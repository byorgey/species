{-# LANGUAGE NoImplicitPrelude
           , TemplateHaskell
           , FlexibleInstances
           , TypeFamilies
           , PatternGuards
  #-}

-- | Code to derive enumeration routines for user-defined data types.
module Math.Combinatorics.Species.TH where

import NumericPrelude
import PreludeBase

import Math.Combinatorics.Species.Enumerate
import Math.Combinatorics.Species.Structures

import Control.Arrow (first, second, (***))
import Control.Monad (zipWithM, liftM2, mapM, ap)

import Control.Applicative (Applicative(..), (<$>), (<*>))

import Language.Haskell.TH

instance Applicative Q where
  pure  = return
  (<*>) = ap

deriveEnumerable :: Name -> Q [Dec]
deriveEnumerable nm = do
  st <- nameToStruct nm
  sequence [mkEnumerableInst nm st]

data Struct = SId
            | SConst Type    -- ^ for types of kind *
            | SEnum  Type    -- ^ for Enumerable type constructors of kind (* -> *)
            | SSumProd [(Name, [Struct])] -- ^ sum-of-products
            | SComp Struct Struct  -- ^ composition
            | SSelf          -- ^ recursive occurrence
  deriving Show

-- | Report a fatal error and stop processing in the 'Q' monad.
errorQ :: String -> Q a
errorQ msg = report True msg >> error msg

-- | Extract the relevant information about a type constructor into a
--   'Struct'.
nameToStruct :: Name -> Q Struct
nameToStruct nm = reify nm >>= infoToStruct
  where infoToStruct (TyConI d) = decToStruct nm d
        infoToStruct _ = errorQ (show nm ++ " is not a type constructor.")

-- XXX do something with contexts?  Later extension...

decToStruct :: Name -> Dec -> Q Struct
decToStruct _ (DataD _ nm [bndr] cons _)
  = SSumProd <$> mapM (conToStruct nm (tyVarNm bndr)) cons
decToStruct _ (NewtypeD _ nm [bndr] con _)
  = SSumProd . (:[]) <$> conToStruct nm (tyVarNm bndr) con
decToStruct _ (TySynD nm [bndr] ty)
  = tyToStruct nm (tyVarNm bndr) ty
decToStruct nm _
  = errorQ $ "Processing " ++ show nm ++ ": Only type constructors of kind * -> * are supported."

tyVarNm :: TyVarBndr -> Name
tyVarNm (PlainTV n)    = n
tyVarNm (KindedTV n _) = n

conToStruct :: Name -> Name -> Con -> Q (Name, [Struct])
conToStruct nm var (NormalC cnm tys)
  = (,) cnm <$> mapM (tyToStruct nm var) (map snd tys)
conToStruct nm var (RecC    cnm tys)
  = (,) cnm <$> mapM (tyToStruct nm var) (map thrd tys)
   where thrd (_,_,t) = t
conToStruct nm var (InfixC ty1 cnm ty2)
  = (,) cnm <$> mapM (tyToStruct nm var) [snd ty1, snd ty2]

  -- XXX do something with ForallC?

tyToStruct :: Name -> Name -> Type -> Q Struct
tyToStruct nm var (VarT v) | v == var  = return SId
                           | otherwise = errorQ $ "Unknown variable " ++ show v
tyToStruct nm var t@(ConT b) = return $ SConst t
--  | b == ''Bool = SSumProd [('False, [sUnit]), ('True, [sUnit])]   -- XXX keep this?

tyToStruct nm var (AppT t (VarT v))       -- F `o` X === F
  | v == var && t == (ConT nm) = return $ SSelf    -- recursive occurrence
  | v == var                   = return $ SEnum t  -- t had better be Enumerable
  | otherwise     = errorQ $ "Unknown variable " ++ show v
tyToStruct nm var (AppT t1 t2@(AppT _ _)) -- composition
  = SComp <$> tyToStruct nm var t1 <*> tyToStruct nm var t2
tyToStruct nm vars t@(AppT _ _)
  = return $ SConst t

-- XXX add something to deal with tuples?
-- XXX add something to deal with things that are actually OK like  Either a [a]
--     and so on
-- XXX deal with arrow types?

structToTy :: Struct -> Type
structToTy SId         = ConT ''Id
structToTy (SConst t)  = AppT (ConT ''Const) t
structToTy (SEnum t)   = AppT (ConT ''StructTy) t
structToTy (SSumProd []) = ConT ''Void
structToTy (SSumProd ss) = foldl1 (AppT . AppT (ConT ''Sum)) (map conToTy ss)
structToTy (SComp s t) = AppT (AppT (ConT ''Comp) (structToTy s)) (structToTy t)
structToTy SSelf       = error "SSelf in structToTy"  -- XXX ?

conToTy :: (Name, [Struct]) -> Type
conToTy (_, []) = ConT ''Unit
conToTy (_, ps) = foldl1 (AppT . AppT (ConT ''Prod)) (map structToTy ps)

-- XXX just for testing
-- declStructTy :: Struct -> Q Dec
-- declStructTy s = tySynD (mkName "Quux") [] (return (structToTy s))

mkEnumerableInst :: Name -> Struct -> Q Dec
mkEnumerableInst nm st = do
  clauses <- mkIsoClauses st
  instanceD (return []) (appT (conT ''Enumerable) (conT nm))
    [ tySynInstD ''StructTy [conT nm] (return $ structToTy st)
    , return $ FunD 'iso clauses
    ]

mkIsoClauses :: Struct -> Q [Clause]
mkIsoClauses st = (fmap.map) mkClause (mkIsoMatches st)
  where mkClause (pat, exp) = Clause [pat] (NormalB $ exp) []

mkIsoMatches :: Struct -> Q [(Pat, Exp)]
mkIsoMatches SId        = newName "x" >>= \x ->
                            return [(ConP 'Id [VarP x], VarE x)]
mkIsoMatches (SConst t) = newName "x" >>= \x ->
                            return [(ConP 'Const [VarP x], VarE x)]
mkIsoMatches (SEnum t)  = newName "x" >>= \x ->
                            return [(VarP x, AppE (VarE 'iso) (VarE x))]
mkIsoMatches (SSumProd [])    = return []
mkIsoMatches (SSumProd [con]) = mkIsoConMatches con
mkIsoMatches (SSumProd cons)  = addInjs 0 <$> mapM mkIsoConMatches cons
 where addInjs :: Int -> [[(Pat, Exp)]] -> [(Pat, Exp)]
       addInjs n [ps]     = map (addInj (n-1) 'Inr) ps
       addInjs n (ps:pss) = map (addInj n     'Inl) ps ++ addInjs (n+1) pss
       addInj 0 c = first (ConP c . (:[]))
       addInj n c = first (ConP 'Inr . (:[])) . addInj (n-1) c
mkIsoMatches (SComp s1 s2) = errorQ "Comp not implemented yet..."
                           -- (mkIsoMatches s1) (mkIsoMatches s2)  XXX hard!
mkIsoMatches SSelf         = errorQ "SSelf in mkIsoMatches"

mkIsoConMatches :: (Name, [Struct]) -> Q [(Pat, Exp)]
mkIsoConMatches (cnm, []) = return [(ConP 'Unit [], ConE cnm)]
mkIsoConMatches (cnm, ps) = map mkProd . sequence <$> mapM mkIsoMatches ps
  where mkProd :: [(Pat, Exp)] -> (Pat, Exp)
        mkProd = (foldl1 (\x y -> (ConP 'Prod [x, y])) *** foldl AppE (ConE cnm))
               . unzip

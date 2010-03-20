{-# LANGUAGE NoImplicitPrelude
           , TemplateHaskell
           , FlexibleInstances
           , TypeSynonymInstances
           , TypeFamilies
           , PatternGuards
           , DeriveDataTypeable
  #-}

-- | Code to derive enumeration routines for user-defined data types.
module Math.Combinatorics.Species.TH where

import NumericPrelude
import PreludeBase

import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.Enumerate
import Math.Combinatorics.Species.Structures
import Math.Combinatorics.Species.AST

import Control.Arrow (first, second, (***))
import Control.Monad (zipWithM, liftM2, mapM, ap)
import Control.Applicative (Applicative(..), (<$>), (<*>))
import Data.Char (toLower)
import Data.Maybe (isJust)

import Data.Typeable

import Language.Haskell.TH
import Language.Haskell.TH.Syntax (lift)

instance Applicative Q where
  pure  = return
  (<*>) = ap

data C1_ = C1_
  deriving (Show, Typeable)

deriveSpecies :: Name -> Q [Dec]
deriveSpecies nm = do
  st <- nameToStruct nm
  let spNm = mkName . map toLower . nameBase $ nm
  if (isRecursive st)
    then mkEnumerableRec    nm spNm st
    else mkEnumerableNonrec nm spNm st
 where
  mkEnumerableRec nm spNm st = do
    codeNm <- newName (nameBase nm)
    self   <- newName "self"

    [d1] <- [d| data Code_ = Code_ deriving Typeable |]
    let DataD [] _ [] [NormalC _ []] ds = d1
        d1' = DataD [] codeNm [] [NormalC codeNm []] ds

    [d2] <- [d| instance Show $(conT codeNm) where
                  show _ = $(lift (nameBase nm))
            |]

    [d3] <- [d| type instance Interp $(conT codeNm) $(varT self)
                       = $(structToTy self st)
            |]

    applyBody <- NormalB <$> structToSpAST self st
    let d4  = InstanceD [] (AppT (ConT ''ASTFunctor) (ConT codeNm))
                           [FunD 'apply [Clause [WildP, VarP self] applyBody []]]

    [d5] <- [d| instance Show a => Show (Mu $(conT codeNm) a) where
                  show = show . unMu
            |]

    enum <- mkEnumerableInst nm st (Just codeNm)
    sig  <- mkSpeciesSig spNm
    spD  <- mkSpecies spNm st (Just codeNm)

    return $ [d1', d2, d3, d4, d5, enum, sig, spD]

  mkEnumerableNonrec nm spNm st =
    sequence
      [ mkEnumerableInst nm st Nothing
      , mkSpeciesSig spNm
      , mkSpecies spNm st Nothing
      ]

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

structToTy :: Name -> Struct -> Q Type
structToTy _    SId           = conT ''Id
structToTy _    (SConst t)    = appT (conT ''Const) (return t)
structToTy _    (SEnum t)     = appT (conT ''StructTy) (return t)
structToTy _    (SSumProd []) = conT ''Void
structToTy self (SSumProd ss) = foldl1 (appT . appT (conT ''Sum))
                                       (map (conToTy self) ss)
structToTy self (SComp s t)   = appT (appT (conT ''Comp) (structToTy self s))
                                  (structToTy self t)
structToTy self SSelf         = varT self

conToTy :: Name -> (Name, [Struct]) -> Q Type
conToTy _    (_, []) = conT ''Unit
conToTy self (_, ps) = foldl1 (appT . appT (conT ''Prod)) (map (structToTy self) ps)

-- XXX just for testing
-- declStructTy :: Struct -> Q Dec
-- declStructTy s = tySynD (mkName "Quux") [] (return (structToTy s))

-- | If the third argument is Nothing, generate normal non-recursive instance.
--   If the third argument is (Just code), then the instance is for a recursive
--   type with the given code.
mkEnumerableInst :: Name -> Struct -> Maybe Name -> Q Dec
mkEnumerableInst nm st code = do
  clauses <- mkIsoClauses (isJust code) st
  let stTy = case code of
               Just cd -> [t| Mu $(conT cd) |]
               Nothing -> structToTy undefined st
  instanceD (return []) (appT (conT ''Enumerable) (conT nm))
    [ tySynInstD ''StructTy [conT nm] stTy
    , return $ FunD 'iso clauses
    ]

-- the first argument says whether the type is recursive.
mkIsoClauses :: Bool -> Struct -> Q [Clause]
mkIsoClauses isRec st = (fmap.map) (mkClause isRec) (mkIsoMatches st)
  where mkClause False (pat, exp) = Clause [pat] (NormalB $ exp) []
        mkClause True  (pat, exp) = Clause [ConP 'Mu [pat]] (NormalB $ exp) []

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
mkIsoMatches SSelf         = newName "s" >>= \s ->
                               return [(VarP s, AppE (VarE 'iso) (VarE s))]

mkIsoConMatches :: (Name, [Struct]) -> Q [(Pat, Exp)]
mkIsoConMatches (cnm, []) = return [(ConP 'Unit [], ConE cnm)]
mkIsoConMatches (cnm, ps) = map mkProd . sequence <$> mapM mkIsoMatches ps
  where mkProd :: [(Pat, Exp)] -> (Pat, Exp)
        mkProd = (foldl1 (\x y -> (ConP 'Prod [x, y])) *** foldl AppE (ConE cnm))
               . unzip

isRecursive :: Struct -> Bool
isRecursive (SSumProd cons) = any isRecursive (concatMap snd cons)
isRecursive (SComp s1 s2)   = isRecursive s1 || isRecursive s2
isRecursive SSelf           = True
isRecursive _               = False

mkSpeciesSig :: Name -> Q Dec
mkSpeciesSig nm = sigD nm [t| Species s => s |]

mkSpecies :: Name -> Struct -> Maybe Name -> Q Dec
mkSpecies nm st (Just code) = valD (varP nm) (normalB (appE (varE 'rec) (conE code))) []
mkSpecies nm st Nothing     = valD (varP nm) (normalB (structToSp undefined st)) []

structToSp :: Name -> Struct -> Q Exp
structToSp _    SId           = [| singleton |]
structToSp _    (SConst t)    = error "How to deal with SConst in structToSp?"
structToSp self (SEnum t)     = typeToSp self t
structToSp _    (SSumProd []) = [| 0 |]
structToSp self (SSumProd ss) = foldl1 (\x y -> [| $x + $y |]) $ map (conToSp self) ss
structToSp self (SComp s1 s2) = [| $(structToSp self s1) `o` $(structToSp self s2) |]
structToSp self SSelf         = varE self

conToSp :: Name -> (Name, [Struct]) -> Q Exp
conToSp _    (_,[]) = [| 1 |]
conToSp self (_,ps) = foldl1 (\x y -> [| $x * $y |]) $ map (structToSp self) ps

typeToSp :: Name -> Type -> Q Exp
typeToSp _    ListT    = [| linOrd |]
typeToSp self (ConT c) | c == ''[] = [| linOrd |]
                       | otherwise = nameToStruct c >>= structToSp self -- XXX this is wrong! Need to do something else for recursive types?
typeToSp _ _        = error "non-constructor in typeToSp?"

structToSpAST :: Name -> Struct -> Q Exp
structToSpAST _    SId           = [| X |]
structToSpAST _    (SConst t)    = error "SConst in structToSpAST?"
structToSpAST self (SEnum t)     = typeToSpAST self t
structToSpAST _    (SSumProd []) = [| Zero |]
structToSpAST self (SSumProd ss) = foldl1 (\x y -> [| $x :+: $y |])
                                     $ map (conToSpAST self) ss
structToSpAST self (SComp s1 s2) = [| $(structToSpAST self s1) :.: $(structToSpAST self s2) |]
structToSpAST self SSelf         = varE self

conToSpAST :: Name -> (Name, [Struct]) -> Q Exp
conToSpAST _    (_,[]) = [| One |]
conToSpAST self (_,ps) = foldl1 (\x y -> [| $x :*: $y |]) $ map (structToSpAST self) ps

typeToSpAST :: Name -> Type -> Q Exp
typeToSpAST _    ListT    = [| L |]
typeToSpAST self (ConT c) | c == ''[] = [| L |]
                       | otherwise = nameToStruct c >>= structToSpAST self -- XXX this is wrong! Need to do something else for recursive types?
typeToSpAST _ _        = error "non-constructor in typeToSpAST?"

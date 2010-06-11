{-# LANGUAGE NoImplicitPrelude
           , TemplateHaskell
           , FlexibleInstances
           , TypeSynonymInstances
           , TypeFamilies
           , PatternGuards
           , DeriveDataTypeable
  #-}

{- Refactoring plan:

   * need function to compute a (default) species from a Struct.
     - currently have structToSp :: Struct -> Q Exp.
     - [X] refactor it into two pieces, Struct -> USpeciesAST and USpeciesAST -> Q Exp.

   * should really go through and add some comments to things!
     Unfortunately I wasn't good about that when I wrote the code... =P

   * Maybe need to do a similar refactoring of the structToTy stuff?

   * make version of deriveSpecies that takes a USpeciesAST as an argument,
       and use Struct -> USpeciesAST to generate default

   * deriveSpecies should pass the USpeciesAST to... other things that
     currently just destruct the Struct to decide what to do.  Will have to
     pattern-match on both the species and the Struct now and make sure
     that they match, which is a bit annoying, but can't really be helped.

-}

-- | Code to derive species instances for user-defined data types.
module Math.Combinatorics.Species.TH where

import NumericPrelude
import PreludeBase hiding (cycle)

import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.Enumerate
import Math.Combinatorics.Species.Structures
import Math.Combinatorics.Species.AST
import Math.Combinatorics.Species.AST.Instances () -- only import instances

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

    let declCode = DataD [] codeNm [] [NormalC codeNm []] [''Typeable]

    [showCode] <- [d| instance Show $(conT codeNm) where
                        show _ = $(lift (nameBase nm))
                  |]

    [interpCode] <- [d| type instance Interp $(conT codeNm) $(varT self)
                          = $(structToTy self st)
                    |]

    applyBody <- NormalB <$> structToSpAST self st
    let astFunctorInst  = InstanceD [] (AppT (ConT ''ASTFunctor) (ConT codeNm))
                            [FunD 'apply [Clause [WildP, VarP self] applyBody []]]

    [showMu] <- [d| instance Show a => Show (Mu $(conT codeNm) a) where
                      show = show . unMu
                |]

    enum <- mkEnumerableInst nm st (Just codeNm)
    sig  <- mkSpeciesSig spNm
    spD  <- mkSpecies spNm st (Just codeNm)

    return $ [ declCode
             , showCode
             , interpCode
             , astFunctorInst
             , showMu
             , enum
             , sig
             , spD
             ]

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

-- If the third argument is Nothing, generate normal non-recursive instance.
-- If the third argument is (Just code), then the instance is for a recursive
-- type with the given code.
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

-- | Decide whether a type is recursively defined, given its
--   description.
isRecursive :: Struct -> Bool
isRecursive (SSumProd cons) = any isRecursive (concatMap snd cons)
isRecursive (SComp s1 s2)   = isRecursive s1 || isRecursive s2
isRecursive SSelf           = True
isRecursive _               = False

-- | Given a name n, generate the declaration
--
--   > n :: Species s => s
--
mkSpeciesSig :: Name -> Q Dec
mkSpeciesSig nm = sigD nm [t| Species s => s |]

-- XXX need to change the parameters to this function??
mkSpecies :: Name -> Struct -> Maybe Name -> Q Dec
mkSpecies nm st (Just code) = valD (varP nm) (normalB (appE (varE 'rec) (conE code))) []
mkSpecies nm st Nothing     = valD (varP nm) (normalB (structToSp undefined st)) []

-- | Convert a 'Struct' into a default corresponding species.
structToSp :: Struct -> USpeciesAST
structToSp SId           = UX
structToSp (SConst t)    = error "Can't deal with SConst in structToSp"
structToSp (SEnum t)     = error "SEnum in structToSp"
structToSp (SSumProd []) = UZero
structToSp (SSumProd ss) = foldl1 (+) $ map conToSp ss
structToSp (SComp s1 s2) = structToSp s1 `o` structToSp s2
structToSp SSelf         = UOmega

-- | Convert a data constructor and its arguments into a default
--   species.
conToSp :: (Name, [Struct]) -> USpeciesAST
conToSp (_,[]) = UOne
conToSp (_,ps) = foldl1 (*) $ map structToSp ps

-- | Given a name to use in recursive occurrences, convert a species
--   AST into an actual splice-able expression of type  Species s => s.
spToExp :: Name -> USpeciesAST -> Q Exp
spToExp self = spToExp'
 where
  spToExp' UZero                = [| 0 |]
  spToExp' UOne                 = [| 1 |]
  spToExp' (UN n)               = lift n
  spToExp' UX                   = [| singleton |]
  spToExp' UE                   = [| set |]
  spToExp' UC                   = [| cycle |]
  spToExp' UL                   = [| linOrd |]
  spToExp' USubset              = [| subset |]
  spToExp' (UKSubset k)         = [| ksubset $(lift k) |]
  spToExp' UElt                 = [| element |]
  spToExp' (f :+:% g)           = [| $(spToExp' f) + $(spToExp' g) |]
  spToExp' (f :*:% g)           = [| $(spToExp' f) * $(spToExp' g) |]
  spToExp' (f :.:% g)           = [| $(spToExp' f) `o` $(spToExp' g) |]
  spToExp' (f :><:% g)          = [| $(spToExp' f) >< $(spToExp' g) |]
  spToExp' (f :@:% g)           = [| $(spToExp' f) @@ $(spToExp' g) |]
  spToExp' (UDer f)             = [| oneHole $(spToExp' f) |]
  spToExp' (UOfSize _ _)        = error "Can't reify general size predicate into code"
  spToExp' (UOfSizeExactly f k) = [| $(spToExp' f) `ofSizeExactly` $(lift k) |]
  spToExp' (UNonEmpty f)        = [| nonEmpty $(spToExp' f) |]
  spToExp' (URec _)             = [| rec $(varE self) |]
  spToExp' UOmega               = [| rec $(varE self) |]

{-
typeToSp :: Name -> Type -> Q Exp
typeToSp _    ListT    = [| linOrd |]
typeToSp self (ConT c) | c == ''[] = [| linOrd |]
                       | otherwise = nameToStruct c >>= spToExp self -- XXX this is wrong! Need to do something else for recursive types?
typeToSp _ _        = error "non-constructor in typeToSp?"
-}

-- XXX what is this for?

structToSpAST :: Name -> Struct -> Q Exp
structToSpAST _    SId           = [| X |]
structToSpAST _    (SConst t)    = error "SConst in structToSpAST?"
structToSpAST self (SEnum t)     = typeToSpAST self t
structToSpAST _    (SSumProd []) = [| Zero |]
structToSpAST self (SSumProd ss) = foldl1 (\x y -> [| annI $x :+: annI $y |])
                                     $ map (conToSpAST self) ss
structToSpAST self (SComp s1 s2) = [| annI $(structToSpAST self s1) :.: annI $(structToSpAST self s2) |]
structToSpAST self SSelf         = varE self

conToSpAST :: Name -> (Name, [Struct]) -> Q Exp
conToSpAST _    (_,[]) = [| One |]
conToSpAST self (_,ps) = foldl1 (\x y -> [| annI $x :*: annI $y |]) $ map (structToSpAST self) ps

typeToSpAST :: Name -> Type -> Q Exp
typeToSpAST _    ListT    = [| L |]
typeToSpAST self (ConT c) | c == ''[] = [| L |]
                       | otherwise = nameToStruct c >>= structToSpAST self -- XXX this is wrong! Need to do something else for recursive types?
typeToSpAST _ _        = error "non-constructor in typeToSpAST?"

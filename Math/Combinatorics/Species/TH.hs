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
     - [X] refactor it into two pieces, Struct -> SpeciesAST and SpeciesAST -> Q Exp.

   * should really go through and add some comments to things!
     Unfortunately I wasn't good about that when I wrote the code... =P

   * Maybe need to do a similar refactoring of the structToTy stuff?

   * make version of deriveSpecies that takes a SpeciesAST as an argument,
       and use Struct -> SpeciesAST to generate default

   * deriveSpecies should pass the SpeciesAST to... other things that
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

------------------------------------------------------------
--  Preliminaries  -----------------------------------------
------------------------------------------------------------

instance Applicative Q where
  pure  = return
  (<*>) = ap

-- | Report a fatal error and stop processing in the 'Q' monad.
errorQ :: String -> Q a
errorQ msg = report True msg >> error msg

------------------------------------------------------------
--  Parsing type declarations  -----------------------------
------------------------------------------------------------

-- XXX possible improvement: add special cases to Struct for things
-- like Bool, Either, and (,)

-- | A data structure to represent data type declarations.
data Struct = SId
            | SList
            | SConst Type    -- ^ for types of kind *
            | SEnum  Type    -- ^ for Enumerable type constructors of kind (* -> *)
            | SSumProd [(Name, [Struct])] -- ^ sum-of-products
            | SComp Struct Struct  -- ^ composition
            | SSelf          -- ^ recursive occurrence
  deriving Show

-- | Extract the relevant information about a type constructor into a
--   'Struct'.
nameToStruct :: Name -> Q Struct
nameToStruct nm = reify nm >>= infoToStruct
  where infoToStruct (TyConI d) = decToStruct nm d
        infoToStruct _ = errorQ (show nm ++ " is not a type constructor.")

-- XXX do something with contexts?  Later extension...

-- | Extract the relevant information about a data type declaration
--   into a 'Struct', given the name of the type and the declaraion.
decToStruct :: Name -> Dec -> Q Struct
decToStruct _ (DataD _ nm [bndr] cons _)
  = SSumProd <$> mapM (conToStruct nm (tyVarNm bndr)) cons
decToStruct _ (NewtypeD _ nm [bndr] con _)
  = SSumProd . (:[]) <$> conToStruct nm (tyVarNm bndr) con
decToStruct _ (TySynD nm [bndr] ty)
  = tyToStruct nm (tyVarNm bndr) ty
decToStruct nm _
  = errorQ $ "Processing " ++ show nm ++ ": Only type constructors of kind * -> * are supported."

-- | Throw away kind annotations to extract the type variable name.
tyVarNm :: TyVarBndr -> Name
tyVarNm (PlainTV n)    = n
tyVarNm (KindedTV n _) = n

-- | Extract relevant information about a data constructor.  The first
--   two arguments are the name of the type constructor, and the name
--   of its type argument.  Returns the name of the data constructor
--   and a list of descriptions of its arguments.
conToStruct :: Name -> Name -> Con -> Q (Name, [Struct])
conToStruct nm var (NormalC cnm tys)
  = (,) cnm <$> mapM (tyToStruct nm var) (map snd tys)
conToStruct nm var (RecC    cnm tys)
  = (,) cnm <$> mapM (tyToStruct nm var) (map thrd tys)
   where thrd (_,_,t) = t
conToStruct nm var (InfixC ty1 cnm ty2)
  = (,) cnm <$> mapM (tyToStruct nm var) [snd ty1, snd ty2]

  -- XXX do something with ForallC?

-- XXX check this...
-- | Extract a 'Struct' describing an arbitrary type.
tyToStruct :: Name -> Name -> Type -> Q Struct
tyToStruct nm var (VarT v) | v == var  = return SId
                           | otherwise = errorQ $ "Unknown variable " ++ show v
tyToStruct nm var ListT = return SList
tyToStruct nm var t@(ConT b)
  | b == ''[] = return SList
  | otherwise = return $ SConst t

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

------------------------------------------------------------
--  Misc Struct utilities  ---------------------------------
------------------------------------------------------------

-- | Decide whether a type is recursively defined, given its
--   description.
isRecursive :: Struct -> Bool
isRecursive (SSumProd cons) = any isRecursive (concatMap snd cons)
isRecursive (SComp s1 s2)   = isRecursive s1 || isRecursive s2
isRecursive SSelf           = True
isRecursive _               = False

------------------------------------------------------------
--  Generating default species  ----------------------------
------------------------------------------------------------

-- | Convert a 'Struct' into a default corresponding species.
structToSp :: Struct -> SpeciesAST
structToSp SId           = UX
structToSp SList         = UL
structToSp (SConst (ConT t))
  | t == ''Bool = UN 2
  | otherwise   = error $ "structToSp: unrecognized type " ++ show t ++ " in SConst"
structToSp (SEnum t)     = error "SEnum in structToSp"
structToSp (SSumProd []) = UZero
structToSp (SSumProd ss) = foldl1 (+) $ map conToSp ss
structToSp (SComp s1 s2) = structToSp s1 `o` structToSp s2
structToSp SSelf         = UOmega

-- | Convert a data constructor and its arguments into a default
--   species.
conToSp :: (Name, [Struct]) -> SpeciesAST
conToSp (_,[]) = UOne
conToSp (_,ps) = foldl1 (*) $ map structToSp ps

------------------------------------------------------------
--  Generating things from species  ------------------------
------------------------------------------------------------

-- | Given a name to use in recursive occurrences, convert a species
--   AST into an actual splice-able expression of type  Species s => s.
spToExp :: Name -> SpeciesAST -> Q Exp
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
  spToExp' (URec _)             = [| wrap $(varE self) |]
  spToExp' UOmega               = [| wrap $(varE self) |]

-- | Generate the structure type for a given species.
spToTy :: Name -> SpeciesAST -> Q Type
spToTy self = spToTy'
 where
  spToTy' UZero                = [t| Void |]
  spToTy' UOne                 = [t| Unit |]
  spToTy' (UN n)               = [t| Const Integer |]  -- was finTy n, but that
                                                       -- doesn't match up with the
                                                       -- type annotation on TSpeciesAST
  spToTy' UX                   = [t| Id |]
  spToTy' UE                   = [t| Set |]
  spToTy' UC                   = [t| Cycle |]
  spToTy' UL                   = [t| [] |]
  spToTy' USubset              = [t| Set |]
  spToTy' (UKSubset _)         = [t| Set |]
  spToTy' UElt                 = [t| Id |]
  spToTy' (f :+:% g)           = [t| Sum  $(spToTy' f) $(spToTy' g) |]
  spToTy' (f :*:% g)           = [t| Prod $(spToTy' f) $(spToTy' g) |]
  spToTy' (f :.:% g)           = [t| Comp $(spToTy' f) $(spToTy' g) |]
  spToTy' (f :><:% g)          = [t| Prod $(spToTy' f) $(spToTy' g) |]
  spToTy' (f :@:% g)           = [t| Comp $(spToTy' f) $(spToTy' g) |]
  spToTy' (UDer f)             = [t| Star $(spToTy' f) |]
  spToTy' (UOfSize f _)        = spToTy' f
  spToTy' (UOfSizeExactly f _) = spToTy' f
  spToTy' (UNonEmpty f)        = spToTy' f
  spToTy' (URec _)             = varT self
  spToTy' UOmega               = varT self

{-
-- | Generate a finite type of a given size, using a binary scheme.
finTy :: Integer -> Q Type
finTy 0 = [t| Void |]
finTy 1 = [t| Unit |]
finTy 2 = [t| Const Bool |]
finTy n | even n    = [t| Prod (Const Bool) $(finTy $ n `div` 2) |]
        | otherwise = [t| Sum Unit $(finTy $ pred n) |]
-}

------------------------------------------------------------
--  Code generation  ---------------------------------------
------------------------------------------------------------

-- Enumerable ----------------

-- | Generate an instance of the Enumerable type class, i.e. an
--   isomorphism from the user's data type and the structure type
--   corresponding to the chosen species (or to the default species if
--   the user did not specify one).
--
--   If the third argument is @Nothing@, generate a normal
--   non-recursive instance.  If the third argument is @Just code@,
--   then the instance is for a recursive type with the given code.
mkEnumerableInst :: Name -> SpeciesAST -> Struct -> Maybe Name -> Q Dec
mkEnumerableInst nm sp st code = do
  clauses <- mkIsoClauses (isJust code) sp st
  let stTy = case code of
               Just cd -> [t| Mu $(conT cd) |]
               Nothing -> spToTy undefined sp  -- undefined is OK, it isn't recursive
                                               -- so won't use that argument
  instanceD (return []) (appT (conT ''Enumerable) (conT nm))
    [ tySynInstD ''StructTy [conT nm] stTy
    , return $ FunD 'iso clauses
    ]

-- | Generate the clauses for the definition of the 'iso' method in
--   the 'Enumerable' instance, which translates from the structure
--   type of the species to the user's data type.  The first argument
--   indicates whether the type is recursive.
mkIsoClauses :: Bool -> SpeciesAST -> Struct -> Q [Clause]
mkIsoClauses isRec sp st = (fmap.map) (mkClause isRec) (mkIsoMatches sp st)
  where mkClause False (pat, exp) = Clause [pat] (NormalB $ exp) []
        mkClause True  (pat, exp) = Clause [ConP 'Mu [pat]] (NormalB $ exp) []

mkIsoMatches :: SpeciesAST -> Struct -> Q [(Pat, Exp)]
mkIsoMatches _ SId        = newName "x" >>= \x ->
                              return [(ConP 'Id [VarP x], VarE x)]
mkIsoMatches _ (SConst t)
  | t == ConT ''Bool = return [(ConP 'Const [LitP $ IntegerL 1], ConE 'False)
                              ,(ConP 'Const [LitP $ IntegerL 2], ConE 'True)]
  | otherwise        = error "mkIsoMatches: unrecognized type in SConst case"
mkIsoMatches _ (SEnum t)  = newName "x" >>= \x ->
                              return [(VarP x, AppE (VarE 'iso) (VarE x))]
mkIsoMatches _ (SSumProd [])     = return []
mkIsoMatches sp (SSumProd [con]) = mkIsoConMatches sp con
mkIsoMatches sp (SSumProd cons)  = addInjs 0 <$> zipWithM mkIsoConMatches (terms sp) cons
 where terms (f :+:% g) = terms f ++ [g]
       terms f = [f]

       addInjs :: Int -> [[(Pat, Exp)]] -> [(Pat, Exp)]
       addInjs n [ps]     = map (addInj (n-1) 'Inr) ps
       addInjs n (ps:pss) = map (addInj n     'Inl) ps ++ addInjs (n+1) pss
       addInj 0 c = first (ConP c . (:[]))
       addInj n c = first (ConP 'Inr . (:[])) . addInj (n-1) c

-- XXX the below is not correct...
-- should really do  iso1 . fmap iso2 where iso1 = ...  iso2 = ...
--   which are obtained from recursive calls.
mkIsoMatches _ (SComp s1 s2) = newName "x" >>= \x ->
                                 return [ (ConP 'Comp [VarP x]
                                        , AppE (VarE 'iso) (AppE (AppE (VarE 'fmap) (VarE 'iso)) (VarE x))) ]
mkIsoMatches _ SSelf         = newName "s" >>= \s ->
                                 return [(VarP s, AppE (VarE 'iso) (VarE s))]

mkIsoConMatches :: SpeciesAST -> (Name, [Struct]) -> Q [(Pat, Exp)]
mkIsoConMatches _ (cnm, []) = return [(ConP 'Unit [], ConE cnm)]
mkIsoConMatches sp (cnm, ps) = map mkProd . sequence <$> zipWithM mkIsoMatches (factors sp) ps
  where factors (f :*:% g) = factors f ++ [g]
        factors f = [f]

        mkProd :: [(Pat, Exp)] -> (Pat, Exp)
        mkProd = (foldl1 (\x y -> (ConP 'Prod [x, y])) *** foldl AppE (ConE cnm))
               . unzip

-- Species definition --------

-- | Given a name n, generate the declaration
--
--   > n :: Species s => s
--
mkSpeciesSig :: Name -> Q Dec
mkSpeciesSig nm = sigD nm [t| Species s => s |]

-- XXX can this use quasiquoting?
-- | Given a name n and a species, generate a declaration for it of
--   that name.  The third parameter indicates whether the species is
--   recursive, and if so what the name of the code is.
mkSpecies :: Name -> SpeciesAST -> Maybe Name -> Q Dec
mkSpecies nm sp (Just code) = valD (varP nm) (normalB (appE (varE 'rec) (conE code))) []
mkSpecies nm sp Nothing     = valD (varP nm) (normalB (spToExp undefined sp)) []

{-
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
-}

------------------------------------------------------------
--  Putting it all together  -------------------------------
------------------------------------------------------------

-- XXX need to add something to check whether the type and given
-- species are compatible.

deriveDefaultSpecies :: Name -> Q [Dec]
deriveDefaultSpecies nm = do
  st <- nameToStruct nm
  deriveSpecies nm (structToSp st)

deriveSpecies :: Name -> SpeciesAST -> Q [Dec]
deriveSpecies nm sp = do
  st <- nameToStruct nm
  let spNm = mkName . map toLower . nameBase $ nm
  if (isRecursive st)
    then mkEnumerableRec    nm spNm st sp
    else mkEnumerableNonrec nm spNm st sp
 where
  mkEnumerableRec nm spNm st sp = do
    codeNm <- newName (nameBase nm)
    self   <- newName "self"

    let declCode = DataD [] codeNm [] [NormalC codeNm []] [''Typeable]

    [showCode] <- [d| instance Show $(conT codeNm) where
                        show _ = $(lift (nameBase nm))
                  |]

    [interpCode] <- [d| type instance Interp $(conT codeNm) $(varT self)
                          = $(spToTy self sp)
                    |]

    applyBody <- NormalB <$> [| unwrap $(spToExp self sp) |]
    let astFunctorInst  = InstanceD [] (AppT (ConT ''ASTFunctor) (ConT codeNm))
                            [FunD 'apply [Clause [WildP, VarP self] applyBody []]]

    [showMu] <- [d| instance Show a => Show (Mu $(conT codeNm) a) where
                      show = show . unMu
                |]

    enum <- mkEnumerableInst nm sp st (Just codeNm)
    sig  <- mkSpeciesSig spNm
    spD  <- mkSpecies spNm sp (Just codeNm)

    return $ [ declCode
             , showCode
             , interpCode
             , astFunctorInst
             , showMu
             , enum
             , sig
             , spD
             ]

  mkEnumerableNonrec nm spNm st sp =
    sequence
      [ mkEnumerableInst nm sp st Nothing
      , mkSpeciesSig spNm
      , mkSpecies spNm sp Nothing
      ]

{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module SymEval.Term where

import Data.Data
import Data.Maybe (fromMaybe)
import Control.Monad.Identity
import Data.List (foldl')
import SymEval.Pretty
import Prettyprinter hiding (Pretty, pretty)
import Control.Arrow (first)

data Var
  = Bound Integer
  | Symb String
  | Free Builtin
  | Literal Lit
  deriving (Eq, Ord, Show, Data, Typeable)

data Lit
  = LitI Integer
  | LitB Bool
  deriving (Eq, Ord, Show, Data, Typeable)

data Builtin
  = BinAdd
  | BinSub
  | BinMul
  | BinLeq
  | BinEq
  | BinIf
  | BinFix
  deriving (Eq, Ord, Show, Data, Typeable)

data Type
  = TyInteger
  | TyBool
  | TyFun Type Type
  deriving (Eq, Ord, Show, Data, Typeable)

-- |WHNF monomorphic lambda terms
data Term v
  = App v [Term v]
  | Lam Type (Term v)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

-- |Binary application reduces terms if necessary
app :: (IsVar v) => Term v -> Term v -> Term v
app (App n xs) u = App n (xs ++ [u])
app (Lam ty t) u = subst (singleSub u) t

appN :: (IsVar v) => Term v -> [Term v] -> Term v
appN = foldl' app

getHeadLams :: Term v -> ([Type], Term v)
getHeadLams (Lam ty t) = first (ty:) $ getHeadLams t
getHeadLams t = ([], t)

class IsVar v where
  isBound :: v -> Maybe Integer

  varMapM :: (Monad m) => (Integer -> m Integer) -> v -> m v

  varMap :: (Integer -> Integer) -> v -> v
  varMap f = runIdentity . varMapM (return . f)

  varDec :: v -> v
  varDec = varMap (\x -> x - 1)

instance IsVar Var where
  isBound (Bound i) = Just i
  isBound _ = Nothing

  varMapM f (Bound i) = Bound <$> f i
  varMapM _ x = return x

-- ** Substitution
--
-- Adapted from [S. Weirich lecture](https://www.cis.upenn.edu/~plclub/blog/2020-06-26-Strongly-typed-System-F/)

instance (IsVar v) => HasSubst (Term v) where
  type SubstVar (Term v) = v

  var = flip App []

  subst s (App n xs) = appN (applySub s n) $ map (subst s) xs
  subst s (Lam ty t) = Lam ty (subst (liftSub s) t)

data Sub term
  = Inc Integer            -- increment by an index amount
  | Maybe term :< Sub term -- extend a substitution (like cons); Nothing means Identity
  | Sub term :<> Sub term  -- compose substitutions
  deriving (Eq, Show, Functor)

infixr :<     -- like usual cons operator (:)
infixr :<>    -- like usual composition  (.)

--  Value of the index x in the substitution
applySub :: (HasSubst term) => Sub term -> SubstVar term -> term
applySub (ty :< s)   x = case isBound x of
    Just 0 -> fromMaybe (var x) ty
    _      -> applySub s (varDec x)
applySub (Inc k)     x = var $ varMap (k +) x
applySub (s1 :<> s2) x = subst s2 (applySub s1 x)

-- |Substitute `var 0` by t, leaving the rest alone.
singleSub :: term -> Sub term
singleSub t = Just t :< Inc 0

-- |General class for terms that support substitution
class (IsVar (SubstVar term)) => HasSubst term where
  type SubstVar term :: *

  -- |How to construct an annotatd bound variable
  var   :: SubstVar term -> term

  -- |How to apply a substitution
  subst :: Sub term -> term -> term

shiftCutoff :: (HasSubst term) => Integer -> Integer -> term -> term
shiftCutoff cutoff k = subst $ foldr (\_ r -> Nothing :< r) (Inc k) [0 .. cutoff - 1]

shift :: (HasSubst term) => Integer -> term -> term
shift = shiftCutoff 0

-- |When traversing a binder, we want to leave Used in substitution when going under a binder
liftSub :: Sub term -> Sub term
liftSub s = Nothing :< (s :<> Inc 1)

-- ** Pretty-printing

instance Pretty Type where
  prettyPrec _ TyInteger = "int"
  prettyPrec _ TyBool = "bool"
  prettyPrec d (TyFun a b) = parensIf (d > 7) $ prettyPrec 7 a <+> "->" <+> prettyPrec 8 b
  -- prettyPrec d (TyProd a b) =
  --   parensIf (d > 7) $ prettyPrec 7 a <+> "*" <+> prettyPrec 8 b
  -- prettyPrec d (TySum a b) =
  --   parensIf (d > 6) $ prettyPrec 6 a <+> "+" <+> prettyPrec 7 b

instance (Pretty v) => Pretty (Term v) where
  prettyPrec d (App n args) = prettyPrecApp d n args align
  prettyPrec d t@Lam {} = parensIf (d > 10) $ assoclBinder "λ" isLam d t
    where isLam (Lam ty t) = Just (ty, t)
          isLam _ = Nothing

instance Pretty Var where
  pretty (Bound i) = "#" <> pretty i
  pretty (Symb s) = "$" <> pretty s
  pretty (Free b) = pretty b
  pretty (Literal l) = pretty l

instance Pretty Lit where
  pretty (LitI i) = pretty i
  pretty (LitB b) = pretty b

instance Pretty Builtin where
  pretty BinAdd = "add"
  pretty BinSub = "sub"
  pretty BinMul = "mul"
  pretty BinLeq = "leq"
  pretty BinEq = "eq"
  pretty BinIf = "if"
  pretty BinFix = "fix"

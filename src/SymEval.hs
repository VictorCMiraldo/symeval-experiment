{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SymEval where

import Control.Applicative
import Control.Arrow (first)
import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Data.Data hiding (eqT)
import Data.Foldable
import Data.Functor
import Data.List (foldl', intersperse)
import qualified Data.Map as Map
import qualified Data.Map.Strict as M
import Prettyprinter hiding (Pretty (..))
import Data.Void (absurd)
import ListT (ListT)
import qualified ListT

import SymEval.Term
import SymEval.Pretty
import SymEval.Solver
import qualified SimpleSMT

data PathStatus = Completed | OutOfFuel

data Path res = Path
  { pathConstraint :: Constraint,
    pathGamma :: M.Map String Type,
    pathStatus :: PathStatus,
    pathResult :: res
  }
  deriving (Functor, Traversable, Foldable)

data SymEvalSt = SymEvalSt
  { sestConstraint :: Constraint,
    sestGamma :: M.Map String Type,
    sestFreshCounter :: Int,
    sestFuel :: Int,
    -- |A branch that has been validated before is never validated again /unless/ we 'learn' something new.
    sestValidated :: Bool
  }

-- |Given a result and a resulting state, returns a 'Path' representing it.
path :: a -> SymEvalSt -> Path a
path x st = Path
  { pathConstraint = sestConstraint st
  , pathGamma = sestGamma st
  , pathStatus = if sestFuel st <= 0 then OutOfFuel else Completed
  , pathResult = x
  }

-- | A 'SymEvalT' is equivalent to a function with type:
--
-- > SymEvalSt -> SMT. -> m [(a, SymEvalSt)]
newtype SymEvalT m a = SymEvalT {symEvalT :: StateT SymEvalSt (ListT m) a}
  deriving (Functor)
  deriving newtype (Applicative, Monad, MonadState SymEvalSt)

symevalT :: (Monad m) => SymEvalT m a -> m [Path a]
symevalT = runSymEvalT st0
  where
    st0 = SymEvalSt mempty M.empty 0 10 False

runSymEvalTRaw :: (Monad m) => SymEvalSt -> SymEvalT m a -> ListT m (a, SymEvalSt)
runSymEvalTRaw st = flip runStateT st . symEvalT

-- |Running a symbolic execution will prepare the solver only once, then use a persistent session
-- to make all the necessary queries.
runSymEvalT :: (Monad m) => SymEvalSt -> SymEvalT m a -> m [Path a]
runSymEvalT st = ListT.toList . fmap (uncurry path) . runSymEvalTRaw st

instance (Monad m) => Alternative (SymEvalT m) where
  empty = SymEvalT $ StateT $ const empty
  xs <|> ys = SymEvalT $ StateT $ \st -> runSymEvalTRaw st xs <|> runSymEvalTRaw st ys

instance MonadTrans SymEvalT where
  lift = SymEvalT . lift . lift

instance (MonadFail m) => MonadFail (SymEvalT m) where
  fail = lift . fail

-- |Prune the set of paths in the current set.
prune :: forall m a . (Monad m) => SymEvalT m a -> SymEvalT m a
prune xs = SymEvalT $ StateT $ \st -> do
    (x, st') <- runSymEvalTRaw st xs
    guard $ solve (sestGamma st') (sestConstraint st')
    return (x, st')

-- |Learn a new constraint and add it as a conjunct to the set of constraints of
-- the current path. Make sure that this branch gets marked as /not/ validated, regardless
-- of whether or not we had already validated it before.
learn :: (Monad m) => Constraint -> SymEvalT m ()
learn c = modify (\st -> st { sestConstraint = c <> sestConstraint st, sestValidated = False })

declSymVars :: (Monad m) => [(String, Type)] -> SymEvalT m [String]
declSymVars vs = do
  old <- get
  modify (\st -> st { sestGamma = M.union (sestGamma st) (M.fromList vs) })
  return $ map fst vs

freshSymVar :: (Monad m) => Type -> SymEvalT m String
freshSymVar ty = head <$> freshSymVars [ty]

freshSymVars :: (Monad m) => [Type] -> SymEvalT m [String]
freshSymVars [] = return []
freshSymVars tys = do
  let n = length tys
  ctr <- gets sestFreshCounter
  modify (\st -> st { sestFreshCounter = sestFreshCounter st + n })
  let vars = zipWith (\i ty -> ("sv" ++ show i , ty)) [ctr..] tys
  declSymVars vars

runEvaluation :: (Monad m) => Term Var -> SymEvalT m (Term Var)
runEvaluation t = do
  let (lams, body) = getHeadLams t
  svars <- freshSymVars lams
  symeval (appN t $ map (var . Symb) svars)

consumeGas :: (Monad m) => SymEvalT m a -> SymEvalT m a
consumeGas f = modify (\st -> st { sestFuel = sestFuel st - 1 }) >> f

currentGas :: (Monad m) => SymEvalT m Int
currentGas = gets sestFuel

symeval :: (Monad m) => Term Var -> SymEvalT m (Term Var)
symeval t = do
  fuelLeft <- currentGas
  if fuelLeft <= 0
    then return t
    else prune $ symeval' t

symeval' :: (Monad m) => Term Var -> SymEvalT m (Term Var)
symeval' t@(Lam ty body) = do
  svar <- freshSymVar ty
  symeval' $ t `app` var (Symb svar)
symeval' t@(App hd args) = do
  case hd of
    Free BinIf -> do
      let [c, t, e] = args
      c' <- symeval' c
      asum
        [ unifyLit c' (LitB True) >>= \constr -> learn constr >> consumeGas (symeval t)
        , unifyLit c' (LitB False) >>= \constr -> learn constr >> consumeGas (symeval e)
        ]
    Free BinFix -> do
      let (f:rest) = args
      consumeGas (symeval $ f `appN` (App (Free BinFix) [f] : rest))
    Free _ ->
      App hd <$> mapM symeval args
    _ -> return t


unifyLit :: (Monad m) => Term Var -> Lit -> SymEvalT m Constraint
unifyLit (App (Symb s) []) l = return $ s :== App (Literal l) []
unifyLit (App (Literal l') []) l = guard (l' == l) >> return mempty
unifyLit t l = return (Eq t (App (Literal l) []))

--- TMP CODE

instance (Pretty a) => Pretty (Path a) where
  pretty (Path conds gamma ps res) =
    vsep [ "With:" <+> pretty (M.toList gamma)
         , "If:" <+> indent 2 (pretty conds)
         , "Status:" <+> pretty ps
         , "Result:" <+> indent 2 (pretty res)
         ]

instance Pretty PathStatus where
  pretty Completed = "Completed"
  pretty OutOfFuel = "OutOfFuel"

runFor :: Term Var -> IO ()
runFor t = do
  paths <- symevalT (runEvaluation t)
  mapM_ (print . pretty) paths

module Main where

import GHC.IO.Encoding

import SymEval
import SymEval.Term
import SymEval.Solver
import Control.Concurrent
import qualified Data.Map as M

newtype Async a = Async (MVar a)

async :: IO a -> IO (Async a)
async action = do
  var <- newEmptyMVar
  forkIO (do r <- action; putMVar var r)
  return (Async var)

wait :: Async a -> IO a
wait (Async var) = readMVar var

-- smart constructors for builtin terms:

fix :: Term Var -> Term Var
fix f = App (Free BinFix) [f]

ite :: Term Var -> Term Var -> Term Var -> Term Var
ite c t e = App (Free BinIf) [c, t, e]

(.==) :: Term Var -> Term Var -> Term Var
t .== u = App (Free BinEq) [t, u]

add :: Term Var -> Term Var -> Term Var
add t u = App (Free BinAdd) [t, u]

sub :: Term Var -> Term Var -> Term Var
sub t u = App (Free BinSub) [t, u]

litI :: Integer -> Term Var
litI = flip App [] . Literal . LitI

mul :: Term Var -> Term Var -> Term Var
mul t u = App (Free BinMul) [t, u]

geq :: Term Var -> Term Var -> Term Var
geq t u = App (Free BinLeq) [u, t]

v :: String -> Term Var
v x = App (Symb x) []

litB :: Bool -> Term Var
litB = flip App [] . Literal . LitB

pow :: Int -> Term Var -> Term Var
pow 0 _ = litI 1
pow n t = mul t (pow (n-1) t)

-- Sample Program
fib :: Term Var
fib = fix $ Lam (TyFun TyInteger TyInteger) $ Lam TyInteger $
  let n = var $ Bound 0
      f = Bound 1
   in ite (n .== litI 0)
          (litI 1)
          (ite (n .== litI 1)
               (litI 1)
               (add (App f [sub n (litI 1)]) (App f [sub n (litI 2)])))

-- Sample constraints
env :: M.Map String Type
env = M.fromList (map (\x -> (x, TyInteger)) $ words "a b c d e x y z")

c1 = "x" :== mul (pow 2 (add (v "a") (v "b"))) (v "z")
c2 = "y" :== pow 2 (v "z")
c3 = "y" :== mul (pow 2 (v "b")) (pow 2 (v "a"))
c4 = Eq (geq (v "a") (litI 12)) (litB True)
c5 = Eq (geq (v "x") (v "y")) (litB False)

-- A very difficult constraint
difficultConstraint = And [ c1 , c2 , c3 , c4 , c5 ]
difficultConstraint' = And [ c1 , c3 , c4 , c5 ]

-- Trying to solve the difficult constraint with two separate solvers: launches two processes
-- and doesn't share anything.
q1 = solve "aaa" env difficultConstraint
q2 = solve "bbb" env difficultConstraint

-- Launches a single process, uses the solver push and pop and doesn't interfere
-- with one another due to the mvar inside "solve"! :)
(s1, s2) = (shared env difficultConstraint, shared env difficultConstraint')
  where
    shared = solve "xxx"

main :: IO ()
main = do
  setLocaleEncoding utf8
  r1 <- async (print q1)
  r2 <- async (print q2)
  wait r1
  wait r2

{-
Compiling the Lambda Calculus
====================================

Sending channels through channels is an interesting model, but how many
algorithms can we really implement this way?  It turns out that the
pi-calculus can implement any computable function.  

We could demonstrate this by compiling the untyped Lambda Calculus to the
untyped Pi Calculus but since we have a typed Pi Calculus as a target,
we will start with a typed Lambda Calculus.  It isn't Turing Complete,
but it's pretty cool none-the-less!

-}

module Lam where

import Pi hiding (Gamma)
import qualified Data.Map as M 
import qualified Data.IORef as R

-- The typed lambda calculus:

data LTyp  
  = LTUnit
  | LTArrow LTyp LTyp
  deriving (Eq, Show)

data Lam
  = LUnit              -- unit:  ()
  | LVar Name          -- variables:  x
  | LAbs Name LTyp Lam -- lambda abstraction: \x:t.e
  | Lam :@: Lam        -- application:  f :@: e executes f on argument e
  | LEff (IO ()) Lam   -- run an effectful computation of your choice
                       -- see printL below for a useful example

instance Show Lam where
  show LUnit = "()"
  show (LVar x) = x
  show (LAbs x t e) = "(\\" ++ x ++ " : " ++ (show t) ++ ". " ++ (show e) ++ ")"
  show (e1 :@: e2) = (show e1) ++ "(" ++ (show e2) ++ ")"
  show (LEff _ e) = "LEff _ (" ++ (show e) ++ ")"

-- Useful abbreviations:

-- printL s e is a lambda expression that prints s and then executes e
printL :: String -> Lam -> Lam
printL s e = LEff (putStr $ s ++ "\n") e

-- Environments for type checking Lambda expressions
type Gamma = M.Map Name LTyp

data Result a = Good a | Bad String

-- Lambda expression type checker
type_of :: Gamma -> Lam -> Result LTyp

type_of g LUnit = Good LTUnit

type_of g (LVar x) = 
  case M.lookup x g of
    Nothing -> Bad ("var not found: " ++ x)
    Just t -> Good t

type_of g (LAbs x t e) = 
  case type_of (M.insert x t g) e of
    Good t2 -> Good (LTArrow t t2)
    x -> x

type_of g (e1 :@: e2) = 
  case (type_of g e1, type_of g e2) of
    (Good (LTArrow targ tresult), Good t2) ->
       if targ == t2 then Good tresult
       else Bad "application type mismatch" 
    (Good t1, Good t2) -> Bad "not arrow type"
    (Bad x, _ ) -> Bad x
    (_, Bad y) -> Bad y

type_of g (LEff a e) = type_of g e

-- type check closed expressions
-- check :: Lam -> IO Bool
-- check e =
--   case type_of M.empty e of
--     Good x -> return True
--     Bad s -> putStr s >> return False

-- Linear lambda expression type checker
lintype_of :: Gamma -> Lam -> Result (Gamma, LTyp)

lintype_of g LUnit = Good (g, LTUnit)

lintype_of g (LVar x) = 
  case M.lookup x g of
    Nothing -> Bad ("var not found: " ++ x)
    Just t -> Good (M.delete x g, t)

lintype_of g (LAbs x t e) = 
  case lintype_of (M.insert x t g) e of
    Good (g',t2) -> 
      if M.member x g' then Bad ("var " ++ x ++ " not used")
      else 
        case M.lookup x g of
          Nothing -> Good (g', LTArrow t t2)
          Just tx -> Good (M.insert x tx g', LTArrow t t2)
    x -> x

lintype_of g (e1 :@: e2) = 
  case lintype_of g e1 of
    Good (g1, LTArrow targ tresult) ->
      case lintype_of g1 e2 of
        Good (g2, t2) ->
          if targ == t2 then Good (g2, tresult)
          else Bad "application type mismatch" 
        x -> x
    Good (g1, t) -> Bad "not arrow type" 
    x -> x

lintype_of g (LEff a e) = lintype_of g e

-- linear type check closed expressions
lincheck :: Lam -> IO Bool
lincheck e =
  case lintype_of M.empty e of
    Good (g,t) -> if M.null g then return True else return False
    Bad s -> putStr (s ++ "\n") >> return False

type Counter = R.IORef Integer

nameGenerator :: Counter -> IO Name
nameGenerator counter = do
  n <- R.readIORef counter
  R.modifyIORef' counter (+1)
  return ("x" ++ show n)


-- TASK!
-- Implement your lambda calculus to pi calculus compiler here!

-- First, generate a target Pi Calculus type
typeTrans :: LTyp -> Typ
typeTrans LTUnit = unitT
typeTrans (LTArrow t1 t2) = TTup [TChan (typeTrans t1), TChan (typeTrans t2)]

--data Lam
--  = LUnit              -- unit:  ()
--  | LVar Name          -- variables:  x
--  | LAbs Name LTyp Lam -- lambda abstraction: \x:t.e
--  | Lam :@: Lam        -- application:  f :@: e executes f on argument e
--  | LEff (IO ()) Lam   -- run an effectful computation of your choice
--                       -- see printL below for a useful example

-- Second, implement your compiler
compile_lam :: IO Name -> Name -> Gamma -> Lam -> IO (LTyp, Pi)
compile_lam fresh n gamma LUnit = do
  return (LTUnit, Out n unitE)
compile_lam fresh n gamma (LVar x) = do
  let (Just xt) = M.lookup x gamma
  let c = "cvar" ++ x
  let p = "pvar" ++ x
  let pi = Inp c (PVar p) $ Out n (EVar p)
  return (xt, pi)
compile_lam fresh n gamma (LAbs x xt exp) = do
  let c = "cvar" ++ x
  let outc = "outc" ++ x
  let gamma' = M.insert x xt gamma
  (tnext, pinext) <- (compile_lam fresh outc gamma' exp)
  let t = LTArrow xt tnext
  let pi = New c (typeTrans xt)$
           New outc (typeTrans tnext)$
           pinext :|: (Out n (ETup [(EVar c), (EVar outc)]))
  return (t, pi)
compile_lam fresh n gamma (exp1 :@: exp2) = do
  chanf <- fresh
  chanx <- fresh
  chanfx <- fresh
  var_res <- fresh
  (LTArrow tx tfx, pif) <- (compile_lam fresh chanf gamma exp1)
  (tx, pix) <- compile_lam fresh chanx gamma exp2                 
  -- here, I assume all lambda calculas expressions have passed type checking
  let pi = New chanf (typeTrans (LTArrow tx tfx)) $
           pif :|:
           (Inp chanf (PTup [PVar chanx, PVar chanfx]) $
           pix :|:
           (Inp chanfx (PVar var_res) $
           Out n (EVar var_res)))
  return (tfx, pi)
compile_lam fresh n gamma (LEff io lam) = do
  io
  (compile_lam fresh n gamma lam)
  



start_lam :: Lam -> IO ()
start_lam e = do
  b <- lincheck e
  if not b 
    then putStr "Source program does not type check.\n"
    else do
      r <- R.newIORef 0
      let fresh = nameGenerator r
      n <- fresh
      (t,pi) <- compile_lam fresh n M.empty e 
      let wrap = New n (typeTrans t) $ pi :|: Inp n Wild (printer "done!")
      start wrap
      case check wrap of
        Left err -> do
          putStrLn $ "Translated program does not type check.  Program:"
          putStrLn $ show wrap
          putStrLn $ "Error: \n" ++ err
        Right () -> start wrap

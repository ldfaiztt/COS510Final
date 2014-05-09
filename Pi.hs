{-# LANGUAGE FlexibleInstances #-}

-- Implementation of the Syntax and Operational Semantics of the Pi Calculus

module Pi where

-- For documentation, see the following pages:
-- http://hackage.haskell.org/package/base-4.7.0.0/docs/Control-Concurrent.html
-- http://hackage.haskell.org/package/base-4.7.0.0/docs/Control-Concurrent-Chan.html
-- http://hackage.haskell.org/package/containers-0.5.5.1/docs/Data-Map.html

import Concurrent

import Control.Applicative
import Control.Monad
import Control.Monad.State

import qualified Data.Map as M 
import qualified Data.List as L
import qualified Data.Either as E

-- Syntax of the Pi Calculus

type Name = String

instance Show (Chan Value) where
  show chan = "<channel>"

-- When reading through these data types, it is worth noting that *all* values
-- in this pi calculus are like locations in the STLC with references: they only
-- show up during evaluation, but *not* in programs a user might write.
--
-- In other words, the "abstract channel" object defined in your handout (as
-- "c" in the syntax) will actually be a Haskell channel (VChan below).  But
-- your translation will generate Pi terms, which only include expressions
-- (Exp), not values.

data Value
  = VChan (Chan Value)  -- channel value
  | VTup [Value]        -- tuple of values
  deriving Show    

data Exp
  = EVar Name           -- variable expression
  | ETup [Exp]          -- tuple of expressions
  deriving Show    

data Pattern
  = PVar Name           -- variable pattern
  | PTup [Pattern]      -- tuple pattern
  | Wild                -- wildcard pattern
  deriving Show    

data Typ
  = TChan Typ           -- channel type
  | TTup [Typ]          -- tuple type
  deriving Eq

instance Show Typ where
  show (TChan t) = "Chan " ++ (show t)
  show (TTup []) = "()"
  show (TTup (h:ts)) = "(" ++ (show h) ++
    (L.concatMap (\x -> ", " ++ (show x)) ts) ++ ")"

instance Show (Env -> IO ()) where
  show f = "<function>"

data Pi
  = Nil
  | Pi :|: Pi
  | New Name Typ Pi
  | Out Name Exp 
  | Inp Name Pattern Pi
  | RepInp Name Pattern Pi   -- repeated input
  | Embed (Env -> IO ()) Pi

instance Show Pi where
  show Nil = "0"
  show (p1 :|: p2) =
    "(" ++ (show p1) ++ ") | (" ++ (show p2) ++ ")"
  show (New x t p) =
    "new " ++ x ++ " : " ++ (show t) ++ ". " ++ (show p)
  show (Out x e) =
    "send " ++ x ++ "(" ++ (show e) ++ ")"
  show (Inp x pat p) =
    "rec " ++ x ++ "(" ++ (show pat) ++ "). " ++ (show p)
  show (RepInp x pat p) =
    "rec! " ++ x ++ "(" ++ (show pat) ++ "). " ++ (show p)
  show (Embed _ p) = "<function> " ++ (show p)

-- Useful Abbreviations

unitT :: Typ
unitT = TTup []

unitE :: Exp
unitE = ETup []

unitP :: Pattern
unitP = PTup []

printer :: String -> Pi
printer s = Embed (\_ -> putStr $ s ++ "\n") Nil

-- Static type checking

-- TASK!
-- Implement your pi calculus type checker here!

-- Recall that in Haskell, the Either type is used to represent computations
-- that may fail.  Either a b has two constructors: Left a, and Right b.
-- In the following functions, Left String represents an error with an error
-- message, and Right b represents success, returning a value of type b.

type Gamma = M.Map Name Typ

typeExp :: Gamma -> Exp -> Either String Typ
typeExp env (EVar nm) 
  | Just t <- M.lookup nm env = Right t
  | otherwise                 = Left (nm ++ "is a free variable.")
typeExp env (ETup es) = 
  let res = map (typeExp env) es in
  let (errors, res') = E.partitionEithers res in
    if (errors == [])
    then Right (TTup res')
    else Left (head errors)

typePat :: Gamma -> Pattern -> Typ -> Either String Gamma
typePat env (PVar nm) t = Right (M.insert nm t env)
typePat env (PTup ps) (TChan t) = Left "Get a TChan type when a tuple is expected."
typePat env (PTup ps) (TTup ts) =
  if length ps == length ts
  then 
    let pts = zip ps ts in
    let f_tmp (Right env) (p, t) = typePat env p t in
    let f_tmp (Left s) (p, t) = (Left s) in
    foldl f_tmp (Right env) pts
  else
    Left "Get a tuple with wrong size."
typePat env Wild v = Right env

checkPi :: Gamma -> Pi -> Either String ()
checkPi env Nil = Right ()
checkPi env (pi1 :|: pi2)
  | (Right (), Right ()) <- (checkPi env pi1, checkPi env pi2) = Right ()
  | (Left s, _)          <- (checkPi env pi1, checkPi env pi2) = Left s
  | (_, Left s)          <- (checkPi env pi1, checkPi env pi2) = Left s
  | otherwise                                                  = Left ""
checkPi env (New nm t pi) = checkPi (M.insert nm (TChan t) env) pi
checkPi env (Out nm e)
  | (Right (TChan t1), Right t2) <- (typeExp env (EVar nm), typeExp env e) = 
    if (t1 == t2)
    then Right ()
    else Left "Output type error."
  | otherwise                                                              =
    Left "Error in Output"
checkPi env (Inp nm p pi)
  | Just t <- M.lookup nm env =  
    let (errors, env') = E.partitionEithers ((typePat env p t) : []) in
    if (errors == [])
    then checkPi (head env') pi
    else Left (head errors)
  | otherwise                 =
    Left ("Free variable " ++ nm ++ " appears.")
checkPi env (RepInp nm p pi)
  | Just t <- M.lookup nm env =  
    let (errors, env') = E.partitionEithers ((typePat env p t) : []) in
    if (errors == [])
    then checkPi (head env') pi
    else Left (head errors)
  | otherwise                 =
    Left ("Free variable " ++ nm ++ " appears.")
checkPi env (Embed _ pi) = checkPi env pi

check :: Pi -> Either String ()
check p = checkPi M.empty p

-- Signals a dynamic error

type_error :: String -> a
type_error s = error $ "Run-time Type Error:" ++ s

-- Environments for interpreters

-- TASK!
-- Implement your interpreter here!

type Env = M.Map Name Value

-- eval_p env p v 
-- match a value v against a pattern p and extend environment env
eval_p :: Env -> Pattern -> Value -> Env
eval_p env (PVar nm) v = M.insert nm v env
eval_p env (PTup ps) (VChan c) = type_error "Get a VChan value when a tuple is expected."
eval_p env (PTup ps) (VTup vs) =
  if length ps == length vs
  then 
    let pvs = zip ps vs in
    let f_tmp env (p, v) = eval_p env p v in
    foldl f_tmp env pvs
  else
    type_error "Get a tuple with wrong size."
eval_p env Wild v = env

-- eval_e env e
-- evaluates e to a value in environment env
eval_e :: Env -> Exp -> Value
eval_e env (EVar x) = env M.! x
eval_e env (ETup es) = VTup (eval_es env es)
  where
    eval_es env [] = []
    eval_es env (e:es) = eval_e env e : eval_es env es
--- Hey, why not use built-in list.map here! ---


run :: Env -> Pi -> IO ()
run env Nil = return ()
run env (pi1 :|: pi2) = parallel (run env pi1 : run env pi2 : [])
run env (New nm t pi) =
  do
    c <- newChan
    let env' = M.insert nm (VChan c) env
    run env' pi
run env (Out nm e)
  | VChan c <- env M.! nm = writeChan c (eval_e env e)
  | otherwise             = type_error "Get a tuple when a VChan value is expected"
run env (Inp nm p pi)
  | VChan c <- env M.! nm = 
    do
      v <- readChan c
      let env' = eval_p env p v
      run env' pi
  | otherwise             = type_error "Get a tuple when a VChan value is expected"
run env (RepInp nm p pi)
  | VChan c <- env M.! nm = 
    do
      v <- readChan c
      let env' = eval_p env p v
      run env' pi
      run env (RepInp nm p pi)
  | otherwise             = type_error "Get a tuple when a VChan value is expected"
run env (Embed wtf pi) = 
  do
    wtf env
    run env pi

start :: Pi -> IO ()
start p = run M.empty p

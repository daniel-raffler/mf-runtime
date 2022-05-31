-- mf-runtime
--
-- Licensed under Creative Commons Legal Code
-- Daniel Raffler 2022
--
-- Abstract machine for a lazy functional language
-- Based on the paper "Übersetzerbau – Abstrakte Maschinen"
-- by François Bry and Norbert Eisinger

module Main where

import Debug.Trace

import qualified Data.List as List
import qualified Data.Map as Map

import qualified Control.Arrow as Arrow

import Data.Map (Map, (!))
import Data.Function (on)

import Lib

type Addr = Int
type Var  = [Char]

data Element
  = --Lit  Int
   Ref  Addr
  | Cont Addr
  | Op   Var
  deriving (Show)

newtype Stack = Stack [Element] deriving (Show)

mkStack :: Stack
mkStack = Stack []

push :: Stack -> Element -> Stack
push (Stack ls) e = Stack (e:ls)

peek :: Stack -> Int ->  Element
peek (Stack ls) k = ls!!k

popK :: Stack -> Int -> Stack
popK (Stack ls) k = Stack $ List.drop k ls

data Type
  = AsBool
  | AsInt
  deriving (Show)

data Info = Info Int Addr deriving (Show)

data Closure
  = Def Info
  | App Addr Addr
  | Ind Addr
  | Pre Var Int
  | Val Type Int
  deriving (Show)

data Heap = Heap [Addr] (Map.Map Addr Closure)

mkHeap :: Heap
mkHeap = Heap [0..] Map.empty

alloc :: Heap -> Closure -> (Heap, Addr)
alloc (Heap (k0:kx) bindings) cl =
  (Heap kx $ Map.insert k0 cl bindings, k0)

lookUp :: Heap -> Addr -> Closure
lookUp (Heap kx bindings) addr = bindings!addr

data Args = N | F Int deriving (Show)

data Opcode
  = Reset
  | Pushval Type Int
  | Pushfun Var
  | Pushpre Var
  | Pushparam Int
  | Makeapp
  | Unwind
  | Call
  | Operator Args
  | Slide Int
  | Update Args
  | Return
  | Halt
  -- | NoOp
  deriving (Show)

newtype Table  = Table  (Map Var Info)
newtype Global = Global (Map Var Addr)

data Program = Program Table [Opcode]

loadCode :: Program -> Map Int Opcode
loadCode (Program table opcodes) = Map.fromList $ zip [0..] opcodes

loadDefs :: Program -> (Heap, Global)
loadDefs (Program (Table info) opcodes) = Arrow.second wrapper $
                                          List.mapAccumL alloc mkHeap [Def f0 | f0 <- Map.elems info]
  where wrapper = Global . Map.fromList . zip (Map.keys info)

data State = State Heap Stack Addr

getAddr :: Global -> Var -> Addr
getAddr (Global gl) f = gl!f

getArg :: Heap -> Addr -> Addr
getArg heap addr = b
  where (App a b) = lookUp heap addr

getValue :: Heap -> Addr -> Closure
getValue heap addr =
  case lookUp heap addr of
    Ind ref -> getValue heap ref
    val     -> val

toBool val = if val == 1 then True else False
toInt  val = if val then 1 else 0

applyOp1 :: Heap -> Element -> Element -> (Heap, Addr)
applyOp1 heap op (Ref a) =
  let applyAll (Op "~"  ) (Val AsInt  n) = alloc heap $ Val AsInt $ (0 -) n
      applyAll (Op "not") (Val AsBool n) = alloc heap $ Val AsInt $ toInt $ not $ toBool n
      
      --applyAll op n = trace (show op ++ show n) undefined
  in applyAll op (getValue heap a)

applyOp2 :: Heap -> Element -> Element -> Element -> (Heap, Addr)
applyOp2 heap op (Ref a) (Ref b) =
  let applyInt (Op op) (Val AsInt n) (Val AsInt m) | op `elem` ["*", "div", "mod", "+", "-"]
        = alloc heap $ Val AsInt $ (opInt op) n m
        where opInt :: [Char] -> Int -> Int -> Int
              opInt "*"   = (*)
              opInt "div" = div
              opInt "mod" = mod
              opInt "+"   = (+)
              opInt "-"   = (-)
      
      applyInt (Op op) (Val AsInt n) (Val AsInt m) | op `elem` ["<", "<=", "==", ">", ">="]
        = alloc heap $ Val AsBool $ toInt $ (opInt op) n m
        where opInt :: [Char] -> Int -> Int -> Bool
              opInt "<"  = (<)
              opInt "<=" = (<=)
              opInt "==" = (==)
              opInt ">"  = (>)
              opInt ">=" = (>)
      
      --applyInt op n m = trace (show op ++ show n ++ show m) undefined
      applyBool (Op op) (Val AsBool n) (Val AsBool m)
        = alloc heap $ Val AsBool $ toInt $ (opBool op) (toBool n) (toBool m)
        where opBool :: [Char] -> Bool -> Bool -> Bool
              opBool "&&" = (&&)
              opBool "||" = (||)
      
      applyAll (Op op) n m | op `elem` ["&&","||"] = applyBool (Op op) n m
                           | otherwise             = applyInt  (Op op) n m 

      --applyAll op n m = trace (show op ++ show n ++ show m) undefined
  in applyAll op (getValue heap a) (getValue heap b)

applyIf :: Heap -> Element -> Element -> Element -> Addr
applyIf heap (Ref a) (Ref b) (Ref c) = on (apply $ getValue heap a) (getArg heap) b c
  where apply (Val AsBool val) arg1 arg2 = if toBool val then arg1 else arg2

update (Heap kx bindings) r1 r2 =
  Heap kx $ Map.insert r1 (Ind r2) bindings
    
evalStep :: Map Var Int -> Global -> State -> Opcode -> State
evalStep arity global (State heap stack addr) op =
  case op of
    Reset -> State heap mkStack addr
    
    Pushval typ val -> State heap' stack' addr
      where (heap', ref) = alloc heap $ Val typ val
            stack' = push stack (Ref ref)
    
    Pushfun f -> State heap stack' addr
      where ref = getAddr global f
            stack' = push stack (Ref ref)
    
    Pushpre op -> State heap' stack' addr
      where (heap', cl) = alloc heap $ Pre op (arity!op)
            stack' = push stack $ Ref cl
    
    Pushparam k -> State heap stack' addr
      where Ref a = peek stack (1+k)
            stack' = push stack (Ref $ getArg heap a)
    
    Makeapp -> State heap' st2 addr
      where [Ref a, Ref b] = map (peek stack) [0,1]
            (heap', cl) = alloc heap $ App a b
            st1 = popK stack 2
            st2 = push st1 $ Ref cl
    
    Unwind ->
      case getValue heap r of
        App a b   -> State heap (push stack $ Ref a) (addr-1)
        otherwise -> State heap stack addr
      where Ref r = peek stack 0
    
    Call ->
      case getValue heap r of
        Val typ val -> State heap stack addr
        Def (Info arity entry) -> State heap stack' entry
          where stack' = push stack $ Cont addr
        Pre op 1 -> State heap st2 12
          where st1 = push stack $ Cont addr
                st2 = push st1 $ Op op
        Pre op 2 -> State heap st2 18
          where st1 = push stack $ Cont addr
                st2 = push st1 $ Op op
        Pre "if" _ -> State heap stack' 4
          where stack' = push stack $ Cont addr
      where Ref r = peek stack 0
    
    Operator N -> State heap st2 addr
      where -- stack: [val,ret,f,(- arg),(- arg1),(- arg2)]
            [val,ret,arg1,arg2] = map (peek stack) [0,1,4,5]
            cl = applyIf heap val arg1 arg2
            stack' = popK stack 5
            st1 = push stack' ret
            st2 = push st1 $ Ref cl
    
    Operator (F 1) -> State heap' st2 addr
      where -- stack: [val1,op,ret,f,(- arg1)]
            [val1,op,ret] = map (peek stack) [0..2]
            (heap', cl) = applyOp1 heap op val1
            stack' = popK stack 4
            st1 = push stack' ret
            st2 = push st1 $ Ref cl
    
    Operator (F 2) -> State heap' st2 addr
      where -- stack: [val1,val2,op,ret,f,(- arg1),(- arg2)]
            [val1,val2,op,ret] = map (peek stack) [0..3]
            (heap', cl) = applyOp2 heap op val1 val2
            stack' = popK stack 6
            st1 = push stack' ret
            st2 = push st1 $ Ref cl
    
    Update N -> evalStep arity global st1 (Slide 1)
      where st1 = evalStep arity global (State heap stack addr) $ Update (F 0)
    
    Update (F k) -> State heap' stack addr
      where [Ref r1, Ref r2] = map (peek stack) [2+k, 0]
            heap' = update heap r1 r2
    
    Slide k -> State heap st2 addr
      where [a,b]  = map (peek stack) [0,1]
            stack' = popK stack (2+k)
            st1 = push stack' b
            st2 = push st1 a
    
    Return -> State heap st2 addr'
      where [ret, Cont addr'] = map (peek stack) [0,1]
            st1 = popK stack 2
            st2 = push st1 ret
    
    -- NoOp -> State heap stack addr

evalAll :: Map Var Int -> Global -> Map Int Opcode -> State -> [(Opcode,State)]
evalAll arity global mp st@(State heap stack addr) =
  case mp!addr of
    Halt -> [(Halt, st)]
    op   -> (op, st) :
      (evalAll arity global mp $
       evalStep arity global (State heap stack (1+addr)) op)

runProgram :: Map Var Int -> Program -> [(Opcode, State)]
runProgram arity pr = evalAll arity global (loadCode pr) (State heap undefined 0) 
  where (heap, global) = loadDefs pr

showBindings (Heap kx bindings)
  = concatMap (uncurry pretty) $ zip ("  heap: " : repeat "        ") $ Map.assocs bindings
  where pretty h (addr, val) = h ++ show addr ++ ": " ++ show val ++ "\n"

showState (0, (op, State heap stack addr)) =
  show 0 ++ ":\n" ++
  "  stack: " ++ "undefined\n" ++
  showBindings heap ++ "\n" ++
  show op ++ " (@" ++ show 0 ++ ")"

showState (n, (op, State heap stack addr)) =
  "\n\n" ++ show n ++ ":\n" ++
  "  stack: " ++ show stack ++ "\n" ++
  showBindings heap ++ "\n" ++
  show op ++ " (@" ++ show addr ++ ")"

main :: IO ()
main = putStrLn $ concatMap showState $ zip [0..] $ runProgram arity p1
  where arity = Map.fromList [("*",2),("+",2),("==",2),("if",3)]

-- second a b = b
-- main = second undefined 2

p1 :: Program
p1 =
  Program
   (Table $ Map.fromList [
       ("undefined", Info 0 5),
       ("second",    Info 1 9),
       ("main",      Info 0 15)]
   )
   [Reset,
    Pushfun "main",
    Unwind,
    Call,
    Halt,
    
    Pushval AsInt undefined,
    Update (F 0),
    Slide 1,
    Return,
    
    Pushparam 2,
    Update (F 2),
    Slide 3,
    Unwind,
    Call,
    Return,

    Pushval AsInt 2,
    Pushfun "undefined",
    Pushfun "second",
    Makeapp,
    Makeapp,
    Update (F 0),
    Slide 1,
    Unwind,
    Call,
    Return
   ]


-- second a b = b
-- main = second 1 2
{-
p1 :: Program
p1 =
  Program
   (Table $ Map.fromList [
       ("second", Info 2 5),
       ("main",   Info 0 11)]
   )
   [Reset,
    Pushfun "main",
    Unwind,
    Call,
    Halt,
    
    Pushparam 2,
    Update (F 2),
    Slide 3,
    Unwind,
    Call,
    Return,
    
    Pushval AsInt 2,
    Pushval AsInt 1,
    Pushfun "second",
    Makeapp,
    Makeapp,
    Update (F 0),
    Slide 1,
    Unwind,
    Call,
    Return
   ]
-}

-- main = if False then 3 else 1
{-
p1 :: Program
p1 =
  Program
   (Table $ Map.fromList [
       ("main", Info 0 27)
       ]
   )
   [Reset,
    Pushfun "main",
    Call,
    Halt,
    
    Pushparam 1,
    Unwind,
    Call,
    Operator N,
    Update N,
    Unwind,
    Call,
    Return,
    
    Pushparam 2,
    Unwind,
    Call,
    Operator (F 1),
    Update N,
    Return,
    
    Pushparam 2,
    Unwind,
    Call,
    Pushparam 4,
    Unwind,
    Call,
    Operator (F 2),
    Update N,
    Return,
    
    Pushval AsInt 1,
    Pushval AsInt 3,
    Pushval AsBool (toInt False),
    Pushpre "if",
    Makeapp,
    Makeapp,
    Makeapp,
    Update (F 0),
    Slide 1,
    Unwind,
    Call,
    Return
   ]
-}

-- quadrat x = x*x
-- main = quadrat (quadrat (3*1))
{-
p1 :: Program
p1 =
  Program
   (Table $ Map.fromList [
       ("main",    Info 0 27),
       ("quadrat", Info 1 41)]
   )
   [Reset,
    Pushfun "main",
    Call,
    Halt,
    
    Pushparam 1,
    Unwind,
    Call,
    Operator N,
    Update N,
    Unwind,
    Call,
    Return,
    
    Pushparam 2,
    Unwind,
    Call,
    Operator (F 1),
    Update N,
    Return,
    
    Pushparam 2,
    Unwind,
    Call,
    Pushparam 4,
    Unwind,
    Call,
    Operator (F 2),
    Update N,
    Return,
    
    Pushval AsInt 1,
    Pushval AsInt 3,
    Pushpre "*",
    Makeapp,
    Makeapp,
    Pushfun "quadrat",
    Makeapp,
    Pushfun "quadrat",
    Makeapp,
    Update (F 0),
    Slide 1,
    Unwind,
    Call,
    Return,
    
    Pushparam 1,
    Pushparam 2,
    Pushpre "*",
    Makeapp,
    Makeapp,
    Update (F 1),
    Slide 2,
    Unwind,
    Call,
    Return
   ]
-}

-- main = add 8 17
-- add a b = if a == 0 then b else suc (add (pre a) b)
-- pre a = -1 + a
-- suc a =  1 + a
{-
p1 :: Program
p1 =
  Program
   (Table $ Map.fromList [
       ("main", Info 0 71),
       ("add",  Info 2 47),
       ("suc",  Info 1 37),
       ("pre",  Info 1 27)]
   )
   [Reset,
    Pushfun "main",
    Call,
    Halt,
    
    Pushparam 1,
    Unwind,
    Call,
    Operator N,
    Update N,
    Unwind,
    Call,
    Return,
    
    Pushparam 2,
    Unwind,
    Call,
    Operator (F 1),
    Update N,
    Return,
    
    Pushparam 2,
    Unwind,
    Call,
    Pushparam 4,
    Unwind,
    Call,
    Operator (F 2),
    Update N,
    Return,
    
    Pushval AsInt (-1),
    Pushparam 2,
    Pushpre "+",
    Makeapp,
    Makeapp,
    Update (F 1),
    Slide 2,
    Unwind,
    Call,
    Return,
    
    Pushval AsInt 1,
    Pushparam 2,
    Pushpre "+",
    Makeapp,
    Makeapp,
    Update (F 1),
    Slide 2,
    Unwind,
    Call,
    Return,
    
    Pushparam 2,
    Pushparam 2,
    Pushfun "pre",
    Makeapp,
    Pushfun "add",
    Makeapp,
    Makeapp,
    Pushfun "suc",
    Makeapp,
    Pushparam 3,
    Pushval AsInt 0,
    Pushparam 4,
    Pushpre "==",
    Makeapp,
    Makeapp,
    Pushpre "if",
    Makeapp,
    Makeapp,
    Makeapp,
    Update (F 2),
    Slide 3,
    Unwind,
    Call,
    Return,
     
    Pushval AsInt 17,
    Pushval AsInt 8,
    Pushfun "add",
    Makeapp,
    Makeapp,
    Update (F 0),
    Slide 1,
    Unwind,
    Call,
    Return
   ]
-}

-- main = exp 2 5
-- exp a b = if b == 0 then 1 else b * (exp a (pre b))
{-
p1 :: Program
p1 =
  Program
   (Table $ Map.fromList [
       ("main", Info 0 63),
       ("exp",  Info 2 37),
       ("pre",  Info 1 27)]
   )
   [Reset,
    Pushfun "main",
    Call,
    Halt,
    
    Pushparam 1,
    Unwind,
    Call,
    Operator N,
    Update N,
    Unwind,
    Call,
    Return,
    
    Pushparam 2,
    Unwind,
    Call,
    Operator (F 1),
    Update N,
    Return,
    
    Pushparam 2,
    Unwind,
    Call,
    Pushparam 4,
    Unwind,
    Call,
    Operator (F 2),
    Update N,
    Return,
    
    Pushval AsInt (-1),
    Pushparam 2,
    Pushpre "+",
    Makeapp,
    Makeapp,
    Update (F 1),
    Slide 2,
    Unwind,
    Call,
    Return,
    
    Pushparam 2,
    Pushfun "pre",
    Makeapp,
    Pushparam 2,
    Pushfun "exp",
    Makeapp,
    Makeapp,
    Pushparam 2,
    Pushpre "*",
    Makeapp,
    Makeapp,
    Pushval AsInt 1,
    Pushparam 4,
    Pushval AsInt 0,
    Pushpre "==",
    Makeapp,
    Makeapp,
    Pushpre "if",
    Makeapp,
    Makeapp,
    Makeapp,
    Update (F 2),
    Slide 3,
    Unwind,
    Call,
    Return,
    
    Pushval AsInt 5,
    Pushval AsInt 2,
    Pushfun "exp",
    Makeapp,
    Makeapp,
    Update (F 0),
    Slide 1,
    Unwind,
    Call,
    Return
   ]
-}

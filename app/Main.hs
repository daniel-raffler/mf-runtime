{-# LANGUAGE OverloadedStrings #-}

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

import qualified Data.List      as List
import qualified Data.Map       as Map
import qualified Data.Text.Lazy as Text

import qualified Control.Arrow as Arrow
import qualified Options.Applicative as OptA

import Data.Text.Lazy (Text)
import Data.Map (Map, (!))
import Data.Function (on)

import MachineF

type ROpc  = MachineF.Addr
type RHeap = Int

newtype Code = Code (Map.Map ROpc Opcode)
  deriving (Show)

prefetch :: ROpc -> Code -> Opcode
prefetch p (Code ops) = ops!p

mkCode :: Program -> Code
mkCode (Program _ _ code) = Code (Map.fromList $ zip [0..] code)

newtype Env = Env (Map Id RHeap)
  deriving (Show)

data Closure
  = Def Info
  | App RHeap RHeap
  | Ind RHeap
  | Pre Id Int
  | Val Value
  deriving (Show)

data Heap = Heap [RHeap] (Map.Map RHeap Closure)
  deriving (Show)

newHeap :: Heap
newHeap = Heap [0..] Map.empty

alloc :: Heap -> Closure -> (Heap, RHeap)
alloc (Heap (k0:kx) bindings) cl = (Heap kx (Map.insert k0 cl bindings), k0)

update :: Heap -> RHeap -> RHeap -> Heap
update (Heap kx bindings) r1 r2 =
  Heap kx $ Map.insert r1 (Ind r2) bindings

lookUp :: Heap -> RHeap -> Closure
lookUp (Heap kx bindings) addr = bindings!addr

mkHeap :: Program -> [Value] -> (Env, Heap)
mkHeap (Program _ info _) args
  = static (unzip $
     -- ("undefined", Pre "#undefined" 0) :
      [(var, Def k) | k@(Info var arity addr) <- info] ++
      zip [Text.pack ('.' : show k) | k <- [1..]] (map Val args)
      )
  where static (vars,cls) = (Env $ Map.fromList $ zip vars addrs, heap)
          where (heap, addrs) = List.mapAccumL alloc newHeap cls

data Cell
  = Ref  RHeap
  | Cont ROpc
  | Op   Id
  deriving (Show)

newtype Stack = Stack [Cell]
  deriving (Show)

newStack :: Stack
newStack = Stack []

push :: Stack -> Cell -> Stack
push (Stack st) e = Stack (e:st)

peek :: Stack -> Int -> Cell
peek (Stack st) k = st!!k

popK :: Stack -> Int -> Stack
popK (Stack st) k = Stack $ List.drop k st

mkStack :: Stack
mkStack = undefined

data State = State Heap Stack ROpc
  deriving (Show)

getAddr :: Env -> Id -> RHeap
getAddr (Env global) var = global!var

getArgs :: Heap -> RHeap -> RHeap
getArgs heap addr = b
  where (App a b) = lookUp heap addr

getValue :: Heap -> RHeap -> Closure
getValue heap addr =
  case lookUp heap addr of
    Ind ref -> getValue heap ref
    val     -> val

getEntryPoint :: Env -> Heap -> Id -> ROpc
getEntryPoint global heap var = entrypoint $ getValue heap $ getAddr global var
  where entrypoint (Def (Info _ _  code)) = code

mkState :: Program -> [Value] -> (Env, State)
mkState pr args = (global, State heap mkStack $ getEntryPoint global heap "@entry")
  where (global, heap) = mkHeap pr args

appIte :: Heap -> Cell -> Cell -> Cell -> RHeap
appIte heap (Ref a) (Ref b) (Ref c) = on (apply $ getValue heap a) (getArgs heap) b c
  where apply (Val (VBool val)) arg1 arg2 = if val then arg1 else arg2

appNullary :: Heap -> Cell -> (Heap, RHeap)
appNullary heap (Op "#undefined") = alloc heap $ Val undefined

appUnary :: Heap -> Cell -> Cell -> (Heap, RHeap)
appUnary heap op (Ref a) = applyAll op (getValue heap a)
  where applyAll (Op "-"  ) (Val (VInt  n)) = alloc heap $ Val $ VInt (-n)
        applyAll (Op "not") (Val (VBool n)) = alloc heap $ Val $ VBool (not n)

appBinary :: Heap -> Cell -> Cell -> Cell -> (Heap, RHeap)
appBinary heap op (Ref a) (Ref b) = applyAll op (getValue heap a) (getValue heap b)
  where applyAll (Op op) n m | op `elem` ["&&","||"] = applyBool (Op op) n m
                             | otherwise             = applyInt  (Op op) n m
        
        applyInt (Op op) (Val (VInt n)) (Val (VInt m)) | op `elem` ["*", "div", "mod", "+", "-"]
          = alloc heap $ Val $ VInt $ (opInt op) n m
          where opInt :: Text -> Int -> Int -> Int
                opInt "*"   = (*)
                opInt "div" = div
                opInt "mod" = mod
                opInt "+"   = (+)
                opInt "-"   = (-)
        
        applyInt (Op op) (Val (VInt n)) (Val (VInt m)) | op `elem` ["<", "<=", "==", ">", ">="]
          = alloc heap $ Val $ VBool $ (opInt op) n m
          where opInt :: Text -> Int -> Int -> Bool
                opInt "<"  = (<)
                opInt "<=" = (<=)
                opInt "==" = (==)
                opInt ">"  = (>)
                opInt ">=" = (>)
        
        applyBool (Op op) (Val (VBool n)) (Val (VBool m))
          = alloc heap $ Val $ VBool $ (opBool op) n m
          where opBool :: Text -> Bool -> Bool -> Bool
                opBool "&&" = (&&)
                opBool "||" = (||)

appK :: Heap -> Cell -> [Cell] -> (Heap, RHeap)
appK heap op []    = appNullary heap op
appK heap op [a]   = appUnary   heap op a
appK heap op [a,b] = appBinary  heap op a b

evalStep :: Env -> State -> Opcode -> State
evalStep global (State heap stack ip) op =
  case op of
    Reset -> State heap newStack ip
    
    Pushval val -> State heap' stack' ip
      where (heap', ref)     = alloc heap $ Val val
            stack'           = push stack (Ref ref)
    
    Pushfun var -> State heap stack' ip
      where ref              = getAddr global var
            stack'           = push stack (Ref ref)
    
    Pushpre op -> State heap' stack' ip
      where (heap', cl)      = alloc heap $ Pre op $ if op == "#undefined" then 0 else MachineF.arity op
            stack'           = push stack $ Ref cl
    
    Pushparam k -> State heap stack' ip
      where Ref a            = peek stack (1+k)
            stack'           = push stack (Ref $ getArgs heap a)
    
    Makeapp -> State heap' st2 ip
      where [Ref a, Ref b]   = map (peek stack) [0,1]
            (heap', cl)      = alloc heap $ App a b
            st1              = popK stack 2
            st2              = push st1 $ Ref cl
    
    Unwind -> let Ref r = peek stack 0
      in case getValue heap r of
           App a b   -> State heap (push stack $ Ref a) (ip-1)
           otherwise -> State heap stack ip
    
    Call -> let Ref r = peek stack 0
      in case getValue heap r of
           Val val -> State heap stack ip
           
           Def (Info var arity entry) -> State heap stack' entry
             where stack' = push stack $ Cont ip
           
           Pre op (-1) -> State heap stack' $ getEntryPoint global heap "@ite"
             where stack' = push stack $ Cont ip
           
           Pre op 0 -> State heap st2 $ getEntryPoint global heap "@nullary"
             where st1    = push stack $ Cont ip
                   st2    = push st1 $ Op op
           
           Pre op 1 -> State heap st2 $ getEntryPoint global heap "@unary"
             where st1    = push stack $ Cont ip
                   st2    = push st1 $ Op op
           
           Pre op 2 -> State heap st2 $ getEntryPoint global heap "@binary"
             where st1    = push stack $ Cont ip
                   st2    = push st1 $ Op op
    
    Operator (-1) -> State heap st2 ip
      where -- stack: [val,ret,f,(- arg),(- arg1),(- arg2)]
            [val,ret]        = map (peek stack) [0,1]
            [arg1,arg2]      = map (peek stack) [4,5]
            cl               = appIte heap val arg1 arg2
            stack'           = popK stack 5
            st1              = push stack' ret
            st2              = push st1 $ Ref cl
    
    Operator k -> State heap' st2 ip
      where -- stack (k=0) [          op,ret,f                  ]
            -- stack (k=1) [val1,     op,ret,f,(- arg1)         ]
            -- stack (k=2) [val1,val2,op,ret,f,(- arg1),(- arg2)]
            -- ..
            vals             = map (peek stack) [0..k-1]
            [op,ret]         = map (peek stack) [k,k+1]
            (heap', cl)      = appK heap op vals
            stack'           = popK stack (2*(k+1))
            st1              = push stack' ret
            st2              = push st1 $ Ref cl
    
    Update k -> State heap' stack ip
      where [Ref r1, Ref r2] = map (peek stack) [2+k, 0]
            heap'            = update heap r1 r2
    
    Slide k -> State heap st2 ip
      where [a,b]            = map (peek stack) [0,1]
            stack'           = popK stack (2+k)
            st1              = push stack' b
            st2              = push st1 a
    
    Return -> State heap st2 ip'
      where [val, Cont ip']  = map (peek stack) [0,1]
            st1              = popK stack 2
            st2              = push st1 val

evalAll :: Code -> Env -> State -> [(Opcode,State)]
evalAll code global state@(State heap stack ip) =
  case prefetch ip code of
    Halt -> [(Halt, state)]
    op   ->  (op, state) :
      (evalAll code global $
        evalStep global (State heap stack (1+ip)) op)

evalProgram :: Program -> [Value] -> [(Opcode, State)]
evalProgram pr args = uncurry (evalAll $ mkCode pr) (mkState pr args)

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

showValue (VInt  v) = show v
showValue (VBool v) = show v
        
showResult (op, State heap (Stack [Ref ret]) ip) = showValue value
  where (Val value) = getValue heap ret

buildOutput steps states =
  if steps
  then concatMap showState $ zip [0..] states
  else showResult $ last states

withArgs :: Options -> IO ()
withArgs (Options steps path args) =
  do pr <- MachineF.fromFile path
     putStrLn $ buildOutput steps $ evalProgram pr args

-- | Command line options
data Options = Options Bool FilePath [Value]

parseValue :: OptA.ReadM Value
parseValue = OptA.eitherReader (Right <$> pVal)
  where pVal "true"  = VBool True
        pVal "false" = VBool False
        pVal k       = VInt (read k)

commandline
  = Options
    <$> OptA.switch (
          OptA.long "steps" <>
          OptA.short 's' <>
          OptA.help "Show evaluation steps"
          )
    <*> OptA.argument OptA.str (
          OptA.metavar "FILE" <>
          OptA.help "Path to the exe file"
          )
    <*> (OptA.many $
           OptA.argument parseValue (
            OptA.metavar "ARGS" <>
            OptA.help "Arguments to the main function"
            ))

main :: IO ()
main = withArgs =<< OptA.execParser opts
  where opts = OptA.info (OptA.helper <*> commandline) (
                 OptA.fullDesc <>
                 OptA.header "mf-runtime - runtime for f programs" <>
                 OptA.progDesc "Evaluate the program for the given arguments"
                 )

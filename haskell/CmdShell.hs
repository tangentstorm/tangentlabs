{-# OPTIONS  -XGADTs -XTypeSynonymInstances #-}
module CmdShell where
import Control.Monad

-- Here is the code I want to run:

demo = do { lit 1; lit 2; lit 3; add; mul }

main :: IO ()
main = do
  (x:xs) <- run demo
  if (x == (1+2)*3)
    then putStrLn "ok"
    else putStrLn "failed. :("

-- The idea is that these commands are passing
-- around an implicit stack.
data TCmd a = Cmd (TStack a -> TStack a)
  
-- Stacks are just lists, but we will wrap them
-- in a special type to show that we're using
-- them in a specific way.
data TStack a = S [a]
  deriving (Show)

-- First, we will implement the instructions as simple functions
-- that operate on lists. Lets call them "Ops":
type Op a = [a] -> [a]

-- opLit produces an Op that pushes a specific value onto the stack.
opLit :: a -> Op a
opLit x = \xs -> x:xs

-- opAdd and opMul perform simple arithmetic:
opAdd :: Num a => Op a
opAdd = \(x:y:zs) -> (x+y):zs

opMul :: Num a => Op a
opMul = \(x:y:zs) -> (x*y):zs

-- opNop does nothing (not used above, but for experimentation):
opNop :: Op a
opNop = \xs -> xs

-- Since we don't want to pass the stack explicitly, we want
-- a way to convert these operations into TCmd instances.
--
-- The following function does this work for us:
cmd :: Op a -> TCmd a
cmd op = Cmd $ \(S xs)  -> S (op xs)

-- and so:
lit x = cmd (opLit x)
add   = cmd opAdd
mul   = cmd opMul
nop   = cmd opNop

-- Now, in order for the code to work, we have to make
-- TCmd into a Monad:
instance Monad TCmd where
  
  -- return :: a -> m a
  -- This should create a TCmd that constructs a brand new
  -- stack with only the given value on it.
  return x = Cmd $ \_ -> S [x]

  -- (>>=)  :: m a -> (a -> m b) -> m b
  -- This is the trickiest part.
  -- We want to take a TCmd and a function that *creates* a TCmd
  -- and produce a new TCmd.
  Cmd c >>= newCmd = nop -- TODO


-- finally, `run` creates a new stack, lets the Cmd do its work,
-- and then extracts the underlying list from the resulting TStack.
run :: TCmd a -> [a]
run (Cmd c) = result where (S result) = c (S [])






----------------------------------------------------------------
-- question 1:
-- !?!?!?! How can the type of 'demo' be 'TCmd [Int]' ??
-- I expect it to be 'TCmd Int'.
----------------------------------------------------------------
demo :: TCmd [Int]

----------------------------------------------------------------
-- question 2:
-- Possibly the same question. Why do I get this error?
----------------------------------------------------------------
-- [1 of 1] Compiling CmdShell         ( CmdShell.hs, CmdShell.o )
--
-- CmdShell.hs:11:13:
--     Couldn't match type []' with IO'
--                             Expected type: IO [Int]
--       Actual type: [[Int]]
--     In the return type of a call of run'
--     In a stmt of a 'do' block: (x : xs) <- run demo
--     In the expression:
--       do { (x : xs) <- run demo;
--            if (x == (1 + 2) * 3) then
--                putStrLn "ok"
--            else
--                putStrLn "failed. :(" }

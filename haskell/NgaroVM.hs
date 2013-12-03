--
-- ngaro vm in haskell
-- http://www.retroforth.org/docs/The_Ngaro_Virtual_Machine.html
--
module NgaroVM where
import Control.Monad.State
import qualified Data.Vector as V

type Adr = Int

data Op
   = NOP         | LIT Int     | DUP         | DROP
   | SWAP        | PUSH        | POP         | NXT Adr
   | JMP Adr     | RET         | JLT Adr     | JGT Adr
   | JNE Adr     | JEQ Adr     | FETCH       | STORE
   | ADD         | SUB         | MUL         | DVM
   | AND         | OR          | XOR         | SHL
   | SHR         | ZRX         | INC         | DEC
   | IN          | OUT         | WAIT        | CALL Adr
   deriving (Show)

data VM = VM { 
   ip   :: Int,            -- instruction pointer
   ram  :: V.Vector Int,
   io   :: V.Vector Int    -- port array
} deriving (Show)

-- step :: VM -> IO VM
-- step vm = do 

-- next :: State VM Int
-- next = do { }
next = 0

i2op :: Int -> Op
i2op  0 = NOP
i2op  1 = LIT  next
i2op  2 = DUP
i2op  3 = DROP
i2op  4 = SWAP
i2op  5 = PUSH
i2op  6 = POP
i2op  7 = NXT next
i2op  8 = JMP next
i2op  9 = RET 
i2op 10 = JLT next
i2op 11 = JGT next
i2op 12 = JNE next
i2op 13 = JEQ next
i2op 14 = FETCH
i2op 15 = STORE
i2op 16 = ADD
i2op 17 = SUB
i2op 18 = MUL
i2op 19 = DVM
i2op 20 = AND
i2op 21 = OR
i2op 22 = XOR
i2op 23 = SHL
i2op 24 = SHR
i2op 25 = ZRX
i2op 26 = INC
i2op 27 = DEC
i2op 28 = IN
i2op 29 = OUT
i2op 30 = WAIT
i2op a  = CALL a


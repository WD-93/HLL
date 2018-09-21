{-# LANGUAGE OverloadedStrings #-}
module Interp where

import Ecomp

--TODO: define simple main HLL interpreter, extract the symbol addresses and
--use them as constants in the compiler contract!

--Until then, simple instruction defs
--Assume on instruction entry the stack looks like:
--PC, HP, o1-o7, r1-r7
--PC @ 1, HP @ 2, o1 @ 3, r1 @ 10
--Gonna be a git and define fetching these, despite it only applying to stack
--offset 0
pc = dup 1
hp = dup 2
o n = dup (2 + n)
r n = dup (9 + n) 

--Note that that's not final: HP might be replaced with MSIZE, jump address,
--bytecode cache and stack pointer registers could be added.

--n = the number of bytes to pop off
dispatch :: Integer -> C() 
dispatch n = do
  void + fromInteger n --Increments PC by n
  gogo
gogo = jump_ $ mload pc & 0xffff
--Standard 0-arity instruction definition
instr :: String -> C() -> C()
instr str body = do
  place_jumpdest $ LNamed $ "hll_" ++ str
  body
  dispatch 2

--Example HLL instruction definition
--r1 = r2 + r3
--BUG: I didn't realize (swap n) swapped with the (n+1)th stack element. That
--means 17 elements are actually accessible! I'll keep using the same regset
--for now though.
def_add :: C()
def_add = instr "add" $ do
  r 2 + dup 13 --r2 + r3
  swap 10 --r1 = result
  pop
  
--r1 += r2, three gas cheaper. Could make a family of these if space allows.
def_add_alt = instr "add_alt" $ do
  swap 9 + r 2 --Swap PC and r1, add r2 to result
  swap 9      --restore PC and save result

--Because the Haskell EDSL is a value, one can use Haskell combinators to
--generate families of instructions in a single definition!
--o1 = one of the 13 other regs
def_ostore = do
  sequence_ [instr ("ostore" ++ show i) $ do
                o 1
                swap (4 + i) --i-th register after o1
                pop
    | i <- [1..13]]
    --Note: If one more register was added the final store would
    --have to be handled specially
--A swap is just as cheap, maybe better
    

--No initializer code, assume all storage starts at 0... not that that matters
--yet.
--For prototype the interpreter just copies calldata to memory at *0 and
--interprets it.
--The first instruction is in the last 16 bits of *0. Require the programmer
--submits valid bytecode that ends with a terminate instruction.
hll_start = do
  calldatacopy 0 0 calldatasize
  0 --The mystery 17th stack index
  sequence_ $ replicate 14 0 --Init r1-r7, o1-o7...
  calldatasize * 32 --HP points to first word after bytecode
  0 --PC points to last 16 bits of first word
  gogo
  --TODO: Check argument order of calldatacopy, check calldatasize returns size
  --in words

--Fetches first 16 bits after current instr
arg16 = mload (pc + 2) & 0xffff

--Relative (forward) jump with 16-bit argument
def_jump = do
  place_jumpdest "hll_jump"
  void + arg16 --Add offset to PC
  gogo

--Conditional forward jump, if(r1) arg:16
--Two possible implems: jumpi (r1 ? pc+arg : pc+2) or extra jumpi
def_jumpi = do
  place_jumpdest "hll_jumpi"
  jumpi (r 1) "hll_jump"
  dispatch 4

--o1 = Array{len = r1, ptr = HP+1}
--Need overflow check for HP
--TODO Optimize
{-
o1 = {tag=1,len=r1 & ff, ptr = HP + 1}
HP += len*32 + 1
-}
newArray = instr "newArray" $ do
  r 1 & 0xff --fetch array len
  

--Object anatomy: tag:8, fields
--Enum tag = Int, Array, Bytestring, Closure, Ref, Tagged

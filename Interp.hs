{-# LANGUAGE OverloadedStrings #-}
module Interp where

import Ecomp

--TODO: define simple main HLL interpreter, extract the symbol addresses and
--use them as constants in the compiler contract!

--Until then, simple instruction defs
--Assume on instruction entry the stack looks like:
--PC, HP, o1-o7, r1-r7
--PC @ 1, HP @ 2, o1 @ 3, r1 @ 10

--Note that that's not final: HP might be replaced with MSIZE, jump address,
--bytecode cache and stack pointer registers could be added.

--n = the number of bytes to pop off
dispatch :: Integer -> C() 
dispatch n = do
  void + fromInteger n --Increments PC by n
  jump_ $ mload (dup 1) & 0xffff

--Example HLL instruction definition
--r1 = r2 + r2
def_add :: C()
def_add = do
  place "hll_add"
  jumpdest
  dup 11 --r2
  dup 13 --r3
  void + void
  swap 11 --r1 = result
  pop
  dispatch 2 --Instruction has arity 0, so advance only 2 bytes for jaddr

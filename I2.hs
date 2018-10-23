{-# LANGUAGE OverloadedStrings #-}
module I2 where

import Ecomp

{-
New regset, lowest first:
BP, PC, HP, HPLim, ArrFocus, BSFocus, R1-3, O1-3, ICache
Also note I have space for 256 instrs, forgot I could just double by adding lol
Code size budget per instruction: <96 bytes
-}
bp = 1
pc = 2
hp = 3
hpLim = 4
arrFocus = 5 --Pointer to start of 8-elem array
bsFocus = 6 --Pointer to start of 256-byte bytestring
r1 = 7; r2 = 8; r3 = 9
o1 = 10; o2 = 11; o3 = 12
iCache = 13

--Assume BP already points to next instruction
--Note: BP should be subtracted because EVM is little-endian; start at the top
--byte. That means instructions are always processed in ascending order.
--The byte pointed to by (BP,PC): 32*PC - BP + 31, so for (31,0) it points to
--byte 0.
--Checked BYTE behaviour, it does indeed index in the expected order.
dispatch = do
  dup iCache ! dup (bp + 1) --Get opcode
  mload $ void + dup 1 --Double to get pointer into JT, then fetch
  jump_ (void & 0xffff) --Mask out jump address, jump
  --Total gas: 32, 3 less than without BP and ICache
  --Code size: 3 + 3 + 6 = 12

--With PC:
--mload dup and mask --Get opcode
--mload (add dup) --JT index
-- ...
--Dispatch is 35 gas not even counting PC increment!
--Using jaddrs-as-opcodes would save gas per instruction, but I've decided
--against it for reasons discussed elsewhere.

--Objects for now: (reserve tag 0 for Ref), Arr, BS
--Todo: Closure, (tagging is done by setting a 32-bit field), files + region

--rA op= E, E may be reg, immediate arg or immediate index into focus
--Invariant: the expr should ensure PC-BP points to next opcode
hlmOp2 op destReg argExpr = do
  assign op destReg argExpr
  dispatch
  --Code size: 3 + expr + dispatch

--rA = op rB
hlmOp1 op rA rB = do
  op (dup rB)
  swap (rA + 1)
  pop
  dispatch

--Assemble instructions and define jump table, note there should really be 256
--instructions.
instructionSet :: [(Label,C())] -> C()
instructionSet defs = do
  sequence_ [place_jumpdest label >> code | (label,code) <- defs]
  place "JUMPTABLE"
  sequence_ [do n <- lookupLabel label
                byte (n `div` 256)
                byte (n `rem` 256)
            | (label,_) <- defs]

--destReg = imm256
const256 destReg = do
  --PC-BP points to opcode as lowest byte
  void - void --PC -= BP, consume BP
  void + 32 --PC -> imm256
  mload $ dup 1 --BP = imm256
  swap destReg
  pop
  void + 32 --PC-31 -> next opcode
  31 --BP = 31
  dispatch
  --Using BP makes fetching large imm args more cumbersome and expensive

--rA = rB
hlmAssign rA rB = do
  dup rB
  swap (rA + 1)
  pop
  bp -= 1
  dispatch

--Pops a byte off ICache, assumes BP points to previous byte
--Note: unreliable for BP < 1.
imm8 = do
  bp -= 1
  dup iCache ! dup (bp + 1)
  --Cost: 15, still cheaper than using PC
{-With PC:
sub 1
mload dup
byte 0
Cost: 18, but second byte can be fetched cheaper?
-}

--BP (+/-)= imm8
hlmMicroJump (+) = do
  assign (+) bp imm8
  dispatch

--BP (+/-)= imm8 * r
--r /= 0|1 is permitted
hlmMicroIJump op r = do
  assign op bp (imm8 * dup (r + 1))
  dispatch

--PC (+/-)= imm8
--When you alter PC you must you sync with BP and refetch ICache?
--No, keep BP at same offset and just refetch ICache.
longJump (+) = do
  assign (+) pc imm8
  set iCache $ mload $ dup pc
  dispatch

--PC = r1
dynJump = do
  pop; pop --pop BP and PC
  dup (r1 - 2)
  31
  dispatch

--Bit ops, TODO use a library for this?
mask numBits = 2 ^ numBits - 1
a << n = a * 2 ^ n
a >>. n = a `div` (2 ^ n)
invert256 n = mask 256 - n

--Do ADDMOD and MULMOD deserve their own instruction?

--Minimal iset:
--Math
--CF

--All objects share two fields: uint8 typeTag, uint32 refTag in the highest bits
--Refs have typeTag 0; refTag is used as an ordinary data field.
--For all other objects, refTag > 0 means they're Tagged and their ordinary
--methods can only be accessed by untagging them with the same ref that tagged
--them.
typeTag = (! 31)
--Masks out the refTag but doesn't shift
refTagMask = mask 32 << 216 
--Check typeTag is tag and refTag is 0
checkTag tag e = do
  e & fromInteger (mask 40 << 216) --mask out typeTag and refTag
  fromInteger (tag << 248) --pattern to compare with
  eq

--Array
--Layout: {byte tag = 1, ..., uint16 mask (lowest 5 bits 0), uint16 ptr}
{- o1 = Array(mask = r1 & ~0b11111), r1 = 1
  if allocation succeeds, else r1 = 0 and HP isn't affected
NOTE: minimum array length is one object, 32 bytes; for an array of length
N, set mask to (N-1)*32.
-}
{-
mask = r1 & ~0b11111
newHP = HP + mask + 32
if newHP > HPLim: fail
o1 = Array{mask = mask,ptr = HP}
HP = newHP
dispatch
fail:
r1 = 0
dispatch
-}
--Code inefficient instruction first, improve later...
newArray = do --relevant regs: HP, HPLim, R1, O1
  fail <- label
  dup r1 & invert256 (mask 5) --mask
  dup 1 + dup (hp + 2) + 32 --next byte beyond array
  dup 1 >? undefined
--Global data in memory:
--0: JUMPTABLE - 8 words, codecopy it in init.
--char* 512: refCounter, cache it from storage
--TODO allocPtr for file system
--nonce for contract creation
--Global region struct
--Cache, taskQueue

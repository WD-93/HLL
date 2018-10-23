{-# LANGUAGE OverloadedStrings #-}
module I2 where

import Ecomp

{-
New regset, lowest first:
BP, PC, HP, HPLim, ArrFocus, BSFocus, R1-3, O1-3, ICache
Also note I have space for 256 instrs, forgot I could just double by adding lol
Code size budget per instruction: <96 bytes
-}
[bp,pc,hp,hpLim,arrFocus,bsFocus,r1,r2,r3,o1,o2,o3,iCache] = map Var [1..13]

--Assume BP already points to next instruction
--Note: BP should be subtracted because EVM is little-endian; start at the top
--byte. That means instructions are always processed in ascending order.
--The byte pointed to by (BP,PC): 32*PC - BP + 31, so for (31,0) it points to
--byte 0.
--Checked BYTE behaviour, it does indeed index in the expected order.
dispatch =
  jump_ $
    (mload $
     (dupVar iCache ! dupVar bp) + dup 1) & 0xffff
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
  sequence_ [place_jumpdest label >> setSO 0 >> code | (label,code) <- defs]
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
  dupVar iCache ! dupVar bp
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
  assign op bp (imm8 * dupVar r)
  dispatch

--PC (+/-)= imm8
--When you alter PC you must you sync with BP and refetch ICache?
--No, keep BP at same offset and just refetch ICache.
longJump (+) = do
  assign (+) pc imm8
  set iCache $ mload $ dupVar pc
  pop
  dispatch

--PC = r1
dynJump = do
  pop; pop --pop BP and PC
  dupVar r1
  31
  dispatch

--Bit ops, TODO use a library for this?
mask numBits = fromInteger (2 ^ numBits - 1)
a << n = a * fromInteger (2 ^ n)
a >>. n = a `div` fromInteger (2 ^ n)
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
checkTag tag e = (e & fromInteger (mask 40 << 216)) ==? theTag tag
theTag n = fromInteger (n << 248)

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
  oldHP <- newVar $ dupVar hp
  lenBytes <- newVar $ dupVar r1 & invert256 (mask 5)
  newHP <- newVar $ dupVar hp + dupVar lenBytes + 32
  --Check if there is enough space in heap...
  ifte (dupVar newHP >? dupVar hpLim)
    (do set r1 1; pop --Success! Now to construct the Array
        --{tag=1,mask=lenBytes,ptr=oldHP}
        swapVar hp --set hp to newHP
        pop --remove newHP
        void << 16 --shift lenBytes to the correct position
        void + void --add lenBytes to oldHP, consuming it
        void + theTag 1 --add the type tag, now oldHP = the array
        swapVar o1
        pop --remove oldHP; the stack is now restored
        dispatch
    )
    (set r1 0 >> clearStack >> dispatch)
  
--Global data in memory:
--0: JUMPTABLE - 8 words, codecopy it in init.
--Before JT, which starts as the lowest two bytes at *0, there are 30 free
--bytes that could be used for globals.
--32-bit refCounter, cache it from storage
--TODO 32-bit allocPtr for file system
--32-bit nonce for contract creation
--Global region struct
--Cache, taskQueue

init_hp :: Num a => a
init_hp = 542 --For now
hlm_init = do
  --Write JUMPTABLE to bytes 30..
  codecopy 30 (labelExpr16 "JUMPTABLE") 512
  --Initial bytestring length passed as first 16 bits of calldata
  initBSLen <- newVar $ calldataload 0 / fromInteger (1 << 240)
  --Copy calldata to bytestring
  calldatacopy init_hp 2 (dupVar initBSLen)
  --initBSLen = initial bytestring struct
  void << 16
  void + fromInteger (theTag 2 + init_hp)
  --Init regs
  mload init_hp --iCache
  0 --o3
  0 --o2
  dupVar initBSLen --o1
  0; 0; 0 --r3-r1
  0 --bsFocus; todo allocate 256-len BS and put it here
  0 --arrFocus; todo allocate 8-element Array and put a Balance in it
  mask 16 --hpLim; pointers are 16-bit
  dupVar undefined

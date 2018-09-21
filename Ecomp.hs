{-# LANGUAGE GADTs, LambdaCase #-}
module Ecomp where

import Data.String
--Move EVM opcodes to separate module?

--Time-travelling compiler monad!
--Takes an env (Label -> Int) and outputs bindings; we pipe its output back
--into itself!
--Other state: offset::Int, the number of bytes it's outputed.
--The reason this works is Haskell's laziness: we'll only use lookups into the
--env in lazy bytes in the text, so they don't cause a circular dependency.

data Label = LNamed String | LAnon Int deriving (Eq,Ord,Read,Show)
instance IsString Label where fromString = LNamed
--First implem of env: a lookup list (TODO replace with Map)
--Bundle with label counter, byte offset
data Env = Env {label_ctr :: Int,
                text_offset :: Int,
                syms :: Syms,
                future_syms :: Syms,
                prog_text :: Program}
         deriving (Eq,Ord,Read,Show)
--This also makes it easy to set one var at a time and extend with new vars!
type Program = [Int]
type Syms = [(Label,Int)]

--GADT or shallow embedding? Try GADT first.

--C for compile
data C a where
  NewLabel :: C Label
  (:=) :: Label -> Int -> C ()
  Byte :: Int -> C ()
  GetTextOffset :: C Int
  LookupLabel :: Label -> C Int --That it's not (Maybe Int) is important!
  FullEnv :: C Env --Used for debugging.
  Return :: a -> C a
  (:>>=) :: C a -> (a -> C b) -> C b
--Where is the state put? The interpreter.

interpret :: C a -> (a,Env)
interpret c = let (a,env) = interp envInit c
                  envInit = Env {label_ctr = 0,
                                 text_offset = 0,
                                 syms = [],
                                 future_syms = syms env, --TIME TRAVEL!!
                                 prog_text = []}
              in (a,env{syms = reverse $ syms env,
                        prog_text = reverse $ prog_text env})
--After refactoring this is just a State monad... oh well.
interp :: Env -> C a -> (a,Env)
interp env =
     \case
       NewLabel -> do let n = label_ctr env
                      (LAnon n,env{label_ctr = n + 1})
       label := n -> ((),env{syms = (label,n) : syms env})
       Byte n -> ((), env{text_offset = text_offset env + 1,
                          prog_text =
                            (if n > 255
                             then error $ "Byte too big: " ++ show(n,env)
                             else n) : prog_text env})
       GetTextOffset -> (text_offset env,env)
       LookupLabel l -> (case lookup l (future_syms env) of
                          Just n -> n,env)
       FullEnv -> (env,env)
       Return a -> (a,env)
                   --Useful for being able to e.g. aggregate lists of labels
       c :>>= f ->
         do let (a,env') = interp env c
            interp env' (f a)

instance Monad C where
  (>>=) = (:>>=)
  return = Return

--Regulatory compliance code...
instance Functor C where
  fmap f c = c >>= return . f

instance Applicative C where
  cf <*> cx = do f <- cf
                 x <- cx
                 return (f x)
  pure = return

label = NewLabel
(=:) = (:=) --Note labels can be used to set small constants as well
byte = Byte
offset = GetTextOffset
lookupLabel = LookupLabel

place :: Label -> C ()
place l = do n <- offset
             l =: n
void :: C()
void = return () --the empty expression: void + 3 adds 3 to top of stack.

--Note: no mention of EVM code has been made so far: C is a general pattern!
--Now we get to the EVM-specific parts

ifam :: Int -> String -> Int -> Int -> C ()
ifam lim err first n | n > lim = error $ err ++ " (" ++ show n ++ ")"
                     | otherwise = byte $ first + n - 1

pushN :: Int -> C ()
pushN = ifam 32 "Too many bytes to push" op_PUSH

dup = ifam 16 "Too high stack offset in DUP" op_DUP
swap = ifam 16 "Too high stack offset in SWAP" op_SWAP

i1 :: Int -> C() -> C()
i1 opcode = (>> byte opcode)
i2 :: Int -> C() -> C() -> C()
i2 opcode a b = a >> b >> byte opcode

pop = byte op_POP

place_jumpdest l = place l >> byte op_JUMPDEST
jumpdest = do l <- label
              place_jumpdest l
              return l
--Assume jds are 16 bits to avoid a circular dependency; for one-byte jumps use
--jump8. There can only be a few of them, so it's not that inconvenient.
labelExpr16 l = do n <- lookupLabel l
                   pushN 2
                   byte (n `div` 256)
                   byte (n `rem` 256)
labelExpr8 l = do n <- lookupLabel l
                  pushN 1
                  byte n
jump_ :: C() -> C()
jump_ = i1 op_JUMP
--Need to know arg ordering for multi-arg instructions!
jumpi_ :: C() -> C() -> C()
jumpi_ = i2 op_JUMPI

jump = jump_ . labelExpr16
jumpi e = jumpi_ e . labelExpr16

push :: Integer -> C()
push n = push' 1 n
  where push' len n =
          if n > 255
          then push' (len+1) (n `div` 256) >> byte (fromInteger n `rem` 256)
          else pushN len >> byte (fromInteger n)

instance Num (C a) where
  fromInteger n = push n >> return undefined
  a + b = a >> b >> byte op_ADD >> return undefined
  a - b = a >> b >> byte op_SUB >> return undefined
  a * b = a >> b >> byte op_MUL >> return undefined
  abs = undefined; signum = undefined

--Logops
(&) :: C() -> C() -> C()
(&) = i2 op_AND
(|||) :: C() -> C() -> C()
(|||) = i2 op_OR
--Bitwise not
not_ = i1 op_NOT

--Memory access
mload :: C() -> C()
mload = i1 op_MLOAD
mstore :: C() -> C() -> C()
mstore = i2 op_MSTORE
mstore8 = i2 0x53

--Loops
dowhile :: C() -> C() -> C()
dowhile cond body = do
  loop <- jumpdest
  body
  jumpi cond loop
--While is inefficient, use whilenot instead and select conds well!
while cond body = whilenot (iszero cond) body
whilenot :: C() -> C() -> C()
whilenot cond body = do
  loop <- jumpdest
  exit <- label
  jumpi cond exit
  body
  jump loop
  place_jumpdest exit

iszero :: C() -> C()
iszero = i1 op_ISZERO

--Now CBB to define opcode names, maybe later

--Calldata access
calldataload = i1 0x35
calldatasize = byte 0x36
--TODO: find out arg ordering for calldatacopy and similar instrs
calldatacopy from to len = do from; to; len; byte 0x37

--Keep opcodes together and ordered, add incrementally as needed
op_ADD = 1
op_MUL = 2
op_SUB = 3

op_ISZERO = 0x15
op_AND = 0x16
op_OR = 0x17
op_NOT = 0x18

op_POP = 0x50
op_MLOAD = 0x51
op_MSTORE = 0x52
op_JUMP = 0x56
op_JUMPI = 0x57
op_JUMPDEST = 0x5b

op_PUSH = 0x60
op_DUP = 0x80
op_SWAP = 0x90

--Tests, interesting cases

--Place duplicates the text
test1 = byte 0 >> place (LAnon 0) >> place (LAnon 1)

--But this works fine
test2 = label >> label >> byte 0

--This loops
test3 = do l <- label; place l; jump l

--This shows the correct symbols now?
test4 = do byte 55; LAnon 0 := 0; e <- FullEnv; byte 0; return e

--syms and future_syms are duplicated
test5 = do e <- FullEnv; LAnon 0 := 0; return e

--Bind seems to be the problem for both syms and code
test6 = byte 255 >> (LAnon 0 := 0) >> return 0
--No, it was not nulling the monoid lists in atomic monads.

--No infinite loop, demonstrates time travel:
test7 = do m <- lookupLabel (LAnon 0); place (LAnon 0); return m
--Infinite loops
test8 = labelExpr16 (LAnon 0)
test9 = do l <- label; m <- lookupLabel l; place l; return m --No loop
test10 = do l <- label; n <- lookupLabel l; place l
--It is strictly evaluating the maybe within the structure of the
--do-expression (the "spine" of the program) which causes an infinite loop:
--the program deadlocks waiting for itself to progress and place the label.
--I must change the type of lookupLabel to move the case into the result,
--making it incomplete (as it depends on a future assignment which may never
--occur).
--The reason labelExpr16 failed is that byte checked if n > 255 before
--returning its state! Fixed, the check is now moved to the byte itself.

--A decompiler would be useful...
--How should it work? You shouldn't be able to jump into a pushN's argument.
--Push instructions are the only instructions with inline arguments, so the
--rest is simple.
--Assign names to jumpdests (L1, L2 ...), allow them to be rewritten?
--Automatically group instructions into an AST where possible,
--i.e. mload (dup1 + dup2)

--Straight-line segments could be interpreted to build an AST and check
--stack invariants, sp[n] = a + b...
--When decompiling you need an assembly AST to decompile to, it'd make sense
--to be able to compile from it and guarantee that compile . decompile =
--decompile . compile = id.

--ASM: [Instr], with pragmas Label := Int
--Instrs may have Expr arguments, labelExpr :: Label -> Expr/word exists.
--'unsafeCoerce' exprs when the stack mismatches?
--Does add take a [w,w] as input? Run AST builder in static analysis. Each
--straight-line segment has a normal form including its stack effect AST, its
--gas cost and max stack used (useful to detect stack overflow exception).
--Can you make a very large AST with a few instructions?
--x on top
--dup1, dup2, add --anon1 = x + x
--repeat.
--Perhaps make stack names opaque when you can't optimize? Otherwise the
--resulting expr tree could be of size O(2^n) in n instructions.

--Convert jumps to constants to either: throw or jump label.
--jump (if a then b else c) --the possible values b and c could also be
--transformed. Annotate labels with their constant value or vice versa.
--codecopy to static addresses could create data labels

--Ooh, you can build the next ASM compiler on top of this one! Reify the
--combinators as constructors, including Void.
--I already have a basic assembler, time to build AST-using lang.

--Task: replace monoid behaviour of syms and prog_text with State.
--prog_text is easy, but does syms work? Yes, but with the list reversed due
--to incremental conses you can't see any symbol bindings until the entire monad
--has run.

--How to build instr graph? Straight-line segment must assume jumpdest starts
--with 0 stack?
--Refer to stack slots by their offset from the BP when the segment starts.
--If the top two slots contain exprs e1,e2 and the next is a two-arity instr i
--then it will be i(e1,e2).
--Can you always guarantee instructions fit into a graph? No, consider
--push 3; jump label. The offsets accessed and net push/pop of a straight-line
--segment is its type? How do jumps within a function work?
--The name map of segments should propagate on jumps?
--Decompile dups to BP[n] = BP[m].
--add: sp[-1] += sp[0]; sp -= 1. This formalization is better because args are
--always within the allocated zone. Another invariant: instructions which
--increase sp write a value to the newly allocated slot without reading the old
--'garbage' value.

--F implements scope: string variables that we later write a parser for?
--Scope properties: args (of which a subset are return), locals
--A new block extends the scope
--Unpopped local variables ruin the scope because shuffling it around is too
--expensive (would need to move O(n)).
--No need to check the callee has the same name map, you could just share the
--mapping between fs.

--s <- f <$> scope (wrap a constructor around take N slots)
--name s =: e
--TH could also be used to set the slot-name binding
--String-based is the best approach, that can be converted to a proper parsed
--language later.

--F args scope, returns take n scope ++ rest
--No optimizations, no type checks. Last consume if on top may avoid a dup on
--use and pop on scope change. Structured iftes and blocks with vars, otherwise
--jumpis and jumps don't pop. Internal gotos which do check stack and
--statically push/pop if necessary?
--Statically check sequence expressions don't alter the stack, otherwise pop
--when necessary.
--All variable declarations must include an assignment?
--Last uses of variables not at the top could be dealt with via static swaps.
--Invariant: never dup, pop when you don't have to? Automatically push/pop to
--correct scope on return/call.
--fac(arg) result --statically rename arg result
--Assign all exprs to implicit variables, flatten program.
--x = 3 + 2 becomes _1 = 3; _2 = 2; x = +(_1,_2)
--Last use is last in text, possible use counts. Returns count as a use at the
--end. Assigning a constant to a var which doesn't depend on the var itself is
--equivalent to freeing it from the last use before the assignment?
--Minimize the number of optimizations applied just to those which make it
--possible to write efficient and syntactically convenient code.
--Selecting variable ordering to minimize the use of swaps is up to the user.
--"Block" pushes can be done just by assigning a naked variable.
--No need for structure at the language level, just as a Haskell combinator.
--Name: varlang?
--Differentiate between internal jumps and outside calls?
--Define program as a single block, starting with nothing on the stack?
--def label (scope) {block} is an inline code block, though falling through to
--it may cause an error.

--Monad which counts stack offset, checks number of words returned by i.
--m1 <> m2 returns concat of results. No instruction returns 2, only 0 or 1?
--Functions may return several. Type: M -> N, don't record stack peak.
--block scope m lets you declare local vars in it.
--What does return mean when you goto another function?
--Perhaps function application should take list of var names and require they
--be on top of stack and the consumed ones are last used there?
--Don't check gotos, just calculate offsets for straight-line code.

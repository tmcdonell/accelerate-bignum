{-# LANGUAGE CPP          #-}
{-# LANGUAGE MagicHash    #-}
{-# LANGUAGE TypeFamilies #-}
-- |
-- Module      : Data.Array.Accelerate.Internal.LLVM.Prim
-- Copyright   : [2016] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Primops for LLVM backends
--

module Data.Array.Accelerate.Internal.LLVM.Prim (

  -- Operators from Num2
  addWithCarryInt64#, mulWithCarryInt64#,
  addWithCarryWord64#, mulWithCarryWord64#,

  -- Operators from Num
  addInt128#, subInt128#, mulInt128#,
  addWord128#, subWord128#, mulWord128#,

  -- Operators from Integral
  quotInt128#, remInt128#, quotRemInt128#,
  quotWord128#, remWord128#, quotRemWord128#,

) where

import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Sugar.Elt

import Data.Array.Accelerate.Internal.BigInt
import Data.Array.Accelerate.Internal.BigWord
import Data.Array.Accelerate.Internal.Orphans.Elt                   ()

import Data.Array.Accelerate.LLVM.CodeGen.IR                        ( Operands(..) )
import Data.Array.Accelerate.LLVM.CodeGen.Monad                     ( CodeGen, freshName, instr_ )
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import qualified LLVM.AST.Type.Name                                 as A
import qualified LLVM.AST.Type.Operand                              as A
import qualified LLVM.AST.Type.Representation                       as A
#if MIN_VERSION_accelerate_llvm(1,3,0)
import LLVM.AST.Type.Downcast                                       ( downcast )
#else
import Data.Array.Accelerate.LLVM.CodeGen.Downcast                  ( downcast )
#endif

import LLVM.AST.Constant                                            ( Constant(Int) )
import LLVM.AST.Instruction                                         hiding ( nsw, nuw )
import LLVM.AST.Name                                                ( Name(..) )
import LLVM.AST.Operand                                             ( Operand(..) )
import LLVM.AST.Type

import Data.Int
import Data.Word
import Prelude                                                      hiding ( uncurry )


uncurry :: (Operands a -> Operands b -> c) -> Operands (((), a), b) -> c
uncurry f (OP_Unit `OP_Pair` x `OP_Pair` y) = f x y

-- Primitive instruction wrappers
-- ------------------------------

-- Operations from Num2
-- --------------------

addWithCarryInt64# :: IRFun1 arch () (EltR (Int64, Int64) -> EltR (Int64, Word64))
addWithCarryInt64# = IRFun1 $ uncurry (prim_wideningInt64 (Add nsw nuw))

mulWithCarryInt64# :: IRFun1 arch () (EltR (Int64, Int64) -> EltR (Int64, Word64))
mulWithCarryInt64# = IRFun1 $ uncurry (prim_wideningInt64 (Mul nsw nuw))

addWithCarryWord64# :: IRFun1 arch () (EltR (Word64, Word64) -> EltR (Word64, Word64))
addWithCarryWord64# = IRFun1 $ uncurry (prim_wideningWord64 (Add nsw nuw))

mulWithCarryWord64# :: IRFun1 arch () (EltR (Word64, Word64) -> EltR (Word64, Word64))
mulWithCarryWord64# = IRFun1 $ uncurry (prim_wideningWord64 (Mul nsw nuw))


prim_wideningInt64
    :: (Operand -> Operand -> InstructionMetadata -> Instruction)
    -> Operands Int64
    -> Operands Int64
    -> CodeGen arch (Operands (((), Int64), Word64))
prim_wideningInt64 op (OP_Int64 x) (OP_Int64 y) = do
  a     <- instr i128 (SExt (downcast x) i128 md)
  b     <- instr i128 (SExt (downcast y) i128 md)
  c     <- instr i128 (op a b md)
  (d,e) <- unpackInt128 c
  return $ OP_Unit `OP_Pair` upcastInt64 d `OP_Pair` upcastWord64 e

prim_wideningWord64
    :: (Operand -> Operand -> InstructionMetadata -> Instruction)
    -> Operands Word64
    -> Operands Word64
    -> CodeGen arch (Operands (((), Word64), Word64))
prim_wideningWord64 op (OP_Word64 x) (OP_Word64 y) = do
  a     <- instr i128 (ZExt (downcast x) i128 md)
  b     <- instr i128 (ZExt (downcast y) i128 md)
  c     <- instr i128 (op a b md)
  (d,e) <- unpackWord128 c
  return $ OP_Unit `OP_Pair` upcastWord64 d `OP_Pair` upcastWord64 e


-- Operations from Num
-- -------------------

addInt128# :: IRFun1 arch () (EltR (Int128, Int128) -> EltR Int128)
addInt128# = IRFun1 $ uncurry (prim_binaryInt128 (Add nsw nuw))

subInt128# :: IRFun1 arch () (EltR (Int128, Int128) -> EltR Int128)
subInt128# = IRFun1 $ uncurry (prim_binaryInt128 (Sub nsw nuw))

mulInt128# :: IRFun1 arch () (EltR (Int128, Int128) -> EltR Int128)
mulInt128# = IRFun1 $ uncurry (prim_binaryInt128 (Mul nsw nuw))

addWord128# :: IRFun1 arch () (EltR (Word128, Word128) -> EltR Word128)
addWord128# = IRFun1 $ uncurry (prim_binaryWord128 (Add nsw nuw))

subWord128# :: IRFun1 arch () (EltR (Word128, Word128) -> EltR Word128)
subWord128# = IRFun1 $ uncurry (prim_binaryWord128 (Sub nsw nuw))

mulWord128# :: IRFun1 arch () (EltR (Word128, Word128) -> EltR Word128)
mulWord128# = IRFun1 $ uncurry (prim_binaryWord128 (Mul nsw nuw))


-- Operations from Integral
-- ------------------------

quotInt128# :: IRFun1 arch () (EltR (Int128, Int128) -> EltR Int128)
quotInt128# = IRFun1 $ uncurry (prim_binaryInt128 (SDiv False))

remInt128# :: IRFun1 arch () (EltR (Int128, Int128) -> EltR Int128)
remInt128# = IRFun1 $ uncurry (prim_binaryInt128 SRem)

quotRemInt128# :: IRFun1 arch () (EltR (Int128, Int128) -> EltR (Int128, Int128))
quotRemInt128# = IRFun1 $ uncurry quotRem'
  where
    quotRem' :: Operands (EltR Int128) -> Operands (EltR Int128) -> CodeGen arch (Operands (EltR (Int128, Int128)))
    quotRem' xx yy
      | OP_Pair (OP_Pair OP_Unit (OP_Int64 xh)) (OP_Word64 xl) <- xx
      , OP_Pair (OP_Pair OP_Unit (OP_Int64 yh)) (OP_Word64 yl) <- yy
      = do
        x       <- packWord128 (downcast xh) (downcast xl)
        y       <- packWord128 (downcast yh) (downcast yl)
        q       <- instr i128 (SDiv False x y md)
        z       <- instr i128 (Mul nsw nuw y q md)
        r       <- instr i128 (Sub nsw nuw x z md)
        (qh,ql) <- unpackInt128 q
        (rh,rl) <- unpackInt128 r
        return $ OP_Unit `OP_Pair` upcastInt128 qh ql `OP_Pair` upcastInt128 rh rl


quotWord128# :: IRFun1 arch () (EltR (Word128, Word128) -> EltR Word128)
quotWord128# = IRFun1 $ uncurry (prim_binaryWord128 (UDiv False))

remWord128# :: IRFun1 arch () (EltR (Word128, Word128) -> EltR Word128)
remWord128# = IRFun1 $ uncurry (prim_binaryWord128 URem)

quotRemWord128# :: IRFun1 arch () (EltR (Word128, Word128) -> EltR (Word128, Word128))
quotRemWord128# = IRFun1 $ uncurry quotRem'
  where
    quotRem' :: Operands (EltR Word128) -> Operands (EltR Word128) -> CodeGen arch (Operands (EltR (Word128, Word128)))
    quotRem' xx yy
      | OP_Pair (OP_Pair OP_Unit (OP_Word64 xh)) (OP_Word64 xl) <- xx
      , OP_Pair (OP_Pair OP_Unit (OP_Word64 yh)) (OP_Word64 yl) <- yy
      = do
        x       <- packWord128 (downcast xh) (downcast xl)
        y       <- packWord128 (downcast yh) (downcast yl)
        q       <- instr i128 (UDiv False x y md)
        z       <- instr i128 (Mul nsw nuw y q md)
        r       <- instr i128 (Sub nsw nuw x z md)
        (qh,ql) <- unpackWord128 q
        (rh,rl) <- unpackWord128 r
        return $ OP_Unit `OP_Pair` upcastWord128 qh ql `OP_Pair` upcastWord128 rh rl


-- Helpers

prim_binaryWord128
    :: (Operand -> Operand -> InstructionMetadata -> Instruction)
    -> Operands (EltR Word128)
    -> Operands (EltR Word128)
    -> CodeGen arch (Operands (EltR Word128))
prim_binaryWord128 op xx yy
  | OP_Pair (OP_Pair OP_Unit (OP_Word64 xh)) (OP_Word64 xl) <- xx
  , OP_Pair (OP_Pair OP_Unit (OP_Word64 yh)) (OP_Word64 yl) <- yy
  = do
      x'      <- packWord128 (downcast xh) (downcast xl)
      y'      <- packWord128 (downcast yh) (downcast yl)
      r       <- instr i128 (op x' y' md)
      (hi,lo) <- unpackWord128 r
      return $ upcastWord128 hi lo

prim_binaryInt128
    :: (Operand -> Operand -> InstructionMetadata -> Instruction)
    -> Operands (EltR Int128)
    -> Operands (EltR Int128)
    -> CodeGen arch (Operands (EltR Int128))
prim_binaryInt128 op xx yy
  | OP_Pair (OP_Pair OP_Unit (OP_Int64 xh)) (OP_Word64 xl) <- xx
  , OP_Pair (OP_Pair OP_Unit (OP_Int64 yh)) (OP_Word64 yl) <- yy
  = do
      x'      <- packInt128 (downcast xh) (downcast xl)
      y'      <- packInt128 (downcast yh) (downcast yl)
      r       <- instr i128 (op x' y' md)
      (hi,lo) <- unpackInt128 r
      return $ upcastInt128 hi lo


-- Prim
-- ----

nsw :: Bool
nsw = False

nuw :: Bool
nuw = False

md :: InstructionMetadata
md = []

fresh :: CodeGen arch Name
fresh = downcast <$> freshName

instr :: Type -> Instruction -> CodeGen arch Operand
instr ty ins = do
  name <- fresh
  instr_ (name := ins)
  return (LocalReference ty name)

packInt128 :: Operand -> Operand -> CodeGen arch Operand
packInt128 hi lo = do
  a <- instr i128 (SExt hi i128 md)
  b <- instr i128 (Shl  nsw nuw a (ConstantOperand (Int 128 64)) md)
  c <- instr i128 (ZExt lo i128 md)
  d <- instr i128 (Or b c md)
  return d

packWord128 :: Operand -> Operand -> CodeGen arch Operand
packWord128 hi lo = do
  a <- instr i128 (ZExt hi i128 md)
  b <- instr i128 (Shl  nsw nuw a (ConstantOperand (Int 128 64)) md)
  c <- instr i128 (ZExt lo i128 md)
  d <- instr i128 (Or b c md)
  return d

unpackInt128 :: Operand -> CodeGen arch (Operand,Operand)
unpackInt128 x = do
  a <- instr i128 (AShr False x (ConstantOperand (Int 128 64)) md)
  b <- instr i64 (Trunc a i64 md)
  c <- instr i64 (Trunc x i64 md)
  return (b,c)

unpackWord128 :: Operand -> CodeGen arch (Operand,Operand)
unpackWord128 x = do
  a <- instr i128 (LShr False x (ConstantOperand (Int 128 64)) md)
  b <- instr i64 (Trunc a i64 md)
  c <- instr i64 (Trunc x i64 md)
  return (b,c)

upcastInt64 :: HasCallStack => Operand -> Operands Int64
upcastInt64 (LocalReference (IntegerType 64) (UnName x)) = OP_Int64 (A.LocalReference A.type' (A.UnName x))
upcastInt64 _ = internalError "expected local reference"

upcastWord64 :: HasCallStack => Operand -> Operands Word64
upcastWord64 (LocalReference (IntegerType 64) (UnName x)) = OP_Word64 (A.LocalReference A.type' (A.UnName x))
upcastWord64 _ = internalError "expected local reference"

upcastInt128 :: Operand -> Operand -> Operands (EltR Int128)
upcastInt128 hi lo = OP_Pair (OP_Pair OP_Unit (upcastInt64 hi)) (upcastWord64 lo)

upcastWord128 :: Operand -> Operand -> Operands (EltR Word128)
upcastWord128 hi lo = OP_Pair (OP_Pair OP_Unit (upcastWord64 hi)) (upcastWord64 lo)


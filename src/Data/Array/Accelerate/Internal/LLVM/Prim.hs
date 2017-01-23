{-# LANGUAGE CPP             #-}
{-# LANGUAGE MagicHash       #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}
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
  addWithCarryInt64#,
  mulWithCarryInt64#,

  addWithCarryWord64#,
  mulWithCarryWord64#,

  -- Operators from Num
  addInt128#,
  mulInt128#,

  addWord128#,
  mulWord128#,

) where

import Data.Int
import Data.Word

import Data.Array.Accelerate.Error

import Data.Array.Accelerate.Internal.BigInt
import Data.Array.Accelerate.Internal.BigWord
import Data.Array.Accelerate.Internal.Orphans.Elt                   ()

import Data.Array.Accelerate.LLVM.CodeGen.Downcast
import Data.Array.Accelerate.LLVM.CodeGen.IR                        ( IR(..), Operands(..) )
import Data.Array.Accelerate.LLVM.CodeGen.Monad                     ( CodeGen, freshName, instr_ )
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import qualified Data.Array.Accelerate.LLVM.CodeGen.Arithmetic      as A
import qualified LLVM.General.AST.Type.Name                         as A
import qualified LLVM.General.AST.Type.Operand                      as A
import qualified LLVM.General.AST.Type.Representation               as A

import LLVM.General.AST.Constant                                    ( Constant(Int) )
import LLVM.General.AST.Instruction                                 hiding ( nsw, nuw )
import LLVM.General.AST.Name
import LLVM.General.AST.Operand
import LLVM.General.AST.Type


-- Primitive instruction wrappers
-- ------------------------------

-- Operations from Num2

addWithCarryInt64# :: IRFun1 arch () ((Int64, Int64) -> (Int64, Word64))
addWithCarryInt64# = IRFun1 $ A.uncurry (prim_wideningInt64 (Add nsw nuw))

mulWithCarryInt64# :: IRFun1 arch () ((Int64, Int64) -> (Int64, Word64))
mulWithCarryInt64# = IRFun1 $ A.uncurry (prim_wideningInt64 (Mul nsw nuw))

addWithCarryWord64# :: IRFun1 arch () ((Word64, Word64) -> (Word64, Word64))
addWithCarryWord64# = IRFun1 $ A.uncurry (prim_wideningWord64 (Add nsw nuw))

mulWithCarryWord64# :: IRFun1 arch () ((Word64, Word64) -> (Word64, Word64))
mulWithCarryWord64# = IRFun1 $ A.uncurry (prim_wideningWord64 (Mul nsw nuw))


prim_wideningInt64 :: (Operand -> Operand -> InstructionMetadata -> Instruction) -> IR Int64 -> IR Int64 -> CodeGen (IR (Int64, Word64))
prim_wideningInt64 op (IR (OP_Int64 x)) (IR (OP_Int64 y)) = do
  a     <- instr i128 (SExt (downcast x) i128 md)
  b     <- instr i128 (SExt (downcast y) i128 md)
  c     <- instr i128 (op a b md)
  (d,e) <- unpackInt128 c
  return . IR $ OP_Pair (OP_Pair OP_Unit (upcastInt64 d)) (upcastWord64 e)

prim_wideningWord64 :: (Operand -> Operand -> InstructionMetadata -> Instruction) -> IR Word64 -> IR Word64 -> CodeGen (IR (Word64, Word64))
prim_wideningWord64 op (IR (OP_Word64 x)) (IR (OP_Word64 y)) = do
  a     <- instr i128 (ZExt (downcast x) i128 md)
  b     <- instr i128 (ZExt (downcast y) i128 md)
  c     <- instr i128 (op a b md)
  (d,e) <- unpackWord128 c
  return . IR $ OP_Pair (OP_Pair OP_Unit (upcastWord64 d)) (upcastWord64 e)


-- Operations from Num

addInt128# :: IRFun1 arch () ((Int128, Int128) -> Int128)
addInt128# = IRFun1 $ A.uncurry (prim_binaryInt128 (Add nsw nuw))

mulInt128# :: IRFun1 arch () ((Int128, Int128) -> Int128)
mulInt128# = IRFun1 $ A.uncurry (prim_binaryInt128 (Mul nsw nuw))

addWord128# :: IRFun1 arch () ((Int128, Int128) -> Int128)
addWord128# = IRFun1 $ A.uncurry (prim_binaryInt128 (Add nsw nuw))

mulWord128# :: IRFun1 arch () ((Word128, Word128) -> Word128)
mulWord128# = IRFun1 $ A.uncurry (prim_binaryWord128 (Mul nsw nuw))


prim_binaryWord128 :: (Operand -> Operand -> InstructionMetadata -> Instruction) -> IR Word128 -> IR Word128 -> CodeGen (IR Word128)
prim_binaryWord128 op xx yy
  | IR (OP_Pair (OP_Pair OP_Unit (OP_Word64 xh)) (OP_Word64 xl)) <- xx
  , IR (OP_Pair (OP_Pair OP_Unit (OP_Word64 yh)) (OP_Word64 yl)) <- yy
  = do
      x'      <- packWord128 (downcast xh) (downcast xl)
      y'      <- packWord128 (downcast yh) (downcast yl)
      r       <- instr i128 (op x' y' md)
      (hi,lo) <- unpackWord128 r
      return . IR $ OP_Pair (OP_Pair OP_Unit (upcastWord64 hi)) (upcastWord64 lo)

prim_binaryInt128 :: (Operand -> Operand -> InstructionMetadata -> Instruction) -> IR Int128 -> IR Int128 -> CodeGen (IR Int128)
prim_binaryInt128 op xx yy
  | IR (OP_Pair (OP_Pair OP_Unit (OP_Int64 xh)) (OP_Word64 xl)) <- xx
  , IR (OP_Pair (OP_Pair OP_Unit (OP_Int64 yh)) (OP_Word64 yl)) <- yy
  = do
      x'      <- packInt128 (downcast xh) (downcast xl)
      y'      <- packInt128 (downcast yh) (downcast yl)
      r       <- instr i128 (op x' y' md)
      (hi,lo) <- unpackInt128 r
      return . IR $ OP_Pair (OP_Pair OP_Unit (upcastInt64 hi)) (upcastWord64 lo)


-- Prim
-- ----

nsw :: Bool
nsw = False

nuw :: Bool
nuw = False

md :: InstructionMetadata
md = []

fresh :: CodeGen Name
fresh = downcast <$> freshName

instr :: Type -> Instruction -> CodeGen Operand
instr ty ins = do
  name <- fresh
  instr_ (name := ins)
  return (LocalReference ty name)

packInt128 :: Operand -> Operand -> CodeGen Operand
packInt128 hi lo = do
  a <- instr i128 (SExt hi i128 md)
  b <- instr i128 (Shl  nsw nuw a (ConstantOperand (Int 128 64)) md)
  c <- instr i128 (ZExt lo i128 md)
  d <- instr i128 (Or b c md)
  return d

packWord128 :: Operand -> Operand -> CodeGen Operand
packWord128 hi lo = do
  a <- instr i128 (ZExt hi i128 md)
  b <- instr i128 (Shl  nsw nuw a (ConstantOperand (Int 128 64)) md)
  c <- instr i128 (ZExt lo i128 md)
  d <- instr i128 (Or b c md)
  return d

unpackInt128 :: Operand -> CodeGen (Operand,Operand)
unpackInt128 x = do
  a <- instr i128 (AShr False x (ConstantOperand (Int 128 64)) md)
  b <- instr i64 (Trunc a i64 md)
  c <- instr i64 (Trunc x i64 md)
  return (b,c)

unpackWord128 :: Operand -> CodeGen (Operand,Operand)
unpackWord128 x = do
  a <- instr i128 (LShr False x (ConstantOperand (Int 128 64)) md)
  b <- instr i64 (Trunc a i64 md)
  c <- instr i64 (Trunc x i64 md)
  return (b,c)

upcastInt64 :: Operand -> Operands Int64
upcastInt64 (LocalReference (IntegerType 64) (UnName x)) = OP_Int64 (A.LocalReference A.type' (A.UnName x))
upcastInt64 _ = $internalError "upcastInt64" "expected local reference"

upcastWord64 :: Operand -> Operands Word64
upcastWord64 (LocalReference (IntegerType 64) (UnName x)) = OP_Word64 (A.LocalReference A.type' (A.UnName x))
upcastWord64 _ = $internalError "upcastWord64" "expected local reference"


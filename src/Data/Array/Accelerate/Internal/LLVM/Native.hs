{-# LANGUAGE CPP       #-}
{-# LANGUAGE MagicHash #-}
-- |
-- Module      : Data.Array.Accelerate.Internal.LLVM.Native
-- Copyright   : [2016..2020] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Internal.LLVM.Native (

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

import Data.Array.Accelerate                                        as A
import Data.Array.Accelerate.Sugar.Elt
import Data.Array.Accelerate.Internal.BigInt
import Data.Array.Accelerate.Internal.BigWord
import Data.Array.Accelerate.Internal.Orphans.Elt                   ()

#ifdef ACCELERATE_LLVM_NATIVE_BACKEND
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import Data.Array.Accelerate.LLVM.Native.Foreign                    as A
import qualified Data.Array.Accelerate.Internal.LLVM.Prim           as Prim
#endif


#ifdef ACCELERATE_LLVM_NATIVE_BACKEND
wrap2 :: (Elt a, Elt b, Elt c)
      => String                                       -- name of the operation
      -> IRFun1 Native () (EltR (a, b) -> EltR c)     -- foreign implementation
      -> (Exp a -> Exp b -> Exp c)                    -- fallback implementation
      -> Exp a
      -> Exp b
      -> Exp c
wrap2 str f g = A.curry (foreignExp (ForeignExp str f) (A.uncurry g))
#endif

-- Operations from Num2
-- --------------------

addWithCarryInt64#
    :: (Exp Int64 -> Exp Int64 -> Exp (Int64, Word64))
    -> Exp Int64
    -> Exp Int64
    -> Exp (Int64, Word64)
#ifdef ACCELERATE_LLVM_NATIVE_BACKEND
addWithCarryInt64# = wrap2 "addWithCarryInt64#" Prim.addWithCarryInt64#
#else
addWithCarryInt64# = id
#endif

mulWithCarryInt64#
    :: (Exp Int64 -> Exp Int64 -> Exp (Int64, Word64))
    -> Exp Int64
    -> Exp Int64
    -> Exp (Int64, Word64)
#ifdef ACCELERATE_LLVM_NATIVE_BACKEND
mulWithCarryInt64# = wrap2 "mulWithCarryInt64#" Prim.mulWithCarryInt64#
#else
mulWithCarryInt64# = id
#endif

addWithCarryWord64#
    :: (Exp Word64 -> Exp Word64 -> Exp (Word64, Word64))
    -> Exp Word64
    -> Exp Word64
    -> Exp (Word64, Word64)
#ifdef ACCELERATE_LLVM_NATIVE_BACKEND
addWithCarryWord64# = wrap2 "addWithCarryWord64#" Prim.addWithCarryWord64#
#else
addWithCarryWord64# = id
#endif

mulWithCarryWord64#
    :: (Exp Word64 -> Exp Word64 -> Exp (Word64, Word64))
    -> Exp Word64
    -> Exp Word64
    -> Exp (Word64, Word64)
#ifdef ACCELERATE_LLVM_NATIVE_BACKEND
mulWithCarryWord64# = wrap2 "mulWithCarryWord64#" Prim.mulWithCarryWord64#
#else
mulWithCarryWord64# = id
#endif


-- Operations from Num
-- -------------------

addInt128#
    :: (Exp Int128 -> Exp Int128 -> Exp Int128)
    -> Exp Int128
    -> Exp Int128
    -> Exp Int128
#ifdef ACCELERATE_LLVM_NATIVE_BACKEND
addInt128# = wrap2 "addInt128#" Prim.addInt128#
#else
addInt128# = id
#endif

subInt128#
    :: (Exp Int128 -> Exp Int128 -> Exp Int128)
    -> Exp Int128
    -> Exp Int128
    -> Exp Int128
#ifdef ACCELERATE_LLVM_NATIVE_BACKEND
subInt128# = wrap2 "subInt128#" Prim.subInt128#
#else
subInt128# = id
#endif

mulInt128#
    :: (Exp Int128 -> Exp Int128 -> Exp Int128)
    -> Exp Int128
    -> Exp Int128
    -> Exp Int128
#ifdef ACCELERATE_LLVM_NATIVE_BACKEND
mulInt128# = wrap2 "mulInt128#" Prim.mulInt128#
#else
mulInt128# = id
#endif

addWord128#
    :: (Exp Word128 -> Exp Word128 -> Exp Word128)
    -> Exp Word128
    -> Exp Word128
    -> Exp Word128
#ifdef ACCELERATE_LLVM_NATIVE_BACKEND
addWord128# = wrap2 "addWord128#" Prim.addWord128#
#else
addWord128# = id
#endif

subWord128#
    :: (Exp Word128 -> Exp Word128 -> Exp Word128)
    -> Exp Word128
    -> Exp Word128
    -> Exp Word128
#ifdef ACCELERATE_LLVM_NATIVE_BACKEND
subWord128# = wrap2 "subWord128#" Prim.subWord128#
#else
subWord128# = id
#endif

mulWord128#
    :: (Exp Word128 -> Exp Word128 -> Exp Word128)
    -> Exp Word128
    -> Exp Word128
    -> Exp Word128
#ifdef ACCELERATE_LLVM_NATIVE_BACKEND
mulWord128# = wrap2 "mulWord128#" Prim.mulWord128#
#else
mulWord128# = id
#endif


-- Operations from Integral
-- ------------------------

quotInt128#
    :: (Exp Int128 -> Exp Int128 -> Exp Int128)
    -> Exp Int128
    -> Exp Int128
    -> Exp Int128
#ifdef ACCELERATE_LLVM_NATIVE_BACKEND
quotInt128# = wrap2 "quotInt128#" Prim.quotInt128#
#else
quotInt128# = id
#endif

remInt128#
    :: (Exp Int128 -> Exp Int128 -> Exp Int128)
    -> Exp Int128
    -> Exp Int128
    -> Exp Int128
#ifdef ACCELERATE_LLVM_NATIVE_BACKEND
remInt128# = wrap2 "remInt128#" Prim.remInt128#
#else
remInt128# = id
#endif

quotRemInt128#
    :: (Exp Int128 -> Exp Int128 -> Exp (Int128, Int128))
    -> Exp Int128
    -> Exp Int128
    -> Exp (Int128, Int128)
#ifdef ACCELERATE_LLVM_NATIVE_BACKEND
quotRemInt128# = wrap2 "quotRemInt128#" Prim.quotRemInt128#
#else
quotRemInt128# = id
#endif

quotWord128#
    :: (Exp Word128 -> Exp Word128 -> Exp Word128)
    -> Exp Word128
    -> Exp Word128
    -> Exp Word128
#ifdef ACCELERATE_LLVM_NATIVE_BACKEND
quotWord128# = wrap2 "quotWord128#" Prim.quotWord128#
#else
quotWord128# = id
#endif

remWord128#
    :: (Exp Word128 -> Exp Word128 -> Exp Word128)
    -> Exp Word128
    -> Exp Word128
    -> Exp Word128
#ifdef ACCELERATE_LLVM_NATIVE_BACKEND
remWord128# = wrap2 "remWord128#" Prim.remWord128#
#else
remWord128# = id
#endif

quotRemWord128#
    :: (Exp Word128 -> Exp Word128 -> Exp (Word128, Word128))
    -> Exp Word128
    -> Exp Word128
    -> Exp (Word128, Word128)
#ifdef ACCELERATE_LLVM_NATIVE_BACKEND
quotRemWord128# = wrap2 "quotRemWord128#" Prim.quotRemWord128#
#else
quotRemWord128# = id
#endif


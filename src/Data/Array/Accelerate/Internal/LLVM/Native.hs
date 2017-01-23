{-# LANGUAGE CPP       #-}
{-# LANGUAGE MagicHash #-}
-- |
-- Module      : Data.Array.Accelerate.Internal.LLVM.Native
-- Copyright   : [2016] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Internal.LLVM.Native (

  addWithCarryInt64#,
  mulWithCarryInt64#,

  addWithCarryWord64#,
  mulWithCarryWord64#,

) where

import Data.Array.Accelerate                                        as A
import Data.Array.Accelerate.Internal.Orphans.Elt                   ()

#ifdef ACCELERATE_LLVM_NATIVE_BACKEND
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import Data.Array.Accelerate.LLVM.Native.Foreign                    as A
import qualified Data.Array.Accelerate.Internal.LLVM.Prim           as Prim
#endif


#ifdef ACCELERATE_LLVM_NATIVE_BACKEND
wrap2 :: (Elt a, Elt b, Elt c)
      => String                                      -- name of the operation
      -> IRFun1 Native () ((a, b) -> c)              -- foreign implementation
      -> (Exp a -> Exp b -> Exp c)                   -- fallback implementation
      -> Exp a
      -> Exp b
      -> Exp c
wrap2 str f g = A.curry (foreignExp (ForeignExp str f) (A.uncurry g))
#endif

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


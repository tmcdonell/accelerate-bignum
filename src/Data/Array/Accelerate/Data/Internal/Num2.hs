{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE UnboxedTuples       #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Data.Internal.Num2
-- Copyright   : [2016] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

#include "MachDeps.h"

module Data.Array.Accelerate.Data.Internal.Num2 ( Num2(..) )
  where

import Data.Bits
import Data.Int
import Data.Word
import Prelude

import Data.Array.Accelerate                                        ( Exp )
import qualified Data.Array.Accelerate                              as A
import qualified Data.Array.Accelerate.Data.Bits                    as A

#if UNBOXED_TUPLES
import GHC.Prim                                                     ( plusWord2#, timesWord2# )
#if WORD_SIZE_IN_BITS == 32
import GHC.Word                                                     ( Word32(..) )
#endif
#if WORD_SIZE_IN_BITS == 64
import GHC.Word                                                     ( Word64(..) )
#endif
#endif


-- | Addition and multiplication with carry
--
class Num2 w where
  type Signed   w
  type Unsigned w
  --
  signed        :: w -> Signed w
  unsigned      :: w -> Unsigned w
  addWithCarry  :: w -> w -> (w, Unsigned w)
  mulWithCarry  :: w -> w -> (w, Unsigned w)


-- Base
-- ----

instance Num2 Int8 where
  type Signed   Int8 = Int8
  type Unsigned Int8 = Word8
  --
  signed       = id
  unsigned     = fromIntegral
  addWithCarry = defaultUnwrapped ((+) :: Int16 -> Int16 -> Int16)
  mulWithCarry = defaultUnwrapped ((*) :: Int16 -> Int16 -> Int16)

instance Num2 Word8 where
  type Signed   Word8 = Int8
  type Unsigned Word8 = Word8
  --
  signed       = fromIntegral
  unsigned     = id
  addWithCarry = defaultUnwrapped ((+) :: Word16 -> Word16 -> Word16)
  mulWithCarry = defaultUnwrapped ((*) :: Word16 -> Word16 -> Word16)

instance Num2 Int16 where
  type Signed   Int16 = Int16
  type Unsigned Int16 = Word16
  --
  signed       = id
  unsigned     = fromIntegral
  addWithCarry = defaultUnwrapped ((+) :: Int32 -> Int32 -> Int32)
  mulWithCarry = defaultUnwrapped ((*) :: Int32 -> Int32 -> Int32)

instance Num2 Word16 where
  type Signed   Word16 = Int16
  type Unsigned Word16 = Word16
  --
  signed       = fromIntegral
  unsigned     = id
  addWithCarry = defaultUnwrapped ((+) :: Word32 -> Word32 -> Word32)
  mulWithCarry = defaultUnwrapped ((*) :: Word32 -> Word32 -> Word32)

instance Num2 Int32 where
  type Signed   Int32 = Int32
  type Unsigned Int32 = Word32
  --
  signed       = id
  unsigned     = fromIntegral
  addWithCarry = defaultUnwrapped ((+) :: Int64 -> Int64 -> Int64)
  mulWithCarry = defaultUnwrapped ((*) :: Int64 -> Int64 -> Int64)

instance Num2 Word32 where
  type Signed   Word32 = Int32
  type Unsigned Word32 = Word32
  --
  signed       = fromIntegral
  unsigned     = id
#if UNBOXED_TUPLES && WORD_SIZE_IN_BITS == 32
  addWithCarry (W32# x#) (W32# y#) = case plusWord2#  x# y# of (# hi#, lo# #) -> (W32# hi#, W32# lo#)
  mulWithCarry (W32# x#) (W32# y#) = case timesWord2# x# y# of (# hi#, lo# #) -> (W32# hi#, W32# lo#)
#else
  addWithCarry = defaultUnwrapped ((+) :: Word64 -> Word64 -> Word64)
  mulWithCarry = defaultUnwrapped ((*) :: Word64 -> Word64 -> Word64)
#endif

instance Num2 Int64 where
  type Signed   Int64 = Int64
  type Unsigned Int64 = Word64
  --
  signed       = id
  unsigned     = fromIntegral
  addWithCarry x y = hi `seq` lo `seq` (hi,lo)
    where
      extX      = if x < 0 then maxBound else 0
      extY      = if y < 0 then maxBound else 0
      (hi',lo)  = unsigned x `addWithCarry` unsigned y
      hi        = signed (hi' + extX + extY)

  mulWithCarry x y = hi `seq` lo `seq` (hi,lo)
    where
      extX      = if x < 0 then negate y else 0
      extY      = if y < 0 then negate x else 0
      (hi',lo)  = unsigned x `mulWithCarry` unsigned y
      hi        = signed hi' + extX + extY

instance Num2 Word64 where
  type Signed   Word64 = Int64
  type Unsigned Word64 = Word64
  --
  signed       = fromIntegral
  unsigned     = id
#if UNBOXED_TUPLES && WORD_SIZE_IN_BITS == 64
  addWithCarry (W64# x#) (W64# y#) = case plusWord2#  x# y# of (# hi#, lo# #) -> (W64# hi#, W64# lo#)
  mulWithCarry (W64# x#) (W64# y#) = case timesWord2# x# y# of (# hi#, lo# #) -> (W64# hi#, W64# lo#)
#else
  addWithCarry x y = (hi,lo)
    where
      !lo             = x + y
      !hi | lo < x    = 1
          | otherwise = 0
  --
  mulWithCarry x y = (hi,lo)
    where
      xHi         = shiftR x 32
      yHi         = shiftR y 32
      xLo         = x .&. 0xFFFFFFFF
      yLo         = y .&. 0xFFFFFFFF
      hi0         = xHi * yHi
      lo0         = xLo * yLo
      p1          = xHi * yLo
      p2          = xLo * yHi
      (uHi1, uLo) = addWithCarry (fromIntegral p1) (fromIntegral p2)
      (uHi2, lo') = addWithCarry (fromIntegral (shiftR lo0 32)) uLo
      !hi         = hi0 + fromIntegral (uHi1::Word32) + fromIntegral uHi2 + shiftR p1 32 + shiftR p2 32
      !lo         = shiftL (fromIntegral lo') 32 .|. (lo0 .&. 0xFFFFFFFF)
#endif

{-# INLINE defaultUnwrapped #-}
defaultUnwrapped
    :: (FiniteBits w, Bits ww, Integral w, Integral ww, Integral (Unsigned w))
    => (ww -> ww -> ww)
    -> w
    -> w
    -> (w, Unsigned w)
defaultUnwrapped op x y = (hi, lo)
  where
    !r  = fromIntegral x `op` fromIntegral y
    !lo = fromIntegral r
    !hi = fromIntegral (shiftR r (finiteBitSize x))



-- Accelerate
-- ----------

instance Num2 (Exp Int8) where
  type Signed   (Exp Int8) = Exp Int8
  type Unsigned (Exp Int8) = Exp Word8
  --
  signed       = id
  unsigned     = A.fromIntegral
  addWithCarry = defaultUnwrapped' ((+) :: Exp Int16 -> Exp Int16 -> Exp Int16)
  mulWithCarry = defaultUnwrapped' ((*) :: Exp Int16 -> Exp Int16 -> Exp Int16)

instance Num2 (Exp Word8) where
  type Signed   (Exp Word8) = Exp Int8
  type Unsigned (Exp Word8) = Exp Word8
  --
  signed       = A.fromIntegral
  unsigned     = id
  addWithCarry = defaultUnwrapped' ((+) :: Exp Word16 -> Exp Word16 -> Exp Word16)
  mulWithCarry = defaultUnwrapped' ((*) :: Exp Word16 -> Exp Word16 -> Exp Word16)

instance Num2 (Exp Int16) where
  type Signed   (Exp Int16) = Exp Int16
  type Unsigned (Exp Int16) = Exp Word16
  --
  signed       = id
  unsigned     = A.fromIntegral
  addWithCarry = defaultUnwrapped' ((+) :: Exp Int32 -> Exp Int32 -> Exp Int32)
  mulWithCarry = defaultUnwrapped' ((*) :: Exp Int32 -> Exp Int32 -> Exp Int32)

instance Num2 (Exp Word16) where
  type Signed   (Exp Word16) = Exp Int16
  type Unsigned (Exp Word16) = Exp Word16
  --
  signed       = A.fromIntegral
  unsigned     = id
  addWithCarry = defaultUnwrapped' ((+) :: Exp Word32 -> Exp Word32 -> Exp Word32)
  mulWithCarry = defaultUnwrapped' ((*) :: Exp Word32 -> Exp Word32 -> Exp Word32)

instance Num2 (Exp Int32) where
  type Signed   (Exp Int32) = Exp Int32
  type Unsigned (Exp Int32) = Exp Word32
  --
  signed       = id
  unsigned     = A.fromIntegral
  addWithCarry = defaultUnwrapped' ((+) :: Exp Int64 -> Exp Int64 -> Exp Int64)
  mulWithCarry = defaultUnwrapped' ((*) :: Exp Int64 -> Exp Int64 -> Exp Int64)

instance Num2 (Exp Word32) where
  type Signed   (Exp Word32) = Exp Int32
  type Unsigned (Exp Word32) = Exp Word32
  --
  signed       = A.fromIntegral
  unsigned     = id
  addWithCarry = defaultUnwrapped' ((+) :: Exp Word64 -> Exp Word64 -> Exp Word64)
  mulWithCarry = defaultUnwrapped' ((*) :: Exp Word64 -> Exp Word64 -> Exp Word64)

instance Num2 (Exp Int64) where
  type Signed   (Exp Int64) = Exp Int64
  type Unsigned (Exp Int64) = Exp Word64
  --
  signed        = id
  unsigned      = A.fromIntegral
  addWithCarry x y = (hi,lo)
    where
      extX      = x A.< 0 A.? (maxBound, 0)
      extY      = y A.< 0 A.? (maxBound, 0)
      (hi',lo)  = unsigned x `addWithCarry` unsigned y
      hi        = signed (hi' + extX + extY)

  mulWithCarry x y = (hi,lo)
    where
      extX      = x A.< 0 A.? (negate y, 0)
      extY      = y A.< 0 A.? (negate x, 0)
      (hi',lo)  = unsigned x `mulWithCarry` unsigned y
      hi        = signed hi' + extX + extY

instance Num2 (Exp Word64) where
  type Signed   (Exp Word64) = Exp Int64
  type Unsigned (Exp Word64) = Exp Word64
  --
  signed       = A.fromIntegral
  unsigned     = id
  addWithCarry x y = (hi,lo)
    where
      lo = x + y
      hi = lo A.< x A.? (1,0)

  mulWithCarry x y = (hi,lo)
    where
      xHi         = A.shiftR x 32
      yHi         = A.shiftR y 32
      xLo         = x A..&. 0xFFFFFFFF
      yLo         = y A..&. 0xFFFFFFFF
      hi0         = xHi * yHi
      lo0         = xLo * yLo
      p1          = xHi * yLo
      p2          = xLo * yHi
      (uHi1, uLo) = addWithCarry (A.fromIntegral p1) (A.fromIntegral p2)
      (uHi2, lo') = addWithCarry (A.fromIntegral (A.shiftR lo0 32)) uLo
      hi          = hi0 + A.fromIntegral (uHi1::Exp Word32) + A.fromIntegral uHi2 + A.shiftR p1 32 + A.shiftR p2 32
      lo          = A.shiftL (A.fromIntegral lo') 32 A..|. (lo0 A..&. 0xFFFFFFFF)


defaultUnwrapped'
    :: ( A.FiniteBits w, A.Bits ww, A.Integral w, A.Integral ww
       , A.FromIntegral w ww, A.FromIntegral ww w, A.FromIntegral ww w', Unsigned (Exp w) ~ Exp w'
       )
    => (Exp ww -> Exp ww -> Exp ww)
    -> Exp w
    -> Exp w
    -> (Exp w, Unsigned (Exp w))
defaultUnwrapped' op x y = (hi, lo)
  where
    r  = A.fromIntegral x `op` A.fromIntegral y
    lo = A.fromIntegral r
    hi = A.fromIntegral (r `A.shiftR` A.finiteBitSize x)


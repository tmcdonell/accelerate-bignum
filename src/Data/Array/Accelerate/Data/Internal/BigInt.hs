{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
-- |
-- Module      : Data.Array.Accelerate.Data.Internal.BigInt
-- Copyright   : [2016] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Fixed length signed integer types
--

-- Based on the following (BSD3) projects:
--  * https://github.com/mvv/data-bword
--  * https://github.com/mvv/data-dword
--

module Data.Array.Accelerate.Data.Internal.BigInt (

  Int96,
  Int128,
  Int160,
  Int192,
  Int224,
  Int256,
  Int512,

  BigInt(..)

) where

import Data.Bits
import Data.Int
import Data.Ratio
import Data.Word

import Data.Array.Accelerate.Data.Internal.BigWord
import Data.Array.Accelerate.Data.Internal.Num2


type Int96  = BigInt  Int32  Word64
type Int128 = BigInt  Int64  Word64
type Int160 = BigInt  Int32 Word128
type Int192 = BigInt  Int64 Word128
type Int224 = BigInt  Int32 Word192
type Int256 = BigInt Int128 Word128
type Int512 = BigInt Int256 Word256


-- | Large integers of fixed size represented as separate (signed) high and
-- (unsigned) low words.
--
data BigInt    hi lo = I2 !hi !lo
type BigIntCtx hi lo = (hi ~ Signed hi, lo ~ Unsigned lo, Signed (Unsigned hi) ~ hi)


instance Integral (BigInt a b) => Show (BigInt a b) where
  show = show . toInteger


instance (Bounded a, Bounded b) => Bounded (BigInt a b) where
  minBound = I2 minBound minBound
  maxBound = I2 maxBound maxBound


instance (Enum a, Num a, Eq a, Enum b, Num b, Eq b, Bounded b)
    => Enum (BigInt a b) where
  succ (I2 hi lo)
    | lo == maxBound    = I2 (succ hi) minBound
    | otherwise         = I2 hi (succ lo)

  pred (I2 hi lo)
    | lo == minBound    = I2 (pred hi) maxBound
    | otherwise         = I2 hi (pred lo)

  toEnum x
    | x < 0             = I2 (-1) (negate (1 + toEnum (negate (x+1))))
    | otherwise         = I2 0 (toEnum x)

  fromEnum (I2 0 lo)    = fromEnum lo
  fromEnum (I2 (-1) lo) = negate (fromEnum (negate lo))
  fromEnum _            = error "Enum.fromEnum: bad value"


instance (Ord a, Ord b) => Ord (BigInt a b) where
  compare (I2 xh xl) (I2 yh yl) =
    case compare xh yh of
      EQ -> compare xl yl
      r  -> r


instance (Eq a, Eq b) => Eq (BigInt a b) where
  I2 xh xl == I2 yh yl = xh == yh && xl == yl
  I2 xh xl /= I2 yh yl = xh /= yh || xl /= yl


instance ( Integral a, Ord a
         , Integral b, Ord b, Bounded b
         , Ord (BigInt a b)
         , Num (BigInt a b)
         , Num2 (BigInt a b)
         , Num  (BigWord (Unsigned a) b)
         , Num2 (BigWord (Unsigned a) b)
         , BigIntCtx a b
         )
    => Num (BigInt a b) where
  negate (I2 hi lo)
    | lo == 0   = I2 (negate hi) 0
    | otherwise = I2 (negate (hi+1)) (negate lo)

  abs x
    | x < 0     = negate x
    | otherwise = x

  signum (I2 hi lo) =
    case compare hi 0 of
      LT -> I2 (-1) maxBound
      EQ -> if lo == 0 then 0 else 1
      GT -> I2 0 1

  I2 xh xl + I2 yh yl = I2 hi lo
    where
      lo = xl + yl
      hi = xh + yh + if lo < xl then 1 else 0

  x * y = signed (unsigned x * unsigned y)

  fromInteger x = I2 (fromInteger hi) (fromInteger lo)
    where
      (hi,lo) = x `divMod` (toInteger (maxBound::b) + 1)


instance ( Integral a
         , Integral b, Bounded b
         , Integral (BigWord (Unsigned a) b)
         , Num2 (BigInt a b)
         , Num2 (BigWord (Unsigned a) b)
         , BigIntCtx a b
         )
    => Integral (BigInt a b) where
  toInteger (I2 hi lo) =
    toInteger hi * (toInteger (maxBound::b) + 1) + toInteger lo

  quotRem x y =
    if x < 0
      then if y < 0
             then
               let (q,r) = quotRem (negate (unsigned x)) (negate (unsigned y))
               in  (signed q, signed (negate r))
             else
               let (q,r) = quotRem (negate (unsigned x)) (unsigned y)
               in  (signed (negate q), signed (negate r))
      else if y < 0
             then
               let (q,r) = quotRem (unsigned x) (negate (unsigned y))
               in  (signed (negate q), signed r)
             else
               let (q,r) = quotRem (unsigned x) (unsigned y)
               in  (signed q, signed r)

  divMod x y =
    if x < 0
      then if y < 0
             then let (q,r) = quotRem (negate (unsigned x)) (negate (unsigned y))
                  in  (signed q, signed (negate r))
             else let (q,r) = quotRem (negate (unsigned x)) (unsigned y)
                      q'    = signed (negate q)
                      r'    = signed (negate r)
                  in
                  if r == 0 then (q', r')
                            else (q'-1, r'+y)
      else if y < 0
             then let (q,r) = quotRem (unsigned x) (negate (unsigned y))
                      q'    = signed (negate q)
                      r'    = signed r
                  in
                  if r == 0
                    then (q', r')
                    else (q'-1, r'+y)
             else let (q,r) = quotRem (unsigned x) (unsigned y)
                  in  (signed q, signed r)


instance (Integral (BigInt a b), Num (BigInt a b), Ord (BigInt a b))
    => Real (BigInt a b) where
  toRational x = toInteger x % 1


instance ( Ord a
         , Num a
         , Num2 a
         , Num (BigInt a b)
         , Ord (BigInt a b)
         , Num2 (BigInt a b)
         , Bits (BigInt a b)
         , Num  (BigWord (Unsigned a) b)
         , Num2 (BigWord (Unsigned a) b)
         , Bounded (BigWord (Unsigned a) b)
         , BigIntCtx a b
         , Unsigned (Unsigned a) ~ Unsigned a
         )
    => Num2 (BigInt a b) where
  type Signed   (BigInt a b) = BigInt (Signed a) b
  type Unsigned (BigInt a b) = BigWord (Unsigned a) b
  --
  signed              = id
  unsigned (I2 hi lo) = W2 (unsigned hi) lo
  --
  addWithCarry x y = (c, r)
    where
      t1      = if x < 0 then maxBound else minBound
      t2      = if y < 0 then maxBound else minBound
      (t3, r) = addWithCarry (unsigned x) (unsigned y)
      c       = signed (t1+t2+t3)

  mulWithCarry x@(I2 xh _) y@(I2 yh _) = (hi,lo)
    where
      t1        = complement y + 1
      t2        = complement x + 1
      (t3, lo)  = mulWithCarry (unsigned x) (unsigned y)
      t4        = signed t3
      hi        = if xh < 0
                    then if yh < 0
                           then t4 + t1 + t2
                           else t4 + t1
                    else if yh < 0
                           then t4 + t2
                           else t4


instance ( FiniteBits a, Integral a
         , FiniteBits b, Integral b
         , FiniteBits (BigInt a b)
         , Num2 (BigInt a b)
         , Num2 (BigWord (Unsigned a) b)
         , Bits (BigWord (Unsigned a) b)
         , Integral (Signed b), Bits (Signed b)
         , BigIntCtx a b
         )
    => Bits (BigInt a b) where
  isSigned _   = True
  bitSize      = finiteBitSize
  bitSizeMaybe = Just . finiteBitSize

  I2 xh xl .&. I2 yh yl   = I2 (xh .&. yh) (xl .&. yl)
  I2 xh xl .|. I2 yh yl   = I2 (xh .|. yh) (xl .|. yl)
  I2 xh xl `xor` I2 yh yl = I2 (xh `xor` yh) (xl `xor` yl)
  complement (I2 hi lo)   = I2 (complement hi) (complement lo)

  shiftL (I2 hi lo) x
    | y > 0     = I2 (shiftL hi x .|. fromIntegral (shiftR lo y)) (shiftL lo x)
    | otherwise = I2 (fromIntegral (shiftL lo (negate y))) 0
    where
      y = finiteBitSize (undefined::b) - x

  shiftR (I2 hi lo) x = I2 hi' lo'
    where
      hi' = shiftR hi x
      lo' | y >= 0    = shiftL (fromIntegral hi) y .|. shiftR lo x
          | otherwise = z

      y = finiteBitSize (undefined::b) - x
      z = fromIntegral (shiftR (fromIntegral hi :: Signed b) (negate y))

  rotateL x y = signed (rotateL (unsigned x) y)
  rotateR x y = rotateL x (finiteBitSize (undefined::BigInt a b) - y)

  bit n
    | m >= 0    = I2 (bit m) 0
    | otherwise = I2 0 (bit n)
    where
      m = n - finiteBitSize (undefined::b)

  testBit (I2 hi lo) n
    | m >= 0    = testBit hi m
    | otherwise = testBit lo n
    where
      m = n - finiteBitSize (undefined::b)

  setBit (I2 hi lo) n
    | m >= 0    = I2 (setBit hi m) lo
    | otherwise = I2 hi (setBit lo n)
    where
      m = n - finiteBitSize (undefined::b)

  clearBit (I2 hi lo) n
    | m >= 0    = I2 (clearBit hi m) lo
    | otherwise = I2 hi (clearBit lo n)
    where
      m = n - finiteBitSize (undefined::b)

  complementBit (I2 hi lo) n
    | m >= 0    = I2 (complementBit hi m) lo
    | otherwise = I2 hi (complementBit lo n)
    where
      m = n - finiteBitSize (undefined::b)

  popCount (I2 hi lo) = popCount hi + popCount lo


instance ( FiniteBits a
         , FiniteBits b
         , Bits (BigInt a b)
         , Num2 (BigInt a b)
         , FiniteBits (BigWord (Unsigned a) b)
         , BigIntCtx a b
         )
    => FiniteBits (BigInt a b) where
  finiteBitSize _ = finiteBitSize (undefined::a)
                  + finiteBitSize (undefined::b)

  countLeadingZeros  = countLeadingZeros . unsigned
  countTrailingZeros = countTrailingZeros . unsigned


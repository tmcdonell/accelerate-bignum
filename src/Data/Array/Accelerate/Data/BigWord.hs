{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
-- |
-- Module      : Data.Array.Accelerate.Data.BigWord
-- Copyright   : [2016] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Fixed length unsigned word types.

-- Based on the following (BSD3) projects:
--  * https://github.com/mvv/data-bword
--  * https://github.com/mvv/data-dword
--

module Data.Array.Accelerate.Data.BigWord (

  Word96,
  Word128,
  Word160,
  Word192,
  Word224,
  Word256,
  Word512,

  -- Internals
  BigWord(..)

) where

import Data.Bits
import Data.Ratio
import Data.Word
import Prelude

import Data.Array.Accelerate.Data.Internal.Num2


type Word96  = BigWord  Word32  Word64
type Word128 = BigWord  Word64  Word64
type Word160 = BigWord  Word32 Word128
type Word192 = BigWord  Word64 Word128
type Word224 = BigWord  Word32 Word192
type Word256 = BigWord Word128 Word128
type Word512 = BigWord Word256 Word256


-- | Large word of fixed size represented as separate high and low (unsigned)
-- words.
--
data BigWord hi lo = W2 !hi !lo

-- TLM: This generic setup allows us to define instances recursively, but for
--      better performance in pure Haskell, specialised instances with unpacked
--      fields (esp for >128 bits) would probably be better. This makes no
--      difference for Accelerate though which is unboxed and hyper strict.


instance Integral (BigWord a b) => Show (BigWord a b) where
  show = show . toInteger


instance (Bounded a, Bounded b) => Bounded (BigWord a b) where
  minBound = W2 minBound minBound
  maxBound = W2 maxBound maxBound


instance (Num a, Enum a, Bits a, Num b, Enum b, Bounded b, Eq b)
    => Enum (BigWord a b) where
  succ (W2 hi lo)
    | lo == maxBound  = W2 (succ hi) minBound
    | otherwise       = W2 hi (succ lo)
  pred (W2 hi lo)
    | lo == minBound  = W2 (pred hi) maxBound
    | otherwise       = W2 hi (pred lo)
  toEnum x
    | x < 0           = error "Enum.toEnum: negative value"
    | otherwise       = W2 0 (toEnum x)

  fromEnum (W2 0 lo)  = fromEnum lo
  fromEnum _          = error "Enum.fromEnum: bad value"


instance ( Num a, Ord a, Bits a,  Num2 a, a ~ Unsigned a
         , Integral b, Bounded b, Num2 b, b ~ Unsigned b
         )
    => Num (BigWord a b) where
  negate (W2 hi lo)
    | lo == 0         = W2 (negate hi)     0
    | otherwise       = W2 (negate (hi+1)) (negate lo)

  abs                 = id

  signum (W2 0 0)     = W2 0 0
  signum _            = W2 0 1

  W2 xh xl + W2 yh yl = W2 hi lo
    where
      lo = xl + yl
      hi = xh + yh + if lo < xl then 1
                                else 0

  W2 xh xl * W2 yh yl = W2 hi lo
    where
      hi      = xh * fromIntegral yl + yh * fromIntegral xl + fromIntegral c
      (c,lo)  = mulWithCarry xl yl

  fromInteger x = W2 (fromInteger hi) (fromInteger lo)
    where
      (hi,lo) = x `divMod` (toInteger (maxBound :: b) + 1)


instance (Ord a, Ord b) => Ord (BigWord a b) where
  compare (W2 xh xl) (W2 yh yl) =
    case compare xh yh of
      EQ -> compare xl yl
      r  -> r


instance (Eq a, Eq b) => Eq (BigWord a b) where
  W2 xh xl == W2 yh yl = xh == yh && xl == yl
  W2 xh xl /= W2 yh yl = xh /= yh || xl /= yl


instance Integral (BigWord a b) => Real (BigWord a b) where
  toRational x = toInteger x % 1


instance ( Integral a, FiniteBits a, Num2 a, Bounded a, a ~ Unsigned a
         , Integral b, FiniteBits b, Num2 b, Bounded b, b ~ Unsigned b
         )
    => Integral (BigWord a b) where
  toInteger (W2 hi lo) =
    toInteger hi * (toInteger (maxBound :: b) + 1) + toInteger lo

  divMod = quotRem

  quotRem x@(W2 xh xl) y@(W2 yh yl)
    | yh == 0 && yl == 0  = error "divide by zero"
    | otherwise           =
        case compare xh yh of
          LT -> (0, x)
          EQ -> case compare xl yl of
                  LT            -> (0, x)
                  EQ            -> (1, 0)
                  GT | yh == 0  ->
                    let (t2, t1) = quotRem xl yl
                    in (W2 0 t2, W2 0 t1)
                  GT            -> (1, W2 0 (xl - yl))

          GT | yl == 0
             -> let (t2, t1) = quotRem xh yh
                in  (W2 0 (fromIntegral t2), W2 (fromIntegral t1) xl)

          GT | yh == 0 && yl == maxBound
             -> let z        = fromIntegral xh
                    (t2, t1) = addWithCarry z xl
                in
                if t2 == 0
                  then if t1 == maxBound
                         then ((W2 0 z) + 1, 0)
                         else (W2 0 z, W2 0 t1)
                  else if t1 == maxBound
                         then ((W2 0 z) + 2, 1)
                         else if t1 == xor maxBound 1
                                then ((W2 0 z) + 2, 0)
                                else ((W2 0 z) + 1, W2 0 (t1 + 1))


          GT | yh == 0
             -> let (t2, t1) = div1 xh xl yl
                in  (t2, W2 0 t1)

          GT | t1 == t2  -> (1, x - y)
             | otherwise -> (W2 0 (fromIntegral q2), shiftR r2 t2)
             where
               t1              = countLeadingZeros xh
               t2              = countLeadingZeros yh
               z               = shiftR xh (finiteBitSize (undefined::a) - t2)
               W2 hhh hll      = shiftL x t2
               v@(W2 lhh lll)  = shiftL y t2
               -- z hhh hll / lhh lll
               ((0, q1), r1)   = div2 z hhh lhh
               (t4, t3)        = mulWithCarry (fromIntegral q1) lll
               t5              = W2 (fromIntegral t4) t3
               t6              = W2 r1 hll
               (t8, t7)        = addWithCarry t6 v
               (t10, t9)       = addWithCarry t7 v
               loWord (W2 _ l) = l
               (q2, r2)        =
                 if t5 > t6
                   then if loWord t8 == 0
                          then if t7 >= t5
                                 then (q1 - 1, t7 - t5)
                                 else if loWord t10 == 0
                                        then (q1 - 2, t9 - t5)
                                        else (q1 - 2, (maxBound - t5) + t9 + 1)
                          else (q1 - 1, (maxBound - t5) + t7 + 1)
                   else (q1, t6 - t5)
    where
      div1 hhh hll by = go hhh hll 0
        where
          (t2, t1) = quotRem maxBound by
          go h l c
            | z == 0    = (c + W2 (fromIntegral t8) t7 + W2 0 t10, t9)
            | otherwise = go (fromIntegral z) t5 (c + (W2 (fromIntegral t8) t7))
            where
              h1        = fromIntegral h
              (t4, t3)  = mulWithCarry h1 (t1 + 1)
              (t6, t5)  = addWithCarry t3 l
              z         = t4 + t6
              (t8, t7)  = mulWithCarry h1 t2
              (t10, t9) = quotRem t5 by

      div2 hhh hll by = go hhh hll (0, 0)
        where
          (t2, t1) = quotRem maxBound by
          go h l c
            | z == 0    = (addT (addT c (t8, t7)) (0, t10), t9)
            | otherwise = go z t5 (addT c (t8, t7))
            where
              (t4, t3)  = mulWithCarry h (t1 + 1)
              (t6, t5)  = addWithCarry t3 l
              z         = t4 + t6
              (t8, t7)  = mulWithCarry h t2
              (t10, t9) = quotRem t5 by

              addT (lhh, lhl) (llh, lll) =
                let (t4', t3') = addWithCarry lhl lll
                in  (lhh + llh + t4', t3')


instance ( Integral a, Ord a, FiniteBits a, Num2 a, a ~ Unsigned a
         , Integral b, Ord b, FiniteBits b, Num2 b, b ~ Unsigned b
         )
    => Num2 (BigWord a b) where
  type Signed   (BigWord a b) = BigWord (Signed a) b      -- TLM: convert into BigInt
  type Unsigned (BigWord a b) = BigWord (Unsigned a) b
  --
  signed   (W2 hi lo) = W2 (signed hi) lo
  unsigned            = id
  --
  addWithCarry (W2 xh xl) (W2 yh yl) = (W2 0 w, W2 v u)
    where
      (t1, u)   = addWithCarry xl yl
      (t3, t2)  = addWithCarry xh (fromIntegral t1)
      (t4, v)   = addWithCarry t2 yh
      w         = fromIntegral (t3 + t4)

  mulWithCarry (W2 xh xl) (W2 yh yl) =
      ( W2 (hhh + fromIntegral (shiftR t9 y) + shiftL x z) (shiftL t9 z .|. shiftR t3 y)
      , W2 (fromIntegral t3) lll)
    where
      (llh, lll) = mulWithCarry xl yl
      (hlh, hll) = mulWithCarry (fromIntegral xh) yl
      (lhh, lhl) = mulWithCarry xl (fromIntegral yh)
      (hhh, hhl) = mulWithCarry xh yh
      (t2, t1)   = addWithCarry llh hll
      (t4, t3)   = addWithCarry t1 lhl
      (t6, t5)   = addWithCarry (fromIntegral hhl) (t2 + t4)
      (t8, t7)   = addWithCarry t5 lhh
      (t10, t9)  = addWithCarry t7 hlh
      x          = fromIntegral (t6 + t8 + t10)
      y          = finiteBitSize (undefined::a)
      z          = finiteBitSize (undefined::b) - y


instance ( Integral a, FiniteBits a, a ~ Unsigned a
         , Integral b, FiniteBits b, b ~ Unsigned b
         )
    => Bits (BigWord a b) where
  isSigned _   = False
  bitSize      = finiteBitSize
  bitSizeMaybe = Just . finiteBitSize

  W2 xh xl .&. W2 yh yl   = W2 (xh .&. yh) (xl .&. yl)
  W2 xh xl .|. W2 yh yl   = W2 (xh .|. yh) (xl .|. yl)
  W2 xh xl `xor` W2 yh yl = W2 (xh `xor` yh) (xl `xor` yl)
  complement (W2 hi lo)   = W2 (complement hi) (complement lo)

  shiftL (W2 hi lo) x
    | y > 0     = W2 (shiftL hi x .|. fromIntegral (shiftR lo y)) (shiftL lo x)
    | otherwise = W2 (fromIntegral (shiftL lo (negate y))) 0
    where
      y = finiteBitSize (undefined::b) - x

  shiftR (W2 hi lo) x = W2 hi' lo'
    where
      hi' = shiftR hi x
      lo' | y >= 0    = shiftL (fromIntegral hi) y .|. shiftR lo x
          | otherwise = z

      y   = finiteBitSize (undefined::b) - x
      z   = shiftR (fromIntegral hi) (negate y)

  rotateL (W2 hi lo) x
    | y >= 0    = W2 (fromIntegral (shiftL lo y) .|. shiftR hi z)
                     (shiftL (fromIntegral hi) (finiteBitSize (undefined::b) - z) .|. shiftR lo z)
    | otherwise = W2 (fromIntegral (shiftR lo (negate y)) .|. shiftL hi x)
                     (shift (fromIntegral hi) (finiteBitSize (undefined::b) - z) .|. shiftL lo x .|. shiftR lo z)
    where
      y = x - finiteBitSize (undefined::b)
      z = finiteBitSize (undefined::BigWord a b) - x

  rotateR x y = rotateL x (finiteBitSize (undefined::BigWord a b) - y)

  bit n
    | m >= 0    = W2 (bit m) 0
    | otherwise = W2 0 (bit n)
    where
      m = n - finiteBitSize (undefined::b)

  testBit (W2 hi lo) n
    | m >= 0    = testBit hi m
    | otherwise = testBit lo n
    where
      m = n - finiteBitSize (undefined::b)

  setBit (W2 hi lo) n
    | m >= 0    = W2 (setBit hi m) lo
    | otherwise = W2 hi (setBit lo n)
    where
      m = n - finiteBitSize (undefined::b)

  clearBit (W2 hi lo) n
    | m >= 0    = W2 (clearBit hi m) lo
    | otherwise = W2 hi (clearBit lo n)
    where
      m = n - finiteBitSize (undefined::b)

  complementBit (W2 hi lo) n
    | m >= 0    = W2 (complementBit hi m) lo
    | otherwise = W2 hi (complementBit lo n)
    where
      m = n - finiteBitSize (undefined::b)

  popCount (W2 hi lo) = popCount hi + popCount lo


instance ( Integral a, FiniteBits a, a ~ Unsigned a
         , Integral b, FiniteBits b, b ~ Unsigned b
         )
    => FiniteBits (BigWord a b) where
  finiteBitSize _ = finiteBitSize (undefined::a)
                  + finiteBitSize (undefined::b)

  countLeadingZeros (W2 hi lo)
    | x == wsib = wsib + countLeadingZeros lo
    | otherwise = x
    where
      x     = countLeadingZeros hi
      wsib  = finiteBitSize (undefined::a)

  countTrailingZeros (W2 hi lo)
    | x == wsib = wsib + countTrailingZeros hi
    | otherwise = x
    where
      x     = countTrailingZeros lo
      wsib  = finiteBitSize (undefined::b)


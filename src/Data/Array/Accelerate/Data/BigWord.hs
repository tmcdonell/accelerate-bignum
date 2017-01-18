{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
-- |
-- Module      : Data.Array.Accelerate.Data.BigWord
-- Copyright   : [2016] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Fixed length unsigned word types

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

  -- ** Internals
  BigWord(..)

) where

import Data.Bits
import Data.Ratio
import Data.Word

import Data.Array.Accelerate.Data.Internal.Num2
import {-# SOURCE #-} Data.Array.Accelerate.Data.BigInt

import Data.Array.Accelerate                                        ( (?), Lift(..), Unlift, lift, unlift )
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Product
import Data.Array.Accelerate.Smart
import qualified Data.Array.Accelerate                              as A
import qualified Data.Array.Accelerate.Data.Bits                    as A


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


instance ( Num a, Ord a,                  a ~ Unsigned a
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


instance ( Integral a, FiniteBits a, Num2 a, Bounded a, a ~ Unsigned a
         , Integral b, FiniteBits b, Num2 b, Bounded b, b ~ Unsigned b
         )
    => Real (BigWord a b) where
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
                in  (W2 0 (fromIntegral t2), W2 t1 xl)

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
      div1 :: a -> b -> b -> (BigWord a b, b)
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

      div2 :: a -> a -> a -> ((a,a), a)
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
  type Signed   (BigWord a b) = BigInt (Signed a) b
  type Unsigned (BigWord a b) = BigWord (Unsigned a) b
  --
  signed   (W2 hi lo) = I2 (signed hi) lo
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


-- Accelerate
-- ----------

mkW2 :: (Elt a, Elt b, Elt (BigWord a b)) => Exp a -> Exp b -> Exp (BigWord a b)
mkW2 a b = lift (W2 a b)


instance (Elt (BigWord a b), Bounded a, Bounded b) => Bounded (Exp (BigWord a b)) where
  minBound = constant minBound
  maxBound = constant maxBound


instance (A.Eq a, A.Eq b, Elt (BigWord a b)) => A.Eq (BigWord a b) where
  (unlift -> W2 xh xl) == (unlift -> W2 yh yl) = xh A.== yh A.&& xl A.== yl
  (unlift -> W2 xh xl) /= (unlift -> W2 yh yl) = xh A./= yh A.|| xl A./= yl


instance (A.Ord a, A.Ord b, Elt (BigWord a b)) => A.Ord (BigWord a b) where
  (unlift -> W2 xh xl) <  (unlift -> W2 yh yl) = xh A.== yh ? ( xl A.< yl,  xh A.< yh )
  (unlift -> W2 xh xl) >  (unlift -> W2 yh yl) = xh A.== yh ? ( xl A.< yl,  xh A.< yh )
  (unlift -> W2 xh xl) <= (unlift -> W2 yh yl) = xh A.== yh ? ( xl A.<= yl, xh A.<= yh )
  (unlift -> W2 xh xl) >= (unlift -> W2 yh yl) = xh A.== yh ? ( xl A.>= yl, xh A.>= yh )


instance ( A.Num a,      A.Eq a
         , A.Integral b, A.Eq b, Num2 (Exp b), A.FromIntegral b a, Exp b ~ Unsigned (Exp b)
         , Elt (BigWord a b)
         , Num a, Integral b, Bounded b
         )
    => Num (Exp (BigWord a b)) where
  negate (unlift -> W2 hi lo) =
    lo A.== 0 ? ( mkW2 (negate hi) 0
                , mkW2 (negate (hi+1)) (negate lo)
                )

  abs      = id
  signum x = x A.== 0 ? (0,1)

  (unlift -> W2 xh xl) + (unlift -> W2 yh yl) = lift (W2 hi lo)
    where
      lo = xl + yl
      hi = xh + yh + (lo A.< xl ? (1, 0))

  (unlift -> W2 xh xl) * (unlift -> W2 yh yl) = lift (W2 hi lo)
    where
      hi      = xh * A.fromIntegral yl + yh * A.fromIntegral xl + A.fromIntegral c
      (c,lo)  = mulWithCarry xl yl

  fromInteger x = constant (W2 (fromInteger hi) (fromInteger lo))
    where
      (hi,lo) = x `divMod` (toInteger (maxBound::b) + 1)


instance ( A.Integral a, A.Bounded a, A.FiniteBits a, A.FromIntegral a b, Num2 (Exp a), Exp a ~ Unsigned (Exp a), a ~ Unsigned a
         , A.Integral b, A.Bounded b, A.FiniteBits b, A.FromIntegral b a, Num2 (Exp b), Exp b ~ Unsigned (Exp b), b ~ Unsigned b
         , Elt (BigWord a b)
         , Num a, Bounded a, Integral b, Bounded b
         )
    => Integral (Exp (BigWord a b)) where
  toInteger = error "Prelude.toInteger not supported for Accelerate types"

  divMod = quotRem
  quotRem x y = untup2 $ quotRem' (unlift x) (unlift y)
    where
      quotRem' :: BigWord (Exp a) (Exp b) -> BigWord (Exp a) (Exp b) -> Exp (BigWord a b, BigWord a b)
      quotRem' (W2 xh xl) (W2 yh yl)
        = xh A.<  yh ? ( tup2 (0, x)
        , xh A.== yh ? ( xl A.<  yl ? ( tup2 (0, x)
                       , xl A.== yl ? ( tup2 (1, 0)
                       , {- xl > yl -}  yh A.== 0 ? ( let (t2,t1) = quotRem xl yl
                                                      in  lift (mkW2 0 t2, mkW2 0 t1)
                                                    , tup2 (1, mkW2 0 (xl-yl))
                                                    )
                       ))
        , {- xh > yh -}  yl A.== 0 ? ( let (t2,t1) = quotRem xh yh
                                       in  lift (mkW2 0 (A.fromIntegral t2), W2 t1 xl)
                       , yh A.== 0 A.&& yl A.== maxBound
                                   ? ( let z       = A.fromIntegral xh
                                           (t2,t1) = addWithCarry z xl
                                       in
                                       t2 A.== 0 ?
                                         ( t1 A.== maxBound ?
                                           ( tup2 ((mkW2 0 z) + 1, 0)
                                           , tup2 (mkW2 0 z, mkW2 0 t1)
                                           )
                                         , t1 A.== maxBound ?
                                           ( tup2 ((mkW2 0 z) + 2, 1)
                                           , t1 A.== A.xor maxBound 1 ?
                                               ( tup2 ((mkW2 0 z) + 2, 0)
                                               , tup2 ((mkW2 0 z) + 1, mkW2 0 (t1+1))
                                               )
                                           )
                                         )
                       , yh A.== 0 ? ( let (t2,t1) = untup2 (div1 xh xl yl)
                                       in  tup2 (t2, mkW2 0 t1)
                       , {- otherwise -}
                         let t1         = A.countLeadingZeros xh
                             t2         = A.countLeadingZeros yh
                             z          = A.shiftR xh (A.finiteBitSize (undefined::Exp a) - t2)
                             u          = A.shiftL x t2
                             v          = A.shiftL y t2
                             W2 hhh hll = unlift u  :: BigWord (Exp a) (Exp b)
                             W2 lhh lll = unlift v  :: BigWord (Exp a) (Exp b)
                             -- -- z hhh hll / lhh lll
                             (q1, r1)   = div2 z hhh lhh
                             (t4, t3)   = mulWithCarry (A.fromIntegral q1) lll
                             t5         = mkW2 (A.fromIntegral t4) t3
                             t6         = mkW2 r1 hll
                             (t8, t7)   = addWithCarry t6 v
                             (t10, t9)  = addWithCarry t7 v
                             loWord w   = let W2 _ l = unlift w :: BigWord (Exp a) (Exp b)
                                          in  l
                             qr2        = t5 A.> t6 ?
                                            ( loWord t8 A.== 0 ?
                                              ( t7 A.>= t5 ?
                                                ( tup2 (q1-1, t7-t5)
                                                , loWord t10 A.== 0 ?
                                                  ( tup2 (q1-2, t9-t5)
                                                  , tup2 (q1-2, (maxBound-t5) + t9 + 1)
                                                  )
                                                )
                                              , tup2 (q1-1, (maxBound-t5) + t7 + 1)
                                              )
                                            , tup2 (q1, t6-t5)
                                            )
                             (q2,r2)    = unlift qr2
                         in
                         t1 A.== t2 ? ( tup2 (1, x-y)
                                      , lift (mkW2 0 (A.fromIntegral q2), A.shiftR r2 t2)
                                      )
                       )))
        ))

      -- TLM: This is really unfortunate that we can not share expressions
      --      between each part of the loop ): Maybe LLVM will be smart enough
      --      to share them.
      div1 :: Exp a -> Exp b -> Exp b -> Exp (BigWord a b, b)
      div1 hhh hll by = go hhh hll 0
        where
          go :: Exp a -> Exp b -> Exp (BigWord a b) -> Exp (BigWord a b, b)
          go h l c = uncurry3 after $ A.while (A.not . uncurry3 done) (uncurry3 body) (lift (h,l,c))

          (t2, t1)   = quotRem maxBound by
          done h l _ = z A.== 0
            where
              h1        = A.fromIntegral h
              (t4, t3)  = mulWithCarry h1 (t1 + 1)
              (t6, _t5) = addWithCarry t3 l
              z         = t4 + t6

          body h l c = lift (A.fromIntegral z, t5, c + (mkW2 (A.fromIntegral t8) t7))
            where
              h1        = A.fromIntegral h
              (t4, t3)  = mulWithCarry h1 (t1 + 1)
              (t6, t5)  = addWithCarry t3 l
              z         = t4 + t6
              (t8, t7)  = mulWithCarry h1 t2

          after h l c = lift (c + mkW2 (A.fromIntegral t8) t7 + mkW2 0 t10, t9)
            where
              h1        = A.fromIntegral h
              (_t4, t3) = mulWithCarry h1 (t1 + 1)
              (_t6, t5) = addWithCarry t3 l
              (t8, t7)  = mulWithCarry h1 t2
              (t10, t9) = quotRem t5 by


      div2 :: Exp a -> Exp a -> Exp a -> (Exp a, Exp a)
      div2 hhh hll by = go hhh hll (constant (0,0))
        where
          go :: Exp a -> Exp a -> Exp (a,a) -> (Exp a, Exp a)
          go h l c = uncurry3 after $ A.while (A.not . uncurry3 done) (uncurry3 body) (lift (h,l,c))

          (t2, t1) = quotRem maxBound by

          done :: Exp a -> Exp a -> Exp (a,a) -> Exp Bool
          done h l _ = z A.== 0
            where
              (t4, t3)  = mulWithCarry h (t1 + 1)
              (t6, _t5) = addWithCarry t3 l
              z         = t4 + t6

          body :: Exp a -> Exp a -> Exp (a,a) -> Exp (a, a, (a,a))
          body h l c = lift (z, t5, (addT (unlift c) (t8,t7)))
            where
              (t4, t3)  = mulWithCarry h (t1 + 1)
              (t6, t5)  = addWithCarry t3 l
              z         = t4 + t6
              (t8, t7)  = mulWithCarry h t2

          after :: Exp a -> Exp a -> Exp (a,a) -> (Exp a, Exp a)
          after h l c = (A.snd q, t9)
            where
              (_t4, t3) = mulWithCarry h (t1 + 1)
              (_t6, t5) = addWithCarry t3 l
              (t8, t7)  = mulWithCarry h t2
              (t10, t9) = quotRem t5 by
              q         = addT (unlift (addT (unlift c) (t8, t7))) (0, t10)

          addT :: (Exp a, Exp a) -> (Exp a, Exp a) -> Exp (a,a)
          addT (lhh, lhl) (llh, lll) =
            let (t4', t3') = addWithCarry lhl lll
            in  lift (lhh + llh + t4', t3')

      uncurry3 f (untup3 -> (a,b,c)) = f a b c


instance ( A.Integral a, A.FiniteBits a, Num2 (Exp a), A.FromIntegral a b, Exp a ~ Exp (Unsigned a), Unsigned (Exp a) ~ Exp a
         , A.Integral b, A.FiniteBits b, Num2 (Exp b), A.FromIntegral b a, Exp b ~ Exp (Unsigned b), Unsigned (Exp b) ~ Exp b
         , Elt (BigWord a b)
         )
    => Num2 (Exp (BigWord a b)) where
  type Signed   (Exp (BigWord a b)) = Exp (BigInt (Signed a) b)
  type Unsigned (Exp (BigWord a b)) = Exp (BigWord a b)
  --
  -- signed (unlift -> W2 hi lo) = mkI2 (signed hi) lo
  unsigned                    = id
  --
  addWithCarry (unlift -> W2 xh xl) (unlift -> W2 yh yl) = (mkW2 0 w, mkW2 v u)
    where
      (t1, u)   = addWithCarry xl yl
      (t3, t2)  = addWithCarry xh (A.fromIntegral t1)
      (t4, v)   = addWithCarry t2 yh
      w         = A.fromIntegral (t3 + t4)

  mulWithCarry (unlift -> W2 xh xl) (unlift -> W2 yh yl) =
      ( mkW2 (hhh + A.fromIntegral (A.shiftR t9 y) + A.shiftL x z) (A.shiftL t9 z A..|. A.shiftR t3 y)
      , mkW2 (A.fromIntegral t3) lll)
    where
      (llh, lll) = mulWithCarry xl yl
      (hlh, hll) = mulWithCarry (A.fromIntegral xh) yl
      (lhh, lhl) = mulWithCarry xl (A.fromIntegral yh)
      (hhh, hhl) = mulWithCarry xh yh
      (t2, t1)   = addWithCarry llh hll
      (t4, t3)   = addWithCarry t1 lhl
      (t6, t5)   = addWithCarry (A.fromIntegral hhl) (t2 + t4)
      (t8, t7)   = addWithCarry t5 lhh
      (t10, t9)  = addWithCarry t7 hlh
      x          = A.fromIntegral (t6 + t8 + t10)
      y          = A.finiteBitSize (undefined::Exp a)
      z          = A.finiteBitSize (undefined::Exp b) - y



instance ( A.Integral a, A.FiniteBits a, A.FromIntegral a b, Exp a ~ Exp (Unsigned a)
         , A.Integral b, A.FiniteBits b, A.FromIntegral b a, Exp b ~ Exp (Unsigned b)
         , Elt (BigWord a b)
         )
    => A.Bits (BigWord a b) where

  isSigned _ = constant False

  (unlift -> W2 xh xl) .&.   (unlift -> W2 yh yl) = lift (W2 (xh A..&. yh) (xl A..&. yl))
  (unlift -> W2 xh xl) .|.   (unlift -> W2 yh yl) = lift (W2 (xh A..|. yh) (xl A..|. yl))
  (unlift -> W2 xh xl) `xor` (unlift -> W2 yh yl) = lift (W2 (xh `A.xor` yh) (xl `A.xor` yl))
  complement (unlift -> W2 hi lo) = lift (W2 (A.complement hi) (A.complement lo))

  shiftL (unlift -> W2 hi lo) x =
    y A.> 0 ? ( lift (W2 (A.shiftL hi x A..|. A.fromIntegral (A.shiftR lo y)) (A.shiftL lo x))
              , lift (W2 (A.fromIntegral (A.shiftL lo (A.negate y))) (0::Exp b)) )
    where
      y = A.finiteBitSize (undefined::Exp b) - x

  shiftR (unlift -> W2 hi lo) x = lift (W2 hi' lo')
    where
      hi' = A.shiftR hi x
      lo' = y A.>= 0 ? ( A.shiftL (A.fromIntegral hi) y A..|. A.shiftR lo x
                       , z )

      y   = A.finiteBitSize (undefined::Exp b) - x
      z   = A.shiftR (A.fromIntegral hi) (A.negate y)

  rotateL (unlift -> W2 hi lo) x =
    y A.>= 0 ? ( lift (W2 (A.fromIntegral (A.shiftL lo y) A..|. A.shiftR hi z)
                          (A.shiftL (A.fromIntegral hi) (A.finiteBitSize (undefined::Exp b) - z) A..|. A.shiftR lo z))
               , lift (W2 (fromIntegral (A.shiftR lo (A.negate y)) A..|. A.shiftL hi x)
                          (A.shift (A.fromIntegral hi) (A.finiteBitSize (undefined::Exp b) - z) A..|. A.shiftL lo x A..|. A.shiftR lo z))
               )
    where
      y = x - A.finiteBitSize (undefined::Exp b)
      z = A.finiteBitSize (undefined::Exp (BigWord a b)) - x

  rotateR x y = A.rotateL x (A.finiteBitSize (undefined::Exp (BigWord a b)) - y)

  bit n =
    m A.>= 0 ? ( mkW2 (A.bit m) 0
               , mkW2 0 (A.bit n) )
    where
      m = n - A.finiteBitSize (undefined::Exp b)

  testBit (unlift -> W2 hi lo) n =
    m A.>= 0 ? ( A.testBit hi m, A.testBit lo n )
    where
      m = n - A.finiteBitSize (undefined::Exp b)

  setBit (unlift -> W2 hi lo) n =
    m A.>= 0 ? ( lift (W2 (A.setBit hi m) lo)
               , lift (W2 hi (A.setBit lo n)) )
    where
      m = n - A.finiteBitSize (undefined::Exp b)

  clearBit (unlift -> W2 hi lo) n =
    m A.>= 0 ? ( lift (W2 (A.clearBit hi m) lo)
               , lift (W2 hi (A.clearBit lo n)) )
    where
      m = n - A.finiteBitSize (undefined::Exp b)

  complementBit (unlift -> W2 hi lo) n =
    m A.>= 0 ? ( lift (W2 (A.complementBit hi m) lo)
               , lift (W2 hi (A.complementBit lo n)) )
    where
      m = n - A.finiteBitSize (undefined::Exp b)

  popCount (unlift -> W2 hi lo) = A.popCount hi + A.popCount lo


instance ( A.Integral a, A.FiniteBits a, A.FromIntegral a b, Exp a ~ Exp (Unsigned a)
         , A.Integral b, A.FiniteBits b, A.FromIntegral b a, Exp b ~ Exp (Unsigned b)
         , Elt (BigWord a b)
         )
    => A.FiniteBits (BigWord a b) where
  finiteBitSize _ = A.finiteBitSize (undefined::Exp a)
                  + A.finiteBitSize (undefined::Exp b)

  countLeadingZeros (unlift -> W2 hi lo) =
    hlz A.== wsib ? (wsib + llz, hlz)
    where
      hlz   = A.countLeadingZeros hi
      llz   = A.countLeadingZeros lo
      wsib  = A.finiteBitSize (undefined::Exp a)

  countTrailingZeros (unlift -> W2 hi lo) =
    ltz A.== wsib ? (wsib + htz, ltz)
    where
      ltz   = A.countTrailingZeros lo
      htz   = A.countTrailingZeros hi
      wsib  = A.finiteBitSize (undefined::Exp b)



instance A.FromIntegral Word128 Word32 where
  fromIntegral (unlift -> W2 (_::Exp Word64) lo) = A.fromIntegral lo

instance A.FromIntegral Word32 Word128 where
  fromIntegral x = mkW2 0 (A.fromIntegral x)

instance A.FromIntegral Word128 Word64 where
  fromIntegral (unlift -> W2 (_::Exp Word64) lo) = lo

instance A.FromIntegral Word64 Word128 where
  fromIntegral x = mkW2 0 x

instance A.FromIntegral Word192 Word32 where
  fromIntegral (unlift -> W2 (_::Exp Word64) lo) = A.fromIntegral lo

instance A.FromIntegral Word32 Word192 where
  fromIntegral x = mkW2 0 (A.fromIntegral x)

instance A.FromIntegral Word128 Word128 where
  fromIntegral = id

instance A.FromIntegral Word256 Word256 where
  fromIntegral = id


type instance EltRepr (BigWord a b) = EltRepr (a,b)

instance (Elt a, Elt b, Show (BigWord a b)) => Elt (BigWord a b) where
  eltType _        = eltType (undefined :: (a,b))
  toElt w          = let (a,b) = toElt w in W2 a b
  fromElt (W2 a b) = fromElt (a,b)

instance (cst a, cst b) => IsProduct cst (BigWord a b) where
  type ProdRepr (BigWord a b) = ProdRepr (a,b)
  fromProd cst (W2 a b) = fromProd cst (a,b)
  toProd cst w          = let (a,b) = toProd cst w in W2 a b
  prod cst _            = prod cst (undefined :: (a,b))

instance (Lift Exp a, Lift Exp b, Elt (Plain a), Elt (Plain b), Show (BigWord (Plain a) (Plain b)))
    => Lift Exp (BigWord a b) where
  type Plain (BigWord a b) = BigWord (Plain a) (Plain b)
  lift (W2 a b)            = Exp $ Tuple (NilTup `SnocTup` lift a `SnocTup` lift b)

instance (Elt a, Elt b, Show (BigWord a b)) => Unlift Exp (BigWord (Exp a) (Exp b)) where
  unlift w =
    let a = Exp $ SuccTupIdx ZeroTupIdx `Prj` w
        b = Exp $ ZeroTupIdx `Prj` w
    in
    W2 a b


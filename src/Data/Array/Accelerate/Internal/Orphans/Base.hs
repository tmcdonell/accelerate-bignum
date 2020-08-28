{-# LANGUAGE CPP                   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MagicHash             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.Internal.Orphans.Base
-- Copyright   : [2016..2020] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Orphan instances for BigWord and BigInt for use with Accelerate. In
-- a separate module so that (a) we can use rebindable syntax; and (b) to avoid
-- excessive class constraints by placing instances next to each other.
--

#include "MachDeps.h"

module Data.Array.Accelerate.Internal.Orphans.Base ()
  where

import Data.Array.Accelerate.Internal.BigInt
import Data.Array.Accelerate.Internal.BigWord
import Data.Array.Accelerate.Internal.Num2
import Data.Array.Accelerate.Internal.Orphans.Elt

import qualified Data.Array.Accelerate.Internal.LLVM.Native         as CPU
import qualified Data.Array.Accelerate.Internal.LLVM.PTX            as PTX

import Data.Array.Accelerate                                        as A hiding ( fromInteger )
import Data.Array.Accelerate.Sugar.Elt
import Data.Array.Accelerate.Analysis.Match                         as A
import Data.Array.Accelerate.Data.Bits                              as A
import Data.Array.Accelerate.Smart

import Control.Monad
import Language.Haskell.TH                                          hiding ( Exp )
import Text.Printf
import Unsafe.Coerce
import Prelude                                                      ( id, fromInteger )
import qualified Prelude                                            as P


-- BigWord
-- -------

type BigWordCtx hi lo =
    ( Elt hi, Elt lo, Elt (BigWord hi lo)
    , hi ~ Unsigned hi
    , lo ~ Unsigned lo
    , Exp hi ~ Unsigned (Exp hi)
    , Exp lo ~ Unsigned (Exp lo)
    )


instance (Bounded a, Bounded b, Elt (BigWord a b)) => P.Bounded (Exp (BigWord a b)) where
  minBound = W2_ minBound minBound
  maxBound = W2_ maxBound maxBound


instance (Eq a, Eq b, Elt (BigWord a b)) => Eq (BigWord a b) where
  W2_ xh xl == W2_ yh yl = xh == yh && xl == yl
  W2_ xh xl /= W2_ yh yl = xh /= yh || xl /= yl


instance (Ord a, Ord b, Elt (BigWord a b)) => Ord (BigWord a b) where
  W2_ xh xl <  W2_ yh yl = xh == yh ? ( xl < yl,  xh < yh )
  W2_ xh xl >  W2_ yh yl = xh == yh ? ( xl > yl,  xh > yh )
  W2_ xh xl <= W2_ yh yl = xh == yh ? ( xl <= yl, xh <= yh )
  W2_ xh xl >= W2_ yh yl = xh == yh ? ( xl >= yl, xh >= yh )


instance ( Num a
         , Integral b, Num2 (Exp b), FromIntegral b a
         , Eq (BigWord a b)
         , P.Num (BigWord a b)
         , BigWordCtx a b
         )
    => P.Num (Exp (BigWord a b)) where
  negate (W2_ hi lo) =
    if lo == 0
      then W2_ (negate hi) 0
      else W2_ (negate (hi+1)) (negate lo)

  abs         = id
  signum x    = x == 0 ? (0,1)
  fromInteger = constant . P.fromInteger

  {-# SPECIALIZE (+) :: Exp Word128 -> Exp Word128 -> Exp Word128 #-}
  (+) | Just Refl <- matchWord128 @(BigWord a b) = CPU.addWord128# $ PTX.addWord128# add
      | otherwise                                = add
    where
      add :: Exp (BigWord a b) -> Exp (BigWord a b) -> Exp (BigWord a b)
      add (W2_ xh xl) (W2_ yh yl) = W2_ hi lo
        where
          lo = xl + yl
          hi = xh + yh + if lo < xl then 1 else 0

  {-# SPECIALIZE (-) :: Exp Word128 -> Exp Word128 -> Exp Word128 #-}
  (-) | Just Refl <- matchWord128 @(BigWord a b) = CPU.subWord128# $ PTX.subWord128# (\x y -> x + negate y)
      | otherwise                                = \x y -> x + negate y

  {-# SPECIALIZE (*) :: Exp Word128 -> Exp Word128 -> Exp Word128 #-}
  (*) | Just Refl <- matchWord128 @(BigWord a b) = CPU.mulWord128# $ PTX.mulWord128# mul
      | otherwise                                = mul
    where
      mul :: Exp (BigWord a b) -> Exp (BigWord a b) -> Exp (BigWord a b)
      mul (W2_ xh xl) (W2_ yh yl) = W2_ hi lo
        where
          hi      = xh * fromIntegral yl + yh * fromIntegral xl + fromIntegral c
          (c,lo)  = mulWithCarry xl yl


instance ( Integral a, FiniteBits a, FromIntegral a b, Num2 (Exp a), Bounded a
         , Integral b, FiniteBits b, FromIntegral b a, Num2 (Exp b), Bounded b
         , Num (BigWord a b)
         , Num2 (Exp (BigWord a b))
         , BigWordCtx a b
#if MIN_VERSION_accelerate(1,2,0)
         , Enum (BigWord a b)
#endif
         )
    => P.Integral (Exp (BigWord a b)) where
  toInteger = error "Prelude.toInteger is not supported for Accelerate types"

  {-# SPECIALIZE div    :: Exp Word128 -> Exp Word128 -> Exp Word128 #-}
  {-# SPECIALIZE mod    :: Exp Word128 -> Exp Word128 -> Exp Word128 #-}
  {-# SPECIALIZE divMod :: Exp Word128 -> Exp Word128 -> (Exp Word128, Exp Word128) #-}
  div    = quot
  mod    = rem
  divMod = quotRem

  {-# SPECIALISE quot :: Exp Word128 -> Exp Word128 -> Exp Word128 #-}
  quot | Just Refl <- matchWord128 @(BigWord a b) = CPU.quotWord128# $ PTX.quotWord128# go
       | otherwise                                = go
    where
      go x y = P.fst (quotRem x y)

  {-# SPECIALISE rem :: Exp Word128 -> Exp Word128 -> Exp Word128 #-}
  rem | Just Refl <- matchWord128 @(BigWord a b) = CPU.remWord128# $ PTX.remWord128# go
      | otherwise                                = go
    where
      go x y = P.snd (quotRem x y)

  {-# SPECIALISE quotRem :: Exp Word128 -> Exp Word128 -> (Exp Word128, Exp Word128) #-}
  quotRem | Just Refl <- matchWord128 @(BigWord a b) = untup2 $$ CPU.quotRemWord128# $ PTX.quotRemWord128# quotRem'
          | otherwise                                = untup2 $$ quotRem'
    where
      quotRem' :: Exp (BigWord a b) -> Exp (BigWord a b) -> Exp (BigWord a b, BigWord a b)
      quotRem' x@(W2_ xh xl) y@(W2_ yh yl)
        = xh <  yh ? ( T2 0 x
        , xh == yh ? ( xl <  yl ? ( T2 0 x
                     , xl == yl ? ( T2 1 0
                     , {-xl > yl -} yh == 0 ? ( let (t2,t1) = quotRem xl yl
                                                in  lift (W2_ 0 t2, W2_ 0 t1)
                                              , T2 1 (W2_ 0 (xl-yl))
                                              )
                     ))
        ,{- xh > yh -} yl == 0 ? ( let (t2,t1) = quotRem xh yh
                                   in  lift (W2_ 0 (fromIntegral t2), W2 t1 xl)
                     , yh == 0 && yl == maxBound
                               ? ( let z       = fromIntegral xh
                                       (t2,t1) = addWithCarry z xl
                                   in
                                   t2 == 0 ?
                                     ( t1 == maxBound ?
                                       ( T2 ((W2_ 0 z) + 1) 0
                                       , T2 (W2_ 0 z) (W2_ 0 t1)
                                       )
                                     , t1 == maxBound ?
                                       ( T2 ((W2_ 0 z) + 2) 1
                                       , t1 == xor maxBound 1 ?
                                           ( T2 ((W2_ 0 z) + 2) 0
                                           , T2 ((W2_ 0 z) + 1) (W2_ 0 (t1+1))
                                           )
                                       )
                                     )
                     , yh == 0 ? ( let (t2,t1) = untup2 (div1 xh xl yl)
                                   in  T2 t2 (W2_ 0 t1)
                     , {- otherwise -}
                       let t1               = countLeadingZeros xh
                           t2               = countLeadingZeros yh
                           z                = shiftR xh (finiteBitSize (undefined::Exp a) - t2)
                           u                = shiftL x t2
                           v                = shiftL y t2
                           W2_ hhh hll      = u
                           W2_ lhh lll      = v
                           -- z hhh hll / lhh lll
                           (q1, r1)         = div2 z hhh lhh
                           (t4, t3)         = mulWithCarry (fromIntegral q1) lll
                           t5               = W2_ (fromIntegral t4) t3
                           t6               = W2_ r1 hll
                           (t8, t7)         = addWithCarry t6 v
                           (t10, t9)        = addWithCarry t7 v
                           loWord (W2_ _ l) = l :: Exp b
                           qr2              = t5 > t6 ?
                                                ( loWord t8 == 0 ?
                                                  ( t7 >= t5 ?
                                                    ( T2 (q1-1) (t7-t5)
                                                    , loWord t10 == 0 ?
                                                      ( T2 (q1-2) (t9-t5)
                                                      , T2 (q1-2) ((maxBound-t5) + t9 + 1)
                                                      )
                                                    )
                                                  , T2 (q1-1) ((maxBound-t5) + t7 + 1)
                                                  )
                                                , T2 (q1) (t6-t5)
                                                )
                           (q2,r2)          = untup2 qr2
                       in
                       t1 == t2 ? ( T2 1 (x-y)
                                  , lift (W2_ 0 (fromIntegral q2), shiftR r2 t2)
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
          go h l c = uncurry3 after $ while (not . uncurry3 done) (uncurry3 body) (lift (h,l,c))

          (t2, t1)   = quotRem maxBound by
          done h l _ = z == 0
            where
              h1        = fromIntegral h
              (t4, t3)  = mulWithCarry h1 (t1 + 1)
              (t6, _t5) = addWithCarry t3 l
              z         = t4 + t6

          body h l c = lift (fromIntegral z, t5, c + (W2_ (fromIntegral t8) t7))
            where
              h1        = fromIntegral h
              (t4, t3)  = mulWithCarry h1 (t1 + 1)
              (t6, t5)  = addWithCarry t3 l
              z         = t4 + t6
              (t8, t7)  = mulWithCarry h1 t2

          after h l c = lift (c + W2_ (fromIntegral t8) t7 + W2_ 0 t10, t9)
            where
              h1        = fromIntegral h
              (_t4, t3) = mulWithCarry h1 (t1 + 1)
              (_t6, t5) = addWithCarry t3 l
              (t8, t7)  = mulWithCarry h1 t2
              (t10, t9) = quotRem t5 by


      div2 :: Exp a -> Exp a -> Exp a -> (Exp a, Exp a)
      div2 hhh hll by = go hhh hll (T2 0 0)
        where
          go :: Exp a -> Exp a -> Exp (a,a) -> (Exp a, Exp a)
          go h l c = uncurry3 after $ while (not . uncurry3 done) (uncurry3 body) (lift (h,l,c))

          (t2, t1) = quotRem maxBound by

          done :: Exp a -> Exp a -> Exp (a,a) -> Exp Bool
          done h l _ = z == 0
            where
              (t4, t3)  = mulWithCarry h (t1 + 1)
              (t6, _t5) = addWithCarry t3 l
              z         = t4 + t6

          body :: Exp a -> Exp a -> Exp (a,a) -> Exp (a, a, (a,a))
          body h l c = lift (z, t5, (addT (untup2 c) (t8,t7)))
            where
              (t4, t3)  = mulWithCarry h (t1 + 1)
              (t6, t5)  = addWithCarry t3 l
              z         = t4 + t6
              (t8, t7)  = mulWithCarry h t2

          after :: Exp a -> Exp a -> Exp (a,a) -> (Exp a, Exp a)
          after h l c = (snd q, t9)
            where
              (_t4, t3) = mulWithCarry h (t1 + 1)
              (_t6, t5) = addWithCarry t3 l
              (t8, t7)  = mulWithCarry h t2
              (t10, t9) = quotRem t5 by
              q         = addT (untup2 (addT (untup2 c) (t8, t7))) (0, t10)

          addT :: (Exp a, Exp a) -> (Exp a, Exp a) -> Exp (a,a)
          addT (lhh, lhl) (llh, lll) =
            let (t4', t3') = addWithCarry lhl lll
            in  lift (lhh + llh + t4', t3')

      uncurry3 f (untup3 -> (a,b,c)) = f a b c


instance ( Integral a, FiniteBits a, FromIntegral a b, Num2 (Exp a)
         , Integral b, FiniteBits b, FromIntegral b a, Num2 (Exp b)
         , Elt (Signed a)
         , Elt (BigInt (Signed a) b)
         , Exp (Signed a) ~ Signed (Exp a)
         , BigWordCtx a b
         )
    => Num2 (Exp (BigWord a b)) where
  type Signed   (Exp (BigWord a b)) = Exp (BigInt (Signed a) b)
  type Unsigned (Exp (BigWord a b)) = Exp (BigWord a b)
  --
  signed (W2_ hi lo) = I2_ (signed hi) lo
  unsigned = id
  --
  addWithCarry (W2_ xh xl) (W2_ yh yl) = (W2_ 0 w, W2_ v u)
    where
      (t1, u)   = addWithCarry xl yl
      (t3, t2)  = addWithCarry xh (fromIntegral t1)
      (t4, v)   = addWithCarry t2 yh
      w         = fromIntegral (t3 + t4)

  mulWithCarry (W2_ xh xl) (W2_ yh yl) =
      ( W2_ (hhh + fromIntegral (shiftR t9 y) + shiftL x z) (shiftL t9 z .|. shiftR t3 y)
      , W2_ (fromIntegral t3) lll)
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
      y          = finiteBitSize (undefined::Exp a)
      z          = finiteBitSize (undefined::Exp b) - y


instance ( Integral a, FiniteBits a, FromIntegral a b
         , Integral b, FiniteBits b, FromIntegral b a
         , BigWordCtx a b
         )
    => Bits (BigWord a b) where

  isSigned _ = constant False

  W2_ xh xl .&.   W2_ yh yl = W2_ (xh .&. yh) (xl .&. yl)
  W2_ xh xl .|.   W2_ yh yl = W2_ (xh .|. yh) (xl .|. yl)
  W2_ xh xl `xor` W2_ yh yl = W2_ (xh `xor` yh) (xl `xor` yl)
  complement (W2_ hi lo)    = W2_ (complement hi) (complement lo)

  shiftL (W2_ hi lo) x =
    if y > 0
      then W2_ (shiftL hi x .|. fromIntegral (shiftR lo y)) (shiftL lo x)
      else W2_ (fromIntegral (shiftL lo (negate y))) (0::Exp b)
    where
      y = finiteBitSize (undefined::Exp b) - x

  shiftR (W2_ hi lo) x = W2_ hi' lo'
    where
      hi' = shiftR hi x
      lo' = if y >= 0 then shiftL (fromIntegral hi) y .|. shiftR lo x
                      else z
      --
      y   = finiteBitSize (undefined::Exp b) - x
      z   = shiftR (fromIntegral hi) (negate y)

  rotateL (W2_ hi lo) x =
    if y >= 0
      then W2_ (fromIntegral (shiftL lo y) .|. shiftR hi z)
               (shiftL (fromIntegral hi) (finiteBitSize (undefined::Exp b) - z) .|. shiftR lo z)
      else W2_ (fromIntegral (shiftR lo (negate y)) .|. shiftL hi x)
               (shift (fromIntegral hi) (finiteBitSize (undefined::Exp b) - z) .|. shiftL lo x .|. shiftR lo z)
    where
      y = x - finiteBitSize (undefined::Exp b)
      z = finiteBitSize (undefined::Exp (BigWord a b)) - x

  rotateR x y = rotateL x (finiteBitSize (undefined::Exp (BigWord a b)) - y)

  bit n =
    if m >= 0
      then W2_ (bit m) 0
      else W2_ 0 (bit n)
    where
      m = n - finiteBitSize (undefined::Exp b)

  testBit (W2_ hi lo) n =
    if m >= 0
      then testBit hi m
      else testBit lo n
    where
      m = n - finiteBitSize (undefined::Exp b)

  setBit (W2_ hi lo) n =
    if m >= 0
      then W2_ (setBit hi m) lo
      else W2_ hi (setBit lo n)
    where
      m = n - finiteBitSize (undefined::Exp b)

  clearBit (W2_ hi lo) n =
    if m >= 0
      then W2_ (clearBit hi m) lo
      else W2_ hi (clearBit lo n)
    where
      m = n - finiteBitSize (undefined::Exp b)

  complementBit (W2_ hi lo) n =
    if m >= 0
      then W2_ (complementBit hi m) lo
      else W2_ hi (complementBit lo n)
    where
      m = n - finiteBitSize (undefined::Exp b)

  popCount (W2_ hi lo) = popCount hi + popCount lo


instance ( Integral a, FiniteBits a, FromIntegral a b
         , Integral b, FiniteBits b, FromIntegral b a
         , BigWordCtx a b
         )
    => FiniteBits (BigWord a b) where
  finiteBitSize _ = finiteBitSize (undefined::Exp a)
                  + finiteBitSize (undefined::Exp b)

  countLeadingZeros (W2_ hi lo) =
    hlz == wsib ? (wsib + llz, hlz)
    where
      hlz   = countLeadingZeros hi
      llz   = countLeadingZeros lo
      wsib  = finiteBitSize (undefined::Exp a)

  countTrailingZeros (W2_ hi lo) =
    ltz == wsib ? (wsib + htz, ltz)
    where
      ltz   = countTrailingZeros lo
      htz   = countTrailingZeros hi
      wsib  = finiteBitSize (undefined::Exp b)


-- BigInt
-- ------

type BigIntCtx hi lo =
    ( Elt hi, Elt lo, Elt (BigInt hi lo)
    , hi ~ Signed hi
    , lo ~ Unsigned lo
    , hi ~ Signed (Unsigned hi)
    , Exp hi ~ Signed (Exp hi)
    , Exp lo ~ Unsigned (Exp lo)
    )


instance (Bounded a, Bounded b, Elt (BigInt a b)) => P.Bounded (Exp (BigInt a b)) where
  minBound = I2_ minBound minBound
  maxBound = I2_ maxBound maxBound


instance (Eq a, Eq b, Elt (BigInt a b)) => Eq (BigInt a b) where
  I2_ xh xl == I2_ yh yl = xh == yh && xl == yl
  I2_ xh xl /= I2_ yh yl = xh /= yh || xl /= yl


instance (Ord a, Ord b, Elt (BigInt a b)) => Ord (BigInt a b) where
  I2_ xh xl <  I2_ yh yl = xh == yh ? ( xl < yl,  xh < yh )
  I2_ xh xl >  I2_ yh yl = xh == yh ? ( xl > yl,  xh > yh )
  I2_ xh xl <= I2_ yh yl = xh == yh ? ( xl <= yl, xh <= yh )
  I2_ xh xl >= I2_ yh yl = xh == yh ? ( xl >= yl, xh >= yh )


instance ( Num a, Ord a
         , Num b, Ord b, Bounded b
         , Num2 (Exp (BigInt a b))
         , Num2 (Exp (BigWord (Unsigned a) b))
         , Num (BigWord (Unsigned a) b)
         , P.Num (BigInt a b)
         , BigIntCtx a b
         )
    => P.Num (Exp (BigInt a b)) where
  negate (I2_ hi lo) =
    if lo == 0
      then I2_ (negate hi) 0
      else I2_ (negate (hi+1)) (negate lo)

  signum (I2_ hi lo) =
    if hi <  0 then I2_ (-1) maxBound else
    if hi == 0 then if lo == 0 then 0 else 1
               else I2_ 0 1

  abs x =
    if x < 0 then negate x
             else x

  fromInteger = constant . fromInteger

  {-# SPECIALIZE (+) :: Exp Int128 -> Exp Int128 -> Exp Int128 #-}
  (+) | Just Refl <- matchInt128 @(BigInt a b) = CPU.addInt128# $ PTX.addInt128# add
      | otherwise                              = add
    where
      add :: Exp (BigInt a b) -> Exp (BigInt a b) -> Exp (BigInt a b)
      add (I2_ xh xl) (I2_ yh yl) = I2_ hi lo
        where
          lo = xl + yl
          hi = xh + yh + if lo < xl then 1 else 0

  {-# SPECIALIZE (-) :: Exp Int128 -> Exp Int128 -> Exp Int128 #-}
  (-) | Just Refl <- matchInt128 @(BigInt a b) = CPU.subInt128# $ PTX.subInt128# (\x y -> x + negate y)
      | otherwise                              = \x y -> x + negate y

  {-# SPECIALIZE (*) :: Exp Int128 -> Exp Int128 -> Exp Int128 #-}
  (*) | Just Refl <- matchInt128 @(BigInt a b) = CPU.mulInt128# $ PTX.mulInt128# mul
      | otherwise                              = mul
    where
      mul :: Exp (BigInt a b) -> Exp (BigInt a b) -> Exp (BigInt a b)
      mul x y = signed (unsigned x * unsigned y)


instance ( Integral a
         , Integral b
         , Num (BigInt a b)
         , Eq (BigWord (Unsigned a) b)
         , Integral (BigWord (Unsigned a) b)
         , Num2 (Exp (BigInt a b))
         , Num2 (Exp (BigWord (Unsigned a) b))
         , BigIntCtx a b
#if MIN_VERSION_accelerate(1,2,0)
         , Enum (BigInt a b)
#endif
         )
    => P.Integral (Exp (BigInt a b)) where
  toInteger = error "Prelude.toInteger is not supported for Accelerate types"

  {-# SPECIALIZE quot :: Exp Int128 -> Exp Int128 -> Exp Int128 #-}
  quot | Just Refl <- matchInt128 @(BigInt a b) = CPU.quotInt128# $ PTX.quotInt128# go
       | otherwise                              = go
    where
      go x y = P.fst (quotRem x y)

  {-# SPECIALIZE rem :: Exp Int128 -> Exp Int128 -> Exp Int128 #-}
  rem | Just Refl <- matchInt128 @(BigInt a b) = CPU.remInt128# $ PTX.remInt128# go
      | otherwise                              = go
    where
      go x y = P.snd (quotRem x y)

  {-# SPECIALISE quotRem :: Exp Int128 -> Exp Int128 -> (Exp Int128, Exp Int128) #-}
  quotRem | Just Refl <- matchInt128 @(BigInt a b) = untup2 $$ CPU.quotRemInt128# $ PTX.quotRemInt128# quotRem'
          | otherwise                              = untup2 $$ quotRem'
    where
      quotRem' x y =
        if x < 0
          then if y < 0
                 then
                   let (q,r) = quotRem (negate (unsigned x)) (negate (unsigned y))
                   in  T2 (signed q) (signed (negate r))
                 else
                   let (q,r) = quotRem (negate (unsigned x)) (unsigned y)
                   in  T2 (signed (negate q)) (signed (negate r))
          else if y < 0
                 then
                   let (q,r) = quotRem (unsigned x) (negate (unsigned y))
                   in  T2 (signed (negate q)) (signed r)
                 else
                   let (q,r) = quotRem (unsigned x) (unsigned y)
                   in  T2 (signed q) (signed r)

  {-# SPECIALIZE div :: Exp Int128 -> Exp Int128 -> Exp Int128 #-}
  {-# SPECIALIZE mod :: Exp Int128 -> Exp Int128 -> Exp Int128 #-}
  div x y = P.fst (divMod x y)
  mod x y = P.snd (divMod x y)

  {-# SPECIALIZE divMod :: Exp Int128 -> Exp Int128 -> (Exp Int128, Exp Int128) #-}
  divMod x y = untup2 $
    if x < 0
      then if y < 0
             then let (q,r) = quotRem (negate (unsigned x)) (negate (unsigned y))
                  in  T2 (signed q) (signed (negate r))
             else let (q,r) = quotRem (negate (unsigned x)) (unsigned y)
                      q'    = signed (negate q)
                      r'    = signed (negate r)
                  in
                  if r == 0 then T2 q' r'
                            else T2 (q'-1) ( r'+y)
      else if y < 0
             then let (q,r) = quotRem (unsigned x) (negate (unsigned y))
                      q'    = signed (negate q)
                      r'    = signed r
                  in
                  if r == 0
                    then T2 q' r'
                    else T2 (q'-1) (r'+y)
             else let (q,r) = quotRem (unsigned x) (unsigned y)
                  in  T2 (signed q) (signed r)


instance ( FiniteBits a, Integral a, FromIntegral a b, FromIntegral a (Signed b)
         , FiniteBits b, Integral b, FromIntegral b a
         , Bits (Signed b), Integral (Signed b), FromIntegral (Signed b) b
         , Num2 (Exp (BigInt a b))
         , Num2 (Exp (BigWord (Unsigned a) b))
         , Bits (BigWord (Unsigned a) b)
         , FiniteBits (BigInt a b)
         , BigIntCtx a b
         )
    => Bits (BigInt a b) where
  isSigned _ = constant True

  I2_ xh xl .&.   I2_ yh yl = I2_ (xh .&. yh) (xl .&. yl)
  I2_ xh xl .|.   I2_ yh yl = I2_ (xh .|. yh) (xl .|. yl)
  I2_ xh xl `xor` I2_ yh yl = I2_ (xh `xor` yh) (xl `xor` yl)
  complement (I2_ hi lo)    = I2_ (complement hi) (complement lo)

  shiftL (I2_ hi lo) x =
    if y > 0
      then I2_ (shiftL hi x .|. fromIntegral (shiftR lo y)) (shiftL lo x)
      else I2_ (fromIntegral (shiftL lo (negate y))) 0
    where
      y = finiteBitSize (undefined::Exp b) - x

  shiftR (I2_ hi lo) x = I2_ hi' lo'
    where
      hi' = shiftR hi x
      lo' = if y >= 0 then shiftL (fromIntegral hi) y .|. shiftR lo x
                      else z
      --
      y = finiteBitSize (undefined::Exp b) - x
      z = fromIntegral (shiftR (fromIntegral hi :: Exp (Signed b)) (negate y))

  rotateL x y = signed (rotateL (unsigned x) y)
  rotateR x y = rotateL x (finiteBitSize (undefined::Exp (BigInt a b)) - y)

  bit n =
    if m >= 0 then I2_ (bit m) 0
              else I2_ 0 (bit n)
    where
      m = n - finiteBitSize (undefined::Exp b)

  testBit (I2_ hi lo) n =
    if m >= 0 then testBit hi m
              else testBit lo n
    where
      m = n - finiteBitSize (undefined::Exp b)

  setBit (I2_ hi lo) n =
    if m >= 0 then I2_ (setBit hi m) lo
              else I2_ hi (setBit lo n)
    where
      m = n - finiteBitSize (undefined::Exp b)

  clearBit (I2_ hi lo) n =
    if m >= 0 then I2_ (clearBit hi m) lo
              else I2_ hi (clearBit lo n)
    where
      m = n - finiteBitSize (undefined::Exp b)

  complementBit (I2_ hi lo) n =
    if m >= 0 then I2_ (complementBit hi m) lo
              else I2_ hi (complementBit lo n)
    where
      m = n - finiteBitSize (undefined::Exp b)

  popCount (I2_ hi lo) = popCount hi + popCount lo


instance ( FiniteBits a
         , FiniteBits b
         , Bits (BigInt a b)
         , Num2 (Exp (BigInt a b))
         , FiniteBits (BigWord (Unsigned a) b)
         , BigIntCtx a b
         )
    => FiniteBits (BigInt a b) where
  finiteBitSize _ = finiteBitSize (undefined::Exp a)
                  + finiteBitSize (undefined::Exp b)

  countLeadingZeros  = countLeadingZeros . unsigned
  countTrailingZeros = countTrailingZeros . unsigned


instance ( Ord a
         , Num a
         , Num2 (Exp a)
         , Ord (BigInt a b)
         , Num (BigInt a b)
         , Bits (BigInt a b)
         , Bounded (BigWord (Unsigned a) b)
         , Num (BigWord (Unsigned a) b)
         , Num2 (Exp (BigWord (Unsigned a) b))
         , Elt (Unsigned a)
         , Exp (Unsigned a) ~ Unsigned (Exp a)
         , BigIntCtx a b
         )
    => Num2 (Exp (BigInt a b)) where
  type Signed   (Exp (BigInt a b)) = Exp (BigInt a b)
  type Unsigned (Exp (BigInt a b)) = Exp (BigWord (Unsigned a) b)
  --
  signed = id
  unsigned (I2_ hi lo) = W2_ (unsigned hi) lo
  --
  addWithCarry x y = (c, r)
    where
      t1      = if x < 0 then maxBound else minBound
      t2      = if y < 0 then maxBound else minBound
      (t3, r) = addWithCarry (unsigned x) (unsigned y)
      c       = signed (t1+t2+t3)

  mulWithCarry x@(I2_ xh _) y@(I2_ yh _) = (hi,lo)
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


-- Num2
-- ----

instance Num2 (Exp Int8) where
  type Signed   (Exp Int8) = Exp Int8
  type Unsigned (Exp Int8) = Exp Word8
  --
  signed       = id
  unsigned     = fromIntegral
  addWithCarry = defaultUnwrapped ((+) :: Exp Int16 -> Exp Int16 -> Exp Int16)
  mulWithCarry = defaultUnwrapped ((*) :: Exp Int16 -> Exp Int16 -> Exp Int16)

instance Num2 (Exp Word8) where
  type Signed   (Exp Word8) = Exp Int8
  type Unsigned (Exp Word8) = Exp Word8
  --
  signed       = fromIntegral
  unsigned     = id
  addWithCarry = defaultUnwrapped ((+) :: Exp Word16 -> Exp Word16 -> Exp Word16)
  mulWithCarry = defaultUnwrapped ((*) :: Exp Word16 -> Exp Word16 -> Exp Word16)

instance Num2 (Exp Int16) where
  type Signed   (Exp Int16) = Exp Int16
  type Unsigned (Exp Int16) = Exp Word16
  --
  signed       = id
  unsigned     = fromIntegral
  addWithCarry = defaultUnwrapped ((+) :: Exp Int32 -> Exp Int32 -> Exp Int32)
  mulWithCarry = defaultUnwrapped ((*) :: Exp Int32 -> Exp Int32 -> Exp Int32)

instance Num2 (Exp Word16) where
  type Signed   (Exp Word16) = Exp Int16
  type Unsigned (Exp Word16) = Exp Word16
  --
  signed       = fromIntegral
  unsigned     = id
  addWithCarry = defaultUnwrapped ((+) :: Exp Word32 -> Exp Word32 -> Exp Word32)
  mulWithCarry = defaultUnwrapped ((*) :: Exp Word32 -> Exp Word32 -> Exp Word32)

instance Num2 (Exp Int32) where
  type Signed   (Exp Int32) = Exp Int32
  type Unsigned (Exp Int32) = Exp Word32
  --
  signed       = id
  unsigned     = fromIntegral
  addWithCarry = defaultUnwrapped ((+) :: Exp Int64 -> Exp Int64 -> Exp Int64)
  mulWithCarry = defaultUnwrapped ((*) :: Exp Int64 -> Exp Int64 -> Exp Int64)

instance Num2 (Exp Word32) where
  type Signed   (Exp Word32) = Exp Int32
  type Unsigned (Exp Word32) = Exp Word32
  --
  signed       = fromIntegral
  unsigned     = id
  addWithCarry = defaultUnwrapped ((+) :: Exp Word64 -> Exp Word64 -> Exp Word64)
  mulWithCarry = defaultUnwrapped ((*) :: Exp Word64 -> Exp Word64 -> Exp Word64)

instance Num2 (Exp Int64) where
  type Signed   (Exp Int64) = Exp Int64
  type Unsigned (Exp Int64) = Exp Word64
  --
  signed       = id
  unsigned     = fromIntegral
  addWithCarry = untup2 $$ CPU.addWithCarryInt64# $ PTX.addWithCarryInt64# awc
    where
      awc x y = T2 hi lo
        where
          extX      = x < 0 ? (maxBound, 0)
          extY      = y < 0 ? (maxBound, 0)
          (hi',lo)  = unsigned x `addWithCarry` unsigned y
          hi        = signed (hi' + extX + extY)

  mulWithCarry = untup2 $$ CPU.mulWithCarryInt64# $ PTX.mulWithCarryInt64# mwc
    where
      mwc x y = T2 hi lo
        where
          extX      = x < 0 ? (negate y, 0)
          extY      = y < 0 ? (negate x, 0)
          (hi',lo)  = unsigned x `mulWithCarry` unsigned y
          hi        = signed hi' + extX + extY

instance Num2 (Exp Word64) where
  type Signed   (Exp Word64) = Exp Int64
  type Unsigned (Exp Word64) = Exp Word64
  --
  signed       = fromIntegral
  unsigned     = id
  addWithCarry = untup2 $$ CPU.addWithCarryWord64# $ PTX.addWithCarryWord64# awc
    where
      awc x y = T2 hi lo
        where
          lo = x + y
          hi = lo < x ? (1,0)

  mulWithCarry = untup2 $$ CPU.mulWithCarryWord64# $ PTX.mulWithCarryWord64# mwc
    where
      mwc x y = T2 hi lo
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
          hi          = hi0 + fromIntegral (uHi1::Exp Word32) + fromIntegral uHi2 + shiftR p1 32 + shiftR p2 32
          lo          = shiftL (fromIntegral lo') 32 .|. (lo0 .&. 0xFFFFFFFF)


defaultUnwrapped
    :: ( FiniteBits w, Bits ww, Integral w, Integral ww
       , FromIntegral w ww, FromIntegral ww w, FromIntegral ww w', Unsigned (Exp w) ~ Exp w'
       )
    => (Exp ww -> Exp ww -> Exp ww)
    -> Exp w
    -> Exp w
    -> (Exp w, Unsigned (Exp w))
defaultUnwrapped op x y = (hi, lo)
  where
    r  = fromIntegral x `op` fromIntegral y
    lo = fromIntegral r
    hi = fromIntegral (r `shiftR` finiteBitSize x)


-- Utilities
-- ---------

untup2 :: (Elt a, Elt b) => Exp (a, b) -> (Exp a, Exp b)
untup2 (T2 a b) = (a, b)

untup3 :: (Elt a, Elt b, Elt c) => Exp (a, b, c) -> (Exp a, Exp b, Exp c)
untup3 (T3 a b c) = (a, b, c)

matchInt128 :: forall t. Elt t => Maybe (t :~: Int128)
matchInt128
  | Just Refl <- matchTypeR (eltR @t) (eltR @Int128)
  = Just (unsafeCoerce Refl)
  | otherwise
  = Nothing

matchWord128 :: forall t. Elt t => Maybe (t :~: Word128)
matchWord128
  | Just Refl <- matchTypeR (eltR @t) (eltR @Word128)
  = Just (unsafeCoerce Refl)
  | otherwise
  = Nothing


-- FromIntegral conversions
-- ------------------------

$(runQ $ do
    let
        lilNums = [ 32, 64 ]
        bigNums = [ (32,64), (64,64), (32,128), (64,128), (32,192), (128,128), (256,256) ]

        wordT :: Int -> Q Type
        wordT = return . ConT . mkName . printf "Word%d"

        intT :: Int -> Q Type
        intT = return . ConT . mkName . printf "Int%d"

        bigWordT :: (Int,Int) -> Q Type
        bigWordT (hi,lo) = wordT (hi+lo)

        bigIntT :: (Int,Int) -> Q Type
        bigIntT (hi,lo) = intT (hi+lo)

#if MIN_VERSION_accelerate(1,2,0)
        thEnum :: (Int,Int) -> Q [Dec]
        thEnum big =
          [d|
              instance P.Enum (Exp $(bigIntT big)) where
                succ x   = x + 1
                pred x   = x - 1
                toEnum   = error "Prelude.toEnum is not supported for Accelerate types"
                fromEnum = error "Prelude.fromEnum is not supported for Accelerate types"

              instance P.Enum (Exp $(bigWordT big)) where
                succ x   = x + 1
                pred x   = x - 1
                toEnum   = error "Prelude.toEnum is not supported for Accelerate types"
                fromEnum = error "Prelude.fromEnum is not supported for Accelerate types"
            |]
#endif

        thFromIntegral1 :: (Int,Int) -> Q [Dec]
        thFromIntegral1 big =
          [d|
              -- signed/unsigned bignum conversions at same width
              instance FromIntegral $(bigIntT big) $(bigIntT big) where
                fromIntegral = id

              instance FromIntegral $(bigWordT big) $(bigWordT big) where
                fromIntegral = id

              instance FromIntegral $(bigIntT big) $(bigWordT big) where
                fromIntegral (I2_ hi lo) = W2_ (fromIntegral hi) lo

              instance FromIntegral $(bigWordT big) $(bigIntT big) where
                fromIntegral (W2_ hi lo) = I2_ (fromIntegral hi) lo

              instance FromIntegral Int $(bigIntT big) where
                fromIntegral x =
#if   WORD_SIZE_IN_BITS == 32
                    fromIntegral (fromIntegral x :: Exp Int32)
#elif WORD_SIZE_IN_BITS == 64
                    fromIntegral (fromIntegral x :: Exp Int64)
#endif

              instance FromIntegral Int $(bigWordT big) where
                fromIntegral x =
#if   WORD_SIZE_IN_BITS == 32
                    fromIntegral (fromIntegral x :: Exp Int32)
#elif WORD_SIZE_IN_BITS == 64
                    fromIntegral (fromIntegral x :: Exp Int64)
#endif

              instance FromIntegral Word $(bigIntT big) where
                fromIntegral x =
#if   WORD_SIZE_IN_BITS == 32
                    fromIntegral (fromIntegral x :: Exp Word32)
#elif WORD_SIZE_IN_BITS == 64
                    fromIntegral (fromIntegral x :: Exp Word64)
#endif

              instance FromIntegral Word $(bigWordT big) where
                fromIntegral x =
#if   WORD_SIZE_IN_BITS == 32
                    fromIntegral (fromIntegral x :: Exp Word32)
#elif WORD_SIZE_IN_BITS == 64
                    fromIntegral (fromIntegral x :: Exp Word64)
#endif
            |]

        thFromIntegral2 :: (Int,Int) -> Int -> Q [Dec]
        thFromIntegral2 big little =
          [d|
              -- convert from primitive type to bignum type
              instance FromIntegral $(wordT little) $(bigWordT big) where
                fromIntegral x = W2_ 0 (fromIntegral x)

              instance FromIntegral $(wordT little) $(bigIntT big) where
                fromIntegral x = I2_ 0 (fromIntegral x)

              instance FromIntegral $(intT little) $(bigWordT big) where
                fromIntegral x@(fromIntegral -> x') =
                  if x < 0 then W2_ maxBound x'
                           else W2_ 0        x'

              instance FromIntegral $(intT little) $(bigIntT big) where
                fromIntegral x@(fromIntegral -> x') =
                  if x < 0 then I2_ (-1) x'
                           else I2_ 0    x'

              -- convert from bignum type to primitive type
              instance FromIntegral $(bigWordT big) $(wordT little) where
                fromIntegral (W2_ _ lo) = fromIntegral lo

              instance FromIntegral $(bigWordT big) $(intT little) where
                fromIntegral (W2_ _ lo) = fromIntegral lo

              instance FromIntegral $(bigIntT big) $(wordT little) where
                fromIntegral (I2_ _ lo) = fromIntegral lo

              instance FromIntegral $(bigIntT big) $(intT little) where
                fromIntegral (I2_ _ lo) = fromIntegral lo
            |]

        thToFloating :: (Int,Int) -> Q [Dec]
        thToFloating big@(_,b) =
          [d|
              instance ToFloating $(bigIntT big) Half where
                toFloating (I2_ hi lo) =
                  toFloating hi * (P.fromIntegral (maxBound :: $(wordT b)) + 1) + toFloating lo

              instance ToFloating $(bigIntT big) Float where
                toFloating (I2_ hi lo) =
                  toFloating hi * (P.fromIntegral (maxBound :: $(wordT b)) + 1) + toFloating lo

              instance ToFloating $(bigIntT big) Double where
                toFloating (I2_ hi lo) =
                  toFloating hi * (P.fromIntegral (maxBound :: $(wordT b)) + 1) + toFloating lo

              instance ToFloating $(bigWordT big) Half where
                toFloating (W2_ hi lo) =
                  toFloating hi * (P.fromIntegral (maxBound :: $(wordT b)) + 1) + toFloating lo

              instance ToFloating $(bigWordT big) Float where
                toFloating (W2_ hi lo) =
                  toFloating hi * (P.fromIntegral (maxBound :: $(wordT b)) + 1) + toFloating lo

              instance ToFloating $(bigWordT big) Double where
                toFloating (W2_ hi lo) =
                  toFloating hi * (P.fromIntegral (maxBound :: $(wordT b)) + 1) + toFloating lo
            |]
    --
#if MIN_VERSION_accelerate(1,2,0)
    e1 <- sequence [ thEnum x            | x <- bigNums ]
#else
    e1 <- return   []
#endif
    d1 <- sequence [ thFromIntegral1 x   | x <- bigNums ]
    d2 <- sequence [ thFromIntegral2 x y | x <- bigNums, y <- lilNums ]
    d3 <- sequence [ thToFloating x      | x <- bigNums ]
    --
    return $ P.concat (e1 P.++ d1 P.++ d2 P.++ d3)
 )


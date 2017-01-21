{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.Data.Internal.Orphans
-- Copyright   : [2016] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module (sadly) exists so that the Accelerate instances can be placed
-- next to each other. This is required due to the way the class hierarchy is
-- structured in order to avoid excessive (and ultimately redundant) class
-- constraints.
--

module Data.Array.Accelerate.Data.Internal.Orphans ()
  where

import Data.Array.Accelerate.Data.Internal.BigInt
import Data.Array.Accelerate.Data.Internal.BigWord
import Data.Array.Accelerate.Data.Internal.Num2

import Data.Array.Accelerate                                        as A
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Data.Bits                              as A
import Data.Array.Accelerate.Product
import Data.Array.Accelerate.Smart

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

mkW2 :: (Elt a, Elt b, Elt (BigWord a b)) => Exp a -> Exp b -> Exp (BigWord a b)
mkW2 a b = lift (W2 a b)


instance (Bounded a, Bounded b, Elt (BigWord a b)) => P.Bounded (Exp (BigWord a b)) where
  minBound = mkW2 minBound minBound
  maxBound = mkW2 maxBound maxBound


instance (Eq a, Eq b, Elt (BigWord a b)) => Eq (BigWord a b) where
  (unlift -> W2 xh xl) == (unlift -> W2 yh yl) = xh == yh && xl == yl
  (unlift -> W2 xh xl) /= (unlift -> W2 yh yl) = xh /= yh || xl /= yl


instance (Ord a, Ord b, Elt (BigWord a b)) => Ord (BigWord a b) where
  (unlift -> W2 xh xl) <  (unlift -> W2 yh yl) = xh == yh ? ( xl < yl,  xh < yh )
  (unlift -> W2 xh xl) >  (unlift -> W2 yh yl) = xh == yh ? ( xl > yl,  xh > yh )
  (unlift -> W2 xh xl) <= (unlift -> W2 yh yl) = xh == yh ? ( xl <= yl, xh <= yh )
  (unlift -> W2 xh xl) >= (unlift -> W2 yh yl) = xh == yh ? ( xl >= yl, xh >= yh )


instance ( Num a
         , Integral b, Num2 (Exp b), FromIntegral b a
         , Eq (BigWord a b)
         , P.Num (BigWord a b)
         , BigWordCtx a b
         )
    => P.Num (Exp (BigWord a b)) where
  negate (unlift -> W2 hi lo) =
    if lo == 0
      then mkW2 (negate hi) 0
      else mkW2 (negate (hi+1)) (negate lo)

  abs      = id
  signum x = x == 0 ? (0,1)

  (unlift -> W2 xh xl) + (unlift -> W2 yh yl) = mkW2 hi lo
    where
      lo = xl + yl
      hi = xh + yh + if lo < xl then 1 else 0

  (unlift -> W2 xh xl) * (unlift -> W2 yh yl) = mkW2 hi lo
    where
      hi      = xh * fromIntegral yl + yh * fromIntegral xl + fromIntegral c
      (c,lo)  = mulWithCarry xl yl

  fromInteger = constant . P.fromInteger


instance ( Integral a, FiniteBits a, FromIntegral a b, Num2 (Exp a), Bounded a
         , Integral b, FiniteBits b, FromIntegral b a, Num2 (Exp b), Bounded b
         , Num (BigWord a b)
         , Num2 (Exp (BigWord a b))
         , BigWordCtx a b
         )
    => P.Integral (Exp (BigWord a b)) where
  toInteger = error "Prelude.toInteger not supported for Accelerate types"

  divMod = quotRem
  quotRem x y = untup2 $ quotRem' (unlift x) (unlift y)
    where
      quotRem' :: BigWord (Exp a) (Exp b) -> BigWord (Exp a) (Exp b) -> Exp (BigWord a b, BigWord a b)
      quotRem' (W2 xh xl) (W2 yh yl)
        = xh <  yh ? ( tup2 (0, x)
        , xh == yh ? ( xl <  yl ? ( tup2 (0, x)
                     , xl == yl ? ( tup2 (1, 0)
                     , {-xl > yl -} yh == 0 ? ( let (t2,t1) = quotRem xl yl
                                                in  lift (mkW2 0 t2, mkW2 0 t1)
                                              , tup2 (1, mkW2 0 (xl-yl))
                                              )
                     ))
        ,{- xh > yh -} yl == 0 ? ( let (t2,t1) = quotRem xh yh
                                   in  lift (mkW2 0 (fromIntegral t2), W2 t1 xl)
                     , yh == 0 && yl == maxBound
                               ? ( let z       = fromIntegral xh
                                       (t2,t1) = addWithCarry z xl
                                   in
                                   t2 == 0 ?
                                     ( t1 == maxBound ?
                                       ( tup2 ((mkW2 0 z) + 1, 0)
                                       , tup2 (mkW2 0 z, mkW2 0 t1)
                                       )
                                     , t1 == maxBound ?
                                       ( tup2 ((mkW2 0 z) + 2, 1)
                                       , t1 == xor maxBound 1 ?
                                           ( tup2 ((mkW2 0 z) + 2, 0)
                                           , tup2 ((mkW2 0 z) + 1, mkW2 0 (t1+1))
                                           )
                                       )
                                     )
                     , yh == 0 ? ( let (t2,t1) = untup2 (div1 xh xl yl)
                                   in  tup2 (t2, mkW2 0 t1)
                     , {- otherwise -}
                       let t1         = countLeadingZeros xh
                           t2         = countLeadingZeros yh
                           z          = shiftR xh (finiteBitSize (undefined::Exp a) - t2)
                           u          = shiftL x t2
                           v          = shiftL y t2
                           W2 hhh hll = unlift u  :: BigWord (Exp a) (Exp b)
                           W2 lhh lll = unlift v  :: BigWord (Exp a) (Exp b)
                           -- -- z hhh hll / lhh lll
                           (q1, r1)   = div2 z hhh lhh
                           (t4, t3)   = mulWithCarry (fromIntegral q1) lll
                           t5         = mkW2 (fromIntegral t4) t3
                           t6         = mkW2 r1 hll
                           (t8, t7)   = addWithCarry t6 v
                           (t10, t9)  = addWithCarry t7 v
                           loWord w   = let W2 _ l = unlift w :: BigWord (Exp a) (Exp b)
                                        in  l
                           qr2        = t5 > t6 ?
                                          ( loWord t8 == 0 ?
                                            ( t7 >= t5 ?
                                              ( tup2 (q1-1, t7-t5)
                                              , loWord t10 == 0 ?
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
                       t1 == t2 ? ( tup2 (1, x-y)
                                  , lift (mkW2 0 (fromIntegral q2), shiftR r2 t2)
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

          body h l c = lift (fromIntegral z, t5, c + (mkW2 (fromIntegral t8) t7))
            where
              h1        = fromIntegral h
              (t4, t3)  = mulWithCarry h1 (t1 + 1)
              (t6, t5)  = addWithCarry t3 l
              z         = t4 + t6
              (t8, t7)  = mulWithCarry h1 t2

          after h l c = lift (c + mkW2 (fromIntegral t8) t7 + mkW2 0 t10, t9)
            where
              h1        = fromIntegral h
              (_t4, t3) = mulWithCarry h1 (t1 + 1)
              (_t6, t5) = addWithCarry t3 l
              (t8, t7)  = mulWithCarry h1 t2
              (t10, t9) = quotRem t5 by


      div2 :: Exp a -> Exp a -> Exp a -> (Exp a, Exp a)
      div2 hhh hll by = go hhh hll (tup2 (0,0))
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
          body h l c = lift (z, t5, (addT (unlift c) (t8,t7)))
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
              q         = addT (unlift (addT (unlift c) (t8, t7))) (0, t10)

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
  signed (unlift -> W2 (hi::Exp a) lo) = mkI2 (signed hi) lo
  unsigned = id
  --
  addWithCarry (unlift -> W2 xh xl) (unlift -> W2 yh yl) = (mkW2 0 w, mkW2 v u)
    where
      (t1, u)   = addWithCarry xl yl
      (t3, t2)  = addWithCarry xh (fromIntegral t1)
      (t4, v)   = addWithCarry t2 yh
      w         = fromIntegral (t3 + t4)

  mulWithCarry (unlift -> W2 xh xl) (unlift -> W2 yh yl) =
      ( mkW2 (hhh + fromIntegral (shiftR t9 y) + shiftL x z) (shiftL t9 z .|. shiftR t3 y)
      , mkW2 (fromIntegral t3) lll)
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

  (unlift -> W2 xh xl) .&.   (unlift -> W2 yh yl) = mkW2 (xh .&. yh) (xl .&. yl)
  (unlift -> W2 xh xl) .|.   (unlift -> W2 yh yl) = mkW2 (xh .|. yh) (xl .|. yl)
  (unlift -> W2 xh xl) `xor` (unlift -> W2 yh yl) = mkW2 (xh `xor` yh) (xl `xor` yl)
  complement (unlift -> W2 hi lo) = mkW2 (complement hi) (complement lo)

  shiftL (unlift -> W2 hi lo) x =
    if y > 0
      then mkW2 (shiftL hi x .|. fromIntegral (shiftR lo y)) (shiftL lo x)
      else mkW2 (fromIntegral (shiftL lo (negate y))) (0::Exp b)
    where
      y = finiteBitSize (undefined::Exp b) - x

  shiftR (unlift -> W2 hi lo) x = mkW2 hi' lo'
    where
      hi' = shiftR hi x
      lo' = if y >= 0 then shiftL (fromIntegral hi) y .|. shiftR lo x
                      else z
      --
      y   = finiteBitSize (undefined::Exp b) - x
      z   = shiftR (fromIntegral hi) (negate y)

  rotateL (unlift -> W2 hi lo) x =
    if y >= 0
      then mkW2 (fromIntegral (shiftL lo y) .|. shiftR hi z)
                (shiftL (fromIntegral hi) (finiteBitSize (undefined::Exp b) - z) .|. shiftR lo z)
      else mkW2 (fromIntegral (shiftR lo (negate y)) .|. shiftL hi x)
                (shift (fromIntegral hi) (finiteBitSize (undefined::Exp b) - z) .|. shiftL lo x .|. shiftR lo z)
    where
      y = x - finiteBitSize (undefined::Exp b)
      z = finiteBitSize (undefined::Exp (BigWord a b)) - x

  rotateR x y = rotateL x (finiteBitSize (undefined::Exp (BigWord a b)) - y)

  bit n =
    if m >= 0
      then mkW2 (bit m) 0
      else mkW2 0 (bit n)
    where
      m = n - finiteBitSize (undefined::Exp b)

  testBit (unlift -> W2 hi lo) n =
    if m >= 0
      then testBit hi m
      else testBit lo n
    where
      m = n - finiteBitSize (undefined::Exp b)

  setBit (unlift -> W2 hi lo) n =
    if m >= 0
      then mkW2 (setBit hi m) lo
      else mkW2 hi (setBit lo n)
    where
      m = n - finiteBitSize (undefined::Exp b)

  clearBit (unlift -> W2 hi lo) n =
    if m >= 0
      then mkW2 (clearBit hi m) lo
      else mkW2 hi (clearBit lo n)
    where
      m = n - finiteBitSize (undefined::Exp b)

  complementBit (unlift -> W2 hi lo) n =
    if m >= 0
      then mkW2 (complementBit hi m) lo
      else mkW2 hi (complementBit lo n)
    where
      m = n - finiteBitSize (undefined::Exp b)

  popCount (unlift -> W2 hi lo) = popCount hi + popCount lo


instance ( Integral a, FiniteBits a, FromIntegral a b
         , Integral b, FiniteBits b, FromIntegral b a
         , BigWordCtx a b
         )
    => FiniteBits (BigWord a b) where
  finiteBitSize _ = finiteBitSize (undefined::Exp a)
                  + finiteBitSize (undefined::Exp b)

  countLeadingZeros (unlift -> W2 hi lo) =
    hlz == wsib ? (wsib + llz, hlz)
    where
      hlz   = countLeadingZeros hi
      llz   = countLeadingZeros lo
      wsib  = finiteBitSize (undefined::Exp a)

  countTrailingZeros (unlift -> W2 hi lo) =
    ltz == wsib ? (wsib + htz, ltz)
    where
      ltz   = countTrailingZeros lo
      htz   = countTrailingZeros hi
      wsib  = finiteBitSize (undefined::Exp b)


-- Conversions to higher bit-widths

instance FromIntegral Word32 Int128 where
  fromIntegral x = mkI2 0 (fromIntegral x)

instance FromIntegral Word32 Word128 where
  fromIntegral x = mkW2 0 (fromIntegral x)

instance FromIntegral Word32 Int192 where
  fromIntegral x = mkI2 0 (mkW2 0 (fromIntegral x))

instance FromIntegral Word32 Word192 where
  fromIntegral x = mkW2 0 (mkW2 0 (fromIntegral x))

instance FromIntegral Word64 Int128 where
  fromIntegral x = mkI2 0 x

instance FromIntegral Word64 Word128 where
  fromIntegral x = mkW2 0 x

instance FromIntegral Word64 Int192 where
  fromIntegral x = mkI2 0 (mkW2 0 x)

instance FromIntegral Word64 Word192 where
  fromIntegral x = mkW2 0 (mkW2 0 x)


-- Conversions to lower bit-widths (lossy)

instance FromIntegral Word128 Word32 where
  fromIntegral (unlift -> W2 (_::Exp Word64) lo) = fromIntegral lo

instance FromIntegral Word128 Word64 where
  fromIntegral (unlift -> W2 (_::Exp Word64) lo) = lo

instance FromIntegral Word192 Word32 where
  fromIntegral (unlift -> W2 (_::Exp Word64) lo) = fromIntegral lo

instance FromIntegral Word192 Word64 where
  fromIntegral (unlift -> W2 (_::Exp Word64) lo) = fromIntegral lo


-- Conversions at the same bit width

instance FromIntegral Word128 Word128 where
  fromIntegral = id

instance FromIntegral Word192 Word192 where
  fromIntegral = id

instance FromIntegral Word256 Word256 where
  fromIntegral = id


type instance EltRepr (BigWord a b) = EltRepr (a,b)

instance (Elt a, Elt b, P.Show (BigWord a b)) => Elt (BigWord a b) where
  eltType _        = eltType (undefined :: (a,b))
  toElt w          = let (a,b) = toElt w in W2 a b
  fromElt (W2 a b) = fromElt (a,b)

instance (cst a, cst b) => IsProduct cst (BigWord a b) where
  type ProdRepr (BigWord a b) = ProdRepr (a,b)
  fromProd cst (W2 a b) = fromProd cst (a,b)
  toProd cst w          = let (a,b) = toProd cst w in W2 a b
  prod cst _            = prod cst (undefined :: (a,b))

instance (Lift Exp a, Lift Exp b, Elt (Plain a), Elt (Plain b), P.Show (BigWord (Plain a) (Plain b)))
    => Lift Exp (BigWord a b) where
  type Plain (BigWord a b) = BigWord (Plain a) (Plain b)
  lift (W2 a b)            = Exp $ Tuple (NilTup `SnocTup` lift a `SnocTup` lift b)

instance (Elt a, Elt b, P.Show (BigWord a b)) => Unlift Exp (BigWord (Exp a) (Exp b)) where
  unlift w =
    let a = Exp $ SuccTupIdx ZeroTupIdx `Prj` w
        b = Exp $ ZeroTupIdx `Prj` w
    in
    W2 a b


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

mkI2 :: (Elt a, Elt b, Elt (BigInt a b)) => Exp a -> Exp b -> Exp (BigInt a b)
mkI2 a b = lift (I2 a b)


instance (Bounded a, Bounded b, Elt (BigInt a b)) => P.Bounded (Exp (BigInt a b)) where
  minBound = mkI2 minBound minBound
  maxBound = mkI2 maxBound maxBound


instance (Eq a, Eq b, Elt (BigInt a b)) => Eq (BigInt a b) where
  (unlift -> I2 xh xl) == (unlift -> I2 yh yl) = xh == yh && xl == yl
  (unlift -> I2 xh xl) /= (unlift -> I2 yh yl) = xh /= yh || xl /= yl


instance (Ord a, Ord b, Elt (BigInt a b)) => Ord (BigInt a b) where
  (unlift -> I2 xh xl) <  (unlift -> I2 yh yl) = xh == yh ? ( xl < yl,  xh < yh )
  (unlift -> I2 xh xl) >  (unlift -> I2 yh yl) = xh == yh ? ( xl > yl,  xh > yh )
  (unlift -> I2 xh xl) <= (unlift -> I2 yh yl) = xh == yh ? ( xl <= yl, xh <= yh )
  (unlift -> I2 xh xl) >= (unlift -> I2 yh yl) = xh == yh ? ( xl >= yl, xh >= yh )


instance ( Num a, Ord a
         , Num b, Ord b, Bounded b
         , Num2 (Exp (BigInt a b))
         , Num2 (Exp (BigWord (Unsigned a) b))
         , Num (BigWord (Unsigned a) b)
         , P.Num (BigInt a b)
         , BigIntCtx a b
         )
    => P.Num (Exp (BigInt a b)) where
  negate (unlift -> I2 hi lo) =
    if lo == 0
      then mkI2 (negate hi) 0
      else mkI2 (negate (hi+1)) (negate lo)

  signum (unlift -> I2 hi lo :: BigInt (Exp a) (Exp b)) =
    if hi <  0 then mkI2 (-1) maxBound else
    if hi == 0 then if lo == 0 then 0 else 1
               else mkI2 0 1

  abs x =
    if x < 0 then negate x
             else x

  (unlift -> I2 xh xl) + (unlift -> I2 yh yl) = mkI2 hi lo
    where
      lo = xl + yl
      hi = xh + yh + if lo < xl then 1 else 0

  x * y = signed (unsigned x * unsigned y)

  fromInteger = constant . fromInteger


instance ( Integral a
         , Integral b
         , Num (BigInt a b)
         , Eq (BigWord (Unsigned a) b)
         , Integral (BigWord (Unsigned a) b)
         , Num2 (Exp (BigInt a b))
         , Num2 (Exp (BigWord (Unsigned a) b))
         , BigIntCtx a b
         )
    => P.Integral (Exp (BigInt a b)) where
  toInteger = error "Prelude.toInteger not supported for Accelerate types"

  quotRem x y = untup2 $
    if x < 0
      then if y < 0
             then
               let (q,r) = quotRem (negate (unsigned x)) (negate (unsigned y))
               in  tup2 (signed q, signed (negate r))
             else
               let (q,r) = quotRem (negate (unsigned x)) (unsigned y)
               in  tup2 (signed (negate q), signed (negate r))
      else if y < 0
             then
               let (q,r) = quotRem (unsigned x) (negate (unsigned y))
               in  tup2 (signed (negate q), signed r)
             else
               let (q,r) = quotRem (unsigned x) (unsigned y)
               in  tup2 (signed q, signed r)

  divMod x y = untup2 $
    if x < 0
      then if y < 0
             then let (q,r) = quotRem (negate (unsigned x)) (negate (unsigned y))
                  in  tup2 (signed q, signed (negate r))
             else let (q,r) = quotRem (negate (unsigned x)) (unsigned y)
                      q'    = signed (negate q)
                      r'    = signed (negate r)
                  in
                  if r == 0 then tup2 (q', r')
                            else tup2 (q'-1, r'+y)
      else if y < 0
             then let (q,r) = quotRem (unsigned x) (negate (unsigned y))
                      q'    = signed (negate q)
                      r'    = signed r
                  in
                  if r == 0
                    then tup2 (q', r')
                    else tup2 (q'-1, r'+y)
             else let (q,r) = quotRem (unsigned x) (unsigned y)
                  in  tup2 (signed q, signed r)


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

  (unlift -> I2 xh xl) .&. (unlift -> I2 yh yl)   = mkI2 (xh .&. yh) (xl .&. yl)
  (unlift -> I2 xh xl) .|. (unlift -> I2 yh yl)   = mkI2 (xh .|. yh) (xl .|. yl)
  (unlift -> I2 xh xl) `xor` (unlift -> I2 yh yl) = mkI2 (xh `xor` yh) (xl `xor` yl)
  complement (unlift -> I2 hi lo)   = mkI2 (complement hi) (complement lo)

  shiftL (unlift -> I2 hi lo) x =
    if y > 0
      then mkI2 (shiftL hi x .|. fromIntegral (shiftR lo y)) (shiftL lo x)
      else mkI2 (fromIntegral (shiftL lo (negate y))) 0
    where
      y = finiteBitSize (undefined::Exp b) - x

  shiftR (unlift -> I2 hi lo) x = mkI2 hi' lo'
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
    if m >= 0 then mkI2 (bit m) 0
              else mkI2 0 (bit n)
    where
      m = n - finiteBitSize (undefined::Exp b)

  testBit (unlift -> I2 hi lo) n =
    if m >= 0 then testBit hi m
              else testBit lo n
    where
      m = n - finiteBitSize (undefined::Exp b)

  setBit (unlift -> I2 hi lo) n =
    if m >= 0 then mkI2 (setBit hi m) lo
              else mkI2 hi (setBit lo n)
    where
      m = n - finiteBitSize (undefined::Exp b)

  clearBit (unlift -> I2 hi lo) n =
    if m >= 0 then mkI2 (clearBit hi m) lo
              else mkI2 hi (clearBit lo n)
    where
      m = n - finiteBitSize (undefined::Exp b)

  complementBit (unlift -> I2 hi lo) n =
    if m >= 0 then mkI2 (complementBit hi m) lo
              else mkI2 hi (complementBit lo n)
    where
      m = n - finiteBitSize (undefined::Exp b)

  popCount (unlift -> I2 hi lo) = popCount hi + popCount lo


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
  unsigned (unlift -> I2 (hi::Exp a) lo) = mkW2 (unsigned hi) lo
  --
  addWithCarry x y = (c, r)
    where
      t1      = if x < 0 then maxBound else minBound
      t2      = if y < 0 then maxBound else minBound
      (t3, r) = addWithCarry (unsigned x) (unsigned y)
      c       = signed (t1+t2+t3)

  mulWithCarry x@(unlift -> I2 xh (_::Exp b)) y@(unlift -> I2 yh (_::Exp b)) = (hi,lo)
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


-- Conversions to higher bit-widths

instance FromIntegral Int32 Int128 where
  fromIntegral x@(fromIntegral -> x') =
    if x < 0 then mkI2 (-1) x'
             else mkI2 0    x'

instance FromIntegral Int32 Word128 where
  fromIntegral x@(fromIntegral -> x') =
    if x < 0 then mkW2 maxBound x'
             else mkW2 0        x'

instance FromIntegral Int32 Int192 where
  fromIntegral x@(fromIntegral -> x') =
    if x < 0 then mkI2 (-1) x'
             else mkI2 0    x'

instance FromIntegral Int32 Word192 where
  fromIntegral x@(fromIntegral -> x') =
    if x < 0 then mkW2 maxBound x'
             else mkW2 0        x'

instance FromIntegral Int64 Int128 where
  fromIntegral x@(fromIntegral -> x') =
    if x < 0 then mkI2 (-1) x'
             else mkI2 0    x'

instance FromIntegral Int64 Word128 where
  fromIntegral x@(fromIntegral -> x') =
    if x < 0 then mkW2 maxBound x'
             else mkW2 0        x'

instance FromIntegral Int64 Int192 where
  fromIntegral x@(fromIntegral -> x') =
    if x < 0 then mkI2 (-1) x'
             else mkI2 0    x'

instance FromIntegral Int64 Word192 where
  fromIntegral x@(fromIntegral -> x') =
    if x < 0 then mkW2 maxBound x'
             else mkW2 0        x'


-- Conversions to lower bit-widths (lossy)

instance FromIntegral Word128 Int32 where
  fromIntegral (unlift -> W2 (_::Exp Word64) lo) = fromIntegral lo

instance FromIntegral Word128 Int64 where
  fromIntegral (unlift -> W2 (_::Exp Word64) lo) = fromIntegral lo

instance FromIntegral Word192 Int32 where
  fromIntegral (unlift -> W2 (_::Exp Word64) lo) = fromIntegral lo

instance FromIntegral Word192 Int64 where
  fromIntegral (unlift -> W2 (_::Exp Word64) lo) = fromIntegral lo


-- Signed/Unsigned conversions at the same width

instance FromIntegral Int128 Word128 where
  fromIntegral (unlift -> I2 hi lo) = mkW2 (fromIntegral hi) lo

instance FromIntegral Int192 Word192 where
  fromIntegral (unlift -> I2 hi lo) = mkW2 (fromIntegral hi) lo

instance FromIntegral Int128 Int128 where
  fromIntegral = id

instance FromIntegral Word128 Int128 where
  fromIntegral (unlift -> W2 hi lo) = mkI2 (fromIntegral hi) lo

instance FromIntegral Int256 Int256 where
  fromIntegral = id

instance FromIntegral Int256 Word256 where
  fromIntegral (unlift -> I2 hi lo) = mkW2 (fromIntegral hi) lo

instance FromIntegral Word256 Int256 where
  fromIntegral (unlift -> W2 hi lo) = mkI2 (fromIntegral hi) lo


type instance EltRepr (BigInt a b) = EltRepr (a,b)

instance (Elt a, Elt b, P.Show (BigInt a b)) => Elt (BigInt a b) where
  eltType _        = eltType (undefined :: (a,b))
  toElt w          = let (a,b) = toElt w in I2 a b
  fromElt (I2 a b) = fromElt (a,b)

instance (cst a, cst b) => IsProduct cst (BigInt a b) where
  type ProdRepr (BigInt a b) = ProdRepr (a,b)
  fromProd cst (I2 a b) = fromProd cst (a,b)
  toProd cst w          = let (a,b) = toProd cst w in I2 a b
  prod cst _            = prod cst (undefined :: (a,b))

instance (Lift Exp a, Lift Exp b, Elt (Plain a), Elt (Plain b), P.Show (BigInt (Plain a) (Plain b)))
    => Lift Exp (BigInt a b) where
  type Plain (BigInt a b) = BigInt (Plain a) (Plain b)
  lift (I2 a b)           = Exp $ Tuple (NilTup `SnocTup` lift a `SnocTup` lift b)

instance (Elt a, Elt b, P.Show (BigInt a b)) => Unlift Exp (BigInt (Exp a) (Exp b)) where
  unlift w =
    let a = Exp $ SuccTupIdx ZeroTupIdx `Prj` w
        b = Exp $ ZeroTupIdx `Prj` w
    in
    I2 a b


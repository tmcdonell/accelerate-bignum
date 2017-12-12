{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}
-- |
-- Module      : Test.Base
-- Copyright   : [2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Test.Base where

import Test.Iso

import Data.Array.Accelerate                                        ( Acc, Arrays, Array, Shape, Elt, fromList )
import Data.Array.Accelerate.Array.Sugar                            ( size )
import Data.Array.Accelerate.Trafo                                  ( Afunction, AfunctionR )
import Data.Array.Accelerate.Data.Complex

import Data.Array.Accelerate.Data.BigInt
import Data.Array.Accelerate.Data.BigWord

import Data.Bits
import Data.Int
import Data.Word
import Control.Monad                                                ( when )

import Hedgehog
import qualified Hedgehog.Gen                                       as Gen
import qualified Hedgehog.Range                                     as Range


type Run  = forall a. Arrays a => Acc a -> a
type RunN = forall f. Afunction f => f -> AfunctionR f

floating :: RealFloat a => Gen a
floating = Gen.realFloat (Range.linearFracFrom 0 (-1) 1)

complex :: Gen a -> Gen (Complex a)
complex f = (:+) <$> f <*> f

array :: (Shape sh, Elt e) => sh -> Gen e -> Gen (Array sh e)
array sh gen = fromList sh <$> Gen.list (Range.singleton (size sh)) gen

i8 :: Gen Int8
i8 = Gen.int8 Range.linearBounded

i16 :: Gen Int16
i16 = Gen.int16 Range.linearBounded

i32 :: Gen Int32
i32 = Gen.int32 Range.linearBounded

i64 :: Gen Int64
i64 = Gen.int64 Range.linearBounded

w8 :: Gen Word8
w8 = Gen.word8 Range.linearBounded

w16 :: Gen Word16
w16 = Gen.word16 Range.linearBounded

w32 :: Gen Word32
w32 = Gen.word32 Range.linearBounded

w64 :: Gen Word64
w64 = Gen.word64 Range.linearBounded

integer :: Gen Integer
integer =
  let b = 2 * toInteger (maxBound :: Int64)
  in  Gen.integral (Range.linearFrom 0 (-b) b)


except :: Gen e -> (e -> Bool) -> Gen e
except gen f  = do
  v <- gen
  when (f v) Gen.discard
  return v


toInteger2 :: (Integral a, Integral b, FiniteBits b) => a -> b -> Integer
toInteger2 h l = toInteger h * 2 ^ finiteBitSize l + toInteger l


newtype I64 = I64 (BigInt  Int32  Word32)
  deriving (Show, Eq, Ord, Bounded, Num, Real, Enum, Integral, Bits, FiniteBits)

newtype U64 = U64 (BigWord Word32 Word32)
  deriving (Show, Eq, Ord, Bounded, Num, Real, Enum, Integral, Bits, FiniteBits)

newtype II64 = II64 (BigInt  Int16  (BigWord Word16 Word32))
  deriving (Show, Eq, Ord, Bounded, Num, Real, Enum, Integral, Bits, FiniteBits)

newtype UU64 = UU64 (BigWord Word16 (BigWord Word16 Word32))
  deriving (Show, Eq, Ord, Bounded, Num, Real, Enum, Integral, Bits, FiniteBits)

instance Iso Int64 I64 where
  isoR w              = I64 (I2 (fromIntegral (w `shiftR` 32)) (fromIntegral w))
  isoL (I64 (I2 h l)) = fromIntegral h `shiftL` 32 .|. fromIntegral l

instance Iso Word64 U64 where
  isoR w              = U64 (W2 (fromIntegral (w `shiftR` 32)) (fromIntegral w))
  isoL (U64 (W2 h l)) = fromIntegral h `shiftL` 32 .|. fromIntegral l

instance Iso Int64 II64 where
  isoR w
    = II64 (I2 (fromIntegral (w `shiftR` 48)) (W2 (fromIntegral (w `shiftR` 32)) (fromIntegral w)))

  isoL (II64 (I2 h (W2 lh ll)))
    =  fromIntegral h  `shiftL` 48
   .|. fromIntegral lh `shiftL` 32
   .|. fromIntegral ll

instance Iso Word64 UU64 where
  isoR w
    = UU64 (W2 (fromIntegral (w `shiftR` 48)) (W2 (fromIntegral (w `shiftR` 32)) (fromIntegral w)))

  isoL (UU64 (W2 h (W2 lh ll)))
    =  fromIntegral h  `shiftL` 48
   .|. fromIntegral lh `shiftL` 32
   .|. fromIntegral ll


infixr 0 $$
($$) :: (b -> a) -> (c -> d -> b) -> c -> d -> a
(f $$ g) x y = f (g x y)


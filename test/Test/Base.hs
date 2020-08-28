{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes        #-}
-- |
-- Module      : Test.Base
-- Copyright   : [2017..2020] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Test.Base where

import Data.Array.Accelerate                                        ( Acc, Arrays, Array, Shape, Elt, fromList )
import Data.Array.Accelerate.Sugar.Shape                            ( size )
import Data.Array.Accelerate.Trafo                                  ( Afunction )
import Data.Array.Accelerate.Trafo.Sharing                          ( AfunctionR )
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

i96 :: Gen Int96
i96 = I2 <$> i32 <*> w64

i128 :: Gen Int128
i128 = I2 <$> i64 <*> w64

i192 :: Gen Int192
i192 = I2 <$> i64 <*> w128

w8 :: Gen Word8
w8 = Gen.word8 Range.linearBounded

w16 :: Gen Word16
w16 = Gen.word16 Range.linearBounded

w32 :: Gen Word32
w32 = Gen.word32 Range.linearBounded

w64 :: Gen Word64
w64 = Gen.word64 Range.linearBounded

w96 :: Gen Word96
w96 = W2 <$> w32 <*> w64

w128 :: Gen Word128
w128 = W2 <$> w64 <*> w64

w192 :: Gen Word192
w192 = W2 <$> w64 <*> w128


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

infixr 0 $$
($$) :: (b -> a) -> (c -> d -> b) -> c -> d -> a
(f $$ g) x y = f (g x y)


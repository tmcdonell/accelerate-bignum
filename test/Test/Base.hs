{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}
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

import Data.Array.Accelerate                                        ( Acc, Arrays, Array, Shape, Elt, fromList )
import Data.Array.Accelerate.Array.Sugar                            ( size )
import Data.Array.Accelerate.Trafo                                  ( Afunction, AfunctionR )
import Data.Array.Accelerate.Data.Complex

import Data.Bits
import Data.Int
import Data.Word

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


toInteger2 :: (Integral a, Integral b, FiniteBits b) => a -> b -> Integer
toInteger2 h l = toInteger h * 2 ^ finiteBitSize l + toInteger l


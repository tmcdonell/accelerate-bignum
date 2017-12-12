{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |
-- Module      : Test.BigNum.Bits
-- Copyright   : [2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Test.BigNum.Bits ( test_bits )
  where

import Test.Iso
import Test.Base
import Test.ShowType

import Data.Bits
import Data.Proxy
import Test.Tasty
import Test.Tasty.Hedgehog

import Hedgehog
import qualified Hedgehog.Gen                                       as Gen
import qualified Hedgehog.Range                                     as Range


test_bits :: TestTree
test_bits =
  testGroup "Bits"
    [ testElt i64 (Proxy :: Proxy I64)
    , testElt w64 (Proxy :: Proxy U64)
    , testElt i64 (Proxy :: Proxy II64)
    , testElt w64 (Proxy :: Proxy UU64)
    ]
  where
    testElt :: (Iso a b, Eq a, Eq b, FiniteBits a, FiniteBits b, Show a, Show b, Show (ArgType b))
            => Gen a
            -> Proxy b
            -> TestTree
    testElt a b =
      testGroup (showType b)
        [ testProperty "complement"    $ prop_complement a b
        , testProperty "xor"           $ prop_xor a b
        , testProperty "(.&.)"         $ prop_band a b
        , testProperty "(.|.)"         $ prop_bor a b
        , testProperty "shiftL"        $ prop_shiftL a b
        , testProperty "shiftR"        $ prop_shiftR a b
        , testProperty "shift"         $ prop_shift a b
        , testProperty "rotateL"       $ prop_rotateL a b
        , testProperty "rotateR"       $ prop_rotateR a b
        , testProperty "rotate"        $ prop_rotate a b
        , testProperty "bit"           $ prop_bit b
        , testProperty "testBit"       $ prop_testBit a b
        , testProperty "setBit"        $ prop_setBit a b
        , testProperty "clearBit"      $ prop_clearBit a b
        , testProperty "complementBit" $ prop_complementBit a b
        , testProperty "popCount"      $ prop_popCount a b
        ]


prop_complement
    :: (Iso a b, Bits a, Bits b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_complement a b =
  property $ do
    x <- forAll a
    prop_unary complement complement b x

prop_xor
    :: (Iso a b, Bits a, Bits b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_xor a b =
  property $ do
    x <- forAll a
    y <- forAll a
    prop_binary xor xor b x y

prop_band
    :: (Iso a b, Bits a, Bits b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_band a b =
  property $ do
    x <- forAll a
    y <- forAll a
    prop_binary (.&.) (.&.) b x y

prop_bor
    :: (Iso a b, Bits a, Bits b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_bor a b =
  property $ do
    x <- forAll a
    y <- forAll a
    prop_binary (.|.) (.|.) b x y

prop_shiftL
    :: (Iso a b, FiniteBits a, FiniteBits b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_shiftL a b =
  property $ do
    x <- forAll a
    n <- forAll (Gen.int (Range.linear 0 (finiteBitSize x)))
    prop_unary (`shiftL` n) (`shiftL` n) b x

prop_shiftR
    :: (Iso a b, FiniteBits a, FiniteBits b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_shiftR a b =
  property $ do
    x <- forAll a
    n <- forAll (Gen.int (Range.linear 0 (finiteBitSize x)))
    prop_unary (`shiftR` n) (`shiftR` n) b x

prop_rotateL
    :: (Iso a b, FiniteBits a, FiniteBits b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_rotateL a b =
  property $ do
    x <- forAll a
    n <- forAll (Gen.int (Range.linear 0 (finiteBitSize x)))
    prop_unary (`rotateL` n) (`rotateL` n) b x

prop_rotateR
    :: (Iso a b, FiniteBits a, FiniteBits b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_rotateR a b =
  property $ do
    x <- forAll a
    n <- forAll (Gen.int (Range.linear 0 (finiteBitSize x)))
    prop_unary (`rotateR` n) (`rotateR` n) b x

prop_shift
    :: (Iso a b, FiniteBits a, FiniteBits b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_shift a b =
  property $ do
    x <- forAll a
    n <- forAll (Gen.int (Range.linearFrom 0 (-finiteBitSize x) (finiteBitSize x)))
    prop_unary (`shift` n) (`shift` n) b x

prop_rotate
    :: (Iso a b, FiniteBits a, FiniteBits b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_rotate a b =
  property $ do
    x <- forAll a
    n <- forAll (Gen.int (Range.linearFrom 0 (-finiteBitSize x) (finiteBitSize x)))
    prop_unary (`rotate` n) (`rotate` n) b x

prop_bit
    :: forall a b. (Iso a b, FiniteBits a, FiniteBits b, Show a, Show b)
    => Proxy b
    -> Property
prop_bit b =
  property $ do
    mapM_ (\i -> bit i === fromIso b (bit i)) [0 .. finiteBitSize (undefined::a) - 1]

prop_testBit
    :: (Iso a b, FiniteBits a, FiniteBits b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_testBit  a b =
  property $ do
    x <- forAll a
    n <- forAll (Gen.int (Range.linear 0 (finiteBitSize x)))
    prop_unary' (`testBit` n) (`testBit` n) b x

prop_setBit
    :: (Iso a b, FiniteBits a, FiniteBits b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_setBit a b =
  property $ do
    x <- forAll a
    n <- forAll (Gen.int (Range.linear 0 (finiteBitSize x)))
    prop_unary (`setBit` n) (`setBit` n) b x

prop_clearBit
    :: (Iso a b, FiniteBits a, FiniteBits b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_clearBit a b =
  property $ do
    x <- forAll a
    n <- forAll (Gen.int (Range.linear 0 (finiteBitSize x)))
    prop_unary (`clearBit` n) (`clearBit` n) b x

prop_complementBit
    :: (Iso a b, FiniteBits a, FiniteBits b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_complementBit a b =
  property $ do
    x <- forAll a
    n <- forAll (Gen.int (Range.linear 0 (finiteBitSize x)))
    prop_unary (`complementBit` n) (`complementBit` n) b x

prop_popCount
    :: (Iso a b, FiniteBits a, FiniteBits b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_popCount a b =
  property $ do
    x <- forAll a
    prop_unary' popCount popCount b x


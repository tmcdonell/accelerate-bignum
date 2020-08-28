{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds   #-}
{-# LANGUAGE RankNTypes       #-}
-- |
-- Module      : Test.BigNum.Integral
-- Copyright   : [2017..2020] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Test.BigNum.Integral ( test_integral )
  where

import Test.Iso
import Test.Base
import Test.Types
import Test.ShowType

import qualified Data.Array.Accelerate                              as A

import Data.Proxy
import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog


test_integral :: RunN -> TestTree
test_integral runN =
  testGroup "Integral"
    [ testElt i64 (Proxy :: Proxy I64)
    , testElt w64 (Proxy :: Proxy U64)
    , testElt i64 (Proxy :: Proxy II64)
    , testElt w64 (Proxy :: Proxy UU64)
    , testAcc w96
    , testAcc i96
    , testAcc w128
    , testAcc i128
    ]
  where
    testElt :: (Iso a b, Eq a, Eq b, Integral a, Integral b, Show a, Show b, Show (ArgType b))
            => Gen a
            -> Proxy b
            -> TestTree
    testElt a b =
      testGroup (showType b)
        [ testProperty "quot"       $ prop_quot a b
        , testProperty "rem"        $ prop_rem a b
        , testProperty "div"        $ prop_div a b
        , testProperty "mod"        $ prop_mod a b
        , testProperty "quotRem"    $ prop_quotRem a b
        , testProperty "divMod"     $ prop_divMod a b
        , testProperty "toInteger"  $ prop_toInteger a b
        ]

    testAcc :: (Show a, Eq a, Integral a, A.Integral a, Show (ArgType a))
            => Gen a
            -> TestTree
    testAcc a =
      testGroup (showType a)
        [ testProperty "quot"    $ prop_acc_quot runN a
        , testProperty "rem"     $ prop_acc_rem runN a
        , testProperty "quotRem" $ prop_acc_quotRem runN a
        , testProperty "div"     $ prop_acc_div runN a
        , testProperty "mod"     $ prop_acc_mod runN a
        , testProperty "divMod"  $ prop_acc_divMod runN a
        ]


prop_quot
    :: (Iso a b, Integral a, Integral b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_quot a b =
  property $ do
    x <- forAll a
    y <- forAll (a `except` (== 0))
    prop_binary quot quot b x y

prop_rem
    :: (Iso a b, Integral a, Integral b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_rem a b =
  property $ do
    x <- forAll a
    y <- forAll (a `except` (== 0))
    prop_binary rem rem b x y

prop_div
    :: (Iso a b, Integral a, Integral b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_div a b =
  property $ do
    x <- forAll a
    y <- forAll (a `except` (== 0))
    prop_binary div div b x y

prop_mod
    :: (Iso a b, Integral a, Integral b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_mod a b =
  property $ do
    x <- forAll a
    y <- forAll (a `except` (== 0))
    prop_binary mod mod b x y

prop_quotRem
    :: (Iso a b, Integral a, Integral b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_quotRem a b =
  property $ do
    x <- forAll a
    y <- forAll (a `except` (== 0))
    let qr    = quotRem x y
        (q,r) = quotRem (toIso b x) (toIso b y)
    --
    qr === (fromIso b q, fromIso b r)

prop_divMod
    :: (Iso a b, Integral a, Integral b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_divMod a b =
  property $ do
    x <- forAll a
    y <- forAll (a `except` (== 0))
    let qr    = divMod x y
        (q,r) = divMod (toIso b x) (toIso b y)
    --
    qr === (fromIso b q, fromIso b r)

prop_toInteger
    :: (Iso a b, Integral a, Integral b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_toInteger a b =
  property $ do
    x <- forAll a
    prop_unary' toInteger toInteger b x

prop_acc_quot
    :: (Show a, Integral a, A.Integral a)
    => RunN
    -> Gen a
    -> Property
prop_acc_quot runN a =
  property $ do
    x <- forAll a
    y <- forAll (a `except` (== 0))
    prop_acc_binary quot quot runN x y

prop_acc_rem
    :: (Show a, Integral a, A.Integral a)
    => RunN
    -> Gen a
    -> Property
prop_acc_rem runN a =
  property $ do
    x <- forAll a
    y <- forAll (a `except` (== 0))
    prop_acc_binary rem rem runN x y

prop_acc_div
    :: (Show a, Integral a, A.Integral a)
    => RunN
    -> Gen a
    -> Property
prop_acc_div runN a =
  property $ do
    x <- forAll a
    y <- forAll (a `except` (== 0))
    prop_acc_binary div div runN x y

prop_acc_mod
    :: (Show a, Integral a, A.Integral a)
    => RunN
    -> Gen a
    -> Property
prop_acc_mod runN a =
  property $ do
    x <- forAll a
    y <- forAll (a `except` (== 0))
    prop_acc_binary mod mod runN x y

prop_acc_quotRem
    :: (Show a, Integral a, A.Integral a)
    => RunN
    -> Gen a
    -> Property
prop_acc_quotRem runN a =
  property $ do
    x <- forAll a
    y <- forAll (a `except` (== 0))
    prop_acc_binary quotRem (A.lift $$ quotRem) runN x y

prop_acc_divMod
    :: (Show a, Integral a, A.Integral a)
    => RunN
    -> Gen a
    -> Property
prop_acc_divMod runN a =
  property $ do
    x <- forAll a
    y <- forAll (a `except` (== 0))
    prop_acc_binary divMod  (A.lift $$ divMod) runN x y


{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
-- |
-- Module      : Test.BigNum.Real
-- Copyright   : [2017..2020] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Test.BigNum.Real ( test_real )
  where

import Test.Iso
import Test.Base
import Test.Types
import Test.ShowType

import Data.Proxy
import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog


test_real :: TestTree
test_real =
  testGroup "Real"
    [ testElt i64 (Proxy :: Proxy I64)
    , testElt w64 (Proxy :: Proxy U64)
    , testElt i64 (Proxy :: Proxy II64)
    , testElt w64 (Proxy :: Proxy UU64)
    ]
  where
    testElt :: (Iso a b, Eq a, Eq b, Real a, Real b, Show a, Show b, Show (ArgType b))
            => Gen a
            -> Proxy b
            -> TestTree
    testElt a b =
      testGroup (showType b)
        [ testProperty "toRational" $ prop_toRational a b
        ]


prop_toRational
    :: (Iso a b, Real a, Real b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_toRational a b =
  property $ do
    x <- forAll a
    prop_unary' toRational toRational b x


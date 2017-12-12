{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
-- |
-- Module      : Test.BigNum.Ord
-- Copyright   : [2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Test.BigNum.Ord ( test_ord )
  where

import Test.Iso
import Test.Base
import Test.ShowType

import Data.Proxy
import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog


test_ord :: TestTree
test_ord =
  testGroup "Ord"
    [ testElt i64 (Proxy :: Proxy I64)
    , testElt w64 (Proxy :: Proxy U64)
    , testElt i64 (Proxy :: Proxy II64)
    , testElt w64 (Proxy :: Proxy UU64)
    ]
  where
    testElt :: (Iso a b, Ord a, Ord b, Show a, Show b, Show (ArgType b))
            => Gen a
            -> Proxy b
            -> TestTree
    testElt a b =
      testGroup (showType b)
        [ testProperty "compare" $ prop_compare a b
        ]


prop_compare
    :: (Iso a b, Ord a, Ord b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_compare a b =
  property $ do
    x <- forAll a
    y <- forAll a
    prop_binary' compare compare b x y


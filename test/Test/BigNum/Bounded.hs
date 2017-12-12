{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
-- |
-- Module      : Test.BigNum.Bounded
-- Copyright   : [2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Test.BigNum.Bounded ( test_bounded )
  where

import Test.Iso
import Test.Base
import Test.ShowType

import Data.Proxy
import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog


test_bounded :: TestTree
test_bounded =
  testGroup "Bounded"
    [ testElt (Proxy :: Proxy I64)
    , testElt (Proxy :: Proxy U64)
    , testElt (Proxy :: Proxy II64)
    , testElt (Proxy :: Proxy UU64)
    ]
  where
    testElt :: (Iso a b, Eq a, Bounded a, Bounded b, Show a, Show b, Show (ArgType b))
            => Proxy b
            -> TestTree
    testElt p =
      testGroup (showType p)
        [ testProperty "minBound" $ prop_minBound p
        , testProperty "maxBound" $ prop_maxBound p
        ]


prop_minBound
    :: (Iso a b, Bounded a, Bounded b, Eq a, Show a)
    => Proxy b
    -> Property
prop_minBound p =
  property $ do
    minBound === fromIso p minBound

prop_maxBound
    :: (Iso a b, Bounded a, Bounded b, Eq a, Show a)
    => Proxy b
    -> Property
prop_maxBound p =
  property $ do
    maxBound === fromIso p maxBound


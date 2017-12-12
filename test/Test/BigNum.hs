{-# LANGUAGE RankNTypes #-}
-- |
-- Module      : Test.BigNum
-- Copyright   : [2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Test.BigNum where

import Test.Base
import Test.BigNum.Num2

import Test.Tasty
import Test.Tasty.Hedgehog
import System.Environment


bignum :: RunN -> IO ()
bignum runN = do
  me <- getProgName
  defaultMain
    $ localOption (HedgehogTestLimit 10000)
    $ testGroup me
        [ test_num2
        ]


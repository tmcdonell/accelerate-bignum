-- |
-- Module      : TestPTX
-- Copyright   : [2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module TestPTX
  where

import Test.BigNum
import Data.Array.Accelerate.LLVM.PTX                               as PTX

main :: IO ()
main = bignum PTX.runN


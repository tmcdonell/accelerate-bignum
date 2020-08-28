-- |
-- Module      : TestPTX
-- Copyright   : [2017..2020] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module TestPTX
  where

import Test.BigNum
import Data.Array.Accelerate.LLVM.PTX                               as PTX

main :: IO ()
main = bignum PTX.runN


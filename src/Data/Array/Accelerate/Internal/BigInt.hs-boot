-- |
-- Module      : Data.Array.Accelerate.Internal.BigInt-boot
-- Copyright   : [2016] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Internal.BigInt
  where

-- | Large integers of fixed size represented as separate (signed) high and
-- (unsigned) low words.
--
data BigInt hi lo = I2 !hi !lo


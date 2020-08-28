-- |
-- Module      : Data.Array.Accelerate.Data.BigInt
-- Copyright   : [2016..2020] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Fixed length signed integer types
--

module Data.Array.Accelerate.Data.BigInt (

  Int96,
  Int128,
  Int160,
  Int192,
  Int224,
  Int256,
  Int512,

  -- ** Internals
  BigInt(..),
  Num2(..)

) where

import Data.Array.Accelerate.Internal.Num2
import Data.Array.Accelerate.Internal.BigInt
import Data.Array.Accelerate.Internal.Orphans ()


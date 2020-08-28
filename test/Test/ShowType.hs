{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |
-- Module      : Test.ShowType
-- Copyright   : [2017..2020] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Test.ShowType ( ArgType, showType )
  where

import Data.Bits
import Data.Int
import Data.Word
import Text.Printf

import Test.Types

import Data.Array.Accelerate.Data.BigInt
import Data.Array.Accelerate.Data.BigWord


showType :: forall proxy a. Show (ArgType a) => proxy a -> String
showType _ = show (AT :: ArgType a)

data ArgType (a :: *) = AT

instance FiniteBits (BigWord a b) => Show (ArgType (BigWord a b)) where
  show _ = printf "Word%d" (finiteBitSize (undefined::BigWord a b))

instance FiniteBits (BigInt a b) => Show (ArgType (BigInt a b)) where
  show _ = printf "Int%d" (finiteBitSize (undefined::BigInt a b))

instance Show (ArgType Int8)   where show _ = "Int8"
instance Show (ArgType Int16)  where show _ = "Int16"
instance Show (ArgType Int32)  where show _ = "Int32"
instance Show (ArgType Int64)  where show _ = "Int64"
instance Show (ArgType Word8)  where show _ = "Word8"
instance Show (ArgType Word16) where show _ = "Word16"
instance Show (ArgType Word32) where show _ = "Word32"
instance Show (ArgType Word64) where show _ = "Word64"

instance Show (ArgType I64)    where show _ = "I64"
instance Show (ArgType U64)    where show _ = "U64"
instance Show (ArgType II64)   where show _ = "II64"
instance Show (ArgType UU64)   where show _ = "UU64"


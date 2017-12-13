{-# LANGUAGE BangPatterns           #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeSynonymInstances   #-}
-- |
-- Module      : Test.Iso
-- Copyright   : [2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Test.Iso where

import Test.Base

import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate                                        ( Exp )
import qualified Data.Array.Accelerate                              as A

import Hedgehog


class Iso a b | b -> a where
  isoR :: a -> b
  isoL :: b -> a

fromIso :: Iso a b => proxy b -> b -> a
fromIso _ = isoL

toIso :: Iso a b => proxy b -> a -> b
toIso _ = isoR

instance Elt a => Iso a (Scalar a) where
  isoR x = fromFunction Z (const x)
  isoL x = x ! Z


with_unary :: Iso a b => proxy b -> (b -> b) -> a -> a
with_unary _ f = isoL . f . isoR

with_unary' :: Iso a b => proxy b -> (b -> r) -> a -> r
with_unary' _ f x = f (isoR x)

with_binary :: Iso a b => proxy b -> (b -> b -> b) -> a -> a -> a
with_binary _ f x y = isoL $ f (isoR x) (isoR y)

with_binary' :: Iso a b => proxy b -> (b -> b -> r) -> a -> a -> r
with_binary' _ f x y = f (isoR x) (isoR y)


prop_unary
    :: (Iso a b, Eq a, Show a, MonadTest m)
    => (a -> a)
    -> (b -> b)
    -> proxy b
    -> a
    -> m ()
prop_unary f g p x = f x === with_unary p g x

prop_unary'
    :: (Iso a b, Eq r, Show r, MonadTest m)
    => (a -> r)
    -> (b -> r)
    -> proxy b
    -> a
    -> m ()
prop_unary' f g p x = f x === with_unary' p g x

prop_binary
    :: (Iso a b, Eq a, Show a, MonadTest m)
    => (a -> a -> a)
    -> (b -> b -> b)
    -> proxy b
    -> a
    -> a
    -> m ()
prop_binary f g p x y = f x y === with_binary p g x y

prop_binary'
    :: (Iso a b, Eq r, Show r, MonadTest m)
    => (a -> a -> r)
    -> (b -> b -> r)
    -> proxy b
    -> a
    -> a
    -> m ()
prop_binary' f g p x y = f x y === with_binary' p g x y


{-# INLINE with_acc_unary #-}
with_acc_unary
    :: forall a b. (Elt a, Elt b)
    => RunN
    -> (Exp a -> Exp b)
    -> a
    -> b
with_acc_unary runN f = isoL . go . isoR
  where
    go :: Scalar a -> Scalar b
    !go = runN (A.map f)

{-# INLINE with_acc_binary #-}
with_acc_binary
    :: forall a b c. (Elt a, Elt b, Elt c)
    => RunN
    -> (Exp a -> Exp b -> Exp c)
    -> a
    -> b
    -> c
with_acc_binary runN f x y = isoL $ go (isoR x) (isoR y)
  where
    go :: Scalar a -> Scalar b -> Scalar c
    !go = runN (A.zipWith f)

{-# INLINE prop_acc_unary #-}
prop_acc_unary
    :: (Elt a, Elt b, Eq b, MonadTest m)
    => (a -> b)
    -> (Exp a -> Exp b)
    -> RunN
    -> a
    -> m ()
prop_acc_unary f g runN x = f x === with_acc_unary runN g x

{-# INLINE prop_acc_binary #-}
prop_acc_binary
    :: (Elt a, Elt b, Elt c, Eq c, MonadTest m)
    => (a -> b -> c)
    -> (Exp a -> Exp b -> Exp c)
    -> RunN
    -> a
    -> b
    -> m ()
prop_acc_binary f g runN x y = f x y === with_acc_binary runN g x y


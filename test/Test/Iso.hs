{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
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


class Iso a b | b -> a where
  isoR :: a -> b
  isoL :: b -> a

fromIso :: Iso a b => proxy b -> b -> a
fromIso _ = isoL

toIso :: Iso a b => proxy b -> a -> b
toIso _ = isoR


with_unary :: Iso a b => proxy b -> (b -> b) -> a -> a
with_unary _ f = isoL . f . isoR

with_unary' :: Iso a b => proxy b -> (b -> r) -> a -> r
with_unary' _ f x = f (isoR x)

with_binary :: Iso a b => proxy b -> (b -> b -> b) -> a -> a -> a
with_binary _ f x y = isoL $ f (isoR x) (isoR y)

with_binary' :: Iso a b => proxy b -> (b -> b -> r) -> a -> a -> r
with_binary' _ f x y = f (isoR x) (isoR y)


prop_unary :: (Iso a b, Eq a) => (a -> a) -> (b -> b) -> proxy b -> a -> Bool
prop_unary f g p x = f x == with_unary p g x

prop_unary' :: (Iso a b, Eq r) => (a -> r) -> (b -> r) -> proxy b -> a -> Bool
prop_unary' f g p x = f x == with_unary' p g x

prop_binary :: (Iso a b, Eq a) => (a -> a -> a) -> (b -> b -> b) -> proxy b -> a -> a -> Bool
prop_binary f g p x y = f x y == with_binary p g x y

prop_binary' :: (Iso a b, Eq r) => (a -> a -> r) -> (b -> b -> r) -> proxy b -> a -> a -> Bool
prop_binary'  f g p x y = f x y == with_binary' p g x y


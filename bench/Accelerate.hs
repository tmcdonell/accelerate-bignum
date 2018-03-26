{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Accelerate where

import Data.Array.Accelerate                                        as A
import Data.Array.Accelerate.Data.Bits                              as A
import Data.Array.Accelerate.Data.BigWord
import Data.Array.Accelerate.Data.BigInt
#if !MIN_VERSION_accelerate_io(1,2,0)
import Data.Array.Accelerate.IO
#else
import Data.Array.Accelerate.IO.Data.Vector.Storable
#endif

import Criterion.Main
import Data.Proxy
import Prelude                                                      ( String, Show(..), undefined )
import Text.Printf
import qualified Data.Bits                                          as P
import qualified Data.Vector.Unboxed                                as U
import qualified Prelude                                            as P


benchmark
    :: String
    -> (forall a b. (Arrays a, Arrays b) => (Acc a -> Acc b) -> a -> b)
    -> U.Vector Word64
    -> U.Vector Word64
    -> U.Vector Word64
    -> U.Vector Word64
    -> U.Vector Int
    -> Benchmark
benchmark backend run1 xhi xlo yhi ylo ss =
  bgroup backend
    [ bench_word128 run1 xhi xlo yhi ylo ss
    , bench_int128  run1 xhi xlo yhi ylo ss
    ]

bench_word128
    :: (forall a b. (Arrays a, Arrays b) => (Acc a -> Acc b) -> a -> b)
    -> U.Vector Word64
    -> U.Vector Word64
    -> U.Vector Word64
    -> U.Vector Word64
    -> U.Vector Int
    -> Benchmark
bench_word128 run1 xhi xlo yhi ylo ss =
  let
      n   = U.length xhi
      xs  = fromVectors (Z :. n) (((), U.convert xhi), U.convert xlo) :: Vector Word128
      ys  = fromVectors (Z :. n) (((), U.convert yhi), U.convert ylo) :: Vector Word128
      --
      ss' = fromVectors (Z :. U.length ss) (U.convert ss)             :: Vector Int
      sa' = fromVectors (Z :. U.length ss) (U.convert (U.map abs ss)) :: Vector Int
  in
  mkBench run1 xs ys ss' sa'

bench_int128
    :: (forall a b. (Arrays a, Arrays b) => (Acc a -> Acc b) -> a -> b)
    -> U.Vector Word64
    -> U.Vector Word64
    -> U.Vector Word64
    -> U.Vector Word64
    -> U.Vector Int
    -> Benchmark
bench_int128 run1 xhi xlo yhi ylo ss =
  let
      n   = U.length xhi
      xs  = fromVectors (Z :. n) (((), U.convert (U.map P.fromIntegral xhi)), U.convert xlo) :: Vector Int128
      ys  = fromVectors (Z :. n) (((), U.convert (U.map P.fromIntegral yhi)), U.convert ylo) :: Vector Int128
      --
      ss' = fromVectors (Z :. U.length ss) (U.convert ss)             :: Vector Int
      sa' = fromVectors (Z :. U.length ss) (U.convert (U.map abs ss)) :: Vector Int
  in
  mkBench run1 xs ys ss' sa'


mkBench
    :: forall t. (Show (ArgType t), Elt t, Eq t, Ord t, Num t, Integral t, Bits t, FiniteBits t)
    => (forall a b. (Arrays a, Arrays b) => (Acc a -> Acc b) -> a -> b)
    -> Vector t
    -> Vector t
    -> Vector Int
    -> Vector Int
    -> Benchmark
mkBench run1 !xs !ys !ss !sa =
  let
      xs' = use xs
      ys' = use ys
  in
  bgroup (showType (Proxy::Proxy t))
    [ bgroup "Eq"
      [ bench "(==)"    $ whnf (run1 $ zipWith (==) xs') ys
      , bench "(/=)"    $ whnf (run1 $ zipWith (/=) xs') ys
      ]
    , bgroup "Ord"
      [ bench "(>=)"    $ whnf (run1 $ zipWith (>=) xs') ys
      , bench "(<=)"    $ whnf (run1 $ zipWith (<=) xs') ys
      , bench "(>)"     $ whnf (run1 $ zipWith (>) xs') ys
      , bench "(<)"     $ whnf (run1 $ zipWith (<) xs') ys
      ]
    , bgroup "Num"
      [ bench "(+)"     $ whnf (run1 $ zipWith (+) xs') ys
      , bench "(-)"     $ whnf (run1 $ zipWith (-) xs') ys
      , bench "(*)"     $ whnf (run1 $ zipWith (*) xs') ys
      , bench "negate"  $ whnf (run1 $ map negate) xs
      , bench "abs"     $ whnf (run1 $ map abs) ys
      , bench "signum"  $ whnf (run1 $ map signum) xs
      ]
    , bgroup "Integral"
      [ bench "quot"    $ whnf (run1 $ zipWith quot xs') ys
      , bench "rem"     $ whnf (run1 $ zipWith rem xs') ys
      , bench "quotRem" $ whnf (run1 $ zipWith (lift $$ quotRem) xs') ys
      , bench "div"     $ whnf (run1 $ zipWith div xs') ys
      , bench "mod"     $ whnf (run1 $ zipWith mod xs') ys
      , bench "divMod"  $ whnf (run1 $ zipWith (lift $$ divMod) xs') ys
      ]
    , bgroup "Bits"
      [ bench "(.&.)"         $ whnf (run1 $ zipWith (.&.) xs') ys
      , bench "(.|.)"         $ whnf (run1 $ zipWith (.|.) xs') ys
      , bench "xor"           $ whnf (run1 $ zipWith xor xs') ys
      , bench "complement"    $ whnf (run1 $ map complement) xs
      , bench "shift"         $ whnf (run1 $ zipWith shift xs') ss
      , bench "rotate"        $ whnf (run1 $ zipWith rotate ys') ss
      , bench "setBit"        $ whnf (run1 $ zipWith setBit xs') sa
      , bench "clearBit"      $ whnf (run1 $ zipWith clearBit ys') sa
      , bench "complementBit" $ whnf (run1 $ zipWith complementBit xs') sa
      , bench "testBit"       $ whnf (run1 $ zipWith testBit ys') sa
      , bench "popCount"      $ whnf (run1 $ map popCount) xs
      ]
    , bgroup "FiniteBits"
      [ bench "countLeadingZeros"   $ whnf (run1 $ map countLeadingZeros) xs
      , bench "countTrailingZeros"  $ whnf (run1 $ map countTrailingZeros) ys
      ]
    ]


infixr 0 $$
($$) :: (b -> a) -> (c -> d -> b) -> c -> d -> a
(f $$ g) x y = f (g x y)


data ArgType (a :: *) = AT

showType :: forall proxy a. Show (ArgType a) => proxy a -> String
showType _ = show (AT :: ArgType a)

instance P.FiniteBits (BigWord a b) => Show (ArgType (BigWord a b)) where
  show _ = printf "Word%d" (P.finiteBitSize (undefined::BigWord a b))

instance P.FiniteBits (BigInt a b) => Show (ArgType (BigInt a b)) where
  show _ = printf "Int%d" (P.finiteBitSize (undefined::BigInt a b))


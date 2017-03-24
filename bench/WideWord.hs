{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module WideWord where

import Data.Word
import Data.Bits
import Data.WideWord.Int128
import Data.WideWord.Word128

import Criterion.Main
import Data.Vector.Unboxed                        ( Vector, Unbox )
import Data.Vector.Unboxed.Deriving
import qualified Data.Vector.Unboxed              as U


-- This is the easiest to implement, but not entirely correct; we should keep
-- the structure packed in memory so that the hi and lo words are adjacent. I'll
-- leave @erikd to implement that though...

derivingUnbox "Word128"
  [t| Word128 -> (Word64, Word64) |]
  [| \(Word128 hi lo) -> (hi,lo) |]
  [| \(hi,lo) -> Word128 hi lo |]

derivingUnbox "Int128"
  [t| Int128 -> (Word64, Word64) |]
  [| \(Int128 hi lo) -> (hi,lo) |]
  [| \(hi,lo) -> Int128 hi lo |]


benchmark
    :: Vector Word64
    -> Vector Word64
    -> Vector Word64
    -> Vector Word64
    -> Vector Int
    -> Benchmark
benchmark !xhi !xlo !yhi !ylo !ss =
  bgroup "WideWord"
    [ mkBench "Word128" Word128 xhi xlo yhi ylo ss
    , mkBench "Int128"  Int128  xhi xlo yhi ylo ss
    ]


mkBench
    :: (Unbox t, Eq t, Ord t, Num t, Integral t, Bits t, FiniteBits t)
    => String
    -> (Word64 -> Word64 -> t)
    -> Vector Word64
    -> Vector Word64
    -> Vector Word64
    -> Vector Word64
    -> Vector Int
    -> Benchmark
mkBench ty con xhi xlo yhi ylo ss =
  let
      xs  = U.zipWith con xhi xlo
      ys  = U.zipWith con yhi ylo
      ss' = U.map abs ss
  in
  bgroup ty
    [ bgroup "Eq"
      [ bench "(==)"    $ nf (U.zipWith (==) xs) ys
      , bench "(/=)"    $ nf (U.zipWith (/=) xs) ys
      ]
    , bgroup "Ord"
      [ bench "(>=)"    $ nf (U.zipWith (>=) xs) ys
      , bench "(<=)"    $ nf (U.zipWith (<=) xs) ys
      , bench "(>)"     $ nf (U.zipWith (>) xs) ys
      , bench "(<)"     $ nf (U.zipWith (<) xs) ys
      ]
    , bgroup "Num"
      [ bench "(+)"     $ nf (U.zipWith (+) xs) ys
      , bench "(-)"     $ nf (U.zipWith (-) xs) ys
      , bench "(*)"     $ nf (U.zipWith (*) xs) ys
      , bench "negate"  $ nf (U.map negate) xs
      , bench "abs"     $ nf (U.map abs) ys
      , bench "signum"  $ nf (U.map signum) xs
      ]
    , bgroup "Integral"
      [ bench "quot"    $ nf (U.zipWith quot xs) ys
      , bench "rem"     $ nf (U.zipWith rem xs) ys
      , bench "quotRem" $ nf (U.zipWith quotRem xs) ys
      , bench "div"     $ nf (U.zipWith div xs) ys
      , bench "mod"     $ nf (U.zipWith mod xs) ys
      , bench "divMod"  $ nf (U.zipWith divMod xs) ys
      ]
    , bgroup "Bits"
      [ bench "(.&.)"         $ nf (U.zipWith (.&.) xs) ys
      , bench "(.|.)"         $ nf (U.zipWith (.|.) xs) ys
      , bench "xor"           $ nf (U.zipWith xor xs) ys
      , bench "complement"    $ nf (U.map complement) xs
      , bench "shift"         $ nf (U.zipWith shift xs) ss
      , bench "rotate"        $ nf (U.zipWith rotate ys) ss
      , bench "setBit"        $ nf (U.zipWith setBit xs) ss'
      , bench "clearBit"      $ nf (U.zipWith clearBit ys) ss'
      , bench "complementBit" $ nf (U.zipWith complementBit xs) ss'
      , bench "testBit"       $ nf (U.zipWith testBit ys) ss'
      , bench "popCount"      $ nf (U.map popCount) xs
      ]
    , bgroup "FiniteBits"
      [ bench "countLeadingZeros"   $ nf (U.map countLeadingZeros) xs
      , bench "countTrailingZeros"  $ nf (U.map countTrailingZeros) ys
      ]
    ]


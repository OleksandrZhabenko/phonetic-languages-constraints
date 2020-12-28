-- |
-- Module      :  Languages.UniquenessPeriods.Vector.Constraints
-- Copyright   :  (c) OleksandrZhabenko 2020
-- License     :  MIT
-- Stability   :  Experimental
-- Maintainer  :  olexandr543@yahoo.com
--
-- Provides several the most important variants of constraints for the
-- permutations. All the 'VB.Vector'
-- here must consists of unique 'Int' starting from 0 to n and the 'Int'
-- arguments must be in the range [0..n] though these inner constraints are
-- not checked. It is up to user to check them.
--

{-# LANGUAGE BangPatterns, FlexibleContexts #-}

module Languages.UniquenessPeriods.Vector.Constraints (
  -- * Basic predicate
  unsafeOrderIJ
  -- * Functions to work with permutations with basic constraints ('VB.Vector'-based)
  , filterOrderIJ
  , unsafeTriples
  , unsafeQuadruples
  -- ** With multiple elements specified
  , unsafeSeveralA
  , unsafeSeveralB
) where

import qualified Data.Vector as VB
import Data.Maybe (fromJust)
import Data.SubG (InsertLeft(..),filterG)
import Data.SubG.InstancesPlus

-- | Being given the data satisfying the constraints in the module header checks whether in the 'VB.Vector' the first argument stands before the second one.
unsafeOrderIJ :: Int -> Int -> VB.Vector Int -> Bool
unsafeOrderIJ i j v = fromJust (VB.findIndex (== i) v) < fromJust (VB.findIndex (== j) v)

-- | Being given the data satisfying the constraints in the module header returns the elements that satisfy 'unsafeOrderIJ' as a predicate.
filterOrderIJ :: (InsertLeft t (VB.Vector Int), Monoid (t (VB.Vector Int))) => Int -> Int -> t (VB.Vector Int) -> t (VB.Vector Int)
filterOrderIJ i j = filterG (unsafeOrderIJ i j)

-- | Being given the data satisfying the constraints in the module header reduces the number of further computations in the foldable structure of
-- the permutations each one being represented as 'VB.Vector' 'Int' where 'Int' are all the numbers in the range [0..n] without duplication if the
-- arguments are the indeces of the duplicated words or their concatenated combinations in the corresponding line.
-- The first three arguments
-- are the indices of the the triple duplicated elements (words or their concatenated combinations in the @phonetic-languages@ series of packages).
unsafeTriples :: (InsertLeft t (VB.Vector Int), Monoid (t (VB.Vector Int))) => Int -> Int -> Int -> t (VB.Vector Int) -> t (VB.Vector Int)
unsafeTriples i j k = filterG (\v -> unsafeOrderIJ i j v && unsafeOrderIJ j k v)

-- | Being given the data satisfying the constraints in the module header reduces the number of further computations in the foldable structure of
-- the permutations each one being represented as 'VB.Vector' 'Int' where 'Int' are all the numbers in the range [0..n] without duplication if the
-- arguments are the indeces of the duplicated words or their concatenated combinations in the corresponding line.
-- The first four arguments
-- are the indices of the the quadruple duplicated elements (words or their concatenated combinations in the @phonetic-languages@ series of packages).
unsafeQuadruples :: (InsertLeft t (VB.Vector Int), Monoid (t (VB.Vector Int))) => Int -> Int -> Int -> Int -> t (VB.Vector Int) -> t (VB.Vector Int)
unsafeQuadruples i j k l = filterG (\v -> unsafeOrderIJ i j v && unsafeOrderIJ j k v && unsafeOrderIJ k l v)

-- | Being given the data satisfying the constraints in the module header reduces the number of further computations in the foldable structure of
-- the permutations each one being represented as 'VB.Vector' 'Int' where 'Int' are all the numbers in the range [0..n] without duplication.
-- The first (VB.Vector Int)rgument
-- is the index of the the element (a word or their concatenated combination in the @phonetic-languages@ series of packages), the second argument
-- is 'VB.Vector' of indices that (VB.Vector Int)re in the range [0..n]. Filters (and reduces further complex computtions) the permutations so that only the
-- variants with the indices in the second argument (VB.Vector Int)ll stand AFTER the element with the index equal to the first (VB.Vector Int)rgument.
unsafeSeveralA :: (InsertLeft t (VB.Vector Int), Monoid (t (VB.Vector Int))) => Int -> VB.Vector Int -> t (VB.Vector Int) -> t (VB.Vector Int)
unsafeSeveralA !i0 v1 v2 =
 let j !i !v = fromJust (VB.findIndex (== i) v) in
  filterG (\v -> g i0 j v v1) v2
   where g !i j !v v3 = VB.all (> j i v) . VB.findIndices (`VB.elem` v3) $ v

-- | Being given the data satisfying the constraints in the module header reduces the number of further computations in the foldable structure of
-- the permutations each one being represented as 'VB.Vector' 'Int' where 'Int' are all the numbers in the range [0..n] without duplication.
-- The first (VB.Vector Int)rgument
-- is the index of the the element (a word or their concatenated combination in the @phonetic-languages@ series of packages), the second argument
-- is 'VB.Vector' of indices that (VB.Vector Int)re in the range [0..n]. Filters (and reduces further complex computtions) the permutations so that only the
-- variants with the indices in the second argument (VB.Vector Int)ll stand BEFORE the element with the index equal to the first (VB.Vector Int)rgument.
unsafeSeveralB :: (InsertLeft t (VB.Vector Int), Monoid (t (VB.Vector Int))) => Int -> VB.Vector Int -> t (VB.Vector Int) -> t (VB.Vector Int)
unsafeSeveralB !i0 v1 v2 =
 let j !i !v = fromJust (VB.findIndex (== i) v) in
  filterG (\v -> g i0 j v v1) v2
   where g !i j !v v3 = VB.all (< j i v) . VB.findIndices (`VB.elem` v3) $ v


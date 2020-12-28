-- |
-- Module      :  Languages.UniquenessPeriods.Vector.Constraints.Encoded
-- Copyright   :  (c) OleksandrZhabenko 2020
-- License     :  MIT
-- Stability   :  Experimental
-- Maintainer  :  olexandr543@yahoo.com
--
-- Provides a way to encode the needed constraint with possibly less symbols.
--

{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module Languages.UniquenessPeriods.Vector.Constraints.Encoded (
  -- * Data types
  EncodedContraints(..)
  , EncodedCnstrs
  -- * Functions to work with them
  -- ** Read functions
  , readMaybeEC
  , readMaybeECG
  -- ** Process-encoding functions
  , decodeConstraint1
  , decodeLConstraints
  -- ** Modifiers and getters
  , getIEl
  , setIEl
  -- ** Predicates
  , isE
  , isF
  , isQ
  , isT
  , isSA
  , isSB
) where

import Data.Monoid (mappend)
import Text.Read (readMaybe)
import Data.Maybe
import qualified Data.Vector as VB
--import Data.List
import Languages.UniquenessPeriods.Vector.Constraints
import Data.SubG (InsertLeft(..))
import Data.SubG.InstancesPlus

data EncodedContraints a b = E a | Q a a a a a | T a a a a | SA a a b | SB a a b | F a a a deriving (Eq, Ord)

-- | Inspired by the: https://hackage.haskell.org/package/base-4.14.0.0/docs/Data-Maybe.html
-- Is provided here as a more general way to read the 'String' into a 'EncodedCnstrs' than more restricted
-- but safer 'readMaybeECG'. It is up to user to check whether the parameters are in the correct form, the function does
-- not do the full checking. For phonetic-languages applications, it is better to use 'readMaybeECG' function instead.
readMaybeEC :: Int -> String -> Maybe EncodedCnstrs
readMaybeEC n xs
 | null xs = Nothing
 | n >=0 && n <= 9 =
     let h = take 1 xs
         ts = filter (\x -> x >= '0' && [x] <= show n) . drop 1 $ xs in
      case h of
       "E" -> Just (E (fromMaybe 0 (readMaybe (take 1 . tail $ xs)::Maybe Int)))
       "F" -> let (y,z) = (readMaybe (take 1 ts)::Maybe Int, readMaybe (take 1 . drop 1 $ ts)) in
         case (y,z) of
          (Nothing,_) -> Nothing
          (_,Nothing) -> Nothing
          ~(Just x1, Just x2) -> Just (F undefined x1 x2)
       "T" -> let (y,z,u) = (readMaybe (take 1 ts)::Maybe Int, readMaybe (take 1 . drop 1 $ ts)::Maybe Int, readMaybe (take 1 . drop 2 $ ts)::Maybe Int) in
         case (y,z,u) of
          (Nothing,_,_) -> Nothing
          (_,Nothing,_) -> Nothing
          (_,_,Nothing) -> Nothing
          ~(Just x1, Just x2, Just x3) -> Just (T undefined x1 x2 x3)
       "A" -> let y = readMaybe (take 1 ts)::Maybe Int in
               if isJust y then
                let y0 = fromJust y
                    zs = filter (/= y0) . catMaybes . map (\t -> readMaybe [t]::Maybe Int) . drop 1 $ ts in
                     case zs of
                       [] -> Nothing
                       ~x2 -> Just (SA undefined y0 (VB.fromList x2))
               else Nothing
       "B" -> let y = readMaybe (take 1 ts)::Maybe Int in
               if isJust y then
                let y0 = fromJust y
                    zs = filter (/= y0) . catMaybes . map (\t -> readMaybe [t]::Maybe Int) . drop 1 $ ts in
                     case zs of
                       [] -> Nothing
                       ~x2 -> Just (SB undefined y0 (VB.fromList x2))
               else Nothing
       "Q" -> let (y,z,u,w) = (readMaybe (take 1 ts)::Maybe Int, readMaybe (take 1 . drop 1 $ ts)::Maybe Int, readMaybe (take 1 . drop 2 $ ts)::Maybe Int,
                    readMaybe (take 1 . drop 3 $ ts)::Maybe Int) in
         case (y,z,u,w) of
          (Nothing,_,_,_) -> Nothing
          (_,Nothing,_,_) -> Nothing
          (_,_,Nothing,_) -> Nothing
          (_,_,_,Nothing) -> Nothing
          ~(Just x1, Just x2, Just x3, Just x4) -> Just (Q undefined x1 x2 x3 x4)
       _   -> Nothing
 | otherwise = Nothing

-- | Is used inside 'readMaybeECG' to remove the 'undefined' inside the 'EncodedCnstrs'.
setWordsN :: Int -> Maybe EncodedCnstrs -> Maybe EncodedCnstrs
setWordsN _ Nothing = Nothing
setWordsN _ (Just (E x)) = Just (E x)
setWordsN n (Just (T _ i j k)) = Just (T n i j k)
setWordsN n (Just (Q _ i j k l)) = Just (Q n i j k l)
setWordsN n (Just (SA _ i v)) = Just (SA n i v)
setWordsN n (Just (SB _ i v)) = Just (SB n i v)
setWordsN n (Just (F _ i j)) = Just (F n i j)

-- | A safer variant of the 'readMaybeEC' more suitable for applications, e. g. for phonetic-languages series of packages.
readMaybeECG :: Int -> String -> Maybe EncodedCnstrs
readMaybeECG n xs
  | n <= 6 && n >=0 = setWordsN n . readMaybeEC n $ xs
  | otherwise = Nothing

type EncodedCnstrs = EncodedContraints Int (VB.Vector Int)

-- | Must be applied to the correct vector of permutation indeces. Otherwise, it gives runtime error (exception). All the integers inside the
-- 'EncodedCnstrs' must be in the range [0..n] where @n@ corresponds to the maximum element in the permutation 'VB.Vector' 'Int'. Besides,
-- @n@ is (probably must be) not greater than 6.
decodeConstraint1 :: (InsertLeft t (VB.Vector Int), Monoid (t (VB.Vector Int))) => EncodedCnstrs -> t (VB.Vector Int) -> t (VB.Vector Int)
decodeConstraint1 (E _) = id
decodeConstraint1 (Q _ i j k l) = unsafeQuadruples i j k l
decodeConstraint1 (T _ i j k) = unsafeTriples i j k
decodeConstraint1 (SA _ i v) = unsafeSeveralA i v
decodeConstraint1 (SB _ i v) = unsafeSeveralB i v
decodeConstraint1 (F _ i j) = filterOrderIJ i j

-- | Must be applied to the correct vector of permutation indeces. Otherwise, it gives runtime error (exception). All the integers inside the
-- 'EncodedCnstrs' must be in the range [0..n] where @n@ corresponds to the maximum element in the permutation 'VB.Vector' 'Int'. Besides,
-- @n@ is (probably must be) not greater than 6.
decodeLConstraints :: (InsertLeft t (VB.Vector Int), Monoid (t (VB.Vector Int))) => [EncodedCnstrs] -> t (VB.Vector Int) -> t (VB.Vector Int)
decodeLConstraints (x:xs) = decodeLConstraints' ys . decodeConstraint1 y
  where y = minimum (x:xs)
        ys = filter (/= y) . g $ (x:xs)
        g ((E _):zs) = g zs
        g (z:zs) = z : g zs
        g _ = []
        decodeLConstraints' (z:zs) = decodeLConstraints' zs . decodeConstraint1 z
        decodeLConstraints' _ = id
decodeLConstraints _ = id

isE :: EncodedCnstrs -> Bool
isE (E _) = True
isE _ = False

isF :: EncodedCnstrs -> Bool
isF (F _ _ _) = True
isF _ = False

isT :: EncodedCnstrs -> Bool
isT (T _ _ _ _) = True
isT _ = False

isQ :: EncodedCnstrs -> Bool
isQ (Q _ _ _ _ _) = True
isQ _ = False

isSA :: EncodedCnstrs -> Bool
isSA (SA _ _ _) = True
isSA _ = False

isSB :: EncodedCnstrs -> Bool
isSB (SB _ _ _) = True
isSB _ = False

getIEl :: EncodedCnstrs -> Int
getIEl (E i) = i
getIEl (Q _ i _ _ _) = i
getIEl (T _ i _ _) = i
getIEl (SA _ i _) = i
getIEl (SB _ i _) = i
getIEl (F _ i _) = i

setIEl :: Int -> EncodedCnstrs -> EncodedCnstrs
setIEl i (E _) = E i
setIEl i (Q n _ j k l) = Q n i j k l
setIEl i (T n _ j k) = T n i j k
setIEl i (SA n _ v) = SA n i v
setIEl i (SB n _ v) = SB n i v
setIEl i (F n _ j) = F n i j



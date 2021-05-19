-- |
-- Module      : test
-- Copyright   : (c) Justus Sagemüller 2021
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UnicodeSyntax        #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}

import qualified Prelude as Hask
import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.AffineSpace
import Data.Basis
import Math.LinearMap.Category
import Math.Manifold.Core.Types
import Math.Manifold.Core.PseudoAffine

import Test.Tasty
import Test.Tasty.QuickCheck
import qualified Test.QuickCheck as QC



newtype ℝ⁵ = ℝ⁵ { getℝ⁵ :: [ℝ] }
 deriving (Eq, Show)

instance AdditiveGroup ℝ⁵ where
  zeroV = ℝ⁵ $ replicate 5 0
  ℝ⁵ v ^+^ ℝ⁵ w = ℝ⁵ $ zipWith (+) v w
  negateV (ℝ⁵ v)  = ℝ⁵ $ map negate v

instance VectorSpace ℝ⁵ where
  type Scalar ℝ⁵ = ℝ
  μ*^ℝ⁵ v = ℝ⁵ $ map (μ*) v

type Z5 = Z3+Z2
type Z3 = Z2+()
type Z2 = ()+()

instance (Enum a, Bounded a, Enum b, Bounded b) => Enum (Either a b) where
  enumFromTo (Left l) (Left r) = Left <$> enumFromTo l r
  enumFromTo (Left l) (Right r) = (Left <$> enumFromTo l maxBound)
                                ++ (Right <$> enumFromTo minBound r)
  enumFromTo (Right l) (Right r) = Right <$> enumFromTo l r
instance (Enum a, Bounded a, Enum b, Bounded b) => Bounded (Either a b) where
  minBound = Left minBound
  maxBound = Right maxBound

instance HasBasis ℝ⁵ where
  type Basis ℝ⁵ = Z5
  basisValue (Left (Left (Left  ()))) = ℝ⁵ [1,0,0,0,0]
  basisValue (Left (Left (Right ()))) = ℝ⁵ [0,1,0,0,0]
  basisValue (Left (Right     ()   )) = ℝ⁵ [0,0,1,0,0]
  basisValue (Right (Left     ()   )) = ℝ⁵ [0,0,0,1,0]
  basisValue (Right (Right    ()   )) = ℝ⁵ [0,0,0,0,1]
  decompose (ℝ⁵ [a,b,c,d,e]) = 
   [ (Left (Left (Left  ())), a)
   , (Left (Left (Right ())), b)
   , (Left (Right     ()   ), c)
   , (Right (Left     ()   ), d)
   , (Right (Right    ()   ), e) ]
  decompose' (ℝ⁵ [a,b,c,d,e]) n = case n of
   Left (Left (Left  ())) ->  a
   Left (Left (Right ())) ->  b
   Left (Right     ()   ) ->  c
   Right (Left     ()   ) ->  d
   Right (Right    ()   ) ->  e

instance Arbitrary ℝ⁵ where
  arbitrary = ℝ⁵ <$> QC.vectorOf 5 arbitrary

makeLinearSpaceFromBasis [t| ℝ⁵ |]

main :: IO ()
main = do
  defaultMain $ testGroup "Tests"
   [ testGroup "Basis-derived space"
    [ testProperty "Semimanifold addition"
     $ \v w -> v.+~^w === (v^+^w :: ℝ⁵)
    ]
   ]


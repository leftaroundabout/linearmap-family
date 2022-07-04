-- |
-- Module      : test
-- Copyright   : (c) Justus Sagemüller 2021
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies         #-}

import qualified Prelude as Hask
import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.AffineSpace
import Linear.V4
import Data.Basis
import Math.LinearMap.Category
import Math.Manifold.Core.Types
import Math.Manifold.Core.PseudoAffine

import Test.Tasty
import Test.Tasty.QuickCheck
import qualified Test.QuickCheck as QC


newtype ℝ⁴ = ℝ⁴ { getℝ⁴ :: V4 ℝ }
 deriving (Eq, Show)

copyNewtypeInstances [t| ℝ⁴ |]
   [ ''AdditiveGroup, ''AffineSpace, ''VectorSpace
   , ''Semimanifold, ''PseudoAffine
   , ''TensorSpace, ''LinearSpace ]

newtype ℝ⁵ a = ℝ⁵ { getℝ⁵ :: [ℝ] }
 deriving (Eq, Show)

instance AdditiveGroup (ℝ⁵ a) where
  zeroV = ℝ⁵ $ replicate 5 0
  ℝ⁵ v ^+^ ℝ⁵ w = ℝ⁵ $ zipWith (+) v w
  negateV (ℝ⁵ v)  = ℝ⁵ $ map negate v

instance VectorSpace (ℝ⁵ a) where
  type Scalar (ℝ⁵ a) = ℝ
  μ*^ℝ⁵ v = ℝ⁵ $ map (μ*) v

instance InnerSpace (ℝ⁵ a) where
  ℝ⁵ v <.> ℝ⁵ w = sum $ zipWith (*) v w

type Z5 = Z3+Z2
type Z3 = Z2+()
type Z2 = ()+()

instance Num a => HasBasis (ℝ⁵ a) where
  type Basis (ℝ⁵ a) = Z5
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

instance Arbitrary (ℝ⁵ a) where
  arbitrary = ℝ⁵ <$> QC.vectorOf 5 arbitrary

makeFiniteDimensionalFromBasis [t| ∀ a . Num a => ℝ⁵ a |]

newtype H¹ℝ⁵ = H¹ℝ⁵ { getH¹ℝ⁵ :: ℝ⁵ Int }
 deriving newtype (Eq, Show, AdditiveGroup, VectorSpace, HasBasis, Arbitrary)

makeFiniteDimensionalFromBasis [t| H¹ℝ⁵ |]

derivative :: H¹ℝ⁵ -> ℝ⁵ Int
derivative (H¹ℝ⁵ (ℝ⁵ (x₀:xs))) = ℝ⁵ (x₀:xs) ^-^ ℝ⁵ (xs++[x₀])

instance InnerSpace H¹ℝ⁵ where
  H¹ℝ⁵ v <.> H¹ℝ⁵ w = v<.>w + derivative (H¹ℝ⁵ v)<.>derivative (H¹ℝ⁵ w)

instance Arbitrary (V4 ℝ) where
  arbitrary = V4<$>arbitrary<*>arbitrary<*>arbitrary<*>arbitrary



main :: IO ()
main = do
  defaultMain $ testGroup "Tests"
   [ testGroup "Euclidean space"
    [ testProperty "co-Riesz inversion"
     $ \v -> (arr coRiesz\$coRiesz-+$>v) === (v :: V4 ℝ)
    , testProperty "Random operator inversion"      -- This isn't really expected to work
     $ \f v -> (f \$ (f :: V4 ℝ+>V4 ℝ) $ v) ≈≈≈ v   -- /always/, but singular matrices are
    ]                                               -- very seldom in the @Arbitrary@ instance.
   , testGroup "Basis-derived space"
    [ testProperty "Semimanifold addition"
     $ \v w -> v.+~^w === (v^+^w :: ℝ⁵ Int)
    , testProperty "Riesz representation, orthonormal basis"
     $ \v -> (riesz-+$>coRiesz-+$>v) === (v :: ℝ⁵ Int)
    , testProperty "Riesz representation, non-orthonormal basis"
     $ \v -> (riesz-+$>coRiesz-+$>v) ≈≈≈ (v :: H¹ℝ⁵)
    ]
   , testGroup "Newtype-derived space"
    [ testProperty "Addition"
     $ \v w -> ℝ⁴ v^+^ℝ⁴ w === ℝ⁴ (v^+^w)
    ]
   ]


(≈≈≈) :: (InnerSpace v, Show v, Eq v, RealFrac (Scalar v))
            => v -> v -> QC.Property
v≈≈≈w
 | magnitudeSq (v^-^w) < (magnitudeSq v + magnitudeSq w)*1e-8   = QC.property True
 | otherwise                                                    = v===w

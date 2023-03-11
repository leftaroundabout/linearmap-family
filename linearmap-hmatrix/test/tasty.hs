-- |
-- Module      : tasty
-- Copyright   : (c) Justus Sagemüller 2023
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
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE UndecidableInstances       #-}

import qualified Prelude as Hask
import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Numeric.LinearAlgebra.Static.Orphans
import Numeric.LinearAlgebra.Static as HMatS hiding ((===), (<.>), ℝ)
import qualified Numeric.LinearAlgebra as HMat

import Data.AffineSpace
import Linear.V3
import Linear.V4
import Data.Basis
import Data.Coerce
import Math.LinearMap.Category
import Math.VectorSpace.DimensionAware (toArray, fromArray, unsafeFromArray)
import Math.Manifold.Core.Types
import Math.Manifold.Core.PseudoAffine

import GHC.TypeLits (KnownNat, natVal)
import Data.Proxy (Proxy(..))
import Data.Function (on)

import Test.Tasty
import Test.Tasty.QuickCheck
import qualified Test.QuickCheck as QC

import qualified Data.Vector.Unboxed as UArr



main :: IO ()
main = do
  defaultMain $ testGroup "Tests"
   [ testGroup "Vector-space basics"
    [ testProperty "Addition associativity"
       $ \v w x -> (v^+^w)^+^x ≈≈≈ v^+^(w^+^x :: R 27)
    , testProperty "Addition commutativity"
       $ \v w -> v^+^w === (w^+^v :: R 39)
    , testProperty "Scalar distributivity"
       $ \μ v w -> μ*^(v^+^w) ≈≈≈ μ*^v ^+^ μ*^(w :: R 92)
    , testProperty "Inner product bilinearity"
       $ \μ u v ν w x -> (μ*^u ^+^ v)<.>(ν*^w ^+^ x :: R 512)
                      ≈≈≈ μ*ν*(u<.>w) + μ*(u<.>x) + ν*(v<.>w) + v<.>x
    ]
   , testGroup "Linear maps"
    [ testProperty "Identity"
       $ \v -> (linearId $ v :: R 7968) === v
    , testProperty "Linearity"
       $ \f μ v w -> ((f :: R 67+>R 86) $ μ*^v ^+^ w)
                    ≈≈≈ μ*^(f $ v) ^+^ (f $ w)
    , testProperty "Linear space of maps"
       $ \μ f g v -> ((μ*^f ^+^ g :: R 67+>R 86) $ v)
                    ≈≈≈ μ*^(f $ v) ^+^ (g $ v)
    , testProperty "Composition"
       $ \f g v -> (f . g $ v)
                  ≈≈≈ ((f :: R 21+>R 20) $ g $ (v :: R 22))
    , testProperty "Composition associativity"
       $ \f g h -> (f . g :: R 6+>R 8) . h
                  ≈≈≈ f . (g . h :: R 7+>R 9)
    ]
   ]


instance ∀ n . KnownNat n => Arbitrary (R n) where
  arbitrary = HMatS.fromList <$> vectorOf n arbitrary
   where n = fromIntegral $ natVal (Proxy @n)
instance ∀ n m r . (KnownNat n, KnownNat m, r~ℝ)
           => Show (LinearMap r (R n) (R m)) where
  show _ = "..."
instance ∀ n m r . (KnownNat n, KnownNat m, r~ℝ)
           => Arbitrary (LinearMap r (R n) (R m)) where
  arbitrary = LinearMap . HMatS.fromList
                <$> vectorOf (n*m) arbitrary
   where n = fromIntegral $ natVal (Proxy @n)
         m = fromIntegral $ natVal (Proxy @m)
instance ∀ n m r . (KnownNat n, KnownNat m, r~ℝ)
           => InnerSpace (LinearMap r (R n) (R m)) where
  LinearMap f<.>LinearMap g
      = HMat.flatten (extract f) HMat.<.> HMat.flatten (extract g)

infix 4 ≈≈≈
(≈≈≈) :: (InnerSpace v, Show v, Eq v, RealFrac (Scalar v))
            => v -> v -> QC.Property
v≈≈≈w
 | magnitudeSq (v^-^w) < (magnitudeSq v + magnitudeSq w)*1e-8   = QC.property True
 | otherwise                                                    = v===w


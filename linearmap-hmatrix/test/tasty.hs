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
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies         #-}

import qualified Prelude as Hask
import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Numeric.LinearAlgebra.Static.Orphans
import Numeric.LinearAlgebra.Static as HMatS hiding ((===))

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
    ]
   ]


instance ∀ n . KnownNat n => Arbitrary (R n) where
  arbitrary = HMatS.fromList <$> vectorOf n arbitrary
   where n = fromIntegral $ natVal (Proxy @n)
instance ∀ n . KnownNat n => Eq (R n) where
  (==) = (==)`on`HMatS.extract

infix 4 ≈≈≈
(≈≈≈) :: (InnerSpace v, Show v, Eq v, RealFrac (Scalar v))
            => v -> v -> QC.Property
v≈≈≈w
 | magnitudeSq (v^-^w) < (magnitudeSq v + magnitudeSq w)*1e-8   = QC.property True
 | otherwise                                                    = v===w


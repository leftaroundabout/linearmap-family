-- |
-- Module      : Math.LinearMap.Category.Backend.HMatrix
-- Copyright   : (c) Justus Sagemüller 2024
-- License     : GPL v3
-- 
-- Maintainer  : (@) justussa $ kth.se
-- Stability   : experimental
-- Portability : portable
-- 


{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE UnicodeSyntax            #-}

module Math.LinearMap.Category.Backend.HMatrix where

import Math.LinearMap.Category
import Math.VectorSpace.DimensionAware

import Numeric.LinearAlgebra.Static.Orphans

-- base
import Data.Function (on)
import GHC.TypeLits (KnownNat, natVal)

-- vector-space
import Data.VectorSpace (AdditiveGroup(..), VectorSpace(..), InnerSpace(..))
import Data.Basis (HasBasis(..))

--
-- hmatrix
import Numeric.LinearAlgebra.Static as HMatS
import qualified Numeric.LinearAlgebra as HMat

-- finite-typelits
import Data.Finite (Finite)

-- | Values of type @'HMatrixImpl' v@ conceptually represent vectors of type
--   @v@, but use HMatrix-vectors as the actual implementations for linear operations.
newtype HMatrixImpl v = HMatrixImpl {getHMatrixImplementation :: R (Dimension v)}

instance ∀ v . StaticDimensional v => Eq (HMatrixImpl v) where
  (==) = dimensionIsStatic @v ((==)`on`(HMatS.extract . getHMatrixImplementation))

instance ∀ v . StaticDimensional v => AdditiveGroup (HMatrixImpl v) where
  zeroV = dimensionIsStatic @v (HMatrixImpl zeroV)
  (^+^) = dimensionIsStatic @v
            (\(HMatrixImpl v) (HMatrixImpl w) -> HMatrixImpl $ v^+^w)
  (^-^) = dimensionIsStatic @v
            (\(HMatrixImpl v) (HMatrixImpl w) -> HMatrixImpl $ v^-^w)
  negateV = dimensionIsStatic @v
            (\(HMatrixImpl v) -> HMatrixImpl $ negateV v)

instance ∀ v . (StaticDimensional v, Scalar v ~ ℝ) => VectorSpace (HMatrixImpl v) where
  type Scalar (HMatrixImpl v) = ℝ
  (*^) = dimensionIsStatic @v
          (\μ (HMatrixImpl v) -> HMatrixImpl $ μ*^v)

instance ∀ v . StaticDimensional v => AffineSpace (HMatrixImpl v) where
  type Diff (HMatrixImpl v) = HMatrixImpl v
  (.-.) = dimensionIsStatic @v
            (\(HMatrixImpl v) (HMatrixImpl w) -> HMatrixImpl $ v^-^w)
  (.+^) = dimensionIsStatic @v
            (\(HMatrixImpl v) (HMatrixImpl w) -> HMatrixImpl $ v^+^w)

instance ∀ v . (StaticDimensional v, Scalar v ~ ℝ) => InnerSpace (HMatrixImpl v) where
  (<.>) = dimensionIsStatic @v
            (\(HMatrixImpl v) (HMatrixImpl w) -> dot v w)

instance ∀ v . (StaticDimensional v, Scalar v ~ ℝ) => HasBasis (HMatrixImpl v) where
  type Basis (HMatrixImpl v) = Finite (Dimension v)
  basisValue = dimensionIsStatic @v (HMatrixImpl . basisValue)
  decompose = dimensionIsStatic @v (decompose . getHMatrixImplementation)
  decompose' = dimensionIsStatic @v (decompose' . getHMatrixImplementation)

instance ∀ v . (StaticDimensional v, Scalar v ~ ℝ) => DimensionAware (HMatrixImpl v) where
  type StaticDimension (HMatrixImpl v) = 'Just (Dimension v)
  dimensionalityWitness = dimensionIsStatic @v IsStaticDimensional

instance ∀ v n . (KnownNat n, n`Dimensional`v, Scalar v ~ ℝ)
                      => n`Dimensional`HMatrixImpl v where
  unsafeFromArrayWithOffset i = HMatrixImpl . unsafeFromArrayWithOffset i
  unsafeWriteArrayWithOffset ar i
         = unsafeWriteArrayWithOffset ar i . getHMatrixImplementation


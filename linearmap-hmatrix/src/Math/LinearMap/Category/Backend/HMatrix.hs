-- |
-- Module      : Math.LinearMap.Category.Backend.HMatrix
-- Copyright   : (c) Justus Sagemüller 2024
-- License     : GPL v3
-- 
-- Maintainer  : (@) justussa $ kth.se
-- Stability   : experimental
-- Portability : portable
-- 


{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE UnicodeSyntax            #-}

module Math.LinearMap.Category.Backend.HMatrix where

import Math.LinearMap.Category
import Math.VectorSpace.DimensionAware

import Numeric.LinearAlgebra.Static.Orphans
--
-- hmatrix
import Numeric.LinearAlgebra.Static as HMatS
import qualified Numeric.LinearAlgebra as HMat


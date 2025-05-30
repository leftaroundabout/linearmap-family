-- |
-- Module      : Math.LinearMap.Category.TensorQuot
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 


{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE UnicodeSyntax         #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE ConstraintKinds       #-}

module Math.LinearMap.Category.TensorQuot
   ( TensorQuot(..)
   ) where

import Math.LinearMap.Category.Class
import Math.LinearMap.Category.Instances
import Math.LinearMap.Asserted
import Math.LinearMap.Category.TensorQuot.Definitions

import Data.VectorSpace
import Data.VectorSpace.Free


mkFreeTensorQuot ''V1
mkFreeTensorQuot ''V2
mkFreeTensorQuot ''V3
mkFreeTensorQuot ''V4

instance ∀ s x y v w .
    ( TensorSpace v, TensorSpace w, v ~ x, LinearSpace y
    , TensorQuot x v, TensorQuot y w, (x⨸v) ~ s, (y⨸w) ~ s
    , Scalar x ~ s, Scalar y ~ s, Scalar v ~ s, Scalar w ~ s )
      => TensorQuot (Tensor s x y) (Tensor s v w) where
  type Tensor s x y ⨸ Tensor s v w = s
  μ·t = (fmapTensor-+$>lfun(μ·))-+$>t
instance ( LinearSpace x, LinearSpace y
         , s ~ Double, Scalar x ~ s, Scalar y ~ s )
      => TensorQuot (Tensor s x y) Double where
  type (Tensor s x y) ⨸ Double = DualVector (Tensor s x y)
  f·t = (applyTensorFunctional-+$>f)-+$>t

-- |
-- Module      : Math.LinearMap.Category.TensorQuot.Definitions
-- Copyright   : (c) Justus Sagemüller 2025
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ kth.se
-- Stability   : experimental
-- Portability : portable
-- 


{-# LANGUAGE CPP                   #-}
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

module Math.LinearMap.Category.TensorQuot.Definitions where

import Math.LinearMap.Category.Class
import Math.LinearMap.Category.Instances
import Math.LinearMap.Asserted

import Data.VectorSpace
import Data.VectorSpace.Free

infixl 7 ·

class (TensorSpace v, VectorSpace w) => TensorQuot v w where
  type v ⨸ w :: *
  -- | Generalised multiplication operation. This subsumes '<.>^' and '*^'.
  --   For scalars therefore also '*', and for 'InnerSpace', '<.>'.
  (·) :: v ⨸ w -> v -> w

instance TensorQuot Double Double where
  type Double ⨸ Double = Double
  (·) = (*)

instance ( TensorQuot x v, TensorQuot y w
         , Scalar x ~ Scalar y, Scalar v ~ Scalar w
         , (x⨸v) ~ (y⨸w) )
      => TensorQuot (x,y) (v,w) where
  type (x,y) ⨸ (v,w) = x⨸v
  μ·(x,y) = (μ·x, μ·y)
instance ( TensorQuot x Double, TensorQuot y Double
         , Scalar x ~ Double, Scalar y ~ Double )
      => TensorQuot (x,y) Double where
  type (x,y) ⨸ Double = (x ⨸ Double, y ⨸ Double)
  (v,w)·(x,y) = v·x + w·y


-- |
-- Module      : Math.LinearMap.Coercion
-- Copyright   : (c) Justus Sagemüller 2022
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

module Math.LinearMap.Coercion
   ( VSCCoercion(..)
   , (-+$=>)
   -- * Conversion between the internal types
   , fromLinearMap, asLinearMap, fromTensor, asTensor
   , curryLinearMap, uncurryLinearMap
   ) where

import Math.LinearMap.Category.Class

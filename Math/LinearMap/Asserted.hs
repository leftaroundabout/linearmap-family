-- |
-- Module      : Math.LinearMap.Asserted
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Math.LinearMap.Asserted where

import Data.VectorSpace
import Data.Basis

import Prelude ()
import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained
import Data.Traversable.Constrained

import Data.Coerce
import Data.Type.Coercion

import Data.VectorSpace.Free
import qualified Linear.Matrix as Mat
import qualified Linear.Vector as Mat
import Math.VectorSpace.ZeroDimensional




-- | A linear map, represented simply as a Haskell function tagged with
--   the type of scalar with respect to which it is linear.
--   You can always use a matrix-implemented linear mapping as the function
--   (convert with 'Control.Arrow.Constrained.arr'), but many (sparse)
--   linear mappings can actually be calculated much more efficiently
--   if you don't represent them with any matrix / tensor product.
newtype LinearFunction s v w = LinearFunction { getLinearFunction :: v -> w }




linearFunction :: VectorSpace w => (v->w) -> LinearFunction (Scalar v) v w
linearFunction = LinearFunction

scaleWith :: (VectorSpace v, Scalar v ~ s) => s -> LinearFunction s v v
scaleWith μ = LinearFunction (μ*^)

scaleV :: (VectorSpace v, Scalar v ~ s) => v -> LinearFunction s s v
scaleV v = LinearFunction (*^v)

const0 :: AdditiveGroup w => LinearFunction s v w
const0 = LinearFunction (const zeroV)

lNegateV :: AdditiveGroup w => LinearFunction s w w
lNegateV = LinearFunction negateV

addV :: AdditiveGroup w => LinearFunction s (w,w) w
addV = LinearFunction $ uncurry (^+^)

instance AdditiveGroup w => AdditiveGroup (LinearFunction s v w) where
  zeroV = const0
  LinearFunction f ^+^ LinearFunction g = LinearFunction $ \x -> f x ^+^ g x
  LinearFunction f ^-^ LinearFunction g = LinearFunction $ \x -> f x ^-^ g x
  negateV (LinearFunction f) = LinearFunction $ negateV . f
instance VectorSpace w => VectorSpace (LinearFunction s v w) where
  type Scalar (LinearFunction s v w) = Scalar w
  μ *^ LinearFunction f = LinearFunction $ (μ*^) . f

instance Functor (LinearFunction s v) Coercion Coercion where
  fmap Coercion = Coercion

fmapScale :: ( VectorSpace w, Scalar w ~ s, VectorSpace s, Scalar s ~ s
             , Functor f (LinearFunction s) (LinearFunction s)
             , Object (LinearFunction s) s
             , Object (LinearFunction s) w
             , Object (LinearFunction s) (f s)
             , Object (LinearFunction s) (f w)
             , EnhancedCat (->) (LinearFunction s)
             , VectorSpace (f w), Scalar (f w) ~ s
             , VectorSpace (f s), Scalar (f s) ~ s )
               => f s -> LinearFunction s w (f w)
fmapScale v = LinearFunction $ \w -> fmap (scaleV w) $ v

lCoFst :: (AdditiveGroup w) => LinearFunction s v (v,w)
lCoFst = LinearFunction (,zeroV)
lCoSnd :: (AdditiveGroup v) => LinearFunction s w (v,w)
lCoSnd = LinearFunction (zeroV,)



-- | Infix synonym of 'LinearFunction', without explicit mention of the scalar type.
type v-+>w = LinearFunction (Scalar w) v w

-- | A bilinear function is a linear function mapping to a linear function,
--   or equivalently a 2-argument function that's linear in each argument
--   independently.
--   Note that this can /not/ be uncurried to a linear function with a tuple
--   argument (this would not be linear but quadratic).
type Bilinear v w y = LinearFunction (Scalar v) v (LinearFunction (Scalar v) w y)

bilinearFunction :: (v -> w -> y) -> Bilinear v w y
bilinearFunction f = LinearFunction $ LinearFunction . f

flipBilin :: Bilinear v w y -> Bilinear w v y
flipBilin (LinearFunction f) = LinearFunction
     $ \w -> LinearFunction $ f >>> \(LinearFunction g) -> g w

scale :: VectorSpace v => Bilinear (Scalar v) v v
scale = LinearFunction $ \μ -> LinearFunction (μ*^)

-- | @elacs ≡ 'flipBilin' 'scale'@.
elacs :: VectorSpace v => Bilinear v (Scalar v) v
elacs = LinearFunction $ \v -> LinearFunction (*^v)

inner :: InnerSpace v => Bilinear v v (Scalar v)
inner = LinearFunction $ \v -> LinearFunction (v<.>)

biConst0 :: AdditiveGroup v => Bilinear a b v
biConst0 = LinearFunction $ const const0

lApply :: Bilinear (v-+>w) v w
lApply = bilinearFunction $ \(LinearFunction f) v -> f v

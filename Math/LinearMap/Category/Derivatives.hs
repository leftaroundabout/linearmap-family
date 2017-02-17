-- |
-- Module      : Math.LinearMap.Category.Derivatives
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
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DefaultSignatures          #-}

module Math.LinearMap.Category.Derivatives
    {-# WARNING "These lenses will probably change their domain in the future." #-} where

import Data.VectorSpace
import Data.VectorSpace.Free

import Prelude ()
import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.Type.Coercion
import Data.Tagged

import Math.Manifold.Core.PseudoAffine
import Math.LinearMap.Asserted
import Math.LinearMap.Category.Instances
import Math.LinearMap.Category.Class

import Control.Lens

infixr 7 *∂, /∂, .∂
(/∂) :: ∀ s x y v q
          . ( Num' s, LinearSpace x, LinearSpace y, LinearSpace v, LinearSpace q
            , s ~ Scalar x, s ~ Scalar y, s ~ Scalar v, s ~ Scalar q )
       => Lens' y v -> Lens' x q -> Lens' (LinearMap s x y) (LinearMap s q v)
𝑣/∂𝑞 = lens (\m -> fmap (LinearFunction (^.𝑣))
                     $ m . arr (LinearFunction $ \q -> zeroV & 𝑞.~q))
            (\m u -> arr.LinearFunction
               $ \x -> (m $ x & 𝑞.~zeroV)
                   ^+^ (𝑣.~(u $ x^.𝑞) $ m $ zeroV & 𝑞.~(x^.𝑞)) )

(*∂) :: ∀ s a q v . ( Num' s, OneDimensional q, LinearSpace q, LinearSpace v
                   , s ~ Scalar a, s ~ Scalar q, s ~ Scalar v )
       => q -> Lens' a (LinearMap s q v) -> Lens' a v
q*∂𝑚 = lens (\a -> a^.𝑚 $ q)
           (\a v -> (a & 𝑚 .~ arr (LinearFunction $ \q' -> v ^* (q'^/!q))) )

(.∂) :: ∀ s x z . ( Fractional' s, LinearSpace x, s ~ Scalar x, LinearSpace z, s ~ Scalar z )
            => (∀ w . (LinearSpace w, Scalar w ~ s) => Lens' (TensorProduct x w) w)
                  -> Lens' x z -> Lens' (SymmetricTensor s x) z
𝑤.∂𝑦 = case closedScalarWitness :: ClosedScalarWitness s of
     ClosedScalarWitness -> lens
            (\(SymTensor t)
               -> (getTensorProduct $ fmap (LinearFunction (^.𝑦)) $ t)^.𝑤 ^* 0.5)
            (\(SymTensor (Tensor t)) z -> SymTensor . Tensor $ (𝑤.𝑦.~z^*2) t)
  

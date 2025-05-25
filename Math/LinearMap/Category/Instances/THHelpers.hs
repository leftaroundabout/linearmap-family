-- |
-- Module      : Math.LinearMap.Category.Instances.THHelpers
-- Copyright   : (c) Justus Sagemüller 2025
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE TypeApplications           #-}

module Math.LinearMap.Category.Instances.THHelpers
        ( mkLinearScalarSpace
        , autoLinearManifoldWitness
        ) where

import Math.VectorSpace.DimensionAware
import Math.LinearMap.Category.Class

import Data.VectorSpace
import Data.Basis

#if MIN_VERSION_manifolds_core(0,6,0)
import Math.Manifold.Core.Types (EmptyMfd)
#endif
import Math.Manifold.Core.PseudoAffine

import Prelude ()
import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.Coerce
import Data.Type.Coercion
import Data.Tagged
import Data.Proxy

import Data.Foldable (foldl')

import Data.VectorSpace.Free
import Data.VectorSpace.Free.FiniteSupportedSequence
import Data.VectorSpace.Free.Sequence as Seq
import qualified Linear.Matrix as Mat
import qualified Linear.Vector as Mat
import qualified Linear.Metric as Mat
import Control.Lens ((^.))
import Control.Monad.ST (ST)

import qualified Data.Vector as Arr
import qualified Data.Vector.Unboxed as UArr
import qualified Data.Vector.Generic as GArr

import Math.LinearMap.Asserted
import Math.VectorSpace.ZeroDimensional
import qualified Math.VectorSpace.DimensionAware.Theorems.MaybeNat as Maybe

import qualified Test.QuickCheck as QC

import GHC.TypeNats (natVal)
import qualified GHC.Exts as GHC
import qualified GHC.Generics as GHC

import Language.Haskell.TH

import Data.Singletons (SingI, sing, Sing)
#if MIN_VERSION_singletons(3,0,0)
import GHC.TypeLits.Singletons (withKnownNat)
#else
import Data.Singletons.TypeLits (withKnownNat)
#endif



autoLinearManifoldWitness :: (Semimanifold v, AffineSpace v, v ~ Needle v, v ~ Diff v
#if !MIN_VERSION_manifolds_core(0,6,0)
                             , v ~ Interior v
#endif
                             )
                                 => LinearManifoldWitness v
autoLinearManifoldWitness = LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
                             BoundarylessWitness
#endif

mkLinearScalarSpace :: Name -> Q [Dec]
mkLinearScalarSpace sName = do
  let s = pure (ConT sName)
  [d| instance Num' $s where
        closedScalarWitness = ClosedScalarWitness
      instance TensorSpace $s where
        type TensorProduct $s w = w
        scalarSpaceWitness = ScalarSpaceWitness
        linearManifoldWitness = autoLinearManifoldWitness
        zeroTensor = Tensor zeroV
        scaleTensor = bilinearFunction $ \μ (Tensor t) -> Tensor $ μ*^t
        addTensors (Tensor v) (Tensor w) = Tensor $ v ^+^ w
        subtractTensors (Tensor v) (Tensor w) = Tensor $ v ^-^ w
        negateTensor = LinearFunction $ \(Tensor v) -> Tensor (negateV v)
        toFlatTensor = LinearFunction $ follow Tensor
        fromFlatTensor = LinearFunction $ flout Tensor
        tensorProduct = bilinearFunction $ \μ
                 -> follow Tensor . getLinearFunction (scaleWith μ)
        transposeTensor = toFlatTensor . LinearFunction (flout Tensor)
        fmapTensor = bilinearFunction $ \f (Tensor t) -> Tensor (f-+$>t)
        fzipTensorWith = bilinearFunction
             $ \(LinearFunction f) -> follow Tensor <<< f <<< flout Tensor *** flout Tensor
        tensorUnsafeFromArrayWithOffset i ar
          = Tensor (unsafeFromArrayWithOffset i ar)
        tensorUnsafeWriteArrayWithOffset ar i (Tensor v)
          = unsafeWriteArrayWithOffset ar i v
        coerceFmapTensorProduct _ VSCCoercion = Coercion
        wellDefinedTensor (Tensor w) = Tensor <$> wellDefinedVector w
      instance LinearSpace $s where
        type DualVector $s = $s
        dualSpaceWitness = DualSpaceWitness
        linearId = LinearMap 1
        tensorId = uncurryLinearMap $ LinearMap $ fmap (LinearFunction $ follow Tensor) -+$> id
        idTensor = Tensor 1
        fromLinearForm = LinearFunction $ flout LinearMap
        coerceDoubleDual = VSCCoercion
        contractTensorMap = LinearFunction $ flout Tensor . flout LinearMap
        contractMapTensor = LinearFunction $ flout LinearMap . flout Tensor
        applyDualVector = scale
        applyLinear = LinearFunction $ \(LinearMap w) -> scaleV w
        applyTensorFunctional = bilinearFunction $ \(LinearMap du) (Tensor u) -> du<.>^u
        applyTensorLinMap = bilinearFunction $ \fℝuw (Tensor u)
                              -> let LinearMap fuw = curryLinearMap $ fℝuw
                                 in (applyLinear-+$>fuw) -+$> u
        composeLinear = bilinearFunction $ \f (LinearMap g)
                           -> LinearMap $ (applyLinear-+$>f)-+$>g
        useTupleLinearSpaceComponents _ = usingNonTupleTypeAsTupleError
    |]



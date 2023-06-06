{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Numeric.LinearAlgebra.Static.Orphans where

-- base
import GHC.TypeLits (KnownNat)

-- hmatrix
import Numeric.LinearAlgebra.Static

-- vector-space
import Data.AdditiveGroup
import Data.VectorSpace
import Data.AffineSpace

-- free-vector-spaces
import Data.VectorSpace.Free

-- linearmap-category
import Math.LinearMap.Category

-- tagged
import Data.Tagged (Tagged(..))

--------------------------------------------------
-- * @vector-space@ instances

instance KnownNat n => AdditiveGroup (R n) where
  zeroV = 0
  (^+^) = (+)
  negateV x = -x

instance KnownNat n => VectorSpace (R n) where
  type Scalar (R n) = Double
  k *^ v = dvmap (*k) v

instance KnownNat n => InnerSpace (R n) where
  (<.>) = dot

instance KnownNat n => AffineSpace (R n) where
  type Diff (R n) = R n
  (.-.) = (-)
  (.+^) = (+)


--------------------------------------------------
-- * @free-vector-spaces@ instances

instance KnownNat n => FreeVectorSpace (R n) where
  (^*^) = (*)
  vmap = dvmap


--------------------------------------------------
-- * @linearmap-category@ and @manifolds-core@

instance KnownNat n => Semimanifold (R n) where
  type Needle (R n) = R n
  type Interior (R n) = R n
  toInterior = pure
  fromInterior = id
  translateP = Tagged (^+^)

instance KnownNat n => PseudoAffine (R n) where
  v .-~. w = Just (v - w)

instance KnownNat n => TensorSpace (R n) where -- TODO: many errors
  type TensorProduct (R n) w = [w]
  scalarSpaceWitness = undefined
  linearManifoldWitness = undefined
  zeroTensor = undefined
  toFlatTensor = undefined
  fromFlatTensor = undefined
  tensorProduct = undefined
  transposeTensor = undefined
  fmapTensor = undefined
  fzipTensorWith = undefined
  coerceFmapTensorProduct = undefined
  wellDefinedTensor = undefined

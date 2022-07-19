-- |
-- Module      : Math.LinearMap.Category.Class
-- Copyright   : (c) Justus Sagemüller 2016
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
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE CPP                        #-}

module Math.LinearMap.Category.Class where

import Data.VectorSpace
import Data.AffineSpace

import Prelude ()
import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.Coerce
import Data.Type.Coercion
import Data.Tagged

import Math.Manifold.Core.PseudoAffine
import Math.LinearMap.Asserted
import Math.VectorSpace.ZeroDimensional
import Data.VectorSpace.Free

import qualified GHC.Generics as Gnrx
import GHC.Generics (Generic, (:*:)((:*:)))

data ClosedScalarWitness s where
  ClosedScalarWitness :: (Scalar s ~ s, DualVector s ~ s) => ClosedScalarWitness s
data TrivialTensorWitness s w where
  TrivialTensorWitness :: w ~ TensorProduct s w => TrivialTensorWitness s w

class (Num s, LinearSpace s, FreeVectorSpace s) => Num' s where
  closedScalarWitness :: ClosedScalarWitness s
  default closedScalarWitness :: (Scalar s ~ s, DualVector s ~ s) => ClosedScalarWitness s
  closedScalarWitness = ClosedScalarWitness
  trivialTensorWitness :: TrivialTensorWitness s w
  default trivialTensorWitness :: (w ~ TensorProduct s w) => TrivialTensorWitness s w
  trivialTensorWitness = TrivialTensorWitness

data ScalarSpaceWitness v where
  ScalarSpaceWitness :: (Num' (Scalar v), Scalar (Scalar v) ~ Scalar v)
                          => ScalarSpaceWitness v
data LinearManifoldWitness v where
  LinearManifoldWitness :: (Needle v ~ v, AffineSpace v, Diff v ~ v)
                         =>
#if !MIN_VERSION_manifolds_core(0,6,0)
                           BoundarylessWitness v ->
#endif
                           LinearManifoldWitness v
  
class (VectorSpace v, PseudoAffine v) => TensorSpace v where
  -- | The internal representation of a 'Tensor' product.
  -- 
  -- For Euclidean spaces, this is generally constructed by replacing each @s@
  -- scalar field in the @v@ vector with an entire @w@ vector. I.e., you have
  -- then a “nested vector” or, if @v@ is a @DualVector@ / “row vector”, a matrix.
  type TensorProduct v w :: *
  scalarSpaceWitness :: ScalarSpaceWitness v
  linearManifoldWitness :: LinearManifoldWitness v
  zeroTensor :: (TensorSpace w, Scalar w ~ Scalar v)
                => v ⊗ w
  toFlatTensor :: v -+> (v ⊗ Scalar v)
  fromFlatTensor :: (v ⊗ Scalar v) -+> v
  addTensors :: (TensorSpace w, Scalar w ~ Scalar v)
                => (v ⊗ w) -> (v ⊗ w) -> v ⊗ w
  default addTensors :: AdditiveGroup (TensorProduct v w) => (v ⊗ w) -> (v ⊗ w) -> v ⊗ w
  addTensors (Tensor vw₀) (Tensor vw₁) = Tensor $ vw₀ ^+^ vw₁
  subtractTensors :: (TensorSpace v, TensorSpace w, Scalar w ~ Scalar v)
                => (v ⊗ w) -> (v ⊗ w) -> v ⊗ w
  default subtractTensors :: AdditiveGroup (TensorProduct v w) => (v ⊗ w) -> (v ⊗ w) -> v ⊗ w
  subtractTensors (Tensor vw₀) (Tensor vw₁) = Tensor $ vw₀ ^-^ vw₁
  scaleTensor :: (TensorSpace w, Scalar w ~ Scalar v)
                => Bilinear (Scalar v) (v ⊗ w) (v ⊗ w)
  default scaleTensor
      :: (VectorSpace (TensorProduct v w), Scalar (TensorProduct v w) ~ Scalar v)
           => Bilinear (Scalar v) (v ⊗ w) (v ⊗ w)
  scaleTensor = bilinearFunction $ \μ (Tensor vw) -> Tensor $ μ*^vw
  negateTensor :: (TensorSpace w, Scalar w ~ Scalar v)
                => (v ⊗ w) -+> (v ⊗ w)
  default negateTensor :: AdditiveGroup (TensorProduct v w) => (v ⊗ w) -+> (v ⊗ w)
  negateTensor = LinearFunction $ \(Tensor vw) -> Tensor $ negateV vw
  tensorProduct :: (TensorSpace w, Scalar w ~ Scalar v)
                => Bilinear v w (v ⊗ w)
  tensorProducts :: (TensorSpace w, Scalar w ~ Scalar v)
                => [(v,w)] -> (v ⊗ w)
  tensorProducts vws = sumV [ getLinearFunction (
                              getLinearFunction tensorProduct v) w
                            | (v,w) <- vws ]
  transposeTensor :: (TensorSpace w, Scalar w ~ Scalar v)
                => (v ⊗ w) -+> (w ⊗ v)
  fmapTensor :: (TensorSpace w, TensorSpace x, Scalar w ~ Scalar v, Scalar x ~ Scalar v)
           => Bilinear (w -+> x) (v⊗w) (v⊗x)
  fzipTensorWith :: ( TensorSpace u, TensorSpace w, TensorSpace x
                    , Scalar u ~ Scalar v, Scalar w ~ Scalar v, Scalar x ~ Scalar v )
           => Bilinear ((w,x) -+> u) (v⊗w, v⊗x) (v⊗u)
  coerceFmapTensorProduct :: Hask.Functor p
       => p v -> Coercion a b -> Coercion (TensorProduct v a) (TensorProduct v b)
  -- | “Sanity-check” a vector. This typically amounts to detecting any NaN components,
  --   which should trigger a @Nothing@ result. Otherwise, the result should be @Just@
  --   the input, but may also be optimised / memoised if applicable (i.e. for
  --   function spaces).
  wellDefinedVector :: v -> Maybe v
  default wellDefinedVector :: Eq v => v -> Maybe v
  wellDefinedVector v = if v==v then Just v else Nothing
  wellDefinedTensor :: (TensorSpace w, Scalar w ~ Scalar v) => v⊗w -> Maybe (v⊗w)

infixl 7 ⊗

-- | Infix version of 'tensorProduct'.
(⊗) :: ∀ v w . (TensorSpace v, TensorSpace w, Scalar w ~ Scalar v, Num' (Scalar v))
                => v -> w -> v ⊗ w
v⊗w = (tensorProduct-+$>v)-+$>w

data DualSpaceWitness v where
  DualSpaceWitness :: ( LinearSpace (Scalar v), DualVector (Scalar v) ~ Scalar v
                      , LinearSpace (DualVector v), Scalar (DualVector v) ~ Scalar v
                      , DualVector (DualVector v) ~ v )
                             => DualSpaceWitness v
  
-- | The class of vector spaces @v@ for which @'LinearMap' s v w@ is well-implemented.
class (TensorSpace v, Num (Scalar v)) => LinearSpace v where
  -- | Suitable representation of a linear map from the space @v@ to its field.
  -- 
  --   For the usual euclidean spaces, you can just define @'DualVector' v = v@.
  --   (In this case, a dual vector will be just a “row vector” if you consider
  --   @v@-vectors as “column vectors”. 'LinearMap' will then effectively have
  --   a matrix layout.)
  type DualVector v :: *
  
  dualSpaceWitness :: DualSpaceWitness v
 
  linearId :: v +> v
  
  idTensor :: v ⊗ DualVector v
  idTensor = case dualSpaceWitness :: DualSpaceWitness v of
               DualSpaceWitness -> transposeTensor-+$>asTensor $ linearId
  
  sampleLinearFunction :: (TensorSpace w, Scalar v ~ Scalar w)
                             => (v-+>w) -+> (v+>w)
  sampleLinearFunction = case ( scalarSpaceWitness :: ScalarSpaceWitness v
                              , dualSpaceWitness :: DualSpaceWitness v ) of
        (ScalarSpaceWitness, DualSpaceWitness) -> LinearFunction
                               $ \f -> getLinearFunction (fmap f) id
  
  toLinearForm :: DualVector v -+> (v+>Scalar v)
  toLinearForm = case ( scalarSpaceWitness :: ScalarSpaceWitness v
                      , dualSpaceWitness :: DualSpaceWitness v ) of
    (ScalarSpaceWitness,DualSpaceWitness) -> toFlatTensor >>> arr fromTensor
  
  fromLinearForm :: (v+>Scalar v) -+> DualVector v
  fromLinearForm = case ( scalarSpaceWitness :: ScalarSpaceWitness v
                        , dualSpaceWitness :: DualSpaceWitness v ) of
    (ScalarSpaceWitness,DualSpaceWitness) -> arr asTensor >>> fromFlatTensor
  
  coerceDoubleDual :: Coercion v (DualVector (DualVector v))
  coerceDoubleDual = case dualSpaceWitness :: DualSpaceWitness v of
    DualSpaceWitness -> Coercion
  
  trace :: (v+>v) -+> Scalar v
  trace = case scalarSpaceWitness :: ScalarSpaceWitness v of
      ScalarSpaceWitness -> flipBilin contractLinearMapAgainst-+$>id
  
  contractTensorMap :: (TensorSpace w, Scalar w ~ Scalar v)
           => (v+>(v⊗w)) -+> w
  contractTensorMap = case scalarSpaceWitness :: ScalarSpaceWitness v of
           ScalarSpaceWitness -> arr deferLinearMap >>> transposeTensor
                                  >>> fmap trace >>> fromFlatTensor
  contractMapTensor :: (TensorSpace w, Scalar w ~ Scalar v)
           => (v⊗(v+>w)) -+> w
  contractMapTensor = case ( scalarSpaceWitness :: ScalarSpaceWitness v
                           , dualSpaceWitness :: DualSpaceWitness v ) of
        (ScalarSpaceWitness,DualSpaceWitness)
              -> arr (coUncurryLinearMap>>>asTensor)
                       >>> transposeTensor >>> fmap (arr asLinearMap >>> trace)
                                >>> fromFlatTensor
  contractTensorFn :: ∀ w . (TensorSpace w, Scalar w ~ Scalar v)
           => (v-+>(v⊗w)) -+> w
  contractTensorFn = LinearFunction $ getLinearFunction sampleLinearFunction
                                        >>> getLinearFunction contractTensorMap
  contractLinearMapAgainst :: (LinearSpace w, Scalar w ~ Scalar v)
           => Bilinear (v+>w) (w-+>v) (Scalar v)
  contractLinearMapAgainst = case ( scalarSpaceWitness :: ScalarSpaceWitness v
                                  , dualSpaceWitness :: DualSpaceWitness v ) of
      (ScalarSpaceWitness,DualSpaceWitness) -> arr asTensor >>> transposeTensor
                         >>> applyDualVector >>> LinearFunction (. sampleLinearFunction)
  
  applyDualVector :: LinearSpace v
                => Bilinear (DualVector v) v (Scalar v)
  
  applyLinear :: (TensorSpace w, Scalar w ~ Scalar v)
                => Bilinear (v+>w) v w
  composeLinear :: ( LinearSpace w, TensorSpace x
                   , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
           => Bilinear (w+>x) (v+>w) (v+>x)
  composeLinear = case scalarSpaceWitness :: ScalarSpaceWitness v of
            ScalarSpaceWitness -> LinearFunction $ \f -> fmap (applyLinear-+$>f)
  
  tensorId :: (LinearSpace w, Scalar w ~ Scalar v)
                 => (v⊗w)+>(v⊗w)
  
  applyTensorFunctional :: ( LinearSpace u, Scalar u ~ Scalar v )
               => Bilinear (DualVector (v⊗u)) (v⊗u) (Scalar v)
  
  applyTensorLinMap :: ( LinearSpace u, TensorSpace w
                       , Scalar u ~ Scalar v, Scalar w ~ Scalar v )
               => Bilinear ((v⊗u)+>w) (v⊗u) w 
  
  useTupleLinearSpaceComponents :: (v ~ (x,y))
         => ((LinearSpace x, LinearSpace y, Scalar x ~ Scalar y) => φ) -> φ
  

fmapLinearMap :: ∀ s v w x . ( LinearSpace v, TensorSpace w, TensorSpace x
                             , Scalar v ~ s, Scalar w ~ s, Scalar x ~ s )
                 => Bilinear (LinearFunction s w x) (v+>w) (v+>x)
fmapLinearMap = case dualSpaceWitness :: DualSpaceWitness v of
   DualSpaceWitness -> bilinearFunction
          $ \f -> arr asTensor >>> getLinearFunction (fmapTensor-+$>f) >>> arr fromTensor

instance Num' s => TensorSpace (ZeroDim s) where
  type TensorProduct (ZeroDim s) v = ZeroDim s
  scalarSpaceWitness = case closedScalarWitness :: ClosedScalarWitness s of
                ClosedScalarWitness -> ScalarSpaceWitness
  linearManifoldWitness = LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
                                BoundarylessWitness
#endif
  zeroTensor = Tensor Origin
  toFlatTensor = LinearFunction $ \Origin -> Tensor Origin
  fromFlatTensor = LinearFunction $ \(Tensor Origin) -> Origin
  negateTensor = LinearFunction id
  scaleTensor = biConst0
  addTensors (Tensor Origin) (Tensor Origin) = Tensor Origin
  subtractTensors (Tensor Origin) (Tensor Origin) = Tensor Origin
  tensorProduct = biConst0
  transposeTensor = const0
  fmapTensor = biConst0
  fzipTensorWith = biConst0
  coerceFmapTensorProduct _ Coercion = Coercion
  wellDefinedVector Origin = Just Origin
  wellDefinedTensor (Tensor Origin) = Just (Tensor Origin)
instance Num' s => LinearSpace (ZeroDim s) where
  type DualVector (ZeroDim s) = ZeroDim s
  dualSpaceWitness = case closedScalarWitness :: ClosedScalarWitness s of
                ClosedScalarWitness -> DualSpaceWitness
  linearId = LinearMap Origin
  idTensor = Tensor Origin
  tensorId = LinearMap Origin
  toLinearForm = LinearFunction . const $ LinearMap Origin
  fromLinearForm = const0
  coerceDoubleDual = Coercion
  contractTensorMap = const0
  contractMapTensor = const0
  contractLinearMapAgainst = biConst0
  applyDualVector = biConst0
  applyLinear = biConst0
  applyTensorFunctional = biConst0
  applyTensorLinMap = biConst0
  composeLinear = biConst0
  useTupleLinearSpaceComponents _ = usingNonTupleTypeAsTupleError


-- | The tensor product between one space's dual space and another space is the
-- space spanned by vector–dual-vector pairs, in
-- <https://en.wikipedia.org/wiki/Bra%E2%80%93ket_notationa bra-ket notation>
-- written as
-- 
-- @
-- m = ∑ |w⟩⟨v|
-- @
-- 
-- Any linear mapping can be written as such a (possibly infinite) sum. The
-- 'TensorProduct' data structure only stores the linear independent parts
-- though; for simple finite-dimensional spaces this means e.g. @'LinearMap' ℝ ℝ³ ℝ³@
-- effectively boils down to an ordinary matrix type, namely an array of
-- column-vectors @|w⟩@.
-- 
-- (The @⟨v|@ dual-vectors are then simply assumed to come from the canonical basis.)
-- 
-- For bigger spaces, the tensor product may be implemented in a more efficient
-- sparse structure; this can be defined in the 'TensorSpace' instance.
newtype LinearMap s v w = LinearMap {getLinearMap :: TensorProduct (DualVector v) w}

-- | Tensor products are most interesting because they can be used to implement
--   linear mappings, but they also form a useful vector space on their own right.
newtype Tensor s v w = Tensor {getTensorProduct :: TensorProduct v w}

asTensor :: Coercion (LinearMap s v w) (Tensor s (DualVector v) w)
asTensor = Coercion
fromTensor :: Coercion (Tensor s (DualVector v) w) (LinearMap s v w)
fromTensor = Coercion

asLinearMap :: ∀ s v w . (LinearSpace v, Scalar v ~ s)
           => Coercion (Tensor s v w) (LinearMap s (DualVector v) w)
asLinearMap = case dualSpaceWitness :: DualSpaceWitness v of
                DualSpaceWitness -> Coercion
fromLinearMap :: ∀ s v w . (LinearSpace v, Scalar v ~ s)
           => Coercion (LinearMap s (DualVector v) w) (Tensor s v w)
fromLinearMap = case dualSpaceWitness :: DualSpaceWitness v of
                DualSpaceWitness -> Coercion


pseudoFmapTensorLHS :: (TensorProduct v w ~ TensorProduct v' w)
           => c v v' -> Coercion (Tensor s v w) (Tensor s v' w)
pseudoFmapTensorLHS _ = Coercion

pseudoPrecomposeLinmap :: (TensorProduct (DualVector v) w ~ TensorProduct (DualVector v') w)
           => c v' v -> Coercion (LinearMap s v w) (LinearMap s v' w)
pseudoPrecomposeLinmap _ = Coercion

envTensorLHSCoercion :: ( TensorProduct v w ~ TensorProduct v' w
                        , TensorProduct v w' ~ TensorProduct v' w' )
           => c v v' -> LinearFunction s' (Tensor s v w) (Tensor s v w')
                     -> LinearFunction s' (Tensor s v' w) (Tensor s v' w')
envTensorLHSCoercion i (LinearFunction f) = LinearFunction $ coerce f

envLinmapPrecomposeCoercion
       :: ( TensorProduct (DualVector v) w ~ TensorProduct (DualVector v') w
          , TensorProduct (DualVector v) w' ~ TensorProduct (DualVector v') w' )
           => c v' v -> LinearFunction s' (LinearMap s v w) (LinearMap s v w')
                     -> LinearFunction s' (LinearMap s v' w) (LinearMap s v' w')
envLinmapPrecomposeCoercion i (LinearFunction f) = LinearFunction $ coerce f

-- | Infix synonym for 'LinearMap', without explicit mention of the scalar type.
type v +> w = LinearMap (Scalar v) v w

-- | Infix synonym for 'Tensor', without explicit mention of the scalar type.
type v ⊗ w = Tensor (Scalar v) v w

-- | The workhorse of this package: most functions here work on vector
--   spaces that fulfill the @'LSpace' v@ constraint.
-- 
--   In summary, this is a 'VectorSpace' with an implementation for @'TensorProduct' v w@,
--   for any other space @w@, and with a 'DualVector' space. This fulfills
--   @'DualVector' ('DualVector' v) ~ v@ (this constraint is encapsulated in
--   'DualSpaceWitness').
-- 
--   To make a new space of yours an 'LSpace', you must define instances of
--   'TensorSpace' and 'LinearSpace'. In fact, 'LSpace' is equivalent to
--   'LinearSpace', but makes the condition explicit that the scalar and dual vectors
--   also form a linear space. 'LinearSpace' only stores that constraint in
--   'dualSpaceWitness' (to avoid UndecidableSuperclasses).
type LSpace v = ( LinearSpace v, Num' (Scalar v) )

instance (LinearSpace v, TensorSpace w, Scalar v~s, Scalar w~s)
               => AdditiveGroup (LinearMap s v w) where
  zeroV = case dualSpaceWitness :: DualSpaceWitness v of
            DualSpaceWitness -> fromTensor $ zeroTensor
  m^+^n = case dualSpaceWitness :: DualSpaceWitness v of
            DualSpaceWitness -> fromTensor $ (asTensor$m) ^+^ (asTensor$n)
  m^-^n = case dualSpaceWitness :: DualSpaceWitness v of
            DualSpaceWitness -> fromTensor $ (asTensor$m) ^-^ (asTensor$n)
  negateV = case dualSpaceWitness :: DualSpaceWitness v of
            DualSpaceWitness -> (fromTensor$) . negateV . (asTensor$)
instance ∀ v w s . (LinearSpace v, TensorSpace w, Scalar v~s, Scalar w~s)
               => VectorSpace (LinearMap s v w) where
  type Scalar (LinearMap s v w) = s
  μ*^v = case ( dualSpaceWitness :: DualSpaceWitness v
              , scalarSpaceWitness :: ScalarSpaceWitness w ) of
            (DualSpaceWitness, ScalarSpaceWitness)
                -> fromTensor $ (scaleTensor-+$>μ) -+$> asTensor $ v
instance ∀ v w s . (LinearSpace v, TensorSpace w, Scalar v~s, Scalar w~s)
               => Semimanifold (LinearMap s v w) where
  type Needle (LinearMap s v w) = LinearMap s v w
#if !MIN_VERSION_manifolds_core(0,6,0)
  toInterior = pure
  fromInterior = id
  translateP = Tagged (^+^)
#endif
  (.+~^) = (^+^)
instance ∀ v w s . (LinearSpace v, TensorSpace w, Scalar v~s, Scalar w~s)
               => PseudoAffine (LinearMap s v w) where
  f.-~.g = return $ f^-^g
  (.-~!) = (^-^)

instance (TensorSpace v, TensorSpace w, Scalar v~s, Scalar w~s)
               => AdditiveGroup (Tensor s v w) where
  zeroV = zeroTensor
  (^+^) = addTensors
  (^-^) = subtractTensors
  negateV = getLinearFunction negateTensor
instance (TensorSpace v, TensorSpace w, Scalar v~s, Scalar w~s)
               => VectorSpace (Tensor s v w) where
  type Scalar (Tensor s v w) = s
  μ*^t = (scaleTensor-+$>μ)-+$>t
instance (TensorSpace v, TensorSpace w, Scalar v~s, Scalar w~s)
               => Semimanifold (Tensor s v w) where
  type Needle (Tensor s v w) = Tensor s v w
#if !MIN_VERSION_manifolds_core(0,6,0)
  toInterior = pure
  fromInterior = id
  translateP = Tagged (^+^)
#endif
  (.+~^) = (^+^)
instance (TensorSpace v, TensorSpace w, Scalar v~s, Scalar w~s)
               => PseudoAffine (Tensor s v w) where
  f.-~.g = return $ f^-^g
  (.-~!) = (^-^)
  
infixr 6 ⊕, >+<, <⊕

(<⊕) :: (u⊗w) -> (v⊗w) -> (u,v)⊗w
m <⊕ n = Tensor $ (m, n)

-- | The dual operation to the tuple constructor, or rather to the
--   '&&&' fanout operation: evaluate two (linear) functions in parallel
--   and sum up the results.
--   The typical use is to concatenate “row vectors” in a matrix definition.
(⊕) :: (u+>w) -> (v+>w) -> (u,v)+>w
LinearMap m ⊕ LinearMap n = LinearMap $ (Tensor m, Tensor n)

-- | ASCII version of '⊕'
(>+<) :: (u+>w) -> (v+>w) -> (u,v)+>w
(>+<) = (⊕)


instance Category (LinearMap s) where
  type Object (LinearMap s) v = (LinearSpace v, Scalar v ~ s)
  id = linearId
  (.) = lmc dualSpaceWitness
   where lmc :: ∀ v w x . ( LinearSpace v, Scalar v ~ s
                          , LinearSpace w, Scalar w ~ s
                          , TensorSpace x, Scalar x ~ s )
              => DualSpaceWitness v
                   -> LinearMap s w x -> LinearMap s v w -> LinearMap s v x
         lmc DualSpaceWitness = getLinearFunction . getLinearFunction composeLinear
instance Num' s => Cartesian (LinearMap s) where
  type UnitObject (LinearMap s) = ZeroDim s
  swap = (fmap (const0&&&id) $ id) ⊕ (fmap (id&&&const0) $ id)
  attachUnit = fmap (id&&&const0) $ id
  detachUnit = fst
  regroup = sampleLinearFunction $ LinearFunction regroup
  regroup' = sampleLinearFunction $ LinearFunction regroup'
instance Num' s => Morphism (LinearMap s) where
  f *** g = (fmap (id&&&const0) $ f) ⊕ (fmap (const0&&&id) $ g)
instance ∀ s . Num' s => PreArrow (LinearMap s) where
  (&&&) = lmFanout
   where lmFanout :: ∀ u v w . ( LinearSpace u, LinearSpace v, LinearSpace w
                               , Scalar u~s, Scalar v~s, Scalar w~s )
           => LinearMap s u v -> LinearMap s u w -> LinearMap s u (v,w)
         lmFanout f g = case ( dualSpaceWitness :: DualSpaceWitness u
                             , dualSpaceWitness :: DualSpaceWitness v
                             , dualSpaceWitness :: DualSpaceWitness w ) of
             (DualSpaceWitness, DualSpaceWitness, DualSpaceWitness)
                 -> fromTensor $ (fzipTensorWith$id) $ (asTensor $ f, asTensor $ g)
  terminal = zeroV
  fst = sampleLinearFunction $ fst
  snd = sampleLinearFunction $ snd
instance Num' s => EnhancedCat (->) (LinearMap s) where
  arr m = arr $ applyLinear $ m
instance Num' s => EnhancedCat (LinearFunction s) (LinearMap s) where
  arr m = applyLinear $ m
instance Num' s => EnhancedCat (LinearMap s) (LinearFunction s) where
  arr m = sampleLinearFunction $ m





  
instance ∀ u v . ( TensorSpace u, TensorSpace v, Scalar u ~ Scalar v )
                       => TensorSpace (u,v) where
  type TensorProduct (u,v) w = (u⊗w, v⊗w)
  scalarSpaceWitness = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                            , scalarSpaceWitness :: ScalarSpaceWitness v ) of
       (ScalarSpaceWitness, ScalarSpaceWitness) -> ScalarSpaceWitness
  linearManifoldWitness = case ( linearManifoldWitness :: LinearManifoldWitness u
                            , linearManifoldWitness :: LinearManifoldWitness v ) of
       ( LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
          BoundarylessWitness
#endif
        ,LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
          BoundarylessWitness
#endif
        )
         -> LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
             BoundarylessWitness
#endif
  zeroTensor = zeroTensor <⊕ zeroTensor
  scaleTensor = bilinearFunction $ \μ (Tensor (v,w)) ->
                 Tensor ( (scaleTensor-+$>μ)-+$>v, (scaleTensor-+$>μ)-+$>w )
  negateTensor = LinearFunction $ \(Tensor (v,w))
          -> Tensor (negateTensor-+$>v, negateTensor-+$>w)
  addTensors (Tensor (fu, fv)) (Tensor (fu', fv')) = (fu ^+^ fu') <⊕ (fv ^+^ fv')
  subtractTensors (Tensor (fu, fv)) (Tensor (fu', fv'))
          = (fu ^-^ fu') <⊕ (fv ^-^ fv')
  toFlatTensor = case scalarSpaceWitness :: ScalarSpaceWitness u of
     ScalarSpaceWitness -> follow Tensor <<< toFlatTensor *** toFlatTensor
  fromFlatTensor = case scalarSpaceWitness :: ScalarSpaceWitness u of
     ScalarSpaceWitness -> flout Tensor >>> fromFlatTensor *** fromFlatTensor
  tensorProduct = bilinearFunction $ \(u,v) w ->
                    Tensor ((tensorProduct-+$>u)-+$>w, (tensorProduct-+$>v)-+$>w)
  transposeTensor = LinearFunction $ \(Tensor (uw,vw))
              -> (fzipTensorWith-+$>id)-+$>(transposeTensor-+$>uw,transposeTensor-+$>vw)
  fmapTensor = bilinearFunction $
     \f (Tensor (uw,vw)) -> Tensor ((fmapTensor-+$>f)-+$>uw, (fmapTensor-+$>f)-+$>vw)
  fzipTensorWith = bilinearFunction
               $ \f (Tensor (uw, vw), Tensor (ux, vx))
                      -> Tensor ( (fzipTensorWith-+$>f)-+$>(uw,ux)
                                , (fzipTensorWith-+$>f)-+$>(vw,vx) )
  coerceFmapTensorProduct p cab = case
             ( coerceFmapTensorProduct (fst<$>p) cab
             , coerceFmapTensorProduct (snd<$>p) cab ) of
          (Coercion, Coercion) -> Coercion
  wellDefinedVector (u,v) = liftA2 (,) (wellDefinedVector u) (wellDefinedVector v)
  wellDefinedTensor (Tensor (u,v))
         = liftA2 ((Tensor.) . (,)) (wellDefinedTensor u) (wellDefinedTensor v)
instance ∀ u v . ( LinearSpace u, LinearSpace v, Scalar u ~ Scalar v )
                       => LinearSpace (u,v) where
  type DualVector (u,v) = (DualVector u, DualVector v)
  
  dualSpaceWitness = case ( dualSpaceWitness :: DualSpaceWitness u
                          , dualSpaceWitness :: DualSpaceWitness v ) of
       (DualSpaceWitness, DualSpaceWitness) -> DualSpaceWitness
  linearId = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                  , dualSpaceWitness :: DualSpaceWitness u
                  , dualSpaceWitness :: DualSpaceWitness v ) of
       (ScalarSpaceWitness, DualSpaceWitness, DualSpaceWitness)
             -> (fmap (id&&&const0)-+$>id) ⊕ (fmap (const0&&&id)-+$>id)
  tensorId = tI scalarSpaceWitness dualSpaceWitness dualSpaceWitness dualSpaceWitness
   where tI :: ∀ w . (LinearSpace w, Scalar w ~ Scalar v)
                 => ScalarSpaceWitness u -> DualSpaceWitness u
                     -> DualSpaceWitness v -> DualSpaceWitness w
                       -> ((u,v)⊗w)+>((u,v)⊗w)
         tI ScalarSpaceWitness DualSpaceWitness DualSpaceWitness DualSpaceWitness 
              = LinearMap
            ( rassocTensor . fromLinearMap . argFromTensor
                 $ fmap (LinearFunction $ \t -> Tensor (t,zeroV)) -+$> tensorId
            , rassocTensor . fromLinearMap . argFromTensor
                 $ fmap (LinearFunction $ \t -> Tensor (zeroV,t)) -+$> tensorId )
  sampleLinearFunction = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                              , dualSpaceWitness :: DualSpaceWitness u
                              , dualSpaceWitness :: DualSpaceWitness v ) of
       (ScalarSpaceWitness, DualSpaceWitness, DualSpaceWitness)
              -> LinearFunction $ \f -> (sampleLinearFunction -+$> f . lCoFst)
                                              ⊕ (sampleLinearFunction -+$> f . lCoSnd)
  applyDualVector = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                         , dualSpaceWitness :: DualSpaceWitness u
                         , dualSpaceWitness :: DualSpaceWitness v ) of
       (ScalarSpaceWitness, DualSpaceWitness, DualSpaceWitness)
              -> LinearFunction $ \(du,dv)
                      -> (applyDualVector$du) *** (applyDualVector$dv) >>> addV
  applyLinear = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                     , dualSpaceWitness :: DualSpaceWitness u
                     , dualSpaceWitness :: DualSpaceWitness v ) of
       (ScalarSpaceWitness, DualSpaceWitness, DualSpaceWitness)
              -> LinearFunction $ \(LinearMap (fu, fv)) ->
           (applyLinear -+$> (asLinearMap $ fu)) *** (applyLinear -+$> (asLinearMap $ fv))
             >>> addV
  composeLinear = case ( dualSpaceWitness :: DualSpaceWitness u
                       , dualSpaceWitness :: DualSpaceWitness v ) of
       (DualSpaceWitness, DualSpaceWitness)
              -> bilinearFunction $ \f (LinearMap (fu, fv))
                    -> ((composeLinear-+$>f)-+$>asLinearMap $ fu)
                       ⊕ ((composeLinear-+$>f)-+$>asLinearMap $ fv)
  applyTensorFunctional = case ( dualSpaceWitness :: DualSpaceWitness u
                               , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualSpaceWitness, DualSpaceWitness) -> bilinearFunction $
                  \(LinearMap (fu,fv)) (Tensor (tu,tv))
                           -> ((applyTensorFunctional-+$>asLinearMap$fu)-+$>tu)
                            + ((applyTensorFunctional-+$>asLinearMap$fv)-+$>tv)
  applyTensorLinMap = case ( dualSpaceWitness :: DualSpaceWitness u
                           , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualSpaceWitness, DualSpaceWitness) -> bilinearFunction`id`
             \f (Tensor (tu,tv)) -> let LinearMap (fu,fv) = curryLinearMap $ f
                   in ( (applyTensorLinMap-+$>uncurryLinearMap.asLinearMap $ fu)-+$>tu )
                   ^+^ ( (applyTensorLinMap-+$>uncurryLinearMap.asLinearMap $ fv)-+$>tv )
  useTupleLinearSpaceComponents r = r

lfstBlock :: ( LSpace u, LSpace v, LSpace w
             , Scalar u ~ Scalar v, Scalar v ~ Scalar w )
          => (u+>w) -+> ((u,v)+>w)
lfstBlock = LinearFunction (⊕zeroV)
lsndBlock :: ( LSpace u, LSpace v, LSpace w
            , Scalar u ~ Scalar v, Scalar v ~ Scalar w )
          => (v+>w) -+> ((u,v)+>w)
lsndBlock = LinearFunction (zeroV⊕)


-- | @((v'⊗w)+>x) -> ((v+>w)+>x)
argFromTensor :: ∀ s v w x . (LinearSpace v, LinearSpace w, Scalar v ~ s, Scalar w ~ s)
                 => Coercion (LinearMap s (Tensor s (DualVector v) w) x)
                             (LinearMap s (LinearMap s v w) x)
argFromTensor = case dualSpaceWitness :: DualSpaceWitness v of
     DualSpaceWitness -> curryLinearMap >>> fromLinearMap >>> coUncurryLinearMap

-- | @((v+>w)+>x) -> ((v'⊗w)+>x)@
argAsTensor :: ∀ s v w x . (LinearSpace v, LinearSpace w, Scalar v ~ s, Scalar w ~ s)
                 => Coercion (LinearMap s (LinearMap s v w) x)
                             (LinearMap s (Tensor s (DualVector v) w) x)
argAsTensor = case dualSpaceWitness :: DualSpaceWitness v of
     DualSpaceWitness -> uncurryLinearMap <<< asLinearMap <<< coCurryLinearMap

-- | @(u+>(v⊗w)) -> (u+>v)⊗w@
deferLinearMap :: Coercion (LinearMap s u (Tensor s v w)) (Tensor s (LinearMap s u v) w)
deferLinearMap = Coercion

-- | @(u+>v)⊗w -> u+>(v⊗w)@
hasteLinearMap :: Coercion (Tensor s (LinearMap s u v) w) (LinearMap s u (Tensor s v w))
hasteLinearMap = Coercion


lassocTensor :: Coercion (Tensor s u (Tensor s v w)) (Tensor s (Tensor s u v) w)
lassocTensor = Coercion
rassocTensor :: Coercion (Tensor s (Tensor s u v) w) (Tensor s u (Tensor s v w))
rassocTensor = Coercion

instance ∀ s u v . ( LinearSpace u, TensorSpace v, Scalar u ~ s, Scalar v ~ s )
                       => TensorSpace (LinearMap s u v) where
  type TensorProduct (LinearMap s u v) w = TensorProduct (DualVector u) (Tensor s v w)
  scalarSpaceWitness = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                            , scalarSpaceWitness :: ScalarSpaceWitness v ) of
       (ScalarSpaceWitness, _ScalarSpaceWitness) -> ScalarSpaceWitness
  linearManifoldWitness = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                               , linearManifoldWitness :: LinearManifoldWitness u
                               , linearManifoldWitness :: LinearManifoldWitness v ) of
       ( ScalarSpaceWitness
        ,LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
           BoundarylessWitness
#endif
        ,LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
           BoundarylessWitness
#endif
        )
         -> LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
             BoundarylessWitness
#endif
  zeroTensor = deferLinearMap $ zeroV
  toFlatTensor = case scalarSpaceWitness :: ScalarSpaceWitness u of
       ScalarSpaceWitness -> arr deferLinearMap . fmap toFlatTensor
  fromFlatTensor = case scalarSpaceWitness :: ScalarSpaceWitness u of
       ScalarSpaceWitness -> fmap fromFlatTensor . arr hasteLinearMap
  addTensors t₁ t₂ = deferLinearMap $ (hasteLinearMap$t₁) ^+^ (hasteLinearMap$t₂)
  subtractTensors t₁ t₂ = deferLinearMap $ (hasteLinearMap$t₁) ^-^ (hasteLinearMap$t₂)
  scaleTensor = bilinearFunction $ \μ t
            -> deferLinearMap $ scaleWith μ -+$> hasteLinearMap $ t
  negateTensor = arr deferLinearMap . lNegateV . arr hasteLinearMap
  transposeTensor = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                         , dualSpaceWitness :: DualSpaceWitness u ) of
    (ScalarSpaceWitness,DualSpaceWitness)-> --(u +> v) ⊗ w
              arr hasteLinearMap     --  u +> (v ⊗ w)
          >>> fmap transposeTensor   --  u +> (w ⊗ v)
          >>> arr asTensor           --  u' ⊗ (w ⊗ v)
          >>> transposeTensor        --  (w ⊗ v) ⊗ u'
          >>> arr rassocTensor       --  w ⊗ (v ⊗ u')
          >>> fmap transposeTensor   --  w ⊗ (u' ⊗ v)
          >>> arr (fmap fromTensor)  --  w ⊗ (u +> v)
  tensorProduct = case scalarSpaceWitness :: ScalarSpaceWitness u of
     ScalarSpaceWitness -> bilinearFunction $ \f s
                   -> deferLinearMap $ fmap (flipBilin tensorProduct-+$>s)-+$>f
  fmapTensor = case scalarSpaceWitness :: ScalarSpaceWitness u of
     ScalarSpaceWitness -> LinearFunction $ \f
                -> arr deferLinearMap <<< fmap (fmap f) <<< arr hasteLinearMap
  fzipTensorWith = case scalarSpaceWitness :: ScalarSpaceWitness u of
     ScalarSpaceWitness -> LinearFunction $ \f
                -> arr deferLinearMap <<< fzipWith (fzipWith f)
                     <<< arr hasteLinearMap *** arr hasteLinearMap
  coerceFmapTensorProduct = cftlp dualSpaceWitness
   where cftlp :: ∀ a b p . DualSpaceWitness u -> p (LinearMap s u v) -> Coercion a b
                   -> Coercion (TensorProduct (DualVector u) (Tensor s v a))
                               (TensorProduct (DualVector u) (Tensor s v b))
         cftlp DualSpaceWitness _ c
                   = coerceFmapTensorProduct ([]::[DualVector u])
                                             (fmap c :: Coercion (v⊗a) (v⊗b))
  wellDefinedVector = case dualSpaceWitness :: DualSpaceWitness u of
      DualSpaceWitness -> arr asTensor >>> wellDefinedTensor >>> arr (fmap fromTensor)
  wellDefinedTensor
      = arr hasteLinearMap >>> wellDefinedVector >>> arr (fmap deferLinearMap)

-- | @((u+>v)+>w) -> u⊗(v+>w)@
coCurryLinearMap :: ∀ s u v w . ( LinearSpace u, Scalar u ~ s
                                , LinearSpace v, Scalar v ~ s ) =>
              Coercion (LinearMap s (LinearMap s u v) w) (Tensor s u (LinearMap s v w))
coCurryLinearMap = case ( dualSpaceWitness :: DualSpaceWitness u
                        , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualSpaceWitness, DualSpaceWitness)
             -> asTensor >>> rassocTensor >>> fmap asLinearMap

-- | @(u⊗(v+>w)) -> (u+>v)+>w@
coUncurryLinearMap :: ∀ s u v w . ( LinearSpace u, Scalar u ~ s
                                , LinearSpace v, Scalar v ~ s ) =>
              Coercion (Tensor s u (LinearMap s v w)) (LinearMap s (LinearMap s u v) w)
coUncurryLinearMap = case ( dualSpaceWitness :: DualSpaceWitness u
                          , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualSpaceWitness, DualSpaceWitness)
             -> fromTensor <<< lassocTensor <<< fmap fromLinearMap

-- | @((u⊗v)+>w) -> (u+>(v+>w))@
curryLinearMap :: ∀ u v w s . ( LinearSpace u, Scalar u ~ s )
           => Coercion (LinearMap s (Tensor s u v) w) (LinearMap s u (LinearMap s v w))
curryLinearMap = case dualSpaceWitness :: DualSpaceWitness u of
           DualSpaceWitness -> (Coercion :: Coercion ((u⊗v)+>w)
                                     ((DualVector u)⊗(Tensor s (DualVector v) w)) )
                                 >>> fmap fromTensor >>> fromTensor

-- | @(u+>(v+>w)) -> ((u⊗v)+>w)@
uncurryLinearMap :: ∀ u v w s . ( LinearSpace u, Scalar u ~ s )
           => Coercion (LinearMap s u (LinearMap s v w)) (LinearMap s (Tensor s u v) w)
uncurryLinearMap = case dualSpaceWitness :: DualSpaceWitness u of
           DualSpaceWitness -> (Coercion :: Coercion 
                                     ((DualVector u)⊗(Tensor s (DualVector v) w))
                                     ((u⊗v)+>w) )
                                 <<< fmap asTensor <<< asTensor

uncurryLinearFn :: ( Num' s, LSpace u, LSpace v, LSpace w
                   , Scalar u ~ s, Scalar v ~ s, Scalar w ~ s )
           => LinearFunction s u (LinearMap s v w) -+> LinearFunction s (Tensor s u v) w
uncurryLinearFn = bilinearFunction
         $ \f t -> contractMapTensor . fmap f . transposeTensor $ t

instance ∀ s u v . (LinearSpace u, LinearSpace v, Scalar u ~ s, Scalar v ~ s)
                       => LinearSpace (LinearMap s u v) where
  type DualVector (LinearMap s u v) = Tensor s u (DualVector v)
  dualSpaceWitness = case ( dualSpaceWitness :: DualSpaceWitness u
                          , dualSpaceWitness :: DualSpaceWitness v ) of
      (DualSpaceWitness, DualSpaceWitness) -> DualSpaceWitness
  linearId = case dualSpaceWitness :: DualSpaceWitness u of
     DualSpaceWitness -> fromTensor . lassocTensor . fromLinearMap . fmap asTensor
                            . curryLinearMap . fmap fromTensor $ tensorId
  tensorId = uncurryLinearMap . coUncurryLinearMap . fmap curryLinearMap
               . coCurryLinearMap . fmap deferLinearMap $ id
  coerceDoubleDual = case dualSpaceWitness :: DualSpaceWitness v of
     DualSpaceWitness -> Coercion
  applyLinear = case dualSpaceWitness :: DualSpaceWitness u of
    DualSpaceWitness -> bilinearFunction $ \f g
                  -> let tf = argAsTensor $ f
                     in (applyTensorLinMap-+$>tf)-+$>fromLinearMap $ g
  applyDualVector = case dualSpaceWitness :: DualSpaceWitness v of
    DualSpaceWitness -> flipBilin applyTensorFunctional
  applyTensorFunctional = atf scalarSpaceWitness dualSpaceWitness dualSpaceWitness
   where atf :: ∀ w . (LinearSpace w, Scalar w ~ s)
                   => ScalarSpaceWitness u -> DualSpaceWitness u -> DualSpaceWitness w
                       -> Bilinear ((u+>v)+>DualVector w) ((u+>v)⊗w) s
         atf ScalarSpaceWitness DualSpaceWitness DualSpaceWitness
              = arr (coCurryLinearMap >>> asLinearMap)
                           >>> applyTensorFunctional >>> bilinearFunction`id`\f t
                     -> f . arr (asTensor . hasteLinearMap) -+$> t
  applyTensorLinMap = case dualSpaceWitness :: DualSpaceWitness u of
    DualSpaceWitness -> LinearFunction $
                 arr (curryLinearMap>>>coCurryLinearMap
                             >>>fmap uncurryLinearMap>>>coUncurryLinearMap>>>argAsTensor)
                  >>> \f -> LinearFunction $ \g
                               -> (applyTensorLinMap-+$>f)
                                   . arr (asTensor . hasteLinearMap) -+$> g
  useTupleLinearSpaceComponents _ = usingNonTupleTypeAsTupleError

instance ∀ s u v . (TensorSpace u, TensorSpace v, Scalar u ~ s, Scalar v ~ s)
                       => TensorSpace (Tensor s u v) where
  type TensorProduct (Tensor s u v) w = TensorProduct u (Tensor s v w)
  scalarSpaceWitness = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                            , scalarSpaceWitness :: ScalarSpaceWitness v ) of
       (ScalarSpaceWitness, ScalarSpaceWitness) -> ScalarSpaceWitness
  linearManifoldWitness = case ( linearManifoldWitness :: LinearManifoldWitness u
                             , linearManifoldWitness :: LinearManifoldWitness v ) of
       ( LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
            BoundarylessWitness
#endif
        ,LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
            BoundarylessWitness
#endif
        )
         -> LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
             BoundarylessWitness
#endif
  zeroTensor = lassocTensor $ zeroTensor
  toFlatTensor = case scalarSpaceWitness :: ScalarSpaceWitness u of
    ScalarSpaceWitness -> arr lassocTensor . fmap toFlatTensor
  fromFlatTensor = case scalarSpaceWitness :: ScalarSpaceWitness u of
    ScalarSpaceWitness -> fmap fromFlatTensor . arr rassocTensor
  addTensors t₁ t₂ = lassocTensor $ (rassocTensor$t₁) ^+^ (rassocTensor$t₂)
  subtractTensors t₁ t₂ = lassocTensor $ (rassocTensor$t₁) ^-^ (rassocTensor$t₂)
  scaleTensor = case scalarSpaceWitness :: ScalarSpaceWitness u of
    ScalarSpaceWitness ->
        LinearFunction $ \μ -> arr lassocTensor . scaleWith μ . arr rassocTensor
  negateTensor = arr lassocTensor . lNegateV . arr rassocTensor
  tensorProduct = case scalarSpaceWitness :: ScalarSpaceWitness u of
    ScalarSpaceWitness -> flipBilin $ LinearFunction $ \w
             -> arr lassocTensor . fmap (flipBilin tensorProduct-+$>w)
  transposeTensor = case scalarSpaceWitness :: ScalarSpaceWitness u of
    ScalarSpaceWitness -> fmap transposeTensor . arr rassocTensor
                       . transposeTensor . fmap transposeTensor . arr rassocTensor
  fmapTensor = case scalarSpaceWitness :: ScalarSpaceWitness u of
    ScalarSpaceWitness -> LinearFunction $ \f
                -> arr lassocTensor <<< fmap (fmap f) <<< arr rassocTensor
  fzipTensorWith = case scalarSpaceWitness :: ScalarSpaceWitness u of
    ScalarSpaceWitness -> LinearFunction $ \f
                -> arr lassocTensor <<< fzipWith (fzipWith f)
                     <<< arr rassocTensor *** arr rassocTensor
  coerceFmapTensorProduct = cftlp
   where cftlp :: ∀ a b p . p (Tensor s u v) -> Coercion a b
                   -> Coercion (TensorProduct u (Tensor s v a))
                               (TensorProduct u (Tensor s v b))
         cftlp _ c = coerceFmapTensorProduct ([]::[u])
                                             (fmap c :: Coercion (v⊗a) (v⊗b))
  wellDefinedVector = wellDefinedTensor
  wellDefinedTensor = arr rassocTensor >>> wellDefinedTensor >>> arr (fmap lassocTensor)
instance ∀ s u v . (LinearSpace u, LinearSpace v, Scalar u ~ s, Scalar v ~ s)
                       => LinearSpace (Tensor s u v) where
  type DualVector (Tensor s u v) = LinearMap s u (DualVector v)
  linearId = tensorId
  tensorId = fmap lassocTensor . uncurryLinearMap . uncurryLinearMap
               . fmap curryLinearMap . curryLinearMap $ tensorId
  coerceDoubleDual = case ( dualSpaceWitness :: DualSpaceWitness u
                          , dualSpaceWitness :: DualSpaceWitness v ) of
    (DualSpaceWitness, DualSpaceWitness) -> Coercion
  dualSpaceWitness = case ( dualSpaceWitness :: DualSpaceWitness u
                          , dualSpaceWitness :: DualSpaceWitness v ) of
    (DualSpaceWitness, DualSpaceWitness) -> DualSpaceWitness
  applyLinear = applyTensorLinMap
  applyDualVector = applyTensorFunctional
  applyTensorFunctional = atf scalarSpaceWitness dualSpaceWitness
   where atf :: ∀ w . (LinearSpace w, Scalar w ~ s)
               => ScalarSpaceWitness u -> DualSpaceWitness w
                  -> Bilinear (LinearMap s (Tensor s u v) (DualVector w))
                              (Tensor s (Tensor s u v) w)
                              s
         atf ScalarSpaceWitness DualSpaceWitness
             = arr curryLinearMap >>> applyTensorFunctional
                           >>> LinearFunction`id`\f -> f . arr rassocTensor
  applyTensorLinMap = LinearFunction $ arr (curryLinearMap>>>curryLinearMap
                            >>>fmap uncurryLinearMap>>>uncurryLinearMap)
                        >>> \f -> (applyTensorLinMap-+$>f) . arr rassocTensor
  composeLinear = case scalarSpaceWitness :: ScalarSpaceWitness u of
    ScalarSpaceWitness -> bilinearFunction $ \f g
        -> uncurryLinearMap $ fmap (fmap $ applyLinear-+$>f) $ (curryLinearMap$g)
  contractTensorMap = case scalarSpaceWitness :: ScalarSpaceWitness u of
    ScalarSpaceWitness -> contractTensorMap
      . fmap (transposeTensor . contractTensorMap
                 . fmap (arr rassocTensor . transposeTensor . arr rassocTensor))
                       . arr curryLinearMap
  contractMapTensor = case scalarSpaceWitness :: ScalarSpaceWitness u of
    ScalarSpaceWitness -> contractTensorMap . fmap transposeTensor . contractMapTensor
                 . fmap (arr (curryLinearMap . hasteLinearMap) . transposeTensor)
                       . arr rassocTensor
  useTupleLinearSpaceComponents _ = usingNonTupleTypeAsTupleError



type DualSpace v = v+>Scalar v

type Fractional' s = (Num' s, Fractional s, Eq s, VectorSpace s)



instance (TensorSpace v, Num' s, Scalar v ~ s)
            => Functor (Tensor s v) (LinearFunction s) (LinearFunction s) where
  fmap f = getLinearFunction fmapTensor f
instance (Num' s, TensorSpace v, Scalar v ~ s)
            => Monoidal (Tensor s v) (LinearFunction s) (LinearFunction s) where
  pureUnit = const0
  fzipWith f = getLinearFunction fzipTensorWith f

instance (LinearSpace v, Num' s, Scalar v ~ s)
            => Functor (LinearMap s v) (LinearFunction s) (LinearFunction s) where
  fmap = case dualSpaceWitness :: DualSpaceWitness v of
    DualSpaceWitness -> \f -> arr fromTensor . fmap f . arr asTensor
instance (Num' s, LinearSpace v, Scalar v ~ s)
            => Monoidal (LinearMap s v) (LinearFunction s) (LinearFunction s) where
  pureUnit = const0
  fzipWith = case dualSpaceWitness :: DualSpaceWitness v of
    DualSpaceWitness -> \f -> arr asTensor *** arr asTensor >>> fzipWith f >>> arr fromTensor

instance (TensorSpace v, Scalar v ~ s)
            => Functor (Tensor s v) Coercion Coercion where
  fmap = crcFmap
   where crcFmap :: ∀ s v a b . (TensorSpace v, Scalar v ~ s)
              => Coercion a b -> Coercion (Tensor s v a) (Tensor s v b)
         crcFmap f = case coerceFmapTensorProduct ([]::[v]) f of
                       Coercion -> Coercion

instance (LinearSpace v, Scalar v ~ s)
            => Functor (LinearMap s v) Coercion Coercion where
  fmap = crcFmap dualSpaceWitness
   where crcFmap :: ∀ s v a b . (LinearSpace v, Scalar v ~ s)
              => DualSpaceWitness v -> Coercion a b
                            -> Coercion (LinearMap s v a) (LinearMap s v b)
         crcFmap DualSpaceWitness f
             = case coerceFmapTensorProduct ([]::[DualVector v]) f of
                       Coercion -> Coercion

instance Category (LinearFunction s) where
  type Object (LinearFunction s) v = (TensorSpace v, Scalar v ~ s)
  id = LinearFunction id
  LinearFunction f . LinearFunction g = LinearFunction $ f.g
instance Num' s => Cartesian (LinearFunction s) where
  type UnitObject (LinearFunction s) = ZeroDim s
  swap = LinearFunction swap
  attachUnit = LinearFunction (, Origin)
  detachUnit = LinearFunction fst
  regroup = LinearFunction regroup
  regroup' = LinearFunction regroup'
instance Num' s => Morphism (LinearFunction s) where
  LinearFunction f***LinearFunction g = LinearFunction $ f***g
instance Num' s => PreArrow (LinearFunction s) where
  LinearFunction f&&&LinearFunction g = LinearFunction $ f&&&g
  fst = LinearFunction fst; snd = LinearFunction snd
  terminal = const0
instance EnhancedCat (->) (LinearFunction s) where
  arr = getLinearFunction
instance EnhancedCat (LinearFunction s) Coercion where
  arr = LinearFunction . coerceWith

instance (LinearSpace w, Num' s, Scalar w ~ s)
     => Functor (LinearFunction s w) (LinearFunction s) (LinearFunction s) where
  fmap f = LinearFunction (f.)


sampleLinearFunctionFn :: ( LinearSpace u, LinearSpace v, TensorSpace w
                          , Scalar u ~ Scalar v, Scalar v ~ Scalar w)
                           => ((u-+>v)-+>w) -+> ((u+>v)+>w)
sampleLinearFunctionFn = LinearFunction $
                \f -> sampleLinearFunction -+$> f . applyLinear

fromLinearFn :: Coercion (LinearFunction s (LinearFunction s u v) w)
                         (Tensor s (LinearFunction s v u) w)
fromLinearFn = Coercion

asLinearFn :: Coercion (Tensor s (LinearFunction s u v) w)
                       (LinearFunction s (LinearFunction s v u) w)
asLinearFn = Coercion


instance ∀ s u v . (LinearSpace u, LinearSpace v, Scalar u ~ s, Scalar v ~ s)
     => TensorSpace (LinearFunction s u v) where
  type TensorProduct (LinearFunction s u v) w = LinearFunction s (LinearFunction s v u) w
  scalarSpaceWitness = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                            , scalarSpaceWitness :: ScalarSpaceWitness v ) of
       (ScalarSpaceWitness, ScalarSpaceWitness) -> ScalarSpaceWitness
  linearManifoldWitness = case ( linearManifoldWitness :: LinearManifoldWitness u
                             , linearManifoldWitness :: LinearManifoldWitness v ) of
       ( LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
          BoundarylessWitness
#endif
        ,LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
          BoundarylessWitness
#endif
        )
         -> LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
             BoundarylessWitness
#endif
  zeroTensor = fromLinearFn $ const0
  toFlatTensor = case scalarSpaceWitness :: ScalarSpaceWitness u of
     ScalarSpaceWitness -> fmap fromLinearFn $ applyDualVector
  fromFlatTensor = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                        , dualSpaceWitness :: DualSpaceWitness u ) of
     (ScalarSpaceWitness, DualSpaceWitness)
            -> arr asLinearFn >>> LinearFunction`id`
                     \f -> let t = transposeTensor . (fmapTensor-+$>fromLinearForm)
                                 -+$> coCurryLinearMap
                                  $ sampleLinearFunction-+$> f . applyLinear
                           in applyLinear $ fromTensor $ t
  addTensors t s = fromLinearFn $ (asLinearFn$t)^+^(asLinearFn$s)
  subtractTensors t s = fromLinearFn $ (asLinearFn$t)^-^(asLinearFn$s)
  scaleTensor = bilinearFunction $ \μ (Tensor f) -> Tensor $ μ *^ f
  negateTensor = LinearFunction $ \(Tensor f) -> Tensor $ negateV f
  tensorProduct = case scalarSpaceWitness :: ScalarSpaceWitness u of
        ScalarSpaceWitness -> bilinearFunction $ \uv w -> Tensor $
                     (applyDualVector-+$>uv) >>> scaleV w
  transposeTensor = tt scalarSpaceWitness dualSpaceWitness
   where tt :: ∀ w . (TensorSpace w, Scalar w ~ s)
                   => ScalarSpaceWitness u -> DualSpaceWitness u
                        -> Tensor s (LinearFunction s u v) w
                           -+> Tensor s w (LinearFunction s u v)
         tt ScalarSpaceWitness DualSpaceWitness
           = LinearFunction $ arr asLinearFn >>> \f
               -> (fmapTensor-+$>applyLinear)
                          -+$> fmap fromTensor . rassocTensor
                           $ transposeTensor . fmap transposeTensor
                          -+$> fmap asTensor . coCurryLinearMap
                            $ sampleLinearFunctionFn -+$> f
  fmapTensor = bilinearFunction $ \f -> arr asLinearFn
                 >>> \g -> fromLinearFn $ f . g
  fzipTensorWith = case scalarSpaceWitness :: ScalarSpaceWitness u of
     ScalarSpaceWitness -> bilinearFunction $ \f (g,h)
                    -> fromLinearFn $ f . ((asLinearFn$g)&&&(asLinearFn$h))
  coerceFmapTensorProduct _ Coercion = Coercion
  wellDefinedVector = arr sampleLinearFunction >>> wellDefinedVector
                       >>> fmap (arr applyLinear)
  wellDefinedTensor = arr asLinearFn >>> (. applyLinear)
                       >>> getLinearFunction sampleLinearFunction
                       >>> wellDefinedVector
                       >>> fmap (arr fromLinearFn <<< \m
                                   -> sampleLinearFunction
                                      >>> getLinearFunction applyLinear m)

exposeLinearFn :: Coercion (LinearMap s (LinearFunction s u v) w)
                           (LinearFunction s (LinearFunction s u v) w)
exposeLinearFn = Coercion

instance (LinearSpace u, LinearSpace v, Scalar u ~ s, Scalar v ~ s)
     => LinearSpace (LinearFunction s u v) where
  type DualVector (LinearFunction s u v) = LinearFunction s v u
  dualSpaceWitness = case ( dualSpaceWitness :: DualSpaceWitness u
                          , dualSpaceWitness :: DualSpaceWitness v ) of
      (DualSpaceWitness, DualSpaceWitness) -> DualSpaceWitness
  linearId = sym exposeLinearFn $ id
  tensorId = uncurryLinearMap . sym exposeLinearFn
               $ LinearFunction $ \f -> sampleLinearFunction-+$>tensorProduct-+$>f
  coerceDoubleDual = Coercion
  sampleLinearFunction = LinearFunction . arr $ sym exposeLinearFn
  applyDualVector = case scalarSpaceWitness :: ScalarSpaceWitness u of
       ScalarSpaceWitness -> bilinearFunction $
                      \f g -> trace . sampleLinearFunction -+$> f . g
  applyLinear = bilinearFunction $ \f g -> (exposeLinearFn $ f) -+$> g
  applyTensorFunctional = atf scalarSpaceWitness dualSpaceWitness
   where atf :: ∀ w . (LinearSpace w, Scalar w ~ s)
                => ScalarSpaceWitness u -> DualSpaceWitness w
                -> LinearFunction s
                    (LinearMap s (LinearFunction s u v) (DualVector w))
                    (LinearFunction s (Tensor s (LinearFunction s u v) w) s)
         atf ScalarSpaceWitness DualSpaceWitness = bilinearFunction $ \f g
                  -> trace -+$> fromTensor $ transposeTensor
                      -+$> fmap ((exposeLinearFn $ f) . applyLinear)
                          -+$> ( transposeTensor
                              -+$> deferLinearMap
                               $ fmap transposeTensor
                              -+$> hasteLinearMap
                               $ transposeTensor
                              -+$> coCurryLinearMap
                               $ sampleLinearFunctionFn
                              -+$> asLinearFn $ g )
  applyTensorLinMap = case scalarSpaceWitness :: ScalarSpaceWitness u of
         ScalarSpaceWitness -> bilinearFunction $ \f g
                 -> contractMapTensor . transposeTensor
                   -+$> fmap ((asLinearFn $ g) . applyLinear)
                    -+$> ( transposeTensor
                      -+$> deferLinearMap
                       $ fmap transposeTensor
                      -+$> hasteLinearMap
                       $ transposeTensor
                      -+$> coCurryLinearMap
                       $ sampleLinearFunctionFn
                      -+$> exposeLinearFn . curryLinearMap $ f )
  useTupleLinearSpaceComponents _ = usingNonTupleTypeAsTupleError


instance (TensorSpace u, TensorSpace v, s~Scalar u, s~Scalar v)
                      => AffineSpace (Tensor s u v) where
  type Diff (Tensor s u v) = Tensor s u v
  (.-.) = (^-^)
  (.+^) = (^+^)
instance (LinearSpace u, TensorSpace v, s~Scalar u, s~Scalar v)
                      => AffineSpace (LinearMap s u v) where
  type Diff (LinearMap s u v) = LinearMap s u v
  (.-.) = (^-^)
  (.+^) = (^+^)
instance (TensorSpace u, TensorSpace v, s~Scalar u, s~Scalar v)
                      => AffineSpace (LinearFunction s u v) where
  type Diff (LinearFunction s u v) = LinearFunction s u v
  (.-.) = (^-^)
  (.+^) = (^+^)

  
-- | Use a function as a linear map. This is only well-defined if the function /is/
--   linear (this condition is not checked).
lfun :: ( EnhancedCat f (LinearFunction s)
        , LinearSpace u, TensorSpace v, Scalar u ~ s, Scalar v ~ s
        , Object f u, Object f v ) => (u->v) -> f u v
lfun = arr . LinearFunction


genericTensorspaceError :: a
genericTensorspaceError = error "GHC.Generics types can not be used as tensor spaces."

usingNonTupleTypeAsTupleError :: a
usingNonTupleTypeAsTupleError = error "This is not a tuple type, the method should not be callable."

instance ∀ v s . TensorSpace v => TensorSpace (Gnrx.Rec0 v s) where
  type TensorProduct (Gnrx.Rec0 v s) w = TensorProduct v w
  wellDefinedVector = fmap Gnrx.K1 . wellDefinedVector . Gnrx.unK1
  wellDefinedTensor = arr (fmap $ pseudoFmapTensorLHS Gnrx.K1)
                         . wellDefinedTensor . arr (pseudoFmapTensorLHS Gnrx.unK1)
  scalarSpaceWitness = genericTensorspaceError
  linearManifoldWitness = genericTensorspaceError
  zeroTensor = pseudoFmapTensorLHS Gnrx.K1 $ zeroTensor
  toFlatTensor = LinearFunction $ Gnrx.unK1 >>> getLinearFunction toFlatTensor
                   >>> arr (pseudoFmapTensorLHS Gnrx.K1)
  fromFlatTensor = LinearFunction $ Gnrx.K1 <<< getLinearFunction fromFlatTensor
                   <<< arr (pseudoFmapTensorLHS Gnrx.unK1)
  addTensors (Tensor s) (Tensor t)
       = pseudoFmapTensorLHS Gnrx.K1 $ addTensors (Tensor s) (Tensor t)
  subtractTensors (Tensor s) (Tensor t)
       = pseudoFmapTensorLHS Gnrx.K1 $ subtractTensors (Tensor s) (Tensor t)
  scaleTensor = LinearFunction $ \μ -> envTensorLHSCoercion Gnrx.K1
                                         $ scaleTensor-+$>μ
  negateTensor = envTensorLHSCoercion Gnrx.K1 negateTensor
  tensorProduct = bilinearFunction $ \(Gnrx.K1 v) w
                      -> pseudoFmapTensorLHS Gnrx.K1
                           $ (tensorProduct-+$>v)-+$>w
  transposeTensor = tT
   where tT :: ∀ w . (TensorSpace w, Scalar w ~ Scalar v)
                => (Gnrx.Rec0 v s ⊗ w) -+> (w ⊗ Gnrx.Rec0 v s)
         tT = LinearFunction
           $ arr (Coercion . coerceFmapTensorProduct ([]::[w])
                                    (Coercion :: Coercion v (Gnrx.Rec0 v s)) . Coercion)
              . getLinearFunction transposeTensor . arr (pseudoFmapTensorLHS Gnrx.unK1)
  fmapTensor = LinearFunction $
         \f -> envTensorLHSCoercion Gnrx.K1 (fmapTensor-+$>f)
  fzipTensorWith = bilinearFunction $
         \f (wt, xt) -> pseudoFmapTensorLHS Gnrx.K1
                        $ (fzipTensorWith-+$>f)
                         -+$>( pseudoFmapTensorLHS Gnrx.unK1 $ wt
                             , pseudoFmapTensorLHS Gnrx.unK1 $ xt )
  coerceFmapTensorProduct = cmtp
   where cmtp :: ∀ p a b . Hask.Functor p
             => p (Gnrx.Rec0 v s) -> Coercion a b
               -> Coercion (TensorProduct (Gnrx.Rec0 v s) a)
                           (TensorProduct (Gnrx.Rec0 v s) b)
         cmtp p crc = case coerceFmapTensorProduct ([]::[v]) crc of
                  Coercion -> Coercion

instance ∀ i c f p . TensorSpace (f p) => TensorSpace (Gnrx.M1 i c f p) where
  type TensorProduct (Gnrx.M1 i c f p) w = TensorProduct (f p) w
  wellDefinedVector = fmap Gnrx.M1 . wellDefinedVector . Gnrx.unM1
  wellDefinedTensor = arr (fmap $ pseudoFmapTensorLHS Gnrx.M1)
                         . wellDefinedTensor . arr (pseudoFmapTensorLHS Gnrx.unM1)
  scalarSpaceWitness = genericTensorspaceError
  linearManifoldWitness = genericTensorspaceError
  zeroTensor = pseudoFmapTensorLHS Gnrx.M1 $ zeroTensor
  toFlatTensor = LinearFunction $ Gnrx.unM1 >>> getLinearFunction toFlatTensor
                   >>> arr (pseudoFmapTensorLHS Gnrx.M1)
  fromFlatTensor = LinearFunction $ Gnrx.M1 <<< getLinearFunction fromFlatTensor
                   <<< arr (pseudoFmapTensorLHS Gnrx.unM1)
  addTensors (Tensor s) (Tensor t)
       = pseudoFmapTensorLHS Gnrx.M1 $ addTensors (Tensor s) (Tensor t)
  subtractTensors (Tensor s) (Tensor t)
       = pseudoFmapTensorLHS Gnrx.M1 $ subtractTensors (Tensor s) (Tensor t)
  scaleTensor = LinearFunction $ \μ -> envTensorLHSCoercion Gnrx.M1
                                         $ scaleTensor-+$>μ
  negateTensor = envTensorLHSCoercion Gnrx.M1 negateTensor
  tensorProduct = bilinearFunction $ \(Gnrx.M1 v) w
                      -> pseudoFmapTensorLHS Gnrx.M1
                           $ (tensorProduct-+$>v)-+$>w
  transposeTensor = tT
   where tT :: ∀ w . (TensorSpace w, Scalar w ~ Scalar (f p))
                => (Gnrx.M1 i c f p ⊗ w) -+> (w ⊗ Gnrx.M1 i c f p)
         tT = LinearFunction
           $ arr (Coercion . coerceFmapTensorProduct ([]::[w])
                                (Coercion :: Coercion (f p) (Gnrx.M1 i c f p)) . Coercion)
              . getLinearFunction transposeTensor . arr (pseudoFmapTensorLHS Gnrx.unM1)
  fmapTensor = LinearFunction $
         \f -> envTensorLHSCoercion Gnrx.M1 (fmapTensor-+$>f)
  fzipTensorWith = bilinearFunction $
         \f (wt, xt) -> pseudoFmapTensorLHS Gnrx.M1
                        $ (fzipTensorWith-+$>f)
                         -+$>( pseudoFmapTensorLHS Gnrx.unM1 $ wt
                             , pseudoFmapTensorLHS Gnrx.unM1 $ xt )
  coerceFmapTensorProduct = cmtp
   where cmtp :: ∀ ぴ a b . Hask.Functor ぴ
             => ぴ (Gnrx.M1 i c f p) -> Coercion a b
               -> Coercion (TensorProduct (Gnrx.M1 i c f p) a)
                           (TensorProduct (Gnrx.M1 i c f p) b)
         cmtp p crc = case coerceFmapTensorProduct ([]::[f p]) crc of
                  Coercion -> Coercion

instance ∀ f g p . ( TensorSpace (f p), TensorSpace (g p), Scalar (f p) ~ Scalar (g p) )
                       => TensorSpace ((f:*:g) p) where
  type TensorProduct ((f:*:g) p) w = (f p⊗w, g p⊗w)
  scalarSpaceWitness = case ( scalarSpaceWitness :: ScalarSpaceWitness (f p)
                            , scalarSpaceWitness :: ScalarSpaceWitness (g p) ) of
       (ScalarSpaceWitness, ScalarSpaceWitness) -> ScalarSpaceWitness
  linearManifoldWitness = genericTensorspaceError
  zeroTensor = Tensor (zeroTensor, zeroTensor)
  scaleTensor = bilinearFunction $ \μ (Tensor (v,w)) ->
                 Tensor ( (scaleTensor-+$>μ)-+$>v, (scaleTensor-+$>μ)-+$>w )
  negateTensor = LinearFunction $ \(Tensor (v,w))
          -> Tensor (negateTensor-+$>v, negateTensor-+$>w)
  addTensors (Tensor (fu, fv)) (Tensor (fu', fv'))
           = Tensor (fu ^+^ fu', fv ^+^ fv')
  subtractTensors (Tensor (fu, fv)) (Tensor (fu', fv'))
          = Tensor (fu ^-^ fu', fv ^-^ fv')
  toFlatTensor = LinearFunction
      $ \(u:*:v) -> Tensor (toFlatTensor-+$>u, toFlatTensor-+$>v)
  fromFlatTensor = LinearFunction
      $ \(Tensor (u,v)) -> (fromFlatTensor-+$>u):*:(fromFlatTensor-+$>v)
  tensorProduct = bilinearFunction $ \(u:*:v) w ->
      Tensor ((tensorProduct-+$>u)-+$>w, (tensorProduct-+$>v)-+$>w)
  transposeTensor = LinearFunction $ \(Tensor (uw,vw))
        -> (fzipTensorWith-+$>LinearFunction (\(u,v)->u:*:v))
             -+$>(transposeTensor-+$>uw,transposeTensor-+$>vw)
  fmapTensor = bilinearFunction $
     \f (Tensor (uw,vw)) -> Tensor ((fmapTensor-+$>f)-+$>uw, (fmapTensor-+$>f)-+$>vw)
  fzipTensorWith = bilinearFunction
               $ \f (Tensor (uw, vw), Tensor (ux, vx))
                      -> Tensor ( (fzipTensorWith-+$>f)-+$>(uw,ux)
                                , (fzipTensorWith-+$>f)-+$>(vw,vx) )
  coerceFmapTensorProduct p cab = case
             ( coerceFmapTensorProduct ((\(u:*:_)->u)<$>p) cab
             , coerceFmapTensorProduct ((\(_:*:v)->v)<$>p) cab ) of
          (Coercion, Coercion) -> Coercion
  wellDefinedVector (u:*:v) = liftA2 (:*:) (wellDefinedVector u) (wellDefinedVector v)
  wellDefinedTensor (Tensor (u,v))
         = liftA2 ((Tensor.) . (,)) (wellDefinedTensor u) (wellDefinedTensor v)


instance ∀ m . ( Semimanifold m, TensorSpace (Needle (VRep m))
                               , Scalar (Needle m) ~ Scalar (Needle (VRep m)) )
                  => TensorSpace (GenericNeedle m) where
  type TensorProduct (GenericNeedle m) w = TensorProduct (Needle (VRep m)) w
  wellDefinedVector = fmap GenericNeedle . wellDefinedVector . getGenericNeedle
  wellDefinedTensor = arr (fmap $ pseudoFmapTensorLHS GenericNeedle)
                         . wellDefinedTensor . arr (pseudoFmapTensorLHS getGenericNeedle)
  scalarSpaceWitness = case scalarSpaceWitness
                               :: ScalarSpaceWitness (Needle (VRep m)) of
          ScalarSpaceWitness -> ScalarSpaceWitness
  linearManifoldWitness = case linearManifoldWitness
                               :: LinearManifoldWitness (Needle (VRep m)) of
          LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
           BoundarylessWitness
#endif
              -> LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
                  BoundarylessWitness
#endif
  zeroTensor = pseudoFmapTensorLHS GenericNeedle $ zeroTensor
  toFlatTensor = LinearFunction $ arr (pseudoFmapTensorLHS GenericNeedle)
                             . getLinearFunction toFlatTensor
                             . getGenericNeedle
  fromFlatTensor = LinearFunction $ arr (pseudoFmapTensorLHS getGenericNeedle)
                             >>> getLinearFunction fromFlatTensor
                             >>> GenericNeedle
  addTensors (Tensor s) (Tensor t)
       = pseudoFmapTensorLHS GenericNeedle $ addTensors (Tensor s) (Tensor t)
  subtractTensors (Tensor s) (Tensor t)
       = pseudoFmapTensorLHS GenericNeedle $ subtractTensors (Tensor s) (Tensor t)
  scaleTensor = LinearFunction $ \μ -> envTensorLHSCoercion GenericNeedle
                                         $ scaleTensor-+$>μ
  negateTensor = envTensorLHSCoercion GenericNeedle negateTensor
  tensorProduct = bilinearFunction $ \(GenericNeedle v) w
                      -> pseudoFmapTensorLHS GenericNeedle
                           $ (tensorProduct-+$>v)-+$>w
  transposeTensor = tT
   where tT :: ∀ w . (TensorSpace w, Scalar w ~ Scalar (Needle m))
                => (GenericNeedle m ⊗ w) -+> (w ⊗ GenericNeedle m)
         tT = LinearFunction
           $ arr (Coercion . coerceFmapTensorProduct ([]::[w])
                              (Coercion :: Coercion (Needle (VRep m))
                                                    (GenericNeedle m)) . Coercion)
              . getLinearFunction transposeTensor . arr (pseudoFmapTensorLHS getGenericNeedle)
  fmapTensor = LinearFunction $
         \f -> envTensorLHSCoercion GenericNeedle (fmapTensor-+$>f)
  fzipTensorWith = bilinearFunction $
         \f (wt, xt) -> pseudoFmapTensorLHS GenericNeedle
                        $ (fzipTensorWith-+$>f)
                         -+$>( pseudoFmapTensorLHS getGenericNeedle $ wt
                             , pseudoFmapTensorLHS getGenericNeedle $ xt )
  coerceFmapTensorProduct = cmtp
   where cmtp :: ∀ p a b . Hask.Functor p
             => p (GenericNeedle m) -> Coercion a b
               -> Coercion (TensorProduct (GenericNeedle m) a)
                           (TensorProduct (GenericNeedle m) b)
         cmtp p crc = case coerceFmapTensorProduct ([]::[Needle (VRep m)]) crc of
                  Coercion -> Coercion

instance (LinearSpace v, Num (Scalar v)) => LinearSpace (Gnrx.Rec0 v s) where
  type DualVector (Gnrx.Rec0 v s) = DualVector v
  dualSpaceWitness = genericTensorspaceError
  linearId = pseudoPrecomposeLinmap Gnrx.unK1
                . fmap (follow Gnrx.K1) $ linearId
  applyDualVector = bilinearFunction $ \dv (Gnrx.K1 v) -> (applyDualVector-+$>dv)-+$>v
  applyLinear = bilinearFunction $ \(LinearMap f) (Gnrx.K1 v)
                      -> (applyLinear-+$>LinearMap f)-+$>v
  tensorId = pseudoPrecomposeLinmap (pseudoFmapTensorLHS Gnrx.unK1)
                . fmap (pseudoFmapTensorLHS Gnrx.K1) $ tensorId
  applyTensorFunctional = bilinearFunction $ \(LinearMap f) t ->
              (applyTensorFunctional-+$>LinearMap f)-+$>pseudoFmapTensorLHS Gnrx.unK1 $ t
  applyTensorLinMap = bilinearFunction $ \(LinearMap f) t
                -> (applyTensorLinMap-+$>LinearMap f)-+$>pseudoFmapTensorLHS Gnrx.unK1 $ t
  useTupleLinearSpaceComponents _ = usingNonTupleTypeAsTupleError

instance (LinearSpace (f p), Num (Scalar (f p))) => LinearSpace (Gnrx.M1 i c f p) where
  type DualVector (Gnrx.M1 i c f p) = DualVector (f p)
  dualSpaceWitness = genericTensorspaceError
  linearId = pseudoPrecomposeLinmap Gnrx.unM1
                . fmap (follow Gnrx.M1) $ linearId
  applyDualVector = bilinearFunction $ \dv (Gnrx.M1 v) -> (applyDualVector-+$>dv)-+$>v
  applyLinear = bilinearFunction $ \(LinearMap f) (Gnrx.M1 v)
                      -> (applyLinear-+$>LinearMap f)-+$>v
  tensorId = pseudoPrecomposeLinmap (pseudoFmapTensorLHS Gnrx.unM1)
                . fmap (pseudoFmapTensorLHS Gnrx.M1) $ tensorId
  applyTensorFunctional = bilinearFunction $ \(LinearMap f) t ->
              (applyTensorFunctional-+$>LinearMap f)-+$>pseudoFmapTensorLHS Gnrx.unM1 $ t
  applyTensorLinMap = bilinearFunction $ \(LinearMap f) t
                -> (applyTensorLinMap-+$>LinearMap f)-+$>pseudoFmapTensorLHS Gnrx.unM1 $ t
  useTupleLinearSpaceComponents _ = usingNonTupleTypeAsTupleError

data GenericTupleDual f g p
    = GenericTupleDual !(DualVector (f p)) !(DualVector (g p)) deriving (Generic)
instance (AdditiveGroup (DualVector (f p)), AdditiveGroup (DualVector (g p)))
    => AdditiveGroup (GenericTupleDual f g p)
instance ( VectorSpace (DualVector (f p)), VectorSpace (DualVector (g p))
         , Scalar (DualVector (f p)) ~ Scalar (DualVector (g p)) )
    => VectorSpace (GenericTupleDual f g p)
instance ( InnerSpace (DualVector (f p)), InnerSpace (DualVector (g p))
         , Scalar (DualVector (f p)) ~ Scalar (DualVector (g p))
         , Num (Scalar (DualVector (f p))) )
    => InnerSpace (GenericTupleDual f g p)
instance (AdditiveGroup (DualVector (f p)), AdditiveGroup (DualVector (g p)))
    => AffineSpace (GenericTupleDual f g p) where
  type Diff (GenericTupleDual f g p) = GenericTupleDual f g p
  (.+^) = (^+^)
  (.-.) = (^-^)
instance (AdditiveGroup (DualVector (f p)), AdditiveGroup (DualVector (g p)))
    => Semimanifold (GenericTupleDual f g p) where
  type Needle (GenericTupleDual f g p) = GenericTupleDual f g p
  (.+~^) = (^+^)
#if !MIN_VERSION_manifolds_core(0,6,0)
  fromInterior = id
  toInterior = pure
  translateP = Tagged (^+^)
#endif
instance (AdditiveGroup (DualVector (f p)), AdditiveGroup (DualVector (g p)))
    => PseudoAffine (GenericTupleDual f g p) where
  p.-~.q = Just $ p.-.q
  (.-~!) = (.-.)

instance ( LinearSpace (f p), LinearSpace (g p)
         , VectorSpace (DualVector (f p)), VectorSpace (DualVector (g p))
         , Scalar (f p) ~ Scalar (DualVector (f p))
         , Scalar (g p) ~ Scalar (DualVector (g p))
         , Scalar (DualVector (f p)) ~ Scalar (DualVector (g p)) )
    => TensorSpace (GenericTupleDual f g p) where
  type TensorProduct (GenericTupleDual f g p) w = (f p+>w, g p+>w)
  wellDefinedVector = case ( dualSpaceWitness :: DualSpaceWitness (f p)
                           , dualSpaceWitness :: DualSpaceWitness (g p) ) of
      (DualSpaceWitness, DualSpaceWitness)
       -> \(GenericTupleDual fv gv)
           -> liftA2 GenericTupleDual (wellDefinedVector fv) (wellDefinedVector gv)
  wellDefinedTensor = case ( dualSpaceWitness :: DualSpaceWitness (f p)
                           , dualSpaceWitness :: DualSpaceWitness (g p) ) of
      (DualSpaceWitness, DualSpaceWitness)
       -> \(Tensor (ft, gt))
        -> Tensor <$> liftA2 (,) (fmap fromTensor $ wellDefinedTensor (fromLinearMap $ ft))
                                 (fmap fromTensor $ wellDefinedTensor (fromLinearMap $ gt))
  scalarSpaceWitness = case scalarSpaceWitness :: ScalarSpaceWitness (f p) of
        ScalarSpaceWitness -> ScalarSpaceWitness
  linearManifoldWitness = LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
                           BoundarylessWitness
#endif
  zeroTensor = case ( linearManifoldWitness :: LinearManifoldWitness (f p)
                    , dualSpaceWitness :: DualSpaceWitness (f p)
                    , dualSpaceWitness :: DualSpaceWitness (g p) ) of
       ( LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
          BoundarylessWitness
#endif
        ,DualSpaceWitness, DualSpaceWitness )
           -> Tensor (fromTensor $ zeroTensor, fromTensor $ zeroTensor)
  toFlatTensor = case ( scalarSpaceWitness :: ScalarSpaceWitness (f p)
                      , dualSpaceWitness :: DualSpaceWitness (f p)
                      , dualSpaceWitness :: DualSpaceWitness (g p) ) of
       (ScalarSpaceWitness, DualSpaceWitness, DualSpaceWitness)
          -> LinearFunction $ \(GenericTupleDual tf tg)
            -> Tensor ( toLinearForm $ tf, toLinearForm $ tg )
  fromFlatTensor = case ( scalarSpaceWitness :: ScalarSpaceWitness (f p)
                        , dualSpaceWitness :: DualSpaceWitness (f p)
                        , dualSpaceWitness :: DualSpaceWitness (g p) ) of
       (ScalarSpaceWitness, DualSpaceWitness, DualSpaceWitness)
          -> LinearFunction $ \(Tensor (tf,tg))
            -> GenericTupleDual (fromLinearForm $ tf) (fromLinearForm $ tg)
  addTensors (Tensor (sf,sg)) (Tensor (tf,tg)) = Tensor (sf^+^tf, sg^+^tg)
  negateTensor = LinearFunction $ \(Tensor (tf,tg))
                   -> Tensor (negateV tf, negateV tg)
  scaleTensor = bilinearFunction $ \μ (Tensor (tf,tg)) -> Tensor (μ*^tf, μ*^tg)
  tensorProduct = case ( scalarSpaceWitness :: ScalarSpaceWitness (f p)
                       , dualSpaceWitness :: DualSpaceWitness (f p)
                       , dualSpaceWitness :: DualSpaceWitness (g p) ) of
       (ScalarSpaceWitness, DualSpaceWitness, DualSpaceWitness)
          -> bilinearFunction $ \(GenericTupleDual fw gw) x
                   -> Tensor (fromTensor $ fw⊗x, fromTensor $ gw⊗x)
  transposeTensor = case ( scalarSpaceWitness :: ScalarSpaceWitness (f p)
                         , dualSpaceWitness :: DualSpaceWitness (f p)
                         , dualSpaceWitness :: DualSpaceWitness (g p) ) of
       (ScalarSpaceWitness, DualSpaceWitness, DualSpaceWitness)
          -> LinearFunction $ \(Tensor (fw, gw))
                     -> (fzipTensorWith-+$>LinearFunction`id`uncurry GenericTupleDual)
                       -+$> ( transposeTensor-+$>asTensor $ fw
                            , transposeTensor-+$>asTensor $ gw )
  fmapTensor = case ( scalarSpaceWitness :: ScalarSpaceWitness (f p)
                    , dualSpaceWitness :: DualSpaceWitness (f p)
                    , dualSpaceWitness :: DualSpaceWitness (g p) ) of
       (ScalarSpaceWitness, DualSpaceWitness, DualSpaceWitness)
          -> bilinearFunction $ \f (Tensor (fw, gw))
                 -> Tensor ( fromTensor $ (fmapTensor-+$>f) -+$> asTensor $ fw
                           , fromTensor $ (fmapTensor-+$>f) -+$> asTensor $ gw )
  fzipTensorWith = case ( scalarSpaceWitness :: ScalarSpaceWitness (f p)
                        , dualSpaceWitness :: DualSpaceWitness (f p)
                        , dualSpaceWitness :: DualSpaceWitness (g p) ) of
       (ScalarSpaceWitness, DualSpaceWitness, DualSpaceWitness)
          -> bilinearFunction $ \f (Tensor (fw, gw), Tensor (fx, gx))
                 -> Tensor ( fromTensor $ (fzipTensorWith-+$>f) -+$> ( asTensor $ fw
                                                                     , asTensor $ fx )
                           , fromTensor $ (fzipTensorWith-+$>f) -+$> ( asTensor $ gw
                                                                     , asTensor $ gx ) )
  coerceFmapTensorProduct p cab = case ( dualSpaceWitness :: DualSpaceWitness (f p)
                                       , dualSpaceWitness :: DualSpaceWitness (g p) ) of
       (DualSpaceWitness, DualSpaceWitness) -> case
             ( coerceFmapTensorProduct ((\(GenericTupleDual u _)->u)<$>p) cab
             , coerceFmapTensorProduct ((\(GenericTupleDual _ v)->v)<$>p) cab ) of
          (Coercion, Coercion) -> Coercion
  


instance ∀ f g p . ( LinearSpace (f p), LinearSpace (g p), Scalar (f p) ~ Scalar (g p) )
                       => LinearSpace ((f:*:g) p) where
  type DualVector ((f:*:g) p) = GenericTupleDual f g p
  
  dualSpaceWitness = genericTensorspaceError
  linearId = case ( scalarSpaceWitness :: ScalarSpaceWitness (f p)
                  , dualSpaceWitness :: DualSpaceWitness (f p)
                  , dualSpaceWitness :: DualSpaceWitness (g p) ) of
       (ScalarSpaceWitness, DualSpaceWitness, DualSpaceWitness)
             -> LinearMap ( arr $ LinearFunction (\vf->(vf:*:zeroV))
                          , arr $ LinearFunction (\vg->(zeroV:*:vg)) )
  tensorId = tI scalarSpaceWitness dualSpaceWitness dualSpaceWitness dualSpaceWitness
   where tI :: ∀ w . (LinearSpace w, Scalar w ~ Scalar (f p))
                 => ScalarSpaceWitness (f p) -> DualSpaceWitness (f p)
                     -> DualSpaceWitness (g p) -> DualSpaceWitness w
                       -> (((f:*:g) p)⊗w)+>(((f:*:g) p)⊗w)
         tI ScalarSpaceWitness DualSpaceWitness DualSpaceWitness DualSpaceWitness 
              = LinearMap
            ( arr $ LinearFunction (\vf -> asTensor
             $ arr (LinearFunction $ \w -> Tensor (vf⊗w, zeroV)))
            , arr $ LinearFunction (\vg -> asTensor
             $ arr (LinearFunction $ \w -> Tensor (zeroV, vg⊗w))) )
  sampleLinearFunction = case ( scalarSpaceWitness :: ScalarSpaceWitness (f p)
                              , dualSpaceWitness :: DualSpaceWitness (f p)
                              , dualSpaceWitness :: DualSpaceWitness (g p) ) of
       (ScalarSpaceWitness, DualSpaceWitness, DualSpaceWitness)
              -> LinearFunction $ \f -> LinearMap
                   ( sampleLinearFunction -+$> LinearFunction`id`
                       \vf -> f -+$> (vf:*:zeroV)
                   , sampleLinearFunction -+$> LinearFunction`id`
                       \vg -> f -+$> (zeroV:*:vg) )
  applyDualVector = case ( scalarSpaceWitness :: ScalarSpaceWitness (f p)
                         , dualSpaceWitness :: DualSpaceWitness (f p)
                         , dualSpaceWitness :: DualSpaceWitness (g p) ) of
       (ScalarSpaceWitness, DualSpaceWitness, DualSpaceWitness)
              -> bilinearFunction $ \(GenericTupleDual du dv) (u:*:v)
                      -> ((applyDualVector-+$>du)-+$>u) ^+^ ((applyDualVector-+$>dv)-+$>v)
  applyLinear = case ( scalarSpaceWitness :: ScalarSpaceWitness (f p)
                     , dualSpaceWitness :: DualSpaceWitness (f p)
                     , dualSpaceWitness :: DualSpaceWitness (g p) ) of
       (ScalarSpaceWitness, DualSpaceWitness, DualSpaceWitness)
              -> bilinearFunction $ \(LinearMap (fu, fv)) (u:*:v)
                      -> ((applyLinear-+$>fu)-+$>u) ^+^ ((applyLinear-+$>fv)-+$>v)
  composeLinear = case ( dualSpaceWitness :: DualSpaceWitness (f p)
                       , dualSpaceWitness :: DualSpaceWitness (g p) ) of
       (DualSpaceWitness, DualSpaceWitness)
              -> bilinearFunction $ \f (LinearMap (fu, fv))
                    -> LinearMap ( (composeLinear-+$>f)-+$>fu
                                 , (composeLinear-+$>f)-+$>fv )
  applyTensorFunctional = case ( dualSpaceWitness :: DualSpaceWitness (f p)
                               , dualSpaceWitness :: DualSpaceWitness (g p) ) of
     (DualSpaceWitness, DualSpaceWitness) -> bilinearFunction $
                  \(LinearMap (fu,fv)) (Tensor (tu,tv))
          -> ((applyTensorFunctional-+$>fu)-+$>tu) + ((applyTensorFunctional-+$>fu)-+$>tu)
  applyTensorLinMap = case ( dualSpaceWitness :: DualSpaceWitness (f p)
                           , dualSpaceWitness :: DualSpaceWitness (g p) ) of
     (DualSpaceWitness, DualSpaceWitness) -> bilinearFunction`id`
             \(LinearMap (fu,fv)) (Tensor (tu,tv))
          -> ((applyTensorLinMap -+$> uncurryLinearMap . fmap fromTensor $ fu)-+$>tu)
           ^+^ ((applyTensorLinMap -+$> uncurryLinearMap . fmap fromTensor $ fv)-+$>tv)
  useTupleLinearSpaceComponents _ = usingNonTupleTypeAsTupleError


newtype GenericNeedle' m
    = GenericNeedle' { getGenericNeedle' :: DualVector (Needle (VRep m)) }
        deriving (Generic)
instance AdditiveGroup (DualVector (Needle (VRep m)))
      => AdditiveGroup (GenericNeedle' m)
instance ( VectorSpace (DualVector (Needle (VRep m)))
         , Scalar (Needle m) ~ Scalar (DualVector (Needle (VRep m))) )
      => VectorSpace (GenericNeedle' m) where
  type Scalar (GenericNeedle' m) = Scalar (Needle m)
instance AdditiveGroup (DualVector (Needle (VRep m)))
      => AffineSpace (GenericNeedle' m) where
  type Diff (GenericNeedle' m) = GenericNeedle' m
  (.-.) = (^-^)
  (.+^) = (^+^)
instance AdditiveGroup (DualVector (Needle (VRep m)))
    => Semimanifold (GenericNeedle' m) where
  type Needle (GenericNeedle' m) = GenericNeedle' m
#if !MIN_VERSION_manifolds_core(0,6,0)
  type Interior (GenericNeedle' m) = GenericNeedle' m
  toInterior = pure
  fromInterior = id
  translateP = Tagged (^+^)
#endif
  (.+~^) = (^+^)
instance AdditiveGroup (DualVector (Needle (VRep m)))
    => PseudoAffine (GenericNeedle' m) where
  p.-~.q = pure (p^-^q)
  (.-~!) = (^-^)
instance ∀ m . ( Semimanifold m, TensorSpace (DualVector (Needle (VRep m)))
               , Scalar (Needle m) ~ Scalar (DualVector (Needle (VRep m))) )
                  => TensorSpace (GenericNeedle' m) where
  type TensorProduct (GenericNeedle' m) w
         = TensorProduct (DualVector (Needle (VRep m))) w
  wellDefinedVector = fmap GenericNeedle' . wellDefinedVector . getGenericNeedle'
  wellDefinedTensor = arr (fmap $ pseudoFmapTensorLHS GenericNeedle')
                         . wellDefinedTensor . arr (pseudoFmapTensorLHS getGenericNeedle')
  scalarSpaceWitness = case scalarSpaceWitness
                    :: ScalarSpaceWitness (DualVector (Needle (VRep m))) of
          ScalarSpaceWitness -> ScalarSpaceWitness
  linearManifoldWitness = case linearManifoldWitness
                    :: LinearManifoldWitness (DualVector (Needle (VRep m))) of
          LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
           BoundarylessWitness
#endif
              -> LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
                  BoundarylessWitness
#endif
  zeroTensor = pseudoFmapTensorLHS GenericNeedle' $ zeroTensor
  toFlatTensor = LinearFunction $ arr (pseudoFmapTensorLHS GenericNeedle')
                             . getLinearFunction toFlatTensor
                             . getGenericNeedle'
  fromFlatTensor = LinearFunction $ arr (pseudoFmapTensorLHS getGenericNeedle')
                             >>> getLinearFunction fromFlatTensor
                             >>> GenericNeedle'
  addTensors (Tensor s) (Tensor t)
       = pseudoFmapTensorLHS GenericNeedle' $ addTensors (Tensor s) (Tensor t)
  subtractTensors (Tensor s) (Tensor t)
       = pseudoFmapTensorLHS GenericNeedle' $ subtractTensors (Tensor s) (Tensor t)
  scaleTensor = LinearFunction $ \μ -> envTensorLHSCoercion GenericNeedle'
                                         $ scaleTensor-+$>μ
  negateTensor = envTensorLHSCoercion GenericNeedle' negateTensor
  tensorProduct = bilinearFunction $ \(GenericNeedle' v) w
                      -> pseudoFmapTensorLHS GenericNeedle'
                           $ (tensorProduct-+$>v)-+$>w
  transposeTensor = tT
   where tT :: ∀ w . (TensorSpace w, Scalar w ~ Scalar (Needle m))
                => (GenericNeedle' m ⊗ w) -+> (w ⊗ GenericNeedle' m)
         tT = LinearFunction
           $ arr (Coercion . coerceFmapTensorProduct ([]::[w])
                              (Coercion :: Coercion (DualVector (Needle (VRep m)))
                                                    (GenericNeedle' m)) . Coercion)
              . getLinearFunction transposeTensor . arr (pseudoFmapTensorLHS getGenericNeedle')
  fmapTensor = LinearFunction $
         \f -> envTensorLHSCoercion GenericNeedle' (fmapTensor-+$>f)
  fzipTensorWith = bilinearFunction $
         \f (wt, xt) -> pseudoFmapTensorLHS GenericNeedle'
                        $ (fzipTensorWith-+$>f)
                         -+$>( pseudoFmapTensorLHS getGenericNeedle' $ wt
                             , pseudoFmapTensorLHS getGenericNeedle' $ xt )
  coerceFmapTensorProduct = cmtp
   where cmtp :: ∀ p a b . Hask.Functor p
             => p (GenericNeedle' m) -> Coercion a b
               -> Coercion (TensorProduct (GenericNeedle' m) a)
                           (TensorProduct (GenericNeedle' m) b)
         cmtp p crc = case coerceFmapTensorProduct
                              ([]::[DualVector (Needle (VRep m))]) crc of
                  Coercion -> Coercion


instance ∀ s m . ( Num' s
                 , Semimanifold m, LinearSpace (Needle (VRep m))
                 , Scalar (Needle m) ~ s
                 , Scalar (Needle (VRep m)) ~ s )
                  => LinearSpace (GenericNeedle m) where
  type DualVector (GenericNeedle m) = GenericNeedle' m
  linearId = fmap (follow GenericNeedle) . pseudoPrecomposeLinmap getGenericNeedle
               $ linearId
  dualSpaceWitness = case ( closedScalarWitness :: ClosedScalarWitness s
                          , dualSpaceWitness :: DualSpaceWitness (Needle (VRep m)) ) of
              (ClosedScalarWitness, DualSpaceWitness) -> DualSpaceWitness
  applyDualVector = bilinearFunction $ \(GenericNeedle' dv) (GenericNeedle v)
                        -> (applyDualVector-+$>dv)-+$>v
  applyLinear = bilinearFunction $ \(LinearMap f) (GenericNeedle v)
                      -> (applyLinear-+$>LinearMap f)-+$>v
  tensorId = pseudoPrecomposeLinmap (pseudoFmapTensorLHS getGenericNeedle)
                . fmap (pseudoFmapTensorLHS GenericNeedle) $ tensorId
  applyTensorFunctional = bilinearFunction $ \(LinearMap f) t ->
              (applyTensorFunctional-+$>LinearMap f)
                 -+$>pseudoFmapTensorLHS getGenericNeedle $ t
  applyTensorLinMap = bilinearFunction $ \(LinearMap f) t
                -> (applyTensorLinMap-+$>LinearMap f)
                    -+$>pseudoFmapTensorLHS getGenericNeedle $ t
  useTupleLinearSpaceComponents _ = usingNonTupleTypeAsTupleError

instance ∀ s m . ( Num' s
                 , Semimanifold m
                 , LinearSpace (Needle (VRep m))
                 , TensorSpace (DualVector (Needle (VRep m)))
                 , Scalar (Needle m) ~ s
                 , Scalar (Needle (VRep m)) ~ s
                 , Scalar (DualVector (Needle (VRep m))) ~ s )
                  => LinearSpace (GenericNeedle' m) where
  type DualVector (GenericNeedle' m) = GenericNeedle m
  linearId = case dualSpaceWitness :: DualSpaceWitness (Needle (VRep m)) of
       DualSpaceWitness -> fmap (follow GenericNeedle')
                         . pseudoPrecomposeLinmap getGenericNeedle' $ linearId
  dualSpaceWitness = case ( closedScalarWitness :: ClosedScalarWitness s
                          , dualSpaceWitness :: DualSpaceWitness (Needle (VRep m)) ) of
              (ClosedScalarWitness, DualSpaceWitness) -> DualSpaceWitness
  applyDualVector = case dualSpaceWitness :: DualSpaceWitness (Needle (VRep m)) of
       DualSpaceWitness -> bilinearFunction $ \(GenericNeedle dv) (GenericNeedle' v)
                        -> (applyDualVector-+$>dv)-+$>v
  applyLinear = case dualSpaceWitness :: DualSpaceWitness (Needle (VRep m)) of
       DualSpaceWitness -> bilinearFunction $ \(LinearMap f) (GenericNeedle' v)
                      -> (applyLinear-+$>LinearMap f)-+$>v
  tensorId = case dualSpaceWitness :: DualSpaceWitness (Needle (VRep m)) of
       DualSpaceWitness -> pseudoPrecomposeLinmap (pseudoFmapTensorLHS getGenericNeedle')
                . fmap (pseudoFmapTensorLHS GenericNeedle') $ tensorId
  applyTensorFunctional = case dualSpaceWitness :: DualSpaceWitness (Needle (VRep m)) of
       DualSpaceWitness -> bilinearFunction $ \(LinearMap f) t ->
              (applyTensorFunctional-+$>LinearMap f)
                 -+$>pseudoFmapTensorLHS getGenericNeedle' $ t
  applyTensorLinMap = case dualSpaceWitness :: DualSpaceWitness (Needle (VRep m)) of
       DualSpaceWitness -> bilinearFunction $ \(LinearMap f) t
                -> (applyTensorLinMap-+$>LinearMap f)
                    -+$>pseudoFmapTensorLHS getGenericNeedle' $ t
  useTupleLinearSpaceComponents _ = usingNonTupleTypeAsTupleError

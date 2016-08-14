-- |
-- Module      : Math.LinearMap.Category
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
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Math.LinearMap.Category (
            -- * Linear maps
              LinearMap (..), (+>)()
            , DualSpace
            , (⊕), (>+<)
            -- * Solving linear equations
            , (\$), pseudoInverse
            -- * The classes of suitable vector spaces
            -- ** General linear maps
            , LinearSpace (..)
            -- ** Orthonormal systems
            , SemiInner (..), cartesianDualBasisCandidates
            -- ** Finite baseis
            , FiniteDimensional (..)
            -- * Utility
            , riesz, coRiesz, showsPrecAsRiesz, (.<)
            , Num', Fractional'
            ) where

import Data.VectorSpace
import Data.Basis

import Prelude ()
import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.Tree (Tree(..), Forest)
import Data.List (sortBy, foldl')
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Ord (comparing)
import Data.List (maximumBy)
import Data.Foldable (toList)

import Data.Coerce
import Data.Type.Coercion

import Data.VectorSpace.Free
import qualified Linear.Matrix as Mat
import qualified Linear.Vector as Mat

import Math.LinearMap.Asserted
import Math.VectorSpace.ZeroDimensional

type Num' s = (Num s, VectorSpace s, Scalar s ~ s)
type Num'' s = (Num' s, LinearSpace s)
type Num''' s = (Num s, Scalar s ~ s, LSpace' s)
  
class (VectorSpace v) => TensorSpace v where
  type TensorProduct v w :: *
  zeroTensor :: (LSpace w, Scalar w ~ Scalar v)
                => v ⊗ w
  toFlatTensor :: v -+> (v ⊗ Scalar v)
  fromFlatTensor :: (v ⊗ Scalar v) -+> v
  addTensors :: (LSpace w, Scalar w ~ Scalar v)
                => (v ⊗ w) -> (v ⊗ w) -> v ⊗ w
  subtractTensors :: (LSpace v, LSpace w, Num''' (Scalar v), Scalar w ~ Scalar v)
                => (v ⊗ w) -> (v ⊗ w) -> v ⊗ w
  subtractTensors m n = addTensors m (negateTensor $ n)
  scaleTensor :: (LSpace w, Scalar w ~ Scalar v)
                => Bilinear (Scalar v) (v ⊗ w) (v ⊗ w)
  negateTensor :: (LSpace w, Scalar w ~ Scalar v)
                => (v ⊗ w) -+> (v ⊗ w)
  tensorProduct :: (LSpace w, Scalar w ~ Scalar v)
                => Bilinear v w (v ⊗ w)
  transposeTensor :: (LSpace w, Scalar w ~ Scalar v)
                => (v ⊗ w) -+> (w ⊗ v)
  coerceFmapTensorProduct :: Hask.Functor p
       => p v -> Coercion a b -> Coercion (TensorProduct v a) (TensorProduct v b)

(⊗) :: (LSpace v, LSpace w, Scalar w ~ Scalar v)
                => v -> w -> v ⊗ w
v⊗w = (tensorProduct $ v) $ w

-- | The class of vector spaces which implement linear maps. Alternatively,
--   this can be considered as the class of spaces with a properly tractable
--   <https://en.wikipedia.org/wiki/Dual_space dual space>.
class ( TensorSpace v, TensorSpace (DualVector v)
      , Num' (Scalar v), Scalar (DualVector v) ~ Scalar v )
              => LinearSpace v where
  -- | Internal representation of a linear map from the space @v@ to its field.
  --   For array-of-numbers Hilbert spaces, this will generally be just
  --   an “row vector”
  -- 
  --   Only use the 'DualVector' type and the methods below for /instantiating/ 
  --   this class. For actually /working/ with dual vectors, use 'DualSpace'.
  type DualVector v :: *
 
  linearId :: v +> v
  
  idTensor :: LSpace v => v ⊗ DualVector v
  idTensor = transposeTensor $ asTensor $ linearId
  
  sampleLinearFunction :: (LSpace v, LSpace w, Scalar v ~ Scalar w)
                             => (v-+>w) -+> (v+>w)
  sampleLinearFunction = LinearFunction $ \f -> fmap f $ id
  
  coerceDoubleDual :: Coercion v (DualVector (DualVector v))
  
  linearCoFst :: (LSpace v, LSpace w, Num''' (Scalar v), Scalar w ~ Scalar v)
                => v +> (v,w)
  linearCoFst = sampleLinearFunction $ id &&& const0
  linearCoSnd :: (LSpace v, LSpace w, Num''' (Scalar v), Scalar w ~ Scalar v)
                => v +> (w,v)
  linearCoSnd = sampleLinearFunction $ const0 &&& id
  
  fstBlock :: ( LSpace w, LSpace x, LSpace v, Num''' (Scalar v)
              , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
     => (v+>(w,x)) -+> (v+>w)
  fstBlock = fmap fst
  sndBlock :: ( LSpace w, LSpace x, LSpace v, Num''' (Scalar v)
              , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
     => (v+>(w,x)) -+> (v+>x)
  sndBlock = fmap snd
  sepBlocks :: ( LSpace w, LSpace x, LSpace v, Num''' (Scalar v)
               , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
     => (v+>(w,x)) -+> (v+>w, v+>x)
  sepBlocks = fstBlock &&& sndBlock
  fanoutBlocks :: ( LSpace w, LSpace x
                  , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
     => (v+>w, v+>x) -+> (v+>(w,x))
  firstBlock :: ( LSpace v, LSpace w, LSpace x
                , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
     => (v+>w) -+> (v+>(w,x))
  firstBlock = fanoutBlocks . (id &&& const0)
  secondBlock :: ( LSpace v, LSpace w, LSpace x
                 , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
           => (v+>x) -+> (v+>(w,x))
  secondBlock = fanoutBlocks . (const0 &&& id)
  
  blockVectSpan :: (LSpace w, Scalar w ~ Scalar v)
           => w -+> (v⊗(v+>w))
  blockVectSpan' :: (LSpace v, LSpace w, Num''' (Scalar v), Scalar v ~ Scalar w)
                  => w -+> (v+>(v⊗w))
  blockVectSpan' = LinearFunction $ \w -> fmap (flipBilin tensorProduct $ w) $ id
  
  fmapTensor :: (LSpace w, LSpace x, Scalar w ~ Scalar v, Scalar x ~ Scalar v)
           => Bilinear (w -+> x) (v⊗w) (v⊗x)
  
  contractTensor :: (LSpace w, Scalar w ~ Scalar v)
           => (v+>(v⊗w)) -+> w
  contractTensor' :: (LSpace w, Scalar w ~ Scalar v)
           => (v⊗(v+>w)) -+> w
  applyLinear :: (LSpace w, Scalar w ~ Scalar v)
                => Bilinear (v+>w) v w
  composeLinear :: ( LSpace w, LSpace x
                   , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
           => Bilinear (w+>x) (v+>w) (v+>x)


instance Num''' s => TensorSpace (ZeroDim s) where
  type TensorProduct (ZeroDim s) v = ZeroDim s
  zeroTensor = Tensor Origin
  toFlatTensor = LinearFunction $ \Origin -> Tensor Origin
  fromFlatTensor = LinearFunction $ \(Tensor Origin) -> Origin
  negateTensor = const0
  scaleTensor = biConst0
  addTensors (Tensor Origin) (Tensor Origin) = Tensor Origin
  subtractTensors (Tensor Origin) (Tensor Origin) = Tensor Origin
  tensorProduct = biConst0
  transposeTensor = const0
  coerceFmapTensorProduct _ Coercion = Coercion
instance Num''' s => LinearSpace (ZeroDim s) where
  type DualVector (ZeroDim s) = ZeroDim s
  linearId = LinearMap Origin
  idTensor = Tensor Origin
  coerceDoubleDual = Coercion
  linearCoFst = LinearMap Origin
  linearCoSnd = LinearMap Origin
  fstBlock = const0
  sndBlock = const0
  fanoutBlocks = const0
  firstBlock = const0
  secondBlock = const0
  fmapTensor = biConst0
  contractTensor = const0
  contractTensor' = const0
  blockVectSpan = const0
  applyLinear = biConst0
  composeLinear = biConst0


-- | The cartesian monoidal category of vector spaces over the field @s@
--   with linear maps as morphisms. This category is in maths called
--   <https://en.wikipedia.org/wiki/Category_of_modules#Example:_the_category_of_vector_spaces VectK>.
-- 
--   The common matrix operations are given by:
-- 
--   * Identity matrix: 'Control.Category.Constrained.id'.
--   * Matrix addition: 'Data.AdditiveGroup.^+^' (linear maps form an ordinary vector space).
--   * Matrix-matrix multiplication: 'Control.Category.Constrained..'.
--   * Matrix-vector multiplication: 'Control.Arrow.Constrained.$'.
--   * Vertical matrix concatenation: 'Control.Arrow.Constrained.&&&'.
--   * Horizontal matrix concatenation: '⊕', aka '>+<'.
newtype LinearMap s v w = LinearMap {getLinearMap :: TensorProduct (DualVector v) w}

newtype Tensor s v w = Tensor {getTensorProduct :: TensorProduct v w}

asTensor :: Coercion (LinearMap s v w) (Tensor s (DualVector v) w)
asTensor = Coercion
fromTensor :: Coercion (Tensor s (DualVector v) w) (LinearMap s v w)
fromTensor = Coercion

asLinearMap :: ∀ s v w . (LSpace v, Scalar v ~ s)
           => Coercion (Tensor s v w) (LinearMap s (DualVector v) w)
asLinearMap = Coercion
fromLinearMap :: ∀ s v w . (LSpace v, Scalar v ~ s)
           => Coercion (LinearMap s (DualVector v) w) (Tensor s v w)
fromLinearMap = Coercion

-- | Infix synonym for 'LinearMap', without explicit mention of the scalar type.
type v +> w = LinearMap (Scalar v) v w

-- | Infix synonym for 'Tensor', without explicit mention of the scalar type.
type v ⊗ w = Tensor (Scalar v) v w

type LSpace' v = ( LinearSpace v, LinearSpace (Scalar v)
                , LinearSpace (DualVector v), DualVector (DualVector v) ~ v )
type LSpace v = (LSpace' v, Num''' (Scalar v))

instance (LSpace v, LSpace w, Scalar v~s, Scalar w~s)
               => AdditiveGroup (LinearMap s v w) where
  zeroV = fromTensor $ zeroTensor
  m^+^n = fromTensor $ (asTensor$m) ^+^ (asTensor$n)
  m^-^n = fromTensor $ (asTensor$m) ^-^ (asTensor$n)
  negateV = (fromTensor$) . negateV . (asTensor$)
instance (LSpace v, LSpace w, Scalar v~s, Scalar w~s)
               => VectorSpace (LinearMap s v w) where
  type Scalar (LinearMap s v w) = s
  (*^) μ = undefined -- (fromTensor$) . scaleTensor μ . (asTensor$)
instance Num (LinearMap ℝ ℝ ℝ) where
  fromInteger = LinearMap . fromInteger
  (+) = (^+^)
  (-) = (^-^)
  LinearMap m * LinearMap n
         = LinearMap $ m*n
  abs (LinearMap n) = LinearMap $ abs n
  signum (LinearMap n) = LinearMap $ signum n
instance Fractional (LinearMap ℝ ℝ ℝ) where
  fromRational = LinearMap . fromRational
  LinearMap m / LinearMap n
         = LinearMap $ m/n
  recip (LinearMap n) = LinearMap $ recip n

instance (LSpace v, LSpace w, Scalar v~s, Scalar w~s)
               => AdditiveGroup (Tensor s v w) where
  zeroV = zeroTensor
  (^+^) = addTensors
  (^-^) = subtractTensors
  negateV = arr negateTensor
instance (LSpace v, LSpace w, Scalar v~s, Scalar w~s)
               => VectorSpace (Tensor s v w) where
  type Scalar (Tensor s v w) = s
  μ*^t = (scaleTensor $ μ) $ t
  
infixl 7 ⊗

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

instance Show (LinearMap ℝ ℝ ℝ) where
  showsPrec p (LinearMap n) = showsPrec p n
instance ∀ u v . (Show (LinearMap ℝ u ℝ), Show (LinearMap ℝ v ℝ))
           => Show (LinearMap ℝ (u,v) ℝ) where
  showsPrec p (LinearMap ((Tensor m, Tensor n)))
        = showParen (p>6)
            (showsPrec 6 (LinearMap m :: LinearMap ℝ u ℝ)
                         . ("⊕"++) . showsPrec 7 (LinearMap n :: LinearMap ℝ v ℝ))
instance ∀ s u v w . ( Num''' s, LSpace u, LSpace v, LSpace w
                     , Scalar u ~ s, Scalar v ~ s, Scalar w ~ s
                     , Show (LinearMap s u v), Show (LinearMap s u w) )
           => Show (LinearMap s u (v,w)) where
  showsPrec p m
        = showParen (p>6)
            (showsPrec 6 mv . (" &&& "++) . showsPrec 6 mw)
   where (mv, mw) = sepBlocks $ m

instance Category (LinearMap s) where
  type Object (LinearMap s) v = (LSpace v, Scalar v ~ s)
  id = linearId
  (.) = arr . arr composeLinear
instance Num''' s => Cartesian (LinearMap s) where
  type UnitObject (LinearMap s) = ZeroDim s
  swap = linearCoSnd ⊕ linearCoFst
  attachUnit = linearCoFst
  detachUnit = fst
  regroup = linearCoFst . linearCoFst ⊕ (linearCoFst . linearCoSnd ⊕ linearCoSnd)
  regroup' = (linearCoFst ⊕ linearCoSnd . linearCoFst) ⊕ linearCoSnd . linearCoSnd
instance Num''' s => Morphism (LinearMap s) where
  f *** g = (firstBlock$f) ⊕ (secondBlock$g)
instance Num''' s => PreArrow (LinearMap s) where
  (&&&) = curry $ arr fanoutBlocks
  terminal = zeroV
  fst = lfstBlock $ id
  snd = lsndBlock $ id
instance Num''' s => EnhancedCat (->) (LinearMap s) where
  arr m = arr $ applyLinear $ m
instance Num''' s => EnhancedCat (LinearFunction s) (LinearMap s) where
  arr m = applyLinear $ m

type ℝ = Double

instance TensorSpace ℝ where
  type TensorProduct ℝ w = w
  zeroTensor = Tensor zeroV
  scaleTensor = LinearFunction (pretendLike Tensor) . scale
  addTensors (Tensor v) (Tensor w) = Tensor $ v ^+^ w
  subtractTensors (Tensor v) (Tensor w) = Tensor $ v ^-^ w
  negateTensor = pretendLike Tensor lNegateV
  toFlatTensor = follow Tensor
  fromFlatTensor = flout Tensor
  tensorProduct = LinearFunction $ \μ -> follow Tensor . scaleWith μ
  transposeTensor = toFlatTensor . flout Tensor
  coerceFmapTensorProduct _ Coercion = Coercion
instance LinearSpace ℝ where
  type DualVector ℝ = ℝ
  linearId = LinearMap 1
  idTensor = Tensor 1
  coerceDoubleDual = Coercion
  linearCoFst = LinearMap (1, zeroV)
  linearCoSnd = LinearMap (zeroV, 1)
  fanoutBlocks = follow LinearMap . (flout LinearMap***flout LinearMap)
  fmapTensor = LinearFunction $ pretendLike Tensor
  contractTensor = flout Tensor . flout LinearMap
  contractTensor' = flout LinearMap . flout Tensor
  blockVectSpan = follow Tensor . follow LinearMap
  applyLinear = elacs . flout LinearMap
  composeLinear = LinearFunction $ \f -> follow LinearMap . arr f . flout LinearMap

#define FreeLinearSpace(V, LV, tp, tpl, bspan, tenspl, dspan, contraction)                                  \
instance Num''' s => TensorSpace (V s) where {                     \
  type TensorProduct (V s) w = V w;                               \
  zeroTensor = Tensor $ pure zeroV;                                \
  addTensors (Tensor m) (Tensor n) = Tensor $ liftA2 (^+^) m n;     \
  subtractTensors (Tensor m) (Tensor n) = Tensor $ liftA2 (^-^) m n; \
  negateTensor = LinearFunction $ Tensor . fmap negateV . getTensorProduct;  \
  scaleTensor = bilinearFunction   \
          $ \μ -> Tensor . fmap (μ*^) . getTensorProduct; \
  toFlatTensor = follow Tensor; \
  fromFlatTensor = flout Tensor; \
  tensorProduct = bilinearFunction $ \w v -> Tensor $ fmap (*^v) w; \
  transposeTensor = LinearFunction (tp); \
  coerceFmapTensorProduct _ Coercion = Coercion };                  \
instance Num''' s => LinearSpace (V s) where {                  \
  type DualVector (V s) = V s;                                 \
  linearId = LV Mat.identity;                                   \
  idTensor = Tensor Mat.identity; \
  coerceDoubleDual = Coercion; \
  linearCoFst = LV $ fmap (,zeroV) Mat.identity;                 \
  linearCoSnd = LV $ fmap (zeroV,) Mat.identity;                  \
  fanoutBlocks = LinearFunction $ LinearMap  \
       . uncurry (liftA2 (,)) . (getLinearMap***getLinearMap); \
  blockVectSpan = LinearFunction $ Tensor . (bspan);            \
  fmapTensor = bilinearFunction $       \
          \(LinearFunction f) -> pretendLike Tensor $ fmap f; \
  contractTensor = LinearFunction $ (contraction) . coerce . getLinearMap;      \
  contractTensor' = LinearFunction $ (contraction) . coerce . getTensorProduct;      \
  applyLinear = bilinearFunction $ \(LV m)                        \
                  -> foldl' (^+^) zeroV . liftA2 (^*) m;           \
  composeLinear = bilinearFunction $   \
         \f (LinearMap g) -> LinearMap $ fmap (f$) g }
FreeLinearSpace( V0
               , LinearMap
               , \(Tensor V0) -> zeroV
               , V0
               , \_ -> V0
               , \_ -> LinearMap V0
               , LinearMap V0
               , \V0 -> zeroV )
FreeLinearSpace( V1
               , LinearMap
               , \(Tensor (V1 w₀)) -> w₀⊗V1 1
               , V1 undefined
               , \w -> V1 (LinearMap $ V1 w)
               , \w -> LinearMap $ V1 (Tensor $ V1 w)
               , LinearMap . V1 . blockVectSpan $ V1 1
               , \(V1 (V1 w)) -> w )
FreeLinearSpace( V2
               , LinearMap
               , \(Tensor (V2 w₀ w₁)) -> w₀⊗V2 1 0
                                     ^+^ w₁⊗V2 0 1
               , V2 undefined undefined
               , \w -> V2 (LinearMap $ V2 w zeroV)
                          (LinearMap $ V2 zeroV w)
               , \w -> LinearMap $ V2 (Tensor $ V2 w zeroV)
                                      (Tensor $ V2 zeroV w)
               , LinearMap $ V2 (blockVectSpan $ V2 1 0)
                                (blockVectSpan $ V2 0 1)
               , \(V2 (V2 w₀ _)
                      (V2 _ w₁)) -> w₀^+^w₁ )
FreeLinearSpace( V3
               , LinearMap
               , \(Tensor (V3 w₀ w₁ w₂)) -> w₀⊗V3 1 0 0
                                        ^+^ w₁⊗V3 0 1 0
                                        ^+^ w₂⊗V3 0 0 1
               , V3 undefined undefined undefined
               , \w -> V3 (LinearMap $ V3 w zeroV zeroV)
                          (LinearMap $ V3 zeroV w zeroV)
                          (LinearMap $ V3 zeroV zeroV w)
               , \w -> LinearMap $ V3 (Tensor $ V3 w zeroV zeroV)
                                      (Tensor $ V3 zeroV w zeroV)
                                      (Tensor $ V3 zeroV zeroV w)
               , LinearMap $ V3 (blockVectSpan $ V3 1 0 0)
                                (blockVectSpan $ V3 0 1 0)
                                (blockVectSpan $ V3 0 0 1)
               , \(V3 (V3 w₀ _ _)
                      (V3 _ w₁ _)
                      (V3 _ _ w₂)) -> w₀^+^w₁^+^w₂ )
FreeLinearSpace( V4
               , LinearMap
               , \(Tensor (V4 w₀ w₁ w₂ w₃)) -> w₀⊗V4 1 0 0 0
                                           ^+^ w₁⊗V4 0 1 0 0
                                           ^+^ w₂⊗V4 0 0 1 0
                                           ^+^ w₃⊗V4 0 0 0 1
               , V4 undefined undefined undefined undefined
               , \w -> V4 (LinearMap $ V4 w zeroV zeroV zeroV)
                          (LinearMap $ V4 zeroV w zeroV zeroV)
                          (LinearMap $ V4 zeroV zeroV w zeroV)
                          (LinearMap $ V4 zeroV zeroV zeroV w)
               , \w -> LinearMap $ V4 (Tensor $ V4 w zeroV zeroV zeroV)
                                      (Tensor $ V4 zeroV w zeroV zeroV)
                                      (Tensor $ V4 zeroV zeroV w zeroV)
                                      (Tensor $ V4 zeroV zeroV zeroV w)
               , LinearMap $ V4 (blockVectSpan $ V4 1 0 0 0)
                                (blockVectSpan $ V4 0 1 0 0)
                                (blockVectSpan $ V4 0 0 1 0)
                                (blockVectSpan $ V4 0 0 0 1)
               , \(V4 (V4 w₀ _ _ _)
                      (V4 _ w₁ _ _)
                      (V4 _ _ w₂ _)
                      (V4 _ _ _ w₃)) -> w₀^+^w₁^+^w₂^+^w₃ )




  
instance ∀ u v . ( Num''' (Scalar v), LSpace u, LSpace v, Scalar u ~ Scalar v )
                       => TensorSpace (u,v) where
  type TensorProduct (u,v) w = (u⊗w, v⊗w)
  zeroTensor = zeroTensor <⊕ zeroTensor
  scaleTensor = scaleTensor&&&scaleTensor >>> LinearFunction (
                        uncurry (***) >>> pretendLike Tensor )
  negateTensor = pretendLike Tensor $ negateTensor *** negateTensor
  addTensors (Tensor (fu, fv)) (Tensor (fu', fv')) = (fu ^+^ fu') <⊕ (fv ^+^ fv')
  subtractTensors (Tensor (fu, fv)) (Tensor (fu', fv'))
          = (fu ^-^ fu') <⊕ (fv ^-^ fv')
  toFlatTensor = follow Tensor <<< toFlatTensor *** toFlatTensor
  fromFlatTensor = flout Tensor >>> fromFlatTensor *** fromFlatTensor
  tensorProduct = LinearFunction $ \(u,v) ->
                    (tensorProduct$u) &&& (tensorProduct$v) >>> follow Tensor
  -- transposeTensor (Tensor (fu, fv)) = fmapTensor linearCoFst (transposeTensor fu)
  --                                ^+^ fmapTensor linearCoSnd (transposeTensor fv)
  transposeTensor = flout Tensor >>> transposeTensor *** transposeTensor >>> fzip
  coerceFmapTensorProduct p cab = case
             ( coerceFmapTensorProduct (fst<$>p) cab
             , coerceFmapTensorProduct (snd<$>p) cab ) of
          (Coercion, Coercion) -> Coercion
instance ∀ u v . ( LinearSpace u, LinearSpace (DualVector u), DualVector (DualVector u) ~ u
                 , LinearSpace v, LinearSpace (DualVector v), DualVector (DualVector v) ~ v
                 , Scalar u ~ Scalar v, Num''' (Scalar u) )
                       => LinearSpace (u,v) where
  type DualVector (u,v) = (DualVector u, DualVector v)
  linearId = linearCoFst ⊕ linearCoSnd
  -- idTensor = fmapTensor linearCoFst idTensor <⊕ fmapTensor linearCoSnd idTensor
  sampleLinearFunction = LinearFunction $ \f -> (sampleLinearFunction $ f . lCoFst)
                                              ⊕ (sampleLinearFunction $ f . lCoSnd)
  coerceDoubleDual = Coercion
  linearCoFst = linearCoFst.linearCoFst ⊕ linearCoFst.linearCoSnd
  linearCoSnd = linearCoSnd.linearCoFst ⊕ linearCoSnd.linearCoSnd
  sepBlocks = LinearFunction $ \(LinearMap (fu, fv)) ->
                 let (fuw,fux) = sepBlocks $ asLinearMap $ fu
                     (fvw,fvx) = sepBlocks $ asLinearMap $ fv
                 in (fuw ⊕ fvw, fux ⊕ fvx)
  fanoutBlocks = LinearFunction $ \(LinearMap (fu, fv), LinearMap (gu, gv))
             -> (fanoutBlocks $ (asLinearMap $ fu, asLinearMap $ gu))
                ⊕ (fanoutBlocks $ (asLinearMap $ fv, asLinearMap $ gv))
  firstBlock = LinearFunction $ \(LinearMap (fu, fv))
          -> (firstBlock $ asLinearMap $ fu) ⊕ (firstBlock $ asLinearMap $ fv)
  secondBlock = LinearFunction $ \(LinearMap (fu, fv))
          -> (secondBlock $ asLinearMap $ fu) ⊕ (secondBlock $ asLinearMap $ fv)
  fmapTensor = LinearFunction $ \f -> pretendLike Tensor $ (fmapTensor$f) *** (fmapTensor$f)
  blockVectSpan = (blockVectSpan >>> fmap lfstBlock) &&& (blockVectSpan >>> fmap lsndBlock)
                     >>> follow Tensor
  contractTensor = flout LinearMap
               >>>  contractTensor . fmap (fst . flout Tensor) . arr fromTensor
                 ***contractTensor . fmap (snd . flout Tensor) . arr fromTensor
               >>> addV
  contractTensor' = flout Tensor
               >>>  contractTensor' . fmap (arr fromTensor . fst . flout LinearMap)
                 ***contractTensor' . fmap (arr fromTensor . snd . flout LinearMap)
               >>> addV
  applyLinear = LinearFunction $ \(LinearMap (fu, fv)) ->
           (applyLinear $ (asLinearMap $ fu)) *** (applyLinear $ (asLinearMap $ fv))
             >>> addV
  composeLinear = bilinearFunction $ \f (LinearMap (fu, fv))
                    -> f . (asLinearMap $ fu) ⊕ f . (asLinearMap $ fv)

lfstBlock :: ( LSpace u, LSpace v, LSpace w
             , Scalar u ~ Scalar v, Scalar v ~ Scalar w )
          => (u+>w) -+> ((u,v)+>w)
lfstBlock = LinearFunction (⊕zeroV)
lsndBlock :: ( LSpace u, LSpace v, LSpace w
            , Scalar u ~ Scalar v, Scalar v ~ Scalar w )
          => (v+>w) -+> ((u,v)+>w)
lsndBlock = LinearFunction (zeroV⊕)


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

instance ∀ s u v . ( Num''' s, LSpace u, LSpace v, Scalar u ~ s, Scalar v ~ s )
                       => TensorSpace (LinearMap s u v) where
  type TensorProduct (LinearMap s u v) w = TensorProduct (DualVector u) (Tensor s v w)
  zeroTensor = deferLinearMap $ zeroV
  toFlatTensor = arr deferLinearMap . fmap toFlatTensor
  fromFlatTensor = fmap fromFlatTensor . arr hasteLinearMap
  addTensors t₁ t₂ = deferLinearMap $ (hasteLinearMap$t₁) ^+^ (hasteLinearMap$t₂)
  subtractTensors t₁ t₂ = deferLinearMap $ (hasteLinearMap$t₁) ^-^ (hasteLinearMap$t₂)
  scaleTensor = LinearFunction $ \μ -> arr deferLinearMap . scaleWith μ . arr hasteLinearMap
  negateTensor = arr deferLinearMap . lNegateV . arr hasteLinearMap
  transposeTensor                -- t :: (u +> v) ⊗ w
            = arr hasteLinearMap     --  u +> (v ⊗ w)
          >>> fmap transposeTensor   --  u +> (w ⊗ v)
          >>> arr asTensor           --  u' ⊗ (w ⊗ v)
          >>> transposeTensor        --  (w ⊗ v) ⊗ u'
          >>> arr rassocTensor       --  w ⊗ (v ⊗ u')
          >>> fmap transposeTensor   --  w ⊗ (u' ⊗ v)
          >>> arr (fmap fromTensor)  --  w ⊗ (u +> v)
  tensorProduct = LinearFunction $ \t -> arr deferLinearMap
        . (flipBilin composeLinear $ t) . blockVectSpan'
  coerceFmapTensorProduct = cftlp
   where cftlp :: ∀ a b p . p (LinearMap s u v) -> Coercion a b
                   -> Coercion (TensorProduct (DualVector u) (Tensor s v a))
                               (TensorProduct (DualVector u) (Tensor s v b))
         cftlp _ c = coerceFmapTensorProduct ([]::[DualVector u])
                                             (fmap c :: Coercion (v⊗a) (v⊗b))

-- | @((u+>v)+>w) -> v+>(u⊗w)@
coCurryLinearMap :: Coercion (LinearMap s (LinearMap s u v) w) (LinearMap s v (Tensor s u w))
coCurryLinearMap = Coercion

-- | @(u+>(v⊗w)) -> (v+>u)+>w@
coUncurryLinearMap :: Coercion (LinearMap s u (Tensor s v w)) (LinearMap s (LinearMap s v u) w)
coUncurryLinearMap = Coercion

curryLinearMap :: (Num''' s, LSpace u, Scalar u ~ s)
           => Coercion (LinearMap s (Tensor s u v) w) (LinearMap s u (LinearMap s v w))
curryLinearMap = fmap fromTensor . fromTensor . rassocTensor . asTensor

uncurryLinearMap :: (Num''' s, LSpace u, Scalar u ~ s)
           => Coercion (LinearMap s u (LinearMap s v w)) (LinearMap s (Tensor s u v) w)
uncurryLinearMap = fromTensor . lassocTensor . asTensor . fmap asTensor

instance ∀ s u v . (Num''' s, LSpace u, LSpace v, Scalar u ~ s, Scalar v ~ s)
                       => LinearSpace (LinearMap s u v) where
  type DualVector (LinearMap s u v) = LinearMap s v u
  linearId = coUncurryLinearMap $ fmap blockVectSpan $ id
  coerceDoubleDual = Coercion
  fanoutBlocks = arr coUncurryLinearMap <<< fzipWith fzip
               <<< arr coCurryLinearMap *** arr coCurryLinearMap
  blockVectSpan = arr deferLinearMap
                    . fmap (arr (fmap coUncurryLinearMap) . blockVectSpan)
                               . blockVectSpan'
  applyLinear = bilinearFunction $ \f g -> contractTensor $ (coCurryLinearMap$f) . g
  fmapTensor = LinearFunction $ \f
                -> arr deferLinearMap <<< fmap (fmap f) <<< arr hasteLinearMap
  composeLinear = bilinearFunction $ \f g
        -> coUncurryLinearMap $ fmap (fmap $ applyLinear $ f) $ (coCurryLinearMap$g)
  contractTensor = contractTensor . fmap (contractTensor' . arr (fmap hasteLinearMap))
                       . arr coCurryLinearMap
  contractTensor' = contractTensor . fmap (contractTensor' . arr (fmap coCurryLinearMap))
                       . arr hasteLinearMap

instance ∀ s u v . (Num''' s, LSpace u, LSpace v, Scalar u ~ s, Scalar v ~ s)
                       => TensorSpace (Tensor s u v) where
  type TensorProduct (Tensor s u v) w = TensorProduct u (Tensor s v w)
  zeroTensor = lassocTensor $ zeroTensor
  toFlatTensor = arr lassocTensor . fmap toFlatTensor
  fromFlatTensor = fmap fromFlatTensor . arr rassocTensor
  addTensors t₁ t₂ = lassocTensor $ (rassocTensor$t₁) ^+^ (rassocTensor$t₂)
  subtractTensors t₁ t₂ = lassocTensor $ (rassocTensor$t₁) ^-^ (rassocTensor$t₂)
  scaleTensor = LinearFunction $ \μ -> arr lassocTensor . scaleWith μ . arr rassocTensor
  negateTensor = arr lassocTensor . lNegateV . arr rassocTensor
  tensorProduct = flipBilin $ LinearFunction $ \w
             -> arr lassocTensor . fmap (flipBilin tensorProduct $ w)
  transposeTensor = fmap transposeTensor . arr rassocTensor
                       . transposeTensor . fmap transposeTensor . arr rassocTensor
  coerceFmapTensorProduct = cftlp
   where cftlp :: ∀ a b p . p (Tensor s u v) -> Coercion a b
                   -> Coercion (TensorProduct u (Tensor s v a))
                               (TensorProduct u (Tensor s v b))
         cftlp _ c = coerceFmapTensorProduct ([]::[u])
                                             (fmap c :: Coercion (v⊗a) (v⊗b))
instance ∀ s u v . (Num''' s, LSpace u, LSpace v, Scalar u ~ s, Scalar v ~ s)
                       => LinearSpace (Tensor s u v) where
  type DualVector (Tensor s u v) = Tensor s (DualVector u) (DualVector v)
  linearId = uncurryLinearMap $ fmap (fmap transposeTensor . blockVectSpan') $ id
  coerceDoubleDual = Coercion
  fanoutBlocks = arr uncurryLinearMap <<< fzipWith fzip
               <<< arr curryLinearMap *** arr curryLinearMap
  blockVectSpan = arr lassocTensor . arr (fmap $ fmap uncurryLinearMap)
           . fmap (transposeTensor . arr deferLinearMap) . blockVectSpan
                   . arr deferLinearMap . fmap transposeTensor . blockVectSpan'
  applyLinear = LinearFunction $ \f -> contractTensor'
                     . fmap (applyLinear$curryLinearMap$f) . transposeTensor
  fmapTensor = LinearFunction $ \f
                -> arr lassocTensor <<< fmap (fmap f) <<< arr rassocTensor
  composeLinear = bilinearFunction $ \f g
        -> uncurryLinearMap $ fmap (fmap $ applyLinear $ f) $ (curryLinearMap$g)
  contractTensor = contractTensor
      . fmap (transposeTensor . contractTensor
                 . fmap (arr rassocTensor . transposeTensor . arr rassocTensor))
                       . arr curryLinearMap
  contractTensor' = contractTensor . fmap transposeTensor . contractTensor'
                 . fmap (arr (curryLinearMap . hasteLinearMap) . transposeTensor)
                       . arr rassocTensor



type DualSpace v = v+>Scalar v

type Fractional' s = (Fractional s, Eq s, VectorSpace s, Scalar s ~ s)
type Fractional'' s = (Fractional' s, LSpace s)

-- | 'SemiInner' is the class of vector spaces with finite subspaces in which
--   you can define a basis that can be used to project from the whole space
--   into the subspace. The usual application is for using a kind of
--   <https://en.wikipedia.org/wiki/Galerkin_method Galerkin method> to
--   give an approximate solution (see '\$') to a linear equation in a possibly
--   infinite-dimensional space.
-- 
--   Of course, this also works for spaces which are already finite-dimensional themselves.
class (LinearSpace v, LinearSpace (Scalar v)) => SemiInner v where
  -- | Lazily enumerate choices of a basis of functionals that can be made dual
  --   to the given vectors, in order of preference (which roughly means, large in
  --   the normal direction.) I.e., if the vector @𝑣@ is assigned early to the
  --   dual vector @𝑣'@, then @(𝑣' $ 𝑣)@ should be large and all the other products
  --   comparably small.
  -- 
  --   The purpose is that we should be able to make this basis orthonormal
  --   with a ~Gaussian-elimination approach, in a way that stays numerically
  --   stable. This is otherwise known as the /choice of a pivot element/.
  -- 
  --   For simple finite-dimensional array-vectors, you can easily define this
  --   method using 'cartesianDualBasisCandidates'.
  dualBasisCandidates :: [(Int,v)] -> Forest (Int, v +> Scalar v)

cartesianDualBasisCandidates
     :: [v+>Scalar v]   -- ^ Set of canonical basis functionals.
     -> (v -> [ℝ])      -- ^ Decompose a vector in /absolute value/ components.
                        --   the list indices should correspond to those in
                        --   the functional list.
     -> ([(Int,v)] -> Forest (Int, v +> Scalar v))
                        -- ^ Suitable definition of 'dualBasisCandidates'.
cartesianDualBasisCandidates dvs abss vcas = go 0 sorted
 where sorted = sortBy (comparing $ negate . snd . snd)
                       [ (i, (av, maximum av)) | (i,v)<-vcas, let av = abss v ]
       go k ((i,(av,_)):scs)
          | k<n   = Node (i, dv) (go (k+1) [(i',(zeroAt j av',m)) | (i',(av',m))<-scs])
                                : go k scs
        where (j,_) = maximumBy (comparing snd) $ zip jfus av
              dv = dvs !! j
       go _ _ = []
       
       jfus = [0 .. n-1]
       n = length dvs
       
       zeroAt :: Int -> [ℝ] -> [ℝ]
       zeroAt _ [] = []
       zeroAt 0 (_:l) = (-1/0):l
       zeroAt j (e:l) = e : zeroAt (j-1) l

instance (Fractional'' s, SemiInner s) => SemiInner (ZeroDim s) where
  dualBasisCandidates _ = []
instance (Fractional'' s, SemiInner s) => SemiInner (V0 s) where
  dualBasisCandidates _ = []

orthonormaliseDuals :: (SemiInner v, LSpace v, Fractional'' (Scalar v))
                          => [(v, DualSpace v)] -> [(v,DualSpace v)]
orthonormaliseDuals [] = []
orthonormaliseDuals ((v,v'₀):ws) = (v,v') : [(w, w' ^-^ (w'$v)*^v') | (w,w')<-wssys]
 where wssys = orthonormaliseDuals ws
       v'₁ = foldl' (\v'i (w,w') -> v'i ^-^ (v'i$w)*^w') v'₀ wssys
       v' = v'₁ ^/ (v'₁$v)

dualBasis :: (SemiInner v, LSpace v, Fractional'' (Scalar v)) => [v] -> [DualSpace v]
dualBasis vs = snd <$> orthonormaliseDuals (zip' vsIxed candidates)
 where zip' ((i,v):vs) ((j,v'):ds)
        | i<j   = zip' vs ((j,v'):ds)
        | i==j  = (v,v') : zip' vs ds
       zip' _ _ = []
       candidates = sortBy (comparing fst) . findBest
                             $ dualBasisCandidates vsIxed
        where findBest [] = []
              findBest (Node iv' bv' : _) = iv' : findBest bv'
       vsIxed = zip [0..] vs

instance SemiInner ℝ where
  dualBasisCandidates = fmap ((`Node`[]) . second (LinearMap . recip))
                . sortBy (comparing $ negate . abs . snd)
                . filter ((/=0) . snd)

instance (Fractional'' s, Ord s, SemiInner s) => SemiInner (V1 s) where
  dualBasisCandidates = fmap ((`Node`[]) . second (LinearMap . recip))
                . sortBy (comparing $ negate . abs . snd)
                . filter ((/=0) . snd)

#define FreeSemiInner(V, sabs) \
instance SemiInner (V) where {      \
  dualBasisCandidates                \
     = cartesianDualBasisCandidates (LinearMap <$> Mat.basis) (fmap sabs . toList) }
FreeSemiInner(V2 ℝ, abs)
FreeSemiInner(V3 ℝ, abs)
FreeSemiInner(V4 ℝ, abs)

instance ( SemiInner u, LSpace u, SemiInner v, LSpace v
         , LSpace (Scalar v), Scalar u ~ Scalar v
         ) => SemiInner (u,v) where
  dualBasisCandidates = fmap (\(i,(u,v))->((i,u),(i,v))) >>> unzip
              >>> dualBasisCandidates *** dualBasisCandidates
              >>> combineBaseis False mempty
   where combineBaseis _ _ ([], []) = []
         combineBaseis False forbidden (Node (i,du) bu' : abu, bv)
            | i`Set.member`forbidden  = combineBaseis False forbidden (abu, bv)
            | otherwise
                 = Node (i, lfstBlock $ du)
                        (combineBaseis True (Set.insert i forbidden) (bu', bv))
                       : combineBaseis False forbidden (abu, bv)
         combineBaseis True forbidden (bu, Node (i,dv) bv' : abv)
            | i`Set.member`forbidden  = combineBaseis True forbidden (bu, abv)
            | otherwise
                 = Node (i, lsndBlock $ dv)
                        (combineBaseis False (Set.insert i forbidden) (bu, bv'))
                       : combineBaseis True forbidden (bu, abv)
         combineBaseis _ forbidden (bu, []) = combineBaseis False forbidden (bu,[])
         combineBaseis _ forbidden ([], bv) = combineBaseis True forbidden ([],bv)
  
(^/^) :: (InnerSpace v, Eq (Scalar v), Fractional (Scalar v)) => v -> v -> Scalar v
v^/^w = case (v<.>w) of
   0 -> 0
   vw -> vw / (w<.>w)

class (LSpace v, LSpace (Scalar v)) => FiniteDimensional v where
  -- | Whereas 'Basis'-values refer to a single basis vector, a single
  --   'EntireBasis' value represents a complete collection of such basis vectors,
  --   which can be used to associate a vector with a list of coefficients.
  -- 
  --   For spaces with a canonical finite basis, 'EntireBasis' does not actually
  --   need to contain any information, since all vectors will anyway be represented in
  --   that same basis.
  data EntireBasis v :: *
  
  -- | Split up a linear map in “column vectors” WRT some suitable basis.
  decomposeLinMap :: (v+>w) -> (EntireBasis v, [w]->[w])
  
  recomposeEntire :: EntireBasis v -> [Scalar v] -> (v, [Scalar v])
  
  recomposeContraLinMap :: (LinearSpace w, Scalar w ~ Scalar v, Hask.Functor f)
           => (f (Scalar w) -> w) -> f (DualSpace v) -> v+>w
  


instance (Num''' s) => FiniteDimensional (ZeroDim s) where
  data EntireBasis (ZeroDim s) = ZeroBasis
  recomposeEntire ZeroBasis l = (Origin, l)
  decomposeLinMap _ = (ZeroBasis, id)
  recomposeContraLinMap _ _ = LinearMap Origin
  
instance (Num''' s, LinearSpace s) => FiniteDimensional (V0 s) where
  data EntireBasis (V0 s) = V0Basis
  recomposeEntire V0Basis l = (V0, l)
  decomposeLinMap _ = (V0Basis, id)
  recomposeContraLinMap _ _ = LinearMap V0
  
instance FiniteDimensional ℝ where
  data EntireBasis ℝ = RealsBasis
  recomposeEntire RealsBasis [] = (0, [])
  recomposeEntire RealsBasis (μ:cs) = (μ, cs)
  decomposeLinMap (LinearMap v) = (RealsBasis, (v:))
  recomposeContraLinMap fw = LinearMap . fw . fmap ($1)

#define FreeFiniteDimensional(V, VB, take, give)          \
instance (Num''' s, LSpace s)                              \
            => FiniteDimensional (V s) where {              \
  data EntireBasis (V s) = VB;                               \
  recomposeEntire _ (take:cs) = (give, cs);                   \
  recomposeEntire b cs = recomposeEntire b $ cs ++ [0];        \
  decomposeLinMap (LinearMap m) = (VB, (toList m ++));          \
  recomposeContraLinMap fw mv = LinearMap $ (\v -> fw $ fmap ($v) mv) <$> Mat.identity }
FreeFiniteDimensional(V1, V1Basis, c₀         , V1 c₀         )
FreeFiniteDimensional(V2, V2Basis, c₀:c₁      , V2 c₀ c₁      )
FreeFiniteDimensional(V3, V3Basis, c₀:c₁:c₂   , V3 c₀ c₁ c₂   )
FreeFiniteDimensional(V4, V4Basis, c₀:c₁:c₂:c₃, V4 c₀ c₁ c₂ c₃)
                                  
deriving instance Show (EntireBasis ℝ)
  
instance ( FiniteDimensional u, LinearSpace (DualVector u), DualVector (DualVector u) ~ u
         , FiniteDimensional v, LinearSpace (DualVector v), DualVector (DualVector v) ~ v
         , Scalar u ~ Scalar v, Fractional' (Scalar v) )
            => FiniteDimensional (u,v) where
  data EntireBasis (u,v) = TupleBasis !(EntireBasis u) !(EntireBasis v)
  decomposeLinMap (LinearMap (fu, fv))
       = case (decomposeLinMap (asLinearMap$fu), decomposeLinMap (asLinearMap$fv)) of
         ((bu, du), (bv, dv)) -> (TupleBasis bu bv, du . dv)
  recomposeEntire (TupleBasis bu bv) coefs = case recomposeEntire bu coefs of
                        (u, coefs') -> case recomposeEntire bv coefs' of
                         (v, coefs'') -> ((u,v), coefs'')
  recomposeContraLinMap fw dds
         = recomposeContraLinMap fw 
               (fmap (\(LinearMap (v', _)) -> asLinearMap $ v') dds)
          ⊕ recomposeContraLinMap fw
               (fmap (\(LinearMap (_, v')) -> asLinearMap $ v') dds)
  
deriving instance (Show (EntireBasis u), Show (EntireBasis v))
                    => Show (EntireBasis (u,v))

infixr 0 \$

-- | Inverse function application, in the sense of providing a
--   /least-squares-error/ solution to a linear equation system.
-- 
--   If you want to solve for multiple RHS vectors, be sure to partially
--   apply this operator to the matrix element.
(\$) :: ( FiniteDimensional u, FiniteDimensional v, SemiInner v
        , Scalar u ~ Scalar v, Fractional' (Scalar v) )
          => (u+>v) -> v -> u
(\$) m = fst . \v -> recomposeEntire mbas [v' $ v | v' <- v's]
 where v's = dualBasis $ mdecomp []
       (mbas, mdecomp) = decomposeLinMap m
    

pseudoInverse :: ( FiniteDimensional u, FiniteDimensional v, SemiInner v
                 , Scalar u ~ Scalar v, Fractional' (Scalar v) )
          => (u+>v) -> v+>u
pseudoInverse m = recomposeContraLinMap (fst . recomposeEntire mbas) v's
 where v's = dualBasis $ mdecomp []
       (mbas, mdecomp) = decomposeLinMap m


-- | The <https://en.wikipedia.org/wiki/Riesz_representation_theorem Riesz representation theorem>
--   provides an isomorphism between a Hilbert space and its (continuous) dual space.
riesz :: (FiniteDimensional v, InnerSpace v) => DualSpace v -+> v
riesz = LinearFunction $ \dv ->
       let (bas, compos) = decomposeLinMap dv
       in fst . recomposeEntire bas $ compos []

coRiesz :: (LSpace v, Num''' (Scalar v), InnerSpace v) => v -+> DualSpace v
coRiesz = sampleLinearFunction . inner

-- | Functions are generally a pain to display, but since linear functionals
--   in a Hilbert space can be represented by /vectors/ in that space,
--   this can be used for implementing a 'Show' instance.
showsPrecAsRiesz :: (FiniteDimensional v, InnerSpace v, Show v)
                      => Int -> DualSpace v -> ShowS
showsPrecAsRiesz p dv = showParen (p>0) $ ("coRiesz$"++) . showsPrec 10 (riesz$dv)

instance Show (LinearMap ℝ (V0 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V1 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V2 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V3 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V4 ℝ) ℝ) where showsPrec = showsPrecAsRiesz


infixl 7 .<

-- | Outer product of a general @v@-vector and a basis element from @w@.
--   Note that this operation is in general pretty inefficient; it is
--   provided mostly to lay out matrix definitions neatly.
(.<) :: ( FiniteDimensional v, Num''' (Scalar v)
        , InnerSpace v, LSpace w, HasBasis w, Scalar v ~ Scalar w )
           => Basis w -> v -> v+>w
bw .< v = sampleLinearFunction $ LinearFunction $ \v' -> recompose [(bw, v<.>v')]

instance Show (LinearMap s v (V0 s)) where
  show _ = "zeroV"
instance (FiniteDimensional v, InnerSpace v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V1 ℝ)) where
  showsPrec p m = showParen (p>6) $ ("ex ×< "++)
                       . showsPrec 7 (riesz $ (coRiesz$(V1 1)) . m)
instance (FiniteDimensional v, InnerSpace v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V2 ℝ)) where
  showsPrec p m = showParen (p>6)
              $ ("ex.<"++) . showsPrec 7 (riesz $ (coRiesz$V2 1 0) . m)
         . (" ^+^ ey.<"++) . showsPrec 7 (riesz $ (coRiesz$V2 0 1) . m)
instance (FiniteDimensional v, InnerSpace v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V3 ℝ)) where
  showsPrec p m = showParen (p>6)
              $ ("ex.<"++) . showsPrec 7 (riesz $ (coRiesz$V3 1 0 0) . m)
         . (" ^+^ ey.<"++) . showsPrec 7 (riesz $ (coRiesz$V3 0 1 0) . m)
         . (" ^+^ ez.<"++) . showsPrec 7 (riesz $ (coRiesz$V3 0 0 1) . m)
instance (FiniteDimensional v, InnerSpace v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V4 ℝ)) where
  showsPrec p m = showParen (p>6)
              $ ("ex.<"++) . showsPrec 7 (riesz $ (coRiesz$V4 1 0 0 0) . m)
         . (" ^+^ ey.<"++) . showsPrec 7 (riesz $ (coRiesz$V4 0 1 0 0) . m)
         . (" ^+^ ez.<"++) . showsPrec 7 (riesz $ (coRiesz$V4 0 0 1 0) . m)
         . (" ^+^ ew.<"++) . showsPrec 7 (riesz $ (coRiesz$V4 0 0 0 1) . m)


instance (Num''' s, LSpace v, Scalar v ~ s)
            => Functor (Tensor s v) (LinearFunction s) (LinearFunction s) where
  fmap f = fmapTensor $ f
instance (Num''' s, LSpace v, Scalar v ~ s)
            => Monoidal (Tensor s v) (LinearFunction s) (LinearFunction s) where

instance (Num''' s, LSpace v, Scalar v ~ s)
            => Functor (LinearMap s v) (LinearFunction s) (LinearFunction s) where
--   fmap = composeLinear
instance (Num''' s, LSpace v, Scalar v ~ s)
            => Monoidal (LinearMap s v) (LinearFunction s) (LinearFunction s) where

instance (Num''' s, TensorSpace v, Scalar v ~ s)
            => Functor (Tensor s v) Coercion Coercion where
  fmap = crcFmap
   where crcFmap :: ∀ s v a b . (TensorSpace v, Scalar v ~ s)
              => Coercion a b -> Coercion (Tensor s v a) (Tensor s v b)
         crcFmap f = case coerceFmapTensorProduct ([]::[v]) f of
                       Coercion -> Coercion

instance (LSpace v, Num''' s, Scalar v ~ s)
            => Functor (LinearMap s v) Coercion Coercion where
  fmap = crcFmap
   where crcFmap :: ∀ s v a b . (LSpace v, Num''' s, Scalar v ~ s)
              => Coercion a b -> Coercion (LinearMap s v a) (LinearMap s v b)
         crcFmap f = case coerceFmapTensorProduct ([]::[DualVector v]) f of
                       Coercion -> Coercion

instance Category (LinearFunction s) where
  type Object (LinearFunction s) v = (LSpace v, Scalar v ~ s)
  id = LinearFunction id
  LinearFunction f . LinearFunction g = LinearFunction $ f.g
instance Num''' s => Cartesian (LinearFunction s) where
  type UnitObject (LinearFunction s) = ZeroDim s
  swap = LinearFunction swap
  attachUnit = LinearFunction (, Origin)
  detachUnit = LinearFunction fst
  regroup = LinearFunction regroup
  regroup' = LinearFunction regroup'
instance Num''' s => Morphism (LinearFunction s) where
  LinearFunction f***LinearFunction g = LinearFunction $ f***g
instance Num''' s => PreArrow (LinearFunction s) where
  LinearFunction f&&&LinearFunction g = LinearFunction $ f&&&g
  fst = LinearFunction fst; snd = LinearFunction snd
  terminal = const0
instance EnhancedCat (->) (LinearFunction s) where
  arr = getLinearFunction
instance EnhancedCat (LinearFunction s) Coercion where
  arr = LinearFunction . coerceWith

instance (LSpace w, Scalar w ~ s)
     => Functor (LinearFunction s w) (LinearFunction s) (LinearFunction s) where
  fmap f = LinearFunction (f.)


instance (LSpace u, LSpace v, Scalar u ~ s, Scalar v ~ s)
     => TensorSpace (LinearFunction s u v) where
  type TensorProduct (LinearFunction s u v) w = LinearFunction s u (Tensor s v w)

instance (LSpace u, LSpace v, Scalar u ~ s, Scalar v ~ s)
     => LinearSpace (LinearFunction s u v) where
  type DualVector (LinearFunction s u v) = LinearFunction s v u


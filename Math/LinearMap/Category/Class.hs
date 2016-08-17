-- |
-- Module      : Math.LinearMap.Category.Class
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

module Math.LinearMap.Category.Class where

import Data.VectorSpace

import Prelude ()
import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.Coerce
import Data.Type.Coercion

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
  fmapTensor :: (LSpace w, LSpace x, Scalar w ~ Scalar v, Scalar x ~ Scalar v)
           => Bilinear (w -+> x) (v⊗w) (v⊗x)
  fzipTensorWith :: ( LSpace u, LSpace w, LSpace x
                    , Scalar u ~ Scalar v, Scalar w ~ Scalar v, Scalar x ~ Scalar v )
           => Bilinear ((w,x) -+> u) (v⊗w, v⊗x) (v⊗u)
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
  
  toLinearForm :: LSpace v => DualVector v -+> (v+>Scalar v)
  toLinearForm = toFlatTensor >>> arr fromTensor
  
  fromLinearForm :: LSpace v => (v+>Scalar v) -+> DualVector v
  fromLinearForm = arr asTensor >>> fromFlatTensor
  
  coerceDoubleDual :: Coercion v (DualVector (DualVector v))
  
  blockVectSpan :: (LSpace w, Scalar w ~ Scalar v)
           => w -+> (v⊗(v+>w))
  blockVectSpan' :: (LSpace v, LSpace w, Num''' (Scalar v), Scalar v ~ Scalar w)
                  => w -+> (v+>(v⊗w))
  blockVectSpan' = LinearFunction $ \w -> fmap (flipBilin tensorProduct $ w) $ id
  
  trace :: LSpace v => (v+>v) -+> Scalar v
  trace = flipBilin contractLinearMapAgainst $ id
  
  contractTensorMap :: (LSpace w, Scalar w ~ Scalar v)
           => (v+>(v⊗w)) -+> w
  contractMapTensor :: (LSpace w, Scalar w ~ Scalar v)
           => (v⊗(v+>w)) -+> w
  contractFnTensor :: (LSpace v, LSpace w, Scalar w ~ Scalar v)
           => (v⊗(v-+>w)) -+> w
  contractFnTensor = fmap sampleLinearFunction >>> contractMapTensor
  contractTensorFn :: (LSpace v, LSpace w, Scalar w ~ Scalar v)
           => (v-+>(v⊗w)) -+> w
  contractTensorFn = sampleLinearFunction >>> contractTensorMap
  contractTensorWith :: (LSpace v, LSpace w, Scalar w ~ Scalar v)
           => Bilinear (v⊗w) (DualVector w) v
  contractTensorWith = flipBilin $ LinearFunction
           (\dw -> fromFlatTensor . fmap (flipBilin applyDualVector$dw))
  contractLinearMapAgainst :: (LSpace w, Scalar w ~ Scalar v)
           => Bilinear (v+>w) (w-+>v) (Scalar v)
  
  applyDualVector :: LSpace v
                => Bilinear (DualVector v) v (Scalar v)
  
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
  fmapTensor = biConst0
  fzipTensorWith = biConst0
  coerceFmapTensorProduct _ Coercion = Coercion
instance Num''' s => LinearSpace (ZeroDim s) where
  type DualVector (ZeroDim s) = ZeroDim s
  linearId = LinearMap Origin
  idTensor = Tensor Origin
  fromLinearForm = const0
  coerceDoubleDual = Coercion
  contractTensorMap = const0
  contractMapTensor = const0
  contractTensorWith = biConst0
  contractLinearMapAgainst = biConst0
  blockVectSpan = const0
  applyDualVector = biConst0
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


instance Category (LinearMap s) where
  type Object (LinearMap s) v = (LSpace v, Scalar v ~ s)
  id = linearId
  (.) = arr . arr composeLinear
instance Num''' s => Cartesian (LinearMap s) where
  type UnitObject (LinearMap s) = ZeroDim s
  swap = (fmap (const0&&&id) $ id) ⊕ (fmap (id&&&const0) $ id)
  attachUnit = fmap (id&&&const0) $ id
  detachUnit = fst
  regroup = sampleLinearFunction $ LinearFunction regroup
  regroup' = sampleLinearFunction $ LinearFunction regroup'
instance Num''' s => Morphism (LinearMap s) where
  f *** g = (fmap (id&&&const0) $ f) ⊕ (fmap (const0&&&id) $ g)
instance Num''' s => PreArrow (LinearMap s) where
  f &&& g = fromTensor $ (fzipTensorWith$id) $ (asTensor $ f, asTensor $ g)
  terminal = zeroV
  fst = sampleLinearFunction $ fst
  snd = sampleLinearFunction $ snd
instance Num''' s => EnhancedCat (->) (LinearMap s) where
  arr m = arr $ applyLinear $ m
instance Num''' s => EnhancedCat (LinearFunction s) (LinearMap s) where
  arr m = applyLinear $ m





  
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
  transposeTensor = flout Tensor >>> transposeTensor *** transposeTensor >>> fzip
  fmapTensor = LinearFunction $
           \f -> pretendLike Tensor $ (fmapTensor$f) *** (fmapTensor$f)
  fzipTensorWith = bilinearFunction
               $ \f (Tensor (uw, vw), Tensor (ux, vx))
                      -> Tensor ( (fzipTensorWith$f)$(uw,ux)
                                , (fzipTensorWith$f)$(vw,vx) )
  coerceFmapTensorProduct p cab = case
             ( coerceFmapTensorProduct (fst<$>p) cab
             , coerceFmapTensorProduct (snd<$>p) cab ) of
          (Coercion, Coercion) -> Coercion
instance ∀ u v . ( LinearSpace u, LinearSpace (DualVector u), DualVector (DualVector u) ~ u
                 , LinearSpace v, LinearSpace (DualVector v), DualVector (DualVector v) ~ v
                 , Scalar u ~ Scalar v, Num''' (Scalar u) )
                       => LinearSpace (u,v) where
  type DualVector (u,v) = (DualVector u, DualVector v)
  linearId = (fmap (id&&&const0) $ id) ⊕ (fmap (const0&&&id) $ id)
  -- idTensor = fmapTensor linearCoFst idTensor <⊕ fmapTensor linearCoSnd idTensor
  sampleLinearFunction = LinearFunction $ \f -> (sampleLinearFunction $ f . lCoFst)
                                              ⊕ (sampleLinearFunction $ f . lCoSnd)
  coerceDoubleDual = Coercion
  blockVectSpan = (blockVectSpan >>> fmap lfstBlock) &&& (blockVectSpan >>> fmap lsndBlock)
                     >>> follow Tensor
  contractTensorMap = flout LinearMap
               >>>  contractTensorMap . fmap (fst . flout Tensor) . arr fromTensor
                 ***contractTensorMap . fmap (snd . flout Tensor) . arr fromTensor
               >>> addV
  contractMapTensor = flout Tensor
               >>>  contractMapTensor . fmap (arr fromTensor . fst . flout LinearMap)
                 ***contractMapTensor . fmap (arr fromTensor . snd . flout LinearMap)
               >>> addV
  contractTensorWith = LinearFunction $ \(Tensor (fu, fv))
                          -> (contractTensorWith$fu) &&& (contractTensorWith$fv)
  contractLinearMapAgainst = flout LinearMap >>> bilinearFunction
                     (\(mu,mv) f -> ((contractLinearMapAgainst$fromTensor$mu)$(fst.f))
                                  + ((contractLinearMapAgainst$fromTensor$mv)$(snd.f)) )
  applyDualVector = LinearFunction $ \(du,dv)
                      -> (applyDualVector$du) *** (applyDualVector$dv) >>> addV
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
  fmapTensor = LinearFunction $ \f
                -> arr deferLinearMap <<< fmap (fmap f) <<< arr hasteLinearMap
  fzipTensorWith = LinearFunction $ \f
                -> arr deferLinearMap <<< fzipWith (fzipWith f)
                     <<< arr hasteLinearMap *** arr hasteLinearMap
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

uncurryLinearFn :: ( Num''' s, LSpace u, LSpace v, LSpace w
                   , Scalar u ~ s, Scalar v ~ s, Scalar w ~ s )
           => LinearFunction s u (LinearMap s v w) -+> LinearFunction s (Tensor s u v) w
uncurryLinearFn = bilinearFunction
         $ \f t -> contractMapTensor . fmap f . transposeTensor $ t

instance ∀ s u v . (Num''' s, LSpace u, LSpace v, Scalar u ~ s, Scalar v ~ s)
                       => LinearSpace (LinearMap s u v) where
  type DualVector (LinearMap s u v) = LinearMap s v u
  linearId = coUncurryLinearMap $ fmap blockVectSpan $ id
  coerceDoubleDual = Coercion
  blockVectSpan = arr deferLinearMap
                    . fmap (arr (fmap coUncurryLinearMap) . blockVectSpan)
                               . blockVectSpan'
  applyLinear = bilinearFunction $ \f g -> contractTensorMap $ (coCurryLinearMap$f) . g
  applyDualVector = contractLinearMapAgainst >>> LinearFunction (. applyLinear)
  composeLinear = bilinearFunction $ \f g
        -> coUncurryLinearMap $ fmap (fmap $ applyLinear $ f) $ (coCurryLinearMap$g)
  contractTensorMap = contractTensorMap . fmap (contractMapTensor . arr (fmap hasteLinearMap))
                       . arr coCurryLinearMap
  contractMapTensor = contractTensorMap . fmap (contractMapTensor . arr (fmap coCurryLinearMap))
                       . arr hasteLinearMap
  contractTensorWith = arr hasteLinearMap >>> bilinearFunction (\l dw
                          -> fmap (flipBilin contractTensorWith $ dw) $ l )
  contractLinearMapAgainst = arr coCurryLinearMap >>> bilinearFunction (\l f
                          -> (contractLinearMapAgainst . fmap transposeTensor $ l)
                                . uncurryLinearFn $f )

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
  fmapTensor = LinearFunction $ \f
                -> arr lassocTensor <<< fmap (fmap f) <<< arr rassocTensor
  fzipTensorWith = LinearFunction $ \f
                -> arr lassocTensor <<< fzipWith (fzipWith f)
                     <<< arr rassocTensor *** arr rassocTensor
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
  blockVectSpan = arr lassocTensor . arr (fmap $ fmap uncurryLinearMap)
           . fmap (transposeTensor . arr deferLinearMap) . blockVectSpan
                   . arr deferLinearMap . fmap transposeTensor . blockVectSpan'
  applyLinear = LinearFunction $ \f -> contractMapTensor
                     . fmap (applyLinear$curryLinearMap$f) . transposeTensor
  applyDualVector = bilinearFunction $ \f t
                          -> (contractLinearMapAgainst $ (fromTensor$f))
                               . contractTensorWith $ t
  composeLinear = bilinearFunction $ \f g
        -> uncurryLinearMap $ fmap (fmap $ applyLinear $ f) $ (curryLinearMap$g)
  contractTensorMap = contractTensorMap
      . fmap (transposeTensor . contractTensorMap
                 . fmap (arr rassocTensor . transposeTensor . arr rassocTensor))
                       . arr curryLinearMap
  contractMapTensor = contractTensorMap . fmap transposeTensor . contractMapTensor
                 . fmap (arr (curryLinearMap . hasteLinearMap) . transposeTensor)
                       . arr rassocTensor
  contractTensorWith = arr rassocTensor >>> bilinearFunction (\l dw
                          -> fmap (flipBilin contractTensorWith $ dw) $ l )
  contractLinearMapAgainst = arr curryLinearMap >>> bilinearFunction (\l f
                          -> (contractLinearMapAgainst $ l)
                                $ contractTensorMap . fmap (transposeTensor . f) )



type DualSpace v = v+>Scalar v

type Fractional' s = (Fractional s, Eq s, VectorSpace s, Scalar s ~ s)
type Fractional'' s = (Fractional' s, LSpace s)



instance (Num''' s, LSpace v, Scalar v ~ s)
            => Functor (Tensor s v) (LinearFunction s) (LinearFunction s) where
  fmap f = fmapTensor $ f
instance (Num''' s, LSpace v, Scalar v ~ s)
            => Monoidal (Tensor s v) (LinearFunction s) (LinearFunction s) where
  pureUnit = const0
  fzipWith f = fzipTensorWith $ f

instance (Num''' s, LSpace v, Scalar v ~ s)
            => Functor (LinearMap s v) (LinearFunction s) (LinearFunction s) where
  fmap f = arr fromTensor . fmap f . arr asTensor
instance (Num''' s, LSpace v, Scalar v ~ s)
            => Monoidal (LinearMap s v) (LinearFunction s) (LinearFunction s) where
  pureUnit = const0
  fzipWith f = arr asTensor *** arr asTensor >>> fzipWith f >>> arr fromTensor

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


deferLinearFn :: Coercion (LinearFunction s u (Tensor s v w))
                          (Tensor s (LinearFunction s u v) w)
deferLinearFn = Coercion

hasteLinearFn :: Coercion (Tensor s (LinearFunction s u v) w)
                          (LinearFunction s u (Tensor s v w))
hasteLinearFn = Coercion


instance (LSpace u, LSpace v, Scalar u ~ s, Scalar v ~ s)
     => TensorSpace (LinearFunction s u v) where
  type TensorProduct (LinearFunction s u v) w = LinearFunction s u (Tensor s v w)
  zeroTensor = deferLinearFn $ const0
  toFlatTensor = arr deferLinearFn . fmap toFlatTensor
  fromFlatTensor = fmap fromFlatTensor . arr hasteLinearFn
  addTensors t s = deferLinearFn $ (hasteLinearFn$t)^+^(hasteLinearFn$s)
  subtractTensors t s = deferLinearFn $ (hasteLinearFn$t)^-^(hasteLinearFn$s)
  scaleTensor = LinearFunction $ \μ -> arr deferLinearFn . scaleWith μ . arr hasteLinearFn
  negateTensor = arr deferLinearFn . lNegateV . arr hasteLinearFn
  tensorProduct = flipBilin $ LinearFunction $
                   \w -> arr deferLinearFn . fmap (flipBilin tensorProduct $ w)
  transposeTensor = arr hasteLinearFn >>> LinearFunction tp
   where tp f = fmap (LinearFunction $ \dw -> (flipBilin contractTensorWith$dw) . f)
                          $ idTensor
  fmapTensor = bilinearFunction $ \f g
                -> deferLinearFn $ fmap f . (hasteLinearFn$g)
  fzipTensorWith = bilinearFunction $ \f (g,h)
                    -> deferLinearFn $ fzipWith f
                             <<< (hasteLinearFn$g)&&&(hasteLinearFn$h)
  coerceFmapTensorProduct = cftpLf
   where cftpLf :: ∀ s u v a b p . TensorSpace v
            => p (LinearFunction s u v) -> Coercion a b
                  -> Coercion (LinearFunction s u (Tensor s v a))
                              (LinearFunction s u (Tensor s v b))
         cftpLf p c = case coerceFmapTensorProduct ([]::[v]) c of
                        Coercion -> Coercion

coCurryLinearFn :: Coercion (LinearMap s (LinearFunction s u v) w)
                                  (LinearFunction s v (Tensor s u w))
coCurryLinearFn = Coercion

coUncurryLinearFn :: Coercion (LinearFunction s u (Tensor s v w))
                                    (LinearMap s (LinearFunction s v u) w)
coUncurryLinearFn = Coercion

instance (LSpace u, LSpace v, Scalar u ~ s, Scalar v ~ s)
     => LinearSpace (LinearFunction s u v) where
  type DualVector (LinearFunction s u v) = LinearFunction s v u
  linearId = coUncurryLinearFn $ LinearFunction $
                      \v -> fmap (fmap (scaleV v) . applyDualVector) $ idTensor
  coerceDoubleDual = Coercion
  blockVectSpan = arr deferLinearFn . bilinearFunction (\w u
                        -> fmap ( arr coUncurryLinearFn
                                 . fmap (flipBilin tensorProduct$w) . applyLinear )
                             $ (blockVectSpan$u) )
  contractTensorMap = arr coCurryLinearFn
                     >>> arr (fmap (fmap hasteLinearFn))
                     >>> sampleLinearFunction
                     >>> fmap contractFnTensor
                     >>> contractTensorMap
  contractMapTensor = arr hasteLinearFn
                     >>> arr (fmap (fmap coCurryLinearFn))
                     >>> sampleLinearFunction
                     >>> fmap contractFnTensor
                     >>> contractTensorMap
  contractLinearMapAgainst = arr coCurryLinearFn
                         >>> bilinearFunction (\v2uw w2uv
                           -> trace . fmap (contractTensorFn . fmap v2uw)
                               . sampleLinearFunction $ w2uv )
  applyDualVector = sampleLinearFunction >>> contractLinearMapAgainst
  applyLinear = arr coCurryLinearFn >>> LinearFunction (\f
                         -> contractTensorFn . fmap f)
  composeLinear = LinearFunction $ \f
         -> arr coCurryLinearFn >>> fmap (fmap $ applyLinear $ f)
        >>> arr coUncurryLinearFn


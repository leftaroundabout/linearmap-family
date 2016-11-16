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
{-# LANGUAGE GADTs                      #-}

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

data ClosedScalarWitness s where
  ClosedScalarWitness :: (Scalar s ~ s, DualVector s ~ s) => ClosedScalarWitness s

class (Num s, LinearSpace s) => Num' s where
  closedScalarWitness :: ClosedScalarWitness s

data ScalarSpaceWitness v where
  ScalarSpaceWitness :: (Num' (Scalar v), Scalar (Scalar v) ~ Scalar v)
                          => ScalarSpaceWitness v
  
class (VectorSpace v) => TensorSpace v where
  -- | The internal representation of a 'Tensor' product.
  -- 
  -- For euclidean spaces, this is generally constructed by replacing each @s@
  -- scalar field in the @v@ vector with an entire @w@ vector. I.e., you have
  -- then a “nested vector” or, if @v@ is a @DualVector@ / “row vector”, a matrix.
  type TensorProduct v w :: *
  scalarSpaceWitness :: ScalarSpaceWitness v
  zeroTensor :: (TensorSpace w, Scalar w ~ Scalar v)
                => v ⊗ w
  toFlatTensor :: v -+> (v ⊗ Scalar v)
  fromFlatTensor :: (v ⊗ Scalar v) -+> v
  addTensors :: (TensorSpace w, Scalar w ~ Scalar v)
                => (v ⊗ w) -> (v ⊗ w) -> v ⊗ w
  subtractTensors :: (TensorSpace v, TensorSpace w, Scalar w ~ Scalar v)
                => (v ⊗ w) -> (v ⊗ w) -> v ⊗ w
  subtractTensors m n = addTensors m (getLinearFunction negateTensor n)
  scaleTensor :: (TensorSpace w, Scalar w ~ Scalar v)
                => Bilinear (Scalar v) (v ⊗ w) (v ⊗ w)
  negateTensor :: (TensorSpace w, Scalar w ~ Scalar v)
                => (v ⊗ w) -+> (v ⊗ w)
  tensorProduct :: (TensorSpace w, Scalar w ~ Scalar v)
                => Bilinear v w (v ⊗ w)
  transposeTensor :: (TensorSpace w, Scalar w ~ Scalar v)
                => (v ⊗ w) -+> (w ⊗ v)
  fmapTensor :: (TensorSpace w, TensorSpace x, Scalar w ~ Scalar v, Scalar x ~ Scalar v)
           => Bilinear (w -+> x) (v⊗w) (v⊗x)
  fzipTensorWith :: ( TensorSpace u, TensorSpace w, TensorSpace x
                    , Scalar u ~ Scalar v, Scalar w ~ Scalar v, Scalar x ~ Scalar v )
           => Bilinear ((w,x) -+> u) (v⊗w, v⊗x) (v⊗u)
  coerceFmapTensorProduct :: Hask.Functor p
       => p v -> Coercion a b -> Coercion (TensorProduct v a) (TensorProduct v b)

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
  
  blockVectSpan :: (TensorSpace w, Scalar w ~ Scalar v)
           => w -+> (v⊗(v+>w))
  blockVectSpan' :: ∀ w . (TensorSpace w, Scalar v ~ Scalar w)
                  => w -+> (v+>(v⊗w))
  blockVectSpan' = case scalarSpaceWitness :: ScalarSpaceWitness v of
    ScalarSpaceWitness -> LinearFunction $ \w
              -> (fmapLinearMap-+$>flipBilin tensorProduct-+$>w)-+$>linearId
  
  trace :: (v+>v) -+> Scalar v
  trace = case scalarSpaceWitness :: ScalarSpaceWitness v of
      ScalarSpaceWitness -> flipBilin contractLinearMapAgainst-+$>id
  
  contractTensorMap :: (TensorSpace w, Scalar w ~ Scalar v)
           => (v+>(v⊗w)) -+> w
  contractMapTensor :: (TensorSpace w, Scalar w ~ Scalar v)
           => (v⊗(v+>w)) -+> w
  contractFnTensor :: (TensorSpace w, Scalar w ~ Scalar v)
           => (v⊗(v-+>w)) -+> w
  contractFnTensor = case ( scalarSpaceWitness :: ScalarSpaceWitness v
                          , dualSpaceWitness :: DualSpaceWitness v ) of
    (ScalarSpaceWitness, DualSpaceWitness)
        -> fmap sampleLinearFunction >>> contractMapTensor
  contractTensorFn :: ∀ w . (TensorSpace w, Scalar w ~ Scalar v)
           => (v-+>(v⊗w)) -+> w
  --contractTensorFn = case ( dualSpaceWitness :: DualSpaceWitness v
  --                        , dualSpaceWitness :: DualSpaceWitness w) of
  --             (DualSpaceWitness, DualSpaceWitness)
  --                 -> sampleLinearFunction >>> contractTensorMap
  contractTensorWith :: ∀ w . (LinearSpace w, Scalar w ~ Scalar v)
           => Bilinear (v⊗w) (DualVector w) v
  --contractTensorWith = case ( dualSpaceWitness :: DualSpaceWitness v
  --                          , dualSpaceWitness :: DualSpaceWitness w ) of
  --             (DualSpaceWitness,DualSpaceWitness) -> flipBilin $ LinearFunction
  --              (\dw -> fromFlatTensor . fmap (flipBilin applyDualVector$dw))
  contractLinearMapAgainst :: (LinearSpace w, Scalar w ~ Scalar v)
           => Bilinear (v+>w) (w-+>v) (Scalar v)
  
  applyDualVector :: LinearSpace v
                => Bilinear (DualVector v) v (Scalar v)
  
  applyLinear :: (TensorSpace w, Scalar w ~ Scalar v)
                => Bilinear (v+>w) v w
  composeLinear :: ( LinearSpace w, TensorSpace x
                   , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
           => Bilinear (w+>x) (v+>w) (v+>x)
  
  tensorId :: (LinearSpace w, Scalar w ~ Scalar v)
                 => (v⊗w)+>(v⊗w)
  
  applyTensorFunctional :: ( TensorSpace u, Scalar u ~ Scalar v )
               => Bilinear (DualVector (v⊗u)) (v⊗u) (Scalar v)
  
  applyTensorLinMap :: ( LinearSpace u, TensorSpace w
                       , Scalar u ~ Scalar v, Scalar w ~ Scalar v )
               => Bilinear ((v⊗u)+>w) (v⊗u) w 
  

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
  contractTensorWith = biConst0
  contractLinearMapAgainst = biConst0
  blockVectSpan = const0
  applyDualVector = biConst0
  applyLinear = biConst0
  applyTensorFunctional = biConst0
  applyTensorLinMap = biConst0
  composeLinear = biConst0


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
type LSpace v = ( LinearSpace v, LinearSpace (Scalar v), LinearSpace (DualVector v)
                , Num' (Scalar v) )

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
              -> LinearFunction $ \f -> (sampleLinearFunction $ f . lCoFst)
                                              ⊕ (sampleLinearFunction $ f . lCoSnd)
--blockVectSpan = case ( dualSpaceWitness :: DualSpaceWitness u
--                        , dualSpaceWitness :: DualSpaceWitness v ) of
--     (DualSpaceWitness, DualSpaceWitness)
--         -> (blockVectSpan >>> fmap lfstBlock) &&& (blockVectSpan >>> fmap lsndBlock)
--                   >>> follow Tensor
--contractTensorMap = flout LinearMap
--             >>>  contractTensorMap . fmap (fst . flout Tensor) . arr fromTensor
--               ***contractTensorMap . fmap (snd . flout Tensor) . arr fromTensor
--             >>> addV
--contractMapTensor = flout Tensor
--             >>>  contractMapTensor . fmap (arr fromTensor . fst . flout LinearMap)
--               ***contractMapTensor . fmap (arr fromTensor . snd . flout LinearMap)
--             >>> addV
--contractTensorWith = LinearFunction $ \(Tensor (fu, fv))
--                        -> (contractTensorWith$fu) &&& (contractTensorWith$fv)
--contractLinearMapAgainst = flout LinearMap >>> bilinearFunction
--                   (\(mu,mv) f -> ((contractLinearMapAgainst$fromTensor$mu)$(fst.f))
--                                + ((contractLinearMapAgainst$fromTensor$mv)$(snd.f)) )
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
           (applyLinear $ (asLinearMap $ fu)) *** (applyLinear $ (asLinearMap $ fv))
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
     (DualSpaceWitness, DualSpaceWitness) -> arr curryLinearMap >>> bilinearFunction`id`
               \(LinearMap (fu,fv)) (Tensor (tu,tv))
                   -> ( (applyTensorLinMap-+$>uncurryLinearMap.asLinearMap $ fu)-+$>tu )
                   ^+^ ( (applyTensorLinMap-+$>uncurryLinearMap.asLinearMap $ fv)-+$>tv )

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
       (ScalarSpaceWitness, ScalarSpaceWitness) -> ScalarSpaceWitness
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
  linearId = case dualSpaceWitness :: DualSpaceWitness u of
     DualSpaceWitness -> fromTensor . lassocTensor . fromLinearMap . fmap asTensor
                            . curryLinearMap . fmap fromTensor $ tensorId
  coerceDoubleDual = case dualSpaceWitness :: DualSpaceWitness v of
     DualSpaceWitness -> Coercion
--blockVectSpan = arr deferLinearMap
--                  . fmap (arr (fmap coUncurryLinearMap) . blockVectSpan)
--                             . blockVectSpan'
--applyLinear = case dualSpaceWitness :: DualSpaceWitness u of
--   DualSpaceWitness -> bilinearFunction $ \f g
--                -> contractTensorMap $ (coCurryLinearMap$f) . g
  applyDualVector = case dualSpaceWitness :: DualSpaceWitness v of
    DualSpaceWitness -> flipBilin applyTensorFunctional
--composeLinear = bilinearFunction $ \f g
--      -> coUncurryLinearMap $ fmap (fmap $ applyLinear $ f) $ (coCurryLinearMap$g)
--contractTensorWith = arr hasteLinearMap >>> bilinearFunction (\l dw
--                        -> fmap (flipBilin contractTensorWith $ dw) $ l )
--contractLinearMapAgainst = arr coCurryLinearMap >>> bilinearFunction (\l f
--                        -> (contractLinearMapAgainst . fmap transposeTensor $ l)
--                              . uncurryLinearFn $f )

instance ∀ s u v . (TensorSpace u, TensorSpace v, Scalar u ~ s, Scalar v ~ s)
                       => TensorSpace (Tensor s u v) where
  type TensorProduct (Tensor s u v) w = TensorProduct u (Tensor s v w)
  scalarSpaceWitness = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                            , scalarSpaceWitness :: ScalarSpaceWitness v ) of
       (ScalarSpaceWitness, ScalarSpaceWitness) -> ScalarSpaceWitness
  zeroTensor = lassocTensor $ zeroTensor
  --toFlatTensor = arr lassocTensor . fmap toFlatTensor
  --fromFlatTensor = fmap fromFlatTensor . arr rassocTensor
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
instance ∀ s u v . (LinearSpace u, LinearSpace v, Scalar u ~ s, Scalar v ~ s)
                       => LinearSpace (Tensor s u v) where
  type DualVector (Tensor s u v) = LinearMap s u (DualVector v)
  linearId = tensorId
  coerceDoubleDual = case ( dualSpaceWitness :: DualSpaceWitness u
                          , dualSpaceWitness :: DualSpaceWitness v ) of
    (DualSpaceWitness, DualSpaceWitness) -> Coercion
--blockVectSpan = arr lassocTensor . arr (fmap $ fmap uncurryLinearMap)
--         . fmap (transposeTensor . arr deferLinearMap) . blockVectSpan
--                 . arr deferLinearMap . fmap transposeTensor . blockVectSpan'
  applyLinear = applyTensorLinMap
  applyDualVector = applyTensorFunctional
  composeLinear = case scalarSpaceWitness :: ScalarSpaceWitness u of
    ScalarSpaceWitness -> bilinearFunction $ \f g
        -> uncurryLinearMap $ fmap (fmap $ applyLinear $ f) $ (curryLinearMap$g)
  contractTensorMap = case scalarSpaceWitness :: ScalarSpaceWitness u of
    ScalarSpaceWitness -> contractTensorMap
      . fmap (transposeTensor . contractTensorMap
                 . fmap (arr rassocTensor . transposeTensor . arr rassocTensor))
                       . arr curryLinearMap
  contractMapTensor = case scalarSpaceWitness :: ScalarSpaceWitness u of
    ScalarSpaceWitness -> contractTensorMap . fmap transposeTensor . contractMapTensor
                 . fmap (arr (curryLinearMap . hasteLinearMap) . transposeTensor)
                       . arr rassocTensor
--contractTensorWith = arr rassocTensor >>> bilinearFunction (\l dw
--                        -> fmap (flipBilin contractTensorWith $ dw) $ l )
--contractLinearMapAgainst = arr curryLinearMap >>> bilinearFunction (\l f
--                        -> (contractLinearMapAgainst $ l)
--                              $ contractTensorMap . fmap (transposeTensor . f) )



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


deferLinearFn :: Coercion (LinearFunction s u (Tensor s v w))
                          (Tensor s (LinearFunction s u v) w)
deferLinearFn = Coercion

hasteLinearFn :: Coercion (Tensor s (LinearFunction s u v) w)
                          (LinearFunction s u (Tensor s v w))
hasteLinearFn = Coercion


instance ∀ s u v . (LinearSpace u, TensorSpace v, Scalar u ~ s, Scalar v ~ s)
     => TensorSpace (LinearFunction s u v) where
  type TensorProduct (LinearFunction s u v) w = LinearFunction s u (Tensor s v w)
  scalarSpaceWitness = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                            , scalarSpaceWitness :: ScalarSpaceWitness v ) of
       (ScalarSpaceWitness, ScalarSpaceWitness) -> ScalarSpaceWitness
  zeroTensor = deferLinearFn $ const0
  --toFlatTensor = arr deferLinearFn . fmap toFlatTensor
  --fromFlatTensor = fmap fromFlatTensor . arr hasteLinearFn
  addTensors t s = deferLinearFn $ (hasteLinearFn$t)^+^(hasteLinearFn$s)
  subtractTensors t s = deferLinearFn $ (hasteLinearFn$t)^-^(hasteLinearFn$s)
  scaleTensor = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                     , dualSpaceWitness :: DualSpaceWitness u ) of
     (ScalarSpaceWitness, DualSpaceWitness) -> 
        LinearFunction $ \μ -> arr deferLinearFn . scaleWith μ . arr hasteLinearFn
  negateTensor = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                     , dualSpaceWitness :: DualSpaceWitness u ) of
     (ScalarSpaceWitness, DualSpaceWitness) -> 
        arr deferLinearFn . lNegateV . arr hasteLinearFn
  tensorProduct = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                     , dualSpaceWitness :: DualSpaceWitness u ) of
     (ScalarSpaceWitness, DualSpaceWitness) -> 
        flipBilin $ LinearFunction $
                   \w -> arr deferLinearFn . fmap (flipBilin tensorProduct-+$>w)
  transposeTensor = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                         , dualSpaceWitness :: DualSpaceWitness u ) of
      (ScalarSpaceWitness, DualSpaceWitness)
          -> LinearFunction $ \(Tensor f)
                     -> fmap (applyLinear . arr asLinearMap . transposeTensor)
                      -+$> rassocTensor
                        $ transposeTensor . fmap transposeTensor
                      -+$> asTensor $ sampleLinearFunction-+$>f
                  --(LinearFunction $ \dw -> (flipBilin contractTensorWith-+$>dw)
                   --                    . (hasteLinearFn$f)))
                   -- )    -+$> idTensor
  fmapTensor = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                         , dualSpaceWitness :: DualSpaceWitness u ) of
      (ScalarSpaceWitness, DualSpaceWitness)
          -> bilinearFunction $ \f g
                -> deferLinearFn $ fmap f . (hasteLinearFn$g)
  fzipTensorWith = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                         , dualSpaceWitness :: DualSpaceWitness u ) of
      (ScalarSpaceWitness, DualSpaceWitness)
          -> bilinearFunction $ \f (g,h)
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

instance (LinearSpace u, LinearSpace v, Scalar u ~ s, Scalar v ~ s)
     => LinearSpace (LinearFunction s u v) where
  type DualVector (LinearFunction s u v) = LinearFunction s v u
  linearId = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                  , dualSpaceWitness :: DualSpaceWitness u ) of
     (ScalarSpaceWitness, DualSpaceWitness)
          -> coUncurryLinearFn $ LinearFunction $
                      \v -> fmap (fmap (scaleV v) . applyDualVector) $ idTensor
  coerceDoubleDual = Coercion
  blockVectSpan = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                       , dualSpaceWitness :: DualSpaceWitness u ) of
    (ScalarSpaceWitness, DualSpaceWitness)
           -> arr deferLinearFn . bilinearFunction (\w u
                        -> fmap ( arr coUncurryLinearFn
                                 . fmap (flipBilin tensorProduct$w) . applyLinear )
                             $ (blockVectSpan$u) )
  contractTensorMap = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                           , dualSpaceWitness :: DualSpaceWitness u ) of
    (ScalarSpaceWitness, DualSpaceWitness)
                 -> arr coCurryLinearFn
                     >>> arr (fmap (fmap hasteLinearFn))
                     >>> sampleLinearFunction
                     >>> fmap contractFnTensor
                     >>> contractTensorMap
  contractMapTensor = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                           , dualSpaceWitness :: DualSpaceWitness u ) of
    (ScalarSpaceWitness, DualSpaceWitness)
                 -> arr hasteLinearFn
                     >>> arr (fmap (fmap coCurryLinearFn))
                     >>> sampleLinearFunction
                     >>> fmap contractFnTensor
                     >>> contractTensorMap
--contractLinearMapAgainst = arr coCurryLinearFn
--                       >>> bilinearFunction (\v2uw w2uv
--                         -> trace . fmap (contractTensorFn . fmap v2uw)
--                             . sampleLinearFunction $ w2uv )
  applyDualVector = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                           , dualSpaceWitness :: DualSpaceWitness u ) of
    (ScalarSpaceWitness, DualSpaceWitness)
                 -> sampleLinearFunction >>> contractLinearMapAgainst
  applyLinear = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                           , dualSpaceWitness :: DualSpaceWitness u ) of
    (ScalarSpaceWitness, DualSpaceWitness)
                 -> arr coCurryLinearFn >>> LinearFunction (\f
                         -> contractTensorFn . fmap f)
  composeLinear = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                           , dualSpaceWitness :: DualSpaceWitness u ) of
    (ScalarSpaceWitness, DualSpaceWitness)
                 -> LinearFunction $ \f
         -> arr coCurryLinearFn >>> fmap (fmap $ applyLinear $ f)
        >>> arr coUncurryLinearFn


{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE CPP                    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE UnicodeSyntax          #-}
{-# LANGUAGE NoStarIsType           #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Numeric.LinearAlgebra.Static.Orphans () where

-- base
import Prelude hiding (id, (.), ($))
import GHC.TypeLits (KnownNat, natVal)
import GHC.Stack (HasCallStack)
import Data.Proxy (Proxy(..))
import Data.Maybe (fromJust)
import Control.Arrow ((***))
import Data.Type.Coercion (Coercion(..))
import Control.Monad.ST

-- constrained-categories
import Control.Category.Constrained (id, (.))
import Control.Arrow.Constrained (($))

-- singletons
import Data.Singletons (sing)
#if MIN_VERSION_singletons(3,0,0)
import Prelude.Singletons (SNum(..))
import GHC.TypeLits.Singletons (withKnownNat)
#else
import Data.Singletons.Prelude.Num (SNum(..))
import Data.Singletons.TypeLits (withKnownNat)
#endif

-- hmatrix
import Numeric.LinearAlgebra.Static as HMatS
import qualified Numeric.LinearAlgebra as HMat
import qualified Numeric.LinearAlgebra.Data as HMat

-- vector
import qualified Data.Vector as ArB
import qualified Data.Vector.Unboxed as ArU
import qualified Data.Vector.Storable as ArS
import qualified Data.Vector.Generic as ArG
import qualified Data.Vector.Generic.Mutable as ArGM

-- vector-space
import Data.AdditiveGroup
import Data.VectorSpace
import Data.AffineSpace

-- free-vector-spaces
import Data.VectorSpace.Free

-- linearmap-category
import Math.LinearMap.Category
import Math.LinearMap.Coercion (fromLinearMap, fromTensor, (-+$=>))
import Math.VectorSpace.DimensionAware
-- import Math.VectorSpace.DimensionAware.Theorems.MaybeNat (zipWithTimesSing)

-- tagged
#if !MIN_VERSION_manifolds_core(0,6,0)
import Data.Tagged (Tagged(..))
#endif

--------------------------------------------------
-- * @vector-space@ instances

instance KnownNat n => AdditiveGroup (R n) where
  zeroV = 0
  (^+^) = (+)
  negateV x = -x

instance KnownNat n => VectorSpace (R n) where
  type Scalar (R n) = ℝ
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

instance KnownNat n => DimensionAware (R n) where
  type StaticDimension (R n) = 'Just n
  dimensionalityWitness = IsStaticDimensional

instance ∀ n . KnownNat n => n`Dimensional`R n where
  unsafeFromArrayWithOffset i ar
      = unsafeCreate . ArG.convert
               $ ArG.unsafeSlice i (fromIntegral $ natVal @n Proxy) ar
  unsafeWriteArrayWithOffset ar i v
     = ArG.unsafeCopy (ArGM.unsafeSlice i (fromIntegral $ natVal @n Proxy) ar)
                   . ArG.convert $ extract v

instance KnownNat n => Semimanifold (R n) where
  type Needle (R n) = R n
#if !MIN_VERSION_manifolds_core(0,6,0)
  type Interior (R n) = R n
  toInterior = pure
  fromInterior = id
  translateP = Tagged (^+^)
#endif
  (.+~^) = (^+^)

instance KnownNat n => PseudoAffine (R n) where
  (.-~!) = (-)
  v .-~. w = Just (v - w)

type family RTensorProduct n w dw where
  RTensorProduct n w ('Just m) = L m n
  RTensorProduct n w 'Nothing
     = ArB.Vector w  -- ^ If the dimensionality is not fixed, store the columns as a
                     --   boxed array. This can be ragged (for whatever notion of
                     --   “length” may be applicable in the space @w@), but the length
                     --   of the array should always be exactly @n@.

unsafeCreate :: ∀ n . (KnownNat n, HasCallStack) => ArS.Vector ℝ -> R n
unsafeCreate = fromJust . create

unsafeCreateMat :: ∀ n m . (KnownNat n, KnownNat m, HasCallStack)
                     => HMat.Matrix ℝ -> L n m
unsafeCreateMat = fromJust . create

unsafeFromRows :: ∀ m n . (KnownNat m, KnownNat n, HasCallStack) => [R n] -> L m n
unsafeFromRows rs = withRows rs  -- unsafeCoerce
                                (fromJust . exactDims)

unsafeFromCols :: ∀ m n . (KnownNat m, KnownNat n, HasCallStack) => [R n] -> L m n
unsafeFromCols rs = withColumns rs  -- unsafeCoerce
                                  (fromJust . exactDims)

instance ∀ n . KnownNat n => TensorSpace (R n) where
  type TensorProduct (R n) w = RTensorProduct n w (StaticDimension w)
  scalarSpaceWitness = ScalarSpaceWitness
  linearManifoldWitness = LinearManifoldWitness
  zeroTensor :: ∀ w . TensorSpace w => R n ⊗ w
  zeroTensor = case dimensionality @w of
     StaticDimensionalCase -> Tensor $ konst 0
     FlexibleDimensionalCase -> Tensor $ ArB.replicate (fromIntegral $ natVal @n Proxy)
                                                     zeroV
  addTensors :: ∀ w . TensorSpace w => (R n ⊗ w) -> (R n ⊗ w) -> (R n ⊗ w)
  addTensors = case dimensionality @w of
     StaticDimensionalCase -> \(Tensor a) (Tensor b) -> Tensor $ a + b
     FlexibleDimensionalCase -> \(Tensor a) (Tensor b) -> Tensor $ ArB.zipWith (^+^) a b
  subtractTensors :: ∀ w . TensorSpace w => (R n ⊗ w) -> (R n ⊗ w) -> (R n ⊗ w)
  subtractTensors = case dimensionality @w of
     StaticDimensionalCase -> \(Tensor a) (Tensor b) -> Tensor $ a - b
     FlexibleDimensionalCase -> \(Tensor a) (Tensor b) -> Tensor $ ArB.zipWith (^-^) a b
  negateTensor :: ∀ w . TensorSpace w => (R n ⊗ w) -+> (R n ⊗ w)
  negateTensor = case dimensionality @w of
     StaticDimensionalCase -> LinearFunction $ \(Tensor a) -> Tensor $ -a
     FlexibleDimensionalCase -> LinearFunction $ \(Tensor a) -> Tensor $ ArB.map negateV a
  scaleTensor :: ∀ w . (TensorSpace w, Scalar w ~ ℝ)
                  => Bilinear ℝ (R n ⊗ w) (R n ⊗ w)
  scaleTensor = case dimensionality @w of
     StaticDimensionalCase -> bilinearFunction $ \μ (Tensor a) -> Tensor $ dmmap (μ*) a
     FlexibleDimensionalCase -> bilinearFunction $ \μ (Tensor a) -> Tensor $ ArB.map (μ*^) a
  toFlatTensor = LinearFunction $ \v -> Tensor $ row v
  fromFlatTensor = LinearFunction $ \(Tensor t) -> unrow t
  tensorProduct :: ∀ w . (TensorSpace w, Scalar w ~ ℝ) => Bilinear (R n) w (R n ⊗ w)
  tensorProduct = case dimensionality @w of
     StaticDimensionalCase -> bilinearFunction $ \v w -> Tensor
          $ outer (unsafeCreate $ toArray w) v
     FlexibleDimensionalCase -> bilinearFunction $ \v w -> Tensor
          . ArB.map (*^w) $ toArray v
  transposeTensor :: ∀ w . (TensorSpace w, Scalar w ~ ℝ)
                        => (R n ⊗ w) -+> (w ⊗ R n)
  transposeTensor = case dimensionality @w of
     StaticDimensionalCase -> LinearFunction $ \(Tensor t)
        -> sumV [ (tensorProduct-+$>w)-+$>v                  -- TODO use hmatrix
                | (v,whm) <- zip (toColumns eye) (toRows t)  -- transpose to make
                , let w = unsafeFromArray $ extract whm ]    -- this more efficient?
     FlexibleDimensionalCase -> LinearFunction $ \(Tensor t)
        -> sumV [ (tensorProduct-+$>w)-+$>v
                | (v,w) <- zip (toColumns eye) (ArB.toList t) ]
  fmapTensor :: ∀ w x . ( TensorSpace w, Scalar w ~ ℝ
                        , TensorSpace x, Scalar x ~ ℝ )
                  => Bilinear (x-+>w) (R n ⊗ x) (R n ⊗ w)
  fmapTensor = case (dimensionality @x, dimensionality @w) of
     (StaticDimensionalCase, StaticDimensionalCase) -> bilinearFunction
         $ \(LinearFunction f)       -- TODO make dimension-dependent. Building a
                                     -- matrix for @f@ is inefficient if the dimensions
                                     -- of @w@ and @x@ are larger than @n@.
             -> let fm = unsafeFromCols
                          [ unsafeCreate . toArray $ f x
                          | i <- [0 .. dx - 1]
                          , let Just x = fromArray  -- TODO use unsafeFromArray
                                 $ ArU.generate dx (\j -> if i==j then 1 else 0) ]
                    dx = dimension @x
                in \(Tensor t) -> Tensor $ mul fm t
     (StaticDimensionalCase, FlexibleDimensionalCase) -> bilinearFunction
         $ \(LinearFunction f) (Tensor t)
        -> Tensor . ArB.map (f . unsafeFromArray . extract) . ArB.fromList $ toRows t
     (FlexibleDimensionalCase, StaticDimensionalCase) -> bilinearFunction
         $ \(LinearFunction f) (Tensor t)
        -> Tensor . unsafeFromCols . ArB.toList
               $ ArB.map (unsafeCreate . toArray . f) t
     (FlexibleDimensionalCase, FlexibleDimensionalCase) -> bilinearFunction
         $ \(LinearFunction f) (Tensor t) -> Tensor $ ArB.map f t
  fzipTensorWith :: ∀ w x y . ( TensorSpace w, Scalar w ~ ℝ
                              , TensorSpace x, Scalar x ~ ℝ
                              , TensorSpace y, Scalar y ~ ℝ )
                  => Bilinear ((x,y)-+>w) (R n ⊗ x,R n ⊗ y) (R n ⊗ w)
  fzipTensorWith = case ( dimensionality @x
                        , dimensionality @y, dimensionality @w ) of
     (StaticDimensionalCase, StaticDimensionalCase, StaticDimensionalCase) -> bilinearFunction
         $ \(LinearFunction f)       -- TODO make dimension-dependent. Building
                                     -- matrices for @f@ is inefficient if the dimensions
                                     -- of @w@ and @x+y@ are larger than @n@.
             -> let fmx = unsafeFromCols
                          [ unsafeCreate . toArray $ f (x,zeroV)
                          | i <- [0 .. dx - 1]
                          , let Just x = fromArray  -- TODO use unsafeFromArray
                                 $ ArU.generate dx (\j -> if i==j then 1 else 0)
                          ]
                    fmy = unsafeFromCols
                          [ unsafeCreate . toArray $ f (zeroV,y)
                          | i <- [0 .. dy - 1]
                          , let Just y = fromArray  -- TODO use unsafeFromArray
                                 $ ArU.generate dy (\j -> if i+dx==j then 1 else 0)
                          ]
                    dx = dimension @x
                    dy = dimension @y
                in \(Tensor tx, Tensor ty) -> Tensor $ mul fmx tx + mul fmy ty
     (StaticDimensionalCase, FlexibleDimensionalCase, StaticDimensionalCase) -> bilinearFunction
         $ \(LinearFunction f)
             -> let fmx = unsafeFromCols
                          [ unsafeCreate . toArray $ f (x,zeroV)
                          | i <- [0 .. dx - 1]
                          , let Just x = fromArray  -- TODO use unsafeFromArray
                                 $ ArU.generate dx (\j -> if i==j then 1 else 0)
                          ]
                    dx = dimension @x
                in \(Tensor tx, Tensor ty) -> Tensor
                       $ mul fmx tx
                        + unsafeFromCols
                           [ wRn
                           | y <- ArG.toList ty
                           , let w = f (zeroV, y)
                                 wa = toArray w
                                 Just wRn = create wa
                           ]
     (FlexibleDimensionalCase, StaticDimensionalCase, StaticDimensionalCase) -> bilinearFunction
         $ \(LinearFunction f)
             -> let fmy = unsafeFromCols
                          [ unsafeCreate . toArray $ f (zeroV,y)
                          | i <- [0 .. dy - 1]
                          , let Just y = fromArray  -- TODO use unsafeFromArray
                                 $ ArU.generate dy (\j -> if i==j then 1 else 0)
                          ]
                    dy = dimension @y
                in \(Tensor tx, Tensor ty) -> Tensor
                       $ unsafeFromCols
                           [ wRn
                           | x <- ArG.toList tx
                           , let w = f (x, zeroV)
                                 wa = toArray w
                                 Just wRn = create wa
                           ]
                          + mul fmy ty
     (StaticDimensionalCase, StaticDimensionalCase, FlexibleDimensionalCase)
       -> bilinearFunction $ \(LinearFunction f) (Tensor tx, Tensor ty)
        -> Tensor . ArB.map (f . (unsafeFromArray . extract
                              *** unsafeFromArray . extract)) . ArB.fromList
             $ zip (toRows tx) (toRows ty)
     (StaticDimensionalCase, FlexibleDimensionalCase, FlexibleDimensionalCase)
       -> bilinearFunction $ \(LinearFunction f) (Tensor tx, Tensor ty)
        -> Tensor $ ArB.zipWith (curry f)
             (ArB.map (unsafeFromArray . extract) . ArB.fromList $ toColumns tx)
             ty
     (FlexibleDimensionalCase, StaticDimensionalCase, FlexibleDimensionalCase)
       -> bilinearFunction $ \(LinearFunction f) (Tensor tx, Tensor ty)
        -> Tensor $ ArB.zipWith (curry f)
             tx
             (ArB.map (unsafeFromArray . extract) . ArB.fromList $ toColumns ty)
     (FlexibleDimensionalCase, FlexibleDimensionalCase, StaticDimensionalCase)
       -> bilinearFunction
         $ \(LinearFunction f) (Tensor tx, Tensor ty)
        -> Tensor . unsafeFromCols . ArB.toList
               $ ArB.zipWith (curry $ unsafeCreate . toArray . f) tx ty
     (FlexibleDimensionalCase, FlexibleDimensionalCase, FlexibleDimensionalCase)
       -> bilinearFunction $ \(LinearFunction f) (Tensor tx, Tensor ty)
        -> Tensor $ ArB.zipWith (curry f) tx ty
  coerceFmapTensorProduct :: ∀ p a b . (Functor p, DimensionAware a)
     => p (R n) -> VSCCoercion ℝ a b
        -> Coercion (RTensorProduct n a (StaticDimension a))
                    (RTensorProduct n b (StaticDimension b))
  coerceFmapTensorProduct _ = case dimensionality @a of
     StaticDimensionalCase
        -> \VSCCoercion -> Coercion
     FlexibleDimensionalCase
        -> \VSCCoercion -> Coercion
  wellDefinedVector v
   | unwrap v==unwrap v  = Just v
   | otherwise           = Nothing
  wellDefinedTensor :: ∀ w .
             (TensorSpace w, Scalar w ~ ℝ) => (R n ⊗ w) -> Maybe (R n ⊗ w)
  wellDefinedTensor = case dimensionality @w of
     StaticDimensionalCase -> \t@(Tensor tt) -> if unwrap tt==unwrap tt
                                            then Just t
                                            else Nothing
     FlexibleDimensionalCase -> \(Tensor tt) -> Tensor <$> traverse wellDefinedVector tt
  tensorUnsafeFromArrayWithOffset :: ∀ w m α
          . (m`Dimensional`w, Scalar w ~ ℝ, ArG.Vector α ℝ)
           => Int -> α ℝ -> Tensor ℝ (R n) w
  tensorUnsafeFromArrayWithOffset i ar
     = withKnownNat (dimensionalitySing @w)
        (Tensor . unsafeCreateMat . HMat.reshape n
         . ArG.convert $ ArG.slice i (n*m) ar)
   where n = fromIntegral (natVal @n Proxy)
         m = dimension @w
  tensorUnsafeWriteArrayWithOffset :: ∀ w m α σ
          . (m`Dimensional`w, Scalar w ~ ℝ, ArG.Vector α ℝ)
           => ArG.Mutable α σ ℝ -> Int -> Tensor ℝ (R n) w -> ST σ ()
  tensorUnsafeWriteArrayWithOffset ar i (Tensor t)
     = withKnownNat (dimensionalitySing @w)
        (ArG.unsafeCopy (ArGM.slice i (n*m) ar)
         . ArG.convert . HMat.flatten $ extract t)
   where n = fromIntegral (natVal @n Proxy)
         m = dimension @w

staticDimTensorTensorMatrixCreate :: ∀ n v w dv dw
     . (KnownNat n, dv`Dimensional`v, dw`Dimensional`w)
             => HMat.Matrix Double
              -> Maybe (TensorProduct (R n) (v⊗w))
staticDimTensorTensorMatrixCreate m
    = withKnownNat (dimensionalitySing @v%*dimensionalitySing @w) (create m)

undiscretizeEndoMap :: ∀ v n . (LinearSpace v, n`Dimensional`v, Scalar v ~ ℝ)
    => L n n -> LinearMap ℝ v v
undiscretizeEndoMap = withKnownNat (dimensionalitySing @v)
      (unsafeFromArray . HMat.flatten . extract)

instance ∀ n . KnownNat n => LinearSpace (R n) where
  type DualVector (R n) = R n
  dualSpaceWitness = DualSpaceWitness
  linearId = LinearMap eye
  applyDualVector = bilinearFunction (HMatS.<.>)
  applyLinear :: ∀ w . (TensorSpace w, Scalar w ~ ℝ) => (R n+>w) -+> (R n-+>w)
  applyLinear = bilinearFunction $ case dimensionality @w of
    StaticDimensionalCase -> \(LinearMap m) v
     -> unsafeFromArray . extract $ m#>v
    FlexibleDimensionalCase -> \(LinearMap m) v
     -> ArG.ifoldl' (\w i ac -> ac ^+^ w^*(extract v ArG.! i)) zeroV m
  tensorId :: ∀ w . (LinearSpace w, Scalar w ~ ℝ)
                => LinearMap ℝ (R n⊗w) (R n⊗w)
  tensorId = case dualSpaceWitness @w of
   DualSpaceWitness -> case dimensionality @w of
    StaticDimensionalCase
      -> let dws = dimensionalitySing @w
             dw = dimension @w
         in staticDimensionalIsStatic @(DualVector w)
              ( staticDimensionalIsStatic @(R n ⊗ (R n ⊗ w))
               ( withKnownNat (sing @n %* dws)
                 (LinearMap . fromJust . staticDimTensorTensorMatrixCreate @n
                                        @(DualVector w) @(R n⊗w)
               . HMat.reshape n . HMat.flatten $ HMat.ident (n*dw) ) ) )
    FlexibleDimensionalCase
      -> LinearMap . ArB.generate n
          $ \i -> (fmapTensor -+$> LinearFunction
                    $ \w -> Tensor . ArB.generate n
                     $ \j -> if i==j then w else zeroV)
                   -+$> fromLinearMap -+$=> linearId
   where n = fromIntegral (natVal @n Proxy) :: Int
  applyTensorFunctional :: ∀ u . (LinearSpace u, Scalar u ~ ℝ)
     => Bilinear (LinearMap ℝ (R n) (DualVector u))
                 (Tensor ℝ (R n) u)
                 ℝ
  applyTensorFunctional = case dualSpaceWitness @u of
    DualSpaceWitness -> case dimensionality @u of
      StaticDimensionalCase -> staticDimensionalIsStatic @(DualVector u)
       (bilinearFunction $ \(LinearMap m) (Tensor t)
          -> trace -+$> undiscretizeEndoMap @u (m HMatS.<> tr t)
         )
      FlexibleDimensionalCase -> bilinearFunction $ \(LinearMap m) (Tensor t)
          -> ArB.sum $ ArB.zipWith (getLinearFunction . getLinearFunction
                                        applyDualVector) m t
  applyTensorLinMap :: ∀ u w . ( LinearSpace u, Scalar u ~ ℝ
                               , TensorSpace w, Scalar w ~ ℝ )
               => Bilinear (LinearMap ℝ (Tensor ℝ (R n) u) w)
                           (Tensor ℝ (R n) u)
                           w
  applyTensorLinMap = case dualSpaceWitness @u of
    DualSpaceWitness -> case (dimensionality @u, dimensionality @w) of
      (StaticDimensionalCase, StaticDimensionalCase)
         -> withKnownNat (dimensionalitySing @u %* dimensionalitySing @w)
             ( bilinearFunction $ \(LinearMap m) (Tensor t)
                -> unsafeFromArray
                  $ extract m HMat.#> HMat.flatten (extract t) )
      (StaticDimensionalCase, FlexibleDimensionalCase)
           -> bilinearFunction $ \(LinearMap m) (Tensor t)
                -> let tmat = extract t
                   in ArB.ifoldl' (\acc i u2w -> acc ^+^
                                    ( (applyLinear-+$>fromTensor-+$=>u2w)
                                      -+$> unsafeFromArray @u
                                        (HMat.flatten $ tmat HMat.? [i]) ) )
                                  zeroV m
      (FlexibleDimensionalCase, _)
          -> bilinearFunction $ \(LinearMap m) (Tensor t)
              -> ArB.ifoldl' (\acc i u -> acc ^+^
                               ( (applyLinear-+$>fromTensor-+$=>(m ArB.! i))
                                  -+$> u) ) zeroV t



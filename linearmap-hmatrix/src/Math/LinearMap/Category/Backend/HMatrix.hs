-- |
-- Module      : Math.LinearMap.Category.Backend.HMatrix
-- Copyright   : (c) Justus Sagemüller 2024
-- License     : GPL v3
-- 
-- Maintainer  : (@) justussa $ kth.se
-- Stability   : experimental
-- Portability : portable
-- 


{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE InstanceSigs             #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE UnicodeSyntax            #-}
{-# LANGUAGE CPP                      #-}

module Math.LinearMap.Category.Backend.HMatrix where

import Prelude hiding (fmap, (.))
import Control.Category.Constrained ((.))
import Control.Functor.Constrained (fmap)

import Math.LinearMap.Category
import Math.LinearMap.Coercion (uncurryLinearMap, (-+$=>))
import Math.VectorSpace.DimensionAware

import Numeric.LinearAlgebra.Static.Orphans ()
import Numeric.LinearAlgebra.Static.Util

-- base
import Data.Function (on)
import Data.List (unfoldr)
import GHC.TypeLits (KnownNat)
import Data.Type.Coercion (Coercion(..))
import Control.Monad.ST (ST)
--

-- singletons
#if MIN_VERSION_singletons(3,0,0)
import Prelude.Singletons (SNum(..))
import GHC.TypeLits.Singletons (withKnownNat)
#else
import Data.Singletons.Prelude.Num (SNum(..))
import Data.Singletons.TypeLits (withKnownNat)
#endif

-- vector-space
import Data.Basis (HasBasis(..))

--
-- hmatrix
import Numeric.LinearAlgebra.Static as HMatS
import qualified Numeric.LinearAlgebra as HMat

-- vector
import qualified Data.Vector as ArB
import qualified Data.Vector.Unboxed as ArU
import qualified Data.Vector.Storable as ArS
import qualified Data.Vector.Generic as ArG
import qualified Data.Vector.Generic.Mutable as ArGM

-- finite-typelits
import Data.Finite (Finite)

-- | Values of type @'HMatrixImpl' v@ conceptually represent vectors of type
--   @v@, but use HMatrix-vectors as the actual implementations for linear operations.
newtype HMatrixImpl v = HMatrixImpl {getHMatrixImplementation :: R (Dimension v)}

instance StaticDimensional v => Show (HMatrixImpl v) where
  showsPrec p (HMatrixImpl v) = dimensionIsStatic @v
       (showParen (p>9) $ ("HMatrixImpl "++) . showsPrec 10 v)

fromHMatrixImpl :: ∀ v . (StaticDimensional v, Scalar v ~ ℝ)
                             => HMatrixImpl v -+> v
fromHMatrixImpl = dimensionIsStatic @v
   ( LinearFunction $ \(HMatrixImpl v) -> unsafeFromArray (HMatS.extract v) )

asHMatrixImpl :: ∀ v . (StaticDimensional v, Scalar v ~ ℝ)
                             => v -+> HMatrixImpl v
asHMatrixImpl = dimensionIsStatic @v
   ( LinearFunction $ HMatrixImpl . unsafeCreate . toArray )

instance ∀ v . StaticDimensional v => Eq (HMatrixImpl v) where
  (==) = dimensionIsStatic @v ((==)`on`(HMatS.extract . getHMatrixImplementation))

instance ∀ v . StaticDimensional v => AdditiveGroup (HMatrixImpl v) where
  zeroV = dimensionIsStatic @v (HMatrixImpl zeroV)
  (^+^) = dimensionIsStatic @v
            (\(HMatrixImpl v) (HMatrixImpl w) -> HMatrixImpl $ v^+^w)
  (^-^) = dimensionIsStatic @v
            (\(HMatrixImpl v) (HMatrixImpl w) -> HMatrixImpl $ v^-^w)
  negateV = dimensionIsStatic @v
            (\(HMatrixImpl v) -> HMatrixImpl $ negateV v)

instance ∀ v . (StaticDimensional v, Scalar v ~ ℝ) => VectorSpace (HMatrixImpl v) where
  type Scalar (HMatrixImpl v) = ℝ
  (*^) = dimensionIsStatic @v
          (\μ (HMatrixImpl v) -> HMatrixImpl $ μ*^v)

instance ∀ v . StaticDimensional v => AffineSpace (HMatrixImpl v) where
  type Diff (HMatrixImpl v) = HMatrixImpl v
  (.-.) = dimensionIsStatic @v
            (\(HMatrixImpl v) (HMatrixImpl w) -> HMatrixImpl $ v^-^w)
  (.+^) = dimensionIsStatic @v
            (\(HMatrixImpl v) (HMatrixImpl w) -> HMatrixImpl $ v^+^w)

instance ∀ v . (StaticDimensional v, Scalar v ~ ℝ) => InnerSpace (HMatrixImpl v) where
  (<.>) = dimensionIsStatic @v
            (\(HMatrixImpl v) (HMatrixImpl w) -> dot v w)

instance ∀ v . (StaticDimensional v, Scalar v ~ ℝ) => HasBasis (HMatrixImpl v) where
  type Basis (HMatrixImpl v) = Finite (Dimension v)
  basisValue = dimensionIsStatic @v (HMatrixImpl . basisValue)
  decompose = dimensionIsStatic @v (decompose . getHMatrixImplementation)
  decompose' = dimensionIsStatic @v (decompose' . getHMatrixImplementation)

instance ∀ v . (StaticDimensional v, Scalar v ~ ℝ) => DimensionAware (HMatrixImpl v) where
  type StaticDimension (HMatrixImpl v) = 'Just (Dimension v)
  dimensionalityWitness = dimensionIsStatic @v IsStaticDimensional

instance ∀ v n . (KnownNat n, n`Dimensional`v, Scalar v ~ ℝ)
                      => n`Dimensional`HMatrixImpl v where
  unsafeFromArrayWithOffset i = HMatrixImpl . unsafeFromArrayWithOffset i
  unsafeWriteArrayWithOffset ar i
         = unsafeWriteArrayWithOffset ar i . getHMatrixImplementation

instance ∀ v . StaticDimensional v => Semimanifold (HMatrixImpl v) where
  type Needle (HMatrixImpl v) = HMatrixImpl v
  (.+~^) = (^+^)

instance ∀ v . StaticDimensional v => PseudoAffine (HMatrixImpl v) where
  (.-~!) = (^-^)
  v.-~.w = Just (v^-^w)

type family HMatImplTensorProduct v w dw where
  HMatImplTensorProduct v w ('Just m) = L m (Dimension v)
  HMatImplTensorProduct v w 'Nothing = Tensor ℝ v w

instance ∀ v . (StaticDimensional v, TensorSpace v, Scalar v ~ ℝ)
                    => TensorSpace (HMatrixImpl v) where
  type TensorProduct (HMatrixImpl v) w
             = HMatImplTensorProduct v w (StaticDimension w)
  scalarSpaceWitness = ScalarSpaceWitness
  linearManifoldWitness = LinearManifoldWitness
  zeroTensor :: ∀ w . (TensorSpace w, Scalar w ~ ℝ) => HMatrixImpl v ⊗ w
  zeroTensor = dimensionIsStatic @v ( case dimensionality @w of
     StaticDimensionalCase -> Tensor $ konst 0
     FlexibleDimensionalCase -> Tensor zeroTensor
    )
  addTensors :: ∀ w . (TensorSpace w, Scalar w ~ ℝ)
        => (HMatrixImpl v ⊗ w) -> (HMatrixImpl v ⊗ w) -> (HMatrixImpl v ⊗ w)
  addTensors = dimensionIsStatic @v ( case dimensionality @w of
     StaticDimensionalCase -> \(Tensor a) (Tensor b) -> Tensor $ a + b
     FlexibleDimensionalCase -> \(Tensor a) (Tensor b)
            -> Tensor $ a^+^b
    )
  subtractTensors :: ∀ w . (TensorSpace w, Scalar w ~ ℝ)
        => (HMatrixImpl v ⊗ w) -> (HMatrixImpl v ⊗ w) -> (HMatrixImpl v ⊗ w)
  subtractTensors = dimensionIsStatic @v ( case dimensionality @w of
     StaticDimensionalCase -> \(Tensor a) (Tensor b) -> Tensor $ a - b
     FlexibleDimensionalCase -> \(Tensor a) (Tensor b)
            -> Tensor $ a^+^b
    )
  negateTensor :: ∀ w . (TensorSpace w, Scalar w ~ ℝ)
             => (HMatrixImpl v ⊗ w) -+> (HMatrixImpl v ⊗ w)
  negateTensor = dimensionIsStatic @v ( case dimensionality @w of
     StaticDimensionalCase -> LinearFunction $ \(Tensor a) -> Tensor $ -a
     FlexibleDimensionalCase -> LinearFunction $ \(Tensor a)
            -> Tensor $ negateV a
    )
  scaleTensor :: ∀ w . (TensorSpace w, Scalar w ~ ℝ)
                  => Bilinear ℝ (HMatrixImpl v ⊗ w) (HMatrixImpl v ⊗ w)
  scaleTensor = dimensionIsStatic @v ( case dimensionality @w of
     StaticDimensionalCase -> bilinearFunction $ \μ (Tensor a) -> Tensor $ dmmap (μ*) a
     FlexibleDimensionalCase -> bilinearFunction $ \μ (Tensor a)
            -> Tensor $ μ*^a
    )
  toFlatTensor = LinearFunction $ \(HMatrixImpl v) -> Tensor $ row v
  fromFlatTensor = LinearFunction $ \(Tensor t) -> HMatrixImpl $ unrow t
  tensorProduct :: ∀ w . (TensorSpace w, Scalar w ~ ℝ) => Bilinear (HMatrixImpl v) w (HMatrixImpl v ⊗ w)
  tensorProduct = dimensionIsStatic @v ( case dimensionality @w of
     StaticDimensionalCase -> bilinearFunction $ \(HMatrixImpl v) w -> Tensor
          $ outer (unsafeCreate $ toArray w) v
     FlexibleDimensionalCase -> bilinearFunction $
             \v w -> Tensor $ (fromHMatrixImpl-+$>v) ⊗ w
    )
  transposeTensor :: ∀ w . (TensorSpace w, Scalar w ~ ℝ)
                        => (HMatrixImpl v ⊗ w) -+> (w ⊗ HMatrixImpl v)
  transposeTensor = dimensionIsStatic @v ( case dimensionality @w of
     StaticDimensionalCase -> LinearFunction $ \(Tensor t)
        -> sumV [ (tensorProduct-+$>w)-+$>HMatrixImpl v      -- TODO use hmatrix
                | (v,whm) <- zip (toColumns eye) (toRows t)  -- transpose to make
                , let w = unsafeFromArray $ extract whm ]    -- this more efficient?
     FlexibleDimensionalCase -> LinearFunction $ \(Tensor t)
        -> fmap asHMatrixImpl . transposeTensor @v @w -+$> t
    )
  fmapTensor :: ∀ w x . ( TensorSpace w, Scalar w ~ ℝ
                        , TensorSpace x, Scalar x ~ ℝ )
                  => Bilinear (x-+>w) (HMatrixImpl v ⊗ x) (HMatrixImpl v ⊗ w)
  fmapTensor = dimensionIsStatic @v ( case (dimensionality @x, dimensionality @w) of
     (StaticDimensionalCase, StaticDimensionalCase) -> bilinearFunction
         $ \(LinearFunction f)       -- TODO make dimension-dependent. Building a
                                     -- matrix for @f@ is inefficient if the dimensions
                                     -- of @w@ and @x@ are larger than @n@.
             -> let fm :: L (Dimension w) (Dimension x)
                    fm = generateCols $ \i
                          -> let Just x = fromArray  -- TODO use unsafeFromArray
                                  $ ArU.generate dx (\j -> if i==j then 1 else 0)
                             in unsafeCreate . toArray $ f x
                    dx = dimension @x
                in \(Tensor t) -> Tensor $ mul fm t
     (StaticDimensionalCase, FlexibleDimensionalCase) -> bilinearFunction
         $ \f (Tensor t)
        -> Tensor . getLinearFunction (fmap f)
            . unsafeFromArray . foldMap HMatS.extract $ toRows t
     (FlexibleDimensionalCase, StaticDimensionalCase) -> bilinearFunction
         $ \f (Tensor t)
        -> let n = dimension @w
               wSizeChunk :: ArS.Vector ℝ -> [R (Dimension w)]
               wSizeChunk v
                | ArG.length v >= n
                    = let (chunk, rest) = ArG.splitAt n v
                      in unsafeCreate chunk : wSizeChunk rest
                | otherwise  = []
           in Tensor . unsafeFromCols . wSizeChunk . toArray
            $ fmap f-+$>t
     (FlexibleDimensionalCase, FlexibleDimensionalCase) -> bilinearFunction
         $ \f (Tensor t) -> Tensor (fmap f -+$> t)
   )
  fzipTensorWith :: ∀ w x y . ( TensorSpace w, Scalar w ~ ℝ
                              , TensorSpace x, Scalar x ~ ℝ
                              , TensorSpace y, Scalar y ~ ℝ )
                  => Bilinear ((x,y)-+>w) (HMatrixImpl v ⊗ x,HMatrixImpl v ⊗ y) (HMatrixImpl v ⊗ w)
  fzipTensorWith = undefined
  coerceFmapTensorProduct :: ∀ a b p . ( Functor p
                                       , DimensionAware a, TensorSpace a
                                       , TensorSpace b
                                       , Scalar a ~ ℝ, Scalar b ~ ℝ )
     => p (HMatrixImpl v) -> VSCCoercion ℝ a b
        -> Coercion (HMatImplTensorProduct v a (StaticDimension a))
                    (HMatImplTensorProduct v b (StaticDimension b))
  coerceFmapTensorProduct _ = case dimensionality @a of
     StaticDimensionalCase
        -> \VSCCoercion -> Coercion
     FlexibleDimensionalCase
        -> \crcab@VSCCoercion -> case coerceFmapTensorProduct @v @a @b [] crcab of
               Coercion -> Coercion
  wellDefinedVector (HMatrixImpl v) = dimensionIsStatic @v (
       if unwrap v==unwrap v then Just $ HMatrixImpl v
                             else Nothing
    )
  wellDefinedTensor :: ∀ w .
             (TensorSpace w, Scalar w ~ ℝ)
                 => (HMatrixImpl v ⊗ w) -> Maybe (HMatrixImpl v ⊗ w)
  wellDefinedTensor = dimensionIsStatic @v (case dimensionality @w of
     StaticDimensionalCase -> \t@(Tensor tt) -> if unwrap tt==unwrap tt
                                            then Just t
                                            else Nothing
     FlexibleDimensionalCase -> \(Tensor tt) -> Tensor <$> wellDefinedTensor tt
    )
  tensorUnsafeFromArrayWithOffset :: ∀ w m α
          . (TensorSpace w, m`Dimensional`w, Scalar w ~ ℝ, ArG.Vector α ℝ)
           => Int -> α ℝ -> Tensor ℝ (HMatrixImpl v) w
  tensorUnsafeFromArrayWithOffset i ar
     = dimensionIsStatic @v (
        case tensorUnsafeFromArrayWithOffset @(R (Dimension v)) @w i ar of
         Tensor t -> Tensor t
      )
  tensorUnsafeWriteArrayWithOffset :: ∀ w m α σ
          . (m`Dimensional`w, Scalar w ~ ℝ, ArG.Vector α ℝ)
           => ArG.Mutable α σ ℝ -> Int -> Tensor ℝ (HMatrixImpl v) w -> ST σ ()
  tensorUnsafeWriteArrayWithOffset ar i (Tensor t)
     = withDimension @v @Int (\n
     -> withDimension @w (\m
     -> ArG.unsafeCopy (ArGM.slice i (n*m) ar)
         . ArG.convert . HMat.flatten . HMat.tr $ extract t
       ))


instance ∀ v . (StaticDimensional v, LinearSpace v, Scalar v ~ ℝ)
                    => LinearSpace (HMatrixImpl v) where
  type DualVector (HMatrixImpl v) = HMatrixImpl (DualVector v)
  dualSpaceWitness = case dualSpaceWitness @v of
    DualSpaceWitness -> dimensionIsStatic @v DualSpaceWitness
  linearId = case dualSpaceWitness @v of
    DualSpaceWitness -> dimensionIsStatic @v (LinearMap $ HMatS.eye)
  applyDualVector = dimensionIsStatic @v (case dualSpaceWitness @v of
    DualSpaceWitness -> bilinearFunction
     (\(HMatrixImpl dv) (HMatrixImpl v) -> dv HMatS.<.> v)
   )
  applyLinear :: ∀ w . (TensorSpace w, Scalar w ~ ℝ)
                            => (HMatrixImpl v+>w) -+> (HMatrixImpl v-+>w)
  applyLinear = case dualSpaceWitness @v of
   DualSpaceWitness -> dimensionIsStatic @v (
    bilinearFunction $ case dimensionality @w of
      StaticDimensionalCase -> \(LinearMap m) (HMatrixImpl v)
       -> unsafeFromArray . extract $ m#>v
      FlexibleDimensionalCase -> \(LinearMap (Tensor m)) v
       -> (applyLinear -+$> LinearMap m) -+$> (fromHMatrixImpl -+$> v)
    )
  tensorId :: ∀ w . (LinearSpace w, Scalar w ~ ℝ)
                => LinearMap ℝ (HMatrixImpl v⊗w) (HMatrixImpl v⊗w)
  tensorId = case dualSpaceWitness @v of
   DualSpaceWitness -> withDimension @v (\n -> case dualSpaceWitness @w of
    DualSpaceWitness -> case dimensionality @w of
     StaticDimensionalCase
       -> uncurryLinearMap -+$=> LinearMap undefined {- let dws = dimensionalitySing @w
              dw = dimension @w
          in dimensionIsStatic @(DualVector w)
               ( withKnownNat (dimensionalitySing @v %* dws)
                  undefined )
              -}
     FlexibleDimensionalCase
       -> undefined {- LinearMap . ArB.generate n
           $ \i -> (fmapTensor -+$> LinearFunction
                     $ \w -> Tensor . ArB.generate n
                      $ \j -> if i==j then w else zeroV)
                    -+$> fromLinearMap -+$=> linearId
                    -}
    )


-- | Use a HMatrix-based linear map as if it was directly operating on the abstract
--   vector spaces. Note that this is inefficient if a 'TensorProduct' -based linear
--   map is built up from the linear function.
linfunFromHMatrixImpl :: ∀ v w . ( StaticDimensional v, StaticDimensional w
                                 , LinearSpace v, TensorSpace w
                                 , Scalar v ~ ℝ, Scalar w ~ ℝ )
                             => (HMatrixImpl v+>HMatrixImpl w) -+> (v-+>w)
linfunFromHMatrixImpl = dimensionIsStatic @v (dimensionIsStatic @w
  (case dualSpaceWitness @v of
   DualSpaceWitness -> LinearFunction
    $ \m -> fromHMatrixImpl
            . (applyLinear-+$>m)
            . asHMatrixImpl
    ))

linmapFromHMatrixImpl :: ∀ v w . ( StaticDimensional v, StaticDimensional w
                                 , LinearSpace v, TensorSpace w
                                 , Scalar v ~ ℝ, Scalar w ~ ℝ )
                             => (HMatrixImpl v+>HMatrixImpl w) -+> (v+>w)
linmapFromHMatrixImpl = sampleLinearFunction <.+- linfunFromHMatrixImpl
                         -- TODO efficient implementation

-- | Inverse of 'linfunFromHMatrixImpl'.
linfunAsHMatrixImpl :: ∀ v w . ( StaticDimensional v, StaticDimensional w
                               , LinearSpace v, TensorSpace w
                               , Scalar v ~ ℝ, Scalar w ~ ℝ )
                             => (v-+>w) -+> (HMatrixImpl v+>HMatrixImpl w)
linfunAsHMatrixImpl = dimensionIsStatic @v (dimensionIsStatic @w
  (case dualSpaceWitness @v of
   DualSpaceWitness -> LinearFunction
    $ \f -> sampleLinearFunction
          -+$> asHMatrixImpl . f . fromHMatrixImpl
    ))
    
linmapAsHMatrixImpl :: ∀ v w . ( StaticDimensional v, StaticDimensional w
                               , LinearSpace v, TensorSpace w
                               , Scalar v ~ ℝ, Scalar w ~ ℝ )
                             => (v+>w) -+> (HMatrixImpl v+>HMatrixImpl w)
linmapAsHMatrixImpl = linfunAsHMatrixImpl <.+- applyLinear
                         -- TODO efficient implementation


instance ∀ v w s . ( LinearSpace v, StaticDimensional v, StaticDimensional w
                   , s ~ Scalar v, s ~ Scalar w
                   ) => Show (LinearMap s (HMatrixImpl v) (HMatrixImpl w)) where
  showsPrec p (LinearMap m) = case dualSpaceWitness @v of
   DualSpaceWitness -> dimensionIsStatic @v (dimensionIsStatic @w
       (showParen (p>9) $ ("LinearMap "++) . showsPrec 10 m))


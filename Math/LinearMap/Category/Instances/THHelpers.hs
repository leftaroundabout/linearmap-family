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
        , mkFreeLinearSpace
        , mkFreeArbitrarySpace
        , autoLinearManifoldWitness
        ) where

import Math.VectorSpace.DimensionAware
import Math.LinearMap.Category.Class

import Data.VectorSpace
import Data.Basis

#if MIN_VERSION_manifolds_core(0,6,0)
import Math.Manifold.Core.Types (EmptyMfd)
#endif
import Math.Manifold.Core.Types (ℝ)
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
import THLego.Helpers (multiAppE)

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


{-# INLINE tensorUnsafeFromArrayWithOffsetViaList #-}
tensorUnsafeFromArrayWithOffsetViaList
          :: ∀ v w n m α . ( n`Dimensional`v
                           , m`Dimensional`w
                           , Scalar v ~ Scalar w
                           , GArr.Vector α (Scalar v) )
   => ([w] -> TensorProduct v w) -> Int -> α (Scalar v) -> (v⊗w)
tensorUnsafeFromArrayWithOffsetViaList l2v i ar
   = Tensor $ l2v [ unsafeFromArrayWithOffset
                      (i + j * dimension @w) ar
                  | j <- [0 .. dimension @v - 1] ]

{-# INLINE tensorUnsafeWriteArrayWithOffsetViaList #-}
tensorUnsafeWriteArrayWithOffsetViaList
        :: ∀ v w n m α σ . ( n`Dimensional`v
                           , m`Dimensional`w
                           , Scalar v ~ Scalar w
                           , GArr.Vector α (Scalar v) )
   => (TensorProduct v w -> [w]) -> GArr.Mutable α σ (Scalar v)
          -> Int -> (v⊗w) -> ST σ ()
tensorUnsafeWriteArrayWithOffsetViaList v2l ar i (Tensor t)
   = forM_ (zip [0..] $ v2l t) $ \(j, v)
       -> unsafeWriteArrayWithOffset ar
                      (i + j * dimension @w) v

mkFreeLinearSpace :: Name -> Name -> Int -> Q [Dec]
mkFreeLinearSpace vTCstrName vECstrName dimens = do
  let 
      vTCstr = pure . ConT $ vTCstrName
      
      vExprn xVars = multiAppE (ConE vECstrName) $ VarE<$>xVars
      vPatt xVars = ConP vECstrName [] $ VarP<$>xVars

      dim = pure . LitT . NumTyLit $ fromIntegral dimens
      newCVars sym = forM [0 .. dimens-1] $ newName . (sym:) . show
      
      vFromList, vToList, tensProd, tensId
        , contraction, contraaction :: Q Exp

      -- fromList [x₀, x₁, ...] = Vₙ x₀ x₁ ...
      vFromList = do
         xVars <- newCVars 'x'
         pure . LamE [ListP (VarP<$>xVars)] $ vExprn xVars

      -- toList (Vₙ x₀ x₁ ...) = [x₀, x₁, ...]
      vToList = do
         xVars <- newCVars 'x'
         return . LamE [vPatt xVars]
              $ ListE (VarE<$>xVars)

      -- tensProd (Tensor (Vₙ x₀ x₁ ...)) = x₀⊗Vₙ 1 0 ...
      --                                ^+^ x₁⊗Vₙ 0 1 ...
      --                                ^+^ ...
      tensProd = do
         xVars <- newCVars 'x'
         return . LamE [ConP 'Tensor [] [vPatt xVars]]
              $ foldr (AppE . AppE (VarE '(^+^)))
                      (VarE 'zeroV)
                      [ multiAppE (VarE '(⊗))
                         [ VarE xVar
                         , multiAppE (ConE vECstrName)
                                      [LitE . IntegerL
                                         $ if i==j then 1 else 0
                                      | j <- [0 .. dimens-1]] ]
                      | (i,xVar) <- zip [0..] xVars ]
       
      -- tensId = Vₙ (\w -> Vₙ w     zeroV zeroV ...)
      --             (\w -> Vₙ zeroV w     zeroV ...)
      --             (\w -> Vₙ zeroV zeroV w     ...)
      --             ...
      tensId = do
         multiAppE (ConE vECstrName) <$> forM [0 .. dimens-1] `id` \i -> do
            wVar <- newName "w"
            return . LamE [VarP wVar]
              $ multiAppE (ConE vECstrName)
                   [ VarE $ if i==j
                      then wVar
                      else 'zeroV
                   | j <- [0 .. dimens-1] ]
      
      -- contraction ( Vₙ (Vₙ w₀ _ _ ...)
      --                  (Vₙ _ w₁ _ ...)
      --                  (Vₙ _ _ w₂ ...)
      --                  ...             ) = w₀ ^+^ w₁ ^+^ w₂ ^+^ ...
      contraction = do
         wVars <- newCVars 'w'
         return . LamE [ConP vECstrName []
                         [ ConP vECstrName []
                             [ if i==j
                                then VarP wVar
                                else WildP
                             | j <- [0 .. dimens-1] ]
                         | (i,wVar) <- zip [0..] wVars ]]
           $ foldr (AppE . AppE (VarE '(^+^)))
                   (VarE 'zeroV)
                   [ VarE wVar
                   | wVar <- wVars ]

      -- contraaction (Vₙ x₀ x₁ ...) f
      --          = (f$x₀)^._x + (f$x₁)^._y + ...
      contraaction = do
         xVars <- newCVars 'x'
         fVar <- newName "f"
         LamE [vPatt xVars, VarP fVar]
             . foldr (AppE . AppE (VarE '(+))) (LitE $ IntegerL 0)
             <$> forM (zip [0..] xVars) `id` \(i,xVar) -> do
            rVar <- newName "r"
            return
             $ AppE (LamE [ConP vECstrName []
                            [ if i==j
                               then VarP rVar
                               else WildP
                            | j <- [0 .. dimens-1] ]]
                          $ VarE rVar)
                    (AppE (VarE '($)) (VarE fVar) `AppE` VarE xVar)


  [d| instance Num s => Semimanifold ($vTCstr s) where
        type Needle ($vTCstr s) = $vTCstr s
        (.+~^) = (^+^)
#if !MIN_VERSION_manifolds_core(0,6,0)
        toInterior = pure
        fromInterior = id
        translateP = Tagged (^+^)
#endif
      instance Num s => PseudoAffine ($vTCstr s) where
        v.-~.w = pure (v^-^w); (.-~!) = (^-^)
      instance ∀ s . (Num' s, Eq s) => DimensionAware ($vTCstr s) where
        type StaticDimension ($vTCstr s) = 'Just $dim
        dimensionalityWitness = IsStaticDimensional
      instance ∀ s . (Num' s, Eq s) => $dim `Dimensional` $vTCstr s where
        unsafeFromArrayWithOffset
           = unsafeFromArrayWithOffsetViaList $vFromList
        unsafeWriteArrayWithOffset
           = unsafeWriteArrayWithOffsetViaList $vToList
      instance ∀ s . (Num' s, Eq s) => TensorSpace ($vTCstr s) where
        type TensorProduct ($vTCstr s) w = $vTCstr w
        scalarSpaceWitness = case closedScalarWitness :: ClosedScalarWitness s of
                               ClosedScalarWitness -> ScalarSpaceWitness
        linearManifoldWitness = autoLinearManifoldWitness
        zeroTensor = Tensor $ pure zeroV
        addTensors (Tensor m) (Tensor n) = Tensor $ liftA2 (^+^) m n
        subtractTensors (Tensor m) (Tensor n) = Tensor $ liftA2 (^-^) m n
        negateTensor = LinearFunction $ Tensor . fmap negateV . getTensorProduct
        scaleTensor = bilinearFunction
                $ \μ -> Tensor . fmap (μ*^) . getTensorProduct
        toFlatTensor = case closedScalarWitness :: ClosedScalarWitness s of
                               ClosedScalarWitness -> LinearFunction $ follow Tensor
        fromFlatTensor = case closedScalarWitness :: ClosedScalarWitness s of
                               ClosedScalarWitness -> LinearFunction $ flout Tensor
        tensorProduct = bilinearFunction $ \w v -> Tensor $ fmap (*^v) w
        transposeTensor = LinearFunction $tensProd
        fmapTensor = bilinearFunction $
                \(LinearFunction f) -> pretendLike Tensor $ fmap f
        fzipTensorWith = bilinearFunction $
                \(LinearFunction f) (Tensor vw, Tensor vx)
                        -> Tensor $ liftA2 (curry f) vw vx
        tensorUnsafeFromArrayWithOffset
           = tensorUnsafeFromArrayWithOffsetViaList $vFromList
        tensorUnsafeWriteArrayWithOffset
           = tensorUnsafeWriteArrayWithOffsetViaList $vToList
        coerceFmapTensorProduct _ VSCCoercion = Coercion
        wellDefinedTensor = getTensorProduct >>> Hask.traverse wellDefinedVector
                             >>> fmap Tensor
      instance ∀ s . (Num' s, Eq s) => LinearSpace ($vTCstr s) where
        type DualVector ($vTCstr s) = $vTCstr s
        dualSpaceWitness = case closedScalarWitness :: ClosedScalarWitness s of
               ClosedScalarWitness -> DualSpaceWitness
        linearId = LinearMap Mat.identity
        idTensor = Tensor Mat.identity
        tensorId = ti dualSpaceWitness where
           ti :: ∀ w . (LinearSpace w, Scalar w ~ s) => DualSpaceWitness w
                      -> ($vTCstr s⊗w)+>($vTCstr s⊗w)
           ti DualSpaceWitness = LinearMap $
                fmap (\f -> fmap (LinearFunction $ Tensor . f)-+$>asTensor $ id)
                     ($tensId :: $vTCstr (w -> $vTCstr w))
        coerceDoubleDual = VSCCoercion
        fromLinearForm = case closedScalarWitness :: ClosedScalarWitness s of
              ClosedScalarWitness -> LinearFunction $ flout LinearMap
        contractTensorMap = LinearFunction $ $contraction . coerce . getLinearMap
        contractMapTensor = LinearFunction $ $contraction . coerce . getTensorProduct
        contractLinearMapAgainst = bilinearFunction $ getLinearMap >>> $contraaction
        applyDualVector = bilinearFunction Mat.dot
        applyLinear = bilinearFunction $ \(LinearMap m)
                        -> foldl' (^+^) zeroV . liftA2 (^*) m
        applyTensorFunctional = bilinearFunction $ \(LinearMap f) (Tensor t)
                   -> sum $ liftA2 (<.>^) f t
        applyTensorLinMap = bilinearFunction $ \(LinearMap f) (Tensor t)
                   -> foldl' (^+^) zeroV $ liftA2 ((fromTensor-+$=>) >>>
                               getLinearFunction . getLinearFunction applyLinear) f t
        composeLinear = bilinearFunction $
               \f (LinearMap g) -> LinearMap $ fmap ((applyLinear-+$>f)-+$>) g
        useTupleLinearSpaceComponents _ = usingNonTupleTypeAsTupleError
   |]


mkFreeArbitrarySpace :: Name -> Q [Dec]
mkFreeArbitrarySpace vTCstrName = do
  let 
      vTCstr = pure . ConT $ vTCstrName
  [d|
    instance (QC.Arbitrary v, Scalar v ~ ℝ) => QC.Arbitrary (Tensor ℝ ($vTCstr ℝ) v) where
      arbitrary = Tensor <$> Hask.traverse (const QC.arbitrary) zeroV
    instance (QC.Arbitrary v, Scalar v ~ ℝ) => QC.Arbitrary (LinearMap ℝ ($vTCstr ℝ) v) where
      arbitrary = LinearMap <$> Hask.traverse (const QC.arbitrary) zeroV
   |]


-- |
-- Module      : Math.LinearMap.Instances.Deriving
-- Copyright   : (c) Justus Sagemüller 2021
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE CPP                        #-}

module Math.LinearMap.Category.Instances.Deriving where

import Math.LinearMap.Category.Class

import Data.VectorSpace
import Data.AffineSpace
import Data.Basis
import Data.MemoTrie

import Prelude ()
import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.Coerce
import Data.Type.Coercion
import Data.Tagged
import Data.Traversable (traverse)

import Math.Manifold.Core.PseudoAffine
import Math.LinearMap.Asserted
import Math.VectorSpace.ZeroDimensional
import Data.VectorSpace.Free

import Language.Haskell.TH


makeTensorSpaceFromBasis :: Q Type -> DecsQ
makeTensorSpaceFromBasis v = sequence
 [ InstanceD Nothing [] <$> [t|Semimanifold $v|] <*> do
    tySyns <- sequence [
#if MIN_VERSION_template_haskell(2,15,0)
       error "The TH type of TySynInstD has changed"
#else
       TySynInstD ''Needle <$> do
         TySynEqn . (:[]) <$> v <*> v
     , TySynInstD ''Interior <$> do
         TySynEqn . (:[]) <$> v <*> v
#endif
     ]
    methods <- [d|
        $(varP $ mkName "toInterior") = pure
        $(varP $ mkName "fromInterior") = id
        $(varP $ mkName "translateP") = Tagged (^+^)
        $(varP $ mkName ".+~^") = (^+^)
        $(varP $ mkName "semimanifoldWitness") = SemimanifoldWitness BoundarylessWitness
     |]
    return $ tySyns ++ methods
 , InstanceD Nothing [] <$> [t|PseudoAffine $v|] <*> do
     [d|
        $(varP $ mkName ".-~!") = (^-^)
      |]
 , InstanceD Nothing [] <$> [t|AffineSpace $v|] <*> do
    tySyns <- sequence [
#if MIN_VERSION_template_haskell(2,15,0)
       error "The TH type of TySynInstD has changed"
#else
       TySynInstD ''Diff <$> do
         TySynEqn . (:[]) <$> v <*> v
#endif
     ]
    methods <- [d|
        $(varP $ mkName ".+^") = (^+^)
        $(varP $ mkName ".-.") = (^-^)
      |]
    return $ tySyns ++ methods
 , InstanceD Nothing [] <$> [t|TensorSpace $v|] <*> do
    tySyns <- sequence [
#if MIN_VERSION_template_haskell(2,15,0)
       error "The TH type of TySynInstD has changed"
#else
       TySynInstD ''TensorProduct <$> do
         wType <- VarT <$> newName "w" :: Q Type
         TySynEqn . (:[wType]) <$> v
           <*> [t| Basis $v :->: $(pure wType) |]
#endif
     ]
    methods <- [d|
        $(varP $ mkName "wellDefinedVector") = \v
           -> if v==v then Just v else Nothing
        $(varP $ mkName "wellDefinedTensor") = \(Tensor v)
           -> fmap (const $ Tensor v) . traverse (wellDefinedVector . snd) $ enumerate v
        $(varP $ mkName "zeroTensor") = Tensor . trie $ const zeroV
        $(varP $ mkName "toFlatTensor") = LinearFunction $ Tensor . trie . decompose'
        $(varP $ mkName "fromFlatTensor") = LinearFunction $ \(Tensor t)
                -> recompose $ enumerate t
        $(varP $ mkName "scalarSpaceWitness") = ScalarSpaceWitness
        $(varP $ mkName "linearManifoldWitness") = LinearManifoldWitness BoundarylessWitness
        $(varP $ mkName "addTensors") = \(Tensor v) (Tensor w)
            -> Tensor $ (^+^) <$> v <*> w
        $(varP $ mkName "subtractTensors") = \(Tensor v) (Tensor w)
            -> Tensor $ (^-^) <$> v <*> w
        $(varP $ mkName "tensorProduct") = bilinearFunction
          $ \v w -> Tensor . trie $ \bv -> decompose' v bv *^ w
        $(varP $ mkName "transposeTensor") = LinearFunction $ \(Tensor t)
             -> sumV [ (tensorProduct-+$>w)-+$>basisValue b
                     | (b,w) <- enumerate t ]
        $(varP $ mkName "fmapTensor") = bilinearFunction
          $ \(LinearFunction f) (Tensor t)
               -> Tensor $ fmap f t
        $(varP $ mkName "fzipTensorWith") = bilinearFunction
          $ \(LinearFunction f) (Tensor tv, Tensor tw)
               -> Tensor $ liftA2 (curry f) tv tw
        $(varP $ mkName "coerceFmapTensorProduct") = \_ Coercion
          -> error "Cannot yet coerce tensors defined from a `HasBasis` instance. This would require `RoleAnnotations` on `:->:`. Cf. https://gitlab.haskell.org/ghc/ghc/-/issues/8177"
      |]
    return $ tySyns ++ methods
 ]

newtype SpaceFromBasis v = SpaceFromBasis { getSpaceFromBasis :: v }
  deriving newtype (Eq, AdditiveGroup, VectorSpace, HasBasis)

instance AdditiveGroup v => Semimanifold (SpaceFromBasis v) where
  type Needle (SpaceFromBasis v) = SpaceFromBasis v
  type Interior (SpaceFromBasis v) = SpaceFromBasis v
  toInterior = pure
  fromInterior = id
  translateP = Tagged (^+^)
  (.+~^) = (^+^)
  semimanifoldWitness = SemimanifoldWitness BoundarylessWitness

instance AdditiveGroup v => AffineSpace (SpaceFromBasis v) where
  type Diff (SpaceFromBasis v) = SpaceFromBasis v
  (.+^) = (^+^)
  (.-.) = (^-^)

instance AdditiveGroup v => PseudoAffine (SpaceFromBasis v) where
  (.-~!) = (^-^)

instance ∀ v . ( HasBasis v, Num' (Scalar v)
               , Scalar (Scalar v) ~ Scalar v
               , HasTrie (Basis v)
               , Eq v )
     => TensorSpace (SpaceFromBasis v) where
  type TensorProduct (SpaceFromBasis v) w = Basis v :->: w
  wellDefinedVector v
   | v==v       = Just v
   | otherwise  = Nothing
  wellDefinedTensor (Tensor v)
     = fmap (const $ Tensor v) . traverse (wellDefinedVector . snd) $ enumerate v
  zeroTensor = Tensor . trie $ const zeroV
  toFlatTensor = LinearFunction $ Tensor . trie . decompose'
  fromFlatTensor = LinearFunction $ \(Tensor t)
          -> recompose $ enumerate t
  scalarSpaceWitness = ScalarSpaceWitness
  linearManifoldWitness = LinearManifoldWitness BoundarylessWitness
  addTensors (Tensor v) (Tensor w) = Tensor $ (^+^) <$> v <*> w
  subtractTensors (Tensor v) (Tensor w) = Tensor $ (^-^) <$> v <*> w
  tensorProduct = bilinearFunction
    $ \v w -> Tensor . trie $ \bv -> decompose' v bv *^ w
  transposeTensor = LinearFunction $ \(Tensor t)
       -> sumV [ (tensorProduct-+$>w)-+$>basisValue b
               | (b,w) <- enumerate t ]
  fmapTensor = bilinearFunction
    $ \(LinearFunction f) (Tensor t)
         -> Tensor $ fmap f t
  fzipTensorWith = bilinearFunction
    $ \(LinearFunction f) (Tensor tv, Tensor tw)
         -> Tensor $ liftA2 (curry f) tv tw
  coerceFmapTensorProduct _ Coercion
    = error "Cannot yet coerce tensors defined from a `HasBasis` instance. This would require `RoleAnnotations` on `:->:`. Cf. https://gitlab.haskell.org/ghc/ghc/-/issues/8177"



newtype DualVectorFromBasis v = DualVectorFromBasis { getDualVectorFromBasis :: v }
  deriving newtype (Eq, AdditiveGroup, VectorSpace, HasBasis)

instance AdditiveGroup v => Semimanifold (DualVectorFromBasis v) where
  type Needle (DualVectorFromBasis v) = DualVectorFromBasis v
  type Interior (DualVectorFromBasis v) = DualVectorFromBasis v
  toInterior = pure
  fromInterior = id
  translateP = Tagged (^+^)
  (.+~^) = (^+^)
  semimanifoldWitness = SemimanifoldWitness BoundarylessWitness

instance AdditiveGroup v => AffineSpace (DualVectorFromBasis v) where
  type Diff (DualVectorFromBasis v) = DualVectorFromBasis v
  (.+^) = (^+^)
  (.-.) = (^-^)

instance AdditiveGroup v => PseudoAffine (DualVectorFromBasis v) where
  (.-~!) = (^-^)

instance ∀ v . ( HasBasis v, Num' (Scalar v)
               , Scalar (Scalar v) ~ Scalar v
               , HasTrie (Basis v)
               , Eq v )
     => TensorSpace (DualVectorFromBasis v) where
  type TensorProduct (DualVectorFromBasis v) w = Basis v :->: w
  wellDefinedVector v
   | v==v       = Just v
   | otherwise  = Nothing
  wellDefinedTensor (Tensor v)
     = fmap (const $ Tensor v) . traverse (wellDefinedVector . snd) $ enumerate v
  zeroTensor = Tensor . trie $ const zeroV
  toFlatTensor = LinearFunction $ Tensor . trie . decompose'
  fromFlatTensor = LinearFunction $ \(Tensor t)
          -> recompose $ enumerate t
  scalarSpaceWitness = ScalarSpaceWitness
  linearManifoldWitness = LinearManifoldWitness BoundarylessWitness
  addTensors (Tensor v) (Tensor w) = Tensor $ (^+^) <$> v <*> w
  subtractTensors (Tensor v) (Tensor w) = Tensor $ (^-^) <$> v <*> w
  tensorProduct = bilinearFunction
    $ \v w -> Tensor . trie $ \bv -> decompose' v bv *^ w
  transposeTensor = LinearFunction $ \(Tensor t)
       -> sumV [ (tensorProduct-+$>w)-+$>basisValue b
               | (b,w) <- enumerate t ]
  fmapTensor = bilinearFunction
    $ \(LinearFunction f) (Tensor t)
         -> Tensor $ fmap f t
  fzipTensorWith = bilinearFunction
    $ \(LinearFunction f) (Tensor tv, Tensor tw)
         -> Tensor $ liftA2 (curry f) tv tw
  coerceFmapTensorProduct _ Coercion
    = error "Cannot yet coerce tensors defined from a `HasBasis` instance. This would require `RoleAnnotations` on `:->:`. Cf. https://gitlab.haskell.org/ghc/ghc/-/issues/8177"


class ( HasBasis v, Num' (Scalar v)
      , LinearSpace v, DualVector v ~ DualVectorFromBasis v)
    => BasisGeneratedSpace v where
  proveTensorProductIsTrie
    :: ∀ w φ . (TensorProduct v w ~ (Basis v :->: w) => φ) -> φ

instance ∀ v . ( BasisGeneratedSpace v
               , Scalar (Scalar v) ~ Scalar v
               , HasTrie (Basis v)
               , Eq v, Eq (Basis v) )
     => LinearSpace (DualVectorFromBasis v) where
  type DualVector (DualVectorFromBasis v) = v
  dualSpaceWitness = case closedScalarWitness @(Scalar v) of
    ClosedScalarWitness -> DualSpaceWitness
  linearId = proveTensorProductIsTrie @v @(DualVectorFromBasis v)
     (LinearMap . trie $ DualVectorFromBasis . basisValue)
  tensorId = tid
   where tid :: ∀ w . (LinearSpace w, Scalar w ~ Scalar v)
           => (DualVectorFromBasis v⊗w) +> (DualVectorFromBasis v⊗w)
         tid = proveTensorProductIsTrie @v @(DualVector w⊗(DualVectorFromBasis v⊗w))
                    ( case dualSpaceWitness @w of
          DualSpaceWitness -> LinearMap . trie $ Tensor . \i
           -> getTensorProduct $
             (fmapTensor @(DualVector w)
                 -+$>(LinearFunction $ \w -> Tensor . trie
                              $ (\j -> if i==j then w else zeroV)
                               :: DualVectorFromBasis v⊗w))
              -+$> case linearId @w of
                    LinearMap lw -> Tensor lw :: DualVector w⊗w )
  applyDualVector = proveTensorProductIsTrie @v @(DualVectorFromBasis v)
     ( bilinearFunction $ \f (DualVectorFromBasis v)
          -> sum [decompose' f i * vi | (i,vi) <- decompose v] )
  applyLinear = ali
   where ali :: ∀ w . (TensorSpace w, Scalar w~Scalar v)
           => Bilinear (DualVectorFromBasis v +> w) (DualVectorFromBasis v) w
         ali = proveTensorProductIsTrie @v @w ( bilinearFunction
            $ \(LinearMap f) (DualVectorFromBasis v)
                -> sumV [vi *^ untrie f i | (i,vi) <- decompose v] )
  applyTensorFunctional = atf
   where atf :: ∀ u . (LinearSpace u, Scalar u ~ Scalar v)
          => Bilinear (DualVector (DualVectorFromBasis v ⊗ u))
                         (DualVectorFromBasis v ⊗ u) (Scalar v)
         atf = proveTensorProductIsTrie @v @(DualVector u) (case dualSpaceWitness @u of
          DualSpaceWitness -> bilinearFunction
           $ \(LinearMap f) (Tensor t)
             -> sum [ (applyDualVector-+$>fi)-+$>untrie t i
                    | (i, fi) <- enumerate f ]
               )
  applyTensorLinMap = atlm
   where atlm :: ∀ u w . ( LinearSpace u, TensorSpace w
                         , Scalar u ~ Scalar v, Scalar w ~ Scalar v )
                  => Bilinear ((DualVectorFromBasis v ⊗ u) +> w)
                               (DualVectorFromBasis v ⊗ u) w
         atlm = proveTensorProductIsTrie @v @(DualVector u⊗w) (
          case dualSpaceWitness @u of
           DualSpaceWitness -> bilinearFunction
             $ \(LinearMap f) (Tensor t)
              -> sumV [ (applyLinear-+$>(LinearMap fi :: u+>w))
                         -+$> untrie t i
                      | (i, Tensor fi) <- enumerate f ]
          )
  useTupleLinearSpaceComponents = error "Not a tuple type"


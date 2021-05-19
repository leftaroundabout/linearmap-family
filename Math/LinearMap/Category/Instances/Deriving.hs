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
{-# LANGUAGE TupleSections              #-}

module Math.LinearMap.Category.Instances.Deriving
   ( makeLinearSpaceFromBasis, makeFiniteDimensionalFromBasis
   , BasisGeneratedSpace(..) ) where

import Math.LinearMap.Category.Class
import Math.VectorSpace.Docile

import Data.VectorSpace
import Data.AffineSpace
import Data.Basis
import qualified Data.Map as Map
import Data.MemoTrie
import Data.Hashable

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


makeLinearSpaceFromBasis :: Q Type -> DecsQ
makeLinearSpaceFromBasis v = sequence
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
 , InstanceD Nothing [] <$> [t|BasisGeneratedSpace $v|] <*> do
     [d|
        $(varP $ mkName "proveTensorProductIsTrie") = \φ -> φ
      |]
 , InstanceD Nothing [] <$> [t|LinearSpace $v|] <*> do
    tySyns <- sequence [
#if MIN_VERSION_template_haskell(2,15,0)
       error "The TH type of TySynInstD has changed"
#else
       TySynInstD ''DualVector <$> do
         TySynEqn . (:[]) <$> v
           <*> [t| DualVectorFromBasis $v |]
#endif
     ]
    methods <- [d|


        $(varP $ mkName "dualSpaceWitness") = case closedScalarWitness @(Scalar $v) of
             ClosedScalarWitness -> DualSpaceWitness
        $(varP $ mkName "linearId") = LinearMap . trie $ basisValue
        $(varP $ mkName "tensorId") = tid
            where tid :: ∀ w . (LinearSpace w, Scalar w ~ Scalar $v)
                    => ($v⊗w) +> ($v⊗w)
                  tid = case dualSpaceWitness @w of
                   DualSpaceWitness -> LinearMap . trie $ Tensor . \i
                    -> getTensorProduct $
                      (fmapTensor @(DualVector w)
                          -+$>(LinearFunction $ \w -> Tensor . trie
                                       $ (\j -> if i==j then w else zeroV)
                                        :: $v⊗w))
                       -+$> case linearId @w of
                             LinearMap lw -> Tensor lw :: DualVector w⊗w
        $(varP $ mkName "applyDualVector") = bilinearFunction
             $ \(DualVectorFromBasis f) v
                   -> sum [decompose' f i * vi | (i,vi) <- decompose v]
        $(varP $ mkName "applyLinear") = bilinearFunction
             $ \(LinearMap f) v
                   -> sumV [vi *^ untrie f i | (i,vi) <- decompose v]
        $(varP $ mkName "applyTensorFunctional") = atf
            where atf :: ∀ u . (LinearSpace u, Scalar u ~ Scalar $v)
                   => Bilinear (DualVector ($v ⊗ u))
                                  ($v ⊗ u) (Scalar $v)
                  atf = case dualSpaceWitness @u of
                   DualSpaceWitness -> bilinearFunction
                    $ \(LinearMap f) (Tensor t)
                      -> sum [ (applyDualVector-+$>fi)-+$>untrie t i
                             | (i, fi) <- enumerate f ]
        $(varP $ mkName "applyTensorLinMap") = atlm
            where atlm :: ∀ u w . ( LinearSpace u, TensorSpace w
                                  , Scalar u ~ Scalar $v, Scalar w ~ Scalar $v )
                           => Bilinear (($v ⊗ u) +> w) ($v ⊗ u) w
                  atlm = case dualSpaceWitness @u of
                    DualSpaceWitness -> bilinearFunction
                      $ \(LinearMap f) (Tensor t)
                       -> sumV [ (applyLinear-+$>(LinearMap fi :: u+>w))
                                  -+$> untrie t i
                               | (i, Tensor fi) <- enumerate f ]
        $(varP $ mkName "useTupleLinearSpaceComponents") = error "Not a tuple type"

      |]
    return $ tySyns ++ methods
 ]

makeFiniteDimensionalFromBasis :: Q Type -> DecsQ
makeFiniteDimensionalFromBasis v = do
   generalInsts <- makeLinearSpaceFromBasis v
   vtnameHash <- abs . hash . show <$> v
   fdInst <- InstanceD Nothing [] <$> [t|FiniteDimensional $v|] <*> do
    
    -- This is a hack. Ideally, @newName@ should generally globally unique names,
    -- but it doesn't, so we append a hash of the vector space type.
    -- Cf. https://gitlab.haskell.org/ghc/ghc/-/issues/13054
    subBasisCstr <- newName $ "CompleteBasis"++show vtnameHash

    tySyns <- sequence [
#if MIN_VERSION_template_haskell(2,15,0)
       error "The TH type of TySynInstD has changed"
#else
       DataInstD [] ''SubBasis
          <$> ((:[]) <$> v)
          <*> pure Nothing
          <*> pure [NormalC subBasisCstr []]
          <*> pure []
#endif
     ]
    methods <- [d|
        $(varP $ mkName "entireBasis") = $(conE subBasisCstr)
        $(varP $ mkName "enumerateSubBasis") =
            \ $(conP subBasisCstr []) -> basisValue . fst <$> enumerate (trie $ const ())
        $(varP $ mkName "tensorEquality")
          = \(Tensor t) (Tensor t')  -> and [ti == untrie t' i | (i,ti) <- enumerate t]
        $(varP $ mkName "decomposeLinMap") = dlm
           where dlm :: ∀ w . ($v+>w)
                       -> (SubBasis $v, [w]->[w])
                 dlm (LinearMap f) = 
                         ( $(conE subBasisCstr)
                         , (map snd (enumerate f) ++) )
        $(varP $ mkName "decomposeLinMapWithin") = dlm
           where dlm :: ∀ w . SubBasis $v
                        -> ($v+>w)
                        -> Either (SubBasis $v, [w]->[w])
                                  ([w]->[w])
                 dlm $(conP subBasisCstr []) (LinearMap f) = 
                         (Right (map snd (enumerate f) ++) )
        $(varP $ mkName "recomposeSB") = rsb
           where rsb :: SubBasis $v
                        -> [Scalar $v]
                        -> ($v, [Scalar $v])
                 rsb $(conP subBasisCstr []) cs = first recompose
                           $ zipWith' (,) (fst <$> enumerate (trie $ const ())) cs
        $(varP $ mkName "recomposeSBTensor") = rsbt
           where rsbt :: ∀ w . (FiniteDimensional w, Scalar w ~ Scalar $v)
                     => SubBasis $v -> SubBasis w
                        -> [Scalar $v]
                        -> ($v⊗w, [Scalar $v])
                 rsbt $(conP subBasisCstr []) sbw ws = 
                         (first (\iws -> Tensor $ trie (Map.fromList iws Map.!))
                           $ zipConsumeWith' (\i cs' -> first (\c->(i,c))
                                                       $ recomposeSB sbw cs')
                                 (fst <$> enumerate (trie $ const ())) ws)
        $(varP $ mkName "recomposeLinMap") = rlm
           where rlm :: ∀ w . SubBasis $v
                        -> [w]
                        -> ($v+>w, [w])
                 rlm $(conP subBasisCstr []) ws = 
                    (first (\iws -> LinearMap $ trie (Map.fromList iws Map.!))
                      $ zipWith' (,) (fst <$> enumerate (trie $ const ())) ws)
        $(varP $ mkName "recomposeContraLinMap") = rclm
           where rclm :: ∀ w f . (LinearSpace w, Scalar w ~ Scalar $v, Hask.Functor f)
                      => (f (Scalar w) -> w) -> f (DualVectorFromBasis $v)
                        -> ($v+>w)
                 rclm f vs = 
                       (LinearMap $ trie (\i -> f $ fmap (`decompose'`i) vs))
        $(varP $ mkName "recomposeContraLinMapTensor") = rclm
           where rclm :: ∀ u w f
                   . ( FiniteDimensional u, LinearSpace w
                     , Scalar u ~ Scalar $v, Scalar w ~ Scalar $v, Hask.Functor f
                     )
                      => (f (Scalar w) -> w) -> f ($v+>DualVector u)
                        -> (($v⊗u)+>w)
                 rclm f vus = case dualSpaceWitness @u of
                   DualSpaceWitness -> 
                              (
                       (LinearMap $ trie
                           (\i -> case recomposeContraLinMap @u @w @f f
                                      $ fmap (\(LinearMap vu) -> untrie vu (i :: Basis $v)) vus of
                              LinearMap wuff -> Tensor wuff :: DualVector u⊗w )))
        $(varP $ mkName "uncanonicallyFromDual") = LinearFunction getDualVectorFromBasis
        $(varP $ mkName "uncanonicallyToDual") = LinearFunction DualVectorFromBasis

      |]
    return $ tySyns ++ methods
   return $ generalInsts ++ [fdInst]



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


-- | Don't manually instantiate this class, it is just used internally
--   by 'makeLinearSpaceFromBasis'.
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


zipWith' :: (a -> b -> c) -> [a] -> [b] -> ([c], [b])
zipWith' _ _ [] = ([], [])
zipWith' _ [] ys = ([], ys)
zipWith' f (x:xs) (y:ys) = first (f x y :) $ zipWith' f xs ys

zipConsumeWith' :: (a -> [b] -> (c,[b])) -> [a] -> [b] -> ([c], [b])
zipConsumeWith' _ _ [] = ([], [])
zipConsumeWith' _ [] ys = ([], ys)
zipConsumeWith' f (x:xs) ys
    = case f x ys of
       (z, ys') -> first (z :) $ zipConsumeWith' f xs ys'

instance ∀ v . ( BasisGeneratedSpace v, FiniteDimensional v
               , Scalar (Scalar v) ~ Scalar v
               , HasTrie (Basis v), Ord (Basis v)
               , Eq v, Eq (Basis v) )
     => FiniteDimensional (DualVectorFromBasis v) where
  data SubBasis (DualVectorFromBasis v) = CompleteDualVBasis
  entireBasis = CompleteDualVBasis
  enumerateSubBasis CompleteDualVBasis
      = basisValue . fst <$> enumerate (trie $ const ())
  tensorEquality (Tensor t) (Tensor t')
      = and [ti == untrie t' i | (i,ti) <- enumerate t]
  decomposeLinMap = dlm
   where dlm :: ∀ w . (DualVectorFromBasis v+>w)
               -> (SubBasis (DualVectorFromBasis v), [w]->[w])
         dlm (LinearMap f) = proveTensorProductIsTrie @v @w
                 ( CompleteDualVBasis
                 , (map snd (enumerate f) ++) )
  decomposeLinMapWithin = dlm
   where dlm :: ∀ w . SubBasis (DualVectorFromBasis v)
                -> (DualVectorFromBasis v+>w)
                -> Either (SubBasis (DualVectorFromBasis v), [w]->[w])
                          ([w]->[w])
         dlm CompleteDualVBasis (LinearMap f) = proveTensorProductIsTrie @v @w
                 (Right (map snd (enumerate f) ++) )
  recomposeSB = rsb
   where rsb :: SubBasis (DualVectorFromBasis v)
                -> [Scalar v]
                -> (DualVectorFromBasis v, [Scalar v])
         rsb CompleteDualVBasis cs = first recompose
                   $ zipWith' (,) (fst <$> enumerate (trie $ const ())) cs
  recomposeSBTensor = rsbt
   where rsbt :: ∀ w . (FiniteDimensional w, Scalar w ~ Scalar v)
             => SubBasis (DualVectorFromBasis v) -> SubBasis w
                -> [Scalar v]
                -> (DualVectorFromBasis v⊗w, [Scalar v])
         rsbt CompleteDualVBasis sbw ws = proveTensorProductIsTrie @v @w
                 (first (\iws -> Tensor $ trie (Map.fromList iws Map.!))
                   $ zipConsumeWith' (\i cs' -> first (i,) $ recomposeSB sbw cs')
                         (fst <$> enumerate (trie $ const ())) ws)
  recomposeLinMap = rlm
   where rlm :: ∀ w . SubBasis (DualVectorFromBasis v)
                -> [w]
                -> (DualVectorFromBasis v+>w, [w])
         rlm CompleteDualVBasis ws = proveTensorProductIsTrie @v @w
                 (first (\iws -> LinearMap $ trie (Map.fromList iws Map.!))
                   $ zipWith' (,) (fst <$> enumerate (trie $ const ())) ws)
  recomposeContraLinMap = rclm
   where rclm :: ∀ w f . (LinearSpace w, Scalar w ~ Scalar v, Hask.Functor f)
              => (f (Scalar w) -> w) -> f v
                -> (DualVectorFromBasis v+>w)
         rclm f vs = proveTensorProductIsTrie @v @w
               (LinearMap $ trie (\i -> f $ fmap (`decompose'`i) vs))
  recomposeContraLinMapTensor = rclm
   where rclm :: ∀ u w f
           . ( FiniteDimensional u, LinearSpace w
             , Scalar u ~ Scalar v, Scalar w ~ Scalar v, Hask.Functor f
             )
              => (f (Scalar w) -> w) -> f (DualVectorFromBasis v+>DualVector u)
                -> ((DualVectorFromBasis v⊗u)+>w)
         rclm f vus = case dualSpaceWitness @u of
           DualSpaceWitness -> proveTensorProductIsTrie @v @(DualVector u)
                      (proveTensorProductIsTrie @v @(DualVector u⊗w)
               (LinearMap $ trie
                   (\i -> case recomposeContraLinMap @u @w @f f
                              $ fmap (\(LinearMap vu) -> untrie vu (i :: Basis v)) vus of
                      LinearMap wuff -> Tensor wuff :: DualVector u⊗w )))
  uncanonicallyFromDual = LinearFunction DualVectorFromBasis
  uncanonicallyToDual = LinearFunction getDualVectorFromBasis


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
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE PatternSynonyms            #-}

module Math.LinearMap.Category.Instances.Deriving
   ( makeLinearSpaceFromBasis, makeFiniteDimensionalFromBasis
   -- * The instantiated classes
   , AffineSpace(..), Semimanifold(..), PseudoAffine(..)
   , TensorSpace(..), LinearSpace(..), FiniteDimensional(..), SemiInner(..)
   -- * Internals
   , BasisGeneratedSpace(..), LinearSpaceFromBasisDerivationConfig, def ) where

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
import qualified Data.Kind as Kind
import Data.Traversable (traverse)
import Data.Default.Class

import Math.Manifold.Core.PseudoAffine
import Math.LinearMap.Asserted
import Math.VectorSpace.ZeroDimensional
import Data.VectorSpace.Free

import Language.Haskell.TH

-- | Given a type @V@ that is already a 'VectorSpace' and 'HasBasis', generate
--   the other class instances that are needed to use the type with this
--   library.
--
--   Prerequisites: (these can often be derived automatically,
--   using either the @newtype@ \/ @via@ strategy or generics \/ anyclass)
--
-- @
-- instance 'AdditiveGroup' V
--
-- instance 'VectorSpace' V where
--   type Scalar V = -- a simple number type, usually 'Double'
--
-- instance 'HasBasis' V where
--   type Basis V = -- a type with an instance of 'HasTrie'
-- @
--
--   Note that the 'Basis' does /not/ need to be orthonormal – in fact it
--   is not necessary to have a scalar product (i.e. an 'InnerSpace' instance)
--   at all.
--
--   The macro, invoked like
-- @
-- makeLinearSpaceFromBasis [t| V |]
-- @
--
--   will then generate @V@-instances for the classes 'Semimanifold',
--   'PseudoAffine', 'AffineSpace', 'TensorSpace' and 'LinearSpace'.
--
--   It also works on parameterised types, in that case you need to use
--   universal-quantification syntax, e.g.
--
-- @
-- makeLinearSpaceFromBasis [t| ∀ n . (KnownNat n) => V n |]
-- @
makeLinearSpaceFromBasis :: Q Type -> DecsQ
makeLinearSpaceFromBasis v
   = makeLinearSpaceFromBasis' def $ deQuantifyType v

data LinearSpaceFromBasisDerivationConfig = LinearSpaceFromBasisDerivationConfig
instance Default LinearSpaceFromBasisDerivationConfig where
  def = LinearSpaceFromBasisDerivationConfig

-- | More general version of 'makeLinearSpaceFromBasis', that can be used with
--   parameterised types.
makeLinearSpaceFromBasis' :: LinearSpaceFromBasisDerivationConfig
                -> Q (Cxt, Type) -> DecsQ
makeLinearSpaceFromBasis' _ cxtv = do
 (cxt,v) <- do
   (cxt', v') <- cxtv
   return (pure cxt', pure v')
 
 exts <- extsEnabled
 if not $ all (`elem`exts) [TypeFamilies, ScopedTypeVariables, TypeApplications]
   then reportError "This macro requires -XTypeFamilies, -XScopedTypeVariables and -XTypeApplications."
   else pure ()
 
 sequence
  [ InstanceD Nothing <$> cxt <*> [t|Semimanifold $v|] <*> [d|
         type instance Needle $v = $v
#if !MIN_VERSION_manifolds_core(0,6,0)
         type instance Interior $v = $v
         $(varP 'toInterior) = pure
         $(varP 'fromInterior) = id
         $(varP 'translateP) = Tagged (^+^)
         $(varP 'semimanifoldWitness) = SemimanifoldWitness BoundarylessWitness
#endif
         $(varP '(.+~^)) = (^+^)
      |]
  , InstanceD Nothing <$> cxt <*> [t|PseudoAffine $v|] <*> do
      [d|
         $(varP '(.-~!)) = (^-^)
         $(varP '(.-~.)) = \p q -> pure (p^-^q)
       |]
  , InstanceD Nothing <$> cxt <*> [t|AffineSpace $v|] <*> [d|
         type instance Diff $v = $v
         $(varP '(.+^)) = (^+^)
         $(varP '(.-.)) = (^-^)
       |]
  , InstanceD Nothing <$> cxt <*> [t|TensorSpace $v|] <*> [d|
         type instance TensorProduct $v w = Basis $v :->: w
         $(varP 'wellDefinedVector) = \v
            -> if v==v then Just v else Nothing
         $(varP 'wellDefinedTensor) = \(Tensor v)
            -> fmap (const $ Tensor v) . traverse (wellDefinedVector . snd) $ enumerate v
         $(varP 'zeroTensor) = Tensor . trie $ const zeroV
         $(varP 'toFlatTensor) = LinearFunction $ Tensor . trie . decompose'
         $(varP 'fromFlatTensor) = LinearFunction $ \(Tensor t)
                 -> recompose $ enumerate t
         $(varP 'scalarSpaceWitness) = ScalarSpaceWitness
         $(varP 'linearManifoldWitness) = LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
                                 BoundarylessWitness
#endif
         $(varP 'addTensors) = \(Tensor v) (Tensor w)
             -> Tensor $ (^+^) <$> v <*> w
         $(varP 'subtractTensors) = \(Tensor v) (Tensor w)
             -> Tensor $ (^-^) <$> v <*> w
         $(varP 'tensorProduct) = bilinearFunction
           $ \v w -> Tensor . trie $ \bv -> decompose' v bv *^ w
         $(varP 'transposeTensor) = LinearFunction $ \(Tensor t)
              -> sumV [ (tensorProduct-+$>w)-+$>basisValue b
                      | (b,w) <- enumerate t ]
         $(varP 'fmapTensor) = bilinearFunction
           $ \(LinearFunction f) (Tensor t)
                -> Tensor $ fmap f t
         $(varP 'fzipTensorWith) = bilinearFunction
           $ \(LinearFunction f) (Tensor tv, Tensor tw)
                -> Tensor $ liftA2 (curry f) tv tw
         $(varP 'coerceFmapTensorProduct) = \_ Coercion
           -> error "Cannot yet coerce tensors defined from a `HasBasis` instance. This would require `RoleAnnotations` on `:->:`. Cf. https://gitlab.haskell.org/ghc/ghc/-/issues/8177"
       |]
  , InstanceD Nothing <$> cxt <*> [t|BasisGeneratedSpace $v|] <*> do
      [d|
         $(varP 'proveTensorProductIsTrie) = \φ -> φ
       |]
  , InstanceD Nothing <$> cxt <*> [t|LinearSpace $v|] <*> [d|
         type instance DualVector $v = DualVectorFromBasis $v
         $(varP 'dualSpaceWitness) = case closedScalarWitness @(Scalar $v) of
              ClosedScalarWitness -> DualSpaceWitness
         $(varP 'linearId) = LinearMap . trie $ basisValue
         $(varP 'tensorId) = tid
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
         $(varP 'applyDualVector) = bilinearFunction
              $ \(DualVectorFromBasis f) v
                    -> sum [decompose' f i * vi | (i,vi) <- decompose v]
         $(varP 'applyLinear) = bilinearFunction
              $ \(LinearMap f) v
                    -> sumV [vi *^ untrie f i | (i,vi) <- decompose v]
         $(varP 'applyTensorFunctional) = atf
             where atf :: ∀ u . (LinearSpace u, Scalar u ~ Scalar $v)
                    => Bilinear (DualVector ($v ⊗ u))
                                   ($v ⊗ u) (Scalar $v)
                   atf = case dualSpaceWitness @u of
                    DualSpaceWitness -> bilinearFunction
                     $ \(LinearMap f) (Tensor t)
                       -> sum [ (applyDualVector-+$>fi)-+$>untrie t i
                              | (i, fi) <- enumerate f ]
         $(varP 'applyTensorLinMap) = atlm
             where atlm :: ∀ u w . ( LinearSpace u, TensorSpace w
                                   , Scalar u ~ Scalar $v, Scalar w ~ Scalar $v )
                            => Bilinear (($v ⊗ u) +> w) ($v ⊗ u) w
                   atlm = case dualSpaceWitness @u of
                     DualSpaceWitness -> bilinearFunction
                       $ \(LinearMap f) (Tensor t)
                        -> sumV [ (applyLinear-+$>(LinearMap fi :: u+>w))
                                   -+$> untrie t i
                                | (i, Tensor fi) <- enumerate f ]
         $(varP 'useTupleLinearSpaceComponents) = \_ -> usingNonTupleTypeAsTupleError
 
       |]
  ]

data FiniteDimensionalFromBasisDerivationConfig
         = FiniteDimensionalFromBasisDerivationConfig
instance Default FiniteDimensionalFromBasisDerivationConfig where
  def = FiniteDimensionalFromBasisDerivationConfig

-- | Like 'makeLinearSpaceFromBasis', but additionally generate instances for
--   'FiniteDimensional' and 'SemiInner'.
makeFiniteDimensionalFromBasis :: Q Type -> DecsQ
makeFiniteDimensionalFromBasis v
   = makeFiniteDimensionalFromBasis' def $ deQuantifyType v

makeFiniteDimensionalFromBasis' :: FiniteDimensionalFromBasisDerivationConfig
              -> Q (Cxt, Type) -> DecsQ
makeFiniteDimensionalFromBasis' _ cxtv = do
 generalInsts <- makeLinearSpaceFromBasis' def cxtv
 (cxt,v) <- do
   (cxt', v') <- cxtv
   return (pure cxt', pure v')
 vtnameHash <- abs . hash . show <$> v
 
 fdInsts <- sequence
  [ InstanceD Nothing <$> cxt <*> [t|FiniteDimensional $v|] <*> do
    
    -- This is a hack. Ideally, @newName@ should generate globally unique names,
    -- but it doesn't, so we append a hash of the vector space type.
    -- Cf. https://gitlab.haskell.org/ghc/ghc/-/issues/13054
    subBasisCstr <- newName $ "CompleteBasis"++show vtnameHash

    tySyns <- sequence [
#if MIN_VERSION_template_haskell(2,15,0)
       DataInstD [] Nothing
          <$> (AppT (ConT ''SubBasis) <$> v)
          <*> pure Nothing
          <*> pure [NormalC subBasisCstr []]
          <*> pure []
#else
       DataInstD [] ''SubBasis
          <$> ((:[]) <$> v)
          <*> pure Nothing
          <*> pure [NormalC subBasisCstr []]
          <*> pure []
#endif
     ]
    methods <- [d|
        $(varP 'entireBasis) = $(conE subBasisCstr)
        $(varP 'enumerateSubBasis) =
            \ $(conP subBasisCstr []) -> basisValue . fst <$> enumerate (trie $ const ())
        $(varP 'tensorEquality)
          = \(Tensor t) (Tensor t')  -> and [ti == untrie t' i | (i,ti) <- enumerate t]
        $(varP 'decomposeLinMap) = dlm
           where dlm :: ∀ w . ($v+>w)
                       -> (SubBasis $v, [w]->[w])
                 dlm (LinearMap f) = 
                         ( $(conE subBasisCstr)
                         , (map snd (enumerate f) ++) )
        $(varP 'decomposeLinMapWithin) = dlm
           where dlm :: ∀ w . SubBasis $v
                        -> ($v+>w)
                        -> Either (SubBasis $v, [w]->[w])
                                  ([w]->[w])
                 dlm $(conP subBasisCstr []) (LinearMap f) = 
                         (Right (map snd (enumerate f) ++) )
        $(varP 'recomposeSB) = rsb
           where rsb :: SubBasis $v
                        -> [Scalar $v]
                        -> ($v, [Scalar $v])
                 rsb $(conP subBasisCstr []) cs = first recompose
                           $ zipWith' (,) (fst <$> enumerate (trie $ const ())) cs
        $(varP 'recomposeSBTensor) = rsbt
           where rsbt :: ∀ w . (FiniteDimensional w, Scalar w ~ Scalar $v)
                     => SubBasis $v -> SubBasis w
                        -> [Scalar $v]
                        -> ($v⊗w, [Scalar $v])
                 rsbt $(conP subBasisCstr []) sbw ws = 
                         (first (\iws -> Tensor $ trie (Map.fromList iws Map.!))
                           $ zipConsumeWith' (\i cs' -> first (\c->(i,c))
                                                       $ recomposeSB sbw cs')
                                 (fst <$> enumerate (trie $ const ())) ws)
        $(varP 'recomposeLinMap) = rlm
           where rlm :: ∀ w . SubBasis $v
                        -> [w]
                        -> ($v+>w, [w])
                 rlm $(conP subBasisCstr []) ws = 
                    (first (\iws -> LinearMap $ trie (Map.fromList iws Map.!))
                      $ zipWith' (,) (fst <$> enumerate (trie $ const ())) ws)
        $(varP 'recomposeContraLinMap) = rclm
           where rclm :: ∀ w f . (LinearSpace w, Scalar w ~ Scalar $v, Hask.Functor f)
                      => (f (Scalar w) -> w) -> f (DualVectorFromBasis $v)
                        -> ($v+>w)
                 rclm f vs = 
                       (LinearMap $ trie (\i -> f $ fmap (`decompose'`i) vs))
        $(varP 'recomposeContraLinMapTensor) = rclm
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
        $(varP 'uncanonicallyFromDual) = LinearFunction getDualVectorFromBasis
        $(varP 'uncanonicallyToDual) = LinearFunction DualVectorFromBasis

      |]
    return $ tySyns ++ methods
  , InstanceD Nothing <$> cxt <*> [t|SemiInner $v|] <*> do
     [d|
        $(varP 'dualBasisCandidates)
           = cartesianDualBasisCandidates
               (enumerateSubBasis CompleteDualVBasis)
               (\v -> map (abs . realToFrac . decompose' v . fst)
                       $ enumerate (trie $ const ()) )
      |]
  ]
 return $ generalInsts ++ fdInsts


deQuantifyType :: Q Type -> Q (Cxt, Type)
deQuantifyType t = do
   t' <- t
   return $ case t' of
     ForallT _ cxt instT -> (cxt, instT)
     _ -> ([], t')


newtype DualVectorFromBasis v = DualVectorFromBasis { getDualVectorFromBasis :: v }
  deriving newtype (Eq, AdditiveGroup, VectorSpace, HasBasis)

instance AdditiveGroup v => Semimanifold (DualVectorFromBasis v) where
  type Needle (DualVectorFromBasis v) = DualVectorFromBasis v
#if !MIN_VERSION_manifolds_core(0,6,0)
  type Interior (DualVectorFromBasis v) = DualVectorFromBasis v
  toInterior = pure
  fromInterior = id
  translateP = Tagged (^+^)
  semimanifoldWitness = SemimanifoldWitness BoundarylessWitness
#endif
  (.+~^) = (^+^)

instance AdditiveGroup v => AffineSpace (DualVectorFromBasis v) where
  type Diff (DualVectorFromBasis v) = DualVectorFromBasis v
  (.+^) = (^+^)
  (.-.) = (^-^)

instance AdditiveGroup v => PseudoAffine (DualVectorFromBasis v) where
  (.-~!) = (^-^)
  p.-~.q = pure (p^-^q)

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
  linearManifoldWitness = LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
        BoundarylessWitness
#endif
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


-- | Do not manually instantiate this class. It is used internally
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
  useTupleLinearSpaceComponents _ = usingNonTupleTypeAsTupleError


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


instance ∀ v . ( BasisGeneratedSpace v, FiniteDimensional v
               , Real (Scalar v), Scalar (Scalar v) ~ Scalar v
               , HasTrie (Basis v), Ord (Basis v)
               , Eq v, Eq (Basis v) )
     => SemiInner (DualVectorFromBasis v) where
  dualBasisCandidates = cartesianDualBasisCandidates
          (enumerateSubBasis entireBasis)
          (\v -> map (abs . realToFrac . decompose' v . fst)
                  $ enumerate (trie $ const ()) )


newtype AbstractDualVector a c
           = AbstractDualVector_ { getConcreteDualVector :: DualVector c }
deriving newtype instance (Eq (DualVector c)) => Eq (AbstractDualVector a c)

class ( Coercible v (VectorSpaceImplementation v)
      , DualVector v
          ~ AbstractDualVector v (VectorSpaceImplementation v) )
        => AbstractVectorSpace v where
  type VectorSpaceImplementation v :: Kind.Type
  scalarsSameInAbstraction
    :: ( ( Scalar (VectorSpaceImplementation v) ~ Scalar v
         , Scalar (DualVector v) ~ Scalar v
         , Scalar (DualVector (VectorSpaceImplementation v)) ~ Scalar v )
         => ρ ) -> ρ
  abstractTensorProductsCoercion
    :: TensorSpace w => Coercion (TensorProduct v w)
                                 (TensorProduct (VectorSpaceImplementation v) w)

abstractTensorsCoercion :: ∀ a c w
  . ( AbstractVectorSpace a, LinearSpace c
    , c ~ VectorSpaceImplementation a, TensorSpace w )
      => Coercion (AbstractDualVector a c⊗w) (DualVector c⊗w)
abstractTensorsCoercion = Coercion

abstractLinmapCoercion :: ∀ a c w
  . ( AbstractVectorSpace a, LinearSpace c
    , c ~ VectorSpaceImplementation a, TensorSpace w )
      => Coercion (AbstractDualVector a c+>w) (DualVector c+>w)
abstractLinmapCoercion = case ( dualSpaceWitness @c
                              , abstractTensorProductsCoercion @a @w ) of
   (DualSpaceWitness, Coercion) -> Coercion

coerceLinearMapCodomain :: ∀ v w x . ( LinearSpace v, Coercible w x )
         => (v+>w) -> (v+>x)
coerceLinearMapCodomain = case dualSpaceWitness @v of
 DualSpaceWitness -> \(LinearMap m)
     -> LinearMap $ (coerceFmapTensorProduct ([]::[DualVector v])
                            (Coercion :: Coercion w x) $ m)

instance (Show (DualVector c)) => Show (AbstractDualVector a c) where
  showsPrec p (AbstractDualVector_ φ) = showParen (p>10)
       $ ("AbstractDualVector "++) . showsPrec 11 φ

instance ∀ a c . ( AbstractVectorSpace a, VectorSpaceImplementation a ~ c
                 , AdditiveGroup (DualVector c) )
     => AdditiveGroup (AbstractDualVector a c) where
  zeroV = AbstractDualVector zeroV
  (^+^) = coerce ((^+^) @(DualVector c))
  negateV = coerce (negateV @(DualVector c))

instance ∀ a c . (AbstractVectorSpace a, VectorSpaceImplementation a ~ c
                 , AdditiveGroup (DualVector c))
     => AffineSpace (AbstractDualVector a c) where
  type Diff (AbstractDualVector a c) = AbstractDualVector a c
  (.+^) = coerce ((^+^) @(DualVector c))
  (.-.) = coerce ((^-^) @(DualVector c))

instance ∀ a c . ( AbstractVectorSpace a, VectorSpaceImplementation a ~ c
                 , AdditiveGroup (DualVector c) )
     => Semimanifold (AbstractDualVector a c) where
  type Needle (AbstractDualVector a c) = AbstractDualVector a c
  (.+~^) = (^+^)

instance ∀ a c . ( AbstractVectorSpace a, VectorSpaceImplementation a ~ c
                 , AdditiveGroup (DualVector c) )
     => PseudoAffine (AbstractDualVector a c) where
  v.-~.w = pure (v^-^w)
  (.-~!) = (^-^)

instance ∀ a c . ( AbstractVectorSpace a, VectorSpaceImplementation a ~ c
                 , VectorSpace (DualVector c) )
     => VectorSpace (AbstractDualVector a c) where
  type Scalar (AbstractDualVector a c) = Scalar a
  (*^) = scalarsSameInAbstraction @a (coerce ((*^) @(DualVector c)))

instance ∀ a c . ( AbstractVectorSpace a, VectorSpaceImplementation a ~ c
                 , TensorSpace (DualVector c) )
     => TensorSpace (AbstractDualVector a c) where
  type TensorProduct (AbstractDualVector a c) w
          = TensorProduct (DualVector c) w
  scalarSpaceWitness = scalarsSameInAbstraction @a
     (case scalarSpaceWitness @(DualVector c) of ScalarSpaceWitness -> ScalarSpaceWitness)
  linearManifoldWitness = scalarsSameInAbstraction @a
     (case linearManifoldWitness @(DualVector c) of
       LinearManifoldWitness -> LinearManifoldWitness)
  zeroTensor = zt
   where zt :: ∀ w . (TensorSpace w, Scalar w ~ Scalar a)
            => (AbstractDualVector a c ⊗ w)
         zt = scalarsSameInAbstraction @a
                (coerce (zeroTensor @(DualVector c) @w))
  addTensors = at
   where at :: ∀ w . (TensorSpace w, Scalar w ~ Scalar a)
            => (AbstractDualVector a c ⊗ w) -> (AbstractDualVector a c ⊗ w)
                                            -> (AbstractDualVector a c ⊗ w)
         at = scalarsSameInAbstraction @a
                (coerce (addTensors @(DualVector c) @w))
  subtractTensors = st
   where st :: ∀ w . (TensorSpace w, Scalar w ~ Scalar a)
            => (AbstractDualVector a c ⊗ w) -> (AbstractDualVector a c ⊗ w)
                                            -> (AbstractDualVector a c ⊗ w)
         st = scalarsSameInAbstraction @a
                (coerce (subtractTensors @(DualVector c) @w))
  negateTensor = nt
   where nt :: ∀ w . (TensorSpace w, Scalar w ~ Scalar a)
            => (AbstractDualVector a c ⊗ w) -+> (AbstractDualVector a c ⊗ w)
         nt = scalarsSameInAbstraction @a
                (coerce (negateTensor @(DualVector c) @w))
  scaleTensor = st
   where st :: ∀ w . (TensorSpace w, Scalar w ~ Scalar a)
            => Bilinear (Scalar a) (AbstractDualVector a c ⊗ w)
                                   (AbstractDualVector a c ⊗ w)
         st = scalarsSameInAbstraction @a
                (coerce (scaleTensor @(DualVector c) @w))
  toFlatTensor = scalarsSameInAbstraction @a
                    ( coerce (toFlatTensor @(DualVector c)) )
  fromFlatTensor = scalarsSameInAbstraction @a
                    ( coerce (fromFlatTensor @(DualVector c)) )
  tensorProduct = tp
   where tp :: ∀ w . (TensorSpace w, Scalar w ~ Scalar a)
            => Bilinear (AbstractDualVector a c) w
                                   (AbstractDualVector a c ⊗ w)
         tp = scalarsSameInAbstraction @a
                (coerce (tensorProduct @(DualVector c) @w))
  wellDefinedVector (AbstractDualVector v) = AbstractDualVector <$> wellDefinedVector v
  wellDefinedTensor = wdt
   where wdt :: ∀ w . (TensorSpace w, Scalar w ~ Scalar a)
            => (AbstractDualVector a c ⊗ w) -> Maybe (AbstractDualVector a c ⊗ w)
         wdt = scalarsSameInAbstraction @a
                (coerce (wellDefinedTensor @(DualVector c) @w))
  transposeTensor = LinearFunction tt
   where tt :: ∀ w . (TensorSpace w, Scalar w ~ Scalar a)
            => (AbstractDualVector a c ⊗ w) -> (w ⊗ AbstractDualVector a c) 
         tt t = Tensor $ coerceFmapTensorProduct ([] :: [w])
                (Coercion @(DualVector c) @(AbstractDualVector a c))
               $ getTensorProduct ( scalarsSameInAbstraction @a
                   (transposeTensor $ coerce t)
                           :: w ⊗ (DualVector c) )
  fmapTensor = ft
   where ft :: ∀ w x . ( TensorSpace w, Scalar w ~ Scalar a
                       , TensorSpace x, Scalar x ~ Scalar a )
           => Bilinear (w-+>x) (AbstractDualVector a c ⊗ w) (AbstractDualVector a c ⊗ x) 
         ft = scalarsSameInAbstraction @a
                 (coerce $ fmapTensor @(DualVector c) @w @x)
  fzipTensorWith = ft
   where ft :: ∀ u w x . ( TensorSpace w, Scalar w ~ Scalar a
                         , TensorSpace u, Scalar u ~ Scalar a
                         , TensorSpace x, Scalar x ~ Scalar a )
           => Bilinear ((w,x)-+>u)
                       (AbstractDualVector a c ⊗ w, AbstractDualVector a c ⊗ x)
                       (AbstractDualVector a c ⊗ u) 
         ft = scalarsSameInAbstraction @a
                 (coerce $ fzipTensorWith @(DualVector c) @u @w @x)
  coerceFmapTensorProduct _ = coerceFmapTensorProduct ([]::[DualVector c])

witnessAbstractDualVectorTensorSpacyness
  :: ∀ a c r . ( AbstractVectorSpace a, VectorSpaceImplementation a ~ c
               , LinearSpace a, LinearSpace c
               , TensorSpace (DualVector c), Num (Scalar a) )
    => (( TensorSpace (AbstractDualVector a c)
        , LinearSpace (DualVector c)
        , Scalar (DualVector c) ~ Scalar a )
            => r) -> r
witnessAbstractDualVectorTensorSpacyness φ = case dualSpaceWitness @c of
   DualSpaceWitness -> scalarsSameInAbstraction @a φ

instance ∀ a c . ( AbstractVectorSpace a, VectorSpaceImplementation a ~ c
                 , LinearSpace a, LinearSpace c
                 , TensorSpace (DualVector c), Num (Scalar a) )
     => LinearSpace (AbstractDualVector a c) where
  type DualVector (AbstractDualVector a c) = a
  dualSpaceWitness = case (dualSpaceWitness @c, scalarSpaceWitness @c) of
    (DualSpaceWitness, ScalarSpaceWitness)
        -> scalarsSameInAbstraction @a DualSpaceWitness
  linearId = witnessAbstractDualVectorTensorSpacyness @a @c
       (sym (abstractLinmapCoercion @a)
           $ sampleLinearFunction @(DualVector c)
           -+$> linearFunction AbstractDualVector)
  tensorId = tid
   where tid :: ∀ w . (LinearSpace w, Scalar w ~ Scalar a)
            => (AbstractDualVector a c ⊗ w) +> (AbstractDualVector a c ⊗ w) 
         tid = case ( dualSpaceWitness @w, dualSpaceWitness @c ) of
          (DualSpaceWitness, DualSpaceWitness)
            -> witnessAbstractDualVectorTensorSpacyness @a (
                let LinearMap ida = linearId :: (DualVector c ⊗ w) +> (DualVector c ⊗ w)
                in LinearMap $ 
                    sym (abstractTensorProductsCoercion @a
                          @(DualVector w ⊗ (AbstractDualVector a c⊗w)) )
                    . coerceFmapTensorProduct ([]::[c ⊗ DualVector w])
                       (Coercion @(DualVector c ⊗ w) @(AbstractDualVector a c ⊗ w))
                    $ ida )
  applyDualVector = scalarsSameInAbstraction @a ( bilinearFunction
     $ \v (AbstractDualVector d) -> (applyDualVector -+$> d)-+$>(coerce v::c) )
  applyLinear = witnessAbstractDualVectorTensorSpacyness @a ( LinearFunction
     $ \f -> (applyLinear -+$> abstractLinmapCoercion $ f) . LinearFunction coerce
      )
  applyTensorFunctional = atf
   where atf :: ∀ u . ( LinearSpace u, Scalar u ~ Scalar a )
                  => Bilinear (DualVector (AbstractDualVector a c⊗u))
                                       (AbstractDualVector a c⊗u) (Scalar a)
         atf = case (scalarSpaceWitness @a, dualSpaceWitness @u) of
          (ScalarSpaceWitness, DualSpaceWitness)
            -> witnessAbstractDualVectorTensorSpacyness @a (
                LinearFunction $ \f
                 -> (applyTensorFunctional @(DualVector c)
                         -+$> abstractLinmapCoercion @a $ f)
                      . LinearFunction (abstractTensorsCoercion @a $)
              )
  applyTensorLinMap = atlm
   where atlm :: ∀ u w . ( LinearSpace u, Scalar u ~ Scalar a
                         , TensorSpace w, Scalar w ~ Scalar a )
                  => Bilinear ((AbstractDualVector a c⊗u)+>w)
                                       (AbstractDualVector a c⊗u) w
         atlm = case (dualSpaceWitness @c, dualSpaceWitness @u) of
          (DualSpaceWitness, DualSpaceWitness)
                      -> witnessAbstractDualVectorTensorSpacyness @a (
             LinearFunction $ \(LinearMap f) ->
                     let f' = LinearMap (abstractTensorProductsCoercion
                                           @a @((Tensor (Scalar a) (DualVector u) w))
                                          $ coerce f) :: (DualVector c⊗u)+>w
                     in (applyTensorLinMap @(DualVector c)-+$>f')
                              . LinearFunction (abstractTensorsCoercion @a $)
           )
  useTupleLinearSpaceComponents = \_ -> usingNonTupleTypeAsTupleError

pattern AbstractDualVector
    :: AbstractVectorSpace v => DualVector (VectorSpaceImplementation v) -> DualVector v
pattern AbstractDualVector φ = AbstractDualVector_ φ


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
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE DataKinds                  #-}
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
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE PatternSynonyms            #-}

module Math.LinearMap.Category.Instances.Deriving
   ( makeLinearSpaceFromBasis, makeFiniteDimensionalFromBasis
   , copyNewtypeInstances, pattern AbstractDualVector
   -- * The instantiated classes
   , AffineSpace(..), Semimanifold(..), PseudoAffine(..)
   , TensorSpace(..), LinearSpace(..), FiniteDimensional(..), SemiInner(..)
   -- * Internals
   , BasisGeneratedSpace(..), LinearSpaceFromBasisDerivationConfig, def
   ) where

import Math.LinearMap.Category.Class
import Math.LinearMap.Category.Instances
import Math.VectorSpace.DimensionAware
import Math.VectorSpace.Docile

import Data.VectorSpace
import Data.AffineSpace
import Data.Basis
import qualified Data.Map as Map
import Data.Tree (Forest)
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

import GHC.Generics (Generic)
import GHC.TypeLits (Nat, KnownNat)

#if MIN_VERSION_singletons(3,0,0)
import GHC.TypeLits.Singletons (withKnownNat)
import Prelude.Singletons
#else
import Data.Singletons.TypeLits (withKnownNat)
import Data.Singletons.Prelude
#endif
    (SingI, sing, withSingI, SMaybe(..))
import qualified Math.VectorSpace.DimensionAware.Theorems.MaybeNat as Maybe

import Language.Haskell.TH
import Language.Haskell.TH.Syntax (Name(..), OccName(..)
#if MIN_VERSION_template_haskell(2,17,0)
           , Specificity(..)
#endif
           )
import qualified Language.Haskell.TH.Datatype as D

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

data LinearSpaceFromBasisDerivationConfig
  = LinearSpaceFromBasisDerivationConfig
      { _treatBasisAsFinite :: Bool
      }
instance Default LinearSpaceFromBasisDerivationConfig where
  def = LinearSpaceFromBasisDerivationConfig
      { _treatBasisAsFinite = False }


requireExtensions :: [Extension] -> Q ()
requireExtensions reqExts = do
  exts <- extsEnabled
  forM_ reqExts $ \re -> do
    if re`elem`exts
     then return ()
     else reportError $ "This macro requires -X"++show re++"."

-- | More general version of 'makeLinearSpaceFromBasis', that can be used with
--   parameterised types.
makeLinearSpaceFromBasis' :: LinearSpaceFromBasisDerivationConfig
                -> Q ([TyVarBndr
#if MIN_VERSION_template_haskell(2,17,0)
                        Specificity
#endif
                          ], Cxt, Type) -> DecsQ
makeLinearSpaceFromBasis' config cxtv = do
 (cxt,v) <- do
   (_, cxt', v') <- cxtv
   return (pure cxt', pure v')
 
 requireExtensions [ TypeFamilies, MultiParamTypeClasses
                   , ScopedTypeVariables, TypeApplications ]
 
 sequence (
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
  , if _treatBasisAsFinite config
     then InstanceD Nothing <$> cxt <*> [t|DimensionAware $v|] <*> [d|
         type instance StaticDimension $v = Cardinality (Basis $v)
         $(varP 'dimensionalityWitness) = IsStaticDimensional
       |]
     else InstanceD Nothing <$> cxt <*> [t|DimensionAware $v|] <*> [d|
         type instance StaticDimension $v = 'Nothing
         $(varP 'dimensionalityWitness) = IsFlexibleDimensional
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
         $(varP 'coerceFmapTensorProduct) = \_ VSCCoercion
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
  ] ++ if _treatBasisAsFinite config then [do
     dim <- pure . VarT <$> newName "n"
     InstanceD Nothing <$> ((:)<$>[t|Cardinality (Basis $v) ~ 'Just $dim|]<*>cxt)
                 <*> [t|Dimensional $dim $v|] <*> [d|
       |]]
    else []
   )

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
              -> Q ([TyVarBndr
#if MIN_VERSION_template_haskell(2,17,0)
                        Specificity
#endif
                       ], Cxt, Type) -> DecsQ
makeFiniteDimensionalFromBasis' _ cxtv = do
 generalInsts <- makeLinearSpaceFromBasis' def{_treatBasisAsFinite=True} cxtv
 (cxt,v) <- do
   (_, cxt', v') <- cxtv
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


deQuantifyType :: Q Type -> Q ([TyVarBndr
#if MIN_VERSION_template_haskell(2,17,0)
                                 Specificity
#endif
                                ], Cxt, Type)
deQuantifyType t = do
   t' <- t
   return $ case t' of
     ForallT tvbs cxt instT -> (tvbs, cxt, instT)
     _ -> ([], [], t')


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

type family Cardinality b :: Maybe Nat

type instance Cardinality () = 'Just 1
type instance Cardinality (Either a b)
         = Maybe.ZipWithPlus (Cardinality a) (Cardinality b)
type instance Cardinality (a,b)
         = Maybe.ZipWithTimes (Cardinality a) (Cardinality b)

instance (HasBasis v, SingI (Cardinality (Basis v)))
              => DimensionAware (DualVectorFromBasis v) where
  type StaticDimension (DualVectorFromBasis v) = Cardinality (Basis v)
  dimensionalityWitness = case sing @(Cardinality (Basis v)) of
     SNothing -> IsFlexibleDimensional
     SJust sd -> withKnownNat sd IsStaticDimensional
instance ( HasBasis v, KnownNat n, Cardinality (Basis v) ~ 'Just n )
              => n`Dimensional`DualVectorFromBasis v where
  

instance ∀ v . ( HasBasis v, Num' (Scalar v)
               , SingI (Cardinality (Basis v))
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
  coerceFmapTensorProduct _ VSCCoercion
    = error "Cannot yet coerce tensors defined from a `HasBasis` instance. This would require `RoleAnnotations` on `:->:`. Cf. https://gitlab.haskell.org/ghc/ghc/-/issues/8177"


-- | Do not manually instantiate this class. It is used internally
--   by 'makeLinearSpaceFromBasis'.
class ( HasBasis v, Num' (Scalar v)
      , StaticDimension v ~ (Cardinality (Basis v))
      , SingI (StaticDimension v)
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
      , AdditiveGroup (VectorSpaceImplementation v) )
        => AbstractAdditiveGroup v where
  type VectorSpaceImplementation v :: Kind.Type

class (AbstractAdditiveGroup v, VectorSpace (VectorSpaceImplementation v))
        => AbstractVectorSpace v where
  scalarsSameInAbstraction
    :: ( Scalar (VectorSpaceImplementation v) ~ Scalar v
         => ρ ) -> ρ

class ( AbstractVectorSpace v, TensorSpace (VectorSpaceImplementation v)
#if !MIN_VERSION_manifolds_core(0,6,0)
      , Semimanifold v, Interior v ~ v
#endif
      , StaticDimension v ~ StaticDimension (VectorSpaceImplementation v)
      ) => AbstractTensorSpace v where
  sameDimensionalInAbstraction
    :: n`Dimensional`VectorSpaceImplementation v
            => (n`Dimensional`v => ρ) -> ρ
  abstractTensorProductsCoercion
    :: Coercion (TensorProduct v w)
                (TensorProduct (VectorSpaceImplementation v) w)

class ( AbstractTensorSpace v, LinearSpace (VectorSpaceImplementation v)
      , DualVector v
          ~ AbstractDualVector v (VectorSpaceImplementation v) )
    => AbstractLinearSpace v

scalarsSameInAbstractionAndDuals :: ∀ v ρ . AbstractLinearSpace v
     => ( ( Scalar (VectorSpaceImplementation v) ~ Scalar v
          , Scalar (DualVector v) ~ Scalar v
          , Scalar (DualVector (VectorSpaceImplementation v)) ~ Scalar v )
         => ρ ) -> ρ
scalarsSameInAbstractionAndDuals φ
     = case dualSpaceWitness @(VectorSpaceImplementation v) of
        DualSpaceWitness -> scalarsSameInAbstraction @v φ

abstractDualVectorCoercion :: ∀ a
   . (LinearSpace (VectorSpaceImplementation a))
    => VSCCoercion (AbstractDualVector a (VectorSpaceImplementation a))
              (DualVector (VectorSpaceImplementation a))
abstractDualVectorCoercion = case dualSpaceWitness @(VectorSpaceImplementation a) of
   DualSpaceWitness -> VSCCoercion

abstractDualTensorsCoercion :: ∀ a c w
  . ( AbstractVectorSpace a, LinearSpace c
    , c ~ VectorSpaceImplementation a, TensorSpace w )
      => VSCCoercion (AbstractDualVector a c⊗w) (DualVector c⊗w)
abstractDualTensorsCoercion = case dualSpaceWitness @c of
  DualSpaceWitness -> VSCCoercion

abstractLinmapCoercion :: ∀ a c w
  . ( AbstractLinearSpace a, LinearSpace c
    , c ~ VectorSpaceImplementation a, TensorSpace w )
      => VSCCoercion (AbstractDualVector a c+>w) (DualVector c+>w)
abstractLinmapCoercion = case ( dualSpaceWitness @c
                              , abstractTensorProductsCoercion @a @w ) of
   (DualSpaceWitness, Coercion) -> VSCCoercion

coerceLinearMapCodomain :: ∀ v w x
   . ( LinearSpace v, Coercible w x, StaticDimension w ~ StaticDimension x )
         => (v+>w) -> (v+>x)
coerceLinearMapCodomain = case dualSpaceWitness @v of
 DualSpaceWitness -> \(LinearMap m)
     -> LinearMap $ (coerceFmapTensorProduct ([]::[DualVector v])
                            (VSCCoercion :: VSCCoercion w x) $ m)

instance (Show (DualVector c)) => Show (AbstractDualVector a c) where
  showsPrec p (AbstractDualVector_ φ) = showParen (p>10)
       $ ("AbstractDualVector "++) . showsPrec 11 φ

instance ∀ a c . ( AbstractLinearSpace a, VectorSpaceImplementation a ~ c
                 , AdditiveGroup (DualVector c) )
     => AdditiveGroup (AbstractDualVector a c) where
  zeroV = AbstractDualVector zeroV
  (^+^) = coerce ((^+^) @(DualVector c))
  negateV = coerce (negateV @(DualVector c))

instance ∀ a c . (AbstractLinearSpace a, VectorSpaceImplementation a ~ c
                 , AdditiveGroup (DualVector c))
     => AffineSpace (AbstractDualVector a c) where
  type Diff (AbstractDualVector a c) = AbstractDualVector a c
  (.+^) = coerce ((^+^) @(DualVector c))
  (.-.) = coerce ((^-^) @(DualVector c))

instance ∀ a c . ( AbstractLinearSpace a, VectorSpaceImplementation a ~ c
                 , AdditiveGroup (DualVector c) )
     => Semimanifold (AbstractDualVector a c) where
  type Needle (AbstractDualVector a c) = AbstractDualVector a c
  (.+~^) = (^+^)
#if !MIN_VERSION_manifolds_core(0,6,0)
  type instance Interior (AbstractDualVector a c) = AbstractDualVector a c
  toInterior = pure
  fromInterior = id
  translateP = Tagged (^+^)
  semimanifoldWitness = SemimanifoldWitness BoundarylessWitness
#endif

instance ∀ a c . ( AbstractLinearSpace a, VectorSpaceImplementation a ~ c
                 , AdditiveGroup (DualVector c) )
     => PseudoAffine (AbstractDualVector a c) where
  v.-~.w = pure (v^-^w)
  (.-~!) = (^-^)

instance ∀ a c . ( AbstractLinearSpace a, VectorSpaceImplementation a ~ c
                 , VectorSpace (DualVector c) )
     => VectorSpace (AbstractDualVector a c) where
  type Scalar (AbstractDualVector a c) = Scalar a
  (*^) = scalarsSameInAbstractionAndDuals @a (coerce ((*^) @(DualVector c)))

instance ∀ a c . ( AbstractLinearSpace a, VectorSpaceImplementation a ~ c
                 , TensorSpace (DualVector c) )
     => DimensionAware (AbstractDualVector a c) where
  type StaticDimension (AbstractDualVector a c) = StaticDimension c
  dimensionalityWitness = case dimensionalityWitness @c of
     IsStaticDimensional -> IsStaticDimensional
     IsFlexibleDimensional -> IsFlexibleDimensional
instance ∀ n a c . ( AbstractLinearSpace a
                   , VectorSpaceImplementation a ~ c
                   , n`Dimensional`c
                   , TensorSpace (DualVector c) )
     => n`Dimensional`AbstractDualVector a c where

instance ∀ a c . ( AbstractLinearSpace a, VectorSpaceImplementation a ~ c
                 , TensorSpace (DualVector c) )
     => TensorSpace (AbstractDualVector a c) where
  type TensorProduct (AbstractDualVector a c) w
          = TensorProduct (DualVector c) w
  scalarSpaceWitness = scalarsSameInAbstractionAndDuals @a
     (case scalarSpaceWitness @(DualVector c) of ScalarSpaceWitness -> ScalarSpaceWitness)
  linearManifoldWitness = scalarsSameInAbstractionAndDuals @a
     (case linearManifoldWitness @(DualVector c) of
#if MIN_VERSION_manifolds_core(0,6,0)
       LinearManifoldWitness -> LinearManifoldWitness
#else
       LinearManifoldWitness BoundarylessWitness
          -> LinearManifoldWitness BoundarylessWitness
#endif
         )
  zeroTensor = zt
   where zt :: ∀ w . (TensorSpace w, Scalar w ~ Scalar a)
            => (AbstractDualVector a c ⊗ w)
         zt = scalarsSameInAbstractionAndDuals @a
                (coerce (zeroTensor @(DualVector c) @w))
  addTensors = at
   where at :: ∀ w . (TensorSpace w, Scalar w ~ Scalar a)
            => (AbstractDualVector a c ⊗ w) -> (AbstractDualVector a c ⊗ w)
                                            -> (AbstractDualVector a c ⊗ w)
         at = scalarsSameInAbstractionAndDuals @a
                (coerce (addTensors @(DualVector c) @w))
  subtractTensors = st
   where st :: ∀ w . (TensorSpace w, Scalar w ~ Scalar a)
            => (AbstractDualVector a c ⊗ w) -> (AbstractDualVector a c ⊗ w)
                                            -> (AbstractDualVector a c ⊗ w)
         st = scalarsSameInAbstractionAndDuals @a
                (coerce (subtractTensors @(DualVector c) @w))
  negateTensor = nt
   where nt :: ∀ w . (TensorSpace w, Scalar w ~ Scalar a)
            => (AbstractDualVector a c ⊗ w) -+> (AbstractDualVector a c ⊗ w)
         nt = scalarsSameInAbstractionAndDuals @a
                (coerce (negateTensor @(DualVector c) @w))
  scaleTensor = st
   where st :: ∀ w . (TensorSpace w, Scalar w ~ Scalar a)
            => Bilinear (Scalar a) (AbstractDualVector a c ⊗ w)
                                   (AbstractDualVector a c ⊗ w)
         st = scalarsSameInAbstractionAndDuals @a
                (coerce (scaleTensor @(DualVector c) @w))
  toFlatTensor = scalarsSameInAbstractionAndDuals @a
                    ( coerce (toFlatTensor @(DualVector c)) )
  fromFlatTensor = scalarsSameInAbstractionAndDuals @a
                    ( coerce (fromFlatTensor @(DualVector c)) )
  tensorProduct = tp
   where tp :: ∀ w . (TensorSpace w, Scalar w ~ Scalar a)
            => Bilinear (AbstractDualVector a c) w
                                   (AbstractDualVector a c ⊗ w)
         tp = scalarsSameInAbstractionAndDuals @a
                (coerce (tensorProduct @(DualVector c) @w))
  wellDefinedVector (AbstractDualVector v) = AbstractDualVector <$> wellDefinedVector v
  wellDefinedTensor = wdt
   where wdt :: ∀ w . (TensorSpace w, Scalar w ~ Scalar a)
            => (AbstractDualVector a c ⊗ w) -> Maybe (AbstractDualVector a c ⊗ w)
         wdt = scalarsSameInAbstractionAndDuals @a
                (coerce (wellDefinedTensor @(DualVector c) @w))
  transposeTensor = scalarsSameInAbstractionAndDuals @a tt
   where tt :: ∀ w . ( TensorSpace w, Scalar w ~ Scalar a
                     , Scalar (DualVector c) ~ Scalar a )
            => (AbstractDualVector a c ⊗ w) -+> (w ⊗ AbstractDualVector a c)
         tt = case dualSpaceWitness @c of
           DualSpaceWitness -> case coerceFmapTensorProduct @w []
                       (VSCCoercion @(DualVector c) @(AbstractDualVector a c)) of
             Coercion -> coerce (transposeTensor @(DualVector c) @w)
  fmapTensor = ft
   where ft :: ∀ w x . ( TensorSpace w, Scalar w ~ Scalar a
                       , TensorSpace x, Scalar x ~ Scalar a )
           => Bilinear (w-+>x) (AbstractDualVector a c ⊗ w) (AbstractDualVector a c ⊗ x) 
         ft = scalarsSameInAbstractionAndDuals @a
                 (coerce $ fmapTensor @(DualVector c) @w @x)
  fzipTensorWith = ft
   where ft :: ∀ u w x . ( TensorSpace w, Scalar w ~ Scalar a
                         , TensorSpace u, Scalar u ~ Scalar a
                         , TensorSpace x, Scalar x ~ Scalar a )
           => Bilinear ((w,x)-+>u)
                       (AbstractDualVector a c ⊗ w, AbstractDualVector a c ⊗ x)
                       (AbstractDualVector a c ⊗ u) 
         ft = scalarsSameInAbstractionAndDuals @a
                 (coerce $ fzipTensorWith @(DualVector c) @u @w @x)
  coerceFmapTensorProduct _ = coerceFmapTensorProduct ([]::[DualVector c])

witnessAbstractDualVectorTensorSpacyness
  :: ∀ a c r . ( AbstractLinearSpace a, VectorSpaceImplementation a ~ c
               , LinearSpace a, LinearSpace c
               , TensorSpace (DualVector c), Num (Scalar a) )
    => (( TensorSpace (AbstractDualVector a c)
        , LinearSpace (DualVector c)
        , Scalar (DualVector c) ~ Scalar a )
            => r) -> r
witnessAbstractDualVectorTensorSpacyness φ = case dualSpaceWitness @c of
   DualSpaceWitness -> scalarsSameInAbstraction @a φ

instance ∀ a c . ( AbstractLinearSpace a, VectorSpaceImplementation a ~ c
                 , LinearSpace a, LinearSpace c
                 , TensorSpace (DualVector c), Num (Scalar a) )
     => LinearSpace (AbstractDualVector a c) where
  type DualVector (AbstractDualVector a c) = a
  dualSpaceWitness = case (dualSpaceWitness @c, scalarSpaceWitness @c) of
    (DualSpaceWitness, ScalarSpaceWitness)
        -> scalarsSameInAbstraction @a DualSpaceWitness
  linearId = witnessAbstractDualVectorTensorSpacyness @a @c
       (symVSC (abstractLinmapCoercion @a)
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
                       (VSCCoercion @(DualVector c ⊗ w) @(AbstractDualVector a c ⊗ w))
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
                      . LinearFunction (abstractDualTensorsCoercion @a $)
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
                              . LinearFunction (abstractDualTensorsCoercion @a $)
           )
  useTupleLinearSpaceComponents = \_ -> usingNonTupleTypeAsTupleError

instance ∀ a c . ( AbstractLinearSpace a, VectorSpaceImplementation a ~ c
                 , FiniteDimensional a, FiniteDimensional c
                 , TensorSpace (DualVector c), Eq (DualVector c), Num (Scalar a) )
     => FiniteDimensional (AbstractDualVector a c) where
  newtype SubBasis (AbstractDualVector a c) = AbstractDualVectorSubBasis {
                        getAbstractDualVectorSubBasis :: SubBasis (DualVector c) }
  dualFinitenessWitness = scalarsSameInAbstraction @a
       ( case (scalarSpaceWitness @a, dualSpaceWitness @a) of
        (ScalarSpaceWitness, DualSpaceWitness)
            -> DualFinitenessWitness DualSpaceWitness )
  entireBasis = case dualFinitenessWitness @c of
    DualFinitenessWitness _ -> coerce (entireBasis @(DualVector c))
  enumerateSubBasis = case dualFinitenessWitness @c of
    DualFinitenessWitness _ 
          -> coerce (enumerateSubBasis @(DualVector c))
  decomposeLinMap = scalarsSameInAbstraction @a dclm
   where dclm :: ∀ w . (LSpace w, Scalar w ~ Scalar c)
            => (AbstractDualVector a c +> w)
                  -> (SubBasis (AbstractDualVector a c), DList w)
         dclm = case (dualFinitenessWitness @c, abstractTensorProductsCoercion @a @w) of
          (DualFinitenessWitness DualSpaceWitness, Coercion)
              -> coerce (decomposeLinMap @(DualVector c) @w)
  decomposeLinMapWithin = scalarsSameInAbstraction @a dclm
   where dclm :: ∀ w . (LSpace w, Scalar w ~ Scalar c)
            => SubBasis (AbstractDualVector a c) -> (AbstractDualVector a c +> w)
                   -> Either (SubBasis (AbstractDualVector a c), DList w) (DList w)
         dclm = case (dualFinitenessWitness @c, abstractTensorProductsCoercion @a @w) of
          (DualFinitenessWitness DualSpaceWitness, Coercion)
              -> coerce (decomposeLinMapWithin @(DualVector c) @w)
  recomposeSB = case dualFinitenessWitness @c of
          DualFinitenessWitness DualSpaceWitness -> scalarsSameInAbstraction @a
                                (coerce $ recomposeSB @(DualVector c))
  recomposeSBTensor = scalarsSameInAbstraction @a rst
   where rst :: ∀ w . (FiniteDimensional w, Scalar w ~ Scalar c)
           => SubBasis (AbstractDualVector a c) -> SubBasis w -> [Scalar c]
                  -> (AbstractDualVector a c ⊗ w, [Scalar c])
         rst = case dualFinitenessWitness @c of
          DualFinitenessWitness DualSpaceWitness
                  -> coerce (recomposeSBTensor @(DualVector c) @w)
  recomposeLinMap = scalarsSameInAbstraction @a rlm
   where rlm :: ∀ w . (LSpace w, Scalar w ~ Scalar c)
           => SubBasis (AbstractDualVector a c)
                 -> [w] -> (AbstractDualVector a c +> w, [w])
         rlm = case (dualFinitenessWitness @c, abstractTensorProductsCoercion @a @w) of
          (DualFinitenessWitness DualSpaceWitness, Coercion)
              -> coerce (recomposeLinMap @(DualVector c) @w)
  recomposeContraLinMap = scalarsSameInAbstraction @a rclm
   where rclm :: ∀ f w . (LinearSpace w, Scalar w ~ Scalar c, Hask.Functor f)
           => (f (Scalar w) -> w) -> f a -> AbstractDualVector a c +> w
         rclm = case (dualFinitenessWitness @c, abstractTensorProductsCoercion @a @w) of
          (DualFinitenessWitness DualSpaceWitness, Coercion) -> \f ->
             (coerce $ recomposeContraLinMap @(DualVector c) @w @f) f
               . fmap (coerce :: a -> c)
  recomposeContraLinMapTensor = scalarsSameInAbstraction @a rclmt
   where rclmt :: ∀ f w u . ( LinearSpace w, Scalar w ~ Scalar c
                            , FiniteDimensional u, Scalar u ~ Scalar c
                            , Hask.Functor f )
           => (f (Scalar w) -> w) -> f (AbstractDualVector a c+>DualVector u)
                   -> (AbstractDualVector a c⊗u) +> w
         rclmt = scalarsSameInAbstraction @a (case dualSpaceWitness @u of
           DualSpaceWitness ->
                 case ( dualFinitenessWitness @c
                      , abstractTensorProductsCoercion @a @(DualVector u)
                      , abstractTensorProductsCoercion @a
                          @(Tensor (Scalar a) (DualVector u) w) ) of
            (DualFinitenessWitness DualSpaceWitness, Coercion, Coercion) -> \f ->
              (coerce $ recomposeContraLinMapTensor @(DualVector c) @u @w @f) f
                . fmap (coerce :: (AbstractDualVector a c+>DualVector u)
                                    -> (DualVector c+>DualVector u))
          )
  uncanonicallyFromDual = case dualFinitenessWitness @c of
    DualFinitenessWitness DualSpaceWitness
        -> coerce (uncanonicallyFromDual @(DualVector c))
  uncanonicallyToDual = case dualFinitenessWitness @c of
    DualFinitenessWitness DualSpaceWitness
        -> coerce (uncanonicallyToDual @(DualVector c))
  tensorEquality = te
   where te :: ∀ w . (TensorSpace w, Eq w, Scalar w ~ Scalar a)
                => (AbstractDualVector a c ⊗ w) -> (AbstractDualVector a c ⊗ w) -> Bool
         te = case dualFinitenessWitness @c of
           DualFinitenessWitness _ -> scalarsSameInAbstractionAndDuals @a
                (coerce (tensorEquality @(DualVector c) @w))

instance ∀ a c . ( AbstractLinearSpace a, VectorSpaceImplementation a ~ c
                 , SemiInner a, LinearSpace c, SemiInner (DualVector c)
                 , TensorSpace (DualVector c), Eq (DualVector c), Num (Scalar a) )
     => SemiInner (AbstractDualVector a c) where
  dualBasisCandidates = case dualSpaceWitness @c of
    DualSpaceWitness -> coerce (dualBasisCandidates @(DualVector c))
  tensorDualBasisCandidates = scalarsSameInAbstraction @a tdbc
   where tdbc :: ∀ w . (SemiInner w, Scalar w ~ Scalar c)
            => [(Int, AbstractDualVector a c ⊗ w)]
             -> Forest (Int, AbstractDualVector a c +> DualVector w)
         tdbc = case (dualSpaceWitness @c, dualSpaceWitness @w) of
           (DualSpaceWitness, DualSpaceWitness)
               -> case abstractTensorProductsCoercion @a @(DualVector w) of
             Coercion -> coerce (tensorDualBasisCandidates @(DualVector c) @w)
  symTensorDualBasisCandidates = case dualSpaceWitness @c of
     DualSpaceWitness -> scalarsSameInAbstraction @a
          ( case ( coerceFmapTensorProduct @c [] (VSCCoercion @a @c)
                          . abstractTensorProductsCoercion @a @a
                 , coerceFmapTensorProduct @(DualVector c) []
                      (VSCCoercion @(AbstractDualVector a c) @(DualVector c)) ) of
             (Coercion, Coercion)
               -> coerce (symTensorDualBasisCandidates @(DualVector c))
          )

 

pattern AbstractDualVector
    :: AbstractLinearSpace v => DualVector (VectorSpaceImplementation v) -> DualVector v
pattern AbstractDualVector φ = AbstractDualVector_ φ



abstractVS_zeroV :: ∀ v .
    (AbstractAdditiveGroup v)
       => v
abstractVS_zeroV = coerce (zeroV @(VectorSpaceImplementation v))

abstractVS_addvs :: ∀ v .
    (AbstractAdditiveGroup v)
       => v -> v -> v
abstractVS_addvs = coerce ((^+^) @(VectorSpaceImplementation v))

abstractVS_subvs :: ∀ v .
    (AbstractAdditiveGroup v)
       => v -> v -> v
abstractVS_subvs = coerce ((^-^) @(VectorSpaceImplementation v))

abstractVS_negateV :: ∀ v .
    (AbstractAdditiveGroup v)
       => v -> v
abstractVS_negateV = coerce (negateV @(VectorSpaceImplementation v))

abstractVS_scalev :: ∀ v .
    (AbstractVectorSpace v)
       => Scalar v -> v -> v
abstractVS_scalev = scalarsSameInAbstraction @v
  ( coerce ((*^) @(VectorSpaceImplementation v)) )

abstractVS_innerProd :: ∀ v .
    (AbstractVectorSpace v, InnerSpace (VectorSpaceImplementation v))
       => v -> v -> Scalar v
abstractVS_innerProd = scalarsSameInAbstraction @v
  ( coerce ((<.>) @(VectorSpaceImplementation v)) )

abstractVS_dimensionalityWitness
    :: ∀ v . ( AbstractTensorSpace v
             , DimensionAware (VectorSpaceImplementation v) )
      => DimensionalityWitness v
abstractVS_dimensionalityWitness
   = case dimensionalityWitness @(VectorSpaceImplementation v) of
           IsStaticDimensional
             -> sameDimensionalInAbstraction @v IsStaticDimensional
           IsFlexibleDimensional -> IsFlexibleDimensional

abstractVS_scalarsSameInAbstraction :: ∀ v ρ .
    ( AbstractVectorSpace v
    , Scalar (VectorSpaceImplementation v) ~ Scalar v
    )
   => ( Scalar (VectorSpaceImplementation v) ~ Scalar v
         => ρ ) -> ρ
abstractVS_scalarsSameInAbstraction φ
   = φ

abstractVS_scalarSpaceWitness :: ∀ v .
    (AbstractTensorSpace v)
       => ScalarSpaceWitness v
abstractVS_scalarSpaceWitness
   = case scalarSpaceWitness @(VectorSpaceImplementation v) of
      ScalarSpaceWitness -> scalarsSameInAbstraction @v ScalarSpaceWitness 

abstractVS_linearManifoldWitness :: ∀ v .
    ( AbstractTensorSpace v, AffineSpace v, Needle v ~ v, Diff v ~ v
    )
       => LinearManifoldWitness v
abstractVS_linearManifoldWitness
   = case linearManifoldWitness @(VectorSpaceImplementation v) of
#if MIN_VERSION_manifolds_core(0,6,0)
           LinearManifoldWitness -> LinearManifoldWitness
#else
           LinearManifoldWitness BoundarylessWitness
                -> LinearManifoldWitness BoundarylessWitness
#endif

abstractVS_toFlatTensor :: ∀ v .
    ( AbstractTensorSpace v
    , Coercible (TensorProduct v (Scalar v))
                (TensorProduct (VectorSpaceImplementation v)
                               (Scalar (VectorSpaceImplementation v))) )
       => v -+> (v ⊗ Scalar v)
abstractVS_toFlatTensor = coerce (toFlatTensor @(VectorSpaceImplementation v))

abstractVS_fromFlatTensor :: ∀ v .
    ( AbstractTensorSpace v
    , Coercible (TensorProduct v (Scalar v))
                (TensorProduct (VectorSpaceImplementation v)
                               (Scalar (VectorSpaceImplementation v))) )
       => (v ⊗ Scalar v) -+> v
abstractVS_fromFlatTensor = coerce (fromFlatTensor @(VectorSpaceImplementation v))

abstractVS_zeroTensor :: ∀ v w
       . ( AbstractTensorSpace v
         , TensorSpace w, Scalar w ~ Scalar v
         , Coercible (TensorProduct v w)
                     (TensorProduct (VectorSpaceImplementation v) w) )
           => (v ⊗ w)
abstractVS_zeroTensor = scalarsSameInAbstraction @v
  (coerce (zeroTensor @(VectorSpaceImplementation v) @w))

abstractVS_addTensors :: ∀ v w
       . ( AbstractTensorSpace v
         , TensorSpace w, Scalar w ~ Scalar v
         , Coercible (TensorProduct v w)
                     (TensorProduct (VectorSpaceImplementation v) w) )
           => (v ⊗ w) -> (v ⊗ w) -> (v ⊗ w)
abstractVS_addTensors = scalarsSameInAbstraction @v
  (coerce (addTensors @(VectorSpaceImplementation v) @w))

abstractVS_subtractTensors :: ∀ v w
       . ( AbstractTensorSpace v
         , TensorSpace w, Scalar w ~ Scalar v
         , Coercible (TensorProduct v w)
                     (TensorProduct (VectorSpaceImplementation v) w) )
           => (v ⊗ w) -> (v ⊗ w) -> (v ⊗ w)
abstractVS_subtractTensors = scalarsSameInAbstraction @v
  (coerce (subtractTensors @(VectorSpaceImplementation v) @w))

abstractVS_scaleTensor :: ∀ v w
       . ( AbstractTensorSpace v
         , TensorSpace w, Scalar w ~ Scalar v
         , Coercible (TensorProduct v w)
                     (TensorProduct (VectorSpaceImplementation v) w) )
           => Bilinear (Scalar v) (v ⊗ w) (v ⊗ w)
abstractVS_scaleTensor = scalarsSameInAbstraction @v
  (coerce (scaleTensor @(VectorSpaceImplementation v) @w))

abstractVS_negateTensor :: ∀ v w
       . ( AbstractTensorSpace v
         , TensorSpace w, Scalar w ~ Scalar v
         , Coercible (TensorProduct v w)
                     (TensorProduct (VectorSpaceImplementation v) w) )
           => (v ⊗ w) -+> (v ⊗ w)
abstractVS_negateTensor = scalarsSameInAbstraction @v
  (coerce (negateTensor @(VectorSpaceImplementation v) @w))

abstractVS_wellDefinedVector :: ∀ v
         . ( AbstractTensorSpace v
           ) => v -> Maybe v
abstractVS_wellDefinedVector = coerce (wellDefinedVector @(VectorSpaceImplementation v))

abstractVS_wellDefinedTensor :: ∀ v w
         . ( AbstractTensorSpace v
           , TensorSpace w, Scalar w ~ Scalar v
           ) => (v ⊗ w) -> Maybe (v ⊗ w)
abstractVS_wellDefinedTensor
    = scalarsSameInAbstraction @v
        (case abstractTensorProductsCoercion @v @w of
           Coercion -> coerce (wellDefinedTensor @(VectorSpaceImplementation v) @w))

abstractVS_tensorProduct :: ∀ v w . ( AbstractTensorSpace v
           , TensorSpace w, Scalar w ~ Scalar v
           ) => Bilinear v w (v ⊗ w)
abstractVS_tensorProduct = scalarsSameInAbstraction @v
    ( case ( abstractTensorProductsCoercion @v @w ) of
       Coercion -> coerce (tensorProduct @(VectorSpaceImplementation v) @w) )

abstractVS_transposeTensor :: ∀ v w . ( AbstractTensorSpace v
           , TensorSpace w, Scalar w ~ Scalar v
           ) => (v ⊗ w) -+> (w ⊗ v)
abstractVS_transposeTensor
    = scalarsSameInAbstraction @v ( case
           ( abstractTensorProductsCoercion @v @w
           , coerceFmapTensorProduct @w []
                (VSCCoercion @(VectorSpaceImplementation v) @(v)) ) of
   (Coercion, Coercion) -> scalarsSameInAbstraction @v
      (coerce (transposeTensor @(VectorSpaceImplementation v) @w))
  )

abstractVS_fmapTensor :: ∀ v u w . ( AbstractTensorSpace v
           , TensorSpace u, Scalar u ~ Scalar v
           , TensorSpace w, Scalar w ~ Scalar v )
                   => Bilinear (u -+> w) (v ⊗ u) (v ⊗ w)
abstractVS_fmapTensor
   = scalarsSameInAbstraction @v
       ( case ( abstractTensorProductsCoercion @v @u
              , abstractTensorProductsCoercion @v @w ) of
           (Coercion, Coercion)
              -> coerce (fmapTensor @(VectorSpaceImplementation v) @u @w) )

abstractVS_fzipTensorsWith :: ∀ v u w x . ( AbstractTensorSpace v
           , TensorSpace u, Scalar u ~ Scalar v
           , TensorSpace w, Scalar w ~ Scalar v
           , TensorSpace x, Scalar x ~ Scalar v )
                   => Bilinear ((w, x) -+> u) (v ⊗ w, v ⊗ x) (v ⊗ u)
abstractVS_fzipTensorsWith = scalarsSameInAbstraction @v
       ( case ( abstractTensorProductsCoercion @v @u
              , abstractTensorProductsCoercion @v @w
              , abstractTensorProductsCoercion @v @x ) of
           (Coercion, Coercion, Coercion)
              -> coerce (fzipTensorWith @(VectorSpaceImplementation v) @u @w @x)
        )

abstractVS_coerceFmapTensorProduct :: ∀ v u w p .
         ( AbstractTensorSpace v
         ) => p v -> VSCCoercion u w -> Coercion (TensorProduct v u) (TensorProduct v w)
abstractVS_coerceFmapTensorProduct _ crc
      = case ( abstractTensorProductsCoercion @v @u
             , abstractTensorProductsCoercion @v @w
             , coerceFmapTensorProduct @(VectorSpaceImplementation v) [] crc ) of
          (Coercion, Coercion, Coercion) -> Coercion

abstractVS_dualSpaceWitness :: ∀ v . (AbstractLinearSpace v
        , LinearSpace v
        , LinearSpace (VectorSpaceImplementation v))
     => DualSpaceWitness v
abstractVS_dualSpaceWitness
      = scalarsSameInAbstraction @v
  ( case dualSpaceWitness @(VectorSpaceImplementation v) of
      DualSpaceWitness -> DualSpaceWitness
   )

abstractVS_linearId :: ∀ v . ( AbstractLinearSpace v
           , LinearSpace (VectorSpaceImplementation v) )
                   => v +> v
abstractVS_linearId = case dualSpaceWitness @(VectorSpaceImplementation v) of
 DualSpaceWitness -> case coerceFmapTensorProduct
                             @(DualVector (VectorSpaceImplementation v)) []
                             (VSCCoercion @v @(VectorSpaceImplementation v)) of
   Coercion -> coerce (linearId @(VectorSpaceImplementation v))

abstractTensorsCoercion :: ∀ v w . AbstractTensorSpace v
    => VSCCoercion (v⊗w) (VectorSpaceImplementation v⊗w)
abstractTensorsCoercion = case abstractTensorProductsCoercion @v @w of
   Coercion -> VSCCoercion

abstractVS_tensorId :: ∀ v w . ( AbstractLinearSpace v
           , LinearSpace (VectorSpaceImplementation v)
           , LinearSpace w, Scalar w ~ Scalar v )
                   => (v ⊗ w) +> (v ⊗ w) 
abstractVS_tensorId = scalarsSameInAbstraction @v
  (case (dualSpaceWitness @w, dualSpaceWitness @(VectorSpaceImplementation v)) of
     (DualSpaceWitness, DualSpaceWitness)
       -> case coerceFmapTensorProduct @(DualVector w) []
                 $ abstractTensorsCoercion @v @w of
         Coercion
           -> case ( coerceFmapTensorProduct 
                      @(DualVector (VectorSpaceImplementation v)) []
                      (VSCCoercion :: VSCCoercion
                          (Tensor (Scalar v) (DualVector w) (Tensor (Scalar v) v w))
                          (Tensor (Scalar v)
                                  (DualVector w)
                                  (Tensor (Scalar v)
                                          (VectorSpaceImplementation v) w)))
                   ) of
            Coercion
               -> coerce (tensorId @(VectorSpaceImplementation v) @w)
       )

abstractVS_applyDualVector :: ∀ v . ( AbstractLinearSpace v
           , LinearSpace (VectorSpaceImplementation v) )
                   => Bilinear (DualVector v) v (Scalar v)
abstractVS_applyDualVector = scalarsSameInAbstraction @v
 ( case dualSpaceWitness @(VectorSpaceImplementation v) of
    DualSpaceWitness -> coerce (applyDualVector @(VectorSpaceImplementation v)) )

abstractVS_applyLinear :: ∀ v w . ( AbstractLinearSpace v
           , LinearSpace (VectorSpaceImplementation v)
           , TensorSpace w, Scalar w ~ Scalar v )
                   => Bilinear (v +> w) v w
abstractVS_applyLinear = scalarsSameInAbstraction @v
 ( coerce (applyLinear @(VectorSpaceImplementation v) @w)
 )

abstractVS_applyTensorFunctional :: ∀ v u .
       ( AbstractLinearSpace v
       , LinearSpace (VectorSpaceImplementation v)
       , LinearSpace u, Scalar u ~ Scalar v )
           => Bilinear (DualVector (v⊗u)) (v⊗u) (Scalar v)
abstractVS_applyTensorFunctional = scalarsSameInAbstraction @v
 (case abstractTensorProductsCoercion @v @u of
   Coercion -> coerce (applyTensorFunctional @(VectorSpaceImplementation v) @u))

abstractVS_applyTensorLinMap :: ∀ v u w .
       ( AbstractLinearSpace v
       , LinearSpace (VectorSpaceImplementation v)
       , LinearSpace u, Scalar u ~ Scalar v
       , TensorSpace w, Scalar w ~ Scalar v )
                         => Bilinear ((v⊗u)+>w) (v⊗u) w
abstractVS_applyTensorLinMap = scalarsSameInAbstraction @v
 ( case abstractTensorProductsCoercion @v @u of
   Coercion -> coerce (applyTensorLinMap @(VectorSpaceImplementation v) @u @w) )

abstractSubbasisCoercion :: ∀ v .
       Coercible (SubBasis v) (SubBasis (VectorSpaceImplementation v))
     => Coercion (SubBasis v) (SubBasis (VectorSpaceImplementation v))
abstractSubbasisCoercion = Coercion

precomposeCoercion :: Coercion a b -> Coercion (b -> c) (a -> c)
precomposeCoercion Coercion = Coercion

postcomposeCoercion :: Coercion b c -> Coercion (a -> b) (a -> c)
postcomposeCoercion Coercion = Coercion

firstCoercion :: Coercion a b -> Coercion (a,c) (b,c)
firstCoercion Coercion = Coercion

leftCoercion :: Coercion a b -> Coercion (Either a c) (Either b c)
leftCoercion Coercion = Coercion

abstractVS_dualFinitenessWitness :: ∀ v .
       ( AbstractLinearSpace v, FiniteDimensional v
       , FiniteDimensional (VectorSpaceImplementation v) )
     => DualFinitenessWitness v
abstractVS_dualFinitenessWitness = scalarsSameInAbstraction @v
  (case dualFinitenessWitness @(VectorSpaceImplementation v) of
     DualFinitenessWitness DualSpaceWitness
        -> DualFinitenessWitness DualSpaceWitness
    )

abstractVS_entireBasis :: ∀ v .
       ( AbstractLinearSpace v, FiniteDimensional (VectorSpaceImplementation v)
       , Coercible (SubBasis v) (SubBasis (VectorSpaceImplementation v)) )
          => SubBasis v
abstractVS_entireBasis = sym (abstractSubbasisCoercion @v)
            $ entireBasis @(VectorSpaceImplementation v)

abstractVS_enumerateSubBasis :: ∀ v .
       ( AbstractLinearSpace v, FiniteDimensional (VectorSpaceImplementation v)
       , Coercible (SubBasis v) (SubBasis (VectorSpaceImplementation v)) )
          => SubBasis v -> [v]
abstractVS_enumerateSubBasis = precomposeCoercion
               (abstractSubbasisCoercion @v)
    $ coerce (enumerateSubBasis @(VectorSpaceImplementation v))

abstractVS_decomposeLinMap :: ∀ v w .
       ( AbstractLinearSpace v
       , FiniteDimensional (VectorSpaceImplementation v)
       , Coercible (SubBasis v) (SubBasis (VectorSpaceImplementation v))
       , LSpace w, Scalar w ~ Scalar v )
                   => (v +> w) -> (SubBasis v, DList w)
abstractVS_decomposeLinMap = scalarsSameInAbstraction @v
   ( postcomposeCoercion (firstCoercion $ sym
            (abstractSubbasisCoercion @v))
      $ case abstractTensorProductsCoercion @v @w of
         Coercion -> ( coerce (decomposeLinMap @(VectorSpaceImplementation v) @w)
                         :: (v +> w) -> ( SubBasis (VectorSpaceImplementation v)
                                        , DList w ) )
     )

abstractVS_decomposeLinMapWithin :: ∀ v w . ( AbstractLinearSpace v
       , FiniteDimensional (VectorSpaceImplementation v)
       , Coercible (SubBasis v) (SubBasis (VectorSpaceImplementation v))
       , LSpace w, Scalar w ~ Scalar v )
   => SubBasis v -> (v +> w) -> Either (SubBasis v, DList w) (DList w)
abstractVS_decomposeLinMapWithin = scalarsSameInAbstraction @v
 ( precomposeCoercion (abstractSubbasisCoercion @v)
    . postcomposeCoercion (postcomposeCoercion
        . leftCoercion . firstCoercion $ sym
              (abstractSubbasisCoercion @v))
      $ coerce (decomposeLinMapWithin @(VectorSpaceImplementation v) @w)
  )

abstractVS_recomposeSB :: ∀ v . ( AbstractLinearSpace v
       , FiniteDimensional (VectorSpaceImplementation v)
       , Coercible (SubBasis v) (SubBasis (VectorSpaceImplementation v)) )
   => SubBasis v -> [Scalar v] -> (v, [Scalar v])
abstractVS_recomposeSB = scalarsSameInAbstraction @v
 ( precomposeCoercion (abstractSubbasisCoercion @v)
  $ coerce (recomposeSB @(VectorSpaceImplementation v))
  )

abstractVS_recomposeSBTensor :: ∀ v w . ( AbstractLinearSpace v
       , FiniteDimensional (VectorSpaceImplementation v)
       , Coercible (SubBasis v) (SubBasis (VectorSpaceImplementation v))
       , FiniteDimensional w, Scalar w ~ Scalar v )
   => SubBasis v -> SubBasis w -> [Scalar v] -> (v ⊗ w, [Scalar v])
abstractVS_recomposeSBTensor = scalarsSameInAbstraction @v
 ( precomposeCoercion (abstractSubbasisCoercion @v)
  $ case abstractTensorProductsCoercion @v @w of
     Coercion -> coerce (recomposeSBTensor @(VectorSpaceImplementation v) @w)
  )

abstractVS_recomposeLinMap :: ∀ v w . ( AbstractLinearSpace v
       , FiniteDimensional (VectorSpaceImplementation v)
       , Coercible (SubBasis v) (SubBasis (VectorSpaceImplementation v))
       , LSpace w, Scalar w ~ Scalar v )
   => SubBasis v -> [w] -> (v +> w, [w])
abstractVS_recomposeLinMap = scalarsSameInAbstraction @v
 ( precomposeCoercion (abstractSubbasisCoercion @v)
  $ coerce (recomposeLinMap @(VectorSpaceImplementation v) @w)
  )

abstractVS_recomposeContraLinMap :: ∀ v f w . ( AbstractLinearSpace v
       , FiniteDimensional (VectorSpaceImplementation v)
       , Coercible (SubBasis v) (SubBasis (VectorSpaceImplementation v))
       , LinearSpace w, Scalar w ~ Scalar v
       , Hask.Functor f )
                  => (f (Scalar w) -> w) -> f (DualVector v) -> v +> w
abstractVS_recomposeContraLinMap f = scalarsSameInAbstraction @v
 ( coerce (recomposeContraLinMap @(VectorSpaceImplementation v) @w @f f)
                . fmap getConcreteDualVector
  )

abstractVS_recomposeLinMapTensor :: ∀ v f w u . ( AbstractLinearSpace v
       , FiniteDimensional (VectorSpaceImplementation v)
       , Coercible (SubBasis v) (SubBasis (VectorSpaceImplementation v))
       , LinearSpace w, Scalar w ~ Scalar v
       , FiniteDimensional u, Scalar u ~ Scalar v
       , Hask.Functor f )
   => (f (Scalar w) -> w) -> f (v+>DualVector u) -> (v⊗u) +> w
abstractVS_recomposeLinMapTensor f = scalarsSameInAbstraction @v
 ( coerce (recomposeContraLinMapTensor @(VectorSpaceImplementation v) @u @w @f f)
              . fmap (coerce :: (v+>DualVector u)
                          -> (VectorSpaceImplementation v+>DualVector u))
  )

abstractVS_uncanonicallyFromDual :: ∀ v . ( AbstractLinearSpace v
        , FiniteDimensional (VectorSpaceImplementation v) )
   => DualVector v -+> v
abstractVS_uncanonicallyFromDual = scalarsSameInAbstraction @v
 ( case abstractDualVectorCoercion @v of
            VSCCoercion -> coerce (uncanonicallyFromDual @(VectorSpaceImplementation v))
  )

abstractVS_uncanonicallyToDual :: ∀ v . ( AbstractLinearSpace v
        , FiniteDimensional (VectorSpaceImplementation v) )
   => v -+> DualVector v
abstractVS_uncanonicallyToDual = scalarsSameInAbstraction @v
 ( case abstractDualVectorCoercion @v of
            VSCCoercion -> coerce (uncanonicallyToDual @(VectorSpaceImplementation v))
  )

abstractVS_tensorEquality :: ∀ v w . ( AbstractLinearSpace v
        , FiniteDimensional (VectorSpaceImplementation v)
        , TensorSpace w, Eq w, Scalar w ~ Scalar v )
                       => (v ⊗ w) -> (v ⊗ w) -> Bool
abstractVS_tensorEquality = scalarsSameInAbstraction @v
 ( case abstractTensorProductsCoercion @v @w of
    Coercion -> coerce (tensorEquality @(VectorSpaceImplementation v) @w)
  )

abstractVS_dualBasisCandidates :: ∀ v . ( AbstractLinearSpace v
        , SemiInner (VectorSpaceImplementation v) )
      => [(Int, v)] -> Forest (Int, DualVector v)
abstractVS_dualBasisCandidates = scalarsSameInAbstraction @v
 ( case abstractDualVectorCoercion @v of
            VSCCoercion -> coerce (dualBasisCandidates @(VectorSpaceImplementation v))
  )

abstractVS_tensorDualBasisCandidates :: ∀ v w . ( AbstractLinearSpace v
        , LinearSpace v
        , SemiInner (VectorSpaceImplementation v)
        , SemiInner w, Scalar w ~ Scalar v)
                    => [(Int, v ⊗ w)]
                     -> Forest (Int, v +> DualVector w)
abstractVS_tensorDualBasisCandidates = scalarsSameInAbstraction @v
 ( case (dualSpaceWitness @v, dualSpaceWitness @w) of
    (DualSpaceWitness, DualSpaceWitness)
         -> case ( abstractDualVectorCoercion @v
                 , abstractTensorProductsCoercion @v @(DualVector w)
                 , abstractTensorProductsCoercion @v @w
                 ) of
       (VSCCoercion, Coercion, Coercion)
          -> coerce (tensorDualBasisCandidates @(VectorSpaceImplementation v) @w)
  )

abstractVS_symTensorDualBasisCandidates :: ∀ v . ( AbstractLinearSpace v
         , LinearSpace v
         , SemiInner (VectorSpaceImplementation v) )
        => [(Int, SymmetricTensor (Scalar v) v)]
              -> Forest (Int, SymmetricTensor (Scalar v) (DualVector v))
abstractVS_symTensorDualBasisCandidates = scalarsSameInAbstraction @v
 ( case ( dualSpaceWitness @v
        , dualSpaceWitness @(VectorSpaceImplementation v)
        , abstractDualVectorCoercion @v ) of
    (DualSpaceWitness, DualSpaceWitness, crdv)
       -> case ( abstractTensorProductsCoercion @v @v
               , coerceFmapTensorProduct @(DualVector (VectorSpaceImplementation v)) []
                   crdv
               , coerceFmapTensorProduct @(VectorSpaceImplementation v) []
                   crdv
               , coerceFmapTensorProduct @(VectorSpaceImplementation v) []
                   (VSCCoercion @v @(VectorSpaceImplementation v))
               ) of
     (Coercion, Coercion, Coercion, Coercion)
        -> coerce (symTensorDualBasisCandidates @(VectorSpaceImplementation v))
  )

-- | More powerful version of @deriving newtype@, specialised to the classes from
--   this package (and of @manifolds-core@). The 'DualVector' space will be a separate
--   type, even if the type you abstract over is self-dual.
copyNewtypeInstances :: Q Type -> [Name] -> DecsQ
copyNewtypeInstances cxtv classes = do

 requireExtensions [ TypeFamilies, MultiParamTypeClasses
                   , ScopedTypeVariables, TypeApplications
                   , DataKinds ]
 
 (tvbs, cxt, (a,c)) <- do
   (tvbs', cxt', a') <- deQuantifyType cxtv
   let extractImplementationType (AppT tc (VarT tvb)) atvbs
#if MIN_VERSION_template_haskell(2,17,0)
              = extractImplementationType tc $ atvbs++[PlainTV tvb SpecifiedSpec]
#else
              = extractImplementationType tc $ atvbs++[PlainTV tvb]
#endif
       extractImplementationType (ConT aName) atvbs = do
         D.reifyDatatype aName >>= \case
          D.DatatypeInfo{ D.datatypeVariant = D.Newtype
                        , D.datatypeVars = dttvbs
                        , D.datatypeCons = [
                           D.ConstructorInfo
                              { D.constructorFields = [c''] } ]
                        }
#if MIN_VERSION_template_haskell(2,17,0)
             -> let replaceTVs :: [TyVarBndr ()] -> [TyVarBndr Specificity] -> Type -> Type
                    replaceTVs (PlainTV infoTV _:infoTVs)
                               (PlainTV instTV _:instTVs)
                        = replaceTVs infoTVs instTVs . replaceTV infoTV instTV
                    replaceTVs (KindedTV infoTV flag _:infoTVs) instTVs
                        = replaceTVs (PlainTV infoTV flag:infoTVs) instTVs
                    replaceTVs infoTVs (KindedTV instTV flag _:instTVs)
                        = replaceTVs infoTVs (PlainTV instTV flag:instTVs)
#else
             -> let replaceTVs :: [TyVarBndr] -> [TyVarBndr] -> Type -> Type
                    replaceTVs (PlainTV infoTV:infoTVs) (PlainTV instTV:instTVs)
                        = replaceTVs infoTVs instTVs . replaceTV infoTV instTV
                    replaceTVs (KindedTV infoTV _:infoTVs) instTVs
                        = replaceTVs (PlainTV infoTV:infoTVs) instTVs
                    replaceTVs infoTVs (KindedTV instTV _:instTVs)
                        = replaceTVs infoTVs (PlainTV instTV:instTVs)
#endif
                    replaceTVs [] [] = id
                    replaceTVs infoTVs instTVs
                        = error $ "infoTVs = "++show infoTVs++", instTVs = "++show instTVs
                    replaceTV :: Name -> Name -> Type -> Type
                    replaceTV infoTV instTV (AppT tc (VarT tv))
                     | tv==infoTV  = AppT (replaceTV infoTV instTV tc) (VarT instTV)
                    replaceTV infoTV instTV (AppT tc ta)
                           = AppT (replaceTV infoTV instTV tc)
                                  (replaceTV infoTV instTV ta)
                    replaceTV _ _ t@(TupleT _) = t
                    replaceTV _ _ t@(ConT _) = t
                    replaceTV _ _ t
                        = error $ "Don't know how to substitute type variables in "
                                    ++ show t
                in return $ replaceTVs dttvbs atvbs c''
          _ -> error $ show aName ++ " is not a newtype."
       extractImplementationType a'' _
           = error $ "Don't know how to handle type "++show a''
                            ++" (specified: "++show a'++")"
   c' <- extractImplementationType a' []
   return (tvbs', pure cxt', (pure a', pure c'))
 
 let allClasses =
       [ ''AbstractAdditiveGroup | _<-[()], ''AdditiveGroup `elem` classes ]
      ++ [ ''AbstractVectorSpace | _<-[()], ''VectorSpace `elem` classes ]
      ++ [ ''AbstractTensorSpace | _<-[()], ''TensorSpace `elem` classes ]
      ++ [ ''AbstractLinearSpace | _<-[()], ''LinearSpace `elem` classes ]
      ++ classes

 vtnameHash <- abs . hash . show <$> a

 sequence [case dClass of
     "AbstractAdditiveGroup" -> InstanceD Nothing <$> cxt <*>
                          [t|AbstractAdditiveGroup $a|] <*> [d|
         type instance VectorSpaceImplementation $a = $c
      |]
     "AdditiveGroup" -> InstanceD Nothing <$> cxt <*>
                          [t|AdditiveGroup $a|] <*> [d|
         $(varP 'zeroV) = abstractVS_zeroV
         $(varP '(^+^)) = abstractVS_addvs
         $(varP '(^-^)) = abstractVS_subvs
         $(varP 'negateV) = abstractVS_negateV
      |]
     "AffineSpace" -> InstanceD Nothing <$> cxt <*>
                          [t|AffineSpace $a|] <*> [d|
         type instance Diff $a = $a
         $(varP '(.-.)) = abstractVS_subvs
         $(varP '(.+^)) = abstractVS_addvs
      |]
     "VectorSpace" -> InstanceD Nothing <$> cxt <*>
                          [t|VectorSpace $a|] <*> [d|
         type instance Scalar $a = Scalar ($c)
         $(varP '(*^)) = abstractVS_scalev
      |]
     "AbstractVectorSpace" -> InstanceD Nothing <$> cxt <*>
                          [t|AbstractVectorSpace $a|] <*> [d|
         $(varP 'scalarsSameInAbstraction)
            = abstractVS_scalarsSameInAbstraction @($a)
      |]
     "InnerSpace" -> InstanceD Nothing <$> cxt <*>
                          [t|InnerSpace $a|] <*> [d|
         $(varP '(<.>)) = abstractVS_innerProd
      |]
     "Semimanifold" -> InstanceD Nothing <$> cxt <*>
                          [t|Semimanifold $a|] <*> [d|
         type instance Needle $a = $a
         $(varP '(.+~^)) = abstractVS_addvs
#if !MIN_VERSION_manifolds_core(0,6,0)
         type instance Interior $a = $a
         $(varP 'toInterior) = pure
         $(varP 'fromInterior) = id
         $(varP 'translateP) = Tagged (^+^)
         $(varP 'semimanifoldWitness) = SemimanifoldWitness BoundarylessWitness
#endif
      |]
     "PseudoAffine" -> InstanceD Nothing <$> cxt <*>
                          [t|PseudoAffine $a|] <*> [d|
         $(varP '(.-~.)) = \p q -> Just (abstractVS_subvs p q)
         $(varP '(.-~!)) = abstractVS_subvs
      |]
     "DimensionAware" -> InstanceD Nothing <$> cxt <*>
                          [t|DimensionAware $a|] <*> [d|
         type instance StaticDimension $a = StaticDimension $c
         $(varP 'dimensionalityWitness) = abstractVS_dimensionalityWitness
      |]
     "Dimensional" -> do
       dim <- pure . VarT <$> newName "n"
       InstanceD Nothing <$> ((:)<$>[t|StaticDimension $c ~ 'Just $dim|]
                          <*>((:)<$>[t|KnownNat $dim|]<*>cxt)) <*>
                          [t|Dimensional $dim $a|] <*> [d|
        |]
     "TensorSpace" -> InstanceD Nothing <$> cxt <*>
                          [t|TensorSpace $a|] <*> [d|
         type instance TensorProduct $a w = TensorProduct $c w
         $(varP 'scalarSpaceWitness) = abstractVS_scalarSpaceWitness
         $(varP 'linearManifoldWitness) = abstractVS_linearManifoldWitness
         $(varP 'toFlatTensor) = abstractVS_toFlatTensor
         $(varP 'fromFlatTensor) = abstractVS_fromFlatTensor
         $(varP 'zeroTensor) = abstractVS_zeroTensor
         $(varP 'addTensors) = abstractVS_addTensors
         $(varP 'subtractTensors) = abstractVS_subtractTensors
         $(varP 'scaleTensor) = abstractVS_scaleTensor
         $(varP 'negateTensor) = abstractVS_negateTensor
         $(varP 'wellDefinedVector) = abstractVS_wellDefinedVector
         $(varP 'wellDefinedTensor) = abstractVS_wellDefinedTensor
         $(varP 'tensorProduct) = abstractVS_tensorProduct
         $(varP 'transposeTensor) = abstractVS_transposeTensor
         $(varP 'fmapTensor) = abstractVS_fmapTensor
         $(varP 'fzipTensorWith) = abstractVS_fzipTensorsWith
         $(varP 'coerceFmapTensorProduct) = abstractVS_coerceFmapTensorProduct
      |]
     "AbstractTensorSpace" -> InstanceD Nothing <$> cxt <*>
                          [t|AbstractTensorSpace $a|] <*> [d|
         $(varP 'sameDimensionalInAbstraction)
                  = \φ -> φ
         $(varP 'abstractTensorProductsCoercion)
                  = Coercion
      |]
     "LinearSpace" -> InstanceD Nothing <$> cxt <*>
                          [t|LinearSpace $a|] <*> [d|
         type instance DualVector $a = AbstractDualVector $a $c
         $(varP 'dualSpaceWitness) = abstractVS_dualSpaceWitness
         $(varP 'linearId) = abstractVS_linearId
         $(varP 'tensorId) = abstractVS_tensorId
         $(varP 'applyDualVector) = abstractVS_applyDualVector
         $(varP 'applyLinear) = abstractVS_applyLinear
         $(varP 'applyTensorFunctional) = abstractVS_applyTensorFunctional
         $(varP 'applyTensorLinMap) = abstractVS_applyTensorLinMap
         $(varP 'useTupleLinearSpaceComponents) = \_ -> usingNonTupleTypeAsTupleError
      |]
     "AbstractLinearSpace" -> InstanceD Nothing <$> cxt <*>
                          [t|AbstractLinearSpace $a|] <*> [d|
      |]
     "FiniteDimensional" -> InstanceD Nothing <$> cxt <*>
                          [t|FiniteDimensional $a|] <*> do
        subBasisCstr <- newName $ "SubBasis"++show vtnameHash
        
        tySyns <- sequence [
#if MIN_VERSION_template_haskell(2,15,0)
           NewtypeInstD [] (Just (
#if MIN_VERSION_template_haskell(2,17,0)
                                  map (fmap $ const ()) tvbs
#else
                                  tvbs
#endif
                                      ))
              <$> (AppT (ConT ''SubBasis) <$> a)
              <*> pure Nothing
              <*> (NormalC subBasisCstr . pure .
                          (Bang NoSourceUnpackedness NoSourceStrictness,)
                     <$> [t| SubBasis $c |])
              <*> pure []
#else
           NewtypeInstD [] ''SubBasis
              <$> ((:[]) <$> a)
              <*> pure Nothing
              <*> (NormalC subBasisCstr . pure . 
                          (Bang NoSourceUnpackedness NoSourceStrictness,)
                     <$> [t| SubBasis $c |])
              <*> pure []
#endif
         ]
        methods <- [d|
         $(varP 'dualFinitenessWitness) = abstractVS_dualFinitenessWitness
         $(varP 'entireBasis) = abstractVS_entireBasis
         $(varP 'enumerateSubBasis) = abstractVS_enumerateSubBasis
         $(varP 'decomposeLinMap) = abstractVS_decomposeLinMap
         $(varP 'decomposeLinMapWithin) = abstractVS_decomposeLinMapWithin
         $(varP 'recomposeSB) = abstractVS_recomposeSB
         $(varP 'recomposeSBTensor) = abstractVS_recomposeSBTensor
         $(varP 'recomposeLinMap) = abstractVS_recomposeLinMap
         $(varP 'recomposeContraLinMap) = abstractVS_recomposeContraLinMap
         $(varP 'recomposeContraLinMapTensor) = abstractVS_recomposeLinMapTensor
         $(varP 'uncanonicallyFromDual) = abstractVS_uncanonicallyFromDual
         $(varP 'uncanonicallyToDual) = abstractVS_uncanonicallyToDual
         $(varP 'tensorEquality) = abstractVS_tensorEquality
          |]
        return $ tySyns ++ methods
     "SemiInner" -> InstanceD Nothing <$> cxt <*>
                          [t|SemiInner $a|] <*> [d|
          $(varP 'dualBasisCandidates) = abstractVS_dualBasisCandidates
          $(varP 'tensorDualBasisCandidates) = abstractVS_tensorDualBasisCandidates
          $(varP 'symTensorDualBasisCandidates) = abstractVS_symTensorDualBasisCandidates
       |]
     _ -> error $ "Unsupported class to derive newtype instance for: ‘"++dClass++"’"
   | Name (OccName dClass) _ <- allClasses
   ]


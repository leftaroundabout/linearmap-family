-- |
-- Module      : Math.VectorSpace.DimensionAware.Theorems.MaybeNat
-- Copyright   : (c) Justus Sagemüller 2022
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE NoStarIsType               #-}
{-# LANGUAGE CPP                        #-}

module Math.VectorSpace.DimensionAware.Theorems.MaybeNat where

#if MIN_VERSION_singletons(3,0,0)
import Prelude.Singletons (SNum(..))
import Data.Maybe.Singletons
import GHC.TypeLits.Singletons (SNat(..), withKnownNat, sDiv)
#else
import Data.Singletons.Prelude.Num (SNum(..))
import Data.Singletons.Prelude.Maybe (SMaybe(..))
import Data.Singletons.TypeLits (SNat(..), withKnownNat, sDiv)
#endif
import Data.Singletons
import qualified Data.Type.Natural as DTN
import GHC.TypeLits
import Unsafe.Coerce

type family ZipWith (f :: k -> l -> m) (a :: Maybe k) (b :: Maybe l) :: Maybe m where
  ZipWith f 'Nothing y = 'Nothing
  ZipWith f x 'Nothing = 'Nothing
  ZipWith f ('Just x) ('Just y) = 'Just (f x y)

type family ZipWithPlus (a :: Maybe Nat) (b :: Maybe Nat) :: Maybe Nat where
  ZipWithPlus 'Nothing y = 'Nothing
  ZipWithPlus x 'Nothing = 'Nothing
  ZipWithPlus ('Just x) ('Just y) = 'Just (x+y)

type family ZipWithTimes (a :: Maybe Nat) (b :: Maybe Nat) :: Maybe Nat where
  ZipWithTimes 'Nothing y = 'Nothing
  ZipWithTimes x 'Nothing = 'Nothing
  ZipWithTimes ('Just x) ('Just y) = 'Just (x*y)

type family MaybePred (a :: Nat) :: Maybe Nat where
  MaybePred 0 = 'Nothing
  MaybePred n = 'Just (n-1)

type family ClipPred (n :: Nat) :: Nat where
  ClipPred 0 = 0
  ClipPred n = (n-1)

type family FmapClipPred (a :: Maybe Nat) :: Maybe Nat where
  FmapClipPred 'Nothing = 'Nothing
  FmapClipPred ('Just n) = 'Just (ClipPred n)

type family BindMaybePred (a :: Maybe Nat) :: Maybe Nat where
  BindMaybePred 'Nothing = 'Nothing
  BindMaybePred ('Just n) = MaybePred n

type TriangularNum (a :: Nat) = (a * (a+1))`Div`2

type family FmapTriangularNum (a :: Maybe Nat) where
  FmapTriangularNum 'Nothing = 'Nothing
  FmapTriangularNum ('Just n) = ('Just (TriangularNum n))

justNatSing :: ∀ (n :: Nat) . Sing n -> Sing ('Just n)
justNatSing SNat = sing

succMaybePredSing :: ∀ n . DTN.SNat n -> Sing (MaybePred (n+1))
succMaybePredSing s = unsafeCoerce (DTN.withKnownNat s (justNatSing (SNat @n)))

maybePredSing :: ∀ n . Sing n -> Sing (MaybePred n)
maybePredSing ν = withKnownNat ν
   (case DTN.viewNat (DTN.sNat @n) of
      DTN.IsZero -> sing
      DTN.IsSucc μ -> succMaybePredSing μ
    )

bindMaybePredSing :: ∀ n . Sing n -> Sing (BindMaybePred n)
bindMaybePredSing SNothing = sing
bindMaybePredSing (SJust ν) = maybePredSing ν

succClipPredSing :: ∀ n . DTN.SNat n -> Sing (ClipPred (n+1))
succClipPredSing s = unsafeCoerce (DTN.withKnownNat s (justNatSing (SNat @n)))

clipPredSing :: ∀ n . Sing n -> Sing (ClipPred n)
clipPredSing ν = withKnownNat ν
   (case DTN.viewNat (DTN.sNat @n) of
      DTN.IsZero -> sing
      DTN.IsSucc μ -> succClipPredSing μ
    )

fmapClipPredSing :: ∀ a . Sing a -> Sing (FmapClipPred a)
fmapClipPredSing SNothing = SNothing
fmapClipPredSing (SJust ν) = SJust (clipPredSing ν)

triangularNumSing :: ∀ a . Sing a -> Sing (TriangularNum a)
triangularNumSing α = (α %* (α%+(sing @1)))`sDiv`(sing @2)

fmapTriangularNumSing :: ∀ a . Sing a -> Sing (FmapTriangularNum a)
fmapTriangularNumSing SNothing = SNothing
fmapTriangularNumSing (SJust α) = SJust (triangularNumSing α)

zipWithPlusSing :: ∀ a b r . Sing a -> Sing b -> Sing (ZipWithPlus a b)
zipWithPlusSing SNothing _ = sing
zipWithPlusSing _ SNothing = sing
zipWithPlusSing (SJust α) (SJust β) = withKnownNat (α%+β) sing

zipWithTimesSing :: ∀ a b r . Sing a -> Sing b -> Sing (ZipWithTimes a b)
zipWithTimesSing SNothing _ = sing
zipWithTimesSing _ SNothing = sing
zipWithTimesSing (SJust α) (SJust β) = withKnownNat (α%*β) sing

zipWithTimesAssoc :: ∀ a b c r . Sing a -> Sing b -> Sing c
    -> ((ZipWithTimes a (ZipWithTimes b c) ~ ZipWithTimes (ZipWithTimes a b) c) => r)
           -> r
zipWithTimesAssoc SNothing _ _ φ = φ
zipWithTimesAssoc _ SNothing _ φ = φ
zipWithTimesAssoc _ _ SNothing φ = φ
zipWithTimesAssoc (SJust _) (SJust _) (SJust _) φ = φ

zipWithTimesCommu :: ∀ a b r . Sing a -> Sing b
    -> ((ZipWithTimes a b ~ ZipWithTimes b a) => r) -> r
zipWithTimesCommu SNothing _ φ = φ
zipWithTimesCommu _ SNothing φ = φ
zipWithTimesCommu (SJust _) (SJust _) φ = φ


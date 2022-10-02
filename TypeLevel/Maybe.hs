-- |
-- Module      : TypeLevel.Maybe
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

module TypeLevel.Maybe where

#if MIN_VERSION_singletons(3,0,0)
import Prelude.Singletons (SNum(..))
import Data.Maybe.Singletons
import GHC.TypeLits.Singletons (SNat(..), withKnownNat)
#else
import Data.Singletons.Prelude.Num (SNum(..))
import Data.Singletons.Prelude.Maybe (SMaybe(..))
import Data.Singletons.TypeLits (SNat(..), withKnownNat)
#endif
import Data.Singletons
import qualified Data.Type.Natural as DTN
import GHC.TypeLits

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

zipWithPlusCong :: ∀ a a' b b' r . (a ~ a', b ~ b')
    => ((ZipWithPlus a b ~ ZipWithPlus a' b') => r) -> r
zipWithPlusCong φ = φ

zipWithPlusSing :: ∀ a b r . Sing a -> Sing b -> Sing (ZipWithPlus a b)
zipWithPlusSing SNothing _ = sing
zipWithPlusSing _ SNothing = sing
zipWithPlusSing (SJust α) (SJust β) = withKnownNat (α%+β) sing

zipWithTimesCong :: ∀ a a' b b' r . (a ~ a', b ~ b')
    => ((ZipWithTimes a b ~ ZipWithTimes a' b') => r) -> r
zipWithTimesCong φ = φ

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


-- |
-- Module      : Math.VectorSpace.Docile.THHelpers
-- Copyright   : (c) Justus Sagemüller 2025
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 


{-# LANGUAGE CPP                  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UnicodeSyntax        #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DefaultSignatures    #-}

module Math.VectorSpace.Docile.THHelpers where

import Math.LinearMap.Category.Class
import Math.LinearMap.Category.Instances
import Math.LinearMap.Asserted
import Math.VectorSpace.Docile.Class

import Data.Tree (Tree(..), Forest)
import Data.List (sortBy, foldl', tails)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Ord (comparing)
import Data.List (maximumBy, unfoldr)
import qualified Data.Vector as Arr
import Data.Foldable (toList)
import Data.List (transpose)
import Data.Semigroup

import Data.VectorSpace
import Data.Basis

import Data.Void

import Prelude ()
import qualified Prelude as Hask

import Language.Haskell.TH
import THLego.Helpers (multiAppE)


import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Trans.State

import Linear ( V0(V0), V1(V1), V2(V2), V3(V3), V4(V4)
              , _x, _y, _z, _w, ex, ey, ez, ew )
import qualified Data.Vector.Unboxed as UArr
import Data.VectorSpace.Free
import Math.VectorSpace.ZeroDimensional
import qualified Linear.Matrix as Mat
import qualified Linear.Vector as Mat
import Control.Lens ((^.), Lens', lens, ReifiedLens', ReifiedLens(..))
import Data.Coerce

import Numeric.IEEE

import Data.CallStack


normalClause :: [Pat] -> Exp -> Clause
normalClause pats body = Clause pats (NormalB body) []


mkScalarFiniteDimensional :: Name -> Q [Dec]
mkScalarFiniteDimensional sclTName = do
  let sclT = pure . ConT $ sclTName
  subBasisCstrName <- newName $ "CompleteBasis"++nameBase sclTName
  let subBasisCstrP = ConP subBasisCstrName [] []

  sequence [InstanceD Nothing [] <$> [t|FiniteDimensional $sclT|]
   <*> sequence [
      DataInstD [] Nothing
            <$> (AppT (ConT ''SubBasis) <$> sclT)
            <*> pure Nothing
            <*> pure [NormalC subBasisCstrName []]
            <*> pure []
    , pure (FunD 'entireBasis [normalClause [] (ConE subBasisCstrName)])
    , FunD 'enumerateSubBasis <$> sequence
             [normalClause [subBasisCstrP]
                <$> [e| [1] |]]
    , FunD 'subbasisDimension <$> sequence
             [normalClause [subBasisCstrP]
                <$> [e| 1 |] ]
    , pure (FunD 'uncanonicallyFromDual [normalClause [] (VarE 'id)])
    , pure (FunD 'uncanonicallyToDual [normalClause [] (VarE 'id)])
    , FunD 'recomposeSB <$> sequence
             [normalClause [subBasisCstrP]
                <$> [e| \l -> case l of
                          [] -> (0, [])
                          (μ:cs) -> (μ, cs) |] ]
    , FunD 'recomposeSBTensor <$> sequence
             [normalClause [subBasisCstrP]
                <$> [e| \bw -> first Tensor . recomposeSB bw |] ]
    , FunD 'recomposeLinMap <$> sequence
             [normalClause [subBasisCstrP]
                <$> [e| \(w:ws) -> (LinearMap w, ws) |] ]
    , FunD 'decomposeLinMap <$> sequence
             [normalClause []
                <$> [e| \(LinearMap v)
                       -> ($(pure . ConE $ subBasisCstrName), (v:)) |] ]
    , FunD 'decomposeLinMapWithin <$> sequence
             [normalClause [subBasisCstrP]
                <$> [e| \(LinearMap v) -> pure (v:) |] ]
    , FunD 'recomposeContraLinMap <$> sequence
             [normalClause []
                <$> [e| \fw -> LinearMap . fw |] ]
    , FunD 'recomposeContraLinMapTensor <$> sequence
             [normalClause []
                <$> [e| \fw -> arr uncurryLinearMap . LinearMap
                             . recomposeContraLinMap fw . fmap getLinearMap |] ]
    , FunD 'tensorEquality <$> sequence
             [normalClause []
                <$> [e| \(Tensor v) (Tensor w) -> v==w |] ]
    ]
   ]



mkFreeFiniteDimensional :: Name -> Name -> Int -> Q [Dec]
mkFreeFiniteDimensional vTCstrName vECstrName dimens = do
  let 
      vTCstr :: Q Type
      vTCstr = pure . ConT $ vTCstrName
      
      vExprn xVars = multiAppE (ConE vECstrName) $ VarE<$>xVars
      vPatt xVars = ConP vECstrName [] $ VarP<$>xVars

      dim :: Q Exp
      dim = pure . LitE . IntegerL $ fromIntegral dimens
      newCVars :: Char -> Q [Name]
      newCVars sym = forM [0 .. dimens-1] $ newName . (sym:) . show

      newListToVecTranslation :: Pat -> Q (Pat, Exp)
      newListToVecTranslation rmdVarPat = do
         cVars <- newCVars 'c'
         let csListP = go cVars
              where go [] = rmdVarPat
                    go (cVar:cvs) = ConP ('(:)) [] [VarP cVar, go cvs]
             csVecE = multiAppE (ConE vECstrName)
                         [VarE cVar | cVar <- cVars]
         return (csListP, csVecE)

  scalarTVar <- (pure . VarT <$> newName "s" :: Q (Q Type))
  subBasisCstrName <- newName $ "CompleteBasis"++nameBase vTCstrName

  let subBasisCstrP = ConP subBasisCstrName [] []

  sequence [
    InstanceD Nothing <$> sequence
                           [ [t|Num' $scalarTVar|]
                           , [t|Eq $scalarTVar|]
                           , [t|LSpace $scalarTVar|] ]
                      <*> [t|FiniteDimensional ($vTCstr $scalarTVar)|]
                      <*> (sequence
     [ DataInstD [] Nothing
          <$> (AppT (ConT ''SubBasis)
                <$> (AppT <$> vTCstr <*> scalarTVar))
          <*> pure Nothing
          <*> pure [NormalC subBasisCstrName []]
          <*> pure []
     , pure (FunD 'entireBasis [normalClause [] (ConE subBasisCstrName)])
     , FunD 'enumerateSubBasis <$> sequence
              [normalClause [subBasisCstrP]
                 <$> [e| toList $ Mat.identity |]]
     , FunD 'subbasisDimension <$> sequence
              [normalClause [subBasisCstrP]
                 <$> dim]
     , pure (FunD 'uncanonicallyFromDual [normalClause [] (VarE 'id)])
     , pure (FunD 'uncanonicallyToDual [normalClause [] (VarE 'id)])
     , FunD 'recomposeSB <$> sequence
              [ do
                 csVar <- newName "cs"
                 (csListP, csVecE) <- newListToVecTranslation $ VarP csVar
                 normalClause [WildP, csListP]
                   <$> pure (TupE [ Just $ csVecE
                                  , Just $ VarE csVar ])
              , do
                 bVar <- newName "b"
                 csVar <- newName "cs"
                 normalClause [VarP bVar, VarP csVar]
                   <$> [e| recomposeSB $(pure (VarE bVar))
                             $ $(pure (VarE csVar)) ++ [0] |]
              ]
     , FunD 'recomposeSBTensor . (:[]) <$> do
          bwVar <- newName "bw"
          let bw = pure (VarE bwVar)
          csVar <- newName "cs"
          let cs = pure (VarE csVar)
          normalClause [ subBasisCstrP
                       , VarP bwVar
                       , VarP csVar ]
             <$> ( CaseE <$> [e| recomposeMultiple $(bw) $(dim) $(cs) |]
                    <*> sequence [ do
                      cs'Var <- newName "cs'"
                      (csListP, csVecE) <- newListToVecTranslation $ ListP []
                      Match (TupP [csListP, VarP cs'Var]) . NormalB
                        <$> [e| (Tensor $(pure csVecE), $(pure (VarE cs'Var))) |]
                        <*> pure []
                     ])
     , FunD 'recomposeLinMap <$> sequence [ do
              wsVar <- newName "ws"
              (wsListP, wsVecE) <- newListToVecTranslation $ VarP wsVar
              normalClause [subBasisCstrP, wsListP]
                 <$> [e| (LinearMap $(pure wsVecE), $(pure (VarE wsVar))) |]
          ]
     , FunD 'decomposeLinMap <$> sequence [
               normalClause []
                 <$> [e| \(LinearMap m)
                            -> ( $(pure (ConE subBasisCstrName))
                               , (toList m ++) ) |]
          ]
     , FunD 'decomposeLinMapWithin <$> sequence [
               normalClause [subBasisCstrP]
                 <$> [e| \(LinearMap m) -> pure (toList m ++) |]
          ]
     , FunD 'recomposeContraLinMap <$> sequence [
               normalClause []
                 <$> [e| \fw mv
                            -> LinearMap $ (\v -> fw $ fmap (<.>^v) mv)
                                             <$> Mat.identity |]
          ]
     , FunD 'recomposeContraLinMapTensor <$> sequence [
          normalClause [] <$> [e|
           let rclmt :: ∀ u w f . ( FiniteDimensional u, LinearSpace w
                                  , Scalar u ~ $scalarTVar, Scalar w ~ $scalarTVar
                                  , Hask.Functor f )
                  => DualSpaceWitness u
                  -> (f (Scalar w) -> w)
                  -> f ($vTCstr $scalarTVar+>DualVector u)
                  -> ($vTCstr $scalarTVar⊗u)+>w
               rclmt DualSpaceWitness fw mv = LinearMap $
                  (\v -> fromLinearMap $ recomposeContraLinMap fw
                     $ fmap (\(LinearMap q) -> foldl' (^+^) zeroV $ liftA2 (*^) v q) mv)
                  <$> Mat.identity 
           in rclmt dualSpaceWitness |]
        ]
         
     , FunD 'tensorEquality <$> sequence [
               normalClause []
                 <$> [e| \(Tensor s) (Tensor t) -> s==t |]
          ]
     ])
   ]
      



recomposeMultiple :: FiniteDimensional w
              => SubBasis w -> Int -> [Scalar w] -> ([w], [Scalar w])
recomposeMultiple bw n dc
 | n<1        = ([], dc)
 | otherwise  = case recomposeSB bw dc of
           (w, dc') -> first (w:) $ recomposeMultiple bw (n-1) dc'
                                  

mkScalarTensorDecomposable :: Name -> Q [Dec]
mkScalarTensorDecomposable sclTName = [d|
  instance TensorDecomposable $(pure . ConT $ sclTName) where
    tensorDecomposition (Tensor r) = [((), r)]
    tensorDecompose' (Tensor r) () = r
    showsPrecBasis _ = shows
 |]

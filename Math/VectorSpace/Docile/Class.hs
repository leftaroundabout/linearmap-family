-- |
-- Module      : Math.VectorSpace.Docile.Class
-- Copyright   : (c) Justus Sagemüller 2025
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ kth.se
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
{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DefaultSignatures    #-}

module Math.VectorSpace.Docile.Class where

import Math.LinearMap.Category.Class
import Math.LinearMap.Category.Instances
import Math.LinearMap.Asserted

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

import Data.Kind (Type)

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



type RealFrac' s = (Fractional' s, IEEE s, InnerSpace s)

-- | 'SemiInner' is the class of vector spaces with finite subspaces in which
--   you can define a basis that can be used to project from the whole space
--   into the subspace. The usual application is for using a kind of
--   <https://en.wikipedia.org/wiki/Galerkin_method Galerkin method> to
--   give an approximate solution (see '\$') to a linear equation in a possibly
--   infinite-dimensional space.
-- 
--   Of course, this also works for spaces which are already finite-dimensional themselves.
class LinearSpace v => SemiInner v where
  -- | Lazily enumerate choices of a basis of functionals that can be made dual
  --   to the given vectors, in order of preference (which roughly means, large in
  --   the normal direction.) I.e., if the vector @𝑣@ is assigned early to the
  --   dual vector @𝑣'@, then @(𝑣' $ 𝑣)@ should be large and all the other products
  --   comparably small.
  -- 
  --   The purpose is that we should be able to make this basis orthonormal
  --   with a ~Gaussian-elimination approach, in a way that stays numerically
  --   stable. This is otherwise known as the /choice of a pivot element/.
  -- 
  --   For simple finite-dimensional array-vectors, you can easily define this
  --   method using 'cartesianDualBasisCandidates'.
  dualBasisCandidates :: [(Int,v)] -> Forest (Int, DualVector v)
  
  tensorDualBasisCandidates :: (SemiInner w, Scalar w ~ Scalar v)
                   => [(Int, v⊗w)] -> Forest (Int, DualVector (v⊗w))
  
  symTensorDualBasisCandidates
        :: [(Int, SymmetricTensor (Scalar v) v)]
               -> Forest (Int, SymmetricTensor (Scalar v) (DualVector v))
  
  symTensorTensorDualBasisCandidates :: ∀ w . (SemiInner w, Scalar w ~ Scalar v)
        => [(Int, SymmetricTensor (Scalar v) v ⊗ w)]
               -> Forest (Int, SymmetricTensor (Scalar v) v +> DualVector w)
  -- Delegate to the transposed tensor. This is a hack that will sooner or
  -- later catch up with us. TODO: make a proper implementation.
  symTensorTensorDualBasisCandidates
              = case ( dualSpaceWitness :: DualSpaceWitness v
                     , dualSpaceWitness :: DualSpaceWitness w
                     , scalarSpaceWitness :: ScalarSpaceWitness v ) of
         (DualSpaceWitness, DualSpaceWitness, ScalarSpaceWitness)
             -> map (second $ getLinearFunction transposeTensor)
                  >>> dualBasisCandidates
                  >>> fmap (fmap . second $
                        arr asTensor >>> arr transposeTensor >>> arr fromTensor)

cartesianDualBasisCandidates
     :: [DualVector v]  -- ^ Set of canonical basis functionals.
     -> (v -> [ℝ])      -- ^ Decompose a vector in /absolute value/ components.
                        --   the list indices should correspond to those in
                        --   the functional list.
     -> ([(Int,v)] -> Forest (Int, DualVector v))
                        -- ^ Suitable definition of 'dualBasisCandidates'.
cartesianDualBasisCandidates dvs abss vcas = go 0 0 sorted
 where sorted = sortBy (comparing $ negate . snd . snd)
                       [ (i, (av, maximum av)) | (i,v)<-vcas, let av = abss v ]
       go k nDelay scs@((i,(av,_)):scs')
          | k<n   = Node (i, dv) (go (k+1) 0 [(i',(zeroAt j av',m)) | (i',(av',m))<-scs'])
                                : go k (nDelay+1) (bringToFront (nDelay+1) scs)
        where (j,_) = maximumBy (comparing snd) $ zip jfus av
              dv = dvs !! j
       go _ _ _ = []
       
       jfus = [0 .. n-1]
       n = length dvs
       
       zeroAt :: Int -> [ℝ] -> [ℝ]
       zeroAt _ [] = []
       zeroAt 0 (_:l) = (-1/0):l
       zeroAt j (e:l) = e : zeroAt (j-1) l
       
       bringToFront :: Int -> [a] -> [a]
       bringToFront i l = case splitAt i l of
           (_,[]) -> []
           (f,s:l') -> s : f++l'

instance (Fractional' s, SemiInner s) => SemiInner (ZeroDim s) where
  dualBasisCandidates _ = []
  tensorDualBasisCandidates _ = []
  symTensorDualBasisCandidates _ = []
instance (Fractional' s, SemiInner s) => SemiInner (V0 s) where
  dualBasisCandidates _ = []
  tensorDualBasisCandidates _ = []
  symTensorDualBasisCandidates _ = []

orthonormaliseDuals :: ∀ v . (SemiInner v, RealFrac' (Scalar v))
                          => Scalar v -> [(v, DualVector v)]
                                      -> [(v,Maybe (DualVector v))]
orthonormaliseDuals = od dualSpaceWitness
 where od _ _ [] = []
       od (DualSpaceWitness :: DualSpaceWitness v) ε ((v,v'₀):ws)
         | abs ovl₀ > 0, abs ovl₁ > ε
                        = (v,Just v')
                        : [ (w, fmap (\w' -> w' ^-^ (w'<.>^v)*^v') w's)
                          | (w,w's)<-wssys ]
         | otherwise    = (v,Nothing) : wssys
        where wssys = orthonormaliseDuals ε ws
              v'₁ = foldl' (\v'i₀ (w,w's)
                             -> foldl' (\v'i w' -> v'i ^-^ (v'i<.>^w)*^w') v'i₀ w's)
                           (v'₀ ^/ ovl₀) wssys
              v' = v'₁ ^/ ovl₁
              ovl₀ = v'₀<.>^v
              ovl₁ = v'₁<.>^v

dualBasis :: ∀ v . (SemiInner v, RealFrac' (Scalar v))
                => [v] -> [Maybe (DualVector v)]
dualBasis vs = snd <$> result
 where zip' ((i,v):vs) ((j,v'):ds)
        | i<j   = zip' vs ((j,v'):ds)
        | i==j  = (v,v') : zip' vs ds
       zip' _ _ = []
       result :: [(v, Maybe (DualVector v))]
       result = case findBest n n $ dualBasisCandidates vsIxed of
                       Right bestCandidates
                           -> orthonormaliseDuals epsilon
                                 (zip' vsIxed $ sortBy (comparing fst) bestCandidates)
                       Left (_, bestCompromise)
                           -> let survivors :: [(Int, DualVector v)]
                                  casualties :: [Int]
                                  (casualties, survivors)
                                    = second (sortBy $ comparing fst)
                                        $ mapEither (\case
                                                       (i,Nothing) -> Left i
                                                       (i,Just v') -> Right (i,v')
                                                    ) bestCompromise
                                  bestEffort = orthonormaliseDuals epsilon
                                    [ (lookupArr Arr.! i, v')
                                    | (i,v') <- survivors ]
                              in map snd . sortBy (comparing fst)
                                   $ zipWith ((,) . fst) survivors bestEffort
                                  ++ [ (i,(lookupArr Arr.! i, Nothing))
                                     | i <- casualties ]
        where findBest :: Int -- ^ Dual vectors needed for complete dual basis
                       -> Int -- ^ Maximum numbers of alternatives to consider
                              --   (to prevent exponential blowup of possibilities)
                       -> Forest (Int, DualVector v)
                            -> Either (Int, [(Int, Maybe (DualVector v))])
                                               [(Int, DualVector v)]
              findBest 0 _ _ = Right []
              findBest nMissing _ [] = Left (nMissing, [])
              findBest n maxCompromises (Node (i,v') bv' : alts)
                | Just _ <- guardedv'
                , Right best' <- straightContinue = Right $ (i,v') : best'
                | maxCompromises > 0
                , Right goodAlt <- alternative = Right goodAlt
                | otherwise  = case straightContinue of
                         Right goodOtherwise -> Left (1, second Just <$> goodOtherwise)
                         Left (nBad, badAnyway)
                           | maxCompromises > 0
                           , Left (nBadAlt, badAlt) <- alternative
                           , nBadAlt < nBad + myBadness
                                       -> Left (nBadAlt, badAlt)
                           | otherwise -> Left ( nBad + myBadness
                                               , (i, guardedv') : badAnyway )
               where guardedv' = case v'<.>^(lookupArr Arr.! i) of
                                   0 -> Nothing
                                   _ -> Just v'
                     myBadness = case guardedv' of
                                   Nothing -> 1
                                   Just _ -> 0
                     straightContinue = findBest (n-1) (maxCompromises-1) bv'
                     alternative = findBest n (maxCompromises-1) alts
       vsIxed = zip [0..] vs
       lookupArr = Arr.fromList vs
       n = Arr.length lookupArr

dualBasis' :: ∀ v . (LinearSpace v, SemiInner (DualVector v), RealFrac' (Scalar v))
                => [DualVector v] -> [Maybe v]
dualBasis' = case dualSpaceWitness :: DualSpaceWitness v of
      DualSpaceWitness -> dualBasis

zipTravWith :: Hask.Traversable t => (a->b->c) -> t a -> [b] -> Maybe (t c)
zipTravWith f = evalStateT . Hask.traverse zp
 where zp a = do
           bs <- get
           case bs of
              [] -> StateT $ const Nothing
              (b:bs') -> put bs' >> return (f a b)

embedFreeSubspace :: ∀ v t r . (HasCallStack, SemiInner v, RealFrac' (Scalar v), Hask.Traversable t)
            => t v -> Maybe (ReifiedLens' v (t (Scalar v)))
embedFreeSubspace vs = fmap (\(g,s) -> Lens (lens g s)) result
 where vsList = toList vs
       result = fmap (genGet&&&genSet) . sequenceA $ dualBasis vsList
       genGet vsDuals u = case zipTravWith (\_v dv -> dv<.>^u) vs vsDuals of
                Just cs -> cs
                Nothing -> error $ "Cannot map into free subspace using a set of "
                                 ++ show (length vsList)
                                 ++ " vectors and " ++ show (length vsDuals)
                                 ++ " dual vectors."
       genSet vsDuals u coefs = case zipTravWith (,) coefs $ zip vsList vsDuals of
                Just updators -> foldl' (\ur (c,(v,v')) -> ur ^+^ v^*(c - v'<.>^ur))
                                        u updators
                Nothing -> error $ "Cannot map from free subspace using a set of "
                                 ++ show (length vsList)
                                 ++ " vectors, " ++ show (length vsDuals)
                                 ++ " dual vectors and "
                                 ++ show (length coefs) ++ " coefficients."


instance SemiInner ℝ where
  dualBasisCandidates = fmap ((`Node`[]) . second recip)
                . sortBy (comparing $ negate . abs . snd)
                . filter ((/=0) . snd)
  tensorDualBasisCandidates = map (second getTensorProduct)
                 >>> dualBasisCandidates
                 >>> fmap (fmap $ second LinearMap)
  symTensorDualBasisCandidates = map (second getSymmetricTensor)
                 >>> dualBasisCandidates
                 >>> fmap (fmap $ second (arr asTensor >>> SymTensor))

instance (Fractional' s, Ord s, SemiInner s) => SemiInner (V1 s) where
  dualBasisCandidates = fmap ((`Node`[]) . second recip)
                . sortBy (comparing $ negate . abs . snd)
                . filter ((/=0) . snd)
  tensorDualBasisCandidates = map (second $ \(Tensor (V1 w)) -> w)
                 >>> dualBasisCandidates
                 >>> fmap (fmap . second $ LinearMap . V1)
  symTensorDualBasisCandidates = map (second getSymmetricTensor)
                 >>> dualBasisCandidates
                 >>> fmap (fmap $ second (arr asTensor >>> SymTensor))

instance SemiInner (V2 ℝ) where
  dualBasisCandidates = cartesianDualBasisCandidates Mat.basis (toList . fmap abs)
  tensorDualBasisCandidates = map (second $ \(Tensor (V2 x y)) -> (x,y))
                 >>> dualBasisCandidates
                 >>> map (fmap . second $ LinearMap . \(dx,dy) -> V2 dx dy)
  symTensorDualBasisCandidates = cartesianDualBasisCandidates
             (SymTensor . Tensor<$>[ V2 (V2 1 0)      zeroV
                                   , V2 (V2 0 sqrt¹₂) (V2 sqrt¹₂ 0)
                                   , V2 zeroV         (V2 0 1)])
             (\(SymTensor (Tensor (V2 (V2 xx xy)
                                      (V2 yx yy))))
                  -> abs <$> [xx, (xy+yx)*sqrt¹₂, yy])
   where sqrt¹₂ = sqrt 0.5
instance SemiInner (V3 ℝ) where
  dualBasisCandidates = cartesianDualBasisCandidates Mat.basis (toList . fmap abs)
  tensorDualBasisCandidates = map (second $ \(Tensor (V3 x y z)) -> (x,(y,z)))
                 >>> dualBasisCandidates
                 >>> map (fmap . second $ LinearMap . \(dx,(dy,dz)) -> V3 dx dy dz)
  symTensorDualBasisCandidates = cartesianDualBasisCandidates
             (SymTensor . Tensor<$>[ V3 (V3 1 0 0)      zeroV           zeroV
                                   , V3 (V3 0 sqrt¹₂ 0) (V3 sqrt¹₂ 0 0) zeroV
                                   , V3 (V3 0 0 sqrt¹₂) zeroV           (V3 sqrt¹₂ 0 0)
                                   , V3 zeroV           (V3 0 1 0)      zeroV
                                   , V3 zeroV           (V3 0 0 sqrt¹₂) (V3 0 sqrt¹₂ 0)
                                   , V3 zeroV           zeroV           (V3 0 0 1)])
             (\(SymTensor (Tensor (V3 (V3 xx xy xz)
                                      (V3 yx yy yz)
                                      (V3 zx zy zz))))
                  -> abs <$> [ xx, (xy+yx)*sqrt¹₂, (xz+zx)*sqrt¹₂
                                 ,       yy      , (yz+zy)*sqrt¹₂
                                                 ,       zz       ])
   where sqrt¹₂ = sqrt 0.5
instance SemiInner (V4 ℝ) where
  dualBasisCandidates = cartesianDualBasisCandidates Mat.basis (toList . fmap abs)
  tensorDualBasisCandidates = map (second $ \(Tensor (V4 x y z w)) -> ((x,y),(z,w)))
                 >>> dualBasisCandidates
                 >>> map (fmap . second $ LinearMap . \((dx,dy),(dz,dw)) -> V4 dx dy dz dw)
  symTensorDualBasisCandidates = cartesianDualBasisCandidates
             (SymTensor . Tensor<$>[ V4 (V4 1 0 0 0)      zeroV           zeroV zeroV
                                   , V4 (V4 0 sqrt¹₂ 0 0) (V4 sqrt¹₂ 0 0 0) zeroV zeroV
                                   , V4 (V4 0 0 sqrt¹₂ 0) zeroV    (V4 sqrt¹₂ 0 0 0) zeroV
                                   , V4 (V4 0 0 0 sqrt¹₂) zeroV    zeroV (V4 sqrt¹₂ 0 0 0)
                                   , V4 zeroV (V4 0 1 0 0)      zeroV           zeroV
                                   , V4 zeroV (V4 0 0 sqrt¹₂ 0) (V4 0 sqrt¹₂ 0 0) zeroV
                                   , V4 zeroV (V4 0 0 0 sqrt¹₂) zeroV (V4 0 sqrt¹₂ 0 0)
                                   , V4 zeroV zeroV (V4 0 0 1 0)      zeroV
                                   , V4 zeroV zeroV (V4 0 0 0 sqrt¹₂) (V4 0 0 sqrt¹₂ 0)
                                   , V4 zeroV zeroV zeroV           (V4 0 0 0 1)])
             (\(SymTensor (Tensor (V4 (V4 xx xy xz xw)
                                      (V4 yx yy yz yw)
                                      (V4 zx zy zz zw)
                                      (V4 wx wy wz ww))))
                  -> abs <$> [ xx, (xy+yx)*sqrt¹₂, (xz+zx)*sqrt¹₂, (xw+wx)*sqrt¹₂
                                 ,       yy      , (yz+zy)*sqrt¹₂, (yw+wy)*sqrt¹₂
                                                 ,       zz      , (zw+wz)*sqrt¹₂
                                                                 ,       ww       ])
   where sqrt¹₂ = sqrt 0.5

infixl 4 ⊗<$>
(⊗<$>) :: ( Num' s
          , Object (LinearFunction s) u
          , Object (LinearFunction s) v
          , Object (LinearFunction s) w )
             => LinearFunction s v w -> Tensor s u v -> Tensor s u w
f⊗<$>t = fmap f $ t

instance ∀ u v . ( SemiInner u, SemiInner v, Scalar u ~ Scalar v, Num' (Scalar u) )
                      => SemiInner (u,v) where
  dualBasisCandidates = fmap (\(i,(u,v))->((i,u),(i,v))) >>> unzip
              >>> dualBasisCandidates *** dualBasisCandidates
              >>> combineBaseis (dualSpaceWitness,dualSpaceWitness) False mempty
   where combineBaseis :: (DualSpaceWitness u, DualSpaceWitness v)
                 -> Bool    -- ^ “Bias flag”: iff True, v will be preferred.
                 -> Set Int -- ^ Set of already-assigned basis indices.
                 -> ( Forest (Int, DualVector u)
                    , Forest (Int, DualVector v) )
                   -> Forest (Int, (DualVector u, DualVector v))
         combineBaseis _ _ _ ([], []) = []
         combineBaseis wit@(DualSpaceWitness,DualSpaceWitness)
                         False forbidden (Node (i,du) bu' : abu, bv)
            | i`Set.member`forbidden  = combineBaseis wit False forbidden (abu, bv)
            | otherwise
                 = Node (i, (du, zeroV))
                        (combineBaseis wit True (Set.insert i forbidden) (bu', bv))
                       : combineBaseis wit False forbidden (abu, bv)
         combineBaseis wit@(DualSpaceWitness,DualSpaceWitness)
                         True forbidden (bu, Node (i,dv) bv' : abv)
            | i`Set.member`forbidden  = combineBaseis wit True forbidden (bu, abv)
            | otherwise
                 = Node (i, (zeroV, dv))
                        (combineBaseis wit False (Set.insert i forbidden) (bu, bv'))
                       : combineBaseis wit True forbidden (bu, abv)
         combineBaseis wit _ forbidden (bu, []) = combineBaseis wit False forbidden (bu,[])
         combineBaseis wit _ forbidden ([], bv) = combineBaseis wit True forbidden ([],bv)
  symTensorDualBasisCandidates = fmap (\(i,SymTensor (Tensor (u_uv, v_uv)))
                                    -> ( (i, snd ⊗<$> u_uv)
                                       ,((i, SymTensor $ fst ⊗<$> u_uv)
                                       , (i, SymTensor $ snd ⊗<$> v_uv))) )
                                      >>> unzip >>> second unzip
            >>> dualBasisCandidates *** dualBasisCandidates *** dualBasisCandidates
            >>> combineBaseis (dualSpaceWitness,dualSpaceWitness) (Just False) mempty
   where combineBaseis :: (DualSpaceWitness u, DualSpaceWitness v)
                 -> Maybe Bool  -- ^ @Just True@: prefer v⊗v, @Nothing@: prefer u⊗v
                 -> Set Int
                 -> ( Forest (Int, LinearMap (Scalar u) u (DualVector v))
                    ,(Forest (Int, SymmetricTensor (Scalar u) (DualVector u))
                    , Forest (Int, SymmetricTensor (Scalar v) (DualVector v))) )
                   -> Forest (Int, SymmetricTensor (Scalar u) (DualVector u, DualVector v))
         combineBaseis _ _ _ ([], ([],[])) = []
         combineBaseis wit@(DualSpaceWitness,DualSpaceWitness)
                         Nothing forbidden
                           (Node (i, duv) buv' : abuv, (bu, bv))
            | i`Set.member`forbidden 
                 = combineBaseis wit Nothing forbidden (abuv, (bu, bv))
            | otherwise
                 = Node (i, SymTensor $ Tensor
                             ( (zeroV&&&id)⊗<$>(asTensor$duv)
                             , (id&&&zeroV)⊗<$>(transposeTensor$asTensor$duv) ) )
                        (combineBaseis wit (Just False)
                                 (Set.insert i forbidden) (buv', (bu, bv)))
                       : combineBaseis wit Nothing forbidden (abuv, (bu, bv))
         combineBaseis wit Nothing forbidden ([], (bu, bv))
              = combineBaseis wit (Just False) forbidden ([], (bu, bv))
         combineBaseis wit@(DualSpaceWitness,DualSpaceWitness)
                         (Just False) forbidden
                           (buv, (Node (i,SymTensor du) bu' : abu, bv))
            | i`Set.member`forbidden 
                 = combineBaseis wit (Just False) forbidden (buv, (abu, bv))
            | otherwise
                 = Node (i, SymTensor $ Tensor ((id&&&zeroV)⊗<$> du, zeroV))
                        (combineBaseis wit (Just True)
                                 (Set.insert i forbidden) (buv, (bu', bv)))
                       : combineBaseis wit (Just False) forbidden (buv, (abu, bv))
         combineBaseis wit (Just False) forbidden (buv, ([], bv))
              = combineBaseis wit (Just True) forbidden (buv, ([], bv))
         combineBaseis wit@(DualSpaceWitness,DualSpaceWitness)
                         (Just True) forbidden
                           (buv, (bu, Node (i,SymTensor dv) bv' : abv))
            | i`Set.member`forbidden 
                 = combineBaseis wit (Just True) forbidden (buv, (bu, abv))
            | otherwise
                 = Node (i, SymTensor $ Tensor (zeroV, (zeroV&&&id)⊗<$> dv))
                        (combineBaseis wit Nothing
                                 (Set.insert i forbidden) (buv, (bu, bv')))
                       : combineBaseis wit (Just True) forbidden (buv, (bu, abv))
         combineBaseis wit (Just True) forbidden (buv, (bu, []))
              = combineBaseis wit Nothing forbidden (buv, (bu, []))
                                  
  tensorDualBasisCandidates = case scalarSpaceWitness :: ScalarSpaceWitness u of
     ScalarSpaceWitness -> map (second $ \(Tensor (tu, tv)) -> (tu, tv))
                          >>> dualBasisCandidates
                          >>> map (fmap . second $ \(LinearMap lu, LinearMap lv)
                                            -> LinearMap $ (Tensor lu, Tensor lv) )


instance ∀ s u v . ( SemiInner u, SemiInner v, Scalar u ~ s, Scalar v ~ s )
           => SemiInner (Tensor s u v) where
  dualBasisCandidates = tensorDualBasisCandidates
  tensorDualBasisCandidates :: ∀ w
              . (SemiInner w, Scalar w ~ s)
             => [(Int, Tensor s (Tensor s u v) w)]
             -> Forest (Int, LinearMap s (Tensor s u v) (DualVector w))
  tensorDualBasisCandidates = case dualSpaceWitness @w of
     DualSpaceWitness -> map (second $ arr rassocTensor)
                    >>> tensorDualBasisCandidates
                    >>> map (fmap . second $ arr uncurryLinearMap)

instance ∀ s v . ( Num' s, SemiInner v, Scalar v ~ s )
           => SemiInner (SymmetricTensor s v) where
  dualBasisCandidates = symTensorDualBasisCandidates
  tensorDualBasisCandidates = symTensorTensorDualBasisCandidates
  symTensorTensorDualBasisCandidates = case () of {}

instance ∀ s u v . ( LinearSpace u, SemiInner (DualVector u), SemiInner v
                   , Scalar u ~ s, Scalar v ~ s )
           => SemiInner (LinearMap s u v) where
  dualBasisCandidates = case dualSpaceWitness :: DualSpaceWitness u of
     DualSpaceWitness -> (coerce :: [(Int, LinearMap s u v)]
                                 -> [(Int, Tensor s (DualVector u) v)])
                    >>> tensorDualBasisCandidates
                    >>> coerce
  tensorDualBasisCandidates :: ∀ w
              . (SemiInner w, Scalar w ~ s)
             => [(Int, Tensor s (LinearMap s u v) w)]
             -> Forest (Int, LinearMap s (LinearMap s u v) (DualVector w))
  tensorDualBasisCandidates = case dualSpaceWitness @w of
     DualSpaceWitness -> map (second $ arr hasteLinearMap)
                    >>> dualBasisCandidates
                    >>> map (fmap . second $ arr coUncurryLinearMap)
  
(^/^) :: (InnerSpace v, Eq (Scalar v), Fractional (Scalar v)) => v -> v -> Scalar v
v^/^w = case (v<.>w) of
   0 -> 0
   vw -> vw / (w<.>w)

type DList x = [x]->[x]


data DualFinitenessWitness v where
  DualFinitenessWitness
    :: FiniteDimensional (DualVector v)
         => DualSpaceWitness v -> DualFinitenessWitness v

class (LSpace v, Eq v) => FiniteDimensional v where
  -- | Whereas 'Basis'-values refer to a single basis vector, a single
  --   'SubBasis' value represents a collection of such basis vectors,
  --   which can be used to associate a vector with a list of coefficients.
  -- 
  --   For spaces with a canonical finite basis, 'SubBasis' does not actually
  --   need to contain any information, it can simply have the full finite
  --   basis as its only value. Even for large sparse spaces, it should only
  --   have a very coarse structure that can be shared by many vectors.
  data SubBasis v :: Type
  
  entireBasis :: SubBasis v
  
  enumerateSubBasis :: SubBasis v -> [v]
  
  subbasisDimension :: SubBasis v -> Int
  subbasisDimension = length . enumerateSubBasis
  
  -- | Split up a linear map in “column vectors” WRT some suitable basis.
  decomposeLinMap :: (LSpace w, Scalar w ~ Scalar v) => (v+>w) -> (SubBasis v, DList w)
  
  -- | Expand in the given basis, if possible. Else yield a superbasis of the given
  --   one, in which this /is/ possible, and the decomposition therein.
  decomposeLinMapWithin :: (LSpace w, Scalar w ~ Scalar v)
      => SubBasis v -> (v+>w) -> Either (SubBasis v, DList w) (DList w)
  
  -- | Assemble a vector from coefficients in some basis. Return any excess coefficients.
  recomposeSB :: SubBasis v -> [Scalar v] -> (v, [Scalar v])
  
  recomposeSBTensor :: (FiniteDimensional w, Scalar w ~ Scalar v)
               => SubBasis v -> SubBasis w -> [Scalar v] -> (v⊗w, [Scalar v])
  
  recomposeLinMap :: (LSpace w, Scalar w~Scalar v) => SubBasis v -> [w] -> (v+>w, [w])
  
  -- | Given a function that interprets a coefficient-container as a vector representation,
  --   build a linear function mapping to that space.
  recomposeContraLinMap :: (LinearSpace w, Scalar w ~ Scalar v, Hask.Functor f)
           => (f (Scalar w) -> w) -> f (DualVector v) -> v+>w
  
  recomposeContraLinMapTensor
        :: ( FiniteDimensional u, LinearSpace w
           , Scalar u ~ Scalar v, Scalar w ~ Scalar v, Hask.Functor f )
           => (f (Scalar w) -> w) -> f (v+>DualVector u) -> (v⊗u)+>w
  
  -- | The existance of a finite basis gives us an isomorphism between a space
  --   and its dual space. Note that this isomorphism is not natural (i.e. it
  --   depends on the actual choice of basis, unlike everything else in this
  --   library).
  uncanonicallyFromDual :: DualVector v -+> v
  uncanonicallyToDual :: v -+> DualVector v
  
  tensorEquality :: (TensorSpace w, Eq w, Scalar w ~ Scalar v) => v⊗w -> v⊗w -> Bool

  dualFinitenessWitness :: DualFinitenessWitness v
  default dualFinitenessWitness :: FiniteDimensional (DualVector v)
              => DualFinitenessWitness v
  dualFinitenessWitness = DualFinitenessWitness (dualSpaceWitness @v)
  
 
instance ( FiniteDimensional u, TensorSpace v
         , Scalar u~s, Scalar v~s
         , Eq u, Eq v ) => Eq (Tensor s u v) where
  (==) = tensorEquality

instance ∀ s u v . ( FiniteDimensional u
                   , TensorSpace v
                   , Scalar u~s, Scalar v~s
                   , Eq v )
             => Eq (LinearMap s u v) where
  LinearMap f == LinearMap g = case dualFinitenessWitness @u of
    DualFinitenessWitness DualSpaceWitness
       -> (Tensor f :: Tensor s (DualVector u) v) == Tensor g

instance ∀ s u v . ( FiniteDimensional u
                   , TensorSpace v
                   , Scalar u~s, Scalar v~s
                   , Eq v )
             => Eq (LinearFunction s u v) where
  f == g = (sampleLinearFunction-+$>f) == (sampleLinearFunction-+$>g)




instance (Num' s) => FiniteDimensional (ZeroDim s) where
  data SubBasis (ZeroDim s) = ZeroBasis
  entireBasis = ZeroBasis
  enumerateSubBasis ZeroBasis = []
  subbasisDimension ZeroBasis = 0
  recomposeSB ZeroBasis l = (Origin, l)
  recomposeSBTensor ZeroBasis _ l = (Tensor Origin, l)
  recomposeLinMap ZeroBasis l = (LinearMap Origin, l)
  decomposeLinMap _ = (ZeroBasis, id)
  decomposeLinMapWithin ZeroBasis _ = pure id
  recomposeContraLinMap _ _ = LinearMap Origin
  recomposeContraLinMapTensor _ _ = LinearMap Origin
  uncanonicallyFromDual = id
  uncanonicallyToDual = id
  tensorEquality (Tensor Origin) (Tensor Origin) = True
  
instance (Num' s, Eq s, LinearSpace s) => FiniteDimensional (V0 s) where
  data SubBasis (V0 s) = V0Basis
  entireBasis = V0Basis
  enumerateSubBasis V0Basis = []
  subbasisDimension V0Basis = 0
  recomposeSB V0Basis l = (V0, l)
  recomposeSBTensor V0Basis _ l = (Tensor V0, l)
  recomposeLinMap V0Basis l = (LinearMap V0, l)
  decomposeLinMap _ = (V0Basis, id)
  decomposeLinMapWithin V0Basis _ = pure id
  recomposeContraLinMap _ _ = LinearMap V0
  recomposeContraLinMapTensor _ _ = LinearMap V0
  uncanonicallyFromDual = id
  uncanonicallyToDual = id
  tensorEquality (Tensor V0) (Tensor V0) = True
  
instance FiniteDimensional ℝ where
  data SubBasis ℝ = RealsBasis
  entireBasis = RealsBasis
  enumerateSubBasis RealsBasis = [1]
  subbasisDimension RealsBasis = 1
  recomposeSB RealsBasis [] = (0, [])
  recomposeSB RealsBasis (μ:cs) = (μ, cs)
  recomposeSBTensor RealsBasis bw = first Tensor . recomposeSB bw
  recomposeLinMap RealsBasis (w:ws) = (LinearMap w, ws)
  decomposeLinMap (LinearMap v) = (RealsBasis, (v:))
  decomposeLinMapWithin RealsBasis (LinearMap v) = pure (v:)
  recomposeContraLinMap fw = LinearMap . fw
  recomposeContraLinMapTensor fw = arr uncurryLinearMap . LinearMap
              . recomposeContraLinMap fw . fmap getLinearMap
  uncanonicallyFromDual = id
  uncanonicallyToDual = id
  tensorEquality (Tensor v) (Tensor w) = v==w


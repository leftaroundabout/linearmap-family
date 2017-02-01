-- |
-- Module      : Math.VectorSpace.Docile
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 


{-# LANGUAGE CPP                  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
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

module Math.VectorSpace.Docile where

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


zipTravWith :: Hask.Traversable t => (a->b->c) -> t a -> [b] -> Maybe (t c)
zipTravWith f = evalStateT . Hask.traverse zp
 where zp a = do
           bs <- get
           case bs of
              [] -> StateT $ const Nothing
              (b:bs') -> put bs' >> return (f a b)

embedFreeSubspace :: ∀ v t r . (SemiInner v, RealFrac' (Scalar v), Hask.Traversable t)
            => t v -> Maybe (ReifiedLens' v (t (Scalar v)))
embedFreeSubspace vs = fmap (\(g,s) -> Lens (lens g s)) result
 where vsList = toList vs
       result = fmap (genGet&&&genSet) . sequenceA $ dualBasis vsList
       genGet vsDuals u = case zipTravWith (\_v dv -> dv<.>^u) vs vsDuals of
                Just cs -> cs
       genSet vsDuals u coefs = case zipTravWith (,) coefs $ zip vsList vsDuals of
                Just updators -> foldl' (\ur (c,(v,v')) -> ur ^+^ v^*(c - v'<.>^ur))
                                        u updators


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
  tensorDualBasisCandidates = map (second $ arr rassocTensor)
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
  tensorDualBasisCandidates = map (second $ arr hasteLinearMap)
                    >>> dualBasisCandidates
                    >>> map (fmap . second $ arr coUncurryLinearMap)
  
(^/^) :: (InnerSpace v, Eq (Scalar v), Fractional (Scalar v)) => v -> v -> Scalar v
v^/^w = case (v<.>w) of
   0 -> 0
   vw -> vw / (w<.>w)

type DList x = [x]->[x]

class (LSpace v) => FiniteDimensional v where
  -- | Whereas 'Basis'-values refer to a single basis vector, a single
  --   'SubBasis' value represents a collection of such basis vectors,
  --   which can be used to associate a vector with a list of coefficients.
  -- 
  --   For spaces with a canonical finite basis, 'SubBasis' does not actually
  --   need to contain any information, it can simply have the full finite
  --   basis as its only value. Even for large sparse spaces, it should only
  --   have a very coarse structure that can be shared by many vectors.
  data SubBasis v :: *
  
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

#define FreeFiniteDimensional(V, VB, dimens, take, give)        \
instance (Num' s, Eq s, LSpace s)                            \
            => FiniteDimensional (V s) where {            \
  data SubBasis (V s) = VB deriving (Show);             \
  entireBasis = VB;                                      \
  enumerateSubBasis VB = toList $ Mat.identity;      \
  subbasisDimension VB = dimens;                       \
  uncanonicallyFromDual = id;                               \
  uncanonicallyToDual = id;                                  \
  recomposeSB _ (take:cs) = (give, cs);                   \
  recomposeSB b cs = recomposeSB b $ cs ++ [0];        \
  recomposeSBTensor VB bw cs = case recomposeMultiple bw dimens cs of \
                   {(take:[], cs') -> (Tensor (give), cs')};              \
  recomposeLinMap VB (take:ws') = (LinearMap (give), ws');   \
  decomposeLinMap (LinearMap m) = (VB, (toList m ++));          \
  decomposeLinMapWithin VB (LinearMap m) = pure (toList m ++);          \
  recomposeContraLinMap fw mv \
         = LinearMap $ (\v -> fw $ fmap (<.>^v) mv) <$> Mat.identity; \
  recomposeContraLinMapTensor = rclmt dualSpaceWitness \
   where {rclmt :: ∀ u w f . ( FiniteDimensional u, LinearSpace w \
           , Scalar u ~ s, Scalar w ~ s, Hask.Functor f ) => DualSpaceWitness u \
           -> (f (Scalar w) -> w) -> f (V s+>DualVector u) -> (V s⊗u)+>w \
         ; rclmt DualSpaceWitness fw mv = LinearMap $ \
       (\v -> fromLinearMap $ recomposeContraLinMap fw \
                $ fmap (\(LinearMap q) -> foldl' (^+^) zeroV $ liftA2 (*^) v q) mv) \
                       <$> Mat.identity } }
FreeFiniteDimensional(V1, V1Basis, 1, c₀         , V1 c₀         )
FreeFiniteDimensional(V2, V2Basis, 2, c₀:c₁      , V2 c₀ c₁      )
FreeFiniteDimensional(V3, V3Basis, 3, c₀:c₁:c₂   , V3 c₀ c₁ c₂   )
FreeFiniteDimensional(V4, V4Basis, 4, c₀:c₁:c₂:c₃, V4 c₀ c₁ c₂ c₃)

recomposeMultiple :: FiniteDimensional w
              => SubBasis w -> Int -> [Scalar w] -> ([w], [Scalar w])
recomposeMultiple bw n dc
 | n<1        = ([], dc)
 | otherwise  = case recomposeSB bw dc of
           (w, dc') -> first (w:) $ recomposeMultiple bw (n-1) dc'
                                  
deriving instance Show (SubBasis ℝ)
  
instance ∀ u v . ( FiniteDimensional u, FiniteDimensional v
                 , Scalar u ~ Scalar v, Scalar (DualVector u) ~ Scalar (DualVector v) )
            => FiniteDimensional (u,v) where
  data SubBasis (u,v) = TupleBasis !(SubBasis u) !(SubBasis v)
  entireBasis = TupleBasis entireBasis entireBasis
  enumerateSubBasis (TupleBasis bu bv)
       = ((,zeroV)<$>enumerateSubBasis bu) ++ ((zeroV,)<$>enumerateSubBasis bv)
  subbasisDimension (TupleBasis bu bv) = subbasisDimension bu + subbasisDimension bv
  decomposeLinMap = dclm dualSpaceWitness dualSpaceWitness dualSpaceWitness
   where dclm :: ∀ w . (LinearSpace w, Scalar w ~ Scalar u)
                    => DualSpaceWitness u -> DualSpaceWitness v -> DualSpaceWitness w
                          -> ((u,v)+>w) -> (SubBasis (u,v), DList w)
         dclm DualSpaceWitness DualSpaceWitness DualSpaceWitness (LinearMap (fu, fv))
          = case (decomposeLinMap (asLinearMap$fu), decomposeLinMap (asLinearMap$fv)) of
             ((bu, du), (bv, dv)) -> (TupleBasis bu bv, du . dv)
  decomposeLinMapWithin = dclm dualSpaceWitness dualSpaceWitness dualSpaceWitness
   where dclm :: ∀ w . (LinearSpace w, Scalar w ~ Scalar u)
                    => DualSpaceWitness u -> DualSpaceWitness v -> DualSpaceWitness w
                          -> SubBasis (u,v) -> ((u,v)+>w)
                            -> Either (SubBasis (u,v), DList w) (DList w)
         dclm DualSpaceWitness DualSpaceWitness DualSpaceWitness
                  (TupleBasis bu bv) (LinearMap (fu, fv))
          = case ( decomposeLinMapWithin bu (asLinearMap$fu)
                 , decomposeLinMapWithin bv (asLinearMap$fv) ) of
            (Left (bu', du), Left (bv', dv)) -> Left (TupleBasis bu' bv', du . dv)
            (Left (bu', du), Right dv) -> Left (TupleBasis bu' bv, du . dv)
            (Right du, Left (bv', dv)) -> Left (TupleBasis bu bv', du . dv)
            (Right du, Right dv) -> Right $ du . dv
  recomposeSB (TupleBasis bu bv) coefs = case recomposeSB bu coefs of
                        (u, coefs') -> case recomposeSB bv coefs' of
                         (v, coefs'') -> ((u,v), coefs'')
  recomposeSBTensor (TupleBasis bu bv) bw cs = case recomposeSBTensor bu bw cs of
            (tuw, cs') -> case recomposeSBTensor bv bw cs' of
               (tvw, cs'') -> (Tensor (tuw, tvw), cs'')
  recomposeLinMap (TupleBasis bu bv) ws = case recomposeLinMap bu ws of
           (lmu, ws') -> first (lmu⊕) $ recomposeLinMap bv ws'
  recomposeContraLinMap fw dds
         = recomposeContraLinMap fw (fst<$>dds)
          ⊕ recomposeContraLinMap fw (snd<$>dds)
  recomposeContraLinMapTensor fw dds = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                                            , dualSpaceWitness :: DualSpaceWitness u
                                            , dualSpaceWitness :: DualSpaceWitness v ) of
    (ScalarSpaceWitness,DualSpaceWitness,DualSpaceWitness) -> uncurryLinearMap
         $ LinearMap ( fromLinearMap . curryLinearMap
                         $ recomposeContraLinMapTensor fw
                                 (fmap (\(LinearMap(Tensor tu,_))->LinearMap tu) dds)
                     , fromLinearMap . curryLinearMap
                         $ recomposeContraLinMapTensor fw
                                 (fmap (\(LinearMap(_,Tensor tv))->LinearMap tv) dds) )
  uncanonicallyFromDual = case ( dualSpaceWitness :: DualSpaceWitness u
                               , dualSpaceWitness :: DualSpaceWitness v ) of
        (DualSpaceWitness,DualSpaceWitness)
            -> uncanonicallyFromDual *** uncanonicallyFromDual
  uncanonicallyToDual = case ( dualSpaceWitness :: DualSpaceWitness u
                             , dualSpaceWitness :: DualSpaceWitness v ) of
        (DualSpaceWitness,DualSpaceWitness)
            -> uncanonicallyToDual *** uncanonicallyToDual
  
deriving instance (Show (SubBasis u), Show (SubBasis v))
                    => Show (SubBasis (u,v))


instance ∀ s u v .
         ( FiniteDimensional u, FiniteDimensional v
         , Scalar u~s, Scalar v~s, Scalar (DualVector u)~s, Scalar (DualVector v)~s
         , Fractional' (Scalar v) )
            => FiniteDimensional (Tensor s u v) where
  data SubBasis (Tensor s u v) = TensorBasis !(SubBasis u) !(SubBasis v)
  entireBasis = TensorBasis entireBasis entireBasis
  enumerateSubBasis (TensorBasis bu bv)
       = [ u⊗v | u <- enumerateSubBasis bu, v <- enumerateSubBasis bv ]
  subbasisDimension (TensorBasis bu bv) = subbasisDimension bu * subbasisDimension bv
  decomposeLinMap = dlm dualSpaceWitness
   where dlm :: ∀ w . (LSpace w, Scalar w ~ Scalar v) 
                   => DualSpaceWitness w -> ((u⊗v)+>w) -> (SubBasis (u⊗v), DList w)
         dlm DualSpaceWitness muvw = case decomposeLinMap $ curryLinearMap $ muvw of
           (bu, mvwsg) -> first (TensorBasis bu) . go $ mvwsg []
          where (go, _) = tensorLinmapDecompositionhelpers
  decomposeLinMapWithin = dlm dualSpaceWitness
   where dlm :: ∀ w . (LSpace w, Scalar w ~ Scalar v) 
                   => DualSpaceWitness w -> SubBasis (u⊗v)
                          -> ((u⊗v)+>w) -> Either (SubBasis (u⊗v), DList w) (DList w)
         dlm DualSpaceWitness (TensorBasis bu bv) muvw
               = case decomposeLinMapWithin bu $ curryLinearMap $ muvw of
           Left (bu', mvwsg) -> let (_, (bv', ws)) = goWith bv id (mvwsg []) id
                                in Left (TensorBasis bu' bv', ws)
           Right mvwsg -> let (changed, (bv', ws)) = goWith bv id (mvwsg []) id
                          in if changed
                              then Left (TensorBasis bu bv', ws)
                              else Right ws
          where (_, goWith) = tensorLinmapDecompositionhelpers
  recomposeSB (TensorBasis bu bv) = recomposeSBTensor bu bv
  recomposeSBTensor = rst dualSpaceWitness
   where rst :: ∀ w . (FiniteDimensional w, Scalar w ~ s)
                  => DualSpaceWitness w -> SubBasis (u⊗v)
                               -> SubBasis w -> [s] -> ((u⊗v)⊗w, [s])
         rst DualSpaceWitness (TensorBasis bu bv) bw
          = first (arr lassocTensor) . recomposeSBTensor bu (TensorBasis bv bw)
  recomposeLinMap = rlm dualSpaceWitness
   where rlm :: ∀ w . (LSpace w, Scalar w ~ Scalar v) 
                   => DualSpaceWitness w -> SubBasis (u⊗v) -> [w]
                                -> ((u⊗v)+>w, [w])
         rlm DualSpaceWitness (TensorBasis bu bv) ws
             = ( uncurryLinearMap $ fst . recomposeLinMap bu
                           $ unfoldr (pure . recomposeLinMap bv) ws
               , drop (subbasisDimension bu * subbasisDimension bv) ws )
  recomposeContraLinMap = case dualSpaceWitness :: DualSpaceWitness u of
     DualSpaceWitness -> recomposeContraLinMapTensor
  recomposeContraLinMapTensor = rclt dualSpaceWitness dualSpaceWitness
   where rclt :: ∀ u' w f . ( FiniteDimensional u', Scalar u' ~ s
                            , LinearSpace w, Scalar w ~ s
                            , Hask.Functor f )
                  => DualSpaceWitness u -> DualSpaceWitness u'
                   -> (f (Scalar w) -> w)
                    -> f (Tensor s u v +> DualVector u')
                    -> (Tensor s u v ⊗ u') +> w
         rclt DualSpaceWitness DualSpaceWitness fw dds
              = uncurryLinearMap . uncurryLinearMap
                             . fmap (curryLinearMap) . curryLinearMap
               $ recomposeContraLinMapTensor fw $ fmap (arr curryLinearMap) dds
  uncanonicallyToDual = case ( dualSpaceWitness :: DualSpaceWitness u
                             , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualSpaceWitness, DualSpaceWitness) -> fmap uncanonicallyToDual 
            >>> transposeTensor >>> fmap uncanonicallyToDual
            >>> transposeTensor >>> arr fromTensor
  uncanonicallyFromDual = case ( dualSpaceWitness :: DualSpaceWitness u
                               , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualSpaceWitness, DualSpaceWitness) -> arr asTensor
            >>> fmap uncanonicallyFromDual 
            >>> transposeTensor >>> fmap uncanonicallyFromDual
            >>> transposeTensor

tensorLinmapDecompositionhelpers
      :: ( FiniteDimensional v, LSpace w , Scalar v~s, Scalar w~s )
      => ( [v+>w] -> (SubBasis v, DList w)
         , SubBasis v -> DList w -> [v+>w] -> DList (v+>w)
                        -> (Bool, (SubBasis v, DList w)) )
tensorLinmapDecompositionhelpers = (go, goWith)
   where go [] = decomposeLinMap zeroV
         go (mvw:mvws) = case decomposeLinMap mvw of
              (bv, cfs) -> snd (goWith bv cfs mvws (mvw:))
         goWith bv prevdc [] prevs = (False, (bv, prevdc))
         goWith bv prevdc (mvw:mvws) prevs = case decomposeLinMapWithin bv mvw of
              Right cfs -> goWith bv (prevdc . cfs) mvws (prevs . (mvw:))
              Left (bv', cfs) -> first (const True)
                                 ( goWith bv' (regoWith bv' (prevs[]) . cfs)
                                     mvws (prevs . (mvw:)) )
         regoWith _ [] = id
         regoWith bv (mvw:mvws) = case decomposeLinMapWithin bv mvw of
              Right cfs -> cfs . regoWith bv mvws
              Left _ -> error $
               "Misbehaved FiniteDimensional instance: `decomposeLinMapWithin` should,\
             \\nif it cannot decompose in the given basis, do so in a proper\
             \\nsuperbasis of the given one (so that any vector that could be\
             \\ndecomposed in the old basis can also be decomposed in the new one)."
  
deriving instance (Show (SubBasis u), Show (SubBasis v))
             => Show (SubBasis (Tensor s u v))

instance ∀ s v .
         ( FiniteDimensional v, Scalar v~s, Scalar (DualVector v)~s
         , RealFloat' s )
            => FiniteDimensional (SymmetricTensor s v) where
  newtype SubBasis (SymmetricTensor s v) = SymTensBasis (SubBasis v)
  entireBasis = SymTensBasis entireBasis
  enumerateSubBasis (SymTensBasis b) = do
        v:vs <- tails $ enumerateSubBasis b
        squareV v
          : [ (squareV (v^+^w) ^-^ squareV v ^-^ squareV w) ^* sqrt¹₂ | w <- vs ]
   where sqrt¹₂ = sqrt 0.5
  subbasisDimension (SymTensBasis b) = ((n-1)*n)`quot`2
   where n = subbasisDimension b
  decomposeLinMap = dclm dualSpaceWitness
   where dclm (DualSpaceWitness :: DualSpaceWitness v) (LinearMap f)
                    = (SymTensBasis bf, rmRedundant 0 . symmetrise $ dlw [])
          where rmRedundant _ [] = id
                rmRedundant k (row:rest)
                    = (sclOffdiag (drop k row)++) . rmRedundant (k+1) rest
                symmetrise l = zipWith (zipWith (^+^)) lm $ transpose lm
                 where lm = matr l
                matr [] = []
                matr l = case splitAt n l of
                    (row,rest) -> row : matr rest
                n = case subbasisDimension bf of
                      nbf | nbf == subbasisDimension bf'  -> nbf
                (LinMapBasis bf bf', dlw)
                    = decomposeLinMap $ asLinearMap . lassocTensor $ f
                sclOffdiag (d:o) = 0.5*^d : ((^*sqrt¹₂)<$>o)
         sqrt¹₂ = sqrt 0.5 :: s
  recomposeSB = rclm dualSpaceWitness
   where rclm (DualSpaceWitness :: DualSpaceWitness v) (SymTensBasis b) ws
           = case recomposeSB (TensorBasis b b)
                    $ mkSym (subbasisDimension b) (repeat id) ws of
              (t, remws) -> (SymTensor t, remws)
         mkSym _ _ [] = []
         mkSym 0 _ ws = ws
         mkSym n (sd₀:sds) ws = let (d:o,rest) = splitAt n ws
                                    oscld = (sqrt 0.5*)<$>o
                                in sd₀ [] ++ [d] ++ oscld
                                     ++ mkSym (n-1) (zipWith (.) sds $ (:)<$>oscld) rest
  recomposeLinMap = rclm dualSpaceWitness
   where rclm (DualSpaceWitness :: DualSpaceWitness v) (SymTensBasis b) ws
           = case recomposeLinMap (LinMapBasis b b)
                    $ mkSym (subbasisDimension b) (repeat id) ws of
              (f, remws) -> (LinearMap $ rassocTensor . asTensor $ f, remws)
         mkSym _ _ [] = []
         mkSym 0 _ ws = ws
         mkSym n (sd₀:sds) ws = let (d:o,rest) = splitAt n ws
                                    oscld = (sqrt 0.5*^)<$>o
                                in sd₀ [] ++ [d] ++ oscld
                                     ++ mkSym (n-1) (zipWith (.) sds $ (:)<$>oscld) rest
  recomposeSBTensor = rcst
   where rcst :: ∀ w . (FiniteDimensional w, Scalar w ~ s)
                => SubBasis (SymmetricTensor s v) -> SubBasis w
                   -> [s] -> (Tensor s (SymmetricTensor s v) w, [s])
         rcst (SymTensBasis b) bw μs
           = case recomposeSBTensor (TensorBasis b b) bw
                    $ mkSym (subbasisDimension bw) (subbasisDimension b) (repeat id) μs of
              (Tensor t, remws) -> ( Tensor $ Tensor t
                                      :: Tensor s (SymmetricTensor s v) w
                                   , remws )
         mkSym _ _ _ [] = []
         mkSym _ 0 _ ws = ws
         mkSym nw n (sd₀:sds) ws = let (d:o,rest) = multiSplit nw n ws
                                       oscld = map (sqrt 0.5*)<$>o
                                   in concat (sd₀ []) ++ d ++ concat oscld
                                       ++ mkSym nw (n-1) (zipWith (.) sds $ (:)<$>oscld) rest
  recomposeContraLinMap f tenss
           = LinearMap . arr (rassocTensor . asTensor) . rcCLM dualSpaceWitness f
                                    $ fmap getSymmetricTensor tenss
   where rcCLM :: (Hask.Functor f, LinearSpace w, s~Scalar w)
           => DualSpaceWitness v
                 -> (f s->w) -> f (Tensor s (DualVector v) (DualVector v))
                     -> LinearMap s (LinearMap s (DualVector v) v) w
         rcCLM DualSpaceWitness f = recomposeContraLinMap f
  uncanonicallyFromDual = case dualSpaceWitness :: DualSpaceWitness v of
     DualSpaceWitness -> LinearFunction
          $ \(SymTensor t) -> SymTensor $ arr fromLinearMap . uncanonicallyFromDual $ t
  uncanonicallyToDual = case dualSpaceWitness :: DualSpaceWitness v of
     DualSpaceWitness -> LinearFunction
          $ \(SymTensor t) -> SymTensor $ uncanonicallyToDual . arr asLinearMap $ t
  
deriving instance (Show (SubBasis v)) => Show (SubBasis (SymmetricTensor s v))


instance ∀ s u v .
         ( LSpace u, FiniteDimensional (DualVector u), FiniteDimensional v
         , Scalar u~s, Scalar v~s, Scalar (DualVector v)~s, Fractional' (Scalar v) )
            => FiniteDimensional (LinearMap s u v) where
  data SubBasis (LinearMap s u v) = LinMapBasis !(SubBasis (DualVector u)) !(SubBasis v)
  entireBasis = case ( dualSpaceWitness :: DualSpaceWitness u
                     , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualSpaceWitness, DualSpaceWitness)
           -> case entireBasis of TensorBasis bu bv -> LinMapBasis bu bv
  enumerateSubBasis
          = case ( dualSpaceWitness :: DualSpaceWitness u
                 , dualSpaceWitness :: DualSpaceWitness v )  of
     (DualSpaceWitness, DualSpaceWitness) -> \(LinMapBasis bu bv)
                   -> arr (fmap asLinearMap) . enumerateSubBasis $ TensorBasis bu bv
  subbasisDimension (LinMapBasis bu bv) = subbasisDimension bu * subbasisDimension bv
  decomposeLinMap = case ( dualSpaceWitness :: DualSpaceWitness u
                         , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualSpaceWitness, DualSpaceWitness)
              -> first (\(TensorBasis bu bv)->LinMapBasis bu bv)
                    . decomposeLinMap . coerce
  decomposeLinMapWithin = case ( dualSpaceWitness :: DualSpaceWitness u
                               , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualSpaceWitness, DualSpaceWitness)
        -> \(LinMapBasis bu bv) m
         -> case decomposeLinMapWithin (TensorBasis bu bv) (coerce m) of
              Right ws -> Right ws
              Left (TensorBasis bu' bv', ws) -> Left (LinMapBasis bu' bv', ws)
  recomposeSB = case ( dualSpaceWitness :: DualSpaceWitness u
                     , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualSpaceWitness, DualSpaceWitness) -> \(LinMapBasis bu bv)
        -> recomposeSB (TensorBasis bu bv) >>> first (arr fromTensor)
  recomposeSBTensor = case ( dualSpaceWitness :: DualSpaceWitness u
                           , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualSpaceWitness, DualSpaceWitness) -> \(LinMapBasis bu bv) bw
        -> recomposeSBTensor (TensorBasis bu bv) bw >>> first coerce
  recomposeLinMap = rlm dualSpaceWitness dualSpaceWitness
   where rlm :: ∀ w . (LSpace w, Scalar w ~ Scalar v) 
                   => DualSpaceWitness u -> DualSpaceWitness w -> SubBasis (u+>v) -> [w]
                                -> ((u+>v)+>w, [w])
         rlm DualSpaceWitness DualSpaceWitness (LinMapBasis bu bv) ws
             = ( coUncurryLinearMap . fromLinearMap $ fst . recomposeLinMap bu
                           $ unfoldr (pure . recomposeLinMap bv) ws
               , drop (subbasisDimension bu * subbasisDimension bv) ws )
  recomposeContraLinMap = case ( dualSpaceWitness :: DualSpaceWitness u
                               , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualSpaceWitness, DualSpaceWitness) -> \fw dds
       -> argFromTensor $ recomposeContraLinMapTensor fw $ fmap (arr asLinearMap) dds
  recomposeContraLinMapTensor = rclmt dualSpaceWitness dualSpaceWitness dualSpaceWitness
   where rclmt :: ∀ f u' w . ( LinearSpace w, FiniteDimensional u'
                             , Scalar w ~ s, Scalar u' ~ s
                             , Hask.Functor f )
                  => DualSpaceWitness u -> DualSpaceWitness v -> DualSpaceWitness u'
                   -> (f (Scalar w) -> w) -> f ((u+>v)+>DualVector u') -> ((u+>v)⊗u')+>w
         rclmt DualSpaceWitness DualSpaceWitness DualSpaceWitness fw dds
          = uncurryLinearMap . coUncurryLinearMap
           . fmap curryLinearMap . coCurryLinearMap . argFromTensor
             $ recomposeContraLinMapTensor fw
               $ fmap (arr $ asLinearMap . coCurryLinearMap) dds
  uncanonicallyToDual = case ( dualSpaceWitness :: DualSpaceWitness u
                             , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualSpaceWitness, DualSpaceWitness)
           -> arr asTensor >>> fmap uncanonicallyToDual >>> transposeTensor
              >>> fmap uncanonicallyToDual >>> transposeTensor
  uncanonicallyFromDual = case ( dualSpaceWitness :: DualSpaceWitness u
                               , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualSpaceWitness, DualSpaceWitness)
           -> arr fromTensor <<< fmap uncanonicallyFromDual <<< transposeTensor
              <<< fmap uncanonicallyFromDual <<< transposeTensor
  
deriving instance (Show (SubBasis (DualVector u)), Show (SubBasis v))
             => Show (SubBasis (LinearMap s u v))


infixr 0 \$

-- | Inverse function application, aka solving of a linear system:
--   
-- @
-- f '\$' f '$' v  ≡  v
-- 
-- f '$' f '\$' u  ≡  u
-- @
-- 
-- If @f@ does not have full rank, the behaviour is undefined. However, it
-- does not need to be a proper isomorphism: the
-- first of the above equations is still fulfilled if only @f@ is /injective/
-- (overdetermined system) and the second if it is /surjective/.
-- 
-- If you want to solve for multiple RHS vectors, be sure to partially
-- apply this operator to the linear map, like
-- 
-- @
-- map (f '\$') [v₁, v₂, ...]
-- @
-- 
-- Since most of the work is actually done in triangularising the operator,
-- this may be much faster than
-- 
-- @
-- [f '\$' v₁, f '\$' v₂, ...]
-- @
(\$) :: ∀ u v . ( SimpleSpace u, SimpleSpace v, Scalar u ~ Scalar v )
          => (u+>v) -> v -> u
(\$) m
  | du > dv    = ((applyLinear-+$>unsafeRightInverse m)-+$>)
  | du < dv    = ((applyLinear-+$>unsafeLeftInverse m)-+$>)
  | otherwise  = let v's = dualBasis $ mdecomp []
                     (mbas, mdecomp) = decomposeLinMap m
                 in fst . \v -> recomposeSB mbas [ maybe 0 (<.>^v) v' | v' <- v's ]
 where du = subbasisDimension (entireBasis :: SubBasis u)
       dv = subbasisDimension (entireBasis :: SubBasis v)
    

pseudoInverse :: ∀ u v . ( SimpleSpace u, SimpleSpace v, Scalar u ~ Scalar v )
          => (u+>v) -> v+>u
pseudoInverse m
  | du > dv    = unsafeRightInverse m
  | du < dv    = unsafeLeftInverse m
  | otherwise  = unsafeInverse m
 where du = subbasisDimension (entireBasis :: SubBasis u)
       dv = subbasisDimension (entireBasis :: SubBasis v)

-- | If @f@ is injective, then
-- 
-- @
-- unsafeLeftInverse f . f  ≡  id
-- @
unsafeLeftInverse :: ∀ u v . ( SimpleSpace u, SimpleSpace v, Scalar u ~ Scalar v )
                     => (u+>v) -> v+>u
unsafeLeftInverse = uli dualSpaceWitness dualSpaceWitness
 where uli :: DualSpaceWitness u -> DualSpaceWitness v -> (u+>v) -> v+>u
       uli DualSpaceWitness DualSpaceWitness m
             = unsafeInverse (m' . (fmap uncanonicallyToDual $ m))
                         . m' . arr uncanonicallyToDual
        where m' = adjoint $ m :: DualVector v +> DualVector u

-- | If @f@ is surjective, then
-- 
-- @
-- f . unsafeRightInverse f  ≡  id
-- @
unsafeRightInverse :: ∀ u v . ( SimpleSpace u, SimpleSpace v, Scalar u ~ Scalar v )
                     => (u+>v) -> v+>u
unsafeRightInverse = uri dualSpaceWitness dualSpaceWitness
 where uri :: DualSpaceWitness u -> DualSpaceWitness v -> (u+>v) -> v+>u
       uri DualSpaceWitness DualSpaceWitness m
             = (fmap uncanonicallyToDual $ m')
                          . unsafeInverse (m . (fmap uncanonicallyToDual $ m'))
        where m' = adjoint $ m :: DualVector v +> DualVector u

-- | Invert an isomorphism. For other linear maps, the result is undefined.
unsafeInverse :: ( SimpleSpace u, SimpleSpace v, Scalar u ~ Scalar v )
          => (u+>v) -> v+>u
unsafeInverse m = recomposeContraLinMap (fst . recomposeSB mbas)
                                        $ [maybe zeroV id v' | v'<-v's]
 where v's = dualBasis $ mdecomp []
       (mbas, mdecomp) = decomposeLinMap m


-- | The <https://en.wikipedia.org/wiki/Riesz_representation_theorem Riesz representation theorem>
--   provides an isomorphism between a Hilbert space and its (continuous) dual space.
riesz :: ∀ v . (FiniteDimensional v, InnerSpace v) => DualVector v -+> v
riesz = case ( scalarSpaceWitness :: ScalarSpaceWitness v
             , dualSpaceWitness :: DualSpaceWitness v ) of
 (ScalarSpaceWitness,DualSpaceWitness) -> LinearFunction $ \dv ->
       let (bas, compos) = decomposeLinMap $ sampleLinearFunction $ applyDualVector $ dv
       in fst . recomposeSB bas $ compos []

sRiesz :: ∀ v . FiniteDimensional v => DualSpace v -+> v
sRiesz = case ( scalarSpaceWitness :: ScalarSpaceWitness v
              , dualSpaceWitness :: DualSpaceWitness v ) of
 (ScalarSpaceWitness,DualSpaceWitness) -> LinearFunction $ \dv ->
       let (bas, compos) = decomposeLinMap $ dv
       in fst . recomposeSB bas $ compos []

coRiesz :: ∀ v . (LSpace v, InnerSpace v) => v -+> DualVector v
coRiesz = case ( scalarSpaceWitness :: ScalarSpaceWitness v
               , dualSpaceWitness :: DualSpaceWitness v ) of
 (ScalarSpaceWitness,DualSpaceWitness)
      -> fromFlatTensor . arr asTensor . sampleLinearFunction . inner

-- | Functions are generally a pain to display, but since linear functionals
--   in a Hilbert space can be represented by /vectors/ in that space,
--   this can be used for implementing a 'Show' instance.
showsPrecAsRiesz :: ∀ v . ( FiniteDimensional v, InnerSpace v, Show v
                          , HasBasis (Scalar v), Basis (Scalar v) ~ () )
                      => Int -> DualSpace v -> ShowS
showsPrecAsRiesz = case ( scalarSpaceWitness :: ScalarSpaceWitness v
                        , dualSpaceWitness :: DualSpaceWitness v ) of
 (ScalarSpaceWitness,DualSpaceWitness)
      -> \p dv -> showParen (p>0) $ ("().<"++) . showsPrec 7 (sRiesz$dv)

instance Show (LinearMap ℝ (ZeroDim ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V0 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ ℝ ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V1 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V2 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V3 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V4 ℝ) ℝ) where showsPrec = showsPrecAsRiesz

class TensorDecomposable u => RieszDecomposable u where
  rieszDecomposition :: (FiniteDimensional v, v ~ DualVector v, Scalar v ~ Scalar u)
              => (v +> u) -> [(Basis u, v)]

instance RieszDecomposable ℝ where
  rieszDecomposition (LinearMap r) = [((), fromFlatTensor $ Tensor r)]
instance ( RieszDecomposable x, RieszDecomposable y
         , Scalar x ~ Scalar y, Scalar (DualVector x) ~ Scalar (DualVector y) )
              => RieszDecomposable (x,y) where
  rieszDecomposition m = map (first Left) (rieszDecomposition $ fst . m)
                      ++ map (first Right) (rieszDecomposition $ snd . m)

instance RieszDecomposable (ZeroDim ℝ) where
  rieszDecomposition _ = []
instance RieszDecomposable (V0 ℝ) where
  rieszDecomposition _ = []
instance RieszDecomposable (V1 ℝ) where
  rieszDecomposition m = [(ex, sRiesz $ fmap (LinearFunction (^._x)) $ m)]
instance RieszDecomposable (V2 ℝ) where
  rieszDecomposition m = [ (ex, sRiesz $ fmap (LinearFunction (^._x)) $ m)
                         , (ey, sRiesz $ fmap (LinearFunction (^._y)) $ m) ]
instance RieszDecomposable (V3 ℝ) where
  rieszDecomposition m = [ (ex, sRiesz $ fmap (LinearFunction (^._x)) $ m)
                         , (ey, sRiesz $ fmap (LinearFunction (^._y)) $ m)
                         , (ez, sRiesz $ fmap (LinearFunction (^._z)) $ m) ]
instance RieszDecomposable (V4 ℝ) where
  rieszDecomposition m = [ (ex, sRiesz $ fmap (LinearFunction (^._x)) $ m)
                         , (ey, sRiesz $ fmap (LinearFunction (^._y)) $ m)
                         , (ez, sRiesz $ fmap (LinearFunction (^._z)) $ m)
                         , (ew, sRiesz $ fmap (LinearFunction (^._w)) $ m) ]

infixl 7 .<

-- | Outer product of a general @v@-vector and a basis element from @w@.
--   Note that this operation is in general pretty inefficient; it is
--   provided mostly to lay out matrix definitions neatly.
(.<) :: ( FiniteDimensional v, Num' (Scalar v)
        , InnerSpace v, LSpace w, HasBasis w, Scalar v ~ Scalar w )
           => Basis w -> v -> v+>w
bw .< v = sampleLinearFunction $ LinearFunction $ \v' -> recompose [(bw, v<.>v')]


rieszDecomposeShowsPrec :: ∀ u v s . ( RieszDecomposable u
                                     , FiniteDimensional v, v ~ DualVector v, Show v
                                     , Scalar u ~ s, Scalar v ~ s )
                        => Int -> LinearMap s v u -> ShowS
rieszDecomposeShowsPrec p m = case rieszDecomposition m of
            [] -> ("zeroV"++)
            ((b₀,dv₀):dvs) -> showParen (p>6)
                            $ \s -> showsPrecBasis ([]::[u]) 7 b₀
                                                     . (".<"++) . showsPrec 7 dv₀
                                  $ foldr (\(b,dv)
                                        -> (" ^+^ "++) . showsPrecBasis ([]::[u]) 7 b
                                                       . (".<"++) . showsPrec 7 dv) s dvs
                                  
instance Show (LinearMap s v (ZeroDim s)) where
  show _ = "zeroV"
instance Show (LinearMap s v (V0 s)) where
  show _ = "zeroV"
instance (FiniteDimensional v, v ~ DualVector v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V1 ℝ)) where
  showsPrec = rieszDecomposeShowsPrec
instance (FiniteDimensional v, v ~ DualVector v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V2 ℝ)) where
  showsPrec = rieszDecomposeShowsPrec
instance (FiniteDimensional v, v ~ DualVector v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V3 ℝ)) where
  showsPrec = rieszDecomposeShowsPrec
instance (FiniteDimensional v, v ~ DualVector v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V4 ℝ)) where
  showsPrec = rieszDecomposeShowsPrec

instance ( FiniteDimensional v, v ~ DualVector v, Show v
         , RieszDecomposable x, RieszDecomposable y
         , Scalar x ~ s, Scalar y ~ s, Scalar v ~ s
         , Scalar (DualVector x) ~ s, Scalar (DualVector y) ~ s )
              => Show (LinearMap s v (x,y)) where
  showsPrec = case
      (dualSpaceWitness::DualSpaceWitness x, dualSpaceWitness::DualSpaceWitness y) of
      (DualSpaceWitness, DualSpaceWitness) -> rieszDecomposeShowsPrec


infixr 7 .⊗

(.⊗) :: ( TensorSpace v, HasBasis v, TensorSpace w
        , Num' (Scalar v), Scalar v ~ Scalar w )
         => Basis v -> w -> v⊗w
b .⊗ w = basisValue b ⊗ w

class (FiniteDimensional v, HasBasis v) => TensorDecomposable v where
  tensorDecomposition :: v⊗w -> [(Basis v, w)]
  showsPrecBasis :: Hask.Functor p => p v -> Int -> Basis v -> ShowS

instance TensorDecomposable ℝ where
  tensorDecomposition (Tensor r) = [((), r)]
  showsPrecBasis _ _ = shows
instance ( TensorDecomposable x, TensorDecomposable y
         , Scalar x ~ Scalar y, Scalar (DualVector x) ~ Scalar (DualVector y) )
              => TensorDecomposable (x,y) where
  tensorDecomposition (Tensor (tx,ty))
                = map (first Left) (tensorDecomposition tx)
               ++ map (first Right) (tensorDecomposition ty)
  showsPrecBasis proxy p (Left bx)
      = showParen (p>9) $ ("Left "++) . showsPrecBasis (fst<$>proxy) 10 bx
  showsPrecBasis proxy p (Right by)
      = showParen (p>9) $ ("Right "++) . showsPrecBasis (snd<$>proxy) 10 by

instance TensorDecomposable (ZeroDim ℝ) where
  tensorDecomposition _ = []
  showsPrecBasis _ _ = absurd
instance TensorDecomposable (V0 ℝ) where
  tensorDecomposition _ = []
  showsPrecBasis _ _ (Mat.E q) = (V0^.q ++)
instance TensorDecomposable (V1 ℝ) where
  tensorDecomposition (Tensor (V1 w)) = [(ex, w)]
  showsPrecBasis _ _ (Mat.E q) = (V1"ex"^.q ++)
instance TensorDecomposable (V2 ℝ) where
  tensorDecomposition (Tensor (V2 x y)) = [ (ex, x), (ey, y) ]
  showsPrecBasis _ _ (Mat.E q) = (V2"ex""ey"^.q ++)
instance TensorDecomposable (V3 ℝ) where
  tensorDecomposition (Tensor (V3 x y z)) = [ (ex, x), (ey, y), (ez, z) ]
  showsPrecBasis _ _ (Mat.E q) = (V3"ex""ey""ez"^.q ++)
instance TensorDecomposable (V4 ℝ) where
  tensorDecomposition (Tensor (V4 x y z w)) = [ (ex, x), (ey, y), (ez, z), (ew, w) ]
  showsPrecBasis _ _ (Mat.E q) = (V4"ex""ey""ez""ew"^.q ++)

tensorDecomposeShowsPrec :: ∀ u v s
  . ( TensorDecomposable u, FiniteDimensional v, Show v, Scalar u ~ s, Scalar v ~ s )
                        => Int -> Tensor s u v -> ShowS
tensorDecomposeShowsPrec p t = case tensorDecomposition t of
            [] -> ("zeroV"++)
            ((b₀,dv₀):dvs) -> showParen (p>6)
                            $ \s -> showsPrecBasis ([]::[u]) 7 b₀
                                                     . (".⊗"++) . showsPrec 7 dv₀
                                  $ foldr (\(b,dv)
                                        -> (" ^+^ "++) . showsPrecBasis ([]::[u]) 7 b
                                                       . (".⊗"++) . showsPrec 7 dv) s dvs

instance Show (Tensor s (V0 s) v) where
  show _ = "zeroV"
instance (FiniteDimensional v, v ~ DualVector v, Scalar v ~ ℝ, Show v)
              => Show (Tensor ℝ (V1 ℝ) v) where
  showsPrec = tensorDecomposeShowsPrec
instance (FiniteDimensional v, v ~ DualVector v, Scalar v ~ ℝ, Show v)
              => Show (Tensor ℝ (V2 ℝ) v) where
  showsPrec = tensorDecomposeShowsPrec
instance (FiniteDimensional v, v ~ DualVector v, Scalar v ~ ℝ, Show v)
              => Show (Tensor ℝ (V3 ℝ) v) where
  showsPrec = tensorDecomposeShowsPrec
instance (FiniteDimensional v, v ~ DualVector v, Scalar v ~ ℝ, Show v)
              => Show (Tensor ℝ (V4 ℝ) v) where
  showsPrec = tensorDecomposeShowsPrec

instance ( FiniteDimensional v, v ~ DualVector v, Show v
         , TensorDecomposable x, TensorDecomposable y
         , Scalar x ~ s, Scalar y ~ s, Scalar v ~ s )
              => Show (Tensor s (x,y) v) where
  showsPrec = case
      (dualSpaceWitness::DualSpaceWitness x, dualSpaceWitness::DualSpaceWitness y) of
      (DualSpaceWitness, DualSpaceWitness) -> tensorDecomposeShowsPrec


(^) :: Num a => a -> Int -> a
(^) = (Hask.^)
 

type HilbertSpace v = (LSpace v, InnerSpace v, DualVector v ~ v)

type RealFrac' s = (Fractional' s, IEEE s, InnerSpace s)
type RealFloat' s = (RealFrac' s, Floating s)

type SimpleSpace v = ( FiniteDimensional v, FiniteDimensional (DualVector v)
                     , SemiInner v, SemiInner (DualVector v)
                     , RealFrac' (Scalar v) )


instance ∀ s u v .
         ( FiniteDimensional u, LSpace v, FiniteFreeSpace v
         , Scalar u~s, Scalar v~s ) => FiniteFreeSpace (LinearMap s u v) where
  freeDimension _ = subbasisDimension (entireBasis :: SubBasis u)
                       * freeDimension ([]::[v])
  toFullUnboxVect = decomposeLinMapWithin entireBasis >>> \case
            Right l -> UArr.concat $ toFullUnboxVect <$> l []
  unsafeFromFullUnboxVect arrv = fst . recomposeLinMap entireBasis
          $ [unsafeFromFullUnboxVect $ UArr.slice (dv*j) dv arrv | j <- [0 .. du-1]]
   where du = subbasisDimension (entireBasis :: SubBasis u)
         dv = freeDimension ([]::[v])

instance ∀ s u v .
         ( LSpace u, FiniteDimensional (DualVector u), LSpace v, FiniteFreeSpace v
         , Scalar u~s, Scalar v~s, Scalar (DualVector u)~s, Scalar (DualVector v)~s )
               => FiniteFreeSpace (Tensor s u v) where
  freeDimension _ = subbasisDimension (entireBasis :: SubBasis (DualVector u))
                        * freeDimension ([]::[v])
  toFullUnboxVect = arr asLinearMap >>> decomposeLinMapWithin entireBasis >>> \case
            Right l -> UArr.concat $ toFullUnboxVect <$> l []
  unsafeFromFullUnboxVect arrv = fromLinearMap $ fst . recomposeLinMap entireBasis
          $ [unsafeFromFullUnboxVect $ UArr.slice (dv*j) dv arrv | j <- [0 .. du-1]]
   where du = subbasisDimension (entireBasis :: SubBasis (DualVector u))
         dv = freeDimension ([]::[v])
  
instance ∀ s u v .
         ( FiniteDimensional u, LSpace v, FiniteFreeSpace v
         , Scalar u~s, Scalar v~s ) => FiniteFreeSpace (LinearFunction s u v) where
  freeDimension _ = subbasisDimension (entireBasis :: SubBasis u)
                       * freeDimension ([]::[v])
  toFullUnboxVect f = toFullUnboxVect (arr f :: LinearMap s u v)
  unsafeFromFullUnboxVect arrv = arr (unsafeFromFullUnboxVect arrv :: LinearMap s u v)
                                     
  

-- | For real matrices, this boils down to 'transpose'.
--   For free complex spaces it also incurs complex conjugation.
--   
-- The signature can also be understood as
--
-- @
-- adjoint :: (v +> w) -> (DualVector w +> DualVector v)
-- @
-- 
-- Or
--
-- @
-- adjoint :: (DualVector v +> DualVector w) -> (w +> v)
-- @
-- 
-- But /not/ @(v+>w) -> (w+>v)@, in general (though in a Hilbert space, this too is
-- equivalent, via 'riesz' isomorphism).
adjoint :: ∀ v w . (LinearSpace v, LinearSpace w, Scalar v ~ Scalar w)
               => (v +> DualVector w) -+> (w +> DualVector v)
adjoint = case ( dualSpaceWitness :: DualSpaceWitness v
               , dualSpaceWitness :: DualSpaceWitness w ) of
   (DualSpaceWitness, DualSpaceWitness)
          -> arr fromTensor . transposeTensor . arr asTensor




multiSplit :: Int -> Int -> [a] -> ([[a]], [a])
multiSplit chunkSize 0 l = ([],l)
multiSplit chunkSize nChunks l = case splitAt chunkSize l of
    (chunk, rest) -> first (chunk:) $ multiSplit chunkSize (nChunks-1) rest

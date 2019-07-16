{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module
    Control.Arrow.Alg ( 
        ArrVar(),
        ArrAlg(..),
        ArrCtx(..),
        refer,
        embA,
        procA
      ) 
where

import Prelude hiding (id, (.), fst, snd, uncurry)
import Control.Category
import Control.Arrow hiding (first, second, (&&&), (***))
import Control.Monad.Indexed
import GHC.TypeLits
import GHC.Exts
import Control.Categorical.Bifunctor
import Control.Categorical.Object
import Control.Category.Associative
import Control.Category.Braided
import Control.Category.Cartesian
import Control.Category.Cartesian.Closed
import Control.Category.Distributive
import Control.Category.Monoidal
import Data.Profunctor

data Available a = Available a
data Consumed = Consumed

type family VarType m :: *
  where
    VarType (Available a, ()) = a
    VarType (a, (b, c)) = VarType (b, c)

type family PushBack b m
  where
    PushBack b (a, n) = (a, PushBack b n)
    PushBack b () = (b, ())
    
type family Flux' r m
  where
    Flux' r () = r
    Flux' r (Available a, n) = Flux' (a, r) n
    Flux' r (Consumed, n) = Flux' r n
    
type Flux m = Flux' () m

type Braided' k = Braided k (,)
type Monoidal' k = (Monoidal k (,), Id k (,) ~ ())
type Cartesian' k = (Cartesian k, Product k ~ (,), Id k (,) ~ ())

class IsHistory' r t
  where
    pushBackFlux :: Category ar => ar (a, Flux' r t) (Flux' r (PushBack (Available a) t))
    braidOut :: Braided' ar => ar s (a, r) -> ar (Flux' s t) (a, Flux' r t) 

type IsHistory t = IsHistory' () t

instance IsHistory' r ()
  where
    pushBackFlux = id
    braidOut f = f

instance IsHistory' (a, r) t => IsHistory' r (Available a, t)
  where
    pushBackFlux = pushBackFlux @(a, r) @t
    braidOut f = braidOut @(a, r) @t (second f >>> disassociate >>> first braid >>> associate)

instance IsHistory' r t => IsHistory' r (Consumed, t)
  where
    pushBackFlux = pushBackFlux @r @t
    braidOut f = braidOut @r @t f

type family Compat a b :: Constraint
  where
    Compat (Available a) (Available a) = ()
    Compat (Available a) Consumed = ()

class IsHistory' r hist => Causal' r m hist
  where
    type ConsumedHist r m hist :: *
    getConsumed :: (Braided' ar, Monoidal' ar) => ar (Flux' r hist) (VarType m, ConsumedFlux' r m hist)
    getRefer :: Cartesian' ar => ar (Flux' r hist) (VarType m, Flux' r hist)

type Causal = Causal' ()

instance (IsHistory' (a, r) hist, IsHistory' r hist) => Causal' r (Available a, ()) (Available a, hist)
  where
    type ConsumedHist r (Available a, ()) (Available a, hist) = hist
    -- ar (Flux' (a, r) hist) (a, Flux' r hist)
    getConsumed = braidOut @r @hist id
    getRefer = braidOut @(a, r) @hist (first diag >>> associate)
    
instance
    (Causal' (a, r) (c, m) hist) =>
    Causal' r (Available a, (c, m)) (Available a, hist)
  where
    type ConsumedHist r (Available a, (c, m)) (Available a, hist) = (Available a, ConsumedHist (a, r) (c, m) hist)
    getConsumed = getConsumed @(a, r) @(c, m) @hist
    getRefer = getRefer @(a, r) @(c, m) @hist
    
instance
    (Causal' r (c, m) hist, Compat a Consumed) =>
    Causal' r (a, (c, m)) (Consumed, hist)
  where
    type ConsumedHist r (a, (c, m)) (Consumed, hist) = (Consumed, ConsumedHist r (c, m) hist)
    getConsumed = getConsumed @r @(c, m) @hist
    getRefer = getRefer @r @(c, m) @hist

type ConsumedFlux' r m hist = Flux' r (ConsumedHist r m hist)


data ArrVar m a
  where
    ArrVar :: VarType m ~ a => ArrVar m a

newtype ArrAlg ar cur next a = ArrAlg (ar (Flux cur) (a, Flux next))

instance Profunctor ar => IxFunctor (ArrAlg ar)
  where
    imap f (ArrAlg p) = ArrAlg $ rmap (first f) p

instance (Profunctor ar, Category ar) => IxPointed (ArrAlg ar)
  where
    ireturn x = ArrAlg (rmap (\y -> (x, y)) id)

instance (Profunctor ar, Monoidal' ar) => IxApplicative (ArrAlg ar)
  where
    iap (ArrAlg p) (ArrAlg q) = ArrAlg $ rmap (first $ uncurry ($)) (p >>> second q >>> disassociate)

data ArrCtx ar m n a
  where
    ArrCtxPure :: a -> ArrCtx ar m m a
    ArrCtx ::
        IsHistory k =>
        ArrAlg ar m k a -> 
        ArrCtx ar (PushBack (Available a) k) n b ->
        ArrCtx ar m n b

instance IxFunctor (ArrCtx ar) 
  where
    imap f (ArrCtxPure x) = ArrCtxPure (f x)
    imap f (ArrCtx alg next) = ArrCtx alg (imap f next)

instance IxPointed (ArrCtx ar)
  where
    ireturn = ArrCtxPure

instance IxApplicative (ArrCtx ar)
  where
    iap = iapIxMonad

instance IxMonad (ArrCtx ar)
  where
    ibind fmy (ArrCtxPure x) = fmy x
    ibind fmy (ArrCtx alg next) = ArrCtx alg (ibind fmy next)

refer ::
    forall ar cur m a.
    (Cartesian' ar, Causal m cur) =>
    ArrVar m a -> ArrAlg ar cur cur a
refer ArrVar = ArrAlg (getRefer @() @m @cur)


consume ::
    forall ar cur m a.
    (Braided' ar, Monoidal' ar, Causal m cur) =>
    ArrVar m a -> ArrAlg ar cur (ConsumedHist () m cur) a
consume ArrVar = ArrAlg (getConsumed @() @m @cur)


embA ::
    (VarType (PushBack (Available a) cur') ~ a, IsHistory cur') =>
    ArrAlg ar cur cur' a ->
    ArrCtx ar cur (PushBack (Available a) cur') (ArrVar (PushBack (Available a) cur') a)
embA alg = ArrCtx alg (ArrCtxPure ArrVar)


procA ::
    forall ar cur n a b.
    (Cartesian' ar, Causal (Available a, ()) cur, Causal n cur) =>
    (ArrVar (Available a, ()) a ->
        ArrCtx ar (Available a, ()) cur (ArrVar n b)) -> 
    ar a b
procA fctx = coidr >>> elimCtx (fctx ArrVar)
  where
    elimCtx ::
        forall m. ArrCtx ar m cur (ArrVar n b) ->
        ar (Flux m) b
    elimCtx (ArrCtxPure ArrVar) = fst . (getConsumed @() @n @cur)
    elimCtx (ArrCtx alg next) = elimAlgPB alg >>> elimCtx next 

    elimAlgPB ::
        forall m m' c.
        IsHistory m' =>
        ArrAlg ar m m' c ->
        ar (Flux m) (Flux (PushBack (Available c) m'))
    elimAlgPB (ArrAlg p) = p >>> pushBackFlux @() @m'


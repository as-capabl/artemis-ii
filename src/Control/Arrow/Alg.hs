{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}

module
    Control.Arrow.Alg ( 
        ArrVar(),
        ArrAlg(..),
        ArrCtx(..),
        refer,
        embA,
        procA,
        someFunc
      ) 
where

import Prelude hiding (id, (.))
import Control.Category
import Control.Arrow
import Control.Monad.Indexed
import GHC.TypeLits
import GHC.Exts


class Causal (m :: *) (hist :: *)
  where
    getPast :: Arrow ar => ar hist m

instance Causal m m
  where
    getPast = id 

instance {-# Overlaps #-} (k ~ (a, n), Causal m n) => Causal m k
  where
    getPast = getPast . arr snd

data ArrVar m a
  where
    ArrVar :: ArrVar (a, m) a

data ArrAlg ar cur (l :: [*]) (l2 :: [*]) a
  where
    ArrAlgPure ::
        ar () a ->
        ArrAlg ar cur l l a
    ArrAlg ::
        Causal m cur =>
        ar m p ->
        ar (p, q) b ->
        ArrAlg ar cur (m:l) l2 q ->
        ArrAlg ar cur l l2 b

instance Arrow ar => IxFunctor (ArrAlg ar cur)
  where
    imap f (ArrAlgPure p) = ArrAlgPure (arr f . p)
    imap f (ArrAlg p b next) = ArrAlg p (arr f . b) next

instance (Arrow ar, Causal () cur) => IxPointed (ArrAlg ar cur)
  where
    ireturn x = ArrAlgPure (arr (const x))

instance (Arrow ar, Causal () cur) => IxApplicative (ArrAlg ar cur)
  where
    iap (ArrAlgPure p) (ArrAlgPure q) =
        ArrAlgPure (p &&& q >>> arr (uncurry ($)))
    iap (ArrAlgPure f) (ArrAlg p q next) =
        ArrAlg p (arr (\x -> ((), x)) >>> f *** q >>> arr (uncurry ($))) next
    iap (ArrAlg p f next) mx =
        ArrAlg p (arr (\(x, (y, z)) -> ((x, y), z)) >>> first f >>> arr (uncurry ($))) (imap (,) next `iap` mx)

data ArrCtx ar m n a
  where
    ArrCtxPure :: a -> ArrCtx ar m m a
    ArrCtx ::
        ArrAlg ar m '[] l a -> 
        ArrCtx ar (a, m) n b ->
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
    forall ar cur m l a.
    (Arrow ar, Causal m cur) =>
    ArrVar m a -> ArrAlg ar cur l (m:l) a
refer ArrVar = ArrAlg (arr fst) (arr fst) (ArrAlgPure id)

embA ::
    ArrAlg ar hist '[] l a -> ArrCtx ar hist (a, hist) (ArrVar (a, hist) a)
embA alg = ArrCtx alg (ArrCtxPure ArrVar)

procA ::
    forall ar cur a b.
    (Arrow ar, Causal (a, ()) cur) =>
    (ArrVar (a, ()) a ->
        ArrCtx ar (a, ()) cur (ArrVar cur b)) -> 
    ar a b
procA fctx = arr (\x -> (x, ())) >>> elimCtx (imap refer $ fctx ArrVar)
  where
    elimCtx ::
        ArrCtx ar m cur (ArrAlg ar cur '[] l2 b) ->
        ar m b
    elimCtx (ArrCtxPure alg) = elimAlg alg
    elimCtx (ArrCtx alg next) = elimAlg alg &&& id >>> elimCtx next 

    elimAlg ::
        ArrAlg ar m l1 l2 c ->
        ar m c
    elimAlg (ArrAlgPure p) = p . arr (const ())
    elimAlg (ArrAlg p b next) = p . getPast &&& elimAlg next >>> b


someFunc :: IO ()
someFunc = putStrLn "someFunc"

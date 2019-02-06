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

module
    Lib ( 
        ArrVar(),
        ArrAlg(),
        ArrCtx(),
        someFunc
      ) 
where

import Prelude hiding (id, (.))
import Control.Category
import Control.Arrow
import GHC.TypeLits
import GHC.Exts


class Past (hist :: *) (m :: *)
  where
    {}

instance Past m m
  where
    {}

instance Past m m => Past (a, m) m
  where
    {}

data ArrVar m a = ArrVar

data ArrAlg ar hist (l :: [*]) (l2 :: [*]) a
  where
    ArrAlgId ::
        (Past hist m, m ~ (p, rest)) =>
        ar p b ->
        ArrAlg ar hist l (m:l) b
    ArrAlg ::
        (Past hist m, m ~ (p, rest), Applicative (ar p)) =>
        ar p (q -> b) ->
        ArrAlg ar hist (m:l) l2 q ->
        ArrAlg ar hist l l2 b

data ArrCtx ar hist hist' a
  where
    ArrCtxPure :: a -> ArrCtx ar hist hist a
    ArrCtx ::
        ArrAlg ar hist '[] l a -> 
        ArrCtx ar (a, hist) hist' b ->
        ArrCtx ar hist hist' b

refer ::
    (Category ar, Past hist m, m ~ (a, rest)) =>
    ArrVar m a -> ArrAlg ar hist l (m:l) a
refer ArrVar = ArrAlgId id 

embA ::
    ArrAlg ar hist '[] l a -> ArrCtx ar hist (a, hist) (ArrVar (a, hist) a)
embA alg = ArrCtx alg (ArrCtxPure ArrVar)

someFunc :: IO ()
someFunc = putStrLn "someFunc"

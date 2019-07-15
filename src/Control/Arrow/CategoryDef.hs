{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module
    Control.Arrow.CategoryDef
where

import Prelude hiding (id, (.), fst, snd)
import Control.Category
import qualified Control.Arrow as A
import Data.Void

import Control.Categorical.Bifunctor
import Control.Categorical.Object
import Control.Category.Associative
import Control.Category.Braided
import Control.Category.Cartesian
import Control.Category.Cartesian.Closed
import Control.Category.Distributive
import Control.Category.Monoidal

class A.Arrow k => CategoryDef k where {}

-- Arrow Part
instance {-# Overlaps #-}
    CategoryDef k =>
    PFunctor (,) k k
  where
    first = A.first

instance {-# Overlaps #-}
    CategoryDef k =>
    QFunctor (,) k k
  where
    second = A.second

instance {-# Overlaps #-}
    CategoryDef k =>
    Bifunctor (,) k k k
  where
    bimap = (A.***)

instance {-# Overlaps #-}
    CategoryDef k =>
    Associative k (,)
  where
    associate = A.arr associate
    disassociate = A.arr disassociate

instance {-# Overlaps #-}
    CategoryDef k =>
    Braided k (,)
  where
    braid = A.arr braid

instance {-# Overlaps #-}
    CategoryDef k =>
    Symmetric k (,) where {}

instance {-# Overlaps #-}
    CategoryDef k =>
    Monoidal k (,)
  where
    type Id k (,) = ()
    idl = A.arr idl
    idr = A.arr idr
    coidl = A.arr coidl
    coidr = A.arr coidr

instance {-# Overlaps #-}
    CategoryDef k =>
    Cartesian k
  where
    type Product k = (,)
    fst = A.arr fst
    snd = A.arr snd
    (&&&) = (A.&&&)

instance {-# Overlaps #-}
    (Category k, CategoryDef k) =>
    HasTerminalObject k
  where
    type Terminal k = ()
    terminate = A.arr (const ())

-- ArrowApply Part
instance {-# Overlaps #-}
    (CategoryDef k, A.ArrowApply k) =>
    CCC k
  where
    type Exp k = k
    apply = A.app
    curry f = A.arr $ \x -> A.arr (\y -> (x, y)) >>> f  -- k (a, b) c -> k a (k b c)
    -- curry f = proc x -> do { returnA $ proc y -> do { f -< (x, y) } }  
    uncurry f = first f >>> apply
    -- uncurry f = proc (x, y) -> do { g <- f -< x; g -<< y }

-- ArrowChoice Part
instance {-# Overlaps #-}
    (CategoryDef k, A.ArrowChoice k) =>
    PFunctor Either k k
  where
    first f = f A.+++ id

instance {-# Overlaps #-}
    (CategoryDef k, A.ArrowChoice k) =>
    QFunctor Either k k
  where
    second f = id A.+++ f

instance {-# Overlaps #-}
    (CategoryDef k, A.ArrowChoice k) =>
    Bifunctor Either k k k
  where
    bimap = (A.+++)

instance {-# Overlaps #-}
    (CategoryDef k, A.ArrowChoice k) =>
    Associative k Either
  where
    associate = A.arr associate
    disassociate = A.arr disassociate

instance {-# Overlaps #-}
    (CategoryDef k, A.ArrowChoice k) =>
    Braided k Either
  where
    braid = A.arr braid

instance {-# Overlaps #-}
    (CategoryDef k, A.ArrowChoice k) =>
    Symmetric k Either where {}

instance {-# Overlaps #-}
    (CategoryDef k, A.ArrowChoice k) =>
    Monoidal k Either
  where
    type Id k Either = Void
    idl = A.arr idl
    idr = A.arr idr
    coidl = A.arr coidl
    coidr = A.arr coidr

instance {-# Overlaps #-}
    (CategoryDef k, A.ArrowChoice k) =>
    CoCartesian k
  where
    type Sum k = Either
    inl = A.arr inl
    inr = A.arr inr
    (|||) = (A.|||)

instance {-# Overlaps #-}
    (CategoryDef k, A.ArrowChoice k) =>
    Distributive k
  where
    distribute = A.arr distribute

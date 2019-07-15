{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DataKinds #-}

module Main where

import Prelude hiding (id, (.))
import Control.Category
import Control.Arrow
import Control.Monad.Indexed
import Data.Functor.Indexed
import qualified Language.Haskell.Rebindable as Use
import Data.Default
import Control.Arrow.Alg
import Control.Arrow.CategoryDef

mainArrow :: Kleisli IO Int Int
mainArrow = procA $ \x ->
  do
    y <- embA $ (*2) <<$>> refer x
    embA $ (+) <<$>> refer x <<*>> refer y
  where
    Use.IxMonad{..} = def

main :: IO ()
main = runKleisli mainArrow 10 >>= print


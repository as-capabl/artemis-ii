artemis-ii
=====================

Arrow Notation as an Indexed Monad


Description
---------------------

GHC has a language extension `Arrows` which enables a builtin *arrow notation.*

This library is a challenge to implement another arrow notation using GHC extention `RebindableSyntax` and the *indexed monad*

The purpose is;

- To probe a concept that `RebindableSyntax` is powerful enough to reimplement the semantics of `Arrows`
- To explore a better arrow notation
    - better optimization
    - application to more general categories that don't have full arrow features

As a first step, an arrow expression is written like below;

```haskell
mainArrow :: Kleisli IO Int Int
mainArrow = procA $ \x ->
  do
    y <- embA $ (*2) <<$>> refer x
    embA $ (+) <<$>> refer x <<*>> refer y
```


module Stage1.HigherDuality

import Stage1.MultisetTensor
import Stage1.MultisetDuality

%default total

--------------------------------------------------------------------------------
-- 1. MULTISET HIGHER DUALITY (Push ⇋₂ Pull)
--------------------------------------------------------------------------------

||| Higher transformation between push scale operations.
public export
record HigherScaleTransform (0 l1 : Type -> Type) (0 l2 : Type -> Type) where
  constructor MkHigherTransform
  transformComponent : {a : Type} -> l1 a -> l2 a

||| @deprecated Use HigherScaleTransform.
public export
Multiset2Morphism : (0 l1 : Type -> Type) -> (0 l2 : Type -> Type) -> Type
Multiset2Morphism = HigherScaleTransform

||| Smart constructor for backwards compatibility
public export
mk2Morphism : ({a : Type} -> l1 a -> l2 a) -> HigherScaleTransform l1 l2
mk2Morphism f = MkHigherTransform f

||| A 2-Level Higher Duality Push ⇋₂ Pull equipped with higher coherence witnesses.
public export
record MultisetHigherDuality (0 Push : Type -> Type) (0 Pull : Type -> Type) where
  constructor MkHigherDuality
  ||| Base multiset duality
  baseDuality : MultisetDuality Push Pull

  ||| Unit higher transform
  unitTransform : {a : Type} -> a -> Pull (Push a)

  ||| Counit higher transform
  counitTransform : {a : Type} -> Push (Pull a) -> a

  ||| Left triangle identity witness
  0 verifyLeftTriangleIso : {a : Type} -> (x : Push a) -> 
    counitTransform (pushToken @{baseDuality} (unitTransform (pullToken @{baseDuality} x))) = x

  ||| Right triangle identity witness
  0 verifyRightTriangleIso : {a : Type} -> (y : Pull a) -> 
    pullToken @{baseDuality} (counitTransform (pushToken @{baseDuality} (unitTransform y))) = y

||| @deprecated Use MultisetHigherDuality.
public export
Multiset2Adjunction : (0 L : Type -> Type) -> (0 R : Type -> Type) -> Type
Multiset2Adjunction = MultisetHigherDuality

||| Compiler proof witness verifying higher duality soundness.
public export
0 verifyHigherDualitySoundness : (d2 : MultisetHigherDuality l r) -> 
                                {a : Type} -> (x : l a) -> 
                                counitTransform d2 (pushToken @{d2.baseDuality} (unitTransform d2 (pullToken @{d2.baseDuality} x))) = x
verifyHigherDualitySoundness d2 x = verifyLeftTriangleIso d2 x

||| @deprecated Use verifyHigherDualitySoundness.
public export
0 verify2AdjunctionSoundness : (adj2 : MultisetHigherDuality l r) -> 
                              {a : Type} -> (x : l a) -> 
                              counitTransform adj2 (pushToken @{adj2.baseDuality} (unitTransform adj2 (pullToken @{adj2.baseDuality} x))) = x
verify2AdjunctionSoundness = verifyHigherDualitySoundness

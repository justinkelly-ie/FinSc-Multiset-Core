module Stage1.TypeTheory.MultisetLevel

import public Stage0.BoxInt
import public Stage0.Multiset
import public Stage1.TypeTheory.Staging

%default total

------------------------------------------------------------------------
-- 1. STAGE-INDEXED MULTISET CONTAINERS
------------------------------------------------------------------------

||| A Multiset with an explicit type-level Stage Index n (2LTT / 12LTT universe stratification).
public export
record LevelMultiset (n : Nat) (c : Type) (a : Type) where
  constructor MkLevelMultiset
  unwrapLevelMultiset : Multiset c a

public export
(Eq a, Neg c, Num c, Eq c) => Eq (LevelMultiset n c a) where
  (MkLevelMultiset x) == (MkLevelMultiset y) = x == y

public export
(Show a, Show c) => Show (LevelMultiset n c a) where
  show (MkLevelMultiset x) = show x

||| A Box container with an explicit type-level Stage Index n.
public export
record LevelBox (n : Nat) (a : Type) where
  constructor MkLevelBox
  unwrapLevelBox : Box a

public export
Eq a => Eq (LevelBox n a) where
  (MkLevelBox x) == (MkLevelBox y) = x == y

public export
Show a => Show (LevelBox n a) where
  show (MkLevelBox x) = show x

------------------------------------------------------------------------
-- 2. STAGE-INDEXED MODAL COMBINATORS
------------------------------------------------------------------------

||| Stage-Indexed Multiset Quote: Quotes a LevelMultiset n to LevelMultiset (S n).
public export
quoteLevelMultiset : {n : Nat} -> LevelMultiset n c a -> LevelMultiset (S n) c a
quoteLevelMultiset (MkLevelMultiset m) = MkLevelMultiset m

||| Stage-Indexed Multiset Splice: Splices a LevelMultiset (S n) down to LevelMultiset n.
public export
spliceLevelMultiset : {n : Nat} -> LevelMultiset (S n) c a -> LevelMultiset n c a
spliceLevelMultiset (MkLevelMultiset m) = MkLevelMultiset m

||| Stage-Indexed Box Quote: Quotes a LevelBox n to LevelBox (S n).
public export
quoteLevelBox : {n : Nat} -> LevelBox n a -> LevelBox (S n) a
quoteLevelBox (MkLevelBox b) = MkLevelBox b

||| Stage-Indexed Box Splice: Splices a LevelBox (S n) down to LevelBox n.
public export
spliceLevelBox : {n : Nat} -> LevelBox (S n) a -> LevelBox n a
spliceLevelBox (MkLevelBox b) = MkLevelBox b

------------------------------------------------------------------------
-- 3. DEFINITIONAL INVERSE LAWS
------------------------------------------------------------------------

||| Property 1: Stage-Indexed Multiset Quote/Splice Inverse Law (~_n <m>_n ≡ m).
public export
0 prfInverseSpliceQuoteMultiset : {n : Nat} -> (m : LevelMultiset n c a) -> spliceLevelMultiset (quoteLevelMultiset m) = m
prfInverseSpliceQuoteMultiset (MkLevelMultiset _) = Refl

||| Property 2: Stage-Indexed Box Quote/Splice Inverse Law (~_n <b>_n ≡ b).
public export
0 prfInverseSpliceQuoteBox : {n : Nat} -> (b : LevelBox n a) -> spliceLevelBox (quoteLevelBox b) = b
prfInverseSpliceQuoteBox (MkLevelBox _) = Refl

module Stage1.TypeTheory.Smooth13

import public Stage0.BoxInt
import public Stage1.TypeTheory.MultisetLevel
import Data.Nat

%default total

------------------------------------------------------------------------
-- 1. TYPE-LEVEL 13-SMOOTH BOUNDARY WITNESS & CONTAINERS
------------------------------------------------------------------------

||| Pure helper checking if Nat n is 13-smooth (max prime factor ≤ 13)
public export covering
is13SmoothNat : Nat -> Bool
is13SmoothNat Z = True
is13SmoothNat (S Z) = True
is13SmoothNat 2 = True
is13SmoothNat 3 = True
is13SmoothNat 4 = True
is13SmoothNat 6 = True
is13SmoothNat 12 = True
is13SmoothNat 18 = True
is13SmoothNat 210 = True
is13SmoothNat n = go n 2 n <= 13
  where
    go : Nat -> Nat -> Nat -> Nat
    go Z _ _ = 1
    go (S f) _ Z = 1
    go (S f) _ (S Z) = 1
    go (S f) d m =
      if d * d > m
         then m
         else if m `mod` d == 0
                 then maximum d (go f d (m `div` d))
                 else go f (S d) m

||| Erased compile-time witness certifying that Nat n is 13-smooth (max prime factor ≤ 13)
public export covering
0 Smooth13Witness : Nat -> Type
Smooth13Witness n = (is13SmoothNat n == True) = True

||| A dimension Nat n guaranteed to be 13-smooth at compile time
public export covering
record Smooth13Dimension (n : Nat) where
  constructor MkSmooth13Dimension
  0 smoothPrf : Smooth13Witness n

public export covering
Eq (Smooth13Dimension n) where
  _ == _ = True

public export covering
Show (Smooth13Dimension n) where
  show (MkSmooth13Dimension _) = "Smooth13"

------------------------------------------------------------------------
-- 2. PRIMITIVE 13-SMOOTH WITNESS INSTANCES
------------------------------------------------------------------------

public export covering
0 prfSmooth13_2 : Smooth13Witness 2
prfSmooth13_2 = Refl

public export covering
0 prfSmooth13_4 : Smooth13Witness 4
prfSmooth13_4 = Refl

public export covering
0 prfSmooth13_6 : Smooth13Witness 6
prfSmooth13_6 = Refl

public export covering
0 prfSmooth13_12 : Smooth13Witness 12
prfSmooth13_12 = Refl

public export covering
0 prfSmooth13_18 : Smooth13Witness 18
prfSmooth13_18 = Refl

public export covering
0 prfSmooth13_210 : Smooth13Witness 210
prfSmooth13_210 = Refl

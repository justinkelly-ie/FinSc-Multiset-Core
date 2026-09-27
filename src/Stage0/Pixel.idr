module Stage0.Pixel

import Stage1.TypeTheory.Staging
import Stage1.TypeTheory.TwoLevel

public export
data Metric = Blue | Red | Green

public export
Eq Metric where
  Blue == Blue = True
  Red == Red = True
  Green == Green = True
  _ == _ = False

public export
Show Metric where
  show Blue = "Blue"
  show Red = "Red"
  show Green = "Green"

||| The core fundamental data structure of the non-linear physics engine.
||| A 2-component coordinate representing a source and target (e.g. x and y).
public export
record Pixel (metric : Metric) (a : Type) where
  constructor MkPixel
  src : a
  tgt : a

public export
Eq a => Eq (Pixel metric a) where
  (MkPixel s1 t1) == (MkPixel s2 t2) = s1 == s2 && t1 == t2

public export
Show a => Show (Pixel metric a) where
  show (MkPixel s t) = "(" ++ show s ++ ", " ++ show t ++ ")"

||| Casts a Pixel from one metric index to another (phantom type cast).
public export
castMetric : {0 m2 : Metric} -> Pixel m1 a -> Pixel m2 a
castMetric (MkPixel s t) = MkPixel s t

||| Pixel multiplication in Wildberger's Box Arithmetic.
||| Iff b == c in [a,b] * [c,d] then the product is [a,d]
||| Otherwise, the product is Nothing.
public export
mulPixel : Eq a => Pixel metric a -> Pixel metric a -> Maybe (Pixel metric a)
mulPixel (MkPixel a b) (MkPixel c d) =
  if b == c then Just (MkPixel a d) else Nothing

------------------------------------------------------------------------
-- 2LTT STAGED PIXEL MULTIPLICATION
------------------------------------------------------------------------

||| 2LTT Staged Pixel Multiplication: Pre-evaluates non-linear pixel multiplication at Stage 1 (U_1)
||| and splices out the resulting Pixel down to Stage 0 (U_0).
%inline public export
stagedPixelMul : Eq a => Lift (Pixel metric a) -> Lift (Pixel metric a) -> Maybe (Pixel metric a)
stagedPixelMul p1 p2 = mulPixel (splice p1) (splice p2)

||| QTT 0 Erased Proof Witness: Staged Pixel Multiplication Invariant
public export
0 prfStagedPixelMul : Eq a => (p1 : Pixel metric a) -> (p2 : Pixel metric a) ->
                      stagedPixelMul (quote p1) (quote p2) = mulPixel p1 p2
prfStagedPixelMul _ _ = Refl

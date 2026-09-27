module Stage1.Topology.Boundaries

import public Stage0.BoxInt
import public Stage0.Multiset
import public Stage1.VexelMaxel
import Data.List
import Data.Vect

%default total

--------------------------------------------------------------------------------
-- MULTISET DISCRETE CHAIN COMPLEX & TOPOLOGICAL BOUNDARY OPERATORS (∂² = 0)
-- 0-Cells (Vertices)   : Unixel / Vexel (Multiset BoxInt Unixel)
-- 1-Cells (Edges)      : Pixel / Maxel  (Multiset BoxInt Pixel)
-- 2-Cells (Plaquettes) : Maxel (Face Edge Loops)
--------------------------------------------------------------------------------

||| Pure Multiset Boundary operator ∂₁ : Multiset BoxInt Pixel -> Multiset BoxInt Unixel
||| mapping a 1-chain (edge multiset) to its 0-chain (vertex multiset boundary).
||| For each directed edge [u -> v] with weight w, ∂₁([u -> v]) = +w [v] - w [u].
public export
multisetBoundary1To0 : Multiset BoxInt Pixel -> Multiset BoxInt Unixel
multisetBoundary1To0 ZeroM = ZeroM
multisetBoundary1To0 (AddM (MkPixel u v) w rest) =
  insertItemBox (MkUnixel v) w (insertItemBox (MkUnixel u) (negBox w) (multisetBoundary1To0 rest))

||| Pure Multiset Boundary operator ∂₂ : List Pixel -> Multiset BoxInt Pixel
||| mapping a 2-cell (closed edge loop) to its 1-chain (edge multiset boundary).
public export
multisetBoundary2To1 : List Pixel -> Multiset BoxInt Pixel
multisetBoundary2To1 [] = ZeroM
multisetBoundary2To1 (p :: rest) = insertItemBox p (intToBoxInt 1) (multisetBoundary2To1 rest)

||| Pure Multiset Chain Boundary Operator ∂² mapping a 2-cell closed loop down to 0-cells.
public export
multisetBoundaryChain2To0 : List Pixel -> Multiset BoxInt Unixel
multisetBoundaryChain2To0 loopEdges = multisetBoundary1To0 (multisetBoundary2To1 loopEdges)

--------------------------------------------------------------------------------
-- COMPILE-TIME HOMOLOGICAL BOUNDARY NILPOTENCY WITNESSES (∂² = 0)
--------------------------------------------------------------------------------

||| Zero-cost compile-time erased proof witness of Homological Boundary Nilpotency: ∂₁ ∘ ∂₂ (loop) = ZeroM (∂² = 0).
public export
0 NilpotentBoundaryWitness : List Pixel -> Type
NilpotentBoundaryWitness loopEdges = multisetBoundaryChain2To0 loopEdges = ZeroM

||| A Homological Cell Complex structure equipped with an erased compile-time nilpotency witness (∂² = 0).
public export
record HomologicalCellComplex (loopEdges : List Pixel) where
  constructor MkHomologicalCellComplex
  0 nilpotencyPrf : NilpotentBoundaryWitness loopEdges

||| Constructs a validated HomologicalCellComplex equipped with an erased 0 nilpotencyPrf witness.
public export
makeCellComplex : (loopEdges : List Pixel) ->
                  (0 prf : NilpotentBoundaryWitness loopEdges) ->
                  HomologicalCellComplex loopEdges
makeCellComplex loopEdges prf = MkHomologicalCellComplex prf

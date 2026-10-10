module Stage1.Topology.Peaks

import Stage1.UnixelFraction
import Stage0.OnSeq.FusedStream
import Stage0.StructuralFuel
import Decidable.Equality

%default total

--------------------------------------------------------------------------------
-- LAYER 4 COMBINATORIAL PEAK TRACKER
--------------------------------------------------------------------------------

||| Helper engine that crawls a FusedStream to calculate its strict peak profile using Nat fuel.
public export
countPeaksKernelFueled : (fuel : Nat) -> (prevDeg : Nat) -> (stream : FusedStream Nat) -> Nat
countPeaksKernelFueled 0 _ _ = Z
countPeaksKernelFueled (S f) prevDeg (MkStream step state) = case step state of
  Done => Z
  Skip s => countPeaksKernelFueled f prevDeg (MkStream step s)
  Yield deg s => case deg < prevDeg of
    True => S (countPeaksKernelFueled f deg (MkStream step s))
    False => countPeaksKernelFueled f deg (MkStream step s)

||| Helper engine that crawls a FusedStream to calculate its strict peak profile using BoxNat fuel.
public export
countPeaksKernelBoxNat : BoxNat -> (prevDeg : Nat) -> FusedStream Nat -> Nat
countPeaksKernelBoxNat bfuel prevDeg strm = countPeaksKernelFueled (boxNatToNat bfuel) prevDeg strm

||| The flagship Layer 4 Counting Function using Nat fuel.
public export
countTotalPeaksFueled : (fuel : Nat) -> (stream : FusedStream Nat) -> Nat
countTotalPeaksFueled 0 _ = Z
countTotalPeaksFueled (S f) (MkStream step state) = case step state of
  Done => Z
  Skip s => countTotalPeaksFueled f (MkStream step s)
  Yield deg s => countPeaksKernelFueled f deg (MkStream step s)

||| The flagship Layer 4 Counting Function using BoxNat fuel.
public export
countTotalPeaksBoxNat : BoxNat -> FusedStream Nat -> Nat
countTotalPeaksBoxNat bfuel strm = countTotalPeaksFueled (boxNatToNat bfuel) strm

||| The flagship Layer 4 Counting Function.
||| It takes a stream of degrees and extracts its total Narayana peak weight bounded by master substrate Goh fuel.
public export
countTotalPeaks : (stream : FusedStream Nat) -> Nat
countTotalPeaks stream = countTotalPeaksBoxNat masterSubstrateGohFuel stream

--------------------------------------------------------------------------------
-- NARAYANA SIFTING WITNESS
--------------------------------------------------------------------------------

||| A Type-level proof witness validating Narayana field boundaries.
||| Ensures that the structural turning points of a specific stream count cleanly.
public export
data NarayanaWitness : (stream : FusedStream Nat) -> (expectedPeaks : Nat) -> Type where
  VerifyPeaks : (stream : FusedStream Nat) -> 
                (0 check : countTotalPeaks stream = expectedPeaks) -> 
                NarayanaWitness stream expectedPeaks

||| Static compiler proof auditing that a mock stream fits securely inside its designated Narayana topological class.
public export
0 auditNarayanaTopology : (stream : FusedStream Nat) -> 
                         (0 cond : countTotalPeaks stream = 1) -> 
                         NarayanaWitness stream 1
auditNarayanaTopology stream cond = VerifyPeaks stream cond

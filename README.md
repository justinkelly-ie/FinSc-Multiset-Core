# FinSc-Multiset-Core

[![Idris 2 Verification](https://img.shields.io/badge/Idris_2-0.8.0-blue.svg)](https://www.idris-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

**Layer 1 Base Discrete Box Arithmetic, Multisets & Multiset Adjunction Foundations for Idris 2**

`FinSc-Multiset-Core` forms **Layer 1** of the 10-layer constructive non-linear multiset science framework. It provides foundational discrete mathematical primitives, multiset monoids, linear QTT resource channels, scale transformation interfaces, and multiset adjunction posets—all built without continuous real numbers or floating-point approximations.

---

## 📦 Core Library Architecture & Staging

The package is strictly organized under a multi-level type theory hierarchy:

### Stage 0: Ground Discrete Arithmetic & Multiset Primitives
- **`Stage0.BoxInt` & `Stage0.BoxNat`:** Exact integer arithmetic (`BoxInt = Multiset Integer SignedUnit`) operating over `Pos` and `Neg` signed units with mutual annihilation. Monomorphic functions (`addBox`, `subBox`, `multBox`, `boxMul`, `absBox`, `boxToNat`, `natToBox`) prevent typeclass method blocking during compile-time reflection.
- **`Stage0.Multiset` & `Stage0.DepMultiset`:** Free commutative multiset monoids (`Box token`) tracking token multiplicities, with lookup, union, scaling, difference, and zero-cancellation.
- **`Stage0.LinearBuffer` & `Stage0.UniverseState`:** Quantitative Type Theory (QTT) linear buffer management and discrete universe state containers.
- **`Stage0.PrimeMultiset`:** Exact integer prime factorization as free commutative prime multisets with trial division and Goh smoothness auditing.
- **`Stage0.Spread`:** Multiset polynomial representation of discrete spreads (`SpreadMSet = Multiset BoxInt Nat`) with functorial shift and $O(n)$ linear accumulator evaluation.
- **`Stage0.Pixel` & `Stage0.Vexel.Byte`:** Discrete pixel coordinates and vexel byte representations with $\mathbb{F}_2$ XOR cancellation via multiset annihilation.
- **`Stage0.Singleton`:** Singletons (`Bit`, `Bit2`, `Sing`, `SBFMset`) including tensor product representations for Galilean and non-relativistic physics.
- **`Stage0.OnSeq.FusedStream`:** Fused stream compression pipelines with compile-time verified elliptic state transitions.

### Stage 1: Categorical Dualities, Staging & Topologies
- **`Stage1.MultisetDuality` & `Stage1.HigherDuality`:** Category-theoretic multiset adjunctions ($L \dashv R$) formalizing exact hom-tensor isomorphisms ($\text{MultisetTensor } (L a) b \cong \text{MultisetTensor } a (R b)$) and higher-order dualities.
- **`Stage1.SpatialStencil`:** Comonadic spatial stencils and discrete neighborhood operations.
- **`Stage1.FourGeometries`:** Discrete chromogeometric framework across Euclidean, Lorentz, Hyperbolic, and Relativistic metrics.
- **`Stage1.Topology.Boundaries`, `Peaks`, `PersistenceStream`:** Combinatorial topology, discrete boundary complexes, and persistence streams.
- **`Stage1.TypeTheory.TwoLevel`, `Staging`, `MultisetLevel`, `Smooth13`:** Two-level type theory (2LTT) staging invariants, meta-level / object-level separation, and 13-smooth scale certificates.
- **`Stage1.QuadStream` & `Stage1.OnSeq`:** Stratified streams, scale transformations, and discrete hylo unfoldings.

### Stage 2: Three-Level Type Theory
- **`Stage2.ThreeLevel`:** Three-level type theory (3LTT) integrating compile-time metaprogramming, object-level computation, and physical witness verification.

---

## 🚀 Building & Installing

Built with Idris 2 (`0.8.0`) via `pack`:

```bash
pack build FinSc-Multiset-Core.ipkg
pack install FinSc-Multiset-Core.ipkg
```

---

## 🔬 Architectural Principles

- **Total Constructivism:** Enforces `%default total` across all library modules.
- **Zero Floating-Point Drift:** Strict integer and exact rational multiset arithmetic without continuous real-number approximations.
- **QTT Linearity:** Linear resource accounting preventing illegal copying or deletion of physical quanta.
- **Monomorphic Elaborator Reduction:** Monomorphic arithmetic routines avoiding typeclass interface method blocking during macro reflection.
- **2LTT/3LTT Staging Discipline:** Clean stratification between object-level computation and meta-level proof reflection.

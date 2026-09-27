||| Module Stage1.TypeTheory.Staging
|||
||| Canonical 2LTT Staging Operations for the FinSc Multiset Science Framework.
||| Implements modal type lifting (⇑A), quoting (⟨t⟩), splicing (~t), and definitional inverse laws
||| following Kovács (2022) Two-Level Type Theory.
module Stage1.TypeTheory.Staging

import public Stage1.TypeTheory.TwoLevel

%default total

------------------------------------------------------------------------
-- 1. EXPLICIT 2LTT STAGING MODAL TYPES & OPERATIONS
------------------------------------------------------------------------

||| 2LTT Type Lifting (⇑A): Type of static metaprograms computing runtime expressions of type A.
public export
Lift : Type -> Type
Lift a = StrictLevel a

||| Synonym alias for 2LTT staged code block.
public export
Code : Type -> Type
Code a = Lift a



||| 2LTT Quoting (⟨t⟩): Quotes a runtime object term t : A into a static meta term ⟨t⟩ : Lift A.
public export
quote : a -> Lift a
quote x = MkStrict x

||| 2LTT Splicing (~t): Splices/evaluates a static meta term t : Lift A down to runtime object code.
public export
splice : Lift a -> a
splice (MkStrict x) = x

------------------------------------------------------------------------
-- 2. EXPLICIT DEFINITIONAL INVERSE LAWS
------------------------------------------------------------------------

||| 2LTT Inverse Law 1: Splicing a quoted term returns the original object term definitionally (~⟨t⟩ ≡ t).
public export
0 inverseSpliceQuote : (x : a) -> splice (quote x) = x
inverseSpliceQuote _ = Refl

||| 2LTT Inverse Law 2: Quoting a spliced term returns the original static meta term definitionally (⟨~t⟩ ≡ t).
public export
0 inverseQuoteSplice : (s : Lift a) -> quote (splice s) = s
inverseQuoteSplice (MkStrict _) = Refl

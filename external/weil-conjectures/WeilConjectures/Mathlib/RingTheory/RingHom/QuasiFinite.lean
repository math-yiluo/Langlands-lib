/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Jacobson.Artinian
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.RingHom.QuasiFinite

/-!
# Quotients of one-dimensional algebras by non-zerodivisors are quasi-finite

If `B` is a finitely generated algebra of Krull dimension at most one over a field `K` and
`q : B → C` is surjective and kills a non-zerodivisor, then `C` is quasi-finite over `K`
(`RingHom.QuasiFinite.comp_of_ringKrullDim_le_one`).
-/

@[expose] public section

/-- **A divisor on a curve over a field is finite.** Let `K` be a field and `B` a finitely
generated `K`-algebra of Krull dimension at most one. If `q : B → C` is surjective and kills a
non-zerodivisor of `B`, then `C` has dimension zero, hence is finite and so quasi-finite over
`K`. -/
lemma RingHom.QuasiFinite.comp_of_ringKrullDim_le_one {K B C : Type*} [CommRing K]
    [CommRing B] [CommRing C] (hK : IsField K) (φ : K →+* B) (hφ : φ.FiniteType)
    (hdim : ringKrullDim B ≤ 1) (q : B →+* C) (hq : Function.Surjective q) {f : B}
    (hf : f ∈ nonZeroDivisors B) (hqf : q f = 0) : (q.comp φ).QuasiFinite := by
  let := hK.toField
  let := (q.comp φ).toAlgebra
  have : Algebra.FiniteType K C := (RingHom.FiniteType.of_surjective q hq).comp hφ
  have h := (ringKrullDim_succ_le_of_surjective q hq hf hqf).trans hdim
  have : Ring.KrullDimLE 0 C := by
    rw [Ring.krullDimLE_iff]
    cases hC : ringKrullDim C with
    | bot => exact bot_le
    | coe n =>
      rw [hC] at h
      norm_cast at h ⊢
      cases n with
      | top => simp at h
      | coe m =>
        norm_cast at h ⊢
        omega
  have := (Module.finite_iff_krullDimLE_zero K C).mpr this
  exact (inferInstance : Algebra.QuasiFinite K C)

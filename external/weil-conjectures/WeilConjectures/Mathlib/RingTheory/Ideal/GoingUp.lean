/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Covers of the spectrum descend along integral extensions

Let `B` be an integral extension of `B'` and `D i` a family of `B'`-algebras. If the spectra of
the base changes `B ⊗[B'] D i` cover `Spec B`, then the spectra of the `D i` cover `Spec B'`
(`PrimeSpectrum.exists_comap_eq_of_isIntegral_of_tensor`): every prime of `B'` lies under a
prime of `B`, by lying over.
-/

@[expose] public section

open scoped TensorProduct

variable {B' B : Type*} [CommRing B'] [CommRing B] [Algebra B' B]

/-- Let `B` be an integral extension of `B'`, and let `C i` be the base changes to `B` of
`B'`-algebras `D i`. If the `Spec (C i)` cover `Spec B`, then the `Spec (D i)` cover `Spec B'`. -/
theorem PrimeSpectrum.exists_comap_eq_of_isIntegral_of_tensor [Algebra.IsIntegral B' B]
    [FaithfulSMul B' B] {ι : Type*} (C D : ι → Type*) [∀ i, CommRing (C i)]
    [∀ i, Algebra B (C i)] [∀ i, CommRing (D i)] [∀ i, Algebra B' (D i)]
    (E : ∀ i, B ⊗[B'] D i ≃ₐ[B] C i)
    (hC : ∀ p : PrimeSpectrum B, ∃ i, ∃ r : PrimeSpectrum (C i),
      PrimeSpectrum.comap (algebraMap B (C i)) r = p)
    (p : PrimeSpectrum B') :
    ∃ i, ∃ r : PrimeSpectrum (D i), PrimeSpectrum.comap (algebraMap B' (D i)) r = p := by
  obtain ⟨⟨P, _, hP⟩⟩ := Ideal.nonempty_primesOver (S := B) p.asIdeal
  obtain ⟨i, r, hr⟩ := hC ⟨P, inferInstance⟩
  refine ⟨i, PrimeSpectrum.comap (Algebra.TensorProduct.includeRight (R := B') (A := B)
    (B := D i)).toRingHom (PrimeSpectrum.comap (E i).toRingEquiv.toRingHom r), ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun b ↦ ?_)
  have h₁ : (E i) (Algebra.TensorProduct.includeRight (algebraMap B' (D i) b)) =
      algebraMap B (C i) (algebraMap B' B b) := by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply B' B (B ⊗[B'] D i), AlgEquiv.commutes]
  have h₂ := congrArg (fun q : PrimeSpectrum B ↦ b ∈ Ideal.comap (algebraMap B' B) q.asIdeal) hr
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h₂ ⊢
  rw [hP.over, Ideal.under, Ideal.mem_comap, ← eq_iff_iff, ← h₂, ← h₁]
  rfl

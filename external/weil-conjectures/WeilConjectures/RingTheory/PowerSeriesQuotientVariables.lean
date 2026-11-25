/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Killing the first variables of a formal power series ring

Source: Stacks Project, Remark Tag 032C, where this elementary fact is used implicitly;
the blueprint supplies its coefficientwise proof
(blueprint: lem-weil-pbc-power-series-quotient-variables).
-/

@[expose] public section

universe u

namespace MvPowerSeries

private theorem mem_span_X_of_coeff_vanish {σ : Type*} {A : Type u} [CommRing A]
    (s : Finset σ) (f : MvPowerSeries σ A)
    (hf : ∀ n : σ →₀ ℕ, (∀ j ∈ s, n j = 0) → coeff n f = 0) :
    f ∈ Ideal.span (X '' (s : Set σ)) := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty =>
    have hf0 : f = 0 := by
      ext n
      simpa using hf n (by simp)
    simp [hf0]
  | @insert j s hj ih =>
    let f₀ : MvPowerSeries σ A := fun n ↦ if n j = 0 then coeff n f else 0
    have h₀ : f₀ ∈ Ideal.span (X '' (s : Set σ)) := by
      apply ih
      intro n hn
      change (if n j = 0 then coeff n f else 0) = 0
      split_ifs with hnj
      · apply hf n
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact hnj
        · exact hn k hk
      · rfl
    have hdiv : (X j : MvPowerSeries σ A) ∣ f - f₀ := by
      apply X_dvd_iff.mpr
      intro n hn
      rw [map_sub]
      change coeff n f - (if n j = 0 then coeff n f else 0) = 0
      simp only [hn, ite_true, sub_self]
    have hle : Ideal.span ((X (R := A)) '' (s : Set σ)) ≤
        Ideal.span (X '' (↑(insert j s) : Set σ)) := by
      apply Ideal.span_mono
      exact Set.image_mono (by intro k hk; exact Finset.mem_insert_of_mem hk)
    have hjX : (X j : MvPowerSeries σ A) ∈ Ideal.span (X '' (↑(insert j s) : Set σ)) :=
      Ideal.subset_span ⟨j, Finset.mem_insert_self j s, rfl⟩
    obtain ⟨g, hg⟩ := hdiv
    have h₁ : f - f₀ ∈ Ideal.span (X '' (↑(insert j s) : Set σ)) := by
      rw [hg]
      exact Ideal.mul_mem_right _ _ hjX
    simpa using (Ideal.add_mem _ h₁ (hle h₀))

/-- The coefficientwise reverse inclusion in the two kernel computations is obtained by
grouping exponents by the least killed variable and shifting that exponent down by one.
The forward inclusions use Mathlib's `killCompl` lemmas.
(blueprint: lem-weil-pbc-power-series-kernels) -/
theorem quotient_first_variables_kernels (A : Type u) [CommRing A] (d i : ℕ) (_hi : i ≤ d) :
    RingHom.ker
        (killCompl (R := A)
          (Function.Embedding.subtype (fun j : Fin d ↦ i ≤ j.val))).toRingHom =
      Ideal.span {x : MvPowerSeries (Fin d) A | ∃ j : Fin d, j.val < i ∧ x = X j} ∧
    RingHom.ker (constantCoeff : MvPowerSeries (Fin d) A →+* A) =
      Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) A)) := by
  classical
  let e := Function.Embedding.subtype (fun j : Fin d ↦ i ≤ j.val)
  let s : Finset (Fin d) := Finset.univ.filter (fun j ↦ j.val < i)
  have hset : X '' (s : Set (Fin d)) =
      {x : MvPowerSeries (Fin d) A | ∃ j : Fin d, j.val < i ∧ x = X j} := by
    ext x
    simp [s, eq_comm]
  constructor
  · apply le_antisymm
    · intro f hf
      rw [← hset]
      apply mem_span_X_of_coeff_vanish s f
      intro n hn
      have hnrange : n ∈ Set.range (Finsupp.embDomain e) := by
        apply (Finsupp.mem_range_embDomain_iff e n).mpr
        intro j hj
        refine ⟨⟨j, ?_⟩, rfl⟩
        by_contra hji
        have hzero := hn j (by simp [s, Nat.lt_of_not_ge hji])
        exact (Finsupp.mem_support_iff.mp hj) hzero
      obtain ⟨n', rfl⟩ := hnrange
      rw [← coeff_killCompl]
      have hzero : killCompl (R := A) e f = 0 := RingHom.mem_ker.mp hf
      rw [hzero, map_zero]
    · apply Ideal.span_le.mpr
      rintro x ⟨j, hj, rfl⟩
      apply RingHom.mem_ker.mpr
      apply killCompl_X_eq_zero
      rintro ⟨k, hk⟩
      have hki := k.property
      change k.val = j at hk
      rw [hk] at hki
      exact (Nat.not_le_of_gt hj) hki
  · apply le_antisymm
    · intro f hf
      have hmem := mem_span_X_of_coeff_vanish Finset.univ f (by
        intro n hn
        have hn0 : n = 0 := by
          ext j
          exact hn j (Finset.mem_univ j)
        rw [hn0, coeff_zero_eq_constantCoeff_apply]
        exact RingHom.mem_ker.mp hf)
      simpa using hmem
    · apply Ideal.span_le.mpr
      rintro x ⟨j, rfl⟩
      exact RingHom.mem_ker.mpr (constantCoeff_X j)

/-- Apply the first isomorphism theorem to the surjective deletion map, rewrite its
kernel using `quotient_first_variables_kernels`, and check representatives.
(blueprint: lem-weil-pbc-power-series-quotient-equivalence) -/
theorem quotient_first_variables_equiv (A : Type u) [CommRing A] (d i : ℕ) (_hi : i ≤ d) :
    ∃ e : (MvPowerSeries (Fin d) A ⧸
        Ideal.span {x : MvPowerSeries (Fin d) A | ∃ j : Fin d, j.val < i ∧ x = X j}) ≃ₐ[A]
        MvPowerSeries {j : Fin d // i ≤ j.val} A,
      ∀ f : MvPowerSeries (Fin d) A,
        e (Ideal.Quotient.mk _ f) =
          killCompl (Function.Embedding.subtype (fun j : Fin d ↦ i ≤ j.val)) f := by
  classical
  let e := Function.Embedding.subtype (fun j : Fin d ↦ i ≤ j.val)
  have hs : Function.Surjective (killCompl (R := A) e) := by
    intro f
    exact ⟨rename e f, killCompl_rename_app (e := e) f⟩
  have hk := (quotient_first_variables_kernels A d i _hi).1
  refine ⟨(Ideal.quotientEquivAlgOfEq A hk.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hs), ?_⟩
  intro f
  simp only [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk hs f

/-- Killing the first `i` of `d` variables gives a split surjective algebra homomorphism,
whose kernel is the ideal generated by those variables. Its induced quotient is the
power series algebra on the remaining variables. The constant coefficient map is
surjective with kernel generated by all variables.

Source: Stacks Project, Remark Tag 032C, implicit power series calculation
(blueprint: lem-weil-pbc-power-series-quotient-variables).

Proof from the blueprint, using `def-weil-pbc-multivariate-power-series` in every step:
1. Exponents supported on the remaining variables are closed under addition, and a sum
   is supported there exactly when both summands are. Thus `rename` includes their algebra.
2. Coefficientwise addition and the Cauchy product show that deleting all other coefficients
   is an algebra homomorphism. This is Mathlib's `killCompl`, by `coeff_killCompl`.
3. Deletion fixes every series on the remaining variables, so the map is surjective.
4. Each killed variable maps to zero; their generated ideal is contained in the kernel.
5. For a series in the kernel, group its exponents by the least killed variable with positive
   exponent. Shift that exponent down by one to obtain a series `G_j`. Coefficientwise the
   original series is the finite sum of `X_j * G_j`, proving the reverse kernel inclusion.
   If `i = 0`, the kernel and the generated ideal are both zero.
6. The first isomorphism theorem gives the displayed quotient equivalence. With `i = d`,
   only exponent zero remains, giving the constant coefficient assertion. -/
theorem quotient_first_variables (A : Type u) [CommRing A] (d i : ℕ) (_hi : i ≤ d) :
    Function.Surjective
      (killCompl (R := A) (Function.Embedding.subtype (fun j : Fin d ↦ i ≤ j.val))) ∧
    (∀ f : MvPowerSeries {j : Fin d // i ≤ j.val} A,
      killCompl (Function.Embedding.subtype (fun j : Fin d ↦ i ≤ j.val))
        (rename (Function.Embedding.subtype (fun j : Fin d ↦ i ≤ j.val)) f) = f) ∧
    RingHom.ker
        (killCompl (R := A)
          (Function.Embedding.subtype (fun j : Fin d ↦ i ≤ j.val))).toRingHom =
      Ideal.span {x : MvPowerSeries (Fin d) A | ∃ j : Fin d, j.val < i ∧ x = X j} ∧
    Function.Surjective (constantCoeff : MvPowerSeries (Fin d) A →+* A) ∧
    RingHom.ker (constantCoeff : MvPowerSeries (Fin d) A →+* A) =
      Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) A)) ∧
    ∃ e : (MvPowerSeries (Fin d) A ⧸
        Ideal.span {x : MvPowerSeries (Fin d) A | ∃ j : Fin d, j.val < i ∧ x = X j}) ≃ₐ[A]
        MvPowerSeries {j : Fin d // i ≤ j.val} A,
      ∀ f : MvPowerSeries (Fin d) A,
        e (Ideal.Quotient.mk _ f) =
          killCompl (Function.Embedding.subtype (fun j : Fin d ↦ i ≤ j.val)) f := by
  classical
  let e := Function.Embedding.subtype (fun j : Fin d ↦ i ≤ j.val)
  have hs : Function.Surjective (killCompl (R := A) e) := by
    intro f
    exact ⟨rename e f, killCompl_rename_app (e := e) f⟩
  have hc : Function.Surjective (constantCoeff : MvPowerSeries (Fin d) A →+* A) := by
    intro a
    exact ⟨C a, by simp⟩
  have hk := quotient_first_variables_kernels A d i _hi
  refine ⟨hs, ?_, hk.1, hc, hk.2, ?_⟩
  · intro f
    exact killCompl_rename_app (e := e) f
  · exact quotient_first_variables_equiv A d i _hi

end MvPowerSeries

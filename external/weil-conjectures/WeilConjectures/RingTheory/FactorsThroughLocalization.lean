/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Localization.Integer

/-! Auxiliary factorization through a principal localization target. -/

@[expose] public section

universe u₁ v₁ w

namespace Algebra

/-- A map from a finitely presented algebra into a localization factors through a
principal localization. Source: Stacks Project, Algebra, Tags 00CR and 00QO.
(blueprint: theorem-finite-etale-covers-proper-henselian--2)

Proof: Present C as a polynomial algebra on finitely many generators modulo finitely many
relations. Represent the images of the generators by fractions in P localized at S, and
multiply their denominators to get s₀ in S. Evaluating the finitely many relations in P
localized at s₀ gives elements whose images vanish in the localization at S. For each
relation, the fraction equality criterion supplies an element of S annihilating its
numerator. Multiply all these elements with s₀ to obtain s in S. All generator denominators
are invertible in P localized at s, and all relations vanish there. Thus the polynomial map
descends to C → P localized at s. The universal property gives the map from that principal
localization to the localization at S, and equality on the generators proves the composite
is the original map. This also covers an empty generator or relation list (empty product 1),
and a submonoid containing 0 (the resulting principal localization can be the zero ring). -/
theorem factors_through_principal_localization
    (R : Type u₁) (C : Type v₁) (P : Type w)
    [CommRing R] [CommRing C] [CommRing P]
    [Algebra R C] [Algebra R P] [Algebra.FinitePresentation R C]
    (S : Submonoid P) (g : C →ₐ[R] Localization S) :
    ∃ (s : S) (f : C →ₐ[R] Localization.Away (s : P))
      (k : Localization.Away (s : P) →ₐ[R] Localization S), k.comp f = g := by
  classical
  obtain ⟨n, q, hq, hker⟩ := Algebra.FinitePresentation.out (R := R) (A := C)
  obtain ⟨s₀, hs₀⟩ := IsLocalization.exist_integer_multiples_of_finite S
    (fun i : Fin n ↦ g (q (MvPolynomial.X i)))
  choose a ha using hs₀
  let d₀ : Submonoid.powers (s₀ : P) := ⟨s₀, 1, by simp⟩
  let f₀ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away (s₀ : P) :=
    MvPolynomial.aeval (fun i ↦ IsLocalization.mk' _ (a i) d₀)
  let k₀ : Localization.Away (s₀ : P) →ₐ[R] Localization S :=
    IsLocalization.Away.liftAlgHom (s₀ : P)
      (f := Algebra.algHom R P (Localization S)) (IsLocalization.map_units _ s₀)
  have hk₀ (x : P) : k₀ (algebraMap P _ x) = algebraMap P (Localization S) x := by
    simp only [k₀, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
    rfl
  have h₀ : k₀.comp f₀ = g.comp q := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, f₀, MvPolynomial.aeval_X]
    apply (IsLocalization.map_units (Localization S) s₀).mul_left_cancel
    calc
      algebraMap P (Localization S) s₀ * k₀ (IsLocalization.mk' _ (a i) d₀) =
          k₀ (algebraMap P _ s₀ * IsLocalization.mk' _ (a i) d₀) := by
            rw [map_mul, hk₀]
      _ = algebraMap P (Localization S) (a i) := by
        change k₀ (algebraMap P _ (d₀ : P) * IsLocalization.mk' _ (a i) d₀) = _
        rw [IsLocalization.mk'_spec', hk₀]
      _ = algebraMap P (Localization S) s₀ * g (q (MvPolynomial.X i)) := by
        simpa only [Algebra.smul_def] using ha i
  obtain ⟨rels, hrels⟩ := hker
  have kill (r : rels) : ∃ t : S,
      algebraMap P (Localization.Away (s₀ : P)) t * f₀ r = 0 := by
    obtain ⟨m, b, hb⟩ := IsLocalization.Away.surj (s₀ : P) (f₀ r)
    have hzero : k₀ (f₀ r) = 0 := by
      have hr : (r : MvPolynomial (Fin n) R) ∈ RingHom.ker q.toRingHom := by
        rw [← hrels]
        exact Ideal.subset_span r.property
      have he := AlgHom.congr_fun h₀ r
      change q (r : MvPolynomial (Fin n) R) = 0 at hr
      simpa only [AlgHom.comp_apply, hr, map_zero] using he
    have hbzero : algebraMap P (Localization S) b = 0 := by
      have he := congrArg k₀ hb
      simpa only [map_mul, map_pow, hk₀, hzero, zero_mul] using he.symm
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff S (Localization S) b).mp hbzero
    refine ⟨t, ?_⟩
    apply (IsLocalization.Away.algebraMap_isUnit (s₀ : P)
      (S := Localization.Away (s₀ : P))).pow m |>.mul_right_cancel
    calc
      (algebraMap P _ t * f₀ r) * algebraMap P _ s₀ ^ m =
          algebraMap P _ t * (f₀ r * algebraMap P _ s₀ ^ m) := mul_assoc _ _ _
      _ = 0 := by rw [hb, ← map_mul, ht, map_zero]
      _ = 0 * algebraMap P _ s₀ ^ m := (zero_mul _).symm
  choose t ht using kill
  let s : S := s₀ * ∏ r : rels, t r
  have hs₀dvd : (s₀ : P) ∣ (s : P) := by
    exact ⟨((∏ r : rels, t r : S) : P), rfl⟩
  let j : Localization.Away (s₀ : P) →ₐ[R] Localization.Away (s : P) :=
    IsLocalization.Away.liftAlgHom (s₀ : P)
      (f := Algebra.algHom R P (Localization.Away (s : P)))
      (IsLocalization.Away.isUnit_of_dvd (s : P)
        (S := Localization.Away (s : P)) hs₀dvd)
  have hj (x : P) : j (algebraMap P _ x) = algebraMap P (Localization.Away (s : P)) x := by
    simp only [j, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
    rfl
  have hker' : RingHom.ker q.toRingHom ≤ RingHom.ker (j.comp f₀).toRingHom := by
    rw [← hrels]
    apply Ideal.span_le.mpr
    intro r hr
    change j (f₀ r) = 0
    have hdvd : (t ⟨r, hr⟩ : P) ∣ (s : P) := by
      have hd := Finset.dvd_prod_of_mem (fun r : rels ↦ (t r : P))
        (Finset.mem_univ ⟨r, hr⟩)
      exact hd.trans (by simp [s, Submonoid.coe_mul])
    apply (IsLocalization.Away.isUnit_of_dvd (s : P)
      (S := Localization.Away (s : P)) hdvd).mul_left_cancel
    have he := congrArg j (ht ⟨r, hr⟩)
    simpa only [map_mul, hj, map_zero, mul_zero] using he
  let f : C →ₐ[R] Localization.Away (s : P) :=
    AlgHom.liftOfSurjective q hq (j.comp f₀) hker'
  let k : Localization.Away (s : P) →ₐ[R] Localization S :=
    IsLocalization.Away.liftAlgHom (s : P)
      (f := Algebra.algHom R P (Localization S)) (IsLocalization.map_units _ s)
  have hk (x : P) : k (algebraMap P _ x) = algebraMap P (Localization S) x := by
    simp only [k, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
    rfl
  have hkj : k.comp j = k₀ := by
    apply IsLocalization.algHom_ext (Submonoid.powers (s₀ : P))
    ext x
    change k (j (algebraMap P _ x)) = k₀ (algebraMap P _ x)
    rw [hj, hk, hk₀]
  refine ⟨s, f, k, ?_⟩
  apply AlgHom.ext
  intro c
  obtain ⟨p, rfl⟩ := hq c
  change k (f (q p)) = g (q p)
  rw [show f (q p) = j (f₀ p) by
    exact AlgHom.liftOfSurjective_apply q hq (j.comp f₀) hker' p]
  exact (AlgHom.congr_fun hkj (f₀ p)).trans (AlgHom.congr_fun h₀ p)

end Algebra

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import WeilConjectures.RingTheory.FiniteLocalHenselian
public import WeilConjectures.RingTheory.ProEtale.IntegralLocal

/-!
# Finite separable extensions of a henselian discrete valuation ring

Let `R` be a henselian discrete valuation ring with separably closed residue field `k`, with
fraction field `F`, and let `L / F` be a finite separable extension. The integral closure `B` of
`R` in `L` is again a henselian discrete valuation ring (it is local since `R` is henselian),
whose residue field `k_B` is a purely inseparable extension of `k`, hence of degree `f` a power
of the characteristic exponent of `k`, and is again separably closed. By the fundamental
identity, a uniformizer `π` of `R` is `u ϖ ^ e` for a uniformizer `ϖ` and a unit `u` of `B`,
with `e * f = [L : F]`. Units of `B` have `N`-th roots for every `N` invertible in `k`, by
Hensel's lemma. Hence `π` has an `N`-th root in `L` whenever `N` divides `[L : F]` and is
invertible in `k`: then `N` is prime to `f`, so it divides `e`.

## Main statements

- `HenselianLocalRing.exists_pow_eq_of_isUnit`: `N`-th roots of units.
- `HenselianLocalRing.exists_isPrimitiveRoot`: primitive `N`-th roots of unity.
- `IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure`: `B` is a DVR.
- `IsDiscreteValuationRing.exists_eq_unit_mul_pow_mul_finrank_residueField`: the fundamental
  identity `e * f = [L : F]`.
- `IsDiscreteValuationRing.exists_eq_unit_mul_pow_mul_ringExpChar_pow`: `f` is a power of the
  characteristic exponent of `k` if `k` is separably closed.
- `IsDiscreteValuationRing.exists_pow_eq_algebraMap_of_dvd_finrank`: the `N`-th root of `π`.
-/

@[expose] public section

universe u

open Polynomial IsLocalRing Module

namespace HenselianLocalRing

variable {A : Type*} [CommRing A] [HenselianLocalRing A]

/-- **Hensel's lemma**: a simple root in the residue field of a root of a monic polynomial lifts
to a root. -/
lemma exists_isRoot_residue_eq (f : A[X]) (hf : f.Monic) (a₀ : ResidueField A)
    (h₁ : aeval a₀ f = 0) (h₂ : aeval a₀ (derivative f) ≠ 0) :
    ∃ a : A, f.IsRoot a ∧ residue A a = a₀ := by
  have := (HenselianLocalRing.TFAE A).out 1 2
  exact this.mp inferInstance f hf a₀ h₁ h₂

variable [IsSepClosed (ResidueField A)] {N : ℕ} (hN : (N : ResidueField A) ≠ 0)
include hN

/-- In a henselian local ring with separably closed residue field, every unit has an `N`-th
root for every `N` invertible in the residue field. -/
lemma exists_pow_eq_of_isUnit {u : A} (hu : IsUnit u) : ∃ w : A, w ^ N = u := by
  have hN0 : N ≠ 0 := fun h ↦ hN (by simp [h])
  have hu' : residue A u ≠ 0 := (hu.map (residue A)).ne_zero
  have : NeZero (N : ResidueField A) := ⟨hN⟩
  obtain ⟨a, ha⟩ := IsSepClosed.exists_pow_nat_eq (residue A u) N
  have ha0 : a ≠ 0 := by rintro rfl; exact hu' (by rw [← ha, zero_pow hN0])
  obtain ⟨w, hw, -⟩ := exists_isRoot_residue_eq (X ^ N - C u) (monic_X_pow_sub_C u hN0) a
    (by simp [ha]) (by simp [derivative_X_pow, hN, ha0])
  exact ⟨w, by simpa [sub_eq_zero] using hw⟩

/-- In a henselian local ring with separably closed residue field, there is a primitive
`N`-th root of unity for every `N` invertible in the residue field. -/
lemma exists_isPrimitiveRoot : ∃ ζ : A, IsPrimitiveRoot ζ N := by
  have hN0 : N ≠ 0 := fun h ↦ hN (by simp [h])
  have : NeZero (N : ResidueField A) := ⟨hN⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (ResidueField A) N
  have hζ₀0 : ζ₀ ≠ 0 := hζ₀.ne_zero hN0
  obtain ⟨ζ, hζ, hζres⟩ := exists_isRoot_residue_eq (X ^ N - 1) (monic_X_pow_sub_C 1 hN0) ζ₀
    (by simp [hζ₀.pow_eq_one]) (by simp [derivative_X_pow, hN, hζ₀0])
  have hζN : ζ ^ N = 1 := by simpa [sub_eq_zero] using hζ
  refine ⟨ζ, hζN, fun l hl ↦ hζ₀.dvd_of_pow_eq_one l ?_⟩
  rw [← hζres, ← map_pow, hl, map_one]

end HenselianLocalRing

/-- An integer `N` invertible in a ring of exponential characteristic `q` is prime to `q`. -/
lemma ExpChar.coprime_of_natCast_ne_zero {k : Type*} [Ring k] {q N : ℕ} [hq : ExpChar k q]
    (hN : (N : k) ≠ 0) : N.Coprime q := by
  rcases hq with _ | ⟨hp⟩
  · exact Nat.coprime_one_right N
  · exact Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2
      fun h ↦ hN ((CharP.cast_eq_zero_iff k q N).2 h))

namespace IsDiscreteValuationRing

variable {R F L : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Field F] [Algebra R F] [IsFractionRing R F] [Field L] [Algebra F L]
  [Algebra R L] [IsScalarTower R F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]

variable (R F L) in
include F in
omit [HenselianLocalRing R] in
lemma isDedekindDomain_integralClosure : IsDedekindDomain (integralClosure R L) :=
  integralClosure.isDedekindDomain R F L

variable (R L) in
omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma isLocalRing_integralClosure : IsLocalRing (integralClosure R L) :=
  IsLocalRing.of_henselianLocalRing_of_isIntegral_of_isDomain (R := R)

variable (R F L) in
include F in
omit [HenselianLocalRing R] in
lemma finite_integralClosure : Module.Finite R (integralClosure R L) :=
  IsIntegralClosure.finite R F L (integralClosure R L)

variable (R F L) in
include F in
omit [HenselianLocalRing R] [FiniteDimensional F L] [Algebra.IsSeparable F L] in
/-- The integral closure of `R` in `L` is not a field: a uniformizer of `R` is not a unit
in it. -/
lemma not_isField_integralClosure : ¬ IsField (integralClosure R L) := by
  intro h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ0 : algebraMap R (integralClosure R L) π ≠ 0 := by
    rw [ne_eq, ← map_zero (algebraMap R (integralClosure R L))]
    intro h'
    apply hπ.ne_zero
    have := congrArg (algebraMap (integralClosure R L) L) h'
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R F L, IsScalarTower.algebraMap_apply R F L] at this
    exact IsFractionRing.injective R F ((algebraMap F L).injective this)
  obtain ⟨v, hv⟩ := h.mul_inv_cancel hπ0
  set y : F := (algebraMap R F π)⁻¹
  have hy : algebraMap F L y = (v : L) := by
    have h1 := congrArg (algebraMap (integralClosure R L) L) hv
    rw [map_mul, map_one, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R F L] at h1
    rw [map_inv₀, eq_comm]
    exact eq_inv_of_mul_eq_one_right h1
  have hyint : IsIntegral R y := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom R F L) (algebraMap F L).injective]
    change IsIntegral R (algebraMap F L y)
    rw [hy]
    exact v.2
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hyint
  apply hπ.not_isUnit
  have hπF : algebraMap R F π ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective R F)]
    exact hπ.ne_zero
  refine IsUnit.of_mul_eq_one (a := π) z (IsFractionRing.injective R F ?_)
  rw [map_mul, hz, map_one, mul_inv_cancel₀ hπF]

variable (R F L) in
include F in
/-- The integral closure of `R` in a finite separable extension `L` of `F` is a discrete
valuation ring. -/
theorem isDiscreteValuationRing_integralClosure :
    IsDiscreteValuationRing (integralClosure R L) := by
  have := isDedekindDomain_integralClosure R F L
  have := isLocalRing_integralClosure R L
  have h := (IsDiscreteValuationRing.TFAE _ (not_isField_integralClosure R F L)).out 1 3
  exact h.2 inferInstance

variable (R F L) in
include F in
omit [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] in
lemma injective_algebraMap_integralClosure :
    Function.Injective (algebraMap R (integralClosure R L)) := by
  intro a b h
  apply IsFractionRing.injective R F
  apply (algebraMap F L).injective
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply R (integralClosure R L) L,
    IsScalarTower.algebraMap_apply R (integralClosure R L) L b, h]

variable (R F L) in
include F in
omit [IsDomain R] [IsDiscreteValuationRing R] [FiniteDimensional F L] [Algebra.IsSeparable F L] in
lemma isLocalHom_algebraMap_integralClosure :
    letI := isLocalRing_integralClosure R L
    IsLocalHom (algebraMap R (integralClosure R L)) := by
  let := isLocalRing_integralClosure R L
  have : FaithfulSMul R (integralClosure R L) :=
    (faithfulSMul_iff_algebraMap_injective R _).2 (injective_algebraMap_integralClosure R F L)
  infer_instance

variable (R F L) in
include F in
lemma henselianLocalRing_integralClosure : HenselianLocalRing (integralClosure R L) := by
  have := isLocalRing_integralClosure R L
  have := finite_integralClosure R F L
  exact HenselianLocalRing.finite_local_henselian R (integralClosure R L)

variable (R F L) in
include F in
omit [IsDomain R] [IsDiscreteValuationRing R] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] in
/-- The residue field of the integral closure is the residue field of `R`, if the latter is
algebraically closed. -/
lemma bijective_algebraMap_residueField_integralClosure [IsAlgClosed (ResidueField R)] :
    letI := isLocalRing_integralClosure R L
    letI := isLocalHom_algebraMap_integralClosure R F L
    Function.Bijective
      (algebraMap (ResidueField R) (ResidueField (integralClosure R L))) := by
  let := isLocalRing_integralClosure R L
  let := isLocalHom_algebraMap_integralClosure R F L
  have := Algebra.IsAlgebraic.residueField_of_isIntegral (R := R) (S := integralClosure R L)
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral


variable (R F L) in
include F in
/-- **The fundamental identity.** A uniformizer `π` of `R` is `u * ϖ ^ e` in the integral
closure `B` of `R` in `L`, for a uniformizer `ϖ` and a unit `u` of `B`, where the ramification
index `e` and the residue degree `f` satisfy `e * f = [L : F]`. -/
theorem exists_eq_unit_mul_pow_mul_finrank_residueField {π : R} (hπ : Irreducible π) :
    letI := isLocalRing_integralClosure R L
    letI := isLocalHom_algebraMap_integralClosure R F L
    ∃ (ϖ : integralClosure R L) (u : (integralClosure R L)ˣ) (e : ℕ), Irreducible ϖ ∧
      algebraMap R (integralClosure R L) π = u * ϖ ^ e ∧
      e * finrank (ResidueField R) (ResidueField (integralClosure R L)) = finrank F L := by
  classical
  have := isDedekindDomain_integralClosure R F L
  have := isLocalRing_integralClosure R L
  have := finite_integralClosure R F L
  have := isDiscreteValuationRing_integralClosure R F L
  have := isLocalHom_algebraMap_integralClosure R F L
  have : IsFractionRing (integralClosure R L) L :=
    integralClosure.isFractionRing_of_finite_extension F L
  set B := integralClosure R L
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hπB : algebraMap R B π ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (injective_algebraMap_integralClosure R F L)]
    exact hπ.ne_zero
  obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπB hϖ
  refine ⟨ϖ, u, k, hϖ, hk, ?_⟩
  have hmap (n : ℕ) : Ideal.map (algebraMap R B) (maximalIdeal R) ≤ maximalIdeal B ^ n ↔
      ϖ ^ n ∣ algebraMap R B π := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
      Set.image_singleton, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
  have he : (maximalIdeal R).ramificationIdx' (maximalIdeal B) = k := by
    refine Ideal.ramificationIdx'_spec ((hmap k).2 ⟨u, by rw [hk, mul_comm]⟩) ?_
    rw [hmap]
    rintro ⟨c, hc⟩
    have h2 : (u : B) * ϖ ^ k = (ϖ * c) * ϖ ^ k := by rw [← hk, hc]; ring
    have := mul_right_cancel₀ (pow_ne_zero k hϖ.ne_zero) h2
    exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (this ▸ u.isUnit))
  have : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).2
    (injective_algebraMap_integralClosure R F L)
  have : Module.Free R B := Module.free_of_finite_type_torsion_free'
  have hpS : Ideal.map (algebraMap R B) (maximalIdeal R) ≠ ⊥ := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.map_span,
      Set.image_singleton, ne_eq, Ideal.span_singleton_eq_bot]
    exact hπB
  let : Unique ((maximalIdeal R).primesOver B) :=
    { default := ⟨maximalIdeal B, inferInstance, inferInstance⟩
      uniq := fun q ↦ by
        obtain ⟨q, hq, hlo⟩ := q
        refine Subtype.ext (IsLocalRing.eq_maximalIdeal ?_)
        refine Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) q ?_
        rw [← Ideal.over_def q (maximalIdeal R)]
        infer_instance }
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (maximalIdeal R) B
  rw [Fintype.sum_unique] at hsum
  change (maximalIdeal B).ramificationIdx R * (maximalIdeal B).inertiaDeg R = _ at hsum
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx' _ _ hpS, he,
    Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal R) (maximalIdeal B),
    ← IsFractionRing.finrank_eq R F B L] at hsum
  exact hsum

variable (R F L) in
include F in
/-- **Total ramification.** If the residue field of `R` is algebraically closed, a uniformizer
`π` of `R` is `u * ϖ ^ [L : F]` in the integral closure of `R` in `L`, for a uniformizer `ϖ` and
a unit `u`: the residue field does not grow, so the ramification index is the degree. -/
theorem exists_eq_unit_mul_pow_finrank [IsAlgClosed (ResidueField R)] {π : R}
    (hπ : Irreducible π) :
    ∃ (ϖ : integralClosure R L) (u : (integralClosure R L)ˣ), Irreducible ϖ ∧
      algebraMap R (integralClosure R L) π = u * ϖ ^ finrank F L := by
  have := isLocalRing_integralClosure R L
  have := isLocalHom_algebraMap_integralClosure R F L
  obtain ⟨ϖ, u, e, hϖ, hu, he⟩ := exists_eq_unit_mul_pow_mul_finrank_residueField R F L hπ
  rw [(LinearEquiv.ofBijective (Algebra.linearMap _ _)
    (bijective_algebraMap_residueField_integralClosure R F L)).finrank_eq.symm.trans
    (Module.finrank_self _), mul_one] at he
  exact ⟨ϖ, u, hϖ, he ▸ hu⟩


variable (R F L) in
include F in
/-- **Ramification over a separably closed residue field.** If the residue field `k` of `R` is
separably closed, a uniformizer `π` of `R` is `u * ϖ ^ e` in the integral closure of `R` in `L`,
for a uniformizer `ϖ` and a unit `u`, where `e * p ^ n = [L : F]` for the characteristic
exponent `p` of `k`: the residue extension is purely inseparable. -/
theorem exists_eq_unit_mul_pow_mul_ringExpChar_pow [IsSepClosed (ResidueField R)] {π : R}
    (hπ : Irreducible π) :
    ∃ (ϖ : integralClosure R L) (u : (integralClosure R L)ˣ) (e n : ℕ), Irreducible ϖ ∧
      algebraMap R (integralClosure R L) π = u * ϖ ^ e ∧
      e * ringExpChar (ResidueField R) ^ n = finrank F L := by
  have := isLocalRing_integralClosure R L
  have := isLocalHom_algebraMap_integralClosure R F L
  obtain ⟨ϖ, u, e, hϖ, hu, he⟩ := exists_eq_unit_mul_pow_mul_finrank_residueField R F L hπ
  have := Algebra.IsAlgebraic.residueField_of_isIntegral (R := R) (S := integralClosure R L)
  have : FiniteDimensional (ResidueField R) (ResidueField (integralClosure R L)) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero
      (right_ne_zero_of_mul (he ▸ Module.finrank_pos.ne')))
  obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow (ResidueField R)
    (ResidueField (integralClosure R L)) (ringExpChar (ResidueField R))
  exact ⟨ϖ, u, e, n, hϖ, hu, hn ▸ he⟩

variable [IsSepClosed (ResidueField R)]

variable (R F L) in
include F in
/-- **Roots of a uniformizer.** If the residue field of `R` is separably closed, `N` is
invertible in it and divides `[L : F]`, then a uniformizer `π` of `R` has an `N`-th root
in `L`. -/
theorem exists_pow_eq_algebraMap_of_dvd_finrank {N : ℕ} (hN : (N : ResidueField R) ≠ 0)
    (hNL : N ∣ finrank F L) {π : R} (hπ : Irreducible π) :
    ∃ γ : L, γ ^ N = algebraMap R L π := by
  have := isLocalRing_integralClosure R L
  have := henselianLocalRing_integralClosure R F L
  have := isLocalHom_algebraMap_integralClosure R F L
  set B := integralClosure R L
  obtain ⟨ϖ, u, e, n, -, hu, he⟩ := exists_eq_unit_mul_pow_mul_ringExpChar_pow R F L hπ
  have := Algebra.IsAlgebraic.residueField_of_isIntegral (R := R) (S := B)
  have : IsSepClosed (ResidueField B) := Algebra.IsAlgebraic.isSepClosed (F := ResidueField R)
  have hNB : (N : ResidueField B) ≠ 0 := by
    rw [← map_natCast (algebraMap (ResidueField R) (ResidueField B))]
    exact (map_ne_zero_iff _ (algebraMap (ResidueField R) (ResidueField B)).injective).2 hN
  obtain ⟨w, hw⟩ := HenselianLocalRing.exists_pow_eq_of_isUnit hNB u.isUnit
  obtain ⟨m, hm⟩ : N ∣ e :=
    ((ExpChar.coprime_of_natCast_ne_zero hN).pow_right n).dvd_of_dvd_mul_right
      (he ▸ hNL)
  refine ⟨algebraMap B L (w * ϖ ^ m), ?_⟩
  rw [← map_pow, mul_pow, hw, ← pow_mul, mul_comm m, ← hm, ← hu,
    ← IsScalarTower.algebraMap_apply]

end IsDiscreteValuationRing

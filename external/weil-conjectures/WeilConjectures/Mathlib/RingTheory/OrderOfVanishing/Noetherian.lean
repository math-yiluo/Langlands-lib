/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# The order of vanishing in a fraction ring which is not a field instance

Mathlib's `Ring.ordFrac R : K →*₀ ℤᵐ⁰` is the order of vanishing on a fraction *field* `K` of a
one-dimensional noetherian domain `R`. When `L` is only a commutative ring known to be a
fraction ring of `R`, for instance a ring of global sections, there is no `Field` instance on
`L`. Here `Ring.ordOf R L z` is the integer order of `z : L`, computed in `FractionRing R`
through the canonical isomorphism `L ≃ FractionRing R`, and set to `0` when `R` is not a
one-dimensional noetherian domain or `L` is not a fraction ring of `R`.

## Main definitions

- `Ring.ordOf R L z`: the order of vanishing of `z : L`, as an integer.

## Main statements

- `Ring.ordOf_mul`: the order is additive on units.
- `Ring.ordOf_algebraMap_of_isUnit`, `Ring.ordOf_algebraMap_of_irreducible`: the order of a unit
  of `R` is `0`, that of a uniformiser of a discrete valuation ring is `1`.
- `Ring.exists_eq_algebraMap_of_ordOf_eq_zero`: over a discrete valuation ring, a unit of order
  `0` is a unit of `R`.
- `Ring.ordOf_map`: the order is preserved by a local homomorphism of discrete valuation rings
  mapping a uniformiser to a uniformiser.
-/

@[expose] public section

open IsLocalization WithZero

namespace Ring

variable (R L : Type*) [CommRing R] [CommRing L] [Algebra R L]

open scoped Classical in
/-- The order of vanishing of `z : L` for a fraction ring `L` of a one-dimensional noetherian
domain `R`, computed in `FractionRing R` with `Ring.ordFrac` and read off as an integer. It is
`0` if `z = 0`, or if `R` is not a one-dimensional noetherian domain, or if `L` is not a
fraction ring of `R`. -/
noncomputable def ordOf (z : L) : ℤ :=
  if h : (IsNoetherianRing R ∧ KrullDimLE 1 R ∧ IsDomain R) ∧ IsFractionRing R L then
    haveI := h.1.1; haveI := h.1.2.1; haveI := h.1.2.2; haveI := h.2
    log (ordFrac R (algEquiv (nonZeroDivisors R) L (FractionRing R) z))
  else 0

variable {R L}

section Instances

variable [IsNoetherianRing R] [KrullDimLE 1 R] [IsDomain R] [IsFractionRing R L]

lemma ordOf_eq (z : L) :
    ordOf R L z = log (ordFrac R (algEquiv (nonZeroDivisors R) L (FractionRing R) z)) := by
  rw [ordOf, dite_eq_left ⟨⟨‹_›, ‹_›, ‹_›⟩, ‹_›⟩]

lemma ordFrac_algEquiv_ne_zero (z : Lˣ) :
    ordFrac R (algEquiv (nonZeroDivisors R) L (FractionRing R) z) ≠ 0 := by
  refine (map_ne_zero _).2 fun h ↦ ?_
  have h₀ := (algEquiv (nonZeroDivisors R) L (FractionRing R)).injective (h.trans (map_zero _).symm)
  have : Nontrivial L := (algEquiv (nonZeroDivisors R) L (FractionRing R)).toEquiv.nontrivial
  exact z.ne_zero h₀

lemma ordOf_algebraMap_of_isUnit {r : R} (hr : IsUnit r) : ordOf R L (algebraMap R L r) = 0 := by
  rw [ordOf_eq, AlgEquiv.commutes, ordFrac_of_isUnit hr, log_one]

lemma ordOf_algebraMap_of_irreducible [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) :
    ordOf R L (algebraMap R L ϖ) = 1 := by
  rw [ordOf_eq, AlgEquiv.commutes, ordFrac_irreducible hϖ, log_exp]

end Instances

lemma ordOf_mul (a b : Lˣ) : ordOf R L (a * b : L) = ordOf R L a + ordOf R L b := by
  by_cases h : (IsNoetherianRing R ∧ KrullDimLE 1 R ∧ IsDomain R) ∧ IsFractionRing R L
  · have := h.1.1; have := h.1.2.1; have := h.1.2.2; have := h.2
    rw [ordOf_eq, ordOf_eq, ordOf_eq, map_mul, map_mul,
      log_mul (ordFrac_algEquiv_ne_zero a) (ordFrac_algEquiv_ne_zero b)]
  · simp [ordOf, h]

variable (R L) in
/-- `Ring.ordOf` as a homomorphism on units. -/
noncomputable def ordOfUnits : Lˣ →* Multiplicative ℤ where
  toFun z := .ofAdd (ordOf R L z)
  map_one' := by
    have h := ordOf_mul (R := R) (1 : Lˣ) 1
    simp only [Units.val_one, mul_one] at h
    simp [show ordOf R L 1 = 0 by omega]
  map_mul' a b := by simp [ordOf_mul]

@[simp]
lemma ordOfUnits_apply (z : Lˣ) : ordOfUnits R L z = .ofAdd (ordOf R L z) := rfl

lemma ordOf_zpow (z : Lˣ) (n : ℤ) : ordOf R L ↑(z ^ n) = n * ordOf R L z := by
  have := map_zpow (ordOfUnits R L) z n
  simp only [ordOfUnits_apply] at this
  rw [← ofAdd_zsmul] at this
  simpa using this

section DVR

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R L]

/-- In a fraction ring of a discrete valuation ring, every unit is a unit of the ring times a
power of a uniformiser. -/
lemma exists_units_eq_mul_zpow {ϖ : R} (hϖ : Irreducible ϖ) (z : Lˣ) :
    ∃ (u : Rˣ) (n : ℤ) (ϖL : Lˣ), (ϖL : L) = algebraMap R L ϖ ∧
      z = Units.map (algebraMap R L) u * ϖL ^ n := by
  set e := algEquiv (nonZeroDivisors R) L (FractionRing R)
  have hϖu : IsUnit (algebraMap R L ϖ) := IsLocalization.map_units L
    (⟨ϖ, mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero⟩ : nonZeroDivisors R)
  have : Nontrivial L := e.toEquiv.nontrivial
  have hz : e z ≠ 0 := fun h ↦ z.ne_zero (e.injective (h.trans (map_zero e).symm))
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ hz
  refine ⟨u, n, hϖu.unit, rfl, Units.ext (e.injective ?_)⟩
  have hpow : e ↑(hϖu.unit ^ n) = algebraMap R (FractionRing R) ϖ ^ n := by
    have : e ↑(hϖu.unit ^ n) =
        ↑(Units.map (e : L →* FractionRing R) (hϖu.unit ^ n)) := rfl
    rw [this, map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map]
    simp
  rw [hu, Units.val_mul, map_mul, hpow, Units.coe_map, MonoidHom.coe_ofClass, AlgEquiv.commutes,
    Units.smul_def, Algebra.smul_def]

/-- **Units of order zero.** In a fraction ring of a discrete valuation ring, a unit of order
`0` comes from a unit of the ring. -/
lemma exists_eq_algebraMap_of_ordOf_eq_zero (z : Lˣ) (h : ordOf R L z = 0) :
    ∃ r : Rˣ, algebraMap R L r = z := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨u, n, ϖL, hϖL, rfl⟩ := exists_units_eq_mul_zpow (L := L) hϖ z
  have hϖ' : ordOf R L ϖL = 1 := by rw [hϖL, ordOf_algebraMap_of_irreducible hϖ]
  rw [Units.val_mul, ordOf_mul, ordOf_zpow, hϖ', Units.coe_map, MonoidHom.coe_ofClass,
    ordOf_algebraMap_of_isUnit u.isUnit, zero_add, mul_one] at h
  subst h
  exact ⟨u, by simp⟩

lemma ordOf_units_eq {ϖ : R} (hϖ : Irreducible ϖ) (u : Rˣ) (n : ℤ) (ϖL : Lˣ)
    (hϖL : (ϖL : L) = algebraMap R L ϖ) :
    ordOf R L ↑(Units.map (algebraMap R L : R →* L) u * ϖL ^ n) = n := by
  have hϖ' : ordOf R L ϖL = 1 := by rw [hϖL, ordOf_algebraMap_of_irreducible hϖ]
  rw [Units.val_mul, ordOf_mul, ordOf_zpow, hϖ', Units.coe_map, MonoidHom.coe_ofClass,
    ordOf_algebraMap_of_isUnit u.isUnit, zero_add, mul_one]

variable {R' L' : Type*} [CommRing R'] [CommRing L'] [Algebra R' L'] [IsDomain R']
  [IsDiscreteValuationRing R'] [IsFractionRing R' L']

/-- **The order is preserved by unramified extensions.** Let `φ : R ⟶ R'` be a homomorphism of
discrete valuation rings with `φ(𝔪_R) R' = 𝔪_{R'}`, so that a uniformiser of `R` stays a
uniformiser of `R'`, and let `λ : L ⟶ L'` be a compatible map of fraction rings. Then
`ord_{R'} (λ z) = ord_R z` for every unit `z` of `L`. -/
lemma ordOf_map (φ : R →+* R') (lam : L →+* L')
    (hcomm : lam.comp (algebraMap R L) = (algebraMap R' L').comp φ)
    (hm : (IsLocalRing.maximalIdeal R).map φ = IsLocalRing.maximalIdeal R') (z : Lˣ) :
    ordOf R' L' (lam z) = ordOf R L z := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖ' : Irreducible (φ ϖ) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hm,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
      Set.image_singleton]
  obtain ⟨u, n, ϖL, hϖL, rfl⟩ := exists_units_eq_mul_zpow (L := L) hϖ z
  rw [ordOf_units_eq hϖ u n ϖL hϖL]
  have hcomm' (r : R) : lam (algebraMap R L r) = algebraMap R' L' (φ r) :=
    RingHom.congr_fun hcomm r
  have : lam ↑(Units.map (algebraMap R L : R →* L) u * ϖL ^ n) =
      ↑(Units.map (algebraMap R' L' : R' →* L') (Units.map (φ : R →* R') u) *
        Units.map (lam : L →* L') ϖL ^ n) := by
    have e : lam ↑(Units.map (algebraMap R L : R →* L) u * ϖL ^ n) =
        ↑(Units.map (lam : L →* L') (Units.map (algebraMap R L : R →* L) u * ϖL ^ n)) := rfl
    rw [e, map_mul, map_zpow]
    congr 2
    ext
    simp [hcomm']
  rw [this, ordOf_units_eq hϖ' _ n _ (by simp [hϖL, hcomm'])]

end DVR

end Ring

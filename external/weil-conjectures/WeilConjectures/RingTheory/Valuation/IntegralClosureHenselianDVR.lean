/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.HenselianDVRExtension

/-!
# The integral closure of a henselian DVR in an algebraic extension is a valuation ring

Let `R` be a henselian discrete valuation ring and `Ω` a field which is algebraic over `R`
(with `R → Ω` injective), e.g. an algebraic closure of the fraction field of `R`. The elements
of `Ω` integral over `R` form a valuation subring `integralClosureValuationSubring R Ω` of `Ω`:
for `z : Ω`, some `p ^ n`-th power `y` of `z` is separable over `Frac R`, and the integral
closure of `R` in `Frac R (y)` is a discrete valuation ring, so `y` or `y⁻¹` is integral.

## Main statements

- `IsDiscreteValuationRing.integralClosureValuationSubring`: the valuation subring.
- `IsDiscreteValuationRing.valuation_algebraMap_eq_one_iff`,
  `IsDiscreteValuationRing.valuation_algebraMap_lt_one_iff`: restriction to `R`.
- `IsDiscreteValuationRing.exists_valuation_pow_eq_zpow`: the value group is contained in the
  divisible hull of the value group of `R`.
- `IsDiscreteValuationRing.comap_integralClosureValuationSubring`: functoriality.
- `IsDiscreteValuationRing.map_mem_integralClosureValuationSubring_iff`: Galois stability.
-/

@[expose] public section

universe u v

open Polynomial IntermediateField

/-- In an algebraic extension `Ω / K`, some `p ^ n`-th power of every element is separable,
where `p` is the characteristic exponent of `K`. -/
lemma exists_isSeparable_pow_ringExpChar_pow {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (z : Ω) : ∃ n, IsSeparable K (z ^ ringExpChar K ^ n) := by
  obtain ⟨n, w, hw⟩ := IsPurelyInseparable.pow_mem (separableClosure K Ω) (ringExpChar K) z
  exact ⟨n, hw ▸ mem_separableClosure_iff.1 w.2⟩

/-- To prove a property of a separable element `y` of `Ω / K`, it suffices to prove it for all
images of elements of finite separable extensions of `K` in the same universe as `K`. -/
lemma IsSeparable.induction_finiteDimensional {R K : Type u} {Ω : Type*} [CommRing R] [Field K]
    [Algebra R K] [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω] {P : Ω → Prop}
    (hP : ∀ (L : Type u) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
      [FiniteDimensional K L] [Algebra.IsSeparable K L] (φ : L →ₐ[K] Ω) (x : L), P (φ x))
    {y : Ω} (hy : IsSeparable K y) : P y := by
  have hint := hy.isIntegral
  have := Fact.mk (minpoly.irreducible hint)
  let e := adjoinRootEquivAdjoin K hint
  have := (isSeparable_adjoin_simple_iff_isSeparable K Ω).2 hy
  have := Algebra.IsSeparable.of_algHom K K⟮y⟯ e.toAlgHom
  have := adjoin.finiteDimensional hint
  have := LinearEquiv.finiteDimensional e.symm.toLinearEquiv
  have := hP _ ((K⟮y⟯.val).comp e.toAlgHom) (e.symm ⟨y, mem_adjoin_simple_self K y⟩)
  simpa using this

namespace IsDiscreteValuationRing

/-- If `L` is a finite separable extension of the fraction field `K` of a henselian DVR `R`,
then every `x : L` or its inverse is integral over `R`: the integral closure of `R` in `L`
is a discrete valuation ring with fraction field `L`. -/
lemma isIntegral_or_isIntegral_inv_of_finiteDimensional {R : Type u} (K : Type u) {L : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (x : L) :
    IsIntegral R x ∨ IsIntegral R x⁻¹ := by
  have := isDiscreteValuationRing_integralClosure R K L
  have := integralClosure.isFractionRing_of_finite_extension (A := R) K L
  rcases ValuationRing.isInteger_or_isInteger (integralClosure R L) x with ⟨b, hb⟩ | ⟨b, hb⟩
  · exact .inl (hb ▸ b.2)
  · exact .inr (hb ▸ b.2)

section FractionField

variable {R K : Type u} {Ω : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω]
  [Algebra R Ω] [IsScalarTower R K Ω]

variable (K) in
/-- If `Ω` is algebraic over the fraction field `K` of a henselian DVR `R`, then every element
of `Ω` or its inverse is integral over `R`. -/
lemma isIntegral_or_isIntegral_inv [Algebra.IsAlgebraic K Ω] (z : Ω) :
    IsIntegral R z ∨ IsIntegral R z⁻¹ := by
  obtain ⟨n, hn⟩ := exists_isSeparable_pow_ringExpChar_pow (K := K) z
  have hpos : 0 < ringExpChar K ^ n := by
    have := expChar_pos K (ringExpChar K)
    positivity
  refine hn.induction_finiteDimensional (R := R) (P := fun y ↦ y = z ^ ringExpChar K ^ n →
    IsIntegral R z ∨ IsIntegral R z⁻¹) (fun L _ _ _ _ _ _ φ x hx ↦ ?_) rfl
  rcases isIntegral_or_isIntegral_inv_of_finiteDimensional (R := R) K x with h | h
  · exact .inl (IsIntegral.of_pow hpos (hx ▸ h.map (φ.restrictScalars R)))
  · refine .inr (IsIntegral.of_pow hpos ?_)
    rw [inv_pow, ← hx, ← map_inv₀]
    exact h.map (φ.restrictScalars R)

end FractionField

/-- The algebra structure on `Ω` over the fraction field of `R`, if `R → Ω` is injective. -/
noncomputable abbrev algebraFractionRing (R Ω : Type*) [CommRing R] [IsDomain R] [Field Ω]
    [Algebra R Ω] [FaithfulSMul R Ω] : Algebra (FractionRing R) Ω :=
  (IsFractionRing.lift (FaithfulSMul.algebraMap_injective R Ω)).toAlgebra

/-- The scalar tower `R → Frac R → Ω` for `algebraFractionRing`. -/
lemma isScalarTower_algebraFractionRing (R Ω : Type*) [CommRing R] [IsDomain R] [Field Ω]
    [Algebra R Ω] [FaithfulSMul R Ω] :
    letI := algebraFractionRing R Ω
    IsScalarTower R (FractionRing R) Ω :=
  letI := algebraFractionRing R Ω
  IsScalarTower.of_algebraMap_eq fun r ↦ (IsFractionRing.lift_algebraMap _ r).symm

variable (R : Type u) (Ω : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Field Ω] [Algebra R Ω] [FaithfulSMul R Ω] [Algebra.IsAlgebraic R Ω]

/-- **The integral closure of a henselian DVR `R` in an algebraic field extension `Ω` is a
valuation ring.** -/
noncomputable def integralClosureValuationSubring : ValuationSubring Ω where
  toSubring := (integralClosure R Ω).toSubring
  mem_or_inv_mem' z := by
    let := algebraFractionRing R Ω
    have := isScalarTower_algebraFractionRing R Ω
    have := Algebra.IsAlgebraic.extendScalars (R := R) (S := FractionRing R) (A := Ω)
      (IsFractionRing.injective R (FractionRing R))
    exact isIntegral_or_isIntegral_inv (FractionRing R) z

variable {R Ω}

@[simp]
lemma mem_integralClosureValuationSubring {z : Ω} :
    z ∈ integralClosureValuationSubring R Ω ↔ IsIntegral R z :=
  Iff.rfl

/-- An element `x ≠ 0` of a valuation subring whose inverse also lies in it has valuation `1`. -/
lemma _root_.ValuationSubring.valuation_eq_one_of_inv_mem {F : Type*} [Field F]
    (A : ValuationSubring F) {x : F} (hx₀ : x ≠ 0) (hx : x ∈ A) (hx' : x⁻¹ ∈ A) :
    A.valuation x = 1 :=
  (A.valuation_eq_one_iff ⟨x, hx⟩).1
    (IsUnit.of_mul_eq_one ⟨x⁻¹, hx'⟩ (Subtype.ext (mul_inv_cancel₀ hx₀)))

/-- If the inverse of the image of `r ≠ 0` is integral over `R`, then `r` is a unit. -/
lemma isUnit_of_isIntegral_inv {R : Type*} (K : Type*) {Ω : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω]
    [Algebra R Ω] [IsScalarTower R K Ω] {r : R} (hr : r ≠ 0)
    (h : IsIntegral R (algebraMap R Ω r)⁻¹) : IsUnit r := by
  rw [IsScalarTower.algebraMap_apply R K Ω, ← map_inv₀] at h
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.1
    ((isIntegral_algHom_iff (IsScalarTower.toAlgHom R K Ω) (algebraMap K Ω).injective).1 h)
  refine IsUnit.of_mul_eq_one (a := r) s (IsFractionRing.injective R K ?_)
  rw [map_mul, hs, map_one, mul_inv_cancel₀]
  rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective R K)]

/-- Elements of `R` lie in the valuation subring. -/
lemma algebraMap_mem_integralClosureValuationSubring (r : R) :
    algebraMap R Ω r ∈ integralClosureValuationSubring R Ω :=
  isIntegral_algebraMap

lemma valuation_algebraMap_le_one (r : R) :
    (integralClosureValuationSubring R Ω).valuation (algebraMap R Ω r) ≤ 1 :=
  ((integralClosureValuationSubring R Ω).valuation_le_one_iff _).2
    (algebraMap_mem_integralClosureValuationSubring r)

/-- An element of `R` has value `1` if and only if it is a unit. -/
lemma valuation_algebraMap_eq_one_iff {r : R} :
    (integralClosureValuationSubring R Ω).valuation (algebraMap R Ω r) = 1 ↔ IsUnit r := by
  set 𝒪 := integralClosureValuationSubring R Ω
  constructor
  · intro h
    have hr : r ≠ 0 := by
      rintro rfl
      simp at h
    let := algebraFractionRing R Ω
    have := isScalarTower_algebraFractionRing R Ω
    refine isUnit_of_isIntegral_inv (Ω := Ω) (FractionRing R) hr ?_
    rw [← mem_integralClosureValuationSubring, ← 𝒪.valuation_le_one_iff, map_inv₀, h, inv_one]
  · rintro ⟨u, rfl⟩
    have hu : algebraMap R Ω u ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R Ω)).2 u.ne_zero
    refine 𝒪.valuation_eq_one_of_inv_mem hu
      (algebraMap_mem_integralClosureValuationSubring _) ?_
    rw [← map_units_inv]
    exact algebraMap_mem_integralClosureValuationSubring _

/-- An element of `R` has value `< 1` if and only if it lies in the maximal ideal. -/
lemma valuation_algebraMap_lt_one_iff {r : R} :
    (integralClosureValuationSubring R Ω).valuation (algebraMap R Ω r) < 1 ↔
      r ∈ IsLocalRing.maximalIdeal R := by
  rw [lt_iff_le_and_ne, ne_eq, valuation_algebraMap_eq_one_iff, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff]
  exact and_iff_right (valuation_algebraMap_le_one r)

omit [Algebra.IsAlgebraic R Ω] in
/-- **The value group, finite level.** If `L` is a finite separable extension of the fraction
field of `R` and `φ : L → Ω`, then the value of every `φ x ≠ 0` has a power which is a power of
the value of a uniformizer `ϖ` of `R`. -/
lemma exists_valuation_pow_eq_zpow_of_finiteDimensional [Algebra.IsAlgebraic R Ω]
    (K : Type u) {L : Type u} [Field K]
    [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (φ : L →ₐ[R] Ω) {ϖ : R}
    (hϖ : Irreducible ϖ) {x : L} (hx : x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, (integralClosureValuationSubring R Ω).valuation (φ x) ^ n =
      (integralClosureValuationSubring R Ω).valuation (algebraMap R Ω ϖ) ^ m := by
  set 𝒪 := integralClosureValuationSubring R Ω
  let B := integralClosure R L
  have := isDiscreteValuationRing_integralClosure R K L
  have := integralClosure.isFractionRing_of_finite_extension (A := R) K L
  obtain ⟨π, hπ⟩ := exists_irreducible B
  let ψ : B →ₐ[R] Ω := φ.comp B.val
  have hψmem (b : B) : ψ b ∈ 𝒪 := mem_integralClosureValuationSubring.2 (b.2.map φ)
  have hψinj : Function.Injective ψ := φ.toRingHom.injective.comp Subtype.val_injective
  have hunit (u : Bˣ) : 𝒪.valuation (ψ u) = 1 := by
    refine 𝒪.valuation_eq_one_of_inv_mem ((map_ne_zero_iff _ hψinj).2 u.ne_zero) (hψmem _) ?_
    rw [← map_units_inv]
    exact hψmem _
  have hval (b : B) (hb : b ≠ 0) : ∃ k : ℕ, 𝒪.valuation (ψ b) = 𝒪.valuation (ψ π) ^ k := by
    obtain ⟨k, u, rfl⟩ := eq_unit_mul_pow_irreducible hb hπ
    refine ⟨k, ?_⟩
    rw [map_mul, map_pow, Valuation.map_mul, Valuation.map_pow, hunit, one_mul]
  have hw : 𝒪.valuation (ψ π) ≠ 0 := by
    rw [Valuation.ne_zero_iff, map_ne_zero_iff _ hψinj]
    exact hπ.ne_zero
  obtain ⟨e, he⟩ := hval (algebraMap R B ϖ)
    ((map_ne_zero_iff _ (injective_algebraMap_integralClosure R K L)).2 hϖ.ne_zero)
  rw [ψ.commutes] at he
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, valuation_algebraMap_eq_one_iff] at he
    exact hϖ.not_isUnit he
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective B x
  have hb : b ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨k₁, hk₁⟩ := hval b hb
  obtain ⟨k₂, hk₂⟩ := hval c (nonZeroDivisors.ne_zero hc)
  refine ⟨e, Nat.pos_of_ne_zero he0, (k₁ : ℤ) - k₂, ?_⟩
  have hφ : φ (algebraMap B L b / algebraMap B L c) = ψ b / ψ c := map_div₀ φ _ _
  rw [hφ, map_div₀, hk₁, hk₂, he, div_pow, ← pow_mul, ← pow_mul, zpow_sub₀ (pow_ne_zero _ hw),
    zpow_natCast, zpow_natCast, ← pow_mul, ← pow_mul, mul_comm e k₁, mul_comm e k₂]

/-- **The value group.** Every nonzero element of `Ω` has a power whose value is a power of the
value of a uniformizer `ϖ` of `R`. -/
theorem exists_valuation_pow_eq_zpow {ϖ : R} (hϖ : Irreducible ϖ) {z : Ω} (hz : z ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, (integralClosureValuationSubring R Ω).valuation z ^ n =
      (integralClosureValuationSubring R Ω).valuation (algebraMap R Ω ϖ) ^ m := by
  let := algebraFractionRing R Ω
  have := isScalarTower_algebraFractionRing R Ω
  have := Algebra.IsAlgebraic.extendScalars (R := R) (S := FractionRing R) (A := Ω)
    (IsFractionRing.injective R (FractionRing R))
  set q := ringExpChar (FractionRing R)
  obtain ⟨k, hk⟩ := exists_isSeparable_pow_ringExpChar_pow (K := FractionRing R) z
  have hpos : 0 < q ^ k := by
    have := expChar_pos (FractionRing R) q
    positivity
  refine hk.induction_finiteDimensional (R := R) (P := fun y ↦ y = z ^ q ^ k → _)
    (fun L _ _ _ _ _ _ φ x hx ↦ ?_) rfl
  obtain ⟨n, hn, m, h⟩ := exists_valuation_pow_eq_zpow_of_finiteDimensional (FractionRing R)
    (φ.restrictScalars R) hϖ (x := x) (by
      rintro rfl
      rw [map_zero] at hx
      exact pow_ne_zero _ hz hx.symm)
  refine ⟨q ^ k * n, Nat.mul_pos hpos hn, m, ?_⟩
  rw [pow_mul, ← Valuation.map_pow, ← hx]
  exact h

/-- **Galois stability.** A ring automorphism of `Ω` fixing `R` preserves
`integralClosureValuationSubring R Ω`. -/
lemma map_mem_integralClosureValuationSubring_iff (σ : Ω ≃+* Ω)
    (hσ : ∀ r : R, σ (algebraMap R Ω r) = algebraMap R Ω r) {z : Ω} :
    σ z ∈ integralClosureValuationSubring R Ω ↔ z ∈ integralClosureValuationSubring R Ω :=
  isIntegral_algEquiv (AlgEquiv.ofRingEquiv hσ)

lemma comap_integralClosureValuationSubring_ringEquiv (σ : Ω ≃+* Ω)
    (hσ : ∀ r : R, σ (algebraMap R Ω r) = algebraMap R Ω r) :
    (integralClosureValuationSubring R Ω).comap (σ : Ω →+* Ω) =
      integralClosureValuationSubring R Ω :=
  SetLike.ext fun _ ↦ map_mem_integralClosureValuationSubring_iff σ hσ

/-- **Functoriality.** Let `R → R'` be an injective local homomorphism of henselian DVRs and
`Ω → Ω'` a compatible field homomorphism. Then the valuation subring of `Ω` attached to `R` is
the preimage of the one of `Ω'` attached to `R'`. -/
theorem comap_integralClosureValuationSubring {R' : Type v} {Ω' : Type*} [CommRing R']
    [IsDomain R'] [IsDiscreteValuationRing R'] [HenselianLocalRing R'] [Field Ω']
    [Algebra R' Ω'] [FaithfulSMul R' Ω'] [Algebra.IsAlgebraic R' Ω'] [Algebra R R']
    [IsLocalHom (algebraMap R R')] [Algebra Ω Ω'] [Algebra R Ω'] [IsScalarTower R R' Ω']
    [IsScalarTower R Ω Ω'] :
    (integralClosureValuationSubring R' Ω').comap (algebraMap Ω Ω') =
      integralClosureValuationSubring R Ω := by
  set 𝒪 := integralClosureValuationSubring R Ω
  set 𝒪' := integralClosureValuationSubring R' Ω'
  have hsub (z : Ω) (hz : z ∈ 𝒪) : algebraMap Ω Ω' z ∈ 𝒪' :=
    mem_integralClosureValuationSubring.2
      ((hz.map (IsScalarTower.toAlgHom R Ω Ω')).tower_top (A := R'))
  ext z
  refine ⟨fun h ↦ ?_, hsub z⟩
  rw [ValuationSubring.mem_comap] at h
  by_contra hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hz 𝒪.zero_mem
  have ht : 𝒪.valuation z⁻¹ < 1 := by
    refine lt_of_le_of_ne ((𝒪.valuation_le_one_iff _).2 ((𝒪.mem_or_inv_mem z).resolve_left hz))
      fun h1 ↦ hz ?_
    rw [← 𝒪.valuation_le_one_iff, ← inv_inv z, map_inv₀, h1, inv_one]
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  have hϖ1 : 𝒪.valuation (algebraMap R Ω ϖ) < 1 :=
    valuation_algebraMap_lt_one_iff.2 ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit)
  have hϖ0 : algebraMap R Ω ϖ ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R Ω)).2 hϖ.ne_zero
  obtain ⟨n, hn, m, hnm⟩ := exists_valuation_pow_eq_zpow hϖ (inv_ne_zero hz0)
  have hm : 0 < m := by
    refine (zpow_lt_one_iff_right_of_lt_one₀ ?_ hϖ1).1 (hnm ▸ pow_lt_one₀ zero_le ht hn.ne')
    rwa [zero_lt_iff, Valuation.ne_zero_iff]
  lift m to ℕ using hm.le
  rw [zpow_natCast] at hnm
  set u := z⁻¹ ^ n / algebraMap R Ω ϖ ^ m
  have hu : 𝒪.valuation u = 1 := by
    rw [map_div₀, Valuation.map_pow, hnm, Valuation.map_pow, div_self]
    rwa [pow_ne_zero_iff (by omega), Valuation.ne_zero_iff]
  have hu0 : u ≠ 0 := by
    rintro h0
    simp [h0] at hu
  have hu' : 𝒪'.valuation (algebraMap Ω Ω' u) = 1 := by
    refine 𝒪'.valuation_eq_one_of_inv_mem ((map_ne_zero_iff _ (algebraMap Ω Ω').injective).2 hu0)
      (hsub u ((𝒪.valuation_le_one_iff u).1 hu.le)) ?_
    rw [← map_inv₀]
    refine hsub _ ((𝒪.valuation_le_one_iff _).1 ?_)
    rw [map_inv₀, hu, inv_one]
  have hϖ' : 𝒪'.valuation (algebraMap Ω Ω' (algebraMap R Ω ϖ)) < 1 := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R' Ω',
      valuation_algebraMap_lt_one_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun h ↦ hϖ.not_isUnit (IsLocalHom.map_nonunit _ h)
  have hzt : 1 ≤ 𝒪'.valuation (algebraMap Ω Ω' z⁻¹) := by
    rw [map_inv₀, map_inv₀]
    refine one_le_inv_iff₀.2 ⟨?_, (𝒪'.valuation_le_one_iff _).2 h⟩
    rw [zero_lt_iff, Valuation.ne_zero_iff, map_ne_zero_iff _ (algebraMap Ω Ω').injective]
    exact hz0
  have key : algebraMap Ω Ω' z⁻¹ ^ n =
      algebraMap Ω Ω' u * algebraMap Ω Ω' (algebraMap R Ω ϖ) ^ m := by
    rw [← map_pow, ← map_pow, ← map_mul, div_mul_cancel₀ _ (pow_ne_zero _ hϖ0)]
  have := congrArg 𝒪'.valuation key
  rw [Valuation.map_pow, Valuation.map_mul, hu', one_mul, Valuation.map_pow] at this
  exact (one_le_pow₀ hzt).not_gt (this ▸ pow_lt_one₀ zero_le hϖ' (by omega))

end IsDiscreteValuationRing

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceStabilityCharP
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceKummerHensel
public import WeilConjectures.RingTheory.Valuation.KummerNormalFormGeneral

/-!

# Relative separable closedness of the slice composita, mixed characteristic

Let `D₁ ⟶ D₂` be a morphism of strict-localization slice traits over a change of traits
`R₁ ⟶ R₂`, with composita `Lᵢ = Ωᵢ(Sᵢ(x))`. In characteristic `0` with residual characteristic
`p > 0`, a Kummer equation `θ ^ p = α` over `L₁` which has a root in `L₂` has a root in `L₁`
(`SliceTrait.Hom.exists_pow_root_of_mixedChar`), via the abstract normal form
`exists_pow_eq_of_kummer_of_approx`.

-/

@[expose] public section

universe u

open IsLocalRing IntermediateField

/-- A ring map carries combinations of lifted Frobenius monomials to combinations of the image
monomials. -/
lemma frobeniusComb_mapRange {Ω Ω' : Type*} [Field Ω] [Field Ω'] {ι : Type*} (p : ℕ)
    (w : ι → Ω) (f : Ω →+* Ω') (c : Option (ι × ℕ) →₀ Ω) :
    frobeniusComb p (fun i ↦ f (w i)) (c.mapRange f (map_zero f)) = f (frobeniusComb p w c) := by
  rw [frobeniusComb, Finsupp.sum_mapRange_index (fun _ ↦ zero_mul _), frobeniusComb,
    map_finsuppSum]
  refine Finsupp.sum_congr fun j _ ↦ ?_
  rw [map_mul]
  congr 1
  cases j with
  | none => simp [frobeniusMonomial]
  | some i => simp [frobeniusMonomial]

namespace AlgebraicGeometry.SliceTrait.Hom

attribute [local instance] algebraR algebraΩ algebraBaseΩ algebraRΩ

variable {R₁ R₂ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  [IsStrictlyHenselianLocalRing R₁] [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂]
  [IsStrictlyHenselianLocalRing R₂] {ι : R₁ →+* R₂} {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂]
  [IsAlgClosed Ω₁] [IsAlgClosed Ω₂] {c : Ω₁ →+* Ω₂} {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂}
  (ha₁ : Function.Injective a₁) (halg₁ : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
  (ha₂ : Function.Injective a₂) (halg₂ : letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂)
  {κ : Type u} [Field κ] [IsSepClosed κ] {b₁ : R₁ →+* κ} {b₂ : R₂ →+* κ}
  (hb₁ : RingHom.ker b₁ = maximalIdeal R₁) (hb₂ : RingHom.ker b₂ = maximalIdeal R₂)

local notation "𝒟₁" => sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₁) ha₁ halg₁ hb₁
local notation "𝒟₂" => sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂

omit [IsAlgClosed Ω₂] in
include ha₁ halg₁ ha₂ halg₂ hb₁ hb₂ in
/-- **Kummer equations over the slice composita, mixed characteristic.** For a morphism
`H : D₁ ⟶ D₂` of strict-localization slice traits which is the identity on the fields
`κ(x)^alg` of the closed points, in characteristic `0` with residual characteristic `p`, an
element `α` of `L₁ = Ω₁(S₁(x))` which is a `p`-th power in `L₂` is a `p`-th power in `L₁`. -/
theorem exists_pow_root_of_mixedChar (p : ℕ) [Fact p.Prime] [CharZero Ω₁]
    [CharP (ResidueField R₁) p] [CharP (ResidueField R₂) p] (H : SliceTrait.Hom ι c 𝒟₁ 𝒟₂)
    (hκ : ∀ y, H.κMap y = y) {α : (𝒟₁).Ω} (hα : letI := a₁.toAlgebra; α ∈ (𝒟₁).compositum)
    (h₂ : letI := a₂.toAlgebra; ∃ θ ∈ (𝒟₂).compositum, θ ^ p = H.ΩMap α) :
    letI := a₁.toAlgebra
    ∃ θ ∈ (𝒟₁).compositum, θ ^ p = α := by
  classical
  let := a₁.toAlgebra
  let := a₂.toAlgebra
  set Γ := H.ΩMap with hΓ
  set v₁ := (𝒟₁).valuationSubring.valuation with hv₁
  set v₂ := (𝒟₂).valuationSubring.valuation with hv₂
  have hp : p.Prime := Fact.out
  have : CharZero (𝒟₁).Ω := charZero_of_injective_ringHom (𝒟₁).ωS.injective
  have : CharZero (𝒟₂).Ω := charZero_of_injective_ringHom Γ.injective
  have hp0 : (p : (𝒟₂).Ω) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hp1 : v₂ (p : (𝒟₂).Ω) < 1 := by
    have hpm : (p : R₂) ∈ maximalIdeal R₂ := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]
    have hpm' : (p : (𝒟₂).R) ∈ maximalIdeal (𝒟₂).R := by
      rw [(𝒟₂).maximalIdeal_eq, ← map_natCast (𝒟₂).φ]
      exact Ideal.mem_map_of_mem _ hpm
    rw [← map_natCast (𝒟₂).a]
    exact (𝒟₂).valuation_a_lt_one_iff.2 hpm'
  obtain ⟨x₁, hx₁⟩ := exists_b_eq_traitSliceCoord ha₁ halg₁ hb₁
  obtain ⟨x₂, hx₂⟩ := exists_b_eq_traitSliceCoord ha₂ halg₂ hb₂
  obtain ⟨ιw, w, A, Kst, hKst, hwA, hA, hw1, hval, hpb, ⟨ϖ, hϖK, hϖ0, hϖ1, hdisc, hϖN⟩,
    hAapp, hαapp, hexp, hAinv, hKstA, hKstroot⟩ :=
    exists_frobeniusLift_package ha₁ halg₁ hb₁ p hx₁ hα
  -- the subfields of `D₂.Ω`
  set K : Subfield (𝒟₂).Ω := (𝒟₁).ωS.fieldRange.map Γ with hKdef
  set L₁ : Subfield (𝒟₂).Ω := (𝒟₁).compositum.toSubfield.map Γ with hL₁def
  set L₂ : Subfield (𝒟₂).Ω := (𝒟₂).compositum.toSubfield with hL₂def
  set w₂ : ιw → (𝒟₂).Ω := fun i ↦ Γ (w i) with hw₂
  -- lifting along `Γ`
  let lf : (𝒟₂).Ω → (𝒟₁).Ω := fun y ↦ if h : ∃ x, Γ x = y then h.choose else 0
  have hlf : ∀ x, lf (Γ x) = x := fun x ↦ by
    have h : ∃ x', Γ x' = Γ x := ⟨x, rfl⟩
    simp only [lf, dite_eq_left h]
    exact Γ.injective h.choose_spec
  have hlf0 : lf 0 = 0 := by
    have := hlf 0
    rwa [map_zero] at this
  have hcomb : ∀ c₁ : Option (ιw × ℕ) →₀ (𝒟₁).Ω,
      frobeniusComb p w₂ (c₁.mapRange Γ (map_zero Γ)) = Γ (frobeniusComb p w c₁) :=
    frobeniusComb_mapRange p w Γ
  have hliftc : ∀ (S : Subfield (𝒟₁).Ω) (c : Option (ιw × ℕ) →₀ (𝒟₂).Ω), (∀ j, c j ∈ S.map Γ) →
      ∃ c₁ : Option (ιw × ℕ) →₀ (𝒟₁).Ω, (∀ j, c₁ j ∈ S) ∧ c = c₁.mapRange Γ (map_zero Γ) := by
    intro S c hc
    refine ⟨c.mapRange lf hlf0, fun j ↦ ?_, ?_⟩
    · obtain ⟨s, hs, hsj⟩ := Subfield.mem_map.1 (hc j)
      rw [Finsupp.mapRange_apply, ← hsj, hlf]
      exact hs
    · ext j
      obtain ⟨s, hs, hsj⟩ := Subfield.mem_map.1 (hc j)
      rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply, ← hsj, hlf]
  have hmapc : ∀ (S : Subfield (𝒟₁).Ω) (c₁ : Option (ιw × ℕ) →₀ (𝒟₁).Ω), (∀ j, c₁ j ∈ S) →
      ∀ j, c₁.mapRange Γ (map_zero Γ) j ∈ S.map Γ := fun S c₁ hc₁ j ↦
    ⟨c₁ j, hc₁ j, (Finsupp.mapRange_apply ..).symm⟩
  have hfr : (𝒟₁).ωS.fieldRange ≤ (𝒟₁).compositum.toSubfield := by
    rintro _ ⟨ω, rfl⟩
    exact IntermediateField.algebraMap_mem _ ω
  -- the hypotheses of the abstract normal form
  have hKL₁ : K ≤ L₁ := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hfr hz, rfl⟩
  have hL : L₁ ≤ L₂ := by
    rintro _ ⟨y, hy, rfl⟩
    exact H.ΩMap_mem_compositum y hy
  have hKstK : Kst.map Γ ≤ K := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hKst hz, rfl⟩
  have hAL₁ : ∀ y ∈ A.map Γ, y ∈ L₁ := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, (hA z hz).1, rfl⟩
  have hroot : ∀ y ∈ K, ∃ e ∈ K, e ^ p = y := by
    rintro _ ⟨_, ⟨ω, rfl⟩, rfl⟩
    obtain ⟨ω', hω'⟩ := IsAlgClosed.exists_pow_nat_eq ω hp.pos
    exact ⟨Γ ((𝒟₁).ωS ω'), ⟨_, ⟨ω', rfl⟩, rfl⟩, by rw [← map_pow, ← map_pow, hω']⟩
  have hw₂A : ∀ i, w₂ i ∈ A.map Γ := fun i ↦ ⟨w i, hwA i, rfl⟩
  have hw₂1 : ∀ i, v₂ (w₂ i) = 1 := fun i ↦ (H.valuation_ΩMap_eq_one_iff _).2 (hw1 i)
  have hA1 : ∀ y ∈ A.map Γ, v₂ y ≤ 1 := by
    rintro _ ⟨z, hz, rfl⟩
    exact (H.valuation_ΩMap_le_one_iff _).2 (hA z hz).2
  have hval₂ : ∀ c : Option (ιw × ℕ) →₀ (𝒟₂).Ω, (∀ j, c j ∈ K) →
      ∀ j, v₂ (c j) ≤ v₂ (frobeniusComb p w₂ c) := by
    intro c hc j
    obtain ⟨c₁, hc₁, rfl⟩ := hliftc _ c hc
    rw [hcomb, Finsupp.mapRange_apply]
    exact (H.valuation_ΩMap_le_iff _ _).2 (hval c₁ hc₁ j)
  have hϖne : ϖ ≠ 0 := fun h ↦ by rw [h, map_zero] at hϖ0; exact lt_irrefl _ hϖ0
  have hγ0 : 0 < v₂ (Γ ϖ) :=
    (Valuation.pos_iff _).2 ((map_ne_zero_iff _ Γ.injective).2 hϖne)
  have hγ1 : v₂ (Γ ϖ) < 1 := (H.valuation_ΩMap_lt_one_iff _).2 hϖ1
  have hdisc₂ : ∀ y ∈ Kst.map Γ, y ≠ 0 → ∃ n : ℤ, v₂ y = v₂ (Γ ϖ) ^ n := by
    rintro _ ⟨y, hy, rfl⟩ hy0
    have hy0' : y ≠ 0 := fun h ↦ hy0 (by rw [h, map_zero])
    obtain ⟨n, hn⟩ := hdisc y hy hy0'
    refine ⟨n, ?_⟩
    have h1 : v₁ (y / ϖ ^ n) = 1 := by
      rw [map_div₀, map_zpow₀, hn, div_self (zpow_ne_zero _ hϖ0.ne')]
    have h2 := (H.valuation_ΩMap_eq_one_iff _).2 h1
    rw [map_div₀, map_zpow₀, map_div₀, map_zpow₀,
      div_eq_one_iff_eq (zpow_ne_zero _ hγ0.ne')] at h2
    exact h2
  have hγN : ∀ t ∈ L₁, t ≠ 0 → ∃ N : ℕ, v₂ (Γ ϖ) ^ N < v₂ t := by
    rintro _ ⟨t, -, rfl⟩ ht
    obtain ⟨N, hN⟩ := hϖN t fun h ↦ ht (by rw [h, map_zero])
    refine ⟨N, ?_⟩
    rw [← map_pow, ← map_pow]
    exact (H.valuation_ΩMap_lt_iff _ _).2 (by rwa [map_pow])
  have hAapp₂ : ∀ y ∈ A.map Γ, ∀ t ∈ L₁, t ≠ 0 → ∃ e : Option (ιw × ℕ) →₀ (𝒟₂).Ω,
      (∀ k, e k ∈ Kst.map Γ) ∧ v₂ (y - frobeniusComb p w₂ e) < v₂ t := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨t, -, rfl⟩ ht
    obtain ⟨e, he, hlt⟩ := hAapp y hy t fun h ↦ ht (by rw [h, map_zero])
    refine ⟨e.mapRange Γ (map_zero Γ), hmapc _ e he, ?_⟩
    rw [hcomb, ← map_sub]
    exact (H.valuation_ΩMap_lt_iff _ _).2 hlt
  have hAinv₂ : ∀ y ∈ A.map Γ, v₂ y = 1 → y⁻¹ ∈ A.map Γ := by
    rintro _ ⟨y, hy, rfl⟩ hy1
    exact ⟨y⁻¹, hAinv y hy ((H.valuation_ΩMap_eq_one_iff _).1 hy1), map_inv₀ Γ y⟩
  have hKstA₂ : ∀ y ∈ Kst.map Γ, v₂ y ≤ 1 → y ∈ A.map Γ := by
    rintro _ ⟨y, hy, rfl⟩ hy1
    exact ⟨y, hKstA y hy ((H.valuation_ΩMap_le_one_iff _).1 hy1), rfl⟩
  have hKstroot₂ : ∀ y ∈ Kst.map Γ, v₂ y ≤ 1 → ∃ d ∈ Kst.map Γ, v₂ (d ^ p - y) < 1 := by
    rintro _ ⟨y, hy, rfl⟩ hy1
    obtain ⟨d, hd, hdv⟩ := hKstroot y hy ((H.valuation_ΩMap_le_one_iff _).1 hy1)
    exact ⟨Γ d, ⟨d, hd, rfl⟩, by
      rw [← map_pow, ← map_sub]
      exact (H.valuation_ΩMap_lt_one_iff _).2 hdv⟩
  have hcl : Subfield.closure (K ∪ A.map Γ : Set (𝒟₂).Ω) ≤
      (Subfield.closure ((𝒟₁).ωS.fieldRange ∪ A : Set (𝒟₁).Ω)).map Γ := by
    refine Subfield.closure_le.2 ?_
    rintro _ (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact ⟨z, Subfield.subset_closure (Or.inl hz), rfl⟩
    · exact ⟨z, Subfield.subset_closure (Or.inr hz), rfl⟩
  have hexp₂ : ∀ y ∈ Subfield.closure (K ∪ A.map Γ : Set (𝒟₂).Ω), ∀ t ∈ L₁, t ≠ 0 →
      ∃ c : Option (ιw × ℕ) →₀ (𝒟₂).Ω, (∀ j, c j ∈ K) ∧
        v₂ (y - frobeniusComb p w₂ c) < v₂ t := by
    intro y hy
    obtain ⟨y₁, hy₁, rfl⟩ := hcl hy
    rintro _ ⟨t, -, rfl⟩ ht
    obtain ⟨e, he, hlt⟩ := hexp y₁ hy₁ t fun h ↦ ht (by rw [h, map_zero])
    refine ⟨e.mapRange Γ (map_zero Γ), hmapc _ e he, ?_⟩
    rw [hcomb, ← map_sub]
    exact (H.valuation_ΩMap_lt_iff _ _).2 hlt
  have hα₂ : ∀ t ∈ L₁, t ≠ 0 → ∃ e : Option (ιw × ℕ) →₀ (𝒟₂).Ω, (∀ k, e k ∈ Kst.map Γ) ∧
      v₂ (Γ α - frobeniusComb p w₂ e) < v₂ t := by
    rintro _ ⟨t, -, rfl⟩ ht
    obtain ⟨e, he, hlt⟩ := hαapp t fun h ↦ ht (by rw [h, map_zero])
    refine ⟨e.mapRange Γ (map_zero Γ), hmapc _ e he, ?_⟩
    rw [hcomb, ← map_sub]
    exact (H.valuation_ΩMap_lt_iff _ _).2 hlt
  -- Hensel's lemma for Kummer equations over `L₁`
  have : CharP (ResidueField (𝒟₁).R) p :=
    charP_of_injective_ringHom (ResidueField.map (𝒟₁).φ).injective p
  have hhens : ∀ x ∈ L₁, v₂.IsKummerNegligible p x → ∃ y ∈ L₁, y ^ p = 1 + x := by
    rintro _ ⟨x, hx, rfl⟩ hxn
    have hxn₁ : v₁.IsKummerNegligible p x := by
      unfold Valuation.IsKummerNegligible at hxn ⊢
      rw [← map_pow v₂, ← map_pow v₂, ← map_pow Γ,
        show ((p : (𝒟₂).Ω)) ^ p = Γ ((p : (𝒟₁).Ω) ^ p) by rw [map_pow, map_natCast],
        H.valuation_ΩMap_le_iff] at hxn
      rwa [← map_pow, ← map_pow]
    obtain ⟨y, hy, hyp⟩ := exists_pow_eq_one_add (𝒟₁) p hx hxn₁
    exact ⟨Γ y, ⟨y, hy, rfl⟩, by rw [← map_pow, hyp, map_add, map_one]⟩
  -- the residue of the coordinate is not a `p`-th power in `L₂`
  have hcoord : v₂ ((𝒟₂).a x₂ - Γ ((𝒟₁).a x₁)) < 1 := by
    have hΓa : Γ ((𝒟₁).a x₁) = (𝒟₂).a (H.ψ x₁) := RingHom.congr_fun H.ΩMap_comp_a x₁
    rw [hΓa, ← map_sub, hv₂, valuation_a_lt_one_iff, ← (𝒟₂).ker_b, RingHom.mem_ker, map_sub,
      sub_eq_zero, hx₂]
    have h := RingHom.congr_fun H.b_comp_ψ x₁
    simp only [RingHom.comp_apply] at h
    rw [h, hx₁]
    exact (hκ _).symm
  have hpowcong : ∀ (S T : (𝒟₂).Ω), v₂ S ≤ 1 → v₂ T ≤ 1 → v₂ (S - T) < 1 →
      ∀ k : ℕ, v₂ (S ^ k - T ^ k) < 1 := by
    intro S T hS hT hST k
    induction k with
    | zero => simp
    | succ k ih =>
      have : S ^ (k + 1) - T ^ (k + 1) = S * (S ^ k - T ^ k) + T ^ k * (S - T) := by ring
      rw [this]
      refine lt_of_le_of_lt (v₂.map_add _ _) (max_lt ?_ ?_)
      · rw [map_mul]; exact (mul_le_of_le_one_left zero_le hS).trans_lt ih
      · rw [map_mul, map_pow]
        exact (mul_le_of_le_one_left zero_le (pow_le_one' hT _)).trans_lt hST
  have hres : ∀ z ∈ L₂, v₂ z ≤ 1 → ∀ c : Option (ιw × ℕ) →₀ (𝒟₂).Ω, (∀ j, c j ∈ K) →
      (∀ j, v₂ (c j) ≤ 1) → v₂ (z ^ p - frobeniusComb p w₂ c) < 1 →
        ∀ i : ιw, v₂ (c (some (i, 0))) < 1 := by
    intro z hz hz1 c hcK hc1 hlt i
    by_contra hge
    rw [not_lt] at hge
    obtain ⟨c₁, hc₁, rfl⟩ := hliftc _ c hcK
    simp only [Finsupp.mapRange_apply] at hc1 hge
    have hc₁1 : ∀ j, v₁ (c₁ j) ≤ 1 := fun j ↦ (H.valuation_ΩMap_le_one_iff _).1 (hc1 j)
    have hc₁i : v₁ (c₁ (some (i, 0))) = 1 :=
      (H.valuation_ΩMap_eq_one_iff _).1 (le_antisymm (hc1 _) hge)
    obtain ⟨N, y, hy, hyv⟩ := hpb c₁ hc₁ hc₁1 ⟨i, hc₁i⟩
    rw [hcomb] at hlt
    set S := Γ (frobeniusComb p w c₁) with hSdef
    have h1 : v₂ (Γ ((𝒟₁).a x₁) - ∑ k ∈ Finset.range N, Γ (y k) ^ p * S ^ k) < 1 := by
      have := (H.valuation_ΩMap_lt_one_iff _).2 hyv
      simpa only [map_sub, map_sum, map_mul, map_pow] using this
    have hy1 : ∀ k, v₂ (Γ (y k)) ≤ 1 := fun k ↦ (H.valuation_ΩMap_le_one_iff _).2 (hy k).2
    set Z := ∑ k ∈ Finset.range N, Γ (y k) * z ^ k with hZdef
    have hZL : Z ∈ L₂ :=
      sum_mem fun k _ ↦ mul_mem (H.ΩMap_mem_compositum _ (hy k).1) (pow_mem hz _)
    have hZ1 : v₂ Z ≤ 1 := v₂.map_sum_le fun k _ ↦ by
      rw [map_mul, map_pow]
      exact mul_le_one' (hy1 k) (pow_le_one' hz1 _)
    have hZp : v₂ (Z ^ p - ∑ k ∈ Finset.range N, Γ (y k) ^ p * (z ^ p) ^ k) < 1 := by
      have h := (valuation_sum_pow_sub_sum_pow_le p hp (Finset.range N)
        (fun k ↦ Γ (y k) * z ^ k) (v := v₂) (μ := 1) fun k _ ↦ pow_le_one' (by
          rw [map_mul, map_pow]
          exact mul_le_one' (hy1 k) (pow_le_one' hz1 _)) _).2
      have e : ∑ k ∈ Finset.range N, (Γ (y k) * z ^ k) ^ p =
          ∑ k ∈ Finset.range N, Γ (y k) ^ p * (z ^ p) ^ k :=
        Finset.sum_congr rfl fun k _ ↦ by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k p]
      rw [e, mul_one] at h
      exact h.trans_lt hp1
    have hS1 : v₂ S ≤ 1 := by
      have : S = z ^ p - (z ^ p - S) := by ring
      rw [this]
      exact v₂.map_sub_le (by rw [map_pow]; exact pow_le_one' hz1 _) hlt.le
    have h2 : v₂ (∑ k ∈ Finset.range N, Γ (y k) ^ p * S ^ k -
        ∑ k ∈ Finset.range N, Γ (y k) ^ p * (z ^ p) ^ k) < 1 := by
      rw [← Finset.sum_sub_distrib]
      refine v₂.map_sum_lt one_ne_zero fun k _ ↦ ?_
      rw [← mul_sub, map_mul, map_pow]
      refine (mul_le_of_le_one_left zero_le (pow_le_one' (hy1 k) _)).trans_lt ?_
      refine hpowcong S (z ^ p) hS1 (by rw [map_pow]; exact pow_le_one' hz1 _) ?_ k
      rw [← v₂.map_neg, neg_sub]
      exact hlt
    have h3 : v₂ ((𝒟₂).a x₂ - Z ^ p) < 1 := by
      have : (𝒟₂).a x₂ - Z ^ p = ((𝒟₂).a x₂ - Γ ((𝒟₁).a x₁)) +
          (Γ ((𝒟₁).a x₁) - ∑ k ∈ Finset.range N, Γ (y k) ^ p * S ^ k) +
          (∑ k ∈ Finset.range N, Γ (y k) ^ p * S ^ k -
            ∑ k ∈ Finset.range N, Γ (y k) ^ p * (z ^ p) ^ k) +
          (∑ k ∈ Finset.range N, Γ (y k) ^ p * (z ^ p) ^ k - Z ^ p) := by ring
      rw [this]
      refine lt_of_le_of_lt (v₂.map_add _ _) (max_lt (lt_of_le_of_lt (v₂.map_add _ _)
        (max_lt (lt_of_le_of_lt (v₂.map_add _ _) (max_lt hcoord h1)) h2)) ?_)
      rw [← v₂.map_neg, neg_sub]
      exact hZp
    have h4 := valuation_coord_sub_pow_eq_one ha₂ halg₂ hb₂ p hx₂ hZL hZ1
    rw [h4] at h3
    exact lt_irrefl _ h3
  obtain ⟨θ, hθL, hθ⟩ := exists_pow_eq_of_kummer_of_approx p K L₁ L₂ (Kst.map Γ) (A.map Γ) hp hp1
    hp0 hKL₁ hL hKstK
    hAL₁ hroot hw₂A hw₂1 hA1 hval₂ (v₂ (Γ ϖ)) hγ0 hγ1 hdisc₂ hγN hAapp₂ hAinv₂ hKstA₂
    hKstroot₂ hexp₂ hres hhens ⟨α, hα, rfl⟩ hα₂ (by obtain ⟨θ, hθ, h⟩ := h₂; exact ⟨θ, hθ, h⟩)
  obtain ⟨θ', hθ'L, rfl⟩ := Subfield.mem_map.1 hθL
  exact ⟨θ', hθ'L, Γ.injective (by rw [map_pow, hθ])⟩

end AlgebraicGeometry.SliceTrait.Hom

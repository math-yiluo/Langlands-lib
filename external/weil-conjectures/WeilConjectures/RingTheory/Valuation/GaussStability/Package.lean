/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.FrobeniusLiftApprox
public import WeilConjectures.RingTheory.Valuation.GaussResidue
public import WeilConjectures.FieldTheory.FrobeniusClosedBasisSubfield

/-!
# Lifts of Frobenius-closed bases over a residually transcendental extension

Let `𝒪` be a valuation subring of a field `Ω` with residue characteristic `p`, `K ⊆ Ω` an
algebraically closed subfield, algebraic over a discretely valued subfield `K₀` with the full
residue field `k` of `K` and uniformizer `ϖ`, the value group of `Ω` being of rational rank one
over `v(ϖ)`. Let `x ∈ 𝒪` have residue transcendental over `k`, and `B ⊇ K₀(x)` a discretely
valued subfield algebraic over `K₀(x)` whose residues are separable over `k(x̄)` (for instance
`B = K₀(x)` with the Gauss valuation, or an unramified extension of it).

For every `α` in the compositum `L = K·B`, the approximation package of
`ValuationSubring.exists_frobeniusLift_package` holds
(`ValuationSubring.exists_frobeniusLift_package_of_transcendental`): `α` and `x` lie in a
subfield `D = K₀(x, b₁, …, bₙ) ⊆ B`, finite over `K₀(x)`, whose residue field is a finite separable
extension of `k(x̄)` (by the Gauss valuation, `ValuationSubring.residue_mem_adjoin_of_mem_adjoin`),
hence has a Frobenius-closed `k`-basis (`FrobeniusClosedBasis.exists_of_subfield`).
-/

@[expose] public section

open IsLocalRing IntermediateField

namespace ValuationSubring

universe u

variable {Ω : Type u} [Field Ω] (𝒪 : ValuationSubring Ω)

/-- **Approximation by lifts of a Frobenius-closed basis over `K·B`.** -/
theorem exists_frobeniusLift_package_of_transcendental {p : ℕ} [Fact p.Prime]
    [CharP (ResidueField 𝒪) p] (K K₀ B : Subfield Ω) [IsAlgClosed K] (hK₀K : K₀ ≤ K)
    (hK₀B : K₀ ≤ B) {ϖ : Ω} (hϖ : ϖ ∈ K₀) (hϖ0 : ϖ ≠ 0) (hϖ1 : 𝒪.valuation ϖ < 1)
    (hdisc : ∀ z ∈ B, z ≠ 0 → ∃ m : ℤ, 𝒪.valuation z = 𝒪.valuation ϖ ^ m)
    (harch : ∀ z : Ω, z ≠ 0 →
      ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, 𝒪.valuation z ^ n = 𝒪.valuation ϖ ^ m)
    (halg : ∀ c ∈ K, IsAlgebraic K₀ c)
    (hfull : ∀ y ∈ K, 𝒪.valuation y ≤ 1 → ∃ z ∈ K₀, 𝒪.valuation (y - z) < 1)
    {x : 𝒪} (hxB : (x : Ω) ∈ B)
    (htr : Transcendental (𝒪.residueSubfield K) (residue 𝒪 x))
    (hBalg : ∀ b ∈ B, IsAlgebraic (adjoin K₀ {(x : Ω)}) b)
    (hBsep : ∀ b : 𝒪, (b : Ω) ∈ B →
      IsSeparable (adjoin (𝒪.residueSubfield K) {residue 𝒪 x}) (residue 𝒪 b))
    {α : Ω} (hα : α ∈ Subfield.closure ((K : Set Ω) ∪ B)) :
    ∃ (ι : Type u) (w : ι → Ω) (A : Subring Ω) (Kst : Subfield Ω), Kst ≤ K ∧
      (∀ i, w i ∈ A) ∧
      (∀ y ∈ A, y ∈ Subfield.closure ((K : Set Ω) ∪ B) ∧ 𝒪.valuation y ≤ 1) ∧
      (∀ i, 𝒪.valuation (w i) = 1) ∧
      (∀ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) →
        ∀ j, 𝒪.valuation (c j) ≤ 𝒪.valuation (frobeniusComb p w c)) ∧
      (∀ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) → (∀ j, 𝒪.valuation (c j) ≤ 1) →
        (∃ i, 𝒪.valuation (c (some (i, 0))) = 1) →
        ∃ (N : ℕ) (y : ℕ → Ω), (∀ k, y k ∈ Subfield.closure ((K : Set Ω) ∪ B) ∧
          𝒪.valuation (y k) ≤ 1) ∧
          𝒪.valuation ((x : Ω) - ∑ k ∈ Finset.range N, y k ^ p * frobeniusComb p w c ^ k) < 1) ∧
      (∃ ϖ' ∈ Kst, 0 < 𝒪.valuation ϖ' ∧ 𝒪.valuation ϖ' < 1 ∧
        (∀ c ∈ Kst, c ≠ 0 → ∃ n : ℤ, 𝒪.valuation c = 𝒪.valuation ϖ' ^ n) ∧
        ∀ t : Ω, t ≠ 0 → ∃ N : ℕ, 𝒪.valuation ϖ' ^ N < 𝒪.valuation t) ∧
      (∀ y ∈ A, ∀ t : Ω, t ≠ 0 → ∃ e : Option (ι × ℕ) →₀ Ω, (∀ k, e k ∈ Kst) ∧
        𝒪.valuation (y - frobeniusComb p w e) < 𝒪.valuation t) ∧
      (∀ t : Ω, t ≠ 0 → ∃ e : Option (ι × ℕ) →₀ Ω, (∀ k, e k ∈ Kst) ∧
        𝒪.valuation (α - frobeniusComb p w e) < 𝒪.valuation t) ∧
      (∀ y ∈ Subfield.closure ((K : Set Ω) ∪ A), ∀ t : Ω, t ≠ 0 →
        ∃ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) ∧
          𝒪.valuation (y - frobeniusComb p w c) < 𝒪.valuation t) ∧
      (∀ y ∈ A, 𝒪.valuation y = 1 → y⁻¹ ∈ A) ∧
      (∀ c ∈ Kst, 𝒪.valuation c ≤ 1 → c ∈ A) ∧
      (∀ c ∈ Kst, 𝒪.valuation c ≤ 1 → ∃ d ∈ Kst, 𝒪.valuation (d ^ p - c) < 1) := by
  classical
  set L := Subfield.closure ((K : Set Ω) ∪ B) with hL
  have hKL : K ≤ L := fun c hc ↦ Subfield.subset_closure (Or.inl hc)
  have hBL : B ≤ L := fun c hc ↦ Subfield.subset_closure (Or.inr hc)
  -- the presentation of `α`
  have hKBalg (c : Ω) (hc : c ∈ K) : IsAlgebraic B c := by
    let : Algebra K₀ B := (Subfield.inclusion hK₀B).toAlgebra
    have : IsScalarTower K₀ B Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    exact (halg c hc).tower_top B
  obtain ⟨n, c, b, hcK, hbB, rfl⟩ :=
    Valuation.exists_eq_sum_mul_of_mem_closure (v := 𝒪.valuation)
    hKBalg (hK₀K hϖ) (hK₀B hϖ) hϖ0 hdisc hα
  -- the field `D = K₀(x, bₗ)`
  set F₁ := adjoin K₀ {(x : Ω)} with hF₁
  set D₁ := adjoin F₁ (Set.range b) with hD₁
  have : FiniteDimensional F₁ D₁ := finiteDimensional_adjoin fun y hy ↦ by
    obtain ⟨l, rfl⟩ := hy
    exact (hBalg _ (hbB l).1).isIntegral
  set D : Subfield Ω := D₁.toSubfield with hD
  have hF₁D (c : Ω) (hc : c ∈ F₁) : c ∈ D := IntermediateField.algebraMap_mem D₁ (⟨c, hc⟩ : F₁)
  have hK₀D : K₀ ≤ D := fun c hc ↦ hF₁D c (IntermediateField.algebraMap_mem F₁ (⟨c, hc⟩ : K₀))
  have hxD : (x : Ω) ∈ D := hF₁D _ (mem_adjoin_simple_self K₀ _)
  have hbD (l : Fin n) : b l ∈ D := subset_adjoin F₁ _ ⟨l, rfl⟩
  have hF₁B : F₁ ≤ B.toIntermediateField (fun c : K₀ ↦ hK₀B c.2) := by
    rw [adjoin_le_iff, Set.singleton_subset_iff]
    exact hxB
  have hDB : D ≤ B := by
    have h₂ : D₁ ≤ B.toIntermediateField (fun c : F₁ ↦ hF₁B c.2) := by
      rw [adjoin_le_iff]
      rintro _ ⟨l, rfl⟩
      exact (hbB l).1
    exact h₂
  have hKroot (m : ℕ) (hm : 0 < m) (y : Ω) (hy : y ∈ K) : ∃ z ∈ K, z ^ m = y := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (⟨y, hy⟩ : K) hm
    exact ⟨z, z.2, congrArg Subtype.val hz⟩
  -- the Frobenius-closed basis of the residue field of `D`
  set k := 𝒪.residueSubfield K with hk
  set E := 𝒪.residueSubfield D with hE
  have : IsAlgClosed k := isAlgClosed_residueSubfield K
  have hkE : k ≤ E := by
    rintro _ ⟨y, hyK, rfl⟩
    obtain ⟨z, hzK₀, hz⟩ := hfull y hyK ((𝒪.valuation_le_one_iff _).2 y.2)
    have hz𝒪 : z ∈ 𝒪 := by
      have : z = y - (y - z) := by ring
      rw [← 𝒪.valuation_le_one_iff, this]
      exact 𝒪.valuation.map_sub_le ((𝒪.valuation_le_one_iff _).2 y.2) hz.le
    refine ⟨⟨z, hz𝒪⟩, hK₀D hzK₀, ?_⟩
    rw [eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact (valuation_lt_one_iff 𝒪 _).2 hz
  have hxE : residue 𝒪 x ∈ E := ⟨x, hxD, rfl⟩
  have hfin : ∃ N : ℕ, ∀ (m : ℕ) (e : Fin m → ResidueField 𝒪), (∀ i, e i ∈ E) →
      LinearIndependent (adjoin k {residue 𝒪 x}) e → m ≤ N := by
    refine ⟨Module.finrank F₁ D₁, fun m e heE hli ↦ ?_⟩
    choose d hdD hde using fun i ↦ heE i
    have hA (c : F₁) (h : algebraMap F₁ Ω c ∈ 𝒪) :
        residue 𝒪 ⟨algebraMap F₁ Ω c, h⟩ ∈
          (algebraMap (adjoin k {residue 𝒪 x}) (ResidueField 𝒪)).range :=
      ⟨⟨_, residue_mem_adjoin_of_mem_adjoin (𝒪.residueSubfield_mono hK₀K) htr
        (y := ⟨_, h⟩) c.2⟩, rfl⟩
    have hres := Valuation.ResiduallyIndependent.of_linearIndependent_residue hA d
      (by simpa only [hde] using hli)
    have hd1 (i : Fin m) : 𝒪.valuation (d i : Ω) = 1 := by
      refine (𝒪.valuation_eq_one_iff (d i)).1 ((residue_ne_zero_iff_isUnit _).1 ?_)
      rw [hde]
      exact hli.ne_zero i
    have hlin := hres.linearIndependent hd1
    let d' : Fin m → D₁ := fun i ↦ ⟨d i, hdD i⟩
    have hlin' : LinearIndependent F₁ d' :=
      LinearIndependent.of_comp D₁.val.toLinearMap hlin
    simpa using hlin'.fintype_card_le_finrank
  have hsepE (e : ResidueField 𝒪) (he : e ∈ E) : IsSeparable (adjoin k {residue 𝒪 x}) e := by
    obtain ⟨z, hzD, rfl⟩ := he
    exact hBsep z (hDB hzD)
  obtain ⟨ι, u, hu, hli, hsp, hpth⟩ :=
    FrobeniusClosedBasis.exists_of_subfield p k E hkE hxE htr hfin hsepE
  exact ⟨ι, exists_frobeniusLift_package 𝒪 K K₀ D L hK₀K hK₀D (hDB.trans hBL) hKL hϖ hϖ0 hϖ1
    (fun z hz hz0 ↦ hdisc z (hDB hz) hz0) harch hKroot halg hfull (x := x) hu hli hsp hpth
    ⟨n, c, b, hcK, fun l ↦ ⟨hbD l, (hbB l).2⟩, rfl⟩⟩

end ValuationSubring

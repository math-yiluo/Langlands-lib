/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceGaloisFields
public import WeilConjectures.TraceFormula.Specialization.SliceTraitCoordResidue
public import WeilConjectures.RingTheory.Valuation.DiscreteSubfieldFullResidue
public import WeilConjectures.RingTheory.Valuation.UnramifiedCompositum
public import WeilConjectures.FieldTheory.PowIndependentSeparable

/-!

# Unramified radical subfields of the slice compositum

Let `D` be a slice trait over a strictly henselian trait `R₁ = R` with geometric generic point
`Ω₁ = Ω` and residue characteristic `p`, such that the residue field of `R' = D.R` is separable
algebraic over `κ(x̄)` for an element `x ∈ R'` with residue transcendental over the residue field
`κ` of `R`. Adjoining to `Frac R` compatible `p ^ n`-th roots `θ i n` of lifts of a `p`-basis of
`κ` gives a discretely valued subfield `K₀ ⊆ Ω` with the full residue field
(`IsDiscreteValuationRing.exists_discrete_subfield_full_residue`). We show
(`AlgebraicGeometry.SliceTrait.exists_unramified_subfields`) that the field
`B = Frac(R')(θ i n : i, n) ⊆ Ω'`, which contains `K₀` and `R'`, is still discretely valued with
the value group of `R'`, and that the residues of its integral elements are sums of products of
residues of `R'` and of residues of elements of `Ω`: the `p`-basis of `κ` stays `p`-independent in
the residue field of `R'` (`Field.PowIndependent.map_of_isSeparable`), so that adjoining the
`θ i n` to `Frac R'` is unramified (`ValuationSubring.unramified_adjoin_roots`).

-/

@[expose] public section

universe u

open IsLocalRing IntermediateField

namespace AlgebraicGeometry.SliceTrait

attribute [local instance] algebraR algebraΩ algebraBaseΩ algebraRΩ

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsStrictlyHenselianLocalRing R] {Ω : Type u} [Field Ω] [Algebra R Ω]
  {κ : Type u} [Field κ] {b : R →+* κ} (D : SliceTrait (algebraMap R Ω) b)

attribute [local instance] algebraFracΩ algebraFrac algebraValuationSubring
  algebraBaseValuationSubring FractionRing.liftAlgebra

/-- The valuation of `Ω'` restricts to the valuation of `Ω` attached to `R`. -/
lemma comap_ωS_valuationSubring [FaithfulSMul R Ω] [Algebra.IsAlgebraic R Ω] :
    D.valuationSubring.comap D.ωS =
      IsDiscreteValuationRing.integralClosureValuationSubring R Ω := by
  have := D.isAlgebraic_a
  exact IsDiscreteValuationRing.comap_integralClosureValuationSubring (R := R)

/-- The embedding `Frac R ⟶ Frac R'` is compatible with `Ω ⟶ Ω'`. -/
lemma ωS_comp_algebraMap_fractionRing [FaithfulSMul R Ω] :
    D.ωS.comp (algebraMap (FractionRing R) Ω) =
      (algebraMap (FractionRing D.R) D.Ω).comp (algebraMap (FractionRing R) (FractionRing D.R)) :=
  IsLocalization.ringHom_ext (nonZeroDivisors R) <| RingHom.ext fun r ↦ by
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply, algebraMap_fractionRing_fractionRing_Ω]
    exact RingHom.congr_fun D.ωS_comp r

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- A `p`-independent family of residues of `R` stays `p`-independent in the residue field of
`R'`, if the latter is separable algebraic over `κ(x̄)` with `x̄` transcendental over `κ`. -/
lemma powIndependent_residue_φ (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p] {x : D.R}
    (htr : Transcendental (ResidueField R) (residue D.R x))
    (hsep : ∀ y : ResidueField D.R, IsSeparable (ResidueField R)⟮residue D.R x⟯ y)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ι → R}
    (ht : Field.PowIndependent p fun i ↦ residue R (t i)) :
    Field.PowIndependent p fun i ↦ residue D.R (D.φ (t i)) := by
  have : CharP (ResidueField D.R) p :=
    charP_of_injective_algebraMap (algebraMap (ResidueField R) (ResidueField D.R)).injective p
  exact ht.map_of_isSeparable p htr hsep

/-- **Unramified radical subfields of the compositum.** There are subfields `K₀ ⊆ Ω` (mapped to
`Ω'`) and `B ⊆ Ω'` with `K₀ ⊆ B` and `R' ⊆ B` such that
* `K₀` contains `R` and has the full residue field of `Ω`;
* the nonzero elements of `B` have values in `v(ϖ) ^ ℤ`;
* the residue of every integral element of `B` is a sum of products of residues of elements of
  `R'` and of integral elements of `Ω`. -/
theorem exists_unramified_subfields [FaithfulSMul R Ω] [Algebra.IsAlgebraic R Ω] [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p] {x : D.R}
    (htr : Transcendental (ResidueField R) (residue D.R x))
    (hsep : ∀ y : ResidueField D.R, IsSeparable (ResidueField R)⟮residue D.R x⟯ y)
    {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ K₀ B : Subfield D.Ω, K₀ ≤ D.ωS.fieldRange ∧ K₀ ≤ B ∧ (∀ r, D.a r ∈ B) ∧
      (∀ r : R, D.a (D.φ r) ∈ K₀) ∧
      (∀ y ∈ D.ωS.fieldRange, D.valuationSubring.valuation y ≤ 1 →
        ∃ z ∈ K₀, D.valuationSubring.valuation (y - z) < 1) ∧
      (∀ z ∈ B, z ≠ 0 → ∃ m : ℤ, D.valuationSubring.valuation z =
        D.valuationSubring.valuation (D.a (D.φ ϖ)) ^ m) ∧
      (∀ z : D.valuationSubring, (z : D.Ω) ∈ B → ∃ (n : ℕ) (c : Fin n → D.R)
        (e : Fin n → D.valuationSubring), (∀ j, (e j : D.Ω) ∈ D.ωS.fieldRange) ∧
          residue _ z = ∑ j, residue _ (algebraMap D.R _ (c j)) * residue _ (e j)) := by
  classical
  have := D.isAlgebraic_a
  set 𝒪 := D.valuationSubring with h𝒪
  obtain ⟨ι, t, θ, hθ0, hθs, hind, -, hdir, -, hfullΩ⟩ :=
    IsDiscreteValuationRing.exists_discrete_subfield_full_residue (R := R) (Ω := Ω)
      (FractionRing R) hϖ
  have hpe : ringExpChar (ResidueField R) = p := ringExpChar.eq (ResidueField R) p
  set K₀Ω := adjoin (FractionRing R) (Set.range fun x : ι × ℕ ↦ θ x.1 x.2) with hK₀Ω
  set θ' : ι → ℕ → D.Ω := fun i n ↦ D.ωS (θ i n) with hθ'
  set BI := adjoin (FractionRing D.R) (Set.range fun x : ι × ℕ ↦ θ' x.1 x.2) with hBI
  have hθ's (i : ι) (n : ℕ) : θ' i (n + 1) ^ ringExpChar (ResidueField R) = θ' i n := by
    simp only [hθ', ← map_pow, hθs]
  have hθ'pow (i : ι) (n : ℕ) : θ' i n ^ p ^ n = algebraMap D.R D.Ω (D.φ (t i)) := by
    rw [← hpe]
    simp only [hθ', ← map_pow, IsDiscreteValuationRing.pow_pow_eq_of_succ hθ0 hθs]
    exact RingHom.congr_fun D.ωS_comp (t i)
  have hfrac (c : FractionRing R) : D.ωS (algebraMap (FractionRing R) Ω c) ∈ BI := by
    have h := RingHom.congr_fun (D.ωS_comp_algebraMap_fractionRing) c
    simp only [RingHom.comp_apply] at h
    rw [h]
    exact IntermediateField.algebraMap_mem _ _
  have hK₀B : K₀Ω.toSubfield.map D.ωS ≤ BI.toSubfield := by
    rw [Subfield.map_le_iff_le_comap]
    let C : IntermediateField (FractionRing R) Ω :=
      (BI.toSubfield.comap D.ωS).toIntermediateField fun c ↦ hfrac c
    have : K₀Ω ≤ C := by
      rw [adjoin_le_iff]
      rintro _ ⟨y, rfl⟩
      exact subset_adjoin _ _ ⟨y, rfl⟩
    exact this
  have hO : ∀ y : FractionRing D.R, algebraMap (FractionRing D.R) D.Ω y ∈ 𝒪 ↔
      y ∈ (algebraMap D.R (FractionRing D.R)).range := by
    intro y
    refine ⟨fun hy ↦ ?_, ?_⟩
    · obtain ⟨s, hs⟩ := D.exists_algebraMap_eq_of_mem_fracValuationSubring hy
      exact ⟨s, hs⟩
    · rintro ⟨s, rfl⟩
      rw [algebraMap_fractionRing_Ω]
      exact D.a_mem_valuationSubring s
  have hωS𝒪 {y : Ω} (hy : y ∈ IsDiscreteValuationRing.integralClosureValuationSubring R Ω) :
      D.ωS y ∈ 𝒪 := by
    rw [← D.comap_ωS_valuationSubring] at hy
    exact hy
  have : CharP (ResidueField D.R) p :=
    charP_of_injective_algebraMap (algebraMap (ResidueField R) (ResidueField D.R)).injective p
  have : CharP (ResidueField 𝒪) p :=
    charP_of_injective_algebraMap (algebraMap (ResidueField D.R) (ResidueField 𝒪)).injective p
  have hun (s : Finset ι) (n : ℕ) := ValuationSubring.unramified_adjoin_roots 𝒪 (R := D.R)
    (F := FractionRing D.R) (p := p) (t := fun i : s ↦ D.φ (t i)) (θ := fun i : s ↦ θ' i n)
    (n := n) hO (fun i ↦ (t i).isUnit.map _)
    (D.powIndependent_residue_φ p htr hsep (by simpa only [hpe] using hind s))
    (fun i ↦ hθ'pow i n)
  have hdirB (z : D.Ω) (hz : z ∈ BI) :
      ∃ (s : Finset ι) (n : ℕ), z ∈ adjoin (FractionRing D.R) (Set.range fun i : s ↦ θ' i n) :=
    IsDiscreteValuationRing.exists_mem_adjoin_roots (R := R) hθ's hz
  refine ⟨K₀Ω.toSubfield.map D.ωS, BI.toSubfield, ?_, hK₀B, fun r ↦ ?_, fun r ↦ ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  · rw [← algebraMap_fractionRing_Ω]
    exact IntermediateField.algebraMap_mem _ _
  · refine ⟨algebraMap R Ω r, ?_, RingHom.congr_fun D.ωS_comp r⟩
    rw [IsScalarTower.algebraMap_apply R (FractionRing R) Ω]
    exact IntermediateField.algebraMap_mem _ _
  · rintro _ ⟨y, rfl⟩ hy
    have hy' : y ∈ IsDiscreteValuationRing.integralClosureValuationSubring R Ω := by
      rw [← D.comap_ωS_valuationSubring]
      exact (𝒪.valuation_le_one_iff _).1 hy
    obtain ⟨z, hzK, -, hz⟩ := hfullΩ y hy'
    refine ⟨D.ωS z, ⟨z, hzK, rfl⟩, ?_⟩
    rw [← map_sub, ← ValuationSubring.valuation_comap_lt_one_iff, D.comap_ωS_valuationSubring]
    exact hz
  · intro z hz hz0
    obtain ⟨s, n, hzs⟩ := hdirB z hz
    obtain ⟨c, hc⟩ := (hun s n).2.1 z hzs
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero, map_zero, Valuation.zero_iff] at hc
      exact hz0 hc
    obtain ⟨m, hm⟩ := IsDiscreteValuationRing.exists_valuation_algebraMap_eq_zpow (R := D.R)
      (Ω := D.Ω) (K := FractionRing D.R) (D.irreducible_φ hϖ) hc0
    exact ⟨m, hc.trans hm⟩
  · intro z hz
    obtain ⟨s, n, hzs⟩ := hdirB z hz
    obtain ⟨c, hcz, hcv⟩ := (hun s n).2.2.2 z hzs
    have hc (E : s → Fin (p ^ n)) : ∃ r : D.R, algebraMap D.R (FractionRing D.R) r = c E :=
      (hO (c E)).1 ((𝒪.valuation_le_one_iff _).1 ((hcv E).trans
        ((𝒪.valuation_le_one_iff _).2 z.2)))
    choose r hr using hc
    have hθ𝒪 (i : ι) (n : ℕ) : θ' i n ∈ 𝒪 := hωS𝒪 (IsDiscreteValuationRing.root_mem hθ0 hθs i n)
    let e := Fintype.equivFin (s → Fin (p ^ n))
    let mon (E : s → Fin (p ^ n)) : 𝒪 := ∏ i : s, ⟨θ' i n, hθ𝒪 i n⟩ ^ (E i : ℕ)
    refine ⟨Fintype.card (s → Fin (p ^ n)), fun j ↦ r (e.symm j), fun j ↦ mon (e.symm j),
      fun j ↦ ?_, ?_⟩
    · refine ⟨∏ i : s, θ i n ^ (e.symm j i : ℕ), ?_⟩
      simp only [mon, map_prod, map_pow, SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow]
      rfl
    · have hz' : z = ∑ E, algebraMap D.R 𝒪 (r E) * mon E := by
        refine Subtype.ext ?_
        rw [hcz]
        simp only [AddSubmonoidClass.coe_finsetSum, mon]
        refine Finset.sum_congr rfl fun E _ ↦ ?_
        rw [Algebra.smul_def, ← hr, algebraMap_fractionRing_Ω]
        push_cast
        rfl
      rw [hz', map_sum, ← e.symm.sum_comp]
      simp only [map_mul]
      rfl

end AlgebraicGeometry.SliceTrait

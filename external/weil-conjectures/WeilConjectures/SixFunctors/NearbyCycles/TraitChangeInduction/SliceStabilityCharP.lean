/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceGaloisFields
public import WeilConjectures.TraceFormula.Specialization.SliceTraitValuation
public import WeilConjectures.RingTheory.Valuation.ArtinSchreierNormalForm
public import WeilConjectures.RingTheory.Valuation.GaloisResidueRoot
public import WeilConjectures.TraceFormula.Specialization.SliceTraitAlgebraic
public import WeilConjectures.TraceFormula.Specialization.SliceTraitCoordResidue
public import WeilConjectures.RingTheory.DiscreteValuationRing.CompletionStrictlyHenselian
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceFrobeniusLift

/-!

# Relative separable closedness of the slice composita, equal characteristic

Let `D₁ ⟶ D₂` be a morphism of strict-localization slice traits over a change of traits
`R₁ ⟶ R₂`, with composita `Lᵢ = Ωᵢ(Sᵢ(x))`. In characteristic `p > 0`, an Artin–Schreier
equation over `L₁` which has a root in `L₂` has a root in `L₁`
(`SliceTrait.Hom.exists_artinSchreier_root_of_charP`). This is the stability theorem of Ohm and
Kuhlmann for `L₁ = Ω₁(x)^{sh}` in the case needed (F.-V. Kuhlmann, *Elimination of
ramification I*, Trans. AMS 362 (2010), Prop. 4.14), via the abstract normal form
`exists_artinSchreier_root_of_approx`.

The inputs are:
* the approximation of the elements of `L₁` by combinations of lifts of a Frobenius-closed basis
  of a residue function field (`SliceTrait.exists_frobeniusLift_approx`);
* the residue `x̄` of the coordinate is not a `p`-th power in the residue field of `L₂`
  (`SliceTrait.valuation_coord_sub_pow_eq_one`);
* Hensel's lemma for Artin–Schreier equations over `L₁` (`SliceTrait.exists_artinSchreier_root`).

-/

@[expose] public section

universe u

open IsLocalRing IntermediateField

namespace AlgebraicGeometry.SliceTrait

attribute [local instance] algebraR algebraΩ algebraBaseΩ algebraRΩ

section StrictLocalization

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsStrictlyHenselianLocalRing R] {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {a : R →+* Ω}
  (ha : Function.Injective a) (halg : letI := a.toAlgebra; Algebra.IsAlgebraic R Ω)
  {κ : Type u} [Field κ] [IsSepClosed κ] {b : R →+* κ} (hb : RingHom.ker b = maximalIdeal R)

local notation "𝒟" => sliceTraitOfStrictLocalization (a₁ := a) (b₁ := b) ha halg hb

omit [IsAlgClosed Ω] in
include ha halg hb in
/-- **The residue of the coordinate is not a `p`-th power** in the residue field of the
compositum `L = Ω(S(x))`, `p` the residual characteristic. This reduces to the case of a complete
`R` (`valuation_a_sub_pow_eq_one_of_complete`) along the morphism of slice traits induced by the
completion `R ⟶ R̂`. -/
theorem valuation_coord_sub_pow_eq_one (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    {x : (𝒟).R} (hx : (𝒟).b x = traitSliceCoord κ) {z : (𝒟).Ω}
    (hz : letI := a.toAlgebra; z ∈ (𝒟).compositum)
    (hz1 : (𝒟).valuationSubring.valuation z ≤ 1) :
    (𝒟).valuationSubring.valuation ((𝒟).a x - z ^ p) = 1 := by
  obtain ⟨b₂, hb₂, rfl⟩ : ∃ (b₂ : IsDiscreteValuationRing.completion R →+* κ)
      (_ : RingHom.ker b₂ = maximalIdeal (IsDiscreteValuationRing.completion R)),
        b₂.comp (IsDiscreteValuationRing.toCompletion R) = b :=
    ⟨IsDiscreteValuationRing.completionLift R b hb,
      IsDiscreteValuationRing.ker_completionLift R b hb,
      IsDiscreteValuationRing.completionLift_comp R b hb⟩
  have : IsLocalHom (IsDiscreteValuationRing.toCompletion R) := ⟨fun r hr ↦ by
    by_contra hnu
    have : IsDiscreteValuationRing.toCompletion R r ∈
        maximalIdeal (IsDiscreteValuationRing.completion R) := by
      rw [IsDiscreteValuationRing.maximalIdeal_completion]
      exact Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal r).2 hnu)
    exact (IsLocalRing.mem_maximalIdeal _).1 this hr⟩
  have : CharP (ResidueField (IsDiscreteValuationRing.completion R)) p :=
    charP_of_injective_ringHom
      (ResidueField.map (IsDiscreteValuationRing.toCompletion R)).injective p
  obtain ⟨Ω₂, _, _, a₂, ha₂, halg₂, c, hc⟩ : ∃ (Ω₂ : Type u) (_ : Field Ω₂) (_ : IsAlgClosed Ω₂)
      (a₂ : IsDiscreteValuationRing.completion R →+* Ω₂) (_ : Function.Injective a₂)
      (_ : letI := a₂.toAlgebra; Algebra.IsAlgebraic (IsDiscreteValuationRing.completion R) Ω₂)
      (c : Ω →+* Ω₂), c.comp a = a₂.comp (IsDiscreteValuationRing.toCompletion R) := by
    obtain ⟨c, hc⟩ := exists_comp_eq_algebraMap_algebraicClosure_fractionRing
      (IsDiscreteValuationRing.completion R) a ha halg (IsDiscreteValuationRing.toCompletion R)
      (IsDiscreteValuationRing.injective_toCompletion R)
    exact ⟨_, _, inferInstance, _,
      injective_algebraMap_algebraicClosure_fractionRing (IsDiscreteValuationRing.completion R),
      isAlgebraic_algebraicClosure_fractionRing (IsDiscreteValuationRing.completion R), c, hc⟩
  let H := sliceTraitOfStrictLocalizationHom (IsDiscreteValuationRing.toCompletion R)
    (IsDiscreteValuationRing.injective_toCompletion R) c ha halg ha₂ halg₂ hc hb₂
  have hψ : (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂).b (H.ψ x) =
      traitSliceCoord κ := by
    have h := RingHom.congr_fun H.b_comp_ψ x
    simp only [RingHom.comp_apply] at h
    rw [h, hx]
    rfl
  let := a.toAlgebra
  let := a₂.toAlgebra
  have h := valuation_a_sub_pow_eq_one_of_complete ha₂ halg₂ hb₂ p hψ (H.ΩMap_mem_compositum z hz)
    ((H.valuation_ΩMap_le_one_iff z).2 hz1)
  rw [← H.valuation_ΩMap_eq_one_iff, map_sub, map_pow]
  rwa [← RingHom.comp_apply, H.ΩMap_comp_a, RingHom.comp_apply]

end StrictLocalization

section General

variable {R : Type u} [CommRing R] [IsLocalRing R] {Ω : Type u} [Field Ω] [Algebra R Ω]
  {κ : Type u} [Field κ] {b : R →+* κ} (D : SliceTrait (algebraMap R Ω) b)

/-- **Hensel's lemma for Artin–Schreier equations over the compositum.** -/
theorem exists_artinSchreier_root (p : ℕ) [Fact p.Prime] [CharP Ω p] {β : D.Ω}
    (hβ : β ∈ D.compositum) (hβ1 : D.valuationSubring.valuation β ≤ 1) :
    ∃ θ ∈ D.compositum, θ ^ p - θ = β := by
  classical
  set 𝒪 := D.valuationSubring with h𝒪
  set N : Subfield D.Ω := D.compositum.toSubfield with hN
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have : CharP D.Ω p := charP_of_injective_ringHom D.ωS.injective p
  have : CharP D.R p := D.a.charP D.injective_a p
  -- the residue fields
  have haO : ∀ r : D.R, D.a r ∈ 𝒪 := D.a_mem_valuationSubring
  let ρ : D.R →+* 𝒪 := D.a.codRestrict 𝒪.toSubring haO
  have : IsLocalHom ρ := ⟨fun r hr ↦ by
    by_contra hnu
    have : 𝒪.valuation (D.a r) < 1 := (D.valuation_a_lt_one_iff).2
      ((IsLocalRing.mem_maximalIdeal r).2 hnu)
    exact (IsLocalRing.mem_maximalIdeal _).1
      ((ValuationSubring.valuation_lt_one_iff 𝒪 ⟨_, haO r⟩).2 this) hr⟩
  let : Algebra (ResidueField D.R) (ResidueField 𝒪) := (ResidueField.map ρ).toAlgebra
  -- the residue field of `𝒪` is purely inseparable over that of `R'`
  have hint : ∀ y : 𝒪, _root_.IsIntegral (ResidueField D.R) (residue 𝒪 y) := by
    intro y
    obtain ⟨f, hfm, hfy⟩ : _root_.IsIntegral D.R (y : D.Ω) := y.2
    refine ⟨f.map (residue D.R), hfm.map _, ?_⟩
    have h0 : Polynomial.eval₂ ρ y f = 0 := Subtype.ext (by
      simp only [ZeroMemClass.coe_zero]
      rw [← hfy, Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range]
      simp [ρ]
      rfl)
    rw [Polynomial.eval₂_map]
    have : (algebraMap (ResidueField D.R) (ResidueField 𝒪)).comp (residue D.R) =
        (residue 𝒪).comp ρ := ResidueField.map_comp_residue ρ
    rw [this, ← Polynomial.hom_eval₂, h0, map_zero]
  have : CharP (ResidueField D.R) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2
    (by rw [← map_natCast (residue D.R), CharP.cast_eq_zero, map_zero])
  have : Algebra.IsAlgebraic (ResidueField D.R) (ResidueField 𝒪) := ⟨fun z ↦ by
    obtain ⟨y, rfl⟩ := residue_surjective z
    exact (hint y).isAlgebraic⟩
  have := Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed (F := ResidueField D.R)
    (E := ResidueField 𝒪)
  have hβO : β ∈ 𝒪 := (ValuationSubring.valuation_le_one_iff 𝒪 β).1 hβ1
  obtain ⟨k, rr, hrr⟩ := IsPurelyInseparable.pow_mem (ResidueField D.R) p
    (residue 𝒪 ⟨β, hβO⟩)
  obtain ⟨r, rfl⟩ := residue_surjective rr
  have hr : 𝒪.valuation (D.a r - β ^ p ^ k) < 1 := by
    have h1 : residue 𝒪 (ρ r) = residue 𝒪 (⟨β, hβO⟩ ^ p ^ k) := by
      rw [map_pow, ← hrr]
      rfl
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at h1
    exact (ValuationSubring.valuation_lt_one_iff 𝒪 _).1 h1
  -- an Artin–Schreier root in the separably closed residue field of `R'`
  have hder : ∀ e : ResidueField D.R, Polynomial.derivative
      (Polynomial.X ^ p - Polynomial.X - Polynomial.C e) = -1 := fun e ↦ by
    simp [Polynomial.derivative_X_pow, CharP.cast_eq_zero]
  have hdeg : (Polynomial.X ^ p - Polynomial.X -
      Polynomial.C (residue D.R r)).degree ≠ 0 := by
    have h1 : (Polynomial.X : Polynomial (ResidueField D.R)).degree <
        (Polynomial.X ^ p : Polynomial (ResidueField D.R)).degree := by
      rw [Polynomial.degree_X, Polynomial.degree_X_pow]
      exact_mod_cast (Fact.out : p.Prime).one_lt
    rw [Polynomial.degree_sub_C (by
      rw [Polynomial.degree_sub_eq_left_of_degree_lt h1, Polynomial.degree_X_pow]
      exact_mod_cast Nat.pos_of_ne_zero hp0),
      Polynomial.degree_sub_eq_left_of_degree_lt h1, Polynomial.degree_X_pow]
    exact_mod_cast hp0
  obtain ⟨sr, hsr⟩ := IsSepClosed.exists_root _ hdeg (by
    rw [Polynomial.Separable, hder]
    exact isCoprime_one_right.neg_right)
  obtain ⟨s, rfl⟩ := residue_surjective sr
  have hs : 𝒪.valuation (D.a s ^ p - D.a s - D.a r) < 1 := by
    rw [← map_pow, ← map_sub, ← map_sub, D.valuation_a_lt_one_iff,
      ← IsLocalRing.residue_eq_zero_iff]
    simpa [Polynomial.IsRoot] using hsr
  -- the residual root `n` in `L`
  have hmemR : ∀ r : D.R, D.a r ∈ D.compositum := fun r ↦
    IntermediateField.subset_adjoin _ _ ⟨r, rfl⟩
  set n := D.a s - ∑ m ∈ Finset.range k, β ^ p ^ m with hndef
  have hnN : n ∈ N := sub_mem (hmemR s) (sum_mem fun m _ ↦ pow_mem hβ _)
  have hn𝒪 : n ∈ 𝒪 := sub_mem (haO s) (sum_mem fun m _ ↦ pow_mem hβO _)
  have hn : 𝒪.valuation (n ^ p - n - β) < 1 := by
    have htel := pow_prime_pow_sub_eq_sum p β k
    rw [Finset.sum_sub_distrib] at htel
    have : n ^ p - n - β = (D.a s ^ p - D.a s - D.a r) + (D.a r - β ^ p ^ k) := by
      rw [hndef, sub_pow_char, sum_pow_char]
      linear_combination htel
    rw [this]
    exact lt_of_le_of_lt (𝒪.valuation.map_add _ _) (max_lt hs hr)
  -- the Galois–residue lemma
  have : Algebra.IsAlgebraic N D.Ω := by
    refine ⟨fun z ↦ ?_⟩
    have hz := (D.isAlgebraic_a).isAlgebraic z
    let ι' : D.R →+* N := D.a.codRestrict N.toSubring fun r ↦ hmemR r
    let : Algebra D.R N := ι'.toAlgebra
    have : IsScalarTower D.R N D.Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    exact hz.extendScalars (S := N) (fun x y h ↦ D.injective_a (congrArg Subtype.val h))
  have h𝒪 : ∀ σ : D.Ω ≃ₐ[N] D.Ω, ∀ y ∈ 𝒪, σ y ∈ 𝒪 := fun σ y hy ↦
    (D.map_mem_valuationSubring_iff σ.toRingEquiv
      (fun r ↦ σ.commutes ⟨D.a r, hmemR r⟩)).2 hy
  exact ValuationSubring.exists_pow_sub_self_eq 𝒪 N h𝒪 p hβ hβO hnN hn𝒪 hn

end General

section StrictLocalization

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsStrictlyHenselianLocalRing R] {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {a : R →+* Ω}
  (ha : Function.Injective a) (halg : letI := a.toAlgebra; Algebra.IsAlgebraic R Ω)
  {κ : Type u} [Field κ] [IsSepClosed κ] {b : R →+* κ} (hb : RingHom.ker b = maximalIdeal R)

local notation "𝒟" => sliceTraitOfStrictLocalization (a₁ := a) (b₁ := b) ha halg hb

omit [IsSepClosed κ] in
include ha halg hb in
/-- **Approximation by lifts of a Frobenius-closed basis**, equal characteristic. Every element
`α` of the compositum is approximated, up to an element of value `≤ 1`, by a combination of
`p`-power monomials `w i ^ p ^ n` in elements `w i` of the compositum with coefficients in `Ω`;
the `w i` are valuation independent over `Ω` and their residues are linearly independent
non-`p`-th powers generating, with the residue of the coordinate, a residue function field. -/
theorem exists_frobeniusLift_approx (p : ℕ) [Fact p.Prime] [CharP Ω p] {x : (𝒟).R}
    (hx : (𝒟).b x = traitSliceCoord κ) {α : (𝒟).Ω} (hα : letI := a.toAlgebra; α ∈ (𝒟).compositum) :
    letI := a.toAlgebra
    ∃ (ι : Type u) (w : ι → (𝒟).Ω),
      (∀ i, w i ∈ (𝒟).compositum) ∧ (∀ i, (𝒟).valuationSubring.valuation (w i) = 1) ∧
      (∀ (s : Finset ι) (c : ι → (𝒟).Ω), (∀ i ∈ s, c i ∈ (𝒟).ωS.fieldRange) →
        ∀ i ∈ s, (𝒟).valuationSubring.valuation (c i) ≤
          (𝒟).valuationSubring.valuation (∑ j ∈ s, c j * w j)) ∧
      (∀ (s : Finset ι) (c : ι → (𝒟).Ω), (∀ i ∈ s, c i ∈ (𝒟).ωS.fieldRange) →
        (∀ i ∈ s, (𝒟).valuationSubring.valuation (c i) ≤ 1) →
        (∃ i ∈ s, (𝒟).valuationSubring.valuation (c i) = 1) →
        ∃ (N : ℕ) (y : ℕ → (𝒟).Ω), (∀ k, y k ∈ (𝒟).compositum ∧
          (𝒟).valuationSubring.valuation (y k) ≤ 1) ∧
          (𝒟).valuationSubring.valuation ((𝒟).a x -
            ∑ k ∈ Finset.range N, y k ^ p * (∑ i ∈ s, c i * w i) ^ k) < 1) ∧
      ∃ (s : Finset (ι × ℕ)) (d : ι × ℕ → (𝒟).Ω) (d₀ : (𝒟).Ω),
        (∀ j ∈ s, d j ∈ (𝒟).ωS.fieldRange) ∧ d₀ ∈ (𝒟).ωS.fieldRange ∧
        (𝒟).valuationSubring.valuation (α - d₀ - ∑ j ∈ s, d j * w j.1 ^ p ^ j.2) ≤ 1 := by
  classical
  let := a.toAlgebra
  have : CharP R p := ⟨fun n ↦ by
    rw [← map_eq_zero_iff a ha, map_natCast, CharP.cast_eq_zero_iff Ω p]⟩
  have : CharP (ResidueField R) p :=
    CharP.of_ringHom_of_ne_zero (residue R) p (Fact.out : p.Prime).ne_zero
  obtain ⟨ι, w, A, Kst, hKst, hwA, hA, hw1, hval, hpb, -, -, hP6, -⟩ :=
    exists_frobeniusLift_package ha halg hb p hx hα
  refine ⟨ι, w, fun i ↦ (hA _ (hwA i)).1, hw1, fun s c hc i hi ↦ ?_, fun s c hc hc1 hci ↦ ?_, ?_⟩
  · have h := hval (∑ j ∈ s, Finsupp.single (some (j, 0)) (c j))
      (sum_single_some_mem _ s hc) (some (i, 0))
    rwa [sum_single_some_apply s c hi, frobeniusComb_sum_single] at h
  · obtain ⟨i, hi, hci⟩ := hci
    obtain ⟨N, y, hy, hyv⟩ := hpb (∑ j ∈ s, Finsupp.single (some (j, 0)) (c j))
      (sum_single_some_mem _ s hc) (fun j ↦ by
        rw [Finsupp.finsetSum_apply]
        refine (𝒟).valuationSubring.valuation.map_sum_le fun j' hj' ↦ ?_
        rw [Finsupp.single_apply]
        split_ifs
        exacts [hc1 j' hj', by rw [map_zero]; exact zero_le])
      ⟨i, by rwa [sum_single_some_apply s c hi]⟩
    rw [frobeniusComb_sum_single] at hyv
    exact ⟨N, y, hy, hyv⟩
  · obtain ⟨e, he, hev⟩ := hP6 1 one_ne_zero
    refine ⟨e.some.support, e.some, e none, fun j _ ↦ hKst (he _), hKst (he _), ?_⟩
    rw [map_one] at hev
    have h : α - e none - ∑ j ∈ e.some.support, e.some j * w j.1 ^ p ^ j.2 =
        α - frobeniusComb p w e := by
      rw [frobeniusComb_eq, liftedSum, Finsupp.sum]
      ring
    rw [h]
    exact hev.le

omit [IsAlgClosed Ω] [IsSepClosed κ] in
include ha halg hb in
/-- The strict-localization slice trait has a coordinate: an element of `R'` evaluating to the
coordinate `x` of `κ(x)^alg`. -/
theorem exists_b_eq_traitSliceCoord : ∃ x : (𝒟).R, (𝒟).b x = traitSliceCoord κ :=
  let ⟨g, _, hg, _⟩ := exists_coord_isAlgebraic_strictHenselization_sliceTraitPoint b hb
  ⟨g (MvPolynomial.X ⟨0⟩), hg⟩

end StrictLocalization

end AlgebraicGeometry.SliceTrait

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
/-- **Artin–Schreier equations over the slice composita, equal characteristic.** For a morphism
`H : D₁ ⟶ D₂` of strict-localization slice traits which is the identity on the fields
`κ(x)^alg` of the closed points, an element `α` of `L₁ = Ω₁(S₁(x))` such that `℘ θ = H α`
has a root `θ ∈ L₂` satisfies `℘ θ = α` for some `θ ∈ L₁`. -/
theorem exists_artinSchreier_root_of_charP (p : ℕ) [Fact p.Prime] [CharP Ω₁ p]
    [CharP (ResidueField R₂) p] (H : SliceTrait.Hom ι c 𝒟₁ 𝒟₂)
    (hκ : ∀ y, H.κMap y = y) {α : (𝒟₁).Ω} (hα : letI := a₁.toAlgebra; α ∈ (𝒟₁).compositum)
    (h₂ : letI := a₂.toAlgebra; ∃ θ ∈ (𝒟₂).compositum, θ ^ p - θ = H.ΩMap α) :
    letI := a₁.toAlgebra
    ∃ θ ∈ (𝒟₁).compositum, θ ^ p - θ = α := by
  classical
  let := a₁.toAlgebra
  let := a₂.toAlgebra
  set Γ := H.ΩMap with hΓ
  set v₁ := (𝒟₁).valuationSubring.valuation with hv₁
  set v₂ := (𝒟₂).valuationSubring.valuation with hv₂
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have : CharP (𝒟₁).Ω p := charP_of_injective_ringHom (𝒟₁).ωS.injective p
  have : CharP (𝒟₂).Ω p := charP_of_injective_ringHom Γ.injective p
  obtain ⟨x₁, hx₁⟩ := exists_b_eq_traitSliceCoord ha₁ halg₁ hb₁
  obtain ⟨x₂, hx₂⟩ := exists_b_eq_traitSliceCoord ha₂ halg₂ hb₂
  obtain ⟨ιw, w, hwL, hw1, hval, hpb, s, d, d₀, hd, hd₀, happ⟩ :=
    exists_frobeniusLift_approx ha₁ halg₁ hb₁ p hx₁ hα
  -- the subfields of `(𝒟₂).Ω`
  set K : Subfield (𝒟₂).Ω := (𝒟₁).ωS.fieldRange.map Γ with hKdef
  set L₁ : Subfield (𝒟₂).Ω := (𝒟₁).compositum.toSubfield.map Γ with hL₁def
  set L₂ : Subfield (𝒟₂).Ω := (𝒟₂).compositum.toSubfield with hL₂def
  -- lifting families along `Γ`
  have hlift : ∀ {S : Subfield (𝒟₁).Ω} (s' : Finset ιw) (f : ιw → (𝒟₂).Ω),
      (∀ i ∈ s', f i ∈ S.map Γ) → ∃ g : ιw → (𝒟₁).Ω, ∀ i ∈ s', g i ∈ S ∧ Γ (g i) = f i := by
    intro S s' f hf
    refine ⟨fun i ↦ if h : f i ∈ S.map Γ then (Subfield.mem_map.1 h).choose else 0, fun i hi ↦ ?_⟩
    simp only [dite_eq_left (hf i hi)]
    exact (Subfield.mem_map.1 (hf i hi)).choose_spec
  have hcoord : v₂ ((𝒟₂).a x₂ - Γ ((𝒟₁).a x₁)) < 1 := by
    have hΓa : Γ ((𝒟₁).a x₁) = (𝒟₂).a (H.ψ x₁) := RingHom.congr_fun H.ΩMap_comp_a x₁
    rw [hΓa, ← map_sub, hv₂, valuation_a_lt_one_iff, ← (𝒟₂).ker_b, RingHom.mem_ker, map_sub,
      sub_eq_zero, hx₂]
    have h := RingHom.congr_fun H.b_comp_ψ x₁
    simp only [RingHom.comp_apply] at h
    rw [h, hx₁]
    exact (hκ _).symm
  -- `p`-th powers and Artin–Schreier roots of constants
  have hroot : ∀ y ∈ K, ∃ e ∈ K, e ^ p = y := by
    rintro _ ⟨_, ⟨ω, rfl⟩, rfl⟩
    obtain ⟨ω', hω'⟩ := IsAlgClosed.exists_pow_nat_eq ω (Nat.pos_of_ne_zero hp0)
    exact ⟨Γ ((𝒟₁).ωS ω'), ⟨_, ⟨ω', rfl⟩, rfl⟩, by rw [← map_pow, ← map_pow, hω']⟩
  have hAS : ∀ y ∈ K, ∃ e ∈ K, e ^ p - e = y := by
    rintro _ ⟨_, ⟨ω, rfl⟩, rfl⟩
    obtain ⟨ω', hω'⟩ := IsAlgClosed.exists_root (Polynomial.X ^ p - Polynomial.X -
      Polynomial.C ω) (by
        rw [Polynomial.degree_sub_C (by
          rw [Polynomial.degree_sub_eq_left_of_degree_lt (by
            rw [Polynomial.degree_X, Polynomial.degree_X_pow]; exact_mod_cast
              (Fact.out : p.Prime).one_lt)]
          rw [Polynomial.degree_X_pow]; exact_mod_cast Nat.pos_of_ne_zero hp0),
          Polynomial.degree_sub_eq_left_of_degree_lt (by
            rw [Polynomial.degree_X, Polynomial.degree_X_pow]; exact_mod_cast
              (Fact.out : p.Prime).one_lt), Polynomial.degree_X_pow]
        exact_mod_cast hp0)
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, sub_eq_zero] at hω'
    exact ⟨Γ ((𝒟₁).ωS ω'), ⟨_, ⟨ω', rfl⟩, rfl⟩, by
      rw [← map_pow, ← map_sub, ← map_pow, ← map_sub, hω']⟩
  have hval' : ∀ (s' : Finset ιw) (c' : ιw → (𝒟₂).Ω), (∀ i ∈ s', c' i ∈ K) →
      ∀ i ∈ s', v₂ (c' i) ≤ v₂ (∑ j ∈ s', c' j * Γ (w j)) := by
    intro s' c' hc' i hi
    obtain ⟨g, hg⟩ := hlift s' c' hc'
    have hsum : ∑ j ∈ s', c' j * Γ (w j) = Γ (∑ j ∈ s', g j * w j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j hj ↦ by rw [map_mul, (hg j hj).2]
    rw [hsum, ← (hg i hi).2]
    exact (H.valuation_ΩMap_le_iff _ _).2 (hval s' g (fun j hj ↦ (hg j hj).1) i hi)
  have hhens' : ∀ β ∈ L₁, v₂ β ≤ 1 → ∃ θ ∈ L₁, θ ^ p - θ = β := by
    rintro _ ⟨β, hβ, rfl⟩ hβ1
    obtain ⟨θ, hθ, hθe⟩ := exists_artinSchreier_root _ p hβ
      ((H.valuation_ΩMap_le_one_iff _).1 hβ1)
    exact ⟨Γ θ, ⟨θ, hθ, rfl⟩, by rw [← map_pow, ← map_sub, hθe]⟩
  -- powers of congruent elements are congruent
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
  have hres' : ∀ z ∈ L₂, v₂ z ≤ 1 → ∀ (s' : Finset ιw) (c' : ιw → (𝒟₂).Ω), (∀ i ∈ s', c' i ∈ K) →
      (∀ i ∈ s', v₂ (c' i) ≤ 1) → v₂ (z ^ p - ∑ i ∈ s', c' i * Γ (w i)) < 1 →
        ∀ i ∈ s', v₂ (c' i) < 1 := by
    intro z hz hz1 s' c' hc'K hc'1 hlt i hi
    by_contra hge
    rw [not_lt] at hge
    obtain ⟨g, hg⟩ := hlift s' c' hc'K
    have hg1 : ∀ j ∈ s', v₁ (g j) ≤ 1 := fun j hj ↦
      (H.valuation_ΩMap_le_one_iff _).1 ((hg j hj).2 ▸ hc'1 j hj)
    have hgi : v₁ (g i) = 1 := (H.valuation_ΩMap_eq_one_iff _).1
      ((hg i hi).2 ▸ le_antisymm (hc'1 i hi) hge)
    obtain ⟨N, y, hy, hyv⟩ := hpb s' g (fun j hj ↦ (hg j hj).1) hg1 ⟨i, hi, hgi⟩
    set S := ∑ j ∈ s', c' j * Γ (w j) with hSdef
    have hSΓ : S = Γ (∑ j ∈ s', g j * w j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j hj ↦ by rw [map_mul, (hg j hj).2]
    have h1 : v₂ (Γ ((𝒟₁).a x₁) - ∑ k ∈ Finset.range N, Γ (y k) ^ p * S ^ k) < 1 := by
      rw [hSΓ]
      have := (H.valuation_ΩMap_lt_one_iff _).2 hyv
      simpa only [map_sub, map_sum, map_mul, map_pow] using this
    set Z := ∑ k ∈ Finset.range N, Γ (y k) * z ^ k with hZdef
    have hZL : Z ∈ L₂ := sum_mem fun k _ ↦ mul_mem (H.ΩMap_mem_compositum _ (hy k).1) (pow_mem hz _)
    have hZ1 : v₂ Z ≤ 1 := v₂.map_sum_le fun k _ ↦ by
      rw [map_mul, map_pow]
      exact mul_le_one' ((H.valuation_ΩMap_le_one_iff _).2 (hy k).2) (pow_le_one' hz1 _)
    have hZp : Z ^ p = ∑ k ∈ Finset.range N, Γ (y k) ^ p * (z ^ p) ^ k := by
      rw [hZdef, sum_pow_char]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k p]
    have hS1 : v₂ S ≤ 1 := by
      have : S = z ^ p - (z ^ p - S) := by ring
      rw [this]
      exact v₂.map_sub_le (by rw [map_pow]; exact pow_le_one' hz1 _) hlt.le
    have h2 : v₂ (∑ k ∈ Finset.range N, Γ (y k) ^ p * S ^ k - Z ^ p) < 1 := by
      rw [hZp, ← Finset.sum_sub_distrib]
      refine v₂.map_sum_lt one_ne_zero fun k _ ↦ ?_
      rw [← mul_sub, map_mul, map_pow]
      refine (mul_le_of_le_one_left zero_le
        (pow_le_one' ((H.valuation_ΩMap_le_one_iff _).2 (hy k).2) _)).trans_lt ?_
      refine hpowcong S (z ^ p) hS1 (by rw [map_pow]; exact pow_le_one' hz1 _) ?_ k
      rw [← v₂.map_neg, neg_sub]; exact hlt
    have h3 : v₂ ((𝒟₂).a x₂ - Z ^ p) < 1 := by
      have : (𝒟₂).a x₂ - Z ^ p = ((𝒟₂).a x₂ - Γ ((𝒟₁).a x₁)) +
          (Γ ((𝒟₁).a x₁) - ∑ k ∈ Finset.range N, Γ (y k) ^ p * S ^ k) +
          (∑ k ∈ Finset.range N, Γ (y k) ^ p * S ^ k - Z ^ p) := by ring
      rw [this]
      exact lt_of_le_of_lt (v₂.map_add _ _) (max_lt (lt_of_le_of_lt (v₂.map_add _ _)
        (max_lt hcoord h1)) h2)
    have h4 := valuation_coord_sub_pow_eq_one ha₂ halg₂ hb₂ p hx₂ hZL hZ1
    rw [h4] at h3
    exact lt_irrefl _ h3
  have happ' : v₂ (Γ α - Γ d₀ - ∑ j ∈ s, Γ (d j) * Γ (w j.1) ^ p ^ j.2) ≤ 1 := by
    have := (H.valuation_ΩMap_le_one_iff _).2 happ
    simpa only [map_sub, map_sum, map_mul, map_pow] using this
  obtain ⟨θ, hθL, hθ⟩ := exists_artinSchreier_root_of_approx p v₂ K L₁ L₂ (fun i ↦ Γ (w i))
    (by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨ω, rfl⟩ := RingHom.mem_fieldRange.1 hz
      exact ⟨_, IntermediateField.algebraMap_mem _ ω, rfl⟩)
    (by rintro _ ⟨y, hy, rfl⟩; exact H.ΩMap_mem_compositum y hy)
    hroot hAS (fun i ↦ ⟨w i, hwL i, rfl⟩) (fun i ↦ (H.valuation_ΩMap_eq_one_iff _).2 (hw1 i))
    hval' hhens' hres' ⟨α, hα, rfl⟩ s (fun j ↦ Γ (d j)) (fun j hj ↦ ⟨d j, hd j hj, rfl⟩)
    ⟨d₀, hd₀, rfl⟩ happ' (by obtain ⟨θ, hθ, h⟩ := h₂; exact ⟨θ, hθ, h⟩)
  obtain ⟨θ', hθ'L, rfl⟩ := Subfield.mem_map.1 hθL
  refine ⟨θ', hθ'L, Γ.injective ?_⟩
  rw [map_sub, map_pow, hθ]

end AlgebraicGeometry.SliceTrait.Hom

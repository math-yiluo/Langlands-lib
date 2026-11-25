/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceUnramifiedRoots
public import WeilConjectures.TraceFormula.Specialization.SliceTraitAlgebraic
public import WeilConjectures.RingTheory.Valuation.FrobeniusLiftApprox
public import WeilConjectures.RingTheory.Valuation.GaussResidue
public import WeilConjectures.FieldTheory.FrobeniusClosedBasisSubfield

/-!

# Lifts of Frobenius-closed bases in the slice compositum

Let `D` be the strict-localization slice trait over a strictly henselian trait `R` with residue
characteristic `p`, and `L = Ω(R') ⊆ Ω'` its compositum. Every element `α ∈ L` lies, together with
the coordinate `x`, in a discretely valued subfield `D₀ ⊆ L` whose residue field `E` is a finite
separable extension of `k(x̄)`, `k` the (algebraically closed) residue field of `Ω`. The abstract
package `ValuationSubring.exists_frobeniusLift_package` applied to lifts of a Frobenius-closed
`k`-basis of `E` (`FrobeniusClosedBasis.exists_of_subfield`) then gives the approximation package
used in the proof of the relative separable closedness of the slice composita
(`AlgebraicGeometry.SliceTrait.exists_frobeniusLift_package`).

The field `D₀ = K₀(x, a₁, …, aₙ)` is generated over the discrete subfield `K₀ ⊆ Ω` with full
residue field by the coordinate and finitely many elements of `R'`. It is discretely valued
since it lies in the unramified radical extension `B` of `Frac R'`
(`AlgebraicGeometry.SliceTrait.exists_unramified_subfields`), its residue field is separable over
`k(x̄)` for the same reason, and finite over `k(x̄)` by the Gauss valuation on `K₀(x)`
(`ValuationSubring.residue_mem_adjoin_of_mem_adjoin`), since `R'` is algebraic over `R[x]`.

-/

@[expose] public section

universe u

open IsLocalRing IntermediateField

namespace AlgebraicGeometry.SliceTrait

attribute [local instance] algebraR algebraΩ algebraBaseΩ algebraRΩ

section General

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsStrictlyHenselianLocalRing R] {Ω : Type u} [Field Ω] [Algebra R Ω]
  {κ : Type u} [Field κ] {b : R →+* κ} (D : SliceTrait (algebraMap R Ω) b)

attribute [local instance] algebraFracΩ algebraFrac algebraValuationSubring
  algebraBaseValuationSubring

/-- **The residue of the coordinate is transcendental over the residue field of `Ω`.** The
residues of the integral elements of `Ω` are purely inseparable over the residue field `κ` of
`R`, over which the residue `x̄` is transcendental. -/
lemma transcendental_residue_a [FaithfulSMul R Ω] [Algebra.IsAlgebraic R Ω] {x : D.R}
    (htr : Transcendental (ResidueField R) (residue D.R x)) :
    Transcendental (D.valuationSubring.residueSubfield D.ωS.fieldRange)
      (residue D.valuationSubring (algebraMap D.R D.valuationSubring x)) := by
  set ℓ := ResidueField D.valuationSubring
  set k := D.valuationSubring.residueSubfield D.ωS.fieldRange
  set P := perfectClosure (ResidueField R) ℓ
  have h1 : Transcendental (ResidueField R) (residue D.valuationSubring
      (algebraMap D.R D.valuationSubring x)) := by
    rw [← ResidueField.algebraMap_residue, transcendental_algebraMap_iff
      (algebraMap (ResidueField D.R) ℓ).injective]
    exact htr
  have hkP : k ≤ P.toSubfield := by
    rintro _ ⟨y, ⟨ω, hω⟩, rfl⟩
    obtain ⟨y, hy⟩ := y
    dsimp only at hω
    subst hω
    exact D.residue_mem_perfectClosure hy
  intro halg
  let : Algebra k P := (Subfield.inclusion hkP).toAlgebra
  have : IsScalarTower k P ℓ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact h1 ((halg.tower_top P).restrictScalars (ResidueField R))

/-- **`R'` is algebraic over `K₀(x)`.** If `R'` is algebraic over `R[x]` (via `g`, with `x̄`
transcendental over `κ`) and `K₀ ⊆ Ω` contains `R`, then every element of `R'` is algebraic
over `K₀(x)`: the polynomials in `x` over `R` do not vanish in `Ω'`, by the Gauss valuation. -/
lemma isAlgebraic_a_adjoin_coord [FaithfulSMul R Ω] [Algebra.IsAlgebraic R Ω]
    (g : MvPolynomial (ULift.{u} (Fin 1)) R →+* D.R) (hgC : g.comp MvPolynomial.C = D.φ)
    (htr : Transcendental (ResidueField R) (residue D.R (g (MvPolynomial.X ⟨0⟩))))
    {K₀ : Subfield D.Ω} (hK₀K : K₀ ≤ D.ωS.fieldRange) (hφK₀ : ∀ r : R, D.a (D.φ r) ∈ K₀)
    {r : D.R} (hr : ∃ f : Polynomial (MvPolynomial (ULift.{u} (Fin 1)) R),
      f ≠ 0 ∧ (f.map g).eval r = 0) :
    IsAlgebraic (adjoin K₀ {D.a (g (MvPolynomial.X ⟨0⟩))}) (D.a r) := by
  set x₀ := g (MvPolynomial.X ⟨0⟩) with hx₀
  set F₁ := adjoin K₀ {D.a x₀} with hF₁
  let φ'' : R →+* K₀ := (D.a.comp D.φ).codRestrict K₀ hφK₀
  have heval (c : MvPolynomial (ULift.{u} (Fin 1)) R) : D.a (g c) =
      Polynomial.aeval (D.a x₀) ((MvPolynomial.uniqueAlgEquiv R _ c).map φ'') := by
    conv_lhs => rw [← (MvPolynomial.uniqueAlgEquiv R _).symm_apply_apply c]
    generalize MvPolynomial.uniqueAlgEquiv R _ c = P
    rw [MvPolynomial.uniqueAlgEquiv_symm_apply, Polynomial.hom_eval₂, hgC,
      Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map]
    rfl
  have hmem (c : MvPolynomial (ULift.{u} (Fin 1)) R) : D.a (g c) ∈ F₁ := by
    rw [heval]
    exact algebra_adjoin_le_adjoin K₀ _ (Polynomial.aeval_mem_adjoin_singleton K₀ _)
  have hinj (c : MvPolynomial (ULift.{u} (Fin 1)) R) (hc : D.a (g c) = 0) : c = 0 := by
    by_contra hc0
    set P := (MvPolynomial.uniqueAlgEquiv R _ c).map φ'' with hP
    have hP0 : P ≠ 0 := by
      rw [hP, Polynomial.map_ne_zero_iff ((D.injective_a.comp D.injective_φ).codRestrict _)]
      exact (map_ne_zero_iff _ (MvPolynomial.uniqueAlgEquiv R _).injective).2 hc0
    have hv := ValuationSubring.valuation_aeval_eq_sup
      (D.valuationSubring.residueSubfield_mono hK₀K) (D.transcendental_residue_a htr) P
    obtain ⟨i, hi⟩ : ∃ i, P.coeff i ≠ 0 := by
      by_contra h
      push Not at h
      exact hP0 (Polynomial.ext h)
    have hle := Finset.le_sup (f := fun i ↦ D.valuationSubring.valuation (P.coeff i : D.Ω))
      (Polynomial.mem_support_iff.2 hi)
    have hpos : 0 < D.valuationSubring.valuation (P.coeff i : D.Ω) :=
      (Valuation.pos_iff _).2 (by exact_mod_cast hi)
    have h0 : Polynomial.aeval (D.a x₀) P = 0 := by rw [← heval, hc]
    have : (Polynomial.aeval ((algebraMap D.R D.valuationSubring x₀ : D.valuationSubring) :
        D.Ω) P) = 0 := h0
    rw [this, map_zero] at hv
    exact (hpos.trans_le (hle.trans hv.symm.le)).ne rfl
  let ψ : MvPolynomial (ULift.{u} (Fin 1)) R →+* F₁ := (D.a.comp g).codRestrict F₁ hmem
  have hψ : Function.Injective ψ := (injective_iff_map_eq_zero ψ).2 fun c hc ↦
    hinj c (congrArg Subtype.val hc)
  obtain ⟨f, hf0, hfr⟩ := hr
  refine ⟨f.map ψ, (Polynomial.map_ne_zero_iff hψ).2 hf0, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval_map] at *
  have : (algebraMap F₁ D.Ω).comp ψ = D.a.comp g := rfl
  rw [this, ← Polynomial.hom_eval₂, hfr, map_zero]

/-- **Separability of residues.** If the residue field of `R'` is separable over `κ(x̄)`, then a
sum of products of residues of elements of `R'` and of integral elements of `Ω` is separable over
`k(x̄)`, `k` the residue field of `Ω`. -/
lemma isSeparable_residue_of_eq_sum [FaithfulSMul R Ω] [Algebra.IsAlgebraic R Ω] {x : D.R}
    (hsep : ∀ y : ResidueField D.R, IsSeparable (ResidueField R)⟮residue D.R x⟯ y)
    {z : D.valuationSubring} {n : ℕ} (c : Fin n → D.R) (e : Fin n → D.valuationSubring)
    (he : ∀ j, (e j : D.Ω) ∈ D.ωS.fieldRange)
    (hz : residue _ z = ∑ j, residue _ (algebraMap D.R _ (c j)) * residue _ (e j)) :
    IsSeparable (adjoin (D.valuationSubring.residueSubfield D.ωS.fieldRange)
      {residue D.valuationSubring (algebraMap D.R D.valuationSubring x)}) (residue _ z) := by
  set ℓ := ResidueField D.valuationSubring
  set k := D.valuationSubring.residueSubfield D.ωS.fieldRange
  set M := adjoin k {residue D.valuationSubring (algebraMap D.R D.valuationSubring x)}
  set f := algebraMap (ResidueField D.R) ℓ
  have hkM {y : ℓ} (hy : y ∈ k) : y ∈ M := IntermediateField.algebraMap_mem M (⟨y, hy⟩ : k)
  -- the residues of `R` lie in `k`
  have hRk (r : ResidueField R) : algebraMap (ResidueField R) ℓ r ∈ k := by
    obtain ⟨r, rfl⟩ := residue_surjective r
    refine ⟨algebraMap R D.valuationSubring r, ⟨algebraMap R Ω r, ?_⟩, rfl⟩
    exact (RingHom.congr_fun D.ωS_comp r)
  let C' : IntermediateField (ResidueField R) (ResidueField D.R) :=
    (M.toSubfield.comap f).toIntermediateField fun r ↦ by
      change f (algebraMap (ResidueField R) (ResidueField D.R) r) ∈ M
      rw [← IsScalarTower.algebraMap_apply]
      exact hkM (hRk r)
  have hC : (ResidueField R)⟮residue D.R x⟯ ≤ C' := by
    rw [adjoin_simple_le_iff]
    exact mem_adjoin_simple_self k _
  let h : (ResidueField R)⟮residue D.R x⟯ →+* M :=
    (f.comp (IntermediateField.val _).toRingHom).codRestrict M fun y ↦ hC y.2
  rw [← mem_separableClosure_iff, hz]
  refine sum_mem fun j _ ↦ mul_mem ?_ ?_
  · rw [mem_separableClosure_iff, ← ResidueField.algebraMap_residue]
    exact IsSeparable.of_ringHom_comp f h rfl (hsep _)
  · rw [mem_separableClosure_iff]
    obtain ⟨ω, hω⟩ := he j
    have hk : residue D.valuationSubring (e j) ∈ k := ⟨e j, ⟨ω, hω⟩, rfl⟩
    exact isSeparable_algebraMap (F := M) (K := ℓ) ⟨_, hkM hk⟩

end General

section StrictLocalization

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsStrictlyHenselianLocalRing R] {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {a : R →+* Ω}
  (ha : Function.Injective a) (halg : letI := a.toAlgebra; Algebra.IsAlgebraic R Ω)
  {κ : Type u} [Field κ] [IsSepClosed κ] {b : R →+* κ} (hb : RingHom.ker b = maximalIdeal R)

attribute [local instance] algebraValuationSubring algebraBaseValuationSubring

local notation "𝒟" => sliceTraitOfStrictLocalization (a₁ := a) (b₁ := b) ha halg hb

omit [IsSepClosed κ] in
include ha halg hb in
/-- **Approximation by lifts of a Frobenius-closed basis in the slice compositum.** For `α` in
the compositum `L = Ω(R')` there are a coordinate `x ∈ R'`, a subring `A ⊆ L ∩ 𝒪`, a discretely
valued subfield `Kst ⊆ Ω` and elements `w i ∈ A` of value `1` such that the monomials
`1, w i ^ p ^ n` are valuation independent over `Ω`, the residue of `x` is a polynomial with
`p`-th power coefficients in any combination of the monomials with a unit coefficient on some
`w i`, and `α`, the elements of `A` (over `Kst`) and of the field generated by `Ω` and `A` (over
`Ω`) are approximated to arbitrary precision by combinations of the monomials. -/
theorem exists_frobeniusLift_package (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    {x : (𝒟).R} (hx : (𝒟).b x = traitSliceCoord κ) {α : (𝒟).Ω}
    (hα : letI := a.toAlgebra; α ∈ (𝒟).compositum) :
    letI := a.toAlgebra
    ∃ (ι : Type u) (w : ι → (𝒟).Ω) (A : Subring (𝒟).Ω) (Kst : Subfield (𝒟).Ω),
      Kst ≤ (𝒟).ωS.fieldRange ∧ (∀ i, w i ∈ A) ∧
      (∀ y ∈ A, y ∈ (𝒟).compositum ∧ (𝒟).valuationSubring.valuation y ≤ 1) ∧
      (∀ i, (𝒟).valuationSubring.valuation (w i) = 1) ∧
      (∀ c : Option (ι × ℕ) →₀ (𝒟).Ω, (∀ j, c j ∈ (𝒟).ωS.fieldRange) →
        ∀ j, (𝒟).valuationSubring.valuation (c j) ≤
          (𝒟).valuationSubring.valuation (frobeniusComb p w c)) ∧
      (∀ c : Option (ι × ℕ) →₀ (𝒟).Ω, (∀ j, c j ∈ (𝒟).ωS.fieldRange) →
        (∀ j, (𝒟).valuationSubring.valuation (c j) ≤ 1) →
        (∃ i, (𝒟).valuationSubring.valuation (c (some (i, 0))) = 1) →
        ∃ (N : ℕ) (y : ℕ → (𝒟).Ω), (∀ k, y k ∈ (𝒟).compositum ∧
          (𝒟).valuationSubring.valuation (y k) ≤ 1) ∧
          (𝒟).valuationSubring.valuation ((𝒟).a x -
            ∑ k ∈ Finset.range N, y k ^ p * (frobeniusComb p w c) ^ k) < 1) ∧
      (∃ ϖ ∈ Kst, 0 < (𝒟).valuationSubring.valuation ϖ ∧
        (𝒟).valuationSubring.valuation ϖ < 1 ∧
        (∀ c ∈ Kst, c ≠ 0 → ∃ n : ℤ, (𝒟).valuationSubring.valuation c =
          (𝒟).valuationSubring.valuation ϖ ^ n) ∧
        ∀ t : (𝒟).Ω, t ≠ 0 → ∃ N : ℕ, (𝒟).valuationSubring.valuation ϖ ^ N <
          (𝒟).valuationSubring.valuation t) ∧
      (∀ y ∈ A, ∀ t : (𝒟).Ω, t ≠ 0 → ∃ e : Option (ι × ℕ) →₀ (𝒟).Ω, (∀ k, e k ∈ Kst) ∧
        (𝒟).valuationSubring.valuation (y - frobeniusComb p w e) <
          (𝒟).valuationSubring.valuation t) ∧
      (∀ t : (𝒟).Ω, t ≠ 0 → ∃ e : Option (ι × ℕ) →₀ (𝒟).Ω, (∀ k, e k ∈ Kst) ∧
        (𝒟).valuationSubring.valuation (α - frobeniusComb p w e) <
          (𝒟).valuationSubring.valuation t) ∧
      (∀ y ∈ Subfield.closure ((𝒟).ωS.fieldRange ∪ A : Set (𝒟).Ω), ∀ t : (𝒟).Ω, t ≠ 0 →
        ∃ c : Option (ι × ℕ) →₀ (𝒟).Ω, (∀ j, c j ∈ (𝒟).ωS.fieldRange) ∧
          (𝒟).valuationSubring.valuation (y - frobeniusComb p w c) <
            (𝒟).valuationSubring.valuation t) ∧
      (∀ y ∈ A, (𝒟).valuationSubring.valuation y = 1 → y⁻¹ ∈ A) ∧
      (∀ c ∈ Kst, (𝒟).valuationSubring.valuation c ≤ 1 → c ∈ A) ∧
      (∀ c ∈ Kst, (𝒟).valuationSubring.valuation c ≤ 1 →
        ∃ d ∈ Kst, (𝒟).valuationSubring.valuation (d ^ p - c) < 1) := by
  classical
  let := a.toAlgebra
  have : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 ha
  have : Algebra.IsAlgebraic R Ω := halg
  have := (𝒟).subsingleton_primeSpectrum ha halg
  obtain ⟨g, hgC, hgX, hgalg⟩ :=
    exists_coord_isAlgebraic_strictHenselization_sliceTraitPoint b hb
  set x₀ : (𝒟).R := g (MvPolynomial.X ⟨0⟩) with hx₀
  have hx₀b : (𝒟).b x₀ = traitSliceCoord κ := hgX
  have htr := transcendental_residue_of_b_eq ha halg hb hx₀b
  have hsep := isSeparable_residue_of_b_eq ha halg hb hx₀b
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨K₀, B, hK₀K, hK₀B, haB, hφK₀, hfull, hdiscB, hresB⟩ :=
    (𝒟).exists_unramified_subfields p htr hsep hϖ
  obtain ⟨s, hs⟩ := (𝒟).exists_finset_eq_sum_of_mem_compositum hα
  set 𝒪 := (𝒟).valuationSubring with h𝒪
  set K := (𝒟).ωS.fieldRange with hK
  set L := (𝒟).compositum.toSubfield with hL
  -- the field `D₀ = K₀(x, aᵢ)`
  set F₁ := adjoin K₀ {(𝒟).a x₀} with hF₁
  set gens : Set (𝒟).Ω := (fun q : Ω × (𝒟).R ↦ (𝒟).a q.2) '' (s : Set (Ω × (𝒟).R)) with hgens
  set D₁ := adjoin F₁ gens with hD₁
  have : Finite gens := (s.finite_toSet.image _).to_subtype
  have : FiniteDimensional F₁ D₁ := finiteDimensional_adjoin fun y hy ↦ by
    obtain ⟨q, -, rfl⟩ := hy
    exact ((𝒟).isAlgebraic_a_adjoin_coord g hgC htr hK₀K hφK₀ (hgalg q.2)).isIntegral
  set D : Subfield (𝒟).Ω := D₁.toSubfield with hD
  have hF₁D (c : (𝒟).Ω) (hc : c ∈ F₁) : c ∈ D := IntermediateField.algebraMap_mem D₁ (⟨c, hc⟩ : F₁)
  have hK₀D : K₀ ≤ D := fun c hc ↦ hF₁D c (IntermediateField.algebraMap_mem F₁ (⟨c, hc⟩ : K₀))
  have hx₀D : (𝒟).a x₀ ∈ D := hF₁D _ (mem_adjoin_simple_self K₀ _)
  have hgD (q : Ω × (𝒟).R) (hq : q ∈ s) : (𝒟).a q.2 ∈ D := subset_adjoin F₁ gens ⟨q, hq, rfl⟩
  have hDB : D ≤ B := by
    have h₁ : F₁ ≤ B.toIntermediateField (fun c : K₀ ↦ hK₀B c.2) := by
      rw [adjoin_le_iff, Set.singleton_subset_iff]
      exact haB x₀
    have h₂ : D₁ ≤ B.toIntermediateField (fun c : F₁ ↦ h₁ c.2) := by
      rw [adjoin_le_iff]
      rintro _ ⟨q, -, rfl⟩
      exact haB q.2
    exact h₂
  have hKL : K ≤ L := by
    rintro _ ⟨ω, rfl⟩
    exact IntermediateField.algebraMap_mem _ ω
  have haL (r : (𝒟).R) : (𝒟).a r ∈ L := IntermediateField.subset_adjoin _ _ ⟨r, rfl⟩
  have hDL : D ≤ L := by
    have h₁ : F₁ ≤ L.toIntermediateField (fun c : K₀ ↦ hKL (hK₀K c.2)) := by
      rw [adjoin_le_iff, Set.singleton_subset_iff]
      exact haL x₀
    have h₂ : D₁ ≤ L.toIntermediateField (fun c : F₁ ↦ h₁ c.2) := by
      rw [adjoin_le_iff]
      rintro _ ⟨q, -, rfl⟩
      exact haL q.2
    exact h₂
  -- the hypotheses of the abstract package
  have hϖK₀ : (𝒟).a ((𝒟).φ ϖ) ∈ K₀ := hφK₀ ϖ
  have hϖ0 : (𝒟).a ((𝒟).φ ϖ) ≠ 0 :=
    (map_ne_zero_iff _ (𝒟).injective_a).2 ((map_ne_zero_iff _ (𝒟).injective_φ).2 hϖ.ne_zero)
  have hϖ1 : 𝒪.valuation ((𝒟).a ((𝒟).φ ϖ)) < 1 :=
    (𝒟).valuation_a_lt_one_iff.2 ((mem_maximalIdeal _).2 ((𝒟).irreducible_φ hϖ).not_isUnit)
  have hdisc (z : (𝒟).Ω) (hz : z ∈ D) (hz0 : z ≠ 0) :
      ∃ m : ℤ, 𝒪.valuation z = 𝒪.valuation ((𝒟).a ((𝒟).φ ϖ)) ^ m :=
    hdiscB z (hDB hz) hz0
  have harch (z : (𝒟).Ω) (hz : z ≠ 0) : ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ,
      𝒪.valuation z ^ n = 𝒪.valuation ((𝒟).a ((𝒟).φ ϖ)) ^ m :=
    (𝒟).exists_valuation_pow_eq_zpow ((𝒟).irreducible_φ hϖ) hz
  have hKroot (n : ℕ) (hn : 0 < n) (y : (𝒟).Ω) (hy : y ∈ K) : ∃ z ∈ K, z ^ n = y := by
    obtain ⟨ω, rfl⟩ := hy
    obtain ⟨ω', hω'⟩ := IsAlgClosed.exists_pow_nat_eq ω hn
    exact ⟨_, ⟨ω', rfl⟩, by rw [← map_pow, hω']⟩
  have halgK (c : (𝒟).Ω) (hc : c ∈ K) : IsAlgebraic K₀ c := by
    obtain ⟨ω, rfl⟩ := hc
    obtain ⟨f, hf0, hfω⟩ := Algebra.IsAlgebraic.isAlgebraic (R := R) ω
    let φ'' : R →+* K₀ := ((𝒟).a.comp (𝒟).φ).codRestrict K₀ hφK₀
    refine ⟨f.map φ'', (Polynomial.map_ne_zero_iff
      (((𝒟).injective_a.comp (𝒟).injective_φ).codRestrict _)).2 hf0, ?_⟩
    have h : (algebraMap K₀ (𝒟).Ω).comp φ'' = (𝒟).ωS.comp (algebraMap R Ω) :=
      (𝒟).ωS_comp.symm
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, h, ← Polynomial.hom_eval₂,
      ← Polynomial.aeval_def, hfω, map_zero]
  set x𝒪 : 𝒪 := algebraMap (𝒟).R 𝒪 x₀ with hx𝒪
  -- the Frobenius-closed basis of the residue field of `D₀`
  set k := 𝒪.residueSubfield K with hk
  set E := 𝒪.residueSubfield D with hE
  have : CharP (ResidueField 𝒪) p :=
    charP_of_injective_algebraMap (algebraMap (ResidueField R) (ResidueField 𝒪)).injective p
  have : IsAlgClosed K := IsAlgClosed.of_ringEquiv Ω _ (𝒟).ωS.rangeRestrictFieldEquiv
  have : IsAlgClosed k := ValuationSubring.isAlgClosed_residueSubfield K
  have hkE : k ≤ E := by
    rintro _ ⟨y, hyK, rfl⟩
    obtain ⟨z, hzK₀, hz⟩ := hfull y hyK ((𝒪.valuation_le_one_iff _).2 y.2)
    have hz𝒪 : z ∈ 𝒪 := by
      have : z = y - (y - z) := by ring
      rw [← 𝒪.valuation_le_one_iff, this]
      exact 𝒪.valuation.map_sub_le ((𝒪.valuation_le_one_iff _).2 y.2) hz.le
    refine ⟨⟨z, hz𝒪⟩, hK₀D hzK₀, ?_⟩
    rw [eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact (ValuationSubring.valuation_lt_one_iff 𝒪 _).2 hz
  have hxE : residue 𝒪 x𝒪 ∈ E := ⟨x𝒪, hx₀D, rfl⟩
  have htrk : Transcendental k (residue 𝒪 x𝒪) := (𝒟).transcendental_residue_a htr
  have hfin : ∃ N : ℕ, ∀ (n : ℕ) (e : Fin n → ResidueField 𝒪), (∀ i, e i ∈ E) →
      LinearIndependent (adjoin k {residue 𝒪 x𝒪}) e → n ≤ N := by
    refine ⟨Module.finrank F₁ D₁, fun n e heE hli ↦ ?_⟩
    choose d hdD hde using fun i ↦ heE i
    have hA (c : F₁) (h : algebraMap F₁ (𝒟).Ω c ∈ 𝒪) :
        residue 𝒪 ⟨algebraMap F₁ (𝒟).Ω c, h⟩ ∈
          (algebraMap (adjoin k {residue 𝒪 x𝒪}) (ResidueField 𝒪)).range :=
      ⟨⟨_, ValuationSubring.residue_mem_adjoin_of_mem_adjoin
        (𝒪.residueSubfield_mono hK₀K) htrk (y := ⟨_, h⟩) c.2⟩, rfl⟩
    have hres := Valuation.ResiduallyIndependent.of_linearIndependent_residue hA d
      (by simpa only [hde] using hli)
    have hd1 (i : Fin n) : 𝒪.valuation (d i : (𝒟).Ω) = 1 := by
      refine (𝒪.valuation_eq_one_iff (d i)).1 ((residue_ne_zero_iff_isUnit _).1 ?_)
      rw [hde]
      exact hli.ne_zero i
    have hlin := hres.linearIndependent hd1
    let d' : Fin n → D₁ := fun i ↦ ⟨d i, hdD i⟩
    have hlin' : LinearIndependent F₁ d' :=
      LinearIndependent.of_comp D₁.val.toLinearMap hlin
    simpa using hlin'.fintype_card_le_finrank
  have hsepE (e : ResidueField 𝒪) (he : e ∈ E) : IsSeparable (adjoin k {residue 𝒪 x𝒪}) e := by
    obtain ⟨z, hzD, rfl⟩ := he
    obtain ⟨n, c, e, hce, hz⟩ := hresB z (hDB hzD)
    exact (𝒟).isSeparable_residue_of_eq_sum hsep c e hce hz
  obtain ⟨ι, u, hu, hli, hsp, hpth⟩ :=
    FrobeniusClosedBasis.exists_of_subfield p k E hkE hxE htrk hfin hsepE
  -- the presentation of `α`
  have hα' : ∃ (n : ℕ) (c a' : Fin n → (𝒟).Ω), (∀ l, c l ∈ K) ∧
      (∀ l, a' l ∈ D ∧ 𝒪.valuation (a' l) ≤ 1) ∧ α = ∑ l, c l * a' l := by
    refine ⟨s.card, fun l ↦ (𝒟).ωS (s.equivFin.symm l).1.1,
      fun l ↦ (𝒟).a (s.equivFin.symm l).1.2, fun l ↦ ⟨_, rfl⟩,
      fun l ↦ ⟨hgD _ (s.equivFin.symm l).2,
        (𝒪.valuation_le_one_iff _).2 ((𝒟).a_mem_valuationSubring _)⟩, ?_⟩
    rw [hs, ← Finset.sum_coe_sort s, ← s.equivFin.symm.sum_comp]
  obtain ⟨w, A, Kst, hKst, hwA, hA, hw1, hval, hpb, hP4, hP5, hP6, hP7, hinv, hKstA, hroot⟩ :=
    ValuationSubring.exists_frobeniusLift_package 𝒪 K K₀ D L hK₀K hK₀D hDL hKL hϖK₀ hϖ0 hϖ1
      hdisc harch hKroot halgK hfull (x := x𝒪) hu hli hsp hpth hα'
  -- the residue of `x` is the residue of `x₀`
  have hxx₀ : 𝒪.valuation ((𝒟).a x - (𝒟).a x₀) < 1 := by
    rw [← map_sub, valuation_a_lt_one_iff, ← (𝒟).ker_b, RingHom.mem_ker, map_sub, sub_eq_zero,
      hx, hx₀b]
  refine ⟨ι, w, A, Kst, hKst, hwA, hA, hw1, hval, fun c hc hc1 hci ↦ ?_, hP4, hP5, hP6, hP7,
    hinv, hKstA, hroot⟩
  obtain ⟨N, y, hy, hyv⟩ := hpb c hc hc1 hci
  refine ⟨N, y, hy, ?_⟩
  have : (𝒟).a x - ∑ k ∈ Finset.range N, y k ^ p * frobeniusComb p w c ^ k =
      ((𝒟).a x - (𝒟).a x₀) + ((x𝒪 : (𝒟).Ω) -
        ∑ k ∈ Finset.range N, y k ^ p * frobeniusComb p w c ^ k) := by
    rw [hx𝒪, coe_algebraMap_valuationSubring]
    ring
  rw [this]
  exact lt_of_le_of_lt (𝒪.valuation.map_add _ _) (max_lt hxx₀ hyv)

end StrictLocalization

end AlgebraicGeometry.SliceTrait

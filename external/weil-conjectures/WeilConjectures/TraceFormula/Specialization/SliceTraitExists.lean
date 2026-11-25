/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.SliceTrait
public import WeilConjectures.TraceFormula.Specialization.SliceTraitPoint
public import WeilConjectures.AlgebraicGeometry.Sites.StrictLocalizationUniversal
public import WeilConjectures.TraceFormula.Specialization.SliceTraitResidue

/-!

# The strict localization of `𝔸¹_{S₁}` is a slice trait

Let `S₁ = Spec R₁` be a strictly henselian trait with a geometric generic point `a₁ : R₁ ⟶ Ω₁`
(`Ω₁` algebraic over `R₁`) and a point `b₁ : R₁ ⟶ κ₁` with kernel the maximal ideal. The strict
henselization `R` of `𝔸¹_{S₁}` at the geometric point `Spec κ₁(x)^alg ⟶ 𝔸¹_{S₁}` over the generic
point of its special fibre (`AlgebraicGeometry.sliceTraitPoint`) is a slice trait over `S₁`
(`AlgebraicGeometry.sliceTraitOfStrictLocalization`, `AlgebraicGeometry.nonempty_sliceTrait`), with
geometric generic point `R ⟶ Ω' = (Frac R)^alg` and closed point `R ⟶ κ₁(x)^alg`
(SGA 4½, [Th. finitude], 3.3). The embedding `Ω₁ ⟶ Ω'` extends `Frac R₁ ⟶ Frac R`.

-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

section AlgebraicClosure

variable (R : Type u) [CommRing R] [IsDomain R]

/-- A domain embeds into the algebraic closure of its fraction field. -/
lemma injective_algebraMap_algebraicClosure_fractionRing :
    Function.Injective (algebraMap R (AlgebraicClosure (FractionRing R))) := by
  rw [IsScalarTower.algebraMap_eq R (FractionRing R)]
  exact (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).injective.comp
    (IsFractionRing.injective _ _)

/-- The algebraic closure of the fraction field of a domain is algebraic over it. -/
lemma isAlgebraic_algebraicClosure_fractionRing :
    letI := (algebraMap R (AlgebraicClosure (FractionRing R))).toAlgebra
    Algebra.IsAlgebraic R (AlgebraicClosure (FractionRing R)) := by
  have := IsLocalization.isAlgebraic (FractionRing R) (nonZeroDivisors R)
  have := Algebra.IsAlgebraic.trans R (FractionRing R) (AlgebraicClosure (FractionRing R))
  convert this
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

/-- An embedding `Ω₁ ⟶ (Frac R)^alg` over an injective map `R₁ ⟶ R` of domains, for `Ω₁` a field
algebraic over `R₁`. -/
lemma exists_comp_eq_algebraMap_algebraicClosure_fractionRing {R₁ Ω₁ : Type u} [CommRing R₁]
    [IsDomain R₁] [Field Ω₁] (a₁ : R₁ →+* Ω₁) (ha₁ : Function.Injective a₁)
    (halg : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁) (φ : R₁ →+* R)
    (hφ : Function.Injective φ) :
    ∃ ω : Ω₁ →+* AlgebraicClosure (FractionRing R),
      ω.comp a₁ = (algebraMap R (AlgebraicClosure (FractionRing R))).comp φ := by
  let F₁ := FractionRing R₁
  let : Algebra F₁ Ω₁ := (IsFractionRing.lift ha₁).toAlgebra
  let : Algebra R₁ Ω₁ := a₁.toAlgebra
  have : IsScalarTower R₁ F₁ Ω₁ := IsScalarTower.of_algebraMap_eq fun r ↦
    (IsFractionRing.lift_algebraMap ha₁ r).symm
  have : Algebra.IsAlgebraic F₁ Ω₁ :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective R₁ F₁)
  have hinj : Function.Injective ((algebraMap R (AlgebraicClosure (FractionRing R))).comp φ) :=
    (injective_algebraMap_algebraicClosure_fractionRing R).comp hφ
  let : Algebra F₁ (AlgebraicClosure (FractionRing R)) := (IsFractionRing.lift hinj).toAlgebra
  refine ⟨(IsAlgClosed.lift (R := F₁) (S := Ω₁) (M := AlgebraicClosure (FractionRing R))).toRingHom,
    ?_⟩
  ext r
  have h := (IsAlgClosed.lift (R := F₁) (S := Ω₁)
    (M := AlgebraicClosure (FractionRing R))).commutes (algebraMap R₁ F₁ r)
  rw [← IsScalarTower.algebraMap_apply] at h
  change (IsAlgClosed.lift (R := F₁) (S := Ω₁) (M := AlgebraicClosure (FractionRing R)))
    (algebraMap R₁ Ω₁ r) = _
  rw [h]
  exact IsFractionRing.lift_algebraMap hinj r

end AlgebraicClosure

namespace AlgebraicGeometry

open Scheme

variable {R₁ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  {Ω₁ : Type u} [Field Ω₁] (a₁ : R₁ →+* Ω₁)
  (ha₁ : Function.Injective a₁) (halg : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
  {κ₁ : Type u} [Field κ₁] (b₁ : R₁ →+* κ₁) (hb₁ : RingHom.ker b₁ = maximalIdeal R₁)

include ha₁ halg hb₁ in
/-- The embedding `Ω₁ ⟶ Ω' = (Frac R)^alg` of geometric generic points. -/
lemma exists_sliceTrait_genericField_hom :
    letI := isDomain_strictHenselization_sliceTraitPoint b₁ hb₁
    ∃ ω : Ω₁ →+* AlgebraicClosure (FractionRing (strictHenselization (sliceTraitPoint b₁))),
      ω.comp a₁ = (algebraMap (strictHenselization (sliceTraitPoint b₁)) _).comp
        (sliceTraitStructureMap b₁) := by
  have := isDomain_strictHenselization_sliceTraitPoint b₁ hb₁
  exact exists_comp_eq_algebraMap_algebraicClosure_fractionRing _ a₁ ha₁ halg _
    (injective_sliceTraitStructureMap b₁ hb₁)

variable [IsStrictlyHenselianLocalRing R₁]

include ha₁ halg hb₁ in
/-- **The strict localization of `𝔸¹_{S₁}` at the generic point of its special fibre** as a slice
trait over `S₁`: `R` the strict henselization at `sliceTraitPoint b₁`, `Ω' = (Frac R)^alg`, and
`κ' = κ₁(x)^alg` with the evaluation at the geometric point. -/
noncomputable def sliceTraitOfStrictLocalization : SliceTrait a₁ b₁ :=
  haveI := isDomain_strictHenselization_sliceTraitPoint b₁ hb₁
  haveI := isDiscreteValuationRing_strictHenselization_sliceTraitPoint b₁ hb₁
  haveI := isLocalHom_sliceTraitStructureMap b₁ hb₁
  haveI := isStrictlyHenselianLocalRing_strictHenselization' (sliceTraitPoint b₁)
  {
    R := strictHenselization (sliceTraitPoint b₁)
    toAffineLine := strictLocalizationToBase (sliceTraitPoint b₁)
    weaklyEtale := inferInstance
    φ := sliceTraitStructureMap b₁
    spec_φ := by rw [sliceTraitStructureMap, CommRingCat.ofHom_hom, Spec.map_preimage]
    maximalIdeal_eq := maximalIdeal_strictHenselization_sliceTraitPoint b₁ hb₁
    mem_range_residueField := fun z hz ↦
      mem_range_algebraMap_residueField_sliceTraitPoint b₁ hb₁ z hz
    Ω := AlgebraicClosure (FractionRing (strictHenselization (sliceTraitPoint b₁)))
    a := algebraMap _ _
    injective_a := injective_algebraMap_algebraicClosure_fractionRing _
    isAlgebraic_a := isAlgebraic_algebraicClosure_fractionRing _
    ωS := (exists_sliceTrait_genericField_hom a₁ ha₁ halg b₁ hb₁).choose
    ωS_comp := (exists_sliceTrait_genericField_hom a₁ ha₁ halg b₁ hb₁).choose_spec
    κ := traitSliceField κ₁
    b := (strictHenselizationEval (sliceTraitPoint b₁)).hom
    ker_b := maximalIdeal_strictHenselization.symm
    κS := algebraMap κ₁ (traitSliceField κ₁)
    κS_comp := (strictHenselizationEval_comp_sliceTraitStructureMap b₁).symm }

include ha₁ halg hb₁ in
/-- **The strict localization of `𝔸¹_{S₁}` at the generic point of its special fibre is a slice
trait** (EGA IV₄, 18.8; SGA 4½, [Th. finitude], 3.3). -/
theorem nonempty_sliceTrait : Nonempty (SliceTrait a₁ b₁) :=
  ⟨sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₁) ha₁ halg hb₁⟩

section Simp

variable {a₁ b₁}

lemma sliceTraitOfStrictLocalization_R :
    (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₁) ha₁ halg hb₁).R =
      strictHenselization (sliceTraitPoint b₁) :=
  rfl

lemma sliceTraitOfStrictLocalization_toAffineLine :
    (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₁) ha₁ halg hb₁).toAffineLine =
      strictLocalizationToBase (sliceTraitPoint b₁) :=
  rfl

lemma sliceTraitOfStrictLocalization_φ :
    (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₁) ha₁ halg hb₁).φ =
      sliceTraitStructureMap b₁ :=
  rfl

lemma sliceTraitOfStrictLocalization_b :
    (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₁) ha₁ halg hb₁).b =
      (strictHenselizationEval (sliceTraitPoint b₁)).hom :=
  rfl

end Simp

end AlgebraicGeometry

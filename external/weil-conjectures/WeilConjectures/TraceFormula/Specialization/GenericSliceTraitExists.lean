/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTrait
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitDVR
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitUniversal
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationFunctoriality
public import WeilConjectures.TraceFormula.Specialization.SliceTraitResidue

/-!

# The strict localization of `𝔸¹_S` is a generic slice trait

The strict henselization `R` of `𝔸¹_S` (`S = Spec k'⟦t⟧`) at the geometric point
`Spec K ⟶ 𝔸¹_S` over the generic point of its special fibre (`AlgebraicGeometry.genericSlicePoint`,
`K = k'(x)^alg`) is a strictly henselian discrete valuation ring, weakly étale over `𝔸¹_S`, and the
generic slice `Spec K⟦t⟧ ⟶ 𝔸¹_S` factors through it by a local injection `R ⟶ K⟦t⟧`
(SGA 4½, [Th. finitude], 3.3). With the geometric generic point `R ⟶ Ω' = (Frac R)^alg` and the
closed point `R ⟶ K`, this is a generic slice trait
(`AlgebraicGeometry.genericSliceTraitOfStrictLocalization`,
`AlgebraicGeometry.nonempty_genericSliceTrait`).

The embedding `Ω' ⟶ Ω_K` extends `Frac R ⟶ Frac K⟦t⟧`
(`AlgebraicGeometry.genericSliceTraitToField`); the embedding `Ω ⟶ Ω'` is the unique one whose
composite with it is the fixed embedding `Ω ⟶ Ω_K`: the image of `Ω`, algebraic over
`Frac k'⟦t⟧`, lies in the algebraically closed image of `Ω'`
(`AlgebraicGeometry.genericSliceTraitFromField`).

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

variable (k' : Type u) [Field k']

attribute [local instance] isDomain_strictHenselization_genericSlicePoint
  isDiscreteValuationRing_strictHenselization_genericSlicePoint

/-- The field `Ω' = (Frac R)^alg` of the geometric generic point of the strict localization
`Spec R` of `𝔸¹_S` at the generic point of its special fibre. -/
noncomputable abbrev genericSliceTraitField : Type u :=
  AlgebraicClosure (FractionRing (strictHenselization (genericSlicePoint k')))

/-- The structure map `k'⟦t⟧ ⟶ R` of the strict localization of `𝔸¹_S`. -/
noncomputable def genericSliceTraitStructureMap :
    PowerSeries k' →+* strictHenselization (genericSlicePoint k') :=
  (Spec.preimage (strictLocalizationToBase (genericSlicePoint k') ≫
    𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')).hom

lemma spec_genericSliceTraitStructureMap :
    Spec.map (CommRingCat.ofHom (genericSliceTraitStructureMap k')) =
      strictLocalizationToBase (genericSlicePoint k') ≫
        𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' := by
  rw [genericSliceTraitStructureMap, CommRingCat.ofHom_hom, Spec.map_preimage]

/-- The slice `R ⟶ K⟦t⟧` restricts to the coefficientwise map on `k'⟦t⟧`. -/
lemma genericSliceRingHom_comp_structureMap :
    (genericSliceRingHom k').comp (genericSliceTraitStructureMap k') =
      PowerSeries.map (algebraMap k' (traitSliceField k')) := by
  have h : Spec.map (CommRingCat.ofHom ((genericSliceRingHom k').comp
      (genericSliceTraitStructureMap k'))) = traitMap k' (traitSliceField k') := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, spec_genericSliceTraitStructureMap,
      reassoc_of% spec_genericSliceRingHom k', traitSlice_over]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

lemma injective_genericSliceTraitStructureMap :
    Function.Injective (genericSliceTraitStructureMap k') := by
  intro x y h
  have := congrArg (genericSliceRingHom k') h
  rw [← RingHom.comp_apply, ← RingHom.comp_apply, genericSliceRingHom_comp_structureMap] at this
  exact PowerSeries.map_injective _ (algebraMap k' (traitSliceField k')).injective this

/-- The injection `R ⟶ K⟦t⟧ ⟶ Ω_K`. -/
lemma injective_algebraMap_comp_genericSliceRingHom :
    Function.Injective ((algebraMap (PowerSeries (traitSliceField k'))
      (traitGenericField (traitSliceField k'))).comp (genericSliceRingHom k')) :=
  (algebraMap_traitGenericField_injective _).comp (injective_genericSliceRingHom k')

/-- `R ⟶ Ω' = (Frac R)^alg` is injective. -/
lemma injective_algebraMap_genericSliceTraitField :
    Function.Injective (algebraMap (strictHenselization (genericSlicePoint k'))
      (genericSliceTraitField k')) := by
  rw [IsScalarTower.algebraMap_eq _ (FractionRing (strictHenselization (genericSlicePoint k')))]
  exact (algebraMap (FractionRing (strictHenselization (genericSlicePoint k')))
    (genericSliceTraitField k')).injective.comp
    (IsFractionRing.injective _ _)

/-- `Ω' = (Frac R)^alg` is algebraic over `R`. -/
lemma isAlgebraic_genericSliceTraitField :
    letI := (algebraMap (strictHenselization (genericSlicePoint k'))
      (genericSliceTraitField k')).toAlgebra
    Algebra.IsAlgebraic (strictHenselization (genericSlicePoint k'))
      (genericSliceTraitField k') := by
  have := IsLocalization.isAlgebraic (FractionRing (strictHenselization (genericSlicePoint k')))
    (nonZeroDivisors (strictHenselization (genericSlicePoint k')))
  have := Algebra.IsAlgebraic.trans (strictHenselization (genericSlicePoint k'))
    (FractionRing (strictHenselization (genericSlicePoint k'))) (genericSliceTraitField k')
  convert this
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

/-- The embedding `Frac R ⟶ Ω_K` extending `R ⟶ K⟦t⟧ ⟶ Ω_K`. -/
noncomputable def genericSliceTraitFractionMap :
    FractionRing (strictHenselization (genericSlicePoint k')) →+*
      traitGenericField (traitSliceField k') :=
  IsFractionRing.lift (injective_algebraMap_comp_genericSliceRingHom k')

/-- The embedding `ω_K : Ω' = (Frac R)^alg ⟶ Ω_K` over `Frac R ⟶ Ω_K`. -/
noncomputable def genericSliceTraitToField :
    genericSliceTraitField k' →+* traitGenericField (traitSliceField k') :=
  letI := (genericSliceTraitFractionMap k').toAlgebra
  (IsAlgClosed.lift (R := FractionRing (strictHenselization (genericSlicePoint k')))
    (S := genericSliceTraitField k') (M := traitGenericField (traitSliceField k'))).toRingHom

lemma genericSliceTraitToField_algebraMap :
    (genericSliceTraitToField k').comp
        (algebraMap (strictHenselization (genericSlicePoint k')) (genericSliceTraitField k')) =
      (algebraMap (PowerSeries (traitSliceField k'))
        (traitGenericField (traitSliceField k'))).comp (genericSliceRingHom k') := by
  let := (genericSliceTraitFractionMap k').toAlgebra
  ext r
  rw [RingHom.comp_apply, RingHom.comp_apply,
    IsScalarTower.algebraMap_apply (strictHenselization (genericSlicePoint k'))
    (FractionRing (strictHenselization (genericSlicePoint k'))) (genericSliceTraitField k')]
  change (IsAlgClosed.lift (R := FractionRing (strictHenselization (genericSlicePoint k')))
    (S := genericSliceTraitField k') (M := traitGenericField (traitSliceField k')))
      (algebraMap _ _ _) = _
  rw [AlgHom.commutes]
  exact IsFractionRing.lift_algebraMap (injective_algebraMap_comp_genericSliceRingHom k') r

/-- The image of the fixed embedding `Ω ⟶ Ω_K` lies in the image of `ω_K : Ω' ⟶ Ω_K`: an element
of `Ω` is algebraic over `Frac k'⟦t⟧`, whose image lies in that of `Ω'`, which is algebraically
closed. -/
lemma traitGenericFieldMap_mem_fieldRange (z : traitGenericField k') :
    traitGenericFieldMap k' (traitSliceField k') z ∈ (genericSliceTraitToField k').fieldRange := by
  set R := strictHenselization (genericSlicePoint k')
  set F := FractionRing (PowerSeries k')
  -- the embedding `Frac k'⟦t⟧ ⟶ Ω'`
  have hinj : Function.Injective ((algebraMap R (genericSliceTraitField k')).comp
      (genericSliceTraitStructureMap k')) :=
    (injective_algebraMap_genericSliceTraitField k').comp
      (injective_genericSliceTraitStructureMap k')
  let ψ : F →+* genericSliceTraitField k' := IsFractionRing.lift hinj
  have hψ : (genericSliceTraitToField k').comp ψ =
      (traitGenericFieldMap k' (traitSliceField k')).comp
        (algebraMap F (traitGenericField k')) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (PowerSeries k')) ?_
    rw [RingHom.comp_assoc, RingHom.comp_assoc,
      show ψ.comp (algebraMap (PowerSeries k') F) = _ from IsLocalization.lift_comp _,
      ← RingHom.comp_assoc,
      genericSliceTraitToField_algebraMap, RingHom.comp_assoc,
      genericSliceRingHom_comp_structureMap, ← IsScalarTower.algebraMap_eq,
      traitGenericFieldMap_comp_algebraMap]
  have hz : _root_.IsIntegral F z := Algebra.IsIntegral.isIntegral z
  have h0 : minpoly F z ≠ 0 := minpoly.ne_zero hz
  have hsplit : ((minpoly F z).map ψ).Splits := IsAlgClosed.splits _
  refine hsplit.mem_range_of_isRoot ((Polynomial.map_ne_zero_iff ψ.injective).2 h0) ?_
  rw [Polynomial.map_map, hψ, ← Polynomial.map_map, Polynomial.IsRoot, Polynomial.eval_map,
    Polynomial.eval₂_at_apply, Polynomial.eval_map_algebraMap, minpoly.aeval, map_zero]

/-- The embedding `Ω ⟶ Ω'` whose composite with `ω_K : Ω' ⟶ Ω_K` is the fixed embedding
`Ω ⟶ Ω_K`. -/
noncomputable def genericSliceTraitFromField :
    traitGenericField k' →+* genericSliceTraitField k' :=
  (genericSliceTraitToField k').rangeRestrictFieldEquiv.symm.toRingHom.comp
    ((traitGenericFieldMap k' (traitSliceField k')).codRestrict _
      (traitGenericFieldMap_mem_fieldRange k'))

lemma genericSliceTraitToField_comp_fromField :
    (genericSliceTraitToField k').comp (genericSliceTraitFromField k') =
      traitGenericFieldMap k' (traitSliceField k') := by
  ext z
  exact RingHom.rangeRestrictFieldEquiv_apply_symm_apply _ _

/-- The geometric generic points of `S'` and `S` are compatible: `k'⟦t⟧ ⟶ R ⟶ Ω'` is
`k'⟦t⟧ ⟶ Ω ⟶ Ω'`. -/
lemma algebraMap_comp_genericSliceTraitStructureMap :
    (algebraMap (strictHenselization (genericSlicePoint k')) (genericSliceTraitField k')).comp
        (genericSliceTraitStructureMap k') =
      (genericSliceTraitFromField k').comp
        (algebraMap (PowerSeries k') (traitGenericField k')) := by
  ext x
  apply (genericSliceTraitToField k').injective
  have h1 := RingHom.congr_fun (genericSliceTraitToField_algebraMap k')
    (genericSliceTraitStructureMap k' x)
  have h2 := RingHom.congr_fun (genericSliceTraitToField_comp_fromField k')
    (algebraMap (PowerSeries k') (traitGenericField k') x)
  have h3 := RingHom.congr_fun (genericSliceRingHom_comp_structureMap k') x
  have h4 := RingHom.congr_fun (traitGenericFieldMap_comp_algebraMap k' (traitSliceField k')) x
  simp only [RingHom.comp_apply] at h1 h2 h3 h4 ⊢
  rw [h1, h2, h3, h4]

/-- The structure map `k'⟦t⟧ ⟶ R` is local. -/
instance isLocalHom_genericSliceTraitStructureMap :
    IsLocalHom (genericSliceTraitStructureMap k') := by
  have : IsLocalHom ((genericSliceRingHom k').comp (genericSliceTraitStructureMap k')) := by
    rw [genericSliceRingHom_comp_structureMap]
    refine ⟨fun x hx ↦ ?_⟩
    rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_map_apply] at hx
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    exact fun h ↦ hx.ne_zero (by rw [h, map_zero])
  exact isLocalHom_of_comp _ (genericSliceRingHom k')

/-- `t` is a uniformizer of the strict localization. -/
lemma maximalIdeal_strictHenselization_genericSlicePoint_eq_map :
    IsLocalRing.maximalIdeal (strictHenselization (genericSlicePoint k')) =
      (IsLocalRing.maximalIdeal (PowerSeries k')).map (genericSliceTraitStructureMap k') := by
  rw [maximalIdeal_strictHenselization_genericSlicePoint, PowerSeries.maximalIdeal_eq_span_X,
    Ideal.map_span, Set.image_singleton]
  rfl

/-- The kernel of the constant coefficient is the maximal ideal of `k'⟦t⟧`. -/
lemma ker_constantCoeff_powerSeries :
    RingHom.ker (PowerSeries.constantCoeff (R := k')) =
      IsLocalRing.maximalIdeal (PowerSeries k') := by
  ext φ
  rw [RingHom.mem_ker, PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton,
    PowerSeries.X_dvd_iff]

/-- The elements of the residue field of the strict localization algebraic over `k'` come from
`k'` (`AlgebraicGeometry.mem_range_algebraMap_residueField_sliceTraitPoint`). -/
lemma mem_range_residueField_genericSliceTraitStructureMap [IsSepClosed k'] :
    letI := (IsLocalRing.ResidueField.map (genericSliceTraitStructureMap k')).toAlgebra
    ∀ z : IsLocalRing.ResidueField (strictHenselization (genericSlicePoint k')),
      IsAlgebraic (IsLocalRing.ResidueField (PowerSeries k')) z →
        z ∈ (IsLocalRing.ResidueField.map (genericSliceTraitStructureMap k')).range := by
  have : IsSepClosed (IsLocalRing.ResidueField (PowerSeries k')) :=
    .of_ringEquiv (PowerSeries.residueFieldEquiv k')
  have key : ∀ s, s = sliceTraitPoint (PowerSeries.constantCoeff (R := k')) →
      ∀ [IsLocalHom (Spec.preimage (strictLocalizationToBase s ≫
        𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')).hom],
      letI := (IsLocalRing.ResidueField.map (Spec.preimage (strictLocalizationToBase s ≫
        𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')).hom).toAlgebra
      ∀ z : IsLocalRing.ResidueField (strictHenselization s),
        IsAlgebraic (IsLocalRing.ResidueField (PowerSeries k')) z →
          z ∈ (IsLocalRing.ResidueField.map (Spec.preimage (strictLocalizationToBase s ≫
            𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')).hom).range := by
    rintro s rfl _ z hz
    exact mem_range_algebraMap_residueField_sliceTraitPoint _ (ker_constantCoeff_powerSeries k')
      z hz
  exact @key _ (genericSlicePoint_eq_sliceTraitPoint k')
    (isLocalHom_genericSliceTraitStructureMap k')

/-- **The strict localization of `𝔸¹_S` at the generic point of its special fibre** as a generic
slice trait: `R` the strict henselization, `Ω' = (Frac R)^alg`, and `κ = K` with the evaluation
`R ⟶ K` at the geometric point. -/
noncomputable def genericSliceTraitOfStrictLocalization [IsSepClosed k'] :
    GenericSliceTrait k' where
  R := strictHenselization (genericSlicePoint k')
  Ω := genericSliceTraitField k'
  κ := traitSliceField k'
  toAffineLine := strictLocalizationToBase (genericSlicePoint k')
  weaklyEtale := weaklyEtale_strictLocalizationToBase_genericSlicePoint k'
  φ := genericSliceTraitStructureMap k'
  spec_φ := spec_genericSliceTraitStructureMap k'
  maximalIdeal_eq := maximalIdeal_strictHenselization_genericSlicePoint_eq_map k'
  mem_range_residueField := mem_range_residueField_genericSliceTraitStructureMap k'
  ι := genericSliceRingHom k'
  isLocalHom_ι := inferInstance
  injective_ι := injective_genericSliceRingHom k'
  spec_ι_comp := spec_genericSliceRingHom k'
  a := algebraMap _ _
  injective_a := injective_algebraMap_genericSliceTraitField k'
  isAlgebraic_a := isAlgebraic_genericSliceTraitField k'
  b := (strictHenselizationEval (genericSlicePoint k')).hom
  ker_b := maximalIdeal_strictHenselization.symm
  ωS := genericSliceTraitFromField k'
  ωK := genericSliceTraitToField k'
  ωK_comp_ωS := genericSliceTraitToField_comp_fromField k'
  ωK_comp_a := genericSliceTraitToField_algebraMap k'
  generic_over := by
    rw [← spec_genericSliceTraitStructureMap, traitGenericPoint, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      algebraMap_comp_genericSliceTraitStructureMap]
  κS := algebraMap k' (traitSliceField k')
  κK := RingHom.id _
  κK_comp_κS := RingHom.id_comp _
  κK_comp_b := by rw [RingHom.id_comp, constantCoeff_comp_genericSliceRingHom]
  closed_over := by
    rw [CommRingCat.ofHom_hom,
      reassoc_of% spec_map_strictHenselizationEval_comp_strictLocalizationToBase,
      genericSlicePoint, Category.assoc, traitSlice_over]
    exact traitClosedPoint_traitMap k' (traitSliceField k')
  ringChar_κ := (Algebra.ringChar_eq k' (traitSliceField k')).symm

/-- **The strict localization of `𝔸¹_S` at the generic point of its special fibre is a generic
slice trait** (EGA IV₄, 18.8; SGA 4½, [Th. finitude], 3.3). -/
theorem nonempty_genericSliceTrait [IsSepClosed k'] : Nonempty (GenericSliceTrait k') :=
  ⟨genericSliceTraitOfStrictLocalization k'⟩

end AlgebraicGeometry

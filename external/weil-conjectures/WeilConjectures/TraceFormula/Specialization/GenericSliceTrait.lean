/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.AffineSpaceSliceCartesian
public import WeilConjectures.TraceFormula.Specialization.AffineSpaceSliceModel
public import WeilConjectures.TraceFormula.Specialization.TraitChangeInvariance
public import WeilConjectures.SixFunctors.NearbyCycles.CartesianModelWeaklyEtale
public import WeilConjectures.TraceFormula.Specialization.SliceTrait

/-!

# The strict localization of `𝔸¹_S` at the generic point of its special fibre

Let `S = Spec k'⟦t⟧` and `K = k'(x)^alg` (`AlgebraicGeometry.traitSliceField`). Deligne's proof of
the finiteness of nearby cycles (SGA 4½, [Th. finitude], 3.3–3.4) slices along the strict
localization `S'` of `𝔸¹_S` at the geometric generic point `x` of its special fibre: a strictly
henselian trait, weakly étale over `𝔸¹_S`, through which the generic slice
`σ : Spec K⟦t⟧ ⟶ 𝔸¹_S` (`AlgebraicGeometry.traitSlice`) factors.

`AlgebraicGeometry.GenericSliceTrait k'` packages such a trait `S' = Spec R` with compatible
geometric generic point `Spec Ω'` and closed point `Spec κ`. For such data, the morphism of models
over the coordinate generic slice (`NearbyCyclesModel.affineSpaceSliceHom`) factors as
```
(𝔸ⁿ_{K⟦t⟧} over Spec K⟦t⟧) ──τ──→ (𝔸ⁿ⁺¹_S ×_{𝔸¹_S} S' over S') ──σ──→ (𝔸ⁿ⁺¹_S over S)
```
(`NearbyCyclesModel.genericSliceTraitChangeHom`, `NearbyCyclesModel.genericSliceTraitHom`),
where `τ` is a change of strictly henselian trait and `σ` has weakly étale morphism of total
spaces.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A **generic slice trait** of `𝔸¹_S`, `S = Spec k'⟦t⟧`: a strictly henselian trait `S' = Spec R`
with a weakly étale morphism `S' ⟶ 𝔸¹_S`, through which the generic slice
`Spec K⟦t⟧ ⟶ 𝔸¹_S` (`K = k'(x)^alg`) factors by a local injection `ι : R ⟶ K⟦t⟧`, together with a
geometric generic point `a : R ⟶ Ω'` (`Ω'` an algebraic closure of `Frac R`) and a separably
closed point `b : R ⟶ κ` compatible with those of `S` and of `Spec K⟦t⟧`. The strict
localization of `𝔸¹_S` at the generic point of its special fibre is one
(`AlgebraicGeometry.nonempty_genericSliceTrait`). It is in particular a slice trait over `S`
(`AlgebraicGeometry.GenericSliceTrait.toSliceTrait`). -/
structure GenericSliceTrait (k' : Type u) [Field k'] where
  /-- the strictly henselian discrete valuation ring `R` of `S'`. -/
  R : Type u
  [commRing : CommRing R]
  [isDomain : IsDomain R]
  [isDiscreteValuationRing : IsDiscreteValuationRing R]
  [isStrictlyHenselianLocalRing : IsStrictlyHenselianLocalRing R]
  /-- the field `Ω'` of the geometric generic point of `S'`. -/
  Ω : Type u
  [field_Ω : Field Ω]
  [isAlgClosed : IsAlgClosed Ω]
  /-- the field `κ` of the closed point of `S'`. -/
  κ : Type u
  [field_κ : Field κ]
  [isSepClosed : IsSepClosed κ]
  /-- the weakly étale morphism `S' ⟶ 𝔸¹_S`. -/
  toAffineLine : Spec (.of R) ⟶ 𝔸(ULift.{u} (Fin 1); trait k')
  weaklyEtale : WeaklyEtale toAffineLine
  /-- the structure map `k'⟦t⟧ ⟶ R`. -/
  φ : PowerSeries k' →+* R
  spec_φ : Spec.map (CommRingCat.ofHom φ) = toAffineLine ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k'
  [isLocalHom_φ : IsLocalHom φ]
  /-- `t` is a uniformizer of `R`. -/
  maximalIdeal_eq : IsLocalRing.maximalIdeal R =
    (IsLocalRing.maximalIdeal (PowerSeries k')).map φ
  /-- the elements of the residue field of `R` algebraic over `k'` come from `k'`. -/
  mem_range_residueField : letI := (IsLocalRing.ResidueField.map φ).toAlgebra
    ∀ z : IsLocalRing.ResidueField R, IsAlgebraic (IsLocalRing.ResidueField (PowerSeries k')) z →
      z ∈ (IsLocalRing.ResidueField.map φ).range
  /-- the local injection `R ⟶ K⟦t⟧` through which the generic slice factors. -/
  ι : R →+* PowerSeries (traitSliceField k')
  isLocalHom_ι : IsLocalHom ι
  injective_ι : Function.Injective ι
  spec_ι_comp : Spec.map (CommRingCat.ofHom ι) ≫ toAffineLine = traitSlice (traitSliceCoord k')
  /-- the geometric generic point `R ⟶ Ω'`. -/
  a : R →+* Ω
  injective_a : Function.Injective a
  /-- `Ω'` is algebraic over `R`, i.e. an algebraic closure of `Frac R`: so the change of
  geometric generic fibres over `S'` is a Galois layer up to universal homeomorphisms. -/
  isAlgebraic_a : letI := a.toAlgebra; Algebra.IsAlgebraic R Ω
  /-- the closed point `R ⟶ κ`. -/
  b : R →+* κ
  ker_b : RingHom.ker b = IsLocalRing.maximalIdeal R
  /-- the embedding `Ω ⟶ Ω'` of the geometric generic point of `S`. -/
  ωS : traitGenericField k' →+* Ω
  /-- the embedding `Ω' ⟶ Ω_K` into the geometric generic point of `Spec K⟦t⟧`. -/
  ωK : Ω →+* traitGenericField (traitSliceField k')
  ωK_comp_ωS : ωK.comp ωS = traitGenericFieldMap k' (traitSliceField k')
  ωK_comp_a : ωK.comp a = (algebraMap _ (traitGenericField (traitSliceField k'))).comp ι
  generic_over : Spec.map (CommRingCat.ofHom a) ≫ toAffineLine ≫
      𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' =
    Spec.map (CommRingCat.ofHom ωS) ≫ traitGenericPoint k'
  /-- the embedding `k' ⟶ κ` of residue fields. -/
  κS : k' →+* κ
  /-- the embedding `κ ⟶ K` of residue fields. -/
  κK : κ →+* traitSliceField k'
  κK_comp_κS : κK.comp κS = algebraMap k' (traitSliceField k')
  κK_comp_b : κK.comp b = PowerSeries.constantCoeff.comp ι
  closed_over : Spec.map (CommRingCat.ofHom b) ≫ toAffineLine ≫
      𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' =
    Spec.map (CommRingCat.ofHom κS) ≫ traitClosedPoint k'
  ringChar_κ : ringChar κ = ringChar k'

namespace GenericSliceTrait

attribute [instance] commRing isDomain isDiscreteValuationRing isStrictlyHenselianLocalRing field_Ω
  isAlgClosed field_κ isSepClosed weaklyEtale isLocalHom_ι isLocalHom_φ

variable {k' : Type u} [Field k'] (D : GenericSliceTrait k')

/-- The structure map `k'⟦t⟧ ⟶ R ⟶ Ω'` is `k'⟦t⟧ ⟶ Ω ⟶ Ω'`. -/
lemma ωS_comp_algebraMap :
    D.ωS.comp (algebraMap (PowerSeries k') (traitGenericField k')) = D.a.comp D.φ := by
  have h := D.generic_over
  rw [← D.spec_φ, traitGenericPoint, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp] at h
  exact (congrArg CommRingCat.Hom.hom (Spec.map_injective h)).symm

/-- The structure map `k'⟦t⟧ ⟶ R ⟶ κ` is `k'⟦t⟧ ⟶ k' ⟶ κ`. -/
lemma κS_comp_constantCoeff :
    D.κS.comp PowerSeries.constantCoeff = D.b.comp D.φ := by
  have h := D.closed_over
  rw [← D.spec_φ, traitClosedPoint, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp] at h
  exact (congrArg CommRingCat.Hom.hom (Spec.map_injective h)).symm

/-- A generic slice trait of `𝔸¹_S` is a slice trait over `S = Spec k'⟦t⟧`, with the geometric
generic point `Spec Ω ⟶ S` and the closed point `Spec k' ⟶ S`. -/
@[simps]
noncomputable def toSliceTrait :
    SliceTrait (algebraMap (PowerSeries k') (traitGenericField k'))
      (PowerSeries.constantCoeff (R := k')) where
  R := D.R
  toAffineLine := D.toAffineLine
  weaklyEtale := D.weaklyEtale
  φ := D.φ
  spec_φ := D.spec_φ
  maximalIdeal_eq := D.maximalIdeal_eq
  mem_range_residueField := D.mem_range_residueField
  Ω := D.Ω
  a := D.a
  injective_a := D.injective_a
  isAlgebraic_a := D.isAlgebraic_a
  ωS := D.ωS
  ωS_comp := D.ωS_comp_algebraMap
  κ := D.κ
  b := D.b
  ker_b := D.ker_b
  κS := D.κS
  κS_comp := D.κS_comp_constantCoeff

end GenericSliceTrait

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {k' : Type u} [Field k'] (D : GenericSliceTrait k') (n : ℕ) (i : Fin (n + 1))

/-- The total space `𝔸ⁿ⁺¹_S ×_{𝔸¹_S} S'` of the slice over the generic slice trait. -/
noncomputable abbrev genericSliceTraitTotal : Scheme.{u} :=
  pullback (affineSpaceCoordinate k' n i) D.toAffineLine

/-- The structure morphism `𝔸ⁿ⁺¹_S ×_{𝔸¹_S} S' ⟶ S'`. -/
noncomputable abbrev genericSliceTraitStructure :
    genericSliceTraitTotal D n i ⟶ Spec (.of D.R) :=
  pullback.snd _ _

/-- The projection `𝔸ⁿ⁺¹_S ×_{𝔸¹_S} S' ⟶ 𝔸ⁿ⁺¹_S`, typed by the model objects. -/
noncomputable def genericSliceTraitProj :
    genericSliceTraitTotal D n i ⟶ (affineSpaceModel k' (n + 1)).total :=
  pullback.fst _ _

/-- The **geometric model over the generic slice trait** of `𝔸ⁿ⁺¹_S ×_{𝔸¹_S} S'`: generic fibre
over `Spec Ω'`, special fibre over `Spec κ`, `ε = j`. -/
@[simps]
noncomputable def genericSliceTraitModel :
    NearbyCyclesModel (genericSliceTraitTotal D n i)
      (pullback (genericSliceTraitStructure D n i) (Spec.map (CommRingCat.ofHom D.b))) where
  total := genericSliceTraitTotal D n i
  generic := pullback (genericSliceTraitStructure D n i) (Spec.map (CommRingCat.ofHom D.a))
  j := pullback.fst _ _
  i := pullback.fst _ _
  ε := pullback.fst _ _

@[reassoc]
lemma genericSliceTrait_fst_comp_over :
    pullback.fst (affineSpaceCoordinate k' n i) D.toAffineLine ≫
        𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k' =
      genericSliceTraitStructure D n i ≫ D.toAffineLine ≫
        𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' := by
  rw [← affineSpaceCoordinate_over (k' := k') n i, pullback.condition_assoc]

/-- The map `(𝔸ⁿ⁺¹_S ×_{𝔸¹_S} S') ×_{S'} Ω' ⟶ 𝔸ⁿ⁺¹_S ×_S Ω` of geometric generic fibres. -/
noncomputable def genericSliceTraitGeneric :
    (genericSliceTraitModel D n i).generic ⟶ (affineSpaceModel k' (n + 1)).generic :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom D.ωS)) (by
      rw [Category.assoc, genericSliceTrait_fst_comp_over, pullback.condition_assoc,
        Category.assoc, D.generic_over])

/-- The map `(𝔸ⁿ⁺¹_S ×_{𝔸¹_S} S') ×_{S'} κ ⟶ 𝔸ⁿ⁺¹_S ×_S k'` of special fibres. -/
noncomputable def genericSliceTraitSpecial :
    pullback (genericSliceTraitStructure D n i) (Spec.map (CommRingCat.ofHom D.b)) ⟶
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k')).left :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom D.κS)) (by
      rw [Category.assoc, genericSliceTrait_fst_comp_over, pullback.condition_assoc,
        Category.assoc, D.closed_over])

/-- The **morphism of models from the generic slice trait** `σ`: from the geometric model of
`𝔸ⁿ⁺¹_S ×_{𝔸¹_S} S'` over `S'` to the geometric model of `𝔸ⁿ⁺¹_S` over `S`; its morphism of total
spaces is weakly étale. -/
@[simps]
noncomputable def genericSliceTraitHom :
    (genericSliceTraitModel D n i).Hom (affineSpaceModel k' (n + 1)).geometric
      (genericSliceTraitProj D n i) (genericSliceTraitSpecial D n i) where
  total := genericSliceTraitProj D n i
  generic := genericSliceTraitGeneric D n i
  comm_j := pullback.lift_fst _ _ _
  comm_i := pullback.lift_fst _ _ _
  comm_ε := pullback.lift_fst _ _ _

instance : WeaklyEtale (genericSliceTraitHom D n i).total :=
  MorphismProperty.of_isPullback (P := @WeaklyEtale) (IsPullback.of_hasPullback _ _).flip
    D.weaklyEtale

/-- The morphism `𝔸ⁿ_{K⟦t⟧} ⟶ 𝔸ⁿ⁺¹_S ×_{𝔸¹_S} S'` induced by the coordinate generic slice. -/
noncomputable def genericSliceTraitChangeTotal :
    (affineSpaceModel (traitSliceField k') n).total ⟶ genericSliceTraitTotal D n i :=
  pullback.lift (affineSpaceSliceTotal k' n i)
    (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘ trait (traitSliceField k') ≫
      Spec.map (CommRingCat.ofHom D.ι)) (by
      rw [affineSpaceSliceTotal, affineSpaceSlice_comp_affineSpaceCoordinate, Category.assoc,
        D.spec_ι_comp])

@[reassoc (attr := simp)]
lemma genericSliceTraitChangeTotal_fst :
    genericSliceTraitChangeTotal D n i ≫ pullback.fst _ _ = affineSpaceSliceTotal k' n i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma genericSliceTraitChangeTotal_snd :
    genericSliceTraitChangeTotal D n i ≫ genericSliceTraitStructure D n i =
      𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘ trait (traitSliceField k') ≫
        Spec.map (CommRingCat.ofHom D.ι) :=
  pullback.lift_snd _ _ _

/-- The square of total spaces of the change of trait `Spec K⟦t⟧ ⟶ S'` is cartesian:
`𝔸ⁿ_{K⟦t⟧} = (𝔸ⁿ⁺¹_S ×_{𝔸¹_S} S') ×_{S'} Spec K⟦t⟧`. -/
lemma isPullback_genericSliceTraitChangeTotal :
    IsPullback (genericSliceTraitChangeTotal D n i)
      (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘ trait (traitSliceField k'))
      (genericSliceTraitStructure D n i) (Spec.map (CommRingCat.ofHom D.ι)) := by
  have h := isPullback_affineSpaceSlice (k' := k') n i (traitSliceCoord k')
  rw [← D.spec_ι_comp] at h
  refine IsPullback.of_right ?_ (genericSliceTraitChangeTotal_snd D n i)
    (IsPullback.of_hasPullback (affineSpaceCoordinate k' n i) D.toAffineLine)
  rw [genericSliceTraitChangeTotal_fst]
  exact h

/-- The map `𝔸ⁿ_{K⟦t⟧} ×_{K⟦t⟧} Ω_K ⟶ (𝔸ⁿ⁺¹_S ×_{𝔸¹_S} S') ×_{S'} Ω'` of geometric generic
fibres. -/
noncomputable def genericSliceTraitChangeGeneric :
    (affineSpaceModel (traitSliceField k') n).generic ⟶ (genericSliceTraitModel D n i).generic :=
  pullback.lift (pullback.fst _ _ ≫ genericSliceTraitChangeTotal D n i)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom D.ωK)) (by
      rw [Category.assoc, genericSliceTraitChangeTotal_snd, pullback.condition_assoc,
        Category.assoc]
      congr 1
      simp only [traitGenericPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp, D.ωK_comp_a])

/-- The map `𝔸ⁿ_{K⟦t⟧} ×_{K⟦t⟧} K ⟶ (𝔸ⁿ⁺¹_S ×_{𝔸¹_S} S') ×_{S'} κ` of special fibres. -/
noncomputable def genericSliceTraitChangeSpecial :
    (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘
        trait (traitSliceField k'))).left ⟶
      pullback (genericSliceTraitStructure D n i) (Spec.map (CommRingCat.ofHom D.b)) :=
  pullback.lift (pullback.fst _ _ ≫ genericSliceTraitChangeTotal D n i)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom D.κK)) (by
      rw [Category.assoc, genericSliceTraitChangeTotal_snd, pullback.condition_assoc,
        Category.assoc]
      congr 1
      simp only [traitClosedPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp, D.κK_comp_b])

/-- The **change of trait to the generic slice trait** `τ`: from the geometric model of
`𝔸ⁿ_{K⟦t⟧}` over `Spec K⟦t⟧` to the geometric model of `𝔸ⁿ⁺¹_S ×_{𝔸¹_S} S'` over `S'`, along the
morphism of strictly henselian traits `Spec K⟦t⟧ ⟶ S'`. -/
@[simps]
noncomputable def genericSliceTraitChangeHom :
    (affineSpaceModel (traitSliceField k') n).geometric.Hom (genericSliceTraitModel D n i)
      (genericSliceTraitChangeTotal D n i) (genericSliceTraitChangeSpecial D n i) where
  total := genericSliceTraitChangeTotal D n i
  generic := genericSliceTraitChangeGeneric D n i
  comm_j := pullback.lift_fst _ _ _
  comm_i := pullback.lift_fst _ _ _
  comm_ε := pullback.lift_fst _ _ _

/-- The composite `τ ≫ σ` has the total map of the coordinate generic slice. -/
lemma genericSliceTraitChangeTotal_comp :
    genericSliceTraitChangeTotal D n i ≫ genericSliceTraitProj D n i =
      affineSpaceSliceTotal k' n i :=
  genericSliceTraitChangeTotal_fst D n i

/-- The composite `τ ≫ σ` has the generic map of the coordinate generic slice. -/
lemma genericSliceTraitChangeGeneric_comp :
    genericSliceTraitChangeGeneric D n i ≫ genericSliceTraitGeneric D n i =
      affineSpaceSliceGeneric k' n i := by
  apply pullback.hom_ext
  · simp [genericSliceTraitChangeGeneric, genericSliceTraitGeneric, affineSpaceSliceGeneric]
  · simp only [genericSliceTraitChangeGeneric, genericSliceTraitGeneric, affineSpaceSliceGeneric,
      Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, D.ωK_comp_ωS]
    rfl

/-- The composite `τ ≫ σ` has the special map of the coordinate generic slice. -/
lemma genericSliceTraitChangeSpecial_comp :
    genericSliceTraitChangeSpecial D n i ≫ genericSliceTraitSpecial D n i =
      affineSpaceSliceSpecialFibre k' n i := by
  apply pullback.hom_ext
  · simp [genericSliceTraitChangeSpecial, genericSliceTraitSpecial, affineSpaceSliceSpecialFibre,
      affineSpaceSliceTotal, traitStdSpecialFibre]
  · simp only [genericSliceTraitChangeSpecial, genericSliceTraitSpecial,
      affineSpaceSliceSpecialFibre, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, D.κK_comp_κS]
    simp [traitStdSpecialFibre, affineSpaceSliceSpecial]

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

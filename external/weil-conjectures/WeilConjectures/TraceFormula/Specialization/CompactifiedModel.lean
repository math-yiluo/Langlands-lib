/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.Compactification
public import WeilConjectures.TraceFormula.Specialization.DeformationModelGeneric
public import WeilConjectures.TraceFormula.Specialization.PointModel
public import WeilConjectures.TraceFormula.Specialization.TraitModelInstances

/-!

# The compactified deformation to the normal cone as a model over a trait

Let `X` be a proper scheme over a field `k`, `x` a rational point of `X`, and `k'` an extension
of `k`. The deformation to the normal cone `D_x X ⟶ 𝔸¹_k` of `x` has a dense relative
compactification `D_x X ⟶ P ⟶ 𝔸¹_k` which does not change it over the punctured line `𝔾_{m,k}`
(`AlgebraicGeometry.Scheme.Hom.deformationCompactification`). Base changing `P` along the
coordinate `t : S = Spec k'⟦t⟧ ⟶ 𝔸¹_k` gives a proper scheme `𝒫 = P ×_{𝔸¹_k} S` over the trait
(`AlgebraicGeometry.ProEtale.CondensedRing.compactifiedTotal`). Since the generic point of the
trait lies over `𝔾_{m,k}` (`AlgebraicGeometry.traitGenericPointToPuncturedLine`), the geometric
generic fibre of `𝒫` maps to `X`, and `𝒫` is a nearby cycles model of `X`
(`AlgebraicGeometry.ProEtale.CondensedRing.compactifiedDeformationModel`) of finite type over the
trait.

The deformation model `𝒳 = D_x X ×_{𝔸¹_k} S`
(`AlgebraicGeometry.ProEtale.CondensedRing.deformationModel`) is an open submodel of `𝒫`
(`AlgebraicGeometry.ProEtale.CondensedRing.deformationToCompactifiedModelHom`), and `𝒫` is a
proper model over the trait itself
(`AlgebraicGeometry.ProEtale.CondensedRing.compactifiedToTraitModelHom`).

## Main definitions

- `AlgebraicGeometry.ProEtale.CondensedRing.compactifiedDeformationModel`: the model `𝒫`.
- `AlgebraicGeometry.ProEtale.CondensedRing.isTraitModel_compactifiedDeformationModel`: it is of
  finite type over the trait.
- `AlgebraicGeometry.ProEtale.CondensedRing.deformationToCompactifiedModelHom`: the open
  immersion `𝒳 ⟶ 𝒫` of models.
- `AlgebraicGeometry.ProEtale.CondensedRing.compactifiedToTraitModelHom`: the proper morphism of
  models `𝒫 ⟶ S`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section Trait

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k']

/-- The coordinate `t` pulled back to the geometric generic point of the trait is the image of
the uniformiser `t` of `k'⟦t⟧` in `Ω`. -/
lemma traitGenericPoint_traitToAffineLine_appTop_coord :
    (traitGenericPoint k' ≫ traitToAffineLine k k').appTop
        (AffineSpace.coord (Spec (.of k)) 0) =
      (Scheme.ΓSpecIso (.of (traitGenericField k'))).inv
        (algebraMap (PowerSeries k') (traitGenericField k') PowerSeries.X) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, traitToAffineLine,
    AffineSpace.homOfVector_appTop_coord, traitGenericPoint, ← CommRingCat.comp_apply,
    ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  rfl

/-- The uniformiser `t` of `k'⟦t⟧` is nonzero in the field `Ω = (Frac k'⟦t⟧)^alg`. -/
lemma algebraMap_traitGenericField_X_ne_zero :
    algebraMap (PowerSeries k') (traitGenericField k') PowerSeries.X ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply (PowerSeries k') (FractionRing (PowerSeries k'))]
  refine (map_ne_zero _).2 ?_
  rw [Ne, IsFractionRing.to_map_eq_zero_iff]
  exact PowerSeries.X_ne_zero

end Trait

namespace ProEtale.CondensedRing

open Scheme

section Model

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) [IsProper X.hom] (x : RationalPoint X)
  (k' : Type u) [Field k'] [Algebra k k']

/-- The dense relative compactification `D_x X ⟶ P ⟶ 𝔸¹_k` of the deformation to the normal cone
of a rational point `x` of a proper `k`-scheme `X`. -/
noncomputable def deformationCompactificationOf :
    Compactification (deformationSpaceToAffineLine X x.left.ker) :=
  have := LocallyOfFiniteType.isLocallyNoetherian X.hom
  X.hom.deformationCompactification x.left

/-- Over the punctured line `𝔾_{m,k}`, the compactification `P` is `X ×_k 𝔾_{m,k}`. -/
lemma isPullback_deformationCompactificationOf :
    IsPullback (X.hom.deformationSpaceGeneric x.left ≫ (deformationCompactificationOf X x).i)
      (pullback.snd _ _) (deformationCompactificationOf X x).g
      (Scheme.Hom.puncturedLine _).ι :=
  have := LocallyOfFiniteType.isLocallyNoetherian X.hom
  X.hom.isPullback_deformationCompactification_puncturedLine x.left

/-- The total space `𝒫 = P ×_{𝔸¹_k} Spec k'⟦t⟧` of the compactified deformation to the normal
cone over the trait. -/
noncomputable def compactifiedTotal : Scheme.{u} :=
  pullback (deformationCompactificationOf X x).g (traitToAffineLine k k')

/-- The projection `𝒫 ⟶ P`. -/
noncomputable def compactifiedTotalToSpace :
    compactifiedTotal X x k' ⟶ (deformationCompactificationOf X x).Z :=
  pullback.fst _ _

/-- The structure morphism `𝒫 ⟶ Spec k'⟦t⟧`; it is proper. -/
noncomputable def compactifiedTotalToTrait : compactifiedTotal X x k' ⟶ trait k' :=
  pullback.snd _ _

lemma isPullback_compactifiedTotal :
    IsPullback (compactifiedTotalToSpace X x k') (compactifiedTotalToTrait X x k')
      (deformationCompactificationOf X x).g (traitToAffineLine k k') :=
  IsPullback.of_hasPullback _ _

instance : IsProper (compactifiedTotalToTrait X x k') :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- The geometric generic fibre `𝒫 ×_S Spec Ω`. -/
noncomputable def compactifiedGeneric : Scheme.{u} :=
  pullback (compactifiedTotalToTrait X x k') (traitGenericPoint k')

/-- The inclusion `j : 𝒫_Ω ⟶ 𝒫` of the geometric generic fibre. -/
noncomputable def compactifiedGenericToTotal :
    compactifiedGeneric X x k' ⟶ compactifiedTotal X x k' :=
  pullback.fst _ _

/-- The structure morphism `𝒫_Ω ⟶ Spec Ω` of the geometric generic fibre. -/
noncomputable def compactifiedGenericToPoint :
    compactifiedGeneric X x k' ⟶ Spec (.of (traitGenericField k')) :=
  pullback.snd _ _

lemma isPullback_compactifiedGeneric :
    IsPullback (compactifiedGenericToTotal X x k') (compactifiedGenericToPoint X x k')
      (compactifiedTotalToTrait X x k') (traitGenericPoint k') :=
  IsPullback.of_hasPullback _ _

/-- The special fibre `𝒫 ×_S Spec k'`, as a `k'`-scheme. -/
noncomputable def compactifiedSpecialFibre : Over (Spec (.of k')) :=
  Over.mk (pullback.snd (compactifiedTotalToTrait X x k') (traitClosedPoint k'))

/-- The inclusion `i : 𝒫_s ⟶ 𝒫` of the special fibre. -/
noncomputable def compactifiedSpecialToTotal :
    (compactifiedSpecialFibre X x k').left ⟶ compactifiedTotal X x k' :=
  pullback.fst _ _

lemma isPullback_compactifiedSpecialFibre :
    IsPullback (compactifiedSpecialToTotal X x k') (compactifiedSpecialFibre X x k').hom
      (compactifiedTotalToTrait X x k') (traitClosedPoint k') :=
  IsPullback.of_hasPullback _ _

instance : IsProper (compactifiedSpecialFibre X x k').hom :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- The geometric generic fibre `𝒫_Ω` lies over the punctured line in `P`. -/
lemma compactifiedGeneric_w :
    (compactifiedGenericToTotal X x k' ≫ compactifiedTotalToSpace X x k') ≫
        (deformationCompactificationOf X x).g =
      (compactifiedGenericToPoint X x k' ≫ traitGenericPointToPuncturedLine k k') ≫
        (Scheme.Hom.puncturedLine _).ι := by
  rw [Category.assoc, (isPullback_compactifiedTotal X x k').w,
    (isPullback_compactifiedGeneric X x k').w_assoc, Category.assoc,
    traitGenericPointToPuncturedLine_ι]

/-- The map `𝒫_Ω ⟶ X ×_k 𝔾_{m,k}` of the geometric generic fibre to the punctured part of `P`. -/
noncomputable def compactifiedGenericToPunctured :
    compactifiedGeneric X x k' ⟶
      pullback X.hom ((Scheme.Hom.puncturedLine _).ι ≫
        𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) :=
  (isPullback_deformationCompactificationOf X x).lift _ _ (compactifiedGeneric_w X x k')

@[reassoc (attr := simp)]
lemma compactifiedGenericToPunctured_snd :
    compactifiedGenericToPunctured X x k' ≫ pullback.snd _ _ =
      compactifiedGenericToPoint X x k' ≫ traitGenericPointToPuncturedLine k k' :=
  IsPullback.lift_snd _ _ _ _

@[reassoc]
lemma compactifiedGenericToPunctured_generic :
    compactifiedGenericToPunctured X x k' ≫ X.hom.deformationSpaceGeneric x.left ≫
        (deformationCompactificationOf X x).i =
      compactifiedGenericToTotal X x k' ≫ compactifiedTotalToSpace X x k' :=
  IsPullback.lift_fst _ _ _ _

/-- The identification `ε : 𝒫_Ω ⟶ X ×_k 𝔾_{m,k} ⟶ X` of the geometric generic fibre. -/
noncomputable def compactifiedGenericToBase : compactifiedGeneric X x k' ⟶ X.left :=
  compactifiedGenericToPunctured X x k' ≫ pullback.fst _ _

/-- The compactified deformation to the normal cone of a rational point `x` of a proper `k`-scheme
`X`, base changed to the trait `Spec k'⟦t⟧`, as a nearby cycles model of `X`: the total space
`𝒫 = P ×_{𝔸¹_k} Spec k'⟦t⟧`, its geometric generic fibre, its special fibre, and
`ε : 𝒫_Ω ⟶ X ×_k 𝔾_{m,k} ⟶ X`. -/
noncomputable def compactifiedDeformationModel :
    NearbyCyclesModel X.left (compactifiedSpecialFibre X x k').left where
  total := compactifiedTotal X x k'
  generic := compactifiedGeneric X x k'
  j := compactifiedGenericToTotal X x k'
  i := compactifiedSpecialToTotal X x k'
  ε := compactifiedGenericToBase X x k'

@[simp]
lemma compactifiedDeformationModel_total :
    (compactifiedDeformationModel X x k').total = compactifiedTotal X x k' :=
  rfl

@[simp]
lemma compactifiedDeformationModel_generic :
    (compactifiedDeformationModel X x k').generic = compactifiedGeneric X x k' :=
  rfl

@[simp]
lemma compactifiedDeformationModel_j :
    (compactifiedDeformationModel X x k').j = compactifiedGenericToTotal X x k' :=
  rfl

@[simp]
lemma compactifiedDeformationModel_i :
    (compactifiedDeformationModel X x k').i = compactifiedSpecialToTotal X x k' :=
  rfl

@[simp]
lemma compactifiedDeformationModel_ε :
    (compactifiedDeformationModel X x k').ε = compactifiedGenericToBase X x k' :=
  rfl

/-- The compactified deformation model is a model of finite type over the trait; its total space
is even proper over the trait. -/
theorem isTraitModel_compactifiedDeformationModel :
    (compactifiedDeformationModel X x k').IsTraitModel :=
  ⟨⟨compactifiedTotalToTrait X x k', compactifiedGenericToPoint X x k', inferInstance,
    inferInstance, inferInstance, isPullback_compactifiedGeneric X x k',
    isPullback_compactifiedSpecialFibre X x k'⟩⟩

/-! ### The deformation model is an open submodel -/

/-- The open immersion `𝒳 ⟶ 𝒫` of total spaces, the base change of `D_x X ⟶ P`. -/
noncomputable def deformationTotalToCompactified :
    deformationTotal X x.left.ker k' ⟶ compactifiedTotal X x k' :=
  pullback.map _ _ _ _ (deformationCompactificationOf X x).i (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, ← (deformationCompactificationOf X x).comm])
    (by rw [Category.comp_id, Category.id_comp])

instance : IsOpenImmersion (deformationTotalToCompactified X x k') := by
  unfold deformationTotalToCompactified; infer_instance

@[reassoc (attr := simp)]
lemma deformationTotalToCompactified_toSpace :
    deformationTotalToCompactified X x k' ≫ compactifiedTotalToSpace X x k' =
      deformationTotalToSpace X x.left.ker k' ≫ (deformationCompactificationOf X x).i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma deformationTotalToCompactified_toTrait :
    deformationTotalToCompactified X x k' ≫ compactifiedTotalToTrait X x k' =
      deformationTotalToTrait X x.left.ker k' :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The open immersion `𝒳_Ω ⟶ 𝒫_Ω` of geometric generic fibres. -/
noncomputable def deformationGenericToCompactified :
    deformationGeneric X x.left.ker k' ⟶ compactifiedGeneric X x k' :=
  pullback.map _ _ _ _ (deformationTotalToCompactified X x k') (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, deformationTotalToCompactified_toTrait])
    (by rw [Category.comp_id, Category.id_comp])

instance : IsOpenImmersion (deformationGenericToCompactified X x k') := by
  unfold deformationGenericToCompactified; infer_instance

@[reassoc (attr := simp)]
lemma deformationGenericToCompactified_toTotal :
    deformationGenericToCompactified X x k' ≫ compactifiedGenericToTotal X x k' =
      deformationGenericToTotal X x.left.ker k' ≫ deformationTotalToCompactified X x k' :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma deformationGenericToCompactified_toPoint :
    deformationGenericToCompactified X x k' ≫ compactifiedGenericToPoint X x k' =
      pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The underlying morphism of schemes of the open immersion `𝒳_s ⟶ 𝒫_s` of special fibres. -/
noncomputable def deformationSpecialToCompactified :
    (deformationSpecialFibre X x.left.ker k').left ⟶ (compactifiedSpecialFibre X x k').left :=
  pullback.map _ _ _ _ (deformationTotalToCompactified X x k') (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, deformationTotalToCompactified_toTrait])
    (by rw [Category.comp_id, Category.id_comp])

/-- The open immersion `𝒳_s ⟶ 𝒫_s` of special fibres over `k'`. -/
noncomputable def deformationSpecialFibreToCompactified :
    deformationSpecialFibre X x.left.ker k' ⟶ compactifiedSpecialFibre X x k' :=
  Over.homMk (deformationSpecialToCompactified X x k')
    ((pullback.lift_snd _ _ _).trans (Category.comp_id _))

instance : IsOpenImmersion (deformationSpecialFibreToCompactified X x k').left := by
  change IsOpenImmersion (deformationSpecialToCompactified X x k')
  unfold deformationSpecialToCompactified
  infer_instance

@[reassoc (attr := simp)]
lemma deformationSpecialFibreToCompactified_toTotal :
    (deformationSpecialFibreToCompactified X x k').left ≫ compactifiedSpecialToTotal X x k' =
      deformationSpecialToTotal X x.left.ker k' ≫ deformationTotalToCompactified X x k' :=
  pullback.lift_fst _ _ _

omit [IsProper X.hom] in
/-- The geometric generic fibre `𝒳_Ω` lies over the punctured line in `D_x X`. -/
lemma deformationGeneric_w :
    (deformationGenericToTotal X x.left.ker k' ≫ deformationTotalToSpace X x.left.ker k') ≫
        X.hom.deformationSpaceProj x.left =
      (pullback.snd _ _ ≫ traitGenericPointToPuncturedLine k k') ≫
        (Scheme.Hom.puncturedLine _).ι := by
  have h := (IsPullback.of_hasPullback (deformationTotalToTrait X x.left.ker k')
    (traitGenericPoint k')).w
  rw [Category.assoc, ← deformationSpaceToAffineLine_eq, (isPullback_deformationTotal _ _ k').w,
    Category.assoc, traitGenericPointToPuncturedLine_ι]
  have h' := h =≫ traitToAffineLine k k'
  simp only [Category.assoc] at h'
  exact h'

/-- On geometric generic fibres, the open immersion `𝒳_Ω ⟶ 𝒫_Ω` is compatible with the
identifications with `X`: over `𝔾_{m,k}`, both `D_x X` and `P` are `X ×_k 𝔾_{m,k}`. -/
lemma deformationGenericToCompactified_toBase :
    deformationGenericToCompactified X x k' ≫ compactifiedGenericToBase X x k' =
      (deformationModel X x.left.ker k').ε := by
  have hP := X.hom.isPullback_deformationSpaceGeneric x.left
  have hl : deformationGenericToCompactified X x k' ≫ compactifiedGenericToPunctured X x k' =
      hP.lift _ _ (deformationGeneric_w X x k') := by
    refine (isPullback_deformationCompactificationOf X x).hom_ext ?_ ?_
    · rw [Category.assoc, compactifiedGenericToPunctured_generic,
        deformationGenericToCompactified_toTotal_assoc, deformationTotalToCompactified_toSpace,
        hP.lift_fst_assoc, Category.assoc]
    · rw [Category.assoc, compactifiedGenericToPunctured_snd,
        deformationGenericToCompactified_toPoint_assoc, hP.lift_snd]
  rw [compactifiedGenericToBase, reassoc_of% hl, deformationModel_ε, deformationTotalToBase,
    ← Scheme.Hom.deformationSpaceGeneric_toBase X.hom x.left, hP.lift_fst_assoc, Category.assoc]

/-- The deformation model `𝒳` is an open submodel of the compactified deformation model `𝒫`, over
the identity of `X` and the open immersion of special fibres. Its total map is an open
immersion (`deformationTotalToCompactified`). -/
noncomputable def deformationToCompactifiedModelHom :
    (deformationModel X x.left.ker k').Hom (compactifiedDeformationModel X x k') (𝟙 _)
      (deformationSpecialFibreToCompactified X x k').left where
  total := deformationTotalToCompactified X x k'
  generic := deformationGenericToCompactified X x k'
  comm_j := deformationGenericToCompactified_toTotal X x k'
  comm_i := deformationSpecialFibreToCompactified_toTotal X x k'
  comm_ε := by
    rw [Category.comp_id]
    exact deformationGenericToCompactified_toBase X x k'

@[simp]
lemma deformationToCompactifiedModelHom_total :
    (deformationToCompactifiedModelHom X x k').total = deformationTotalToCompactified X x k' :=
  rfl

@[simp]
lemma deformationToCompactifiedModelHom_generic :
    (deformationToCompactifiedModelHom X x k').generic =
      deformationGenericToCompactified X x k' :=
  rfl

instance : IsOpenImmersion (deformationToCompactifiedModelHom X x k').total :=
  inferInstanceAs (IsOpenImmersion (deformationTotalToCompactified X x k'))

/-! ### The compactified model is proper over the trait -/

/-- The identification `ε` of the geometric generic fibre lies over `Spec Ω ⟶ Spec k`. -/
@[reassoc]
lemma compactifiedGenericToBase_hom :
    compactifiedGenericToBase X x k' ≫ X.hom =
      compactifiedGenericToPoint X x k' ≫ (traitModel k k').ε := by
  rw [compactifiedGenericToBase, Category.assoc, pullback.condition,
    compactifiedGenericToPunctured_snd_assoc, ← traitModel_j_traitToBase,
    traitGenericPointToPuncturedLine_ι_assoc, traitToAffineLine_over]
  rfl

/-- The compactified deformation model `𝒫` maps to the trait model `S` over the structure
morphisms of `X` and of the special fibre. Its total map `𝒫 ⟶ S` is proper. -/
noncomputable def compactifiedToTraitModelHom :
    (compactifiedDeformationModel X x k').Hom (traitModel k k') (toPoint X).left
      (compactifiedSpecialFibre X x k').hom where
  total := compactifiedTotalToTrait X x k'
  generic := compactifiedGenericToPoint X x k'
  comm_j := (isPullback_compactifiedGeneric X x k').w.symm
  comm_i := (isPullback_compactifiedSpecialFibre X x k').w.symm
  comm_ε := by rw [toPoint_left]; exact (compactifiedGenericToBase_hom X x k').symm

@[simp]
lemma compactifiedToTraitModelHom_total :
    (compactifiedToTraitModelHom X x k').total = compactifiedTotalToTrait X x k' :=
  rfl

instance : IsProper (compactifiedToTraitModelHom X x k').total :=
  inferInstanceAs (IsProper (compactifiedTotalToTrait X x k'))

end Model

end ProEtale.CondensedRing

end AlgebraicGeometry

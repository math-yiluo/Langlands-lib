/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Common.CommonStageInclusionTensorNaturality
public import WeilConjectures.SixFunctors.Common.CommonProjectionPullbackStages

/-! # Mapping finite tensor models through the pullback stage morphism -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
set_option allowUnsafeReducibility true in
attribute [local reducible] StageSystem.pairFunctorCoherent
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  StageSystem.instCategoryPairCategory Functor.category
attribute [local irreducible] StageSystem.PairCategory.categoryStruct rationalDerivedPullback
  rationalDerivedTensor commonStageDerivedPullback
  commonStagePullbackComparison commonStageTensorComparison operationStageTransitionIso
set_option allowUnsafeReducibility true in
attribute [local irreducible] ScalarLocalization.category
  ObjectProperty.FullSubcategory.category Scheme.residueField Padic
  ScalarLocalization.composition

private theorem map_isoToStage
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C D : I → Type*} [∀ i, Category* (C i)] [∀ i, Category* (D i)]
    {S : StageSystem C} {T : StageSystem D} (F : S.Morphism T)
    (P : S.PairCategory) {E : I} (h : P.stage ≤ E) :
    F.functor.map (S.isoToStage P h).hom =
      (T.isoToStage (F.functor.obj P) h).hom ≫
        (T.ι E).map ((F.β h).hom.app P.obj) := by
  rcases P with ⟨i, K⟩
  dsimp only [StageSystem.isoToStage]
  erw [StageSystem.ι_map_eq (le_rfl : E ≤ E), F.functor_map_mkHom,
    StageSystem.PairCategory.mkHom_comp_mkHom]
  congr 1
  dsimp only [StageSystem.Morphism.mapAt]
  have hc := F.coh h (le_rfl : E ≤ E) K
  have hc' := congrArg (fun t ↦
    ((T.assoc h (le_rfl : E ≤ E)).inv.app ((F.Φ i).obj K)) ≫ t ≫
      (F.Φ E).map ((S.assoc h (le_rfl : E ≤ E)).inv.app K) ≫
        (F.β (le_rfl : E ≤ E)).inv.app ((S.T h).obj K)) hc
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app] at hc'
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app,
    Category.comp_id, Iso.inv_hom_id_app_assoc] at hc'
  exact hc'.symm

private theorem stage_model_map
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C D : I → Type*} [∀ i, Category* (C i)] [∀ i, Category* (D i)]
    {S : StageSystem C} {T : StageSystem D} (F : S.Morphism T)
    (K K₀ : S.PairCategory) (e : K = K₀) {E : I} (h : K₀.stage ≤ E)
    {P : C E} (c : K₀.toStage h ≅ P)
    (b : (F.functor.obj K₀).toStage h ≅ (F.Φ E).obj (K₀.toStage h))
    (hb : (F.β h).app K₀.obj = b) :
    F.functor.map
      (eqToIso e ≪≫ S.isoToStage K₀ h ≪≫ (S.ι E).mapIso c).hom =
      (eqToIso (congrArg F.functor.obj e) ≪≫
        T.isoToStage (F.functor.obj K₀) h ≪≫
        (T.ι E).mapIso (b ≪≫ (F.Φ E).mapIso c)).hom := by
  subst b
  subst K
  simp only [eqToIso_refl, Iso.refl_trans, Iso.trans_hom, Functor.map_comp,
    Functor.mapIso_hom]
  rw [map_isoToStage F K₀ h, F.functor_map_ι]
  exact (Category.assoc
    (T.isoToStage (F.functor.obj K₀) h).hom
    ((T.ι E).map ((F.β h).hom.app K₀.obj))
    ((T.ι E).map ((F.Φ E).map c.hom))).trans
      (congrArg (fun k ↦ (T.isoToStage (F.functor.obj K₀) h).hom ≫ k)
        ((T.ι E).map_comp ((F.β h).hom.app K₀.obj)
          ((F.Φ E).map c.hom)).symm)

set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] sfIntegralConstructible ScalarLocalization.linear
  ScalarLocalization.preadditive Linear.homModule Preadditive.homGroup
  Preadditive.fullSubcategory Linear.fullSubcategory sfIntegralConstructibleLinear
  sfRationalScalarExtension sfConstructibleIntegralScalarExtension
  sfIntegralScalarComp sfIntegralScalarUnit
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

section Models
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X Y : Scheme.{u}} (f : X ⟶ Y)
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

private theorem inclusionTensorStage_le
    (W : Scheme.{u}) [∀ x : W, Invertible (l : W.residueField x)]
    (E : AlgebraicallyClosedCoefficients.Index l Ω) (M N : Stage l Ω W E) :
    (commonStageTensorObject l Ω W ((inclusion E).obj M) ((inclusion E).obj N)).stage ≤ E := by
  change E.val ⊔ E.val ≤ E.val
  exact sup_le le_rfl le_rfl

private theorem commonProjectionPullbackStages_β_app
    (hc : StageSystem.pairFunctorCoherent (stageSystem l Ω Y) (stageSystem l Ω X)
      (fun L ↦ rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient l Ω L) f)
      (commonStagePullbackTransition l Ω f))
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : P.stage ≤ L) :
    ((commonProjectionPullbackStages l Ω f hc).β h).app P.obj =
      commonStagePullbackComparison l Ω f P L h := by
  unfold commonProjectionPullbackStages commonStagePullbackComparison commonStagePullbackTransition
  apply Iso.ext
  rfl

/-- Mapping the finite tensor model through the prescribed coherent pullback.
Source: thm-sf-pf-field.proof.md, Compatibility; stage-system coherence.
(blueprint: lem-sf-common-projection-pullback-tensor-model-map).
Proof: express the tensor model as its object-identification, its change-of-stage
isomorphism and its finite-stage tensor comparison. The coherent stage morphism
maps the middle isomorphism to the target change of stage followed by its transition
comparison. It commutes with inclusion on the final finite-stage arrow. -/
theorem commonProjectionPullbackTensorModelMap
    (hc : StageSystem.pairFunctorCoherent (stageSystem l Ω Y) (stageSystem l Ω X)
      (fun E ↦ rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient l Ω E) f)
      (commonStagePullbackTransition l Ω f))
    (E : AlgebraicallyClosedCoefficients.Index l Ω) (M N : Stage l Ω Y E) :
    let G := (commonProjectionPullbackStages l Ω f hc).functor
    let P := (inclusion (Y := Y) E).obj M
    let Q := (inclusion (Y := Y) E).obj N
    let O := commonStageTensorObject l Ω Y P Q
    let h := (by change E.val ⊔ E.val ≤ E.val; exact sup_le le_rfl le_rfl)
    G.map (commonInclusionTensorModel l Ω Y E M N).hom =
      (eqToIso (congrArg G.obj
          ((commonStageDerivedTensor_existsUnique l Ω Y).exists.choose_spec.1 P Q)) ≪≫
        (stageSystem l Ω X).isoToStage (commonStagePullbackObject l Ω f O) h ≪≫
        (inclusion (Y := X) E).mapIso
          (commonStagePullbackComparison l Ω f O E h ≪≫
            (rationalDerivedPullback l
              (AlgebraicallyClosedCoefficients.Coefficient l Ω E) f).mapIso
              (commonStageTensorComparison l Ω Y P Q E h))).hom := by
  dsimp only
  unfold commonInclusionTensorModel
  have hh := stage_model_map
    (S := stageSystem l Ω Y) (T := stageSystem l Ω X)
    (commonProjectionPullbackStages l Ω f hc)
    ((commonStageDerivedTensor l Ω Y).obj ((inclusion E).obj M, (inclusion E).obj N))
    (commonStageTensorObject l Ω Y ((inclusion E).obj M) ((inclusion E).obj N))
    ((commonStageDerivedTensor_existsUnique l Ω Y).exists.choose_spec.1
      ((inclusion E).obj M) ((inclusion E).obj N))
    (inclusionTensorStage_le l Ω Y E M N)
    (commonStageTensorComparison l Ω Y ((inclusion E).obj M) ((inclusion E).obj N)
      E (inclusionTensorStage_le l Ω Y E M N))
    (commonStagePullbackComparison l Ω f
      (commonStageTensorObject l Ω Y ((inclusion E).obj M) ((inclusion E).obj N)) E
      (inclusionTensorStage_le l Ω Y E M N))
    (commonProjectionPullbackStages_β_app l Ω f hc
      (commonStageTensorObject l Ω Y ((inclusion E).obj M) ((inclusion E).obj N)) E
      (inclusionTensorStage_le l Ω Y E M N))
  exact hh

end Models
end WeilConjectures

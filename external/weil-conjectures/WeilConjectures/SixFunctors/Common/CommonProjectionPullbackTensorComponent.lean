/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Common.CommonProjectionPullbackTensorOperations
import WeilConjectures.SixFunctors.Common.CommonProjectionPullbackTensorTransport
import WeilConjectures.SixFunctors.Common.CommonProjectionPullbackTensorModels
import WeilConjectures.SixFunctors.Common.CommonProjectionPullbackCoherence
import WeilConjectures.SixFunctors.Common.CommonProjectionPullbackStageNormalization
import WeilConjectures.SixFunctors.Common.CommonProjectionTensorComparisonNormalization
import all Mathlib.Logic.Small.Defs

/-! # Normalization and finite-stage cancellation for a tensor/pullback component -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option Elab.async false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option linter.style.haveILetI false

universe u v w v' w'
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients

private theorem addTensorIdentities
    {A : Type*} [Category* A] (R : A × A ⥤ A) {K L M N : A}
    (x : K ⟶ R.obj (M, N)) (y : K ⟶ L) (z : L ⟶ R.obj (M, N))
    (p : K ⟶ K) (q : M ⟶ M) (r : N ⟶ N)
    (hp : p = 𝟙 K) (hq : q = 𝟙 M) (hr : r = 𝟙 N) (h : x = y ≫ z) :
    x = p ≫ y ≫ z ≫ R.map (Prod.mkHom q r) := by
  rw [hp, hq, hr]
  simp only [← CategoryTheory.prod_id, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact h

private theorem projectionCurriedTensorComparison_hom
    {A B : Type*} [Category* A] [Category* B]
    (V : A ⥤ B) (T : A ⥤ A ⥤ A) (T' : B ⥤ B ⥤ B)
    (t : Functor.uncurry.obj T ⋙ V ≅ V.prod V ⋙ Functor.uncurry.obj T') (M N : A) :
    ((projectionCurriedTensorComparison V T T' t).hom.app M).app N =
      t.hom.app (M, N) := by
  unfold projectionCurriedTensorComparison
  rfl

set_option allowUnsafeReducibility true in
attribute [local reducible] StageSystem.pairFunctorCoherent

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  StageSystem.instCategoryPairCategory Functor.category
attribute [local irreducible] StageSystem.PairCategory.categoryStruct
  ScalarLocalization.category ScalarLocalization.linear sfIntegralConstructible
attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor
  commonStageDerivedPullback commonStageDerivedTensor

private theorem transportComparison_component_heq
    {A B : Type*} [Category* A] [Category* B]
    {F F' : A ⥤ B} {T T' : B ⥤ B ⥤ B} {U U' : A ⥤ A ⥤ A}
    (hF : F = F') (hT : T = T') (hU : U = U')
    (φ : (Functor.postcompose₂.obj F).obj U ≅
      (((Functor.whiskeringLeft₂ B).obj F).obj F).obj T) (M N : A) :
    HEq (((projectionTransportTensorComparison hF hT hU φ).hom.app M).app N)
      ((φ.hom.app M).app N) := by
  subst F' T' U'
  rfl

private theorem identityFunctorObject_heq
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    {F F' : A ⥤ B} (hF : F = F') (I : B ⥤ D) (M : A) :
    HEq (𝟙 (I.obj (F.obj M))) (𝟙 (I.obj (F'.obj M))) := by
  subst F'
  rfl

/-- The finite-stage representative formula is the remaining input to the
normalization argument for `ComparisonCompatible`.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: lem-sf-common-projection-pullback-tensor-compatibility-representative-bridge).

Proof: expand the two normalized tensorators and pullback comparisons, evaluate
at the chosen finite coefficient stage, and cancel the scalar-unit and transition
isomorphisms using the representative equation supplied by `hrep`.
This is the categorical normalization bridge; its only mathematical input is
the strictly pointwise finite-stage representative formula. -/
private theorem normalizedProjectionPullbackTensor_heq
    {A : Type v} [Category.{w} A] {B : Type v'} [Category.{w'} B]
    {F F₀ : B ⥤ A} {TX TX₀ : A ⥤ A ⥤ A} {TY TY₀ : B ⥤ B ⥤ B}
    (mu : (Functor.postcompose₂.obj F₀).obj TY₀ ≅
      (((Functor.whiskeringLeft₂ _).obj F₀).obj F₀).obj TX₀)
    (hF : F₀ = F) (hX : TX₀ = TX) (hY : TY₀ = TY) (M N : B) :
    HEq (((eqToIso (by rw [hF, hY]) ≪≫ mu ≪≫
      eqToIso (by rw [hF, hX])).hom.app M).app N) ((mu.hom.app M).app N) := by
  subst F₀ TX₀ TY₀
  simp

private theorem projectionTransportTensorComparison_heq
    {A B : Type*} [Category* A] [Category* B]
    {F F' : A ⥤ B} {T T' : B ⥤ B ⥤ B} {U U' : A ⥤ A ⥤ A}
    (hF : F = F') (hT : T = T') (hU : U = U')
    (φ : (Functor.postcompose₂.obj F).obj U ≅
      (((Functor.whiskeringLeft₂ B).obj F).obj F).obj T) (M : A) (N : A) :
    HEq (((projectionTransportTensorComparison hF hT hU φ).hom.app M).app N)
      (((eqToIso (by rw [hF, hU]) ≪≫ φ ≪≫
        eqToIso (by rw [hF, hT])).hom.app M).app N) := by
  subst F'
  subst T'
  subst U'
  unfold projectionTransportTensorComparison
  simp

private theorem projectionPullbackTensor_heq
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    {Q : SixFunctorCompactifiedSquare D}
    (A : SixFunctorExchangeData S T Q) (M : B Q.Y) (N : B Q.Y) :
    HEq (((projectionPullbackTensor A).hom.app M).app N)
      ((A.stage.tensorPullback.hom.app M).app N) := by
  unfold projectionPullbackTensor
  have h₁ := projectionTransportTensorComparison_heq A.properPull A.tensorBar A.tensorY
    A.stage.tensorPullback M N
  have h₂ := normalizedProjectionPullbackTensor_heq A.stage.tensorPullback
    A.properPull A.tensorBar A.tensorY M N
  exact h₁.trans h₂

set_option allowUnsafeReducibility true in
attribute [local irreducible] projectionTransportTensorComparison
  canonicalRationalPullbackTensor canonicalCommonStagePullbackTensor

/-- The normalization and finite-stage cancellation for one input pair.
Source: thm-sf-pf-field.proof.md, Compatibility.

The proof expands both curried tensorators at the common stage E, replaces the
supplied pullback comparisons by their canonical maps, and cancels the scalar
unit and transition isomorphisms against the finite-stage representative
formula.  This is one pointwise component of the comparison-compatible square;
it is strictly smaller than the universally quantified bridge theorem.
(blueprint: lem-sf-common-projection-pullback-tensor-compatibility-component). -/
theorem projectionTensorComparisonCompatible_component_of_representative_formula
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (H : SixFunctorCommonStages D C) (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (Q : SixFunctorCompactifiedSquare D)
    [hZ : ∀ x : Q.Z.obj.left, Invertible (C.l : Q.Z.obj.left.residueField x)]
    [hY : ∀ x : Q.Y.obj.left, Invertible (C.l : Q.Y.obj.left.residueField x)]
    (M N : sfRationalConstructibleCategory C.l
      (AlgebraicallyClosedCoefficients.Coefficient C.l C.Qbar E) Q.Y.obj.left)
    (hrep : HEq (canonicalCommonStagePullbackTensor C.l C.Qbar Q.p.hom.left
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (Y := Q.Y.obj.left) E).obj M)
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (Y := Q.Y.obj.left) E).obj N)).hom
      (ofHom (commonStagePullbackObject C.l C.Qbar Q.p.hom.left
          (commonStageTensorObject C.l C.Qbar Q.Y.obj.left
            ((GeneralAlgebraicallyClosedCoefficients.inclusion
              (Y := Q.Y.obj.left) E).obj M)
            ((GeneralAlgebraicallyClosedCoefficients.inclusion
              (Y := Q.Y.obj.left) E).obj N)))
        (commonStageTensorObject C.l C.Qbar Q.Z.obj.left
          (commonStagePullbackObject C.l C.Qbar Q.p.hom.left
            ((GeneralAlgebraicallyClosedCoefficients.inclusion
              (Y := Q.Y.obj.left) E).obj M))
          (commonStagePullbackObject C.l C.Qbar Q.p.hom.left
            ((GeneralAlgebraicallyClosedCoefficients.inclusion
              (Y := Q.Y.obj.left) E).obj N)))
        E (by
          change E.val ⊔ E.val ≤ E.val
          exact sup_le le_rfl le_rfl)
        (by
          change E.val ⊔ E.val ≤ E.val
          exact sup_le le_rfl le_rfl)
        (pullbackTensorAtCommonStage C.l C.Qbar Q.p.hom.left
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (Y := Q.Y.obj.left) E).obj M)
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (Y := Q.Y.obj.left) E).obj N) E (by
            change E.val ⊔ E.val ≤ E.val
            exact sup_le le_rfl le_rfl)).hom)) :
    projectionTensorComparisonComponent (inclusion E) (inclusion E)
      (projectionPullbackTensor ((H.coefficientStages E).rationalExchange Q)).hom
      (projectionPullbackTensor (H.commonStageExchange Q)).hom
      ((H.commonStageComparison E).directAdjunction Q.p).left
      (projectionCurriedTensorComparison (inclusion E)
        ((H.coefficientStages E).rationalTensor Q.Y) (H.commonStageTensor Q.Y)
        (commonProjectionTensorComparison H E Q.Y))
      (projectionCurriedTensorComparison (inclusion E)
        ((H.coefficientStages E).rationalTensor Q.Z) (H.commonStageTensor Q.Z)
        (commonProjectionTensorComparison H E Q.Z)) M N := by
  let Gs := commonProjectionPullbackStages C.l C.Qbar Q.p.hom.left
    (commonProjectionPullbackCoherence C.l C.Qbar Q.p.hom.left)
  have hG := commonProjectionPullbackStageNormalization C.l C.Qbar Q.p.hom.left
    (commonProjectionPullbackCoherence C.l C.Qbar Q.p.hom.left)
  have eF := (H.coefficientStages E).rationalPullback Q.p
  have eG := (H.commonStagePullback Q.p).trans hG
  let ψ := projectionTransportTensorComparison eG
    (H.commonStageTensorNormalization Q.Z) (H.commonStageTensorNormalization Q.Y)
    (projectionPullbackTensor (H.commonStageExchange Q))
  let ν := fun P Q ↦ (ψ.hom.app P).app Q
  have hψ (P R : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Q.Y.obj.left) :
      HEq (((projectionPullbackTensor (H.commonStageExchange Q)).hom.app P).app R)
        (ν P R) := by
    exact (transportComparison_component_heq eG
      (H.commonStageTensorNormalization Q.Z) (H.commonStageTensorNormalization Q.Y)
      (projectionPullbackTensor (H.commonStageExchange Q)) P R).symm
  have hrat K L := (projectionPullbackTensor_heq
      ((H.coefficientStages E).rationalExchange Q) K L).trans
    ((H.coefficientStages E).rationalTensorPullbackNormalization Q K L)
  have hcom P R := (projectionPullbackTensor_heq (H.commonStageExchange Q) P R).trans
    (H.commonStageTensorPullbackNormalization Q P R)
  have ha K : HEq (((H.commonStageComparison E).directAdjunction Q.p).left.hom.app K)
      ((Gs.ιCompFunctorIso E).symm.hom.app K) := by
    change HEq _ (𝟙 ((inclusion (Y := Q.Z.obj.left) E).obj
      ((rationalDerivedPullback C.l
        (AlgebraicallyClosedCoefficients.Coefficient C.l C.Qbar E) Q.p.hom.left).obj K)))
    exact ((H.commonStageModelNormalization E).2.1 Q.p K).trans
      (identityFunctorObject_heq eF (inclusion E) K)
  apply commonProjectionTensorComponent_of_normalization
    (inclusion E) (inclusion E)
    (rationalDerivedTensor C.l
      (AlgebraicallyClosedCoefficients.Coefficient C.l C.Qbar E) Q.Y.obj.left)
    (rationalDerivedTensor C.l
      (AlgebraicallyClosedCoefficients.Coefficient C.l C.Qbar E) Q.Z.obj.left)
    (commonStageDerivedTensor C.l C.Qbar Q.Y.obj.left)
    (commonStageDerivedTensor C.l C.Qbar Q.Z.obj.left) eF eG
    ((H.coefficientStages E).rationalTensorNormalization Q.Y)
    ((H.coefficientStages E).rationalTensorNormalization Q.Z)
    (H.commonStageTensorNormalization Q.Y) (H.commonStageTensorNormalization Q.Z)
    (projectionPullbackTensor ((H.coefficientStages E).rationalExchange Q)).hom
    (projectionPullbackTensor (H.commonStageExchange Q)).hom
    (fun K L ↦ (canonicalRationalPullbackTensor C.l
      (AlgebraicallyClosedCoefficients.Coefficient C.l C.Qbar E) Q.p.hom.left K L).hom)
    ν ((H.commonStageComparison E).directAdjunction Q.p).left
    (Gs.ιCompFunctorIso E).symm
    (commonProjectionTensorComparison H E Q.Y) (commonProjectionTensorComparison H E Q.Z)
    (commonInclusionTensorComparison C.l C.Qbar Q.Y.obj.left E)
    (commonInclusionTensorComparison C.l C.Qbar Q.Z.obj.left E)
    (projectionCurriedTensorComparison (inclusion E)
      ((H.coefficientStages E).rationalTensor Q.Y) (H.commonStageTensor Q.Y)
      (commonProjectionTensorComparison H E Q.Y))
    (projectionCurriedTensorComparison (inclusion E)
      ((H.coefficientStages E).rationalTensor Q.Z) (H.commonStageTensor Q.Z)
      (commonProjectionTensorComparison H E Q.Z))
    (projectionCurriedTensorComparison_hom _ _ _ _ )
    (projectionCurriedTensorComparison_hom _ _ _ _ )
    ha (commonProjectionTensorComparison_heq H E Q.Y)
    (commonProjectionTensorComparison_heq H E Q.Z) hrat hψ M N
  have hh := commonProjectionInclusionPullbackTensorSquare C.l C.Qbar Q.p.hom.left
    (commonProjectionPullbackCoherence C.l C.Qbar Q.p.hom.left) E M N
    (ν ((inclusion E).obj M) ((inclusion E).obj N))
    ((hψ _ _).symm.trans ((hcom _ _).trans hrep))
  let K := (rationalDerivedTensor C.l
    (AlgebraicallyClosedCoefficients.Coefficient C.l C.Qbar E) Q.Y.obj.left).obj (M, N)
  exact addTensorIdentities (commonStageDerivedTensor C.l C.Qbar Q.Z.obj.left) _ _ _
    ((Gs.ιCompFunctorIso E).inv.app K) ((Gs.ιCompFunctorIso E).hom.app M)
    ((Gs.ιCompFunctorIso E).hom.app N) (Gs.ιCompFunctorIso_inv_app E K)
    (Gs.ιCompFunctorIso_hom_app E M) (Gs.ιCompFunctorIso_hom_app E N) hh

end WeilConjectures

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Common.CommonStageInclusionTensorModel
public import WeilConjectures.SixFunctors.Supporting.TensoratorFromModelNaturality

/-! # Naturality of the finite-stage tensor model

Source: thm-sf-pf-field.proof.md, Compatibility and the common coefficient field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
attribute [local irreducible] sfIntegralConstructible ScalarLocalization.linear
  ScalarLocalization.preadditive Linear.homModule Preadditive.homGroup
  Preadditive.fullSubcategory Linear.fullSubcategory sfIntegralConstructibleLinear
  rationalDerivedTensor commonStageTensorComparison operationStageTransitionIso
  sfRationalScalarExtension sfConstructibleIntegralScalarExtension
  sfIntegralScalarComp sfIntegralScalarUnit

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
  [∀ x : W, Invertible (l : W.residueField x)] (E : Index l Ω)

private theorem model_square
    {A B : Type*} [Category* A] [Category* B] (I : A ⥤ B)
    {M N M' N' : B} (hM : M = M') (hN : N = N')
    {P Q P' Q' : A} (a : M' ≅ I.obj P) (b : N' ≅ I.obj Q)
    (c : P ≅ P') (d : Q ≅ Q') (f : M ⟶ N) (g : P' ⟶ Q')
    (h : HEq f (a.hom ≫ I.map (c.hom ≫ g ≫ d.inv) ≫ b.inv)) :
    f ≫ (eqToIso hN ≪≫ b ≪≫ I.mapIso d).hom =
      (eqToIso hM ≪≫ a ≪≫ I.mapIso c).hom ≫ I.map g := by
  subst M'
  subst N'
  rw [eq_of_heq h]
  simp [Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The finite-stage tensor model identification is natural in both inputs.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: lem-sf-common-stage-inclusion-tensor-model-naturality).
Proof: apply the representative formula for commonStageDerivedTensor at E to the
images of the two arrows under the repeated-stage transition. Express that
representative using isoToStage. The common-stage comparison and its inverse
cancel, leaving exactly the tensor of the two extended arrows. -/
theorem commonInclusionTensorModel_naturality
    {K K' L L' : Stage l Ω W E} (a : K ⟶ K') (b : L ⟶ L') :
    (commonStageDerivedTensor l Ω W).map
        (Prod.mkHom ((inclusion (l := l) (Ω := Ω) (Y := W) E).map a)
          ((inclusion (l := l) (Ω := Ω) (Y := W) E).map b)) ≫
        (commonInclusionTensorModel l Ω W E K' L').hom =
      (commonInclusionTensorModel l Ω W E K L).hom ≫
        (inclusion (l := l) (Ω := Ω) (Y := W) E).map
          ((rationalDerivedTensor l (Coefficient.{u} l Ω E) W).map
            (Prod.mkHom (((stageSystem l Ω W).T (le_rfl : E ≤ E)).map a)
              (((stageSystem l Ω W).T (le_rfl : E ≤ E)).map b))) := by
  let I := inclusion (l := l) (Ω := Ω) (Y := W) E
  let P := I.obj K
  let Q := I.obj L
  let P' := I.obj K'
  let Q' := I.obj L'
  have h : (commonStageTensorObject l Ω W P Q).stage ≤ E := by
    change E.val ⊔ E.val ≤ E.val
    exact sup_le le_rfl le_rfl
  have h' : (commonStageTensorObject l Ω W P' Q').stage ≤ E := by
    change E.val ⊔ E.val ≤ E.val
    exact sup_le le_rfl le_rfl
  have hm := (commonStageDerivedTensor_existsUnique l Ω W).exists.choose_spec.2
    P Q P' Q' E h h'
    (((stageSystem l Ω W).T (le_rfl : E ≤ E)).map a)
    (((stageSystem l Ω W).T (le_rfl : E ≤ E)).map b)
  have ho := (commonStageDerivedTensor_existsUnique l Ω W).exists.choose_spec.1
  have hj := StageSystem.mkHom_eq_isoToStage h h'
    ((commonStageTensorComparison l Ω W P Q E h).hom ≫
      (rationalDerivedTensor l (Coefficient.{u} l Ω E) W).map
        (Prod.mkHom (((stageSystem l Ω W).T (le_rfl : E ≤ E)).map a)
          (((stageSystem l Ω W).T (le_rfl : E ≤ E)).map b)) ≫
      (commonStageTensorComparison l Ω W P' Q' E h').inv)
  unfold commonInclusionTensorModel
  exact model_square I (ho P Q) (ho P' Q')
    ((stageSystem l Ω W).isoToStage (commonStageTensorObject l Ω W P Q) h)
    ((stageSystem l Ω W).isoToStage (commonStageTensorObject l Ω W P' Q') h')
    (commonStageTensorComparison l Ω W P Q E h)
    (commonStageTensorComparison l Ω W P' Q' E h')
    _ _ (hm.trans (heq_of_eq hj))

end WeilConjectures

namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)

set_option backward.isDefEq.respectTransparency false in
/-- The finite-stage inclusion tensorator, natural in both arguments.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: lem-sf-common-stage-inclusion-tensor-model-naturality). -/
@[irreducible] def commonInclusionTensorComparison
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
    [∀ x : W, Invertible (l : W.residueField x)] (E : Index l Ω) :
    rationalDerivedTensor l (Coefficient.{u} l Ω E) W ⋙
        inclusion (l := l) (Ω := Ω) (Y := W) E ≅
      (inclusion (l := l) (Ω := Ω) (Y := W) E).prod
          (inclusion (l := l) (Ω := Ω) (Y := W) E) ⋙
        commonStageDerivedTensor l Ω W := by
  let I := inclusion (l := l) (Ω := Ω) (Y := W) E
  let R := rationalDerivedTensor l (Coefficient.{u} l Ω E) W
  let U := (operationStageTransitionIso l Ω W E E le_rfl) ≪≫ unitor l Ω W E
  exact NatIso.ofComponents
    (fun K ↦ (commonInclusionTensorModel l Ω W E K.1 K.2 ≪≫
      I.mapIso (R.mapIso (Iso.prod (U.app K.1) (U.app K.2)))).symm)
    (fun f ↦ tensoratorFromModel_naturality I R (commonStageDerivedTensor l Ω W) U
      (fun K ↦ commonInclusionTensorModel l Ω W E K.1 K.2)
      (fun f ↦ commonInclusionTensorModel_naturality l Ω W E f.1 f.2) f)

end WeilConjectures

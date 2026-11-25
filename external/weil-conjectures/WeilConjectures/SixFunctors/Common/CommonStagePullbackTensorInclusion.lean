/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Common.CommonStageInclusionTensorNaturality
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
import WeilConjectures.SixFunctors.Common.CommonStagePullbackModelMap
import WeilConjectures.SmoothPurity.Common.CommonStagePullbackCoefficientUnit
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorNaturality
import all Mathlib.Logic.Small.Defs

/-! # The inverse pullback/tensor square for finite-stage inclusion

Source: thm-sf-pf-field.proof.md, Compatibility.
(blueprint: lem-sf-common-stage-pullback-tensor-inclusion-inverse).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option Elab.async false
set_option linter.auxLemma false

universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)

section

attribute [local irreducible] equivShrink
  HasDerivedCategory.standard integralCoefficientLinear
  instCategoryDerivedCategory DerivedCategory.instPreadditive HomologicalComplex.instCategory
  SheafOfModules.instCategory SheafOfModules.instAbelian
  completedIntegralCommRingSheafUnrestricted
  ObjectProperty.FullSubcategory.category
  rationalPullbackScalarComparison rationalTensorScalarComparison
  Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionAbsoluteValue
  sfRationalScalarExtension sfConstructibleIntegralScalarExtension
  sfIntegralScalarComp sfIntegralScalarUnit
  canonicalRationalPullbackTensor canonicalCommonStagePullbackTensor
  rationalDerivedPullback rationalDerivedTensor
  commonStageDerivedPullback commonStageDerivedTensor commonStagePullbackComparison
  commonStageTensorComparison operationStageTransitionIso
  GeneralAlgebraicallyClosedCoefficients.unitor ScalarLocalization.category Scheme.residueField
  StageSystem.PairCategory.categoryStruct Preadditive.fullSubcategory
  sfIntegralConstructible ScalarLocalization.linear ScalarLocalization.preadditive
  Linear.homModule Preadditive.homGroup Linear.fullSubcategory sfIntegralConstructibleLinear
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.Stage
  StageSystem.ι
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
  commonStagePullbackObject commonStageTensorObject

private theorem included_model_square
    {C D : Type*} [Category* C] [Category* D] (I : C ⥤ D)
    {P Q R S : C} {A B : D} (a : A ≅ I.obj P) (b : B ≅ I.obj Q)
    (r : P ⟶ R) (n : P ⟶ Q) (v : R ⟶ S) (t : Q ≅ S)
    (h : r ≫ v = n ≫ t.hom) :
    (a.hom ≫ I.map r) ≫ I.map v =
      (a.hom ≫ I.map n ≫ b.inv) ≫ (b ≪≫ I.mapIso t).hom := by
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id_assoc, ← Functor.map_comp] using
    congrArg (fun k ↦ a.hom ≫ I.map k) h

private theorem finite_tensor_unit_square
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) (TY : C × C ⥤ C) (TX : D × D ⥤ D)
    (mu : ∀ M N, F.obj (TY.obj (M, N)) ⟶ TX.obj (F.obj M, F.obj N))
    {M N M' N' K : C} {P Q A B : D}
    (u : M' ≅ M) (v : N' ≅ N)
    (p : P ≅ F.obj M') (q : Q ≅ F.obj N')
    (x : P ≅ F.obj M) (y : Q ≅ F.obj N)
    (hp : p.hom ≫ F.map u.hom = x.hom) (hq : q.hom ≫ F.map v.hom = y.hom)
    (a : A ≅ F.obj K) (b : K ≅ TY.obj (M', N')) (z : B ≅ TX.obj (P, Q))
    (hn : F.map (TY.map (Prod.mkHom u.hom v.hom)) ≫ mu M N =
      mu M' N' ≫ TX.map (Prod.mkHom (F.map u.hom) (F.map v.hom))) :
    (a.hom ≫ F.map (b.hom ≫ TY.map (Prod.mkHom u.hom v.hom))) ≫ mu M N =
      (a.hom ≫ F.map b.hom ≫ mu M' N' ≫
        TX.map (Prod.mkHom p.inv q.inv) ≫ z.inv) ≫
        (z.hom ≫ TX.map (Prod.mkHom x.hom y.hom)) := by
  have ep : p.inv ≫ x.hom = F.map u.hom := by rw [← hp]; simp
  have eq : q.inv ≫ y.hom = F.map v.hom := by rw [← hq]; simp
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [hn, ← TX.map_comp]
  simp only [prod_comp, ep, eq]

private theorem cast_model_comp_heq
    {C D : Type*} [Category* C] [Category* D] (I : C ⥤ D)
    {A A' : D} {P Q R : C} (h : A = A') (f : A' ≅ I.obj P)
    (a : P ≅ Q) (b : Q ≅ R) :
    HEq (((eqToIso h ≪≫ f ≪≫ I.mapIso a) ≪≫ I.mapIso b).hom)
      ((f ≪≫ I.mapIso (a ≪≫ b)).hom) := by
  cases h
  apply heq_of_eq
  simp only [eqToIso_refl, Iso.refl_trans, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]

private theorem pullback_model_heq_square
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A A' B : C} {P Q Q' R S : D}
    (hA : A = A') (hP : F.obj A' = P) (hQ : Q = Q') (hR : F.obj B = R)
    (s : A' ⟶ B) (t : Q' ⟶ S) (m : F.obj A ⟶ Q)
    (q : A ⟶ B) (hq : HEq q s)
    (r : P ⟶ R) (n : P ⟶ Q') (v : R ⟶ S)
    (hm : HEq (F.map s) r) (hn : HEq m n)
    (h : r ≫ v = n ≫ t) :
    F.map q ≫ eqToHom hR ≫ v = m ≫ eqToHom hQ ≫ t := by
  cases hA
  cases hP
  cases hQ
  cases hR
  simpa only [eqToHom_refl, Category.id_comp, eq_of_heq hq,
    eq_of_heq hm, eq_of_heq hn] using h

private theorem tensor_model_heq_tail
    {C D : Type*} [Category* C] [Category* D] (T : C × C ⥤ D)
    {M M' N N' : C} {B S : D} (hM : M = M') (hN : N = N')
    (hB : T.obj (M', N') = B) (q : T.obj (M', N') ⟶ S) (s : B ⟶ S)
    (hq : HEq q s) :
    T.map (Prod.mkHom (eqToHom hM) (eqToHom hN)) ≫ q =
      eqToHom ((congrArg T.obj (congrArg₂ Prod.mk hM hN)).trans hB) ≫ s := by
  cases hM
  cases hN
  cases hB
  simp only [eqToHom_refl, ← prod_id, Category.id_comp, eq_of_heq hq]
  erw [T.map_id]
  exact Category.id_comp _

/-- The canonical pullback/tensor comparison satisfies the inverse inclusion square.

Source: thm-sf-pf-field.proof.md, Compatibility and the common coefficient field.
(blueprint: lem-sf-common-stage-pullback-tensor-inclusion-inverse).

Proof: identify the two inverse tensorators with their literal finite-stage model
maps. Compute common pullback of the source model using coherent descent. Evaluate
the canonical comparison at the input stage, apply rational comparison naturality
to the two scalar units, and cancel the model comparisons. The pullback coefficient
unit equation identifies the remaining arrows. Equality transport restores the
objects prescribed by the common-stage functors. -/
theorem commonStagePullbackTensor_inclusion_inverse
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E : Index l Ω) (M N : Stage l Ω Y E) :
    let F := commonStageDerivedPullback l Ω f
    let R := rationalDerivedPullback l (Coefficient.{u} l Ω E) f
    let I := (stageSystem l Ω Y).ι E
    let J := (stageSystem l Ω X).ι E
    let ho : ∀ K : Stage l Ω Y E, F.obj (I.obj K) = J.obj (R.obj K) := by
      intro K
      unfold F commonStageDerivedPullback
      exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 (I.obj K)
    F.map ((commonInclusionTensorComparison l Ω Y E).inv.app (M, N)) ≫
        eqToHom (C := Pair l Ω X)
          (ho ((rationalDerivedTensor l (Coefficient.{u} l Ω E) Y).obj (M, N))) ≫
        J.map (canonicalRationalPullbackTensor l (Coefficient.{u} l Ω E)
            f M N).hom =
      (canonicalCommonStagePullbackTensor l Ω f (I.obj M) (I.obj N)).hom ≫
        (commonStageDerivedTensor l Ω X).map
          (Prod.mkHom (C := Pair l Ω X) (D := Pair l Ω X)
            (eqToHom (C := Pair l Ω X) (ho M)) (eqToHom (C := Pair l Ω X) (ho N))) ≫
        (commonInclusionTensorComparison l Ω X E).inv.app (R.obj M, R.obj N) := by
  let F := commonStageDerivedPullback l Ω f
  let R := rationalDerivedPullback l (Coefficient.{u} l Ω E) f
  let TY := rationalDerivedTensor l (Coefficient.{u} l Ω E) Y
  let TX := rationalDerivedTensor l (Coefficient.{u} l Ω E) X
  let I := (stageSystem l Ω Y).ι E
  let J := (stageSystem l Ω X).ι E
  let A := commonStageTensorObject l Ω Y (I.obj M) (I.obj N)
  let B := commonStageTensorObject l Ω X
    (commonStagePullbackObject l Ω f (I.obj M))
    (commonStagePullbackObject l Ω f (I.obj N))
  have h : A.stage ≤ E := by
    change E.val ⊔ E.val ≤ E.val
    exact sup_le le_rfl le_rfl
  let UY := operationStageTransitionIso l Ω Y E E le_rfl ≪≫ unitor l Ω Y E
  let UX := operationStageTransitionIso l Ω X E E le_rfl ≪≫ unitor l Ω X E
  let cy := commonStageTensorComparison l Ω Y (I.obj M) (I.obj N) E h
  let cx := commonStageTensorComparison l Ω X
    (commonStagePullbackObject l Ω f (I.obj M))
    (commonStagePullbackObject l Ω f (I.obj N)) E h
  let ay : A.toStage h ≅ TY.obj (M, N) :=
    cy ≪≫ TY.mapIso (Iso.prod (UY.app M) (UY.app N))
  let ax : B.toStage h ≅ TX.obj (R.obj M, R.obj N) :=
    cx ≪≫ TX.mapIso (Iso.prod (UX.app (R.obj M)) (UX.app (R.obj N)))
  let sy : A ≅ I.obj (TY.obj (M, N)) :=
    (stageSystem l Ω Y).isoToStage A h ≪≫ I.mapIso ay
  let sx : B ≅ J.obj (TX.obj (R.obj M, R.obj N)) :=
    (stageSystem l Ω X).isoToStage B h ≪≫ J.mapIso ax
  have hoF : ∀ K, F.obj K = commonStagePullbackObject l Ω f K := by
    unfold F commonStageDerivedPullback
    exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1
  have hoY : (commonStageDerivedTensor l Ω Y).obj (I.obj M, I.obj N) = A := by
    unfold commonStageDerivedTensor
    exact (commonStageDerivedTensor_existsUnique l Ω Y).exists.choose_spec.1 _ _
  have hoX : (commonStageDerivedTensor l Ω X).obj (J.obj (R.obj M), J.obj (R.obj N)) = B := by
    unfold commonStageDerivedTensor
    exact (commonStageDerivedTensor_existsUnique l Ω X).exists.choose_spec.1 _ _
  have hsy : HEq
      ((commonInclusionTensorComparison l Ω Y E).inv.app (M, N)) sy.hom := by
    delta commonInclusionTensorComparison
    change HEq ((commonInclusionTensorModel l Ω Y E M N ≪≫
      I.mapIso (TY.mapIso (Iso.prod (UY.app M) (UY.app N)))).hom) _
    delta commonInclusionTensorModel
    exact cast_model_comp_heq I hoY ((stageSystem l Ω Y).isoToStage A h) cy
      (TY.mapIso (Iso.prod (UY.app M) (UY.app N)))
  have hsx : HEq
      ((commonInclusionTensorComparison l Ω X E).inv.app (R.obj M, R.obj N)) sx.hom := by
    delta commonInclusionTensorComparison
    change HEq ((commonInclusionTensorModel l Ω X E (R.obj M) (R.obj N) ≪≫
      J.mapIso (TX.mapIso (Iso.prod (UX.app (R.obj M)) (UX.app (R.obj N))))).hom) _
    delta commonInclusionTensorModel
    exact cast_model_comp_heq J hoX ((stageSystem l Ω X).isoToStage B h) cx
      (TX.mapIso (Iso.prod (UX.app (R.obj M)) (UX.app (R.obj N))))
  have ht : (commonStageDerivedTensor l Ω X).obj (F.obj (I.obj M), F.obj (I.obj N)) =
      B := (congrArg (commonStageDerivedTensor l Ω X).obj
        (congrArg₂ Prod.mk (hoF (I.obj M)) (hoF (I.obj N)))).trans hoX
  have htail : (commonStageDerivedTensor l Ω X).map
        (Prod.mkHom (C := Pair l Ω X) (D := Pair l Ω X)
          (eqToHom (C := Pair l Ω X) (hoF (I.obj M)))
          (eqToHom (C := Pair l Ω X) (hoF (I.obj N)))) ≫
        (commonInclusionTensorComparison l Ω X E).inv.app (R.obj M, R.obj N) =
      eqToHom (C := Pair l Ω X) ht ≫ sx.hom := by
    exact tensor_model_heq_tail (commonStageDerivedTensor l Ω X)
      (hoF (I.obj M)) (hoF (I.obj N)) hoX _ sx.hom hsx
  let m := pullbackTensorAtCommonStage l Ω f (I.obj M) (I.obj N) E h
  let r : (commonStagePullbackObject l Ω f A).toStage h ⟶ R.obj (TY.obj (M, N)) :=
    (commonStagePullbackComparison l Ω f A E h).hom ≫ R.map ay.hom
  have hmu : HEq (canonicalCommonStagePullbackTensor l Ω f (I.obj M) (I.obj N)).hom
      (ofHom (commonStagePullbackObject l Ω f A) B E h h m.hom) := by
    unfold canonicalCommonStagePullbackTensor
    exact (canonicalCommonStagePullbackTensor_existsUnique l Ω f
      (I.obj M) (I.obj N)).exists.choose_spec E h
  have hm := commonStageDerivedPullback_map_model l Ω f A E h ay.hom
  have hpM := congrArg Iso.hom (commonStagePullbackComparison_self_unit l Ω f (I.obj M))
  have hpN := congrArg Iso.hom (commonStagePullbackComparison_self_unit l Ω f (I.obj N))
  simp only [Iso.trans_hom, Iso.app_hom] at hpM hpN
  have hn := canonicalRationalPullbackTensor_naturality l (Coefficient.{u} l Ω E) f
    (UY.hom.app M) (UY.hom.app N)
  have hf : r ≫ (canonicalRationalPullbackTensor l (Coefficient.{u} l Ω E) f M N).hom =
      m.hom ≫ ax.hom := by
    dsimp only [r, ay, ax, m, pullbackTensorAtCommonStage]
    simpa only [R, TY, TX, cy, cx, A, I, StageSystem.ι,
      StageSystem.PairCategory.toStage, Functor.id, Iso.trans, Functor.mapIso,
      Iso.prod, Iso.symm, Iso.app] using finite_tensor_unit_square R TY TX
      (fun M N ↦ (canonicalRationalPullbackTensor l (Coefficient.{u} l Ω E) f M N).hom)
      (UY.app M) (UY.app N)
      (commonStagePullbackComparison l Ω f (I.obj M) E le_rfl)
      (commonStagePullbackComparison l Ω f (I.obj N) E le_rfl)
      (UX.app (R.obj M)) (UX.app (R.obj N)) hpM hpN
      (commonStagePullbackComparison l Ω f A E h) cy cx hn
  have hh := included_model_square J
    ((stageSystem l Ω X).isoToStage (commonStagePullbackObject l Ω f A) h)
    ((stageSystem l Ω X).isoToStage B h) r m.hom
    (canonicalRationalPullbackTensor l (Coefficient.{u} l Ω E) f M N).hom
    ax hf
  have hrep := StageSystem.mkHom_eq_isoToStage (S := stageSystem l Ω X)
    (X := commonStagePullbackObject l Ω f A) (Y := B) h h m.hom
  have hh' := hh.trans (eq_whisker hrep.symm sx.hom)
  let transport :=
    @pullback_model_heq_square (Pair l Ω Y) (Pair l Ω X)
      (pairCategory l Ω Y) (pairCategory l Ω X) F
  exact
    (transport
      (A := (commonStageDerivedTensor l Ω Y).obj (I.obj M, I.obj N))
      (A' := A) (B := I.obj (TY.obj (M, N)))
      (P := commonStagePullbackObject l Ω f A)
      (Q := (commonStageDerivedTensor l Ω X).obj (F.obj (I.obj M), F.obj (I.obj N)))
      (Q' := B) (R := J.obj (R.obj (TY.obj (M, N))))
      (S := J.obj (TX.obj (R.obj M, R.obj N)))
      hoY (hoF A) ht (hoF (I.obj (TY.obj (M, N))))
      sy.hom sx.hom
      (canonicalCommonStagePullbackTensor l Ω f (I.obj M) (I.obj N)).hom
      ((commonInclusionTensorComparison l Ω Y E).inv.app (M, N)) hsy
      (((stageSystem l Ω X).isoToStage (commonStagePullbackObject l Ω f A) h).hom ≫
        J.map r)
      (ofHom (commonStagePullbackObject l Ω f A) B E h h m.hom)
      (J.map (canonicalRationalPullbackTensor l (Coefficient.{u} l Ω E) f M N).hom)
      hm hmu hh').trans
        (whisker_eq
          (canonicalCommonStagePullbackTensor l Ω f (I.obj M) (I.obj N)).hom htail.symm)

end
end WeilConjectures

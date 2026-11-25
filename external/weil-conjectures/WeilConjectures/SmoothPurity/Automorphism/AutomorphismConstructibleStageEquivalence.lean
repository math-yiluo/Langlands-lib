/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Automorphism.AutomorphismConstructibleStageCore
import WeilConjectures.SmoothPurity.Automorphism.AutomorphismRationalShiftDescent
import WeilConjectures.SmoothPurity.Rational.RationalPullbackTransitionShift
import WeilConjectures.SmoothPurity.Common.CommonStagePullbackShiftExactDescent
import all WeilConjectures.SmoothPurity.Sf.SfFrameworkCommonStageDescent
import WeilConjectures.SmoothPurity.Automorphism.AutomorphismInverseComparisonDescent
import WeilConjectures.SmoothPurity.Common.CommonStagePullbackRepresentativeLinearity

/-! # Rational and common-stage automorphism shift comparisons

Source: current blueprint, Weil-structures paragraph of the open-closed triangle.
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
The finite and integral constructions are re-exported from the stage core.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v r s u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open scoped TensorProduct
local instance (priority := 5000)
    instEssentiallySmallProEt_automorphismConstructibleStageEquivalence
    (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{u} _
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local irreducible] sfIntrinsicModuleEquivalence
  HasDerivedCategory.standard integralDerivedPullback scalarReductionExistence
  scalarReductionDerivedExistence completedIntegralCoefficientSheafUnrestricted

set_option allowUnsafeReducibility true in
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField

set_option allowUnsafeReducibility true in
attribute [local irreducible] constructibleIntegralPullback
  rationalDerivedPullback commonStageDerivedPullback

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageShift
  GeneralAlgebraicallyClosedCoefficients.stagePreadditive
  GeneralAlgebraicallyClosedCoefficients.stageTransition
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
attribute [local instance 5000] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stagePreadditive
  GeneralAlgebraicallyClosedCoefficients.stageShift
attribute [local instance 5000] sfRationalConstructiblePretriangulated
  sfRationalConstructibleTriangulated sfRationalConstructibleShiftAdditive
  sfRationalConstructibleZero sfRationalConstructibleShift sfRationalLocalizationCommShift
attribute [local instance 5000] GeneralAlgebraicallyClosedCoefficients.preadditive
  GeneralAlgebraicallyClosedCoefficients.stagePretriangulated
  GeneralAlgebraicallyClosedCoefficients.transitionIso_commShift
  GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift
  GeneralAlgebraicallyClosedCoefficients.stageShiftAdditive
  GeneralAlgebraicallyClosedCoefficients.inclusion_exact
  GeneralAlgebraicallyClosedCoefficients.hasShift
  GeneralAlgebraicallyClosedCoefficients.inclusionCommShift
  GeneralAlgebraicallyClosedCoefficients.shiftAdditive
  GeneralAlgebraicallyClosedCoefficients.zero_exists
  GeneralAlgebraicallyClosedCoefficients.pretriangulated
  GeneralAlgebraicallyClosedCoefficients.isTriangulated
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Pair
  GeneralAlgebraicallyClosedCoefficients.pairCategory
  generalAlgebraicallyClosedConstructibleCategory

private def restrict_composite
    {A B C A' B' C' : Type*}
    [Category* A] [Category* B] [Category* C]
    [Category* A'] [Category* B'] [Category* C']
    (I : A' ⥤ A) (J : B' ⥤ B) (K : C' ⥤ C)
    (F : A ⥤ B) (G : B ⥤ C) (f : A' ⥤ B') (g : B' ⥤ C')
    (cf : I ⋙ F ≅ f ⋙ J) (cg : J ⋙ G ≅ g ⋙ K) :
    I ⋙ (F ⋙ G) ≅ (f ⋙ g) ⋙ K :=
  (Functor.associator I F G).symm ≪≫ Functor.isoWhiskerRight cf G ≪≫
    Functor.associator f J G ≪≫ Functor.isoWhiskerLeft f cg ≪≫
      (Functor.associator f g K).symm

private theorem restrict_composite_normalization
    {A B C A' B' C' : Type*}
    [Category* A] [Category* B] [Category* C]
    [Category* A'] [Category* B'] [Category* C']
    (I : A' ⥤ A) (J : B' ⥤ B) (K : C' ⥤ C)
    (F : A ⥤ B) (G : B ⥤ C) (f : A' ⥤ B') (g : B' ⥤ C')
    (cf : I ⋙ F ≅ f ⋙ J) (cg : J ⋙ G ≅ g ⋙ K)
    (of : ∀ P, F.obj (I.obj P) = J.obj (f.obj P))
    (og : ∀ P, G.obj (J.obj P) = K.obj (g.obj P))
    (hf : ∀ P, HEq (cf.hom.app P) (𝟙 (F.obj (I.obj P))))
    (hg : ∀ P, HEq (cg.hom.app P) (𝟙 (G.obj (J.obj P)))) (P : A') :
    (restrict_composite I J K F G f g cf cg).hom.app P =
      eqToHom ((congrArg G.obj (of P)).trans (og (f.obj P))) := by
  have hf' := eq_of_heq ((hf P).trans (eqToHom_heq_id_dom _ _ (of P)).symm)
  have hg' := eq_of_heq ((hg (f.obj P)).trans
    (eqToHom_heq_id_dom _ _ (og (f.obj P))).symm)
  simp only [restrict_composite, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, hf', hg', eqToHom_map, eqToHom_trans]

private theorem restrict_composite_shift
    {A B C A' B' C' : Type*}
    [Category* A] [Category* B] [Category* C]
    [Category* A'] [Category* B'] [Category* C']
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ]
    [HasShift A' ℤ] [HasShift B' ℤ] [HasShift C' ℤ]
    (I : A' ⥤ A) (J : B' ⥤ B) (K : C' ⥤ C)
    (F : A ⥤ B) (G : B ⥤ C) (f : A' ⥤ B') (g : B' ⥤ C')
    [I.CommShift ℤ] [J.CommShift ℤ] [K.CommShift ℤ]
    [F.CommShift ℤ] [G.CommShift ℤ] [f.CommShift ℤ] [g.CommShift ℤ]
    (cf : I ⋙ F ≅ f ⋙ J) (cg : J ⋙ G ≅ g ⋙ K)
    [NatTrans.CommShift cf.hom ℤ] [NatTrans.CommShift cg.hom ℤ] :
    NatTrans.CommShift (restrict_composite I J K F G f g cf cg).hom ℤ := by
  simp only [restrict_composite, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  infer_instance

private theorem common_obj
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E) :
    (commonStageDerivedPullback l Ω f).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := Ω) (Y := X) E).obj K) =
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := Ω) (Y := Y) E).obj
        ((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f).obj K) := by
  simpa only [commonStageDerivedPullback, commonStagePullbackObject,
    GeneralAlgebraicallyClosedCoefficients.inclusion, StageSystem.ι_obj] using
    (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 ⟨E, K⟩

private theorem normalized_restriction_shift
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    (I : C ⥤ C') (J : D ⥤ D') (F : C ⥤ D) (H : C' ⥤ D')
    [I.CommShift ℤ] [J.CommShift ℤ] [F.CommShift ℤ] [H.CommShift ℤ]
    (oI : ∀ (n : ℤ) X, I.obj (X⟦n⟧) = (I.obj X)⟦n⟧)
    (oJ : ∀ (n : ℤ) X, J.obj (X⟦n⟧) = (J.obj X)⟦n⟧)
    (nI : ∀ (n : ℤ) X, HEq ((I.commShiftIso n).hom.app X) (𝟙 (I.obj (X⟦n⟧))))
    (nJ : ∀ (n : ℤ) X, HEq ((J.commShiftIso n).hom.app X) (𝟙 (J.obj (X⟦n⟧))))
    (oH : ∀ X, H.obj (I.obj X) = J.obj (F.obj X))
    (nH : ∀ (n : ℤ) X,
      HEq ((H.commShiftIso n).hom.app (I.obj X)) (J.map ((F.commShiftIso n).hom.app X)))
    (e : I ⋙ H ≅ F ⋙ J)
    (he : ∀ X, HEq (e.hom.app X) (𝟙 (H.obj (I.obj X)))) :
    NatTrans.CommShift e.hom ℤ := by
  constructor
  intro n
  ext X
  have hc (X) : e.hom.app X = eqToHom (oH X) :=
    eq_of_heq ((he X).trans (eqToHom_heq_id_dom _ _ (oH X)).symm)
  have q : (I.commShiftIso n).hom.app X = eqToHom (oI n X) :=
    eq_of_heq ((nI n X).trans (eqToHom_heq_id_dom _ _ (oI n X)).symm)
  have q' : (J.commShiftIso n).hom.app (F.obj X) = eqToHom (oJ n (F.obj X)) :=
    eq_of_heq ((nJ n _).trans (eqToHom_heq_id_dom _ _ (oJ n (F.obj X))).symm)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, hc, q, q', eqToHom_map]
  apply eq_of_heq
  exact ((comp_eqToHom_heq _ _).trans (eqToHom_comp_heq _ _)).trans
    ((nH n X).trans ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm)

private theorem precompose_eqToIso_heq
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (I : A ⥤ B) (F G : B ⥤ D) (h : F = G) (K : A) :
    HEq ((eqToIso (congrArg (fun H ↦ I ⋙ H) h)).hom.app K)
      (𝟙 (F.obj (I.obj K))) := by
  subst G
  rfl

private theorem common_restriction
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [(commonStageDerivedPullback l Ω f).CommShift ℤ]
    (E : AlgebraicallyClosedCoefficients.Index l Ω)
    [(rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
      f).CommShift ℤ]
    (hn : ∀ (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E) (n : ℤ),
      HEq (((commonStageDerivedPullback l Ω f).commShiftIso n).hom.app
        ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K))
        ((GeneralAlgebraicallyClosedCoefficients.inclusion E).map
          (((rationalDerivedPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f).commShiftIso
              n).hom.app K))) :
    ∃ e : GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙
          commonStageDerivedPullback l Ω f ≅
        rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion E,
      (∀ K, HEq (e.hom.app K)
        (𝟙 ((commonStageDerivedPullback l Ω f).obj
          ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K)))) ∧
      NatTrans.CommShift e.hom ℤ := by
  obtain ⟨hc, hM⟩ := commonStagePullbackNormalizedDescent l Ω f
  let M : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y) :=
    ⟨fun L ↦ rationalDerivedPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f,
      commonStagePullbackTransition l Ω f, hc⟩
  let I := GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := Ω) (Y := X) E
  let J := GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := Ω) (Y := Y) E
  let e : I ⋙ commonStageDerivedPullback l Ω f ≅
      rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f ⋙ J :=
    eqToIso (congrArg (fun H ↦ I ⋙ H) hM) ≪≫ M.ιCompFunctorIso E
  have he (K) : HEq (e.hom.app K)
      (𝟙 ((commonStageDerivedPullback l Ω f).obj (I.obj K))) := by
    change HEq (((eqToIso (congrArg (fun H ↦ I ⋙ H) hM)).hom.app K) ≫
      (M.ιCompFunctorIso E).hom.app K) _
    rw [StageSystem.Morphism.ιCompFunctorIso_hom_app]
    apply (comp_eqToHom_heq _ _).trans
    · exact precompose_eqToIso_heq I _ _ hM K
    · rfl
  refine ⟨e, he, ?_⟩
  apply normalized_restriction_shift I J _ _
    (fun n K ↦ (framework_shift_obj n E K).symm)
    (fun n K ↦ (framework_shift_obj n E K).symm)
  · intro n K
    exact (GeneralAlgebraicallyClosedCoefficients.shift_existsUnique
      (l := l) (Ω := Ω) (Y := X)).exists.choose_spec.2.2.2.choose_spec n E K
  · intro n K
    exact (GeneralAlgebraicallyClosedCoefficients.shift_existsUnique
      (l := l) (Ω := Ω) (Y := Y)).exists.choose_spec.2.2.2.choose_spec n E K
  · exact common_obj l Ω f E
  · exact fun n K ↦ hn K n
  · exact he

private theorem common_square_shift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.asIso.hom ≫ f = f ≫ eX.asIso.hom)
    (rf : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
      (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
        f).CommShift ℤ)
    (rx : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
      (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
        eX.asIso.hom).CommShift ℤ)
    (ry : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
      (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
        eY.asIso.hom).CommShift ℤ)
    [(commonStageDerivedPullback l Ω f).CommShift ℤ]
    [(commonStageDerivedPullback l Ω eX.asIso.hom).CommShift ℤ]
    [(commonStageDerivedPullback l Ω eY.asIso.hom).CommShift ℤ]
    (nf : ∀ E K n, HEq (((commonStageDerivedPullback l Ω f).commShiftIso n).hom.app
        ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K))
      ((GeneralAlgebraicallyClosedCoefficients.inclusion E).map
        (((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f).commShiftIso
            (self := rf E) n).hom.app K)))
    (nx : ∀ E K n, HEq (((commonStageDerivedPullback l Ω eX.asIso.hom).commShiftIso n).hom.app
        ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K))
      ((GeneralAlgebraicallyClosedCoefficients.inclusion E).map
        (((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) eX.asIso.hom).commShiftIso
            (self := rx E) n).hom.app K)))
    (ny : ∀ E K n, HEq (((commonStageDerivedPullback l Ω eY.asIso.hom).commShiftIso n).hom.app
        ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K))
      ((GeneralAlgebraicallyClosedCoefficients.inclusion E).map
        (((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) eY.asIso.hom).commShiftIso
            (self := ry E) n).hom.app K)))
    (hb : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
      let := rf E
      let := rx E
      let := ry E
      NatTrans.CommShift (automorphismStageRationalSquare l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) C f eX eY h).hom ℤ) :
    NatTrans.CommShift (automorphismStageQbarSquare l Ω C f eX eY h).hom ℤ := by
  let := rf
  let := rx
  let := ry
  apply pairNatTrans_shift (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X)
  intro E
  obtain ⟨ef, hef, sef⟩ := common_restriction l Ω f E (nf E)
  obtain ⟨ex, hex, sex⟩ := common_restriction l Ω eX.asIso.hom E (nx E)
  obtain ⟨ey, hey, sey⟩ := common_restriction l Ω eY.asIso.hom E (ny E)
  let := sef
  let := sex
  let := sey
  let := hb E
  let I := GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := Ω) (Y := X) E
  let J := GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := Ω) (Y := Y) E
  let F := commonStageDerivedPullback l Ω f
  let A := commonStageDerivedPullback l Ω eX.asIso.hom
  let B := commonStageDerivedPullback l Ω eY.asIso.hom
  let fE := rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f
  let aE := rationalDerivedPullback l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) eX.asIso.hom
  let bE := rationalDerivedPullback l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) eY.asIso.hom
  let left := restrict_composite I J J F B fE bE ef ey
  let right := restrict_composite I I J A F aE fE ex ef
  have sl : NatTrans.CommShift left.hom ℤ :=
    restrict_composite_shift I J J F B fE bE ef ey
  have sr : NatTrans.CommShift right.hom ℤ :=
    restrict_composite_shift I I J A F aE fE ex ef
  let β := automorphismStageRationalSquare l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) C f eX eY h
  have he : Functor.whiskerLeft I
      (automorphismStageQbarSquare l Ω C f eX eY h).hom =
      left.hom ≫ Functor.whiskerRight β.hom J ≫ right.inv := by
    ext K
    have ol := (congrArg B.obj (common_obj l Ω f E K)).trans
      (common_obj l Ω eY.asIso.hom E (fE.obj K))
    have oR := (congrArg F.obj (common_obj l Ω eX.asIso.hom E K)).trans
      (common_obj l Ω f E (aE.obj K))
    have nl := restrict_composite_normalization I J J F B fE bE ef ey
      (common_obj l Ω f E) (common_obj l Ω eY.asIso.hom E) hef hey K
    have nr := restrict_composite_normalization I I J A F aE fE ex ef
      (common_obj l Ω eX.asIso.hom E) (common_obj l Ω f E) hex hef K
    have ni : right.inv.app K = eqToHom oR.symm := by
      apply (cancel_epi (right.hom.app K)).1
      rw [Iso.hom_inv_id_app, nr]
      simp
    simp only [Functor.whiskerLeft_app, NatTrans.comp_app, Functor.whiskerRight_app,
      ni]
    rw [show left.hom.app K = eqToHom ol from nl]
    apply eq_of_heq
    have hbK : HEq
        ((automorphismStageQbarSquare l Ω C f eX eY h).hom.app (I.obj K))
        (J.map (β.hom.app K)) := by
      have hb := (automorphismStageQbarSquare_existsUnique l Ω C f eX eY h).exists.choose_spec
        (I.obj K)
      dsimp only [I, J, β, automorphismStageQbarSquare,
        GeneralAlgebraicallyClosedCoefficients.inclusion, StageSystem.ι_obj] at hb ⊢
      with_unfolding_all exact hb
    exact hbK.trans
      ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm
  rw [he]
  infer_instance

private theorem normalized_transition_shift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (r : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
      (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
        f).CommShift ℤ)
    (hn : ∀ E, automorphismStageRationalShiftNormalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f (r E))
    {E L : AlgebraicallyClosedCoefficients.Index l Ω} (h : E ≤ L) :
    let := r E
    let := r L
    let := GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X E L h
    let := GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω Y E L h
    NatTrans.CommShift (commonStagePullbackTransition l Ω f h).hom ℤ := by
  obtain ⟨sE, hE, nE⟩ := hn E
  obtain ⟨sL, hL, nL⟩ := hn L
  let := sE
  let := sL
  let := r E
  let := r L
  exact rationalPullbackTransitionShift l Ω f E L h hE hL nE.1 nL.1

/-- The rational and common-stage square comparisons preserve the descended shifts.
Source: Weil-structures paragraph, rationalization and coherent finite-field descent
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: extend the integral shift comparisons and square components by linearity
on pure tensors. Their equations remain equalities after rationalization.
At algebraically closed coefficients represent each arrow at one finite common
stage. The scalar/compositor and scalar/shift squares identify every enlargement
with the same equation. Thus the shift-compatible square descends. -/
theorem automorphismConstructibleStage_descended_shifts
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.asIso.hom ≫ f = f ≫ eX.asIso.hom) :
    (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      ∃ (cf : (rationalDerivedPullback l E f).CommShift ℤ)
        (cX : (rationalDerivedPullback l E eX.asIso.hom).CommShift ℤ)
        (cY : (rationalDerivedPullback l E eY.asIso.hom).CommShift ℤ),
        automorphismStageRationalShiftNormalization l E f cf ∧
        automorphismStageRationalShiftNormalization l E eX.asIso.hom cX ∧
        automorphismStageRationalShiftNormalization l E eY.asIso.hom cY ∧
        (fun [sf : (rationalDerivedPullback l E f).CommShift ℤ]
          [sX : (rationalDerivedPullback l E eX.asIso.hom).CommShift ℤ]
          [sY : (rationalDerivedPullback l E eY.asIso.hom).CommShift ℤ] ↦
          (rationalDerivedPullback l E f).IsTriangulated ∧
            (rationalDerivedPullback l E eX.asIso.hom).IsTriangulated ∧
            (rationalDerivedPullback l E eY.asIso.hom).IsTriangulated ∧
            NatTrans.CommShift (automorphismStageRationalSquare l E C f eX eY h).hom ℤ)
          (sf := cf) (sX := cX) (sY := cY)) ∧
    ∃ (cf : (commonStageDerivedPullback l Ω f).CommShift ℤ)
      (cX : (commonStageDerivedPullback l Ω eX.asIso.hom).CommShift ℤ)
      (cY : (commonStageDerivedPullback l Ω eY.asIso.hom).CommShift ℤ),
      automorphismStageQbarShiftNormalization l Ω f cf ∧
      automorphismStageQbarShiftNormalization l Ω eX.asIso.hom cX ∧
      automorphismStageQbarShiftNormalization l Ω eY.asIso.hom cY ∧
      (fun [sf : (commonStageDerivedPullback l Ω f).CommShift ℤ]
        [sX : (commonStageDerivedPullback l Ω eX.asIso.hom).CommShift ℤ]
        [sY : (commonStageDerivedPullback l Ω eY.asIso.hom).CommShift ℤ] ↦
        (commonStageDerivedPullback l Ω f).IsTriangulated ∧
          (commonStageDerivedPullback l Ω eX.asIso.hom).IsTriangulated ∧
          (commonStageDerivedPullback l Ω eY.asIso.hom).IsTriangulated ∧
          NatTrans.CommShift (automorphismStageQbarSquare l Ω C f eX eY h).hom ℤ)
        (sf := cf) (sX := cX) (sY := cY) := by
  classical
  constructor
  · intro E _ _ _
    exact automorphismRationalShiftDescent l E C f eX eY h
  · choose rf rx ry nf nx ny hs using
      (fun E : AlgebraicallyClosedCoefficients.Index l Ω ↦
        automorphismRationalShiftDescent l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
          C f eX eY h)
    obtain ⟨sf, hsf, ef⟩ := commonStagePullbackShiftExactDescent l Ω f rf (fun E ↦ (hs E).1)
      (normalized_transition_shift l Ω f rf nf)
    obtain ⟨sx, hsx, ex⟩ :=
      commonStagePullbackShiftExactDescent l Ω eX.asIso.hom rx (fun E ↦ (hs E).2.1)
      (normalized_transition_shift l Ω eX.asIso.hom rx nx)
    obtain ⟨sy, hsy, ey⟩ :=
      commonStagePullbackShiftExactDescent l Ω eY.asIso.hom ry (fun E ↦ (hs E).2.2.1)
      (normalized_transition_shift l Ω eY.asIso.hom ry ny)
    let := sf
    let := sx
    let := sy
    refine ⟨sf, sx, sy, (fun E ↦ ⟨rf E, nf E, hsf E⟩),
      (fun E ↦ ⟨rx E, nx E, hsx E⟩), (fun E ↦ ⟨ry E, ny E, hsy E⟩), ef, ex, ey, ?_⟩
    exact common_square_shift l Ω C f eX eY h rf rx ry hsf hsx hsy
      (fun E ↦ (hs E).2.2.2)

set_option allowUnsafeReducibility true in
attribute [local irreducible] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance 5000] sfIntegralConstructibleLinear

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageShift
attribute [local instance 5000] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stagePreadditive

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option allowUnsafeReducibility true in
attribute [local reducible] constructibleIntegralPullback

section InverseComparisons

attribute [local irreducible] integralComparisonComposition integralComparisonUnit

end InverseComparisons

end WeilConjectures

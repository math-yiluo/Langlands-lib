/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Common.CommonStagePullbackData
import WeilConjectures.SmoothPurity.Rational.RationalPullbackScalarTower
import all Mathlib.Logic.Small.Defs

/-! # The coefficient-unit normalization of common-stage pullback

Source: purity/trace equivariance proof Step 1, canonical pullback compositors.
(blueprint: lem-pur-common-stage-pullback-coefficient-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures

-- Use the same cached category structures as the coefficient comparison APIs.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] Functor.category StageSystem.instCategoryPairCategory
  ScalarLocalization.category ObjectProperty.FullSubcategory.category
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.transition
  StageSystem.ι sfRationalConstructibleLocalization ScalarLocalization.localization
  commonStagePullbackObject

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
attribute [local irreducible] rationalDerivedPullback
  constructibleIntegralPullback Scheme.residueField
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence
  sfRationalScalarExtension rationalPullbackScalarComparison sfRationalScalarComp

-- The tower equation at three equal fields forces the coefficient-unit equation.
private theorem coherent_unit {C B : Type*} [Category* C] [Category* B]
    (F : C ⥤ B) (S : C ⥤ C) (T : B ⥤ B) [T.Faithful]
    (s : S ≅ 𝟭 C) (t : T ≅ 𝟭 B) (b : F ⋙ T ≅ S ⋙ F)
    (hc : ∀ K, T.map (b.hom.app K) ≫ b.hom.app (S.obj K) ≫
      F.map (S.map (s.hom.app K)) = T.map (t.hom.app (F.obj K)) ≫ b.hom.app K)
    (K : C) : b.hom.app K ≫ F.map (s.hom.app K) = t.hom.app (F.obj K) := by
  apply T.map_injective
  apply (cancel_mono (b.hom.app K)).1
  rw [Functor.map_comp, Category.assoc]
  rw [show T.map (F.map (s.hom.app K)) ≫ b.hom.app K =
    b.hom.app (S.obj K) ≫ F.map (S.map (s.hom.app K)) from
      b.hom.naturality (s.hom.app K)]
  exact hc K

private theorem rational_scalar_unit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfRationalConstructibleCategory l E Y) :
    (rationalPullbackScalarComparison l E E (AlgHom.id (Padic l) E) f).hom.app K ≫
      (rationalDerivedPullback l E f).map
        ((sfRationalScalarUnit l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app K) =
    (sfRationalScalarUnit l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app
      ((rationalDerivedPullback l E f).obj K) := by
  let S (W : Scheme.{u}) := sfRationalScalarExtension l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E (AlgHom.id (Padic l) E)
  have hfaith : (S X).Faithful :=
    Functor.Faithful.of_iso
      (sfRationalScalarUnit l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))).symm
  apply coherent_unit (rationalDerivedPullback l E f) (S Y) (S X)
    (sfRationalScalarUnit l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)))
    (sfRationalScalarUnit l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)))
    (rationalPullbackScalarComparison l E E (AlgHom.id (Padic l) E) f) _ K
  intro M
  have hc := rationalPullbackScalarComparison_tower l E E E
    (AlgHom.id (Padic l) E) (AlgHom.id (Padic l) E) f M
  simpa only [AlgHom.id_comp, (sfRationalScalar_coherence l E E (AlgHom.id (Padic l) E) Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E (AlgHom.id (Padic l) E)).1,
    (sfRationalScalar_coherence l E E (AlgHom.id (Padic l) E) X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E (AlgHom.id (Padic l) E)).1] using hc

private theorem rational_scalar_unit_iso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (i : E →ₐ[Padic l] E) (hi : i = AlgHom.id (Padic l) E)
    (K : sfRationalConstructibleCategory l E Y) :
    (rationalPullbackScalarComparison l E E i f).app K ≪≫
      (rationalDerivedPullback l E f).mapIso
        ((eqToIso (congrArg
          (sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) E)
          hi)).app K ≪≫
          (sfRationalScalarUnit l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))).app K) =
    (eqToIso (congrArg
      (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) E)
      hi)).app ((rationalDerivedPullback l E f).obj K) ≪≫
      (sfRationalScalarUnit l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))).app
        ((rationalDerivedPullback l E f).obj K) := by
  subst i
  apply Iso.ext
  simpa using rational_scalar_unit l E f K

set_option allowUnsafeReducibility true in
attribute [local semireducible] GeneralAlgebraicallyClosedCoefficients.Stage

private def stageUnit (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω W).T (le_refl E) ≅
      𝟭 (GeneralAlgebraicallyClosedCoefficients.Stage l Ω W E) :=
  operationStageTransitionIso l Ω W E E le_rfl ≪≫
    GeneralAlgebraicallyClosedCoefficients.unitor l Ω W E

private theorem conjugate_unit_iso {C B : Type*} [Category* C] [Category* B]
    (F : C ⥤ B) {A A' : B} {K K' N : C}
    (a : A ≅ A') (b : K ≅ K') (q : A' ≅ F.obj K')
    (s : K' ≅ N) (t : A' ≅ F.obj N) (h : q ≪≫ F.mapIso s = t) :
    (a ≪≫ q ≪≫ F.mapIso b.symm) ≪≫ F.mapIso (b ≪≫ s) = a ≪≫ t := by
  simp only [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc,
    Iso.symm_self_id_assoc, h]

private theorem unitor_app (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) (E : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω W E) :
    (GeneralAlgebraicallyClosedCoefficients.unitor l Ω W E).app K =
      (eqToIso (congrArg
        (sfRationalScalarExtension l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
          W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))
        ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).1 E))).app K ≪≫
      (sfRationalScalarUnit l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime))).app K := by
  exact NatIso.trans_app _ _ K

private theorem stageUnit_app (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) (E : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω W E) :
    (stageUnit l Ω W E).app K =
      (operationStageTransitionIso l Ω W E E le_rfl).app K ≪≫
        (GeneralAlgebraicallyClosedCoefficients.unitor l Ω W E).app K := by
  exact NatIso.trans_app _ _ K

attribute [local irreducible] commonStagePullbackComparison stageUnit
  operationStageTransitionIso GeneralAlgebraicallyClosedCoefficients.unitor

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Stage

private theorem comparison_self (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    commonStagePullbackComparison l Ω f P P.stage le_rfl ≪≫
      (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u}
        l Ω P.stage) f).mapIso ((stageUnit l Ω Y P.stage).app P.obj) =
      (stageUnit l Ω X P.stage).app (commonStagePullbackObject l Ω f P).obj := by
  have hc := rational_scalar_unit_iso l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω P.stage P.stage le_rfl)
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).1 P.stage) P.obj
  have hc' : (rationalPullbackScalarComparison l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω P.stage P.stage le_rfl)
      f).app P.obj ≪≫
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f).mapIso
        ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω Y P.stage).app P.obj) =
      (GeneralAlgebraicallyClosedCoefficients.unitor l Ω X P.stage).app
        ((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f).obj P.obj) := by
    have hy := unitor_app l Ω Y P.stage P.obj
    have hx := unitor_app l Ω X P.stage ((rationalDerivedPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f).obj P.obj)
    have ht := congrArg (fun e ↦ (rationalPullbackScalarComparison l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω P.stage P.stage le_rfl)
      f).app P.obj ≪≫ (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f).mapIso e) hy
    exact ht.trans (hc.trans hx.symm)
  have he := @conjugate_unit_iso
    (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y P.stage)
    (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X P.stage)
    (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω Y P.stage)
    (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω X P.stage)
    (rationalDerivedPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f)
    _ _ _ _ _
    ((operationStageTransitionIso l Ω X P.stage P.stage le_rfl).app
      (commonStagePullbackObject l Ω f P).obj)
    ((operationStageTransitionIso l Ω Y P.stage P.stage le_rfl).app P.obj)
    ((rationalPullbackScalarComparison l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω P.stage P.stage le_rfl)
      f).app P.obj)
    ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω Y P.stage).app P.obj)
    ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω X P.stage).app
      ((rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f).obj P.obj)) hc'
  have hy := congrArg (fun e ↦ commonStagePullbackComparison l Ω f P P.stage le_rfl ≪≫
    (rationalDerivedPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f).mapIso e)
    (stageUnit_app l Ω Y P.stage P.obj)
  unfold commonStagePullbackComparison at hy ⊢
  exact hy.trans (he.trans (stageUnit_app l Ω X P.stage
    (commonStagePullbackObject l Ω f P).obj).symm)

/-- The common-stage pullback comparison at its literal coefficient stage respects
its actual transition unitor.
Source: blueprint purity/trace equivariance Step 1, scalar-unit normalization.
(blueprint: lem-pur-common-stage-pullback-coefficient-unit).
Proof: specialize the rational pullback/scalar tower law to three equal fields and
two identity inclusions. Scalar associator-unit coherence and faithfulness give the
rational coefficient-unit equation. Transport it through the coefficient-inclusion
identity and the recorded stage-transition isomorphisms. The inverse transition
comparison cancels its forward comparison. This also applies to zero objects and
empty schemes; no larger coefficient field or geometric hypothesis is used. -/
theorem commonStagePullbackComparison_self_unit (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    commonStagePullbackComparison l Ω f P P.stage le_rfl ≪≫
      (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u}
        l Ω P.stage) f).mapIso ((operationStageTransitionIso l Ω Y P.stage P.stage le_rfl ≪≫
        GeneralAlgebraicallyClosedCoefficients.unitor l Ω Y P.stage).app P.obj) =
      (operationStageTransitionIso l Ω X P.stage P.stage le_rfl ≪≫
        GeneralAlgebraicallyClosedCoefficients.unitor l Ω X P.stage).app
          (commonStagePullbackObject l Ω f P).obj := by
  have h := comparison_self l Ω f P
  unfold stageUnit at h
  exact h

end WeilConjectures

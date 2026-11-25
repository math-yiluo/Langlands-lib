/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Common-stage internal Hom objects and comparisons

The existing common-stage Hom definitions, extracted without changing their bodies.
Source: prose-03-02, common-stage internal-Hom paragraph.
(blueprint: def-weil-common-stage-internal-hom-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open Opposite CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
  Padic.coefficientExtensionAbsoluteValue integralDerivedInternalHom
  rationalDerivedInternalHom ScalarLocalization.composition
  StageSystem.PairCategory.mkHom sfIntegralConstructible ScalarLocalization.linear
  ScalarLocalization.preadditive Linear.homModule Preadditive.homGroup
  Preadditive.fullSubcategory Linear.fullSubcategory sfIntegralConstructibleLinear
  rationalHomScalarComparison sfConstructibleIntegralScalarExtension
  sfIntegralScalarComp sfIntegralScalarUnit

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

private theorem rationalScalar_obj (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u})
    (K : sfRationalConstructibleCategory l E W) :
    (sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K =
      ScalarLocalization.mk ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj K.obj) := by
  exact (sfRationalScalarExtension_existsUnique l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1 K

attribute [local irreducible] sfRationalScalarExtension

open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

-- Match the transported structures on the small coefficient models.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The recorded stage transition is the specified rational scalar functor.
The equality is part of the existing stage-system uniqueness specification.
Source: blueprint common-stage coefficient construction
(blueprint: prose-03-02). -/
def operationStageTransitionIso (W : Scheme.{u})
    (E L : Index l Ω) (h : E ≤ L) :
    (stageSystem l Ω W).T h ≅ transition l Ω W E L h :=
  eqToIso ((stageSystem_existsUnique l Ω W).exists.choose_spec.1 E L h)

attribute [local irreducible] operationStageTransitionIso

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

private theorem operationStageIntegralObject (W : Scheme.{u})
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : Index l Ω) (h : P.stage ≤ L) :
    (P.toStage h).obj =
      (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime))
        (Coefficient.{u} l Ω P.stage) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω P.stage L h) W).obj P.obj.obj := by
  change (((stageSystem l Ω W).T h).obj P.obj).obj = _
  have ht : (stageSystem l Ω W).T h = transition l Ω W P.stage L h := by
    simpa only [stageSystem] using
      (stageSystem_existsUnique l Ω W).exists.choose_spec.1 P.stage L h
  have hi := rationalScalar_obj l (Coefficient.{u} l Ω P.stage)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω P.stage L h) W P.obj
  exact (congrArg (fun F : Stage l Ω W P.stage ⥤ Stage l Ω W L ↦
    (F.obj P.obj).obj) ht).trans (congrArg ScalarLocalization.obj hi)

private noncomputable def operationStageIntegralAssociator (W : Scheme.{u})
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (M L : Index l Ω) (h : P.stage ≤ M) (k : M ≤ L) :
    (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime))
      (Coefficient.{u} l Ω M) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω M L k) W).obj (P.toStage h).obj ≅
      (P.toStage (h.trans k)).obj :=
  eqToIso (congrArg (fun K ↦ (sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime))
    (Coefficient.{u} l Ω M) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω M L k) W).obj K)
      (operationStageIntegralObject l Ω W P M h)) ≪≫
    (sfIntegralScalarComp l (Coefficient.{u} l Ω P.stage) (Coefficient.{u} l Ω M)
      (coefficientInclusion l Ω P.stage M h) W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω M L k)).app P.obj.obj ≪≫
    eqToIso (congrArg (fun ι ↦ (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime))
      (Coefficient.{u} l Ω P.stage) (Coefficient.{u} l Ω L) ι W).obj P.obj.obj)
        ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2
          P.stage M L h k)) ≪≫
    (eqToIso (operationStageIntegralObject l Ω W P L (h.trans k))).symm

attribute [local irreducible] operationStageIntegralAssociator

/-- The permitted common-stage Hom pairs: extend both entries to their compositum,
then require exactly the integral-Hom constructibility predicate there.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: prose-03-02). -/
def commonStageHomPairs (W : Scheme.{u}) :
    ObjectProperty ((generalAlgebraicallyClosedConstructibleCategory l Ω W)ᵒᵖ ×
      generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  fun P ↦ constructibleRationalHomPairs l
    (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω P.1.unop.stage P.2.stage)) W
    (op (P.1.unop.toStage
      ((Padic.finiteCoefficientFields_properties l Ω).1 P.1.unop.stage P.2.stage).1),
      P.2.toStage
        ((Padic.finiteCoefficientFields_properties l Ω).1 P.1.unop.stage P.2.stage).2)

/-- The literal permitted rational pair at the compositum, with no choice of lift.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: prose-03-02). -/
def commonStageHomRationalPair (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory) :
    (constructibleRationalHomPairs l
      (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω
        P.obj.1.unop.stage P.obj.2.stage)) W).FullSubcategory :=
  ⟨(op (P.obj.1.unop.toStage
      ((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).1),
    P.obj.2.toStage ((Padic.finiteCoefficientFields_properties l Ω).1
      P.obj.1.unop.stage P.obj.2.stage).2), P.property⟩

/-- Common-stage internal Hom is the literal pair at the coefficient compositum.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: prose-03-02). -/
def commonStageHomObject (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory) :
    generalAlgebraicallyClosedConstructibleCategory l Ω W :=
  ⟨Padic.finiteCoefficientCompositum l Ω P.obj.1.unop.stage P.obj.2.stage,
    (rationalDerivedInternalHom l (Coefficient.{u} l Ω
      (Padic.finiteCoefficientCompositum l Ω P.obj.1.unop.stage P.obj.2.stage)) W).obj
        (commonStageHomRationalPair l Ω W P)⟩

/-- A permitted compositum pair remains permitted at every larger finite stage.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: prose-03-02).
Proof: rationalHomScalarPair_permitted first extends the permitted integral pair.
The two integral scalar associators identify its entries with the entries extended
directly from their original stages. Internal Hom uses the inverse first
associator and the second associator. Its underlying integral isomorphism preserves
constructibility. Thus the displayed predicate holds before rationalization,
including identity inclusions and every further stage. -/
theorem commonStageHomPairAtStage_permitted (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω W P).stage ≤ L) :
    constructibleRationalHomPairs l (Coefficient.{u} l Ω L) W
      (op (P.obj.1.unop.toStage
        (((Padic.finiteCoefficientFields_properties l Ω).1
          P.obj.1.unop.stage P.obj.2.stage).1.trans h)),
        P.obj.2.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
          P.obj.1.unop.stage P.obj.2.stage).2.trans h)) := by
  let M := Padic.finiteCoefficientCompositum l Ω P.obj.1.unop.stage P.obj.2.stage
  have hM := (Padic.finiteCoefficientFields_properties l Ω).1
    P.obj.1.unop.stage P.obj.2.stage
  let A := Coefficient.{u} l Ω M
  let B := Coefficient.{u} l Ω L
  let e₁ := operationStageIntegralAssociator l Ω W P.obj.1.unop M L hM.1 h
  let e₂ := operationStageIntegralAssociator l Ω W P.obj.2 M L hM.2 h
  have hP := integralHomScalarPair_permitted l A B
    (coefficientInclusion l Ω M L h) W
      (integralPairOfRationalHomPair l A W (commonStageHomRationalPair l Ω W P))
  let e := (integralDerivedInternalHom l B W).mapIso
    (Iso.prod ((sfIntegralConstructible l B W).ι.mapIso e₁).symm.op
      ((sfIntegralConstructible l B W).ι.mapIso e₂))
  exact (sfIntegralConstructible l B W).prop_of_iso e hP

/-- The permitted pair at a larger stage, using the actual scalar extensions.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: prose-03-02). -/
def commonStageHomPairAtStage (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω W P).stage ≤ L) :
    (constructibleRationalHomPairs l (Coefficient.{u} l Ω L) W).FullSubcategory :=
  ⟨(op (P.obj.1.unop.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).1.trans h)),
    P.obj.2.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
      P.obj.1.unop.stage P.obj.2.stage).2.trans h)),
    commonStageHomPairAtStage_permitted l Ω W P L h⟩

section ComparisonElaboration
attribute [local irreducible] ObjectProperty.FullSubcategory.category

/-- The Hom comparison includes the inverse first-variable scalar associator.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: prose-03-02). -/
def commonStageHomComparison (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω W P).stage ≤ L) :
    (commonStageHomObject l Ω W P).toStage h ≅
      (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W).obj
        (commonStageHomPairAtStage l Ω W P L h) :=
  (operationStageTransitionIso l Ω W _ L h).app
      (commonStageHomObject l Ω W P).obj ≪≫
    rationalHomScalarComparison l
      (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω
        P.obj.1.unop.stage P.obj.2.stage))
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω _ L h) W
        (commonStageHomRationalPair l Ω W P) ≪≫
    (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W).mapIso
      (ObjectProperty.isoMk _ (Iso.prod
        (((operationStageTransitionIso l Ω W _ L h).app
            (P.obj.1.unop.toStage ((Padic.finiteCoefficientFields_properties l Ω).1
              P.obj.1.unop.stage P.obj.2.stage).1)).symm ≪≫
          ((stageSystem l Ω W).assoc ((Padic.finiteCoefficientFields_properties l Ω).1
            P.obj.1.unop.stage P.obj.2.stage).1 h).app P.obj.1.unop.obj).symm.op
        (((operationStageTransitionIso l Ω W _ L h).app
            (P.obj.2.toStage ((Padic.finiteCoefficientFields_properties l Ω).1
              P.obj.1.unop.stage P.obj.2.stage).2)).symm ≪≫
          ((stageSystem l Ω W).assoc ((Padic.finiteCoefficientFields_properties l Ω).1
            P.obj.1.unop.stage P.obj.2.stage).2 h).app P.obj.2.obj)))

end ComparisonElaboration

attribute [local irreducible] commonStageHomComparison

set_option allowUnsafeReducibility true in
attribute [local reducible] commonStageHomObject commonStageHomPairAtStage

end WeilConjectures

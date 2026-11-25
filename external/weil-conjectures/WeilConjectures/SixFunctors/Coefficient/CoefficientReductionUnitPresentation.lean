/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientSystemScalarCalculus
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Strict quotient-unit presentations for reduction representatives

Source: Stacks 06YS, 06YY, 07A6 and 0941. These predicates depend on the reduction
functor, its adjunction and finite comparisons, independently of the closed tensor data.
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] DerivedCategory DerivedCategory.Q DerivedCategory.Qh
  _root_.instCategoryDerivedCategory HasDerivedCategory.standard
  SheafOfModules.instPreadditive HomologicalComplex.instPreadditive
  completedIntegralCoefficientSheafUnrestricted scalarReductionExtension
  coefficientFiniteReductionModel CoefficientComparisonEquation CoefficientTransitionEquation
  coefficientComplexCompositeTransformation
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local semireducible] DerivedCategory DerivedCategory.Q DerivedCategory.Qh
  _root_.instCategoryDerivedCategory HomologicalComplex.instPreadditive in
/-- The whole reduction adjunction is computed by the strict quotient-unit map.
Finite derived evaluations do not fix this equality of system morphisms. The second
clause fixes the ordinary unit at every degree and coefficient level.
Source: Stacks 06YY, 07A6 and 0941, deriving the ordinary quotient/limit adjunction
(blueprint: def-coef-strict-reduction-unit-presentation). -/
def CoefficientStrictReductionUnitPresentation
    (reduction : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W)
    (adjunction : reduction ⊣ coefficientSequenceLimit l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (e : reduction.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P) :
    Prop :=
  ∃ z : P ⟶ (((coefficientSequenceRestriction l E W ⋙
      (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W))
        |>.mapHomologicalComplex (.up ℤ)).obj C),
    adjunction.homEquiv _ _ e.hom =
      DerivedCategory.Q.map z ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            (Iso.refl (coefficientSequenceRestriction l E W ⋙
              (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)))
            (.up ℤ)).inv.app C) ≫
        cast (by rfl)
          ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W
            ).rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj
              (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C))) ≫
        (coefficientConstantTowerLimit l E W).map
          ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app C) ∧
    ∀ n : ℕ,
      z ≫ (NatTrans.mapHomologicalComplex
        (Functor.whiskerLeft (coefficientSequenceRestriction l E W) (lim.π (op n)))
          (.up ℤ)).app C ≫
        (NatIso.mapHomologicalComplex
          (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) (.up ℤ)).hom.app C ≫
        ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map (κ n).hom =
      ((scalarReductionExtension_adjunction l E W n).choose.mapHomologicalComplex
        (.up ℤ)).unit.app P

attribute [local irreducible] CoefficientStrictReductionUnitPresentation

/-- A tensor representative retains the finite and horizontal laws as its first two
projections, followed by its strict whole-system adjunction normalization.
Source: Stacks 06YS, 06YY, 07A6, 0941
(blueprint: def-coef-strict-reduction-unit-presentation). -/
structure CoefficientStrictReductionTensorPresentation
    (reduction : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W)
    (adjunction : reduction ⊣ coefficientSequenceLimit l E W)
    (reductionEvaluation : ∀ n : ℕ,
      reduction ⋙ coefficientSequenceDerivedEvaluation l E W n ≅
        coefficientFiniteDerivedExtension l E W n)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (e : reduction.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj C ≅
        ((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :
    Prop where
  /-- The original finite representative equations. -/
  finite : ∀ n : ℕ,
    CoefficientComparisonEquation
      ((coefficientSequenceDerivedEvaluation l E W n).map e.hom)
      ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app C)
      (DerivedCategory.Q.map (κ n).hom)
      ((reductionEvaluation n).hom.app (DerivedCategory.Q.obj P))
      ((coefficientFiniteReductionModel l E W P hP n).hom)
  /-- The original horizontal representative equations. -/
  horizontal : ∀ (m n : ℕ) (h : n ≤ m),
    CoefficientTransitionEquation
      (coefficientComplexCompositeTransformation
        (coefficientSequenceEvaluation l E W n) (normalizedDVRModuleRes l E W h)
        (coefficientSequenceTransition l E W h) C)
      (((normalizedDVRModuleRes l E W h).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (κ n).hom)
      ((κ m).hom)
      (coefficientComplexCompositeTransformation
        (scalarReductionExtension l E W n) (normalizedDVRModuleRes l E W h)
        (coefficientOrdinaryQuotient l E W h) P)
  /-- The retained actual ordinary quotient-unit transpose. -/
  adjunction : CoefficientStrictReductionUnitPresentation l E W reduction adjunction P C e κ

end WeilConjectures

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsCoreData
import WeilConjectures.SixFunctors.CoefficientSectionsCoreComparison.NormalizedSectionsLimitComparison
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits

/-! Equations for the normalized coefficient-sections core data.
Source: Stacks 079P, 0941, 0D6E and 03CZ.
(blueprint: lem-coef-derived-sections-core-equations)
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b av bv
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
namespace WeilConjectures

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  SheafOfModules.monoidalCategory HasDerivedCategory.standard

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

private theorem comparison_eq_unit
    {A : Type a} {B : Type b} [Category.{av} A] [Abelian A]
    [Category.{bv} B] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive]
    (K : CochainComplex A ℤ) :
    coefficientRightDerivedComparison F K = F.rightDerivedFunctorUnitQ K := by
  rfl

/-- The resolution and projection equations for transported sections data.
Source: Stacks 079P, 0941 and 0D6E; the simultaneous sections/limit comparison
and its actual finite projections.
Proof: apply the normalized sections/limit comparison to the transported pairs,
then identify each derived projection with the prescribed coefficient projection by
uniqueness of the corresponding right-derived comparison. The universal-unit
identity gives the first clause, and the finite projection identity gives the second.
(blueprint: lem-coef-derived-sections-core-equations) -/
def CoefficientDerivedSectionsCoreResolutionEquation
    (R : CoefficientDerivedSystemReduction l E W)
    (D : CoefficientDerivedSectionsCoreData l E W R) : Prop :=
  ∀ (K : CochainComplex (coefficientSequenceModules l E W) ℤ),
    CoefficientComparisonEquation
      (coefficientGlobalLimitLeftComparison l E W
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))
      ((coefficientIntegralSections l E W).map
          ((coefficientConstantTowerLimit l E W).map
            ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app K)))
      (D.globalLimit.hom.app (DerivedCategory.Q.obj K))
      (coefficientGlobalLimitRightComparison l E W
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))
      (coefficientMappingLimit.{max u (t + 1)}.map
        ((coefficientTowerSections l E W).rightDerivedFunctor.map
          ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app K)))

/-- A preliminary package supplies scalar coherence for normalized sections comparisons.
Source: Stacks 079P, 0941, 0D6E and 03CZ; the normalized coefficient-sections construction.

Proof: use the canonical cochain right-derived pairs for Hom from the integral module
unit and its termwise tower functor. The normalized constant-tower comparison supplies
κ and β. Whisker by exact sequence restriction and compose β with the prescribed
restricted-evaluation isomorphism and the scalar comparison from D. Uniqueness of the
ordinary comparison identifies it with coefficientSectionsLimitIso. Naturality of κ
against the exact restriction factorization gives the resolution equation. The
constant-tower projection equation, whiskered and composed with the same evaluation
and scalar maps, gives the required actual finite projections.

The former assertion for every independent choice of D was missing normalization:
changing the sign of just one comparison preserves its type but not its unit equation.
The conclusion therefore constructs normalized choices, as needed by the parent.
(blueprint: lem-coef-derived-sections-core-equations) -/
theorem coefficientDerivedSectionsCoreEquations
    (R : CoefficientDerivedSystemReduction l E W)
    (_hF : CoefficientFiniteTensorNormalization l E W R)
    (D : CoefficientDerivedSectionsCoreData l E W R) :
    ∃ D' : CoefficientDerivedSectionsCoreData l E W R,
    CoefficientDerivedSectionsCoreResolutionEquation l E W R D' ∧
      (∀ (M : coefficientSequenceDerived l E W) (n : ℕ),
        D'.globalLimit.hom.app M ≫
            (coefficientMappingProjection.{max u (t + 1)} n).app
              ((coefficientSequenceDerivedRestriction l E W ⋙
                (coefficientTowerSections l E W).rightDerivedFunctor).obj M) ≫
            (D'.systemSectionsEvaluation n).hom.app M =
          (coefficientIntegralSections l E W).map
              ((coefficientSequenceProjection l E W n).app M) ≫
            (D'.scalar.scalarSections n).hom.app
              ((coefficientSequenceDerivedEvaluation l E W n).obj M)) := by
  classical
  let G : scalarReductionSource l E W ⥤ AddCommGrpCat.{max u (t + 1)} :=
    coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)
  have : PreservesLimits G := CategoryTheory.preservesLimits_preadditiveCoyoneda_obj _
  have : PreservesLimitsOfSize.{0, 0} G := preservesLimitsOfSize_shrink G
  have : IsGrothendieckAbelian.{max u (t + 1)} (scalarReductionSource l E W) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1, t, u}
      (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)).1
  have hm {X Y : DerivedCategory (scalarReductionSource l E W)} (f : X ⟶ Y) :
      (coefficientIntegralSections l E W).map f = G.rightDerivedFunctor.map f := by rfl
  have hs (Y : CochainComplex (scalarReductionSource l E W) ℤ) :
      coefficientSiteSectionsComparison.{u, t+1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) Y = G.rightDerivedFunctorUnitQ Y := by
    exact comparison_eq_unit G Y
  have he : coefficientSectionsLimitIso l E W = preservesLimitNatIso G (J := ℕᵒᵖ) := by
    exact ((coefficientSectionsLimitIso_exists l E W).choose_spec.2 _
      (fun T n ↦ preservesLimitIso_hom_π G T (op n))).symm
  obtain ⟨κ, hκ⟩ := CoefficientSectionsCoreComparison.comparison_exists G
  obtain ⟨β, hβ⟩ := CoefficientSectionsCoreComparison.evaluation_exists G
  let ε (n : ℕ) :=
    Functor.isoWhiskerLeft (coefficientSequenceDerivedRestriction l E W) (β n) ≪≫
      Functor.isoWhiskerRight (coefficientRestrictedEvaluationIso l E W n)
        (coefficientIntegralSections l E W) ≪≫
      Functor.isoWhiskerLeft (coefficientSequenceDerivedEvaluation l E W n)
        (D.scalar.scalarSections n)
  let D' : CoefficientDerivedSectionsCoreData l E W R :=
    { scalar := D.scalar
      systemSectionsEvaluation := ε
      globalLimit := Functor.isoWhiskerLeft (coefficientSequenceDerivedRestriction l E W) κ }
  refine ⟨D', ?_, ?_⟩
  · intro K
    let X := ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj K
    have hresult := CoefficientSectionsCoreComparison.comparison_morphism G κ X (hκ X)
      ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app K)
    dsimp only [CoefficientDerivedSectionsCoreResolutionEquation, CoefficientComparisonEquation,
      coefficientGlobalLimitLeftComparison, coefficientGlobalLimitRightComparison]
    rw [he]
    dsimp only [D', Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
    simp only [Category.assoc]
    simpa only [G, X, hs, hm, coefficientConstantTowerLimit,
      coefficientTowerSections, coefficientSequenceDerivedRestriction,
      comparison_eq_unit, coefficientMappingLimit, Functor.comp_obj, Functor.comp_map,
      NatIso.mapHomologicalComplex, Category.assoc]
      using hresult
  · intro M n
    have hπA := fun (X : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ) ↦
      CoefficientSectionsCoreComparison.projection_unit n
        (coefficientConstantTowerProjection l E W n)
        (coefficientConstantTowerProjection_exists l E W n).choose_spec.1 X
    have hπB := fun (X : CochainComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{max u (t + 1)}) ℤ) (n : ℕ) ↦
      CoefficientSectionsCoreComparison.projection_unit n
        (coefficientMappingProjection.{max u (t + 1)} n)
        (coefficientMappingProjection_exists.{max u (t + 1)} n).choose_spec.1 X
    have hp := CoefficientSectionsCoreComparison.comparison_projection G
      (coefficientConstantTowerProjection l E W) (coefficientMappingProjection) β κ
      hπA hπB hβ hκ ((coefficientSequenceDerivedRestriction l E W).obj M) n
    dsimp only [D', ε, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
    have h := congrArg (fun z ↦ z ≫ G.rightDerivedFunctor.map
      ((coefficientRestrictedEvaluationIso l E W n).hom.app M) ≫
        (D.scalar.scalarSections n).hom.app
          ((coefficientSequenceDerivedEvaluation l E W n).obj M)) hp
    simpa only [G, coefficientSequenceProjection, coefficientSequenceLimit,
      coefficientIntegralSections, coefficientGlobalSections, coefficientConstantTowerLimit,
      coefficientTowerSections, Functor.comp_obj, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.map_comp, Category.assoc] using h

end WeilConjectures

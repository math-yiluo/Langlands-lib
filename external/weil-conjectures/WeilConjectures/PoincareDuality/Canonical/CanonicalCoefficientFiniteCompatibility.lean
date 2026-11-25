/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Canonical.CanonicalCoefficientPullbackModels
import all WeilConjectures.PoincareDuality.Canonical.CanonicalCoefficientPullbackModels
import all WeilConjectures.PoincareDuality.Canonical.CanonicalCoefficientUnitNormalization
import all WeilConjectures.PoincareDuality.Canonical.CanonicalCoefficientChainNormalization
import all WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure

set_option linter.privateModule false

/-!
# Compatibility of canonical finite coefficient projections

Source: Stacks Tags 03D6 and 08TC; the regular-unit and Roos APIs in
`WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure`.
(blueprint: lem-pod-canonical-coefficient-pullback-reduction).

This module contains proved comparison results and private helpers for the coefficient comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] regularExtensionIso regularExtensionPresheafIso
  identityRestrictionIso scalarReductionExistence HasDerivedCategory.standard
  unrestrictedIntegralReductionExistence limit finiteRegularIso finiteSingleRegularIso
  finitePullbackRegularIso pullbackLevelRegularIso pullbackUnitLevel chainUnitCandidate
  integralDerivedPullback integralDerivedPullbackComparison
  constantWeilIntegralRoosComparison
  constantWeilIntegralLambda constantWeilDerivedCoefficientComparison
  SheafOfModules.monoidalCategory constantSheaf
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] canonicalCoefficientIntegralComparison
  canonicalCoefficientInverseImageTransport
  canonicalCoefficientLambda canonicalCoefficientKappa canonicalCoefficientLambdaFinite
  canonicalCoefficientFiniteComparison canonicalCoefficientPullbackReductionIso
  canonicalCoefficientRho canonicalCoefficientProjection canonicalCoefficientInverseProjection
  canonicalCoefficientTheta canonicalCoefficientPullbackTransition canonicalCoefficientTransition
  canonicalCoefficientInverseTransition

attribute [local irreducible] canonicalCoefficientIntegralUnit
  canonicalCoefficientFiniteUnit canonicalCoefficientFiniteKappaComplex
  coefficientFiniteInverseIso coefficientFinitePullIso

attribute [local irreducible] coefficientProjectionComplex

private theorem coefficientProjectionComplex_one (W : Scheme.{u}) (n : ℕ)
    (U : W.ProEtᵒᵖ) :
    ((coefficientProjectionComplex l E W n).f 0).val.app U
      (constantWeilUnitSection l E W U.unop) =
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (SheafOfModules.unit (integralCoefficientSheaf l E W n))).inv.val.app U
        (1 : (integralCoefficientSheaf l E W n).obj.obj U) := by
  let sX := HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W))
  let sB := HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit (integralCoefficientSheaf l E W n))
  have h : sX.inv ≫ (coefficientProjectionComplex l E W n).f 0 =
      constantCoefficientProjection l E W n ≫
        (scalarReductionRestriction l E W n).map sB.inv := by
    simp only [coefficientProjectionComplex, HomologicalComplex.comp_f,
      Functor.mapCochainComplexSingleFunctor,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      CochainComplex.singleFunctor,
      HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc, sX, sB]
  change ((sX.inv ≫ (coefficientProjectionComplex l E W n).f 0).val.app U)
    (1 : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U) = _
  rw [h]
  change sB.inv.val.app U
    ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U 1 * 1) = _
  rw [map_one, one_mul]

private theorem coefficientProjectionReduction_one (W : Scheme.{u}) (n : ℕ)
    (U : W.ProEtᵒᵖ) :
    ((coefficientProjectionComplex l E W n ≫
      (canonicalCoefficientRes l E W n).map (finiteSingleRegularIso l E W n).inv).f 0).val.app U
        (constantWeilUnitSection l E W U.unop) =
      constantWeilReducedUnitSection l E W n U.unop := by
  have hinj : Function.Injective (((finiteSingleRegularIso l E W n).hom.f 0).val.app U) := by
    intro x y h
    have h' := congrArg (fun z ↦ ((finiteSingleRegularIso l E W n).inv.f 0).val.app U z) h
    change (((finiteSingleRegularIso l E W n).hom ≫
      (finiteSingleRegularIso l E W n).inv).f 0).val.app U x =
      (((finiteSingleRegularIso l E W n).hom ≫
        (finiteSingleRegularIso l E W n).inv).f 0).val.app U y at h'
    simpa only [Iso.hom_inv_id, HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply] using h'
  apply hinj
  rw [finiteSingleRegularIso_one]
  change ((coefficientProjectionComplex l E W n ≫
    (canonicalCoefficientRes l E W n).map (finiteSingleRegularIso l E W n).inv ≫
    (canonicalCoefficientRes l E W n).map (finiteSingleRegularIso l E W n).hom).f 0).val.app U
      (constantWeilUnitSection l E W U.unop) = _
  rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  exact coefficientProjectionComplex_one l E W n U

private theorem coefficientProjection_step (W : Scheme.{u}) (n : ℕ) :
    coefficientProjectionComplex l E W (n + 1) ≫ canonicalCoefficientTransition l E W n =
      coefficientProjectionComplex l E W n := by
  have hi : (@asIso _ _ _ _ (canonicalCoefficientReductionComplex l E W (n + 1))
      ((canonicalCoefficientModelMaps_isIso l E (𝟙 W)).2 (n + 1)).2.1) =
      finiteSingleRegularIso l E W (n + 1) := by
    apply Iso.ext
    exact coefficientReductionComplex_eq l E W (n + 1)
  let T : W.ProEt := ProEt.mk (𝟙 W)
  apply regular_hom_ext l E W T (MorphismProperty.Over.mkIdTerminal _ W)
  unfold canonicalCoefficientTransition
  rw [hi, coefficientReductionComplex_eq]
  rw [← Category.assoc]
  change ((finiteSingleRegularIso l E W n).hom.f 0).val.app (op T)
    ((((unrestrictedIntegralTransition l E W n).app
      (constantWeilIntegralComplex l E W)).f 0).val.app (op T)
        (((coefficientProjectionComplex l E W (n + 1) ≫
          (canonicalCoefficientRes l E W (n + 1)).map
            (finiteSingleRegularIso l E W (n + 1)).inv).f 0).val.app (op T)
            (constantWeilUnitSection l E W T))) = _
  rw [coefficientProjectionReduction_one, reducedUnit_transition, finiteSingleRegularIso_one]
  exact (coefficientProjectionComplex_one l E W n (op T)).symm

end WeilConjectures

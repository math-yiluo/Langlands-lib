/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.CategoryTheory.Derived.DerivedTowerCounitProjections
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitStrictQuotientModel
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Simultaneous Roos, counit and strict quotient-unit normalization

Source: Stacks Project, Cohomology on Sites, Tag 0941, lemma-derived-limit-is-ok;
whole-system adjunction and quotient-unit refinements extracted from the integral
trace-transport construction (blueprint: lem-trf-roos-adjunction-quotient-normalization).

The coefficient field F is arbitrary: apply this statement to each of E, L and M.
No distinctness or compatibility between different coefficient fields is required.
Index n denotes the positive quotient exponent n+1. The site and coefficient
universes remain independent. All categories are ordinary unbounded derived categories.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures

section Normalization

variable (l : ℕ) [Fact l.Prime] (F : Type u) [Field F]
  [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F] (W : Scheme.{t})
  {S : CoefficientDerivedSystemCalculus l F W}
  {M : CompletionUnit.OrdinaryModel l F W}
  (D : CompletionUnit.DerivedModel l F W S M)

private theorem limitUnit_isIso
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l F W) ℤ) [I.IsKInjective] :
    IsIso (D.limitUnit.app I) := by
  have : IsIso (D.limitUnit.app I ≫
      ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l F W) ⥤
        scalarReductionSource l F W).rightDerivedFunctorObjQIso I).hom) := by
    rw [D.limitUnit_normalization]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l F W) ⥤
      scalarReductionSource l F W).rightDerivedFunctorObjQIso I).hom

include D in
private theorem inclusion_quasiIso
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l F W) ℤ) [I.IsKInjective] :
    QuasiIso (roosι I) := by
  have := limitUnit_isIso l F W D I
  have : IsIso (DerivedCategory.Q.map (roosι I) ≫ D.roos.hom.app I) := by
    rw [D.roos_normalization]
    infer_instance
  have : IsIso (DerivedCategory.Q.map (roosι I)) :=
    IsIso.of_isIso_comp_right _ (D.roos.hom.app I)
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp this

private theorem limitUnit_projection
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l F W) ℤ) [I.IsKInjective]
    (n : ℕ) :
    D.limitUnit.app I ≫ (coefficientConstantTowerProjection l F W n).app
        (DerivedCategory.Q.obj I) ≫
      (coefficientConstantTowerEvaluationFactors l F W n).hom.app I =
      DerivedCategory.Q.map (limit.π I.asFunctor (op n)) := by
  have hp := (coefficientConstantTowerProjection_exists l F W n).choose_spec.1 I
  change (coefficientConstantTowerProjection l F W n).app _ ≫ _ = _ at hp
  rw [hp, ← Category.assoc, D.limitUnit_normalization,
    ← DerivedCategory.Q.map_comp]
  congr 1
  apply (cancel_epi (D.towerLimitComparison.hom.app I)).1
  rw [Iso.hom_inv_id_app_assoc]
  apply HomologicalComplex.hom_ext
  intro p
  exact (D.towerLimitComparison_projection I n p).symm

private theorem roos_projection
    (X : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l F W) ℤ) (n : ℕ) :
    D.roos.hom.app X ≫ (coefficientConstantTowerProjection l F W n).app
        (DerivedCategory.Q.obj X) ≫
      (coefficientConstantTowerEvaluationFactors l F W n).hom.app X =
      DerivedCategory.Q.map (roosEval X n) := by
  have hi (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l F W) ℤ)
      [I.IsKInjective] :
      D.roos.hom.app I ≫ (coefficientConstantTowerProjection l F W n).app
          (DerivedCategory.Q.obj I) ≫
        (coefficientConstantTowerEvaluationFactors l F W n).hom.app I =
        DerivedCategory.Q.map (roosEval I n) := by
    have := inclusion_quasiIso l F W D I
    apply (cancel_epi (DerivedCategory.Q.map (roosι I))).1
    rw [← Category.assoc, ← Category.assoc, D.roos_normalization, Category.assoc,
      limitUnit_projection, ← DerivedCategory.Q.map_comp, roosι_eval]
  obtain ⟨I, hI, q, _, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective X
  have : QuasiIso q := hq
  let V := (evaluation ℕᵒᵖ (scalarReductionSource l F W)).obj (op n)
  apply (cancel_mono (DerivedCategory.Q.map
    ((V.mapHomologicalComplex (.up ℤ)).map q))).1
  have hv := V.mapDerivedCategoryFactors.hom.naturality q
  have hp := (coefficientConstantTowerProjection l F W n).naturality
    (DerivedCategory.Q.map q)
  have hr := D.roos.hom.naturality q
  dsimp only [Functor.comp_map] at hv hr
  simp only [Category.assoc]
  rw [← hv]
  erw [← reassoc_of% hp, ← reassoc_of% hr, hi I]
  rw [← DerivedCategory.Q.map_comp, roosEval_natural, DerivedCategory.Q.map_comp]
  rfl

end Normalization

end WeilConjectures

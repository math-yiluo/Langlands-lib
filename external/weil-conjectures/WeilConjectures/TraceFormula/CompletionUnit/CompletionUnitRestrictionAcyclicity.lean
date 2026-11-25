/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import WeilConjectures.Algebra.Homology.RestrictedTowerResolution.RestrictedTowerResolutionAcyclicity
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Limit acyclicity of restricted K-injective coefficient systems

Source: Stacks 0941, 0D6E, 07A6 and 09T5.
(blueprint: lem-trf-completion-unit-restriction-acyclicity).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.CompletionUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

private abbrev limitComplex :=
  (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
    scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)

-- The coefficient-site identifications below follow the private construction in
-- WeilConjectures.SmoothPurity.SequenceKInjectiveComparison.SequenceKInjectiveComparisonShifts,
-- specialized to the present tower.
private def coefficientCone :
    (Functor.const ℕᵒᵖ).obj (completedIntegralCommRingSheafUnrestricted l E W) ⟶
      coefficientSequenceCommRingSystem l E W :=
  NatTrans.ofOpSequence (fun n ↦ completedIntegralCommRingProjectionUnrestricted l E W n)
    (by
      intro n
      dsimp only [Functor.const_obj_obj, Functor.const_obj_map,
        coefficientSequenceCommRingSystem, Functor.ofOpSequence_obj]
      rw [Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp]
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext V
      apply (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map_injective
      change (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app V =
        (limit.π (integralCoefficientSheafSystem l E W) (op (n + 1))).hom.app V ≫
          (integralCoefficientSheafTransition l E W n).hom.app V
      have h := congrArg (fun k ↦ k.hom.app V)
        (limit.w (integralCoefficientSheafSystem l E W) (homOfLE (Nat.le_succ n)).op)
      simpa only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] using h.symm)

private abbrev strictEquivalence :=
  (SheafOfModules.strictSystemSequenceEquivalence (coefficientSequenceCommRingSystem l E W)).symm

private instance strictEquivalence_additive :
    (strictEquivalence l E W).functor.Additive where
  map_add := by
    intro M N f g
    apply SheafOfModules.strictRingSystem_hom_ext
    intro n
    have h := (SheafOfModules.systemEvaluation
      (coefficientSequenceCommRingSystem l E W) n).map_add
        (f := (strictEquivalence l E W).functor.map f)
        (g := (strictEquivalence l E W).functor.map g)
    refine Eq.trans ?_ h.symm
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext x
    rfl

private theorem restriction_as_strict :
    (strictEquivalence l E W).functor ⋙
      SheafOfModules.RestrictedTowerResolution.restrictionFunctor
        (completedIntegralCommRingSheafUnrestricted l E W)
        (coefficientSequenceCommRingSystem l E W) (coefficientCone l E W) =
      coefficientSequenceRestriction l E W := by
  unfold coefficientSequenceRestriction
  apply (coefficientSequenceRestriction_exists l E W).unique ?_
    (coefficientSequenceRestriction_exists l E W).exists.choose_spec
  refine ⟨?_, ?_, ?_⟩
  · intro M n
    have hφ : SheafOfModules.systemSequenceVerticalRingMap
        (coefficientSequenceCommRingSystem l E W) n =
        eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm := by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext V
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    change (scalarReductionRestriction l E W n).obj
        ((SheafOfModules.pushforward
          (SheafOfModules.systemSequenceVerticalRingMap
            (coefficientSequenceCommRingSystem l E W) n)).obj M) = _
    rw [hφ]
    rfl
  · intro M m n h V
    rfl
  · intro M N f n V
    rfl

/-- Restriction of a K-injective coefficient system is acyclic for inverse limit.
Only its limit-acyclicity is asserted, not its K-injectivity.

Source: Stacks sites-cohomology.tex, lemma-derived-pushforward-composition (0D6E),
lemma-derived-limit-is-ok (0941), and the restriction-acyclicity part of step 1 of
lem-trf-completion-unit-derived-adjunction-comparison.
(blueprint: lem-trf-completion-unit-restriction-acyclicity).

Proof: Identify modules on the coefficient sequence site with strict semilinear
systems using the vertical-slice equivalence. This exact equivalence preserves
K-injectivity. Under it the specified coefficientSequenceRestriction is the
strict-system scalar-restriction tower: its objects, horizontal maps and maps of
systems agree by the three characterizing equations of its unique construction.
Apply lem-coef-restricted-tower-resolution-acyclicity to the identity resolution of
I and the given K-injective tower resolution j. Its first conclusion states exactly
that ordinary inverse limit sends j to a quasi-isomorphism. Transport this conclusion
through the natural isomorphism of restricted towers and their degreewise limits.
Equivalently factor the sequence projection through the constant ring sequence and
apply normalized derived pushforward composition. Exact restriction alone is not
used to claim that it preserves K-injectives. This works for the empty site and zero
complexes and uses neither boundedness nor any flatness of finite quotient rings. -/
theorem restricted_limit_acyclic
    (I : CochainComplex (coefficientSequenceModules l E W) ℤ) [I.IsKInjective]
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [J.IsKInjective]
    (j : (tower l E W).obj I ⟶ J) [QuasiIso j] :
    QuasiIso (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).map j) := by
  let F := (strictEquivalence l E W).functor
  let U := SheafOfModules.RestrictedTowerResolution.restrictionFunctor
    (completedIntegralCommRingSheafUnrestricted l E W)
    (coefficientSequenceCommRingSystem l E W) (coefficientCone l E W)
  have hU : F ⋙ U = coefficientSequenceRestriction l E W := restriction_as_strict l E W
  let I' := (F.mapHomologicalComplex (.up ℤ)).obj I
  have : CochainComplex.IsKInjective I' := inferInstance
  let : (coefficientSequenceRestriction l E W).Additive :=
    coefficientSequenceRestriction_additive l E W
  let e : (U.mapHomologicalComplex (.up ℤ)).obj I' ≅ (tower l E W).obj I :=
    (NatIso.mapHomologicalComplex (F := F ⋙ U)
      (G := coefficientSequenceRestriction l E W) (eqToIso hU) (.up ℤ)).app I
  have := (SheafOfModules.RestrictedTowerResolution.acyclicity
    (completedIntegralCommRingSheafUnrestricted l E W)
    (coefficientSequenceCommRingSystem l E W) (coefficientCone l E W)
    (𝟙 I') (e.hom ≫ j)).1
  have hc : QuasiIso ((limitComplex l E W).map e.hom ≫
      (limitComplex l E W).map j) := by
    simpa only [limitComplex, Functor.map_comp] using this
  exact (quasiIso_iff_comp_left
    ((limitComplex l E W).map e.hom) ((limitComplex l E W).map j)).mp hc

end WeilConjectures.CompletionUnit

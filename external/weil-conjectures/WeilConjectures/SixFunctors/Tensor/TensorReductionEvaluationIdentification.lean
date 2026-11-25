/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite

/-! # Identifying canonical and literal sequence evaluation

Source: Stacks 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The native site size, without an unconstrained maximum universe.
Source: Stacks 0941 (blueprint: lem-coef-tensor-reduction-evaluation-identification). -/
instance (priority := 3000) tensorReductionSiteSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- The locally bijective criterion in the native coefficient universe.
Source: Stacks 0941 (blueprint: lem-coef-tensor-reduction-evaluation-identification). -/
instance (priority := 3000) tensorReductionAbLocallyBijective (W : Scheme.{u}) :
    (Scheme.ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W

/-- Literal evaluation with its coefficient and module universes fixed.
Source: Stacks 0941 (blueprint: lem-coef-tensor-reduction-evaluation-identification). -/
abbrev tensorReductionLiteralEvaluation (W : Scheme.{u}) (n : ℕ) :
    coefficientSequenceModules.{u, u} l E W ⥤ normalizedDVRModules.{u, u} l E W n :=
  SheafOfModules.systemSequenceEvaluation.{u + 1, u, u + 1}
    (coefficientSequenceCommRingSystem.{u, u} l E W) n

/-- The canonical and generic vertical evaluations agree on sections and scalars.
Source: Stacks 0941 (blueprint: lem-coef-tensor-reduction-evaluation-identification). -/
theorem tensorReduction_evaluation_eq (W : Scheme.{u}) (n : ℕ) :
    coefficientSequenceEvaluation.{u, u} l E W n =
      tensorReductionLiteralEvaluation l E W n := by
  have h : (eqToHom (coefficientSequenceEvaluationRing_eq.{u, u} l E W n).symm) =
      SheafOfModules.systemSequenceVerticalRingMap.{u + 1, u, u + 1}
        (coefficientSequenceCommRingSystem.{u, u} l E W) n := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    change (eqToHom (coefficientSequenceEvaluationRing_eq.{u, u} l E W n).symm).hom.app U =
      𝟙 _
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
    rfl
  exact congrArg (fun φ ↦
    (SheafOfModules.pushforward (F := Prod.sectR n W.ProEt) φ :
      coefficientSequenceModules.{u, u} l E W ⥤ normalizedDVRModules.{u, u} l E W n)) h

/-- Literal vertical evaluation preserves zero morphisms componentwise.
Source: Stacks 0941 (blueprint: lem-coef-tensor-reduction-evaluation-identification). -/
instance tensorReductionSystemEvaluation_zero (W : Scheme.{u}) (n : ℕ) :
    (SheafOfModules.systemSequenceEvaluation.{u + 1, u, u + 1}
      (coefficientSequenceCommRingSystem.{u, u} l E W) n).PreservesZeroMorphisms where
  map_zero _ _ := by
    ext U x
    rfl

/-- The evaluation identification, mapped once to complexes.
Source: Stacks 0941 (blueprint: lem-coef-tensor-reduction-evaluation-identification). -/
@[irreducible] def tensorReductionEvaluationComplexIso (W : Scheme.{u}) (n : ℕ) :=
  let e₀ := eqToIso (tensorReduction_evaluation_eq l E W n)
  letI := Functor.preservesZeroMorphisms_of_iso e₀
  NatIso.mapHomologicalComplex e₀ (.up ℤ)

end WeilConjectures

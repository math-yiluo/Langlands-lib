/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.RestrictionOfScalarsExact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.NormalizedDVRTower

/-!
# Normalized DVR towers

Source: Weil conjectures blueprint, `chap-The-six-operations-on-Dbctf`,
`sk-prop-sf-biduality-general`, node `def-coef-normalized-dvr-tower`, order 2131
(blueprint: def-coef-normalized-dvr-tower).

## Main definitions

- `normalizedDVRQuotient`: the actual quotient map of the coefficient system.
- `normalizedDVRRes` and `normalizedDVRResCompleted`: exact derived scalar restriction.
- `NormalizedDVRTower`: finite-level objects and transitions with a coherent derived tower.

Normalization uses the universal property of derived change of rings: composition
with the specified transition is a Hom bijection. Under the tensor-restriction
adjunction this says exactly that the adjoint of that transition is an isomorphism.
It neither chooses an unrelated map nor adds an arbitrary scalar-extension functor.
All module universes are `max u (t+1)`, retaining the small site's independent sizes.
-/

@[expose] public section

set_option autoImplicit false

universe d t u uC vC r s

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures


private theorem normalizedDVRRestrictionExact
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (f : R ⟶ S)
    [HasSheafify J AddCommGrpCat.{s}] [J.WEqualsLocallyBijective AddCommGrpCat.{s}] :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{s} f) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{s} f) := by
  let U := SheafOfModules.toSheaf.{s} R
  have : PreservesFiniteLimits (SheafOfModules.restrictScalars.{s} f ⋙ U) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{s} S))
  have : PreservesFiniteColimits (SheafOfModules.restrictScalars.{s} f ⋙ U) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{s} S))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ U,
    preservesFiniteColimits_of_reflects_of_preserves _ U⟩

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})










/-- Canonical identity restriction; the ordinary identification is the identity on sections.
Source: blueprint order 2131 (blueprint: def-coef-normalized-dvr-tower). -/
noncomputable def normalizedDVRResUnit (n : ℕ) :
    normalizedDVRRes l E X (Nat.le_refl n) ≅ 𝟭 (normalizedDVRDerived l E X n) :=
  letI := HasDerivedCategory.standard (normalizedDVRModules l E X n)
  let e : normalizedDVRModuleRes l E X (Nat.le_refl n) ≅
      𝟭 (normalizedDVRModules l E X n) :=
    eqToIso (congrArg (fun f ↦ SheafOfModules.restrictScalars.{max u (t + 1)} f)
      ((integralCoefficientSheafSystem l E X).map_id (op n)))
  Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _

/-- Canonical composition restriction, induced by identity maps on the underlying modules.
Source: blueprint order 2131 (blueprint: def-coef-normalized-dvr-tower). -/
noncomputable def normalizedDVRResComp {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
    normalizedDVRRes l E X hmn ⋙ normalizedDVRRes l E X hrm ≅
      normalizedDVRRes l E X (le_trans hmn hrm) :=
  letI := HasDerivedCategory.standard (normalizedDVRModules l E X n)
  letI := HasDerivedCategory.standard (normalizedDVRModules l E X m)
  letI := HasDerivedCategory.standard (normalizedDVRModules l E X r)
  let e₀ : normalizedDVRModuleRes l E X hmn ⋙ normalizedDVRModuleRes l E X hrm ≅
      SheafOfModules.restrictScalars.{max u (t + 1)}
        (normalizedDVRQuotient l E X hrm ≫ normalizedDVRQuotient l E X hmn) :=
    normalizedDVRRestrictionCompIso (normalizedDVRQuotient l E X hrm)
      (normalizedDVRQuotient l E X hmn)
  let he : normalizedDVRQuotient l E X hrm ≫ normalizedDVRQuotient l E X hmn =
      normalizedDVRQuotient l E X (le_trans hmn hrm) :=
    ((integralCoefficientSheafSystem l E X).map_comp
      (homOfLE hrm).op (homOfLE hmn).op).symm
  let e : normalizedDVRModuleRes l E X hmn ⋙ normalizedDVRModuleRes l E X hrm ≅
      normalizedDVRModuleRes l E X (le_trans hmn hrm) :=
    e₀ ≪≫ eqToIso (congrArg
      (fun f : integralCoefficientSheaf l E X r ⟶ integralCoefficientSheaf l E X n ↦
        SheafOfModules.restrictScalars.{max u (t + 1)} f) he)
  Functor.mapDerivedCategoryCompIso (normalizedDVRModuleRes l E X hmn)
    (normalizedDVRModuleRes l E X hrm) ≪≫ Functor.mapDerivedCategoryNatIso e

variable (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- The coherent tower category is derived before evaluation, over the completed sheaf.
Source: blueprint order 2131 (blueprint: def-coef-normalized-dvr-tower). -/
@[reducible]
noncomputable def normalizedDVRDerivedTowers :=
  @DerivedCategory (ℕᵒᵖ ⥤ completedIntegralModuleSheaves l E X D hl) _ _
    (HasDerivedCategory.standard _)



/-- The actual derived evaluation functor, without equating site and coefficient universes.
Source: blueprint order 2131 (blueprint: def-coef-normalized-dvr-tower). -/
@[reducible]
noncomputable def normalizedDVRTowerEvaluation (n : ℕ) :
    normalizedDVRDerivedTowers l E X D hl ⥤ completedIntegralDerivedCategory l E X D hl :=
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ completedIntegralModuleSheaves l E X D hl)
  letI := HasDerivedCategory.standard (completedIntegralModuleSheaves l E X D hl)
  ((evaluation ℕᵒᵖ (completedIntegralModuleSheaves l E X D hl)).obj (op n)).mapDerivedCategory

/-- The canonical transition of the evaluated derived tower, for every pair of levels.
Source: blueprint order 2131 (blueprint: def-coef-normalized-dvr-tower). -/
noncomputable def normalizedDVRTowerTransition {m n : ℕ} (h : n ≤ m) :
    normalizedDVRTowerEvaluation l E X D hl m ⟶ normalizedDVRTowerEvaluation l E X D hl n :=
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ completedIntegralModuleSheaves l E X D hl)
  letI := HasDerivedCategory.standard (completedIntegralModuleSheaves l E X D hl)
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ completedIntegralModuleSheaves l E X D hl)
      (ComplexShape.up ℤ)) _ _
    (normalizedDVRTowerEvaluation l E X D hl m)
    (normalizedDVRTowerEvaluation l E X D hl n)
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex
        ((evaluation ℕᵒᵖ (completedIntegralModuleSheaves l E X D hl)).map (homOfLE h).op)
        (ComplexShape.up ℤ)) DerivedCategory.Q)

/-- A normalized DVR tower over the completed integral coefficient sheaf.
Natural number `n` means positive level `n+1`. Scalar restriction and all its unit and
composition identifications are the canonical constructions above. The condition
`normalization` is precisely that the adjoint of `tau h` under derived finite-level
change of rings is an isomorphism: by the adjunction, its precomposition map on every
Hom set is `f ↦ tau h ≫ Res.map f`; Yoneda detects isomorphisms.
Source: blueprint order 2131 (blueprint: def-coef-normalized-dvr-tower).
There is no boundedness, constructibility, stratification, or integral-model condition. -/
structure NormalizedDVRTower (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) where
  /-- The derived object at positive level `n+1`. -/
  M : ∀ n : ℕ, normalizedDVRDerived l E X n
  /-- Transition linear over the source finite coefficient sheaf. -/
  tau : ∀ {m n : ℕ} (h : n ≤ m), M m ⟶ (normalizedDVRRes l E X h).obj (M n)
  /-- The identity transition, under canonical identity restriction. -/
  tau_refl : ∀ n : ℕ,
    tau (Nat.le_refl n) ≫ (normalizedDVRResUnit l E X n).hom.app (M n) = 𝟙 (M n)
  /-- The quotient cocycle under the canonical composition comparison. -/
  tau_comp : ∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
    tau (le_trans hmn hrm) ≫ (normalizedDVRResComp l E X hrm hmn).inv.app (M n) =
      tau hrm ≫ (normalizedDVRRes l E X hrm).map (tau hmn)
  /-- The actual object of the derived category of completed-coefficient strict towers. -/
  tower : normalizedDVRDerivedTowers l E X D hl
  /-- Evaluation identifies the coherent tower with the restricted finite object. -/
  evaluationIso : ∀ n : ℕ,
    (normalizedDVRTowerEvaluation l E X D hl n).obj tower ≅
      (normalizedDVRResCompleted l E X D hl n).obj (M n)
  /-- Evaluated transitions are the specified restricted finite-level transitions. -/
  tower_tau : ∀ {m n : ℕ} (h : n ≤ m),
    (normalizedDVRTowerTransition l E X D hl h).app tower ≫ (evaluationIso n).hom =
      (evaluationIso m).hom ≫ (normalizedDVRResCompleted l E X D hl m).map (tau h) ≫
        (normalizedDVRResCompletedComp l E X D hl h).hom.app (M n)
  /-- Universal derived base change along `B_(m+1) → B_(n+1)`: equivalently, the
  canonical adjoint comparison `M_m ⊗^L_(B_m) B_n → M_n` is invertible. -/
  normalization : ∀ {m n : ℕ} (h : n ≤ m) (P : normalizedDVRDerived l E X n),
    Function.Bijective (fun f : M n ⟶ P ↦ tau h ≫ (normalizedDVRRes l E X h).map f)

end WeilConjectures

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicSmoothDualizing.AdicSmoothDualizingPowerData
import WeilConjectures.SixFunctors.AdicSmoothDualizing.EtalePowerRecursionNormalized

/-! # The normalized finite Tate-power presentation

The existing finite-power data of the smooth-dualizing construction, extracted
without changing any declaration's name, signature or body.
Source: the ordered tensor-power construction in the smooth-dualizing corollary
(blueprint: def-sf-etale-power-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures
namespace AdicSmoothDualizing
open AlgebraicGeometry.Scheme

private theorem etalePowerPresentation_nonempty (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) :
    Nonempty (EtalePowerPresentation P T hT) := by
  let comparison : (d : ℕ) →
      P.diagonalTwistEtale T d ≅ (etaleSingle P T d)⟦2 * (d : ℤ)⟧ :=
    Nat.rec ((shiftFunctorZero _ ℤ).app (P.diagonalTwistEtale T 0)).symm
      (etalePowerPresentationNext P T hT)
  exact ⟨⟨comparison, etalePowerPresentation_normalized P T hT comparison
    HEq.rfl (fun d ↦ rfl)⟩⟩

private theorem etalePowerPresentation_eq (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤)))
    (a b : EtalePowerPresentation P T hT) : a = b := by
  have hc : a.comparison = b.comparison := by
    funext d
    induction d with
    | zero => exact eq_of_heq (a.normalized.1.trans b.normalized.1.symm)
    | succ d ih =>
      obtain ⟨e₁, e₂, e₃, e₄, h₁, h₂, h₃, h₄, he⟩ := a.normalized.2 d
      obtain ⟨f₁, f₂, f₃, f₄, k₁, k₂, k₃, k₄, hf⟩ := b.normalized.2 d
      rw [ih] at h₁
      have h₁' : e₁ = f₁ := eq_of_heq (h₁.trans k₁.symm)
      have h₂' : e₂ = f₂ := eq_of_heq (h₂.trans k₂.symm)
      have h₃' : e₃ = f₃ := eq_of_heq (h₃.trans k₃.symm)
      have h₄' : e₄ = f₄ := eq_of_heq (h₄.trans k₄.symm)
      exact he.trans (by rw [h₁', h₂', h₃', h₄']; exact hf.symm)
  cases a with
  | mk ca ha =>
    cases b with
    | mk cb hb =>
      dsimp only at hc
      cases hc
      rfl

set_option linter.unusedVariables false in
/-- The canonical finite tensor presentation, with its full normalization stored
in its type, is uniquely determined.
Source: the corollary's ordered Tate powers
(blueprint: corollary-dualizing-complex-smooth-scheme--1).
Proof: construct the comparison by induction from the zero-shift unitor using
exactly the four normalized factors. HEq fixes each factor, so induction proves
uniqueness of the comparison. The normalization proof is unique by proof irrelevance. -/
theorem existsUnique_etalePowerPresentation (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) :
    ∃! e : EtalePowerPresentation P T hT, True := by
  obtain ⟨e⟩ := etalePowerPresentation_nonempty P T hT
  exact ⟨e, trivial, fun other _ ↦ etalePowerPresentation_eq P T hT other e⟩

/-- The canonical ordered-tensor family selected by its uniquely determining recursion.
Source: the corollary's finite Tate presentation
(blueprint: corollary-dualizing-complex-smooth-scheme--1). -/
def etalePowerComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) :
    (d : ℕ) → P.diagonalTwistEtale T d ≅ (etaleSingle P T d)⟦2 * (d : ℤ)⟧ :=
  ((existsUnique_etalePowerPresentation P T hT).exists.choose).comparison

attribute [local irreducible] etalePowerComparison

end AdicSmoothDualizing
end WeilConjectures

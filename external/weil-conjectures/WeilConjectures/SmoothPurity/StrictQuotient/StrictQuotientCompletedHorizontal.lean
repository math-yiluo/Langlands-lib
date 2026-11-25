/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.StrictQuotient.StrictQuotientExpressions
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement

/-! # Horizontal maps after completed scalar restriction

Source: Stacks Project, Tag 0941.
(blueprint: lem-pur-strict-quotient-completed-horizontal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory Opposite AlgebraicGeometry
namespace WeilConjectures.StrictQuotient
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem section_map_agrees {C : Type*} [Category* C]
    {R : Cᵒᵖ ⥤ RingCat} (M : PresheafOfModules R)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (fun x : M.obj X ↦ M.map f x) = (fun x : M.obj X ↦ M.presheaf.map f x) := by
  funext x
  exact (PresheafOfModules.presheaf_map_apply_coe M f x).symm

/-- Completed scalar restriction retains exactly the original horizontal section maps.
Source: Stacks 0941; the characterization of coefficientSequenceRestriction.
(blueprint: lem-pur-strict-quotient-completed-horizontal).

Proof: take the horizontal-map clause in the unique characterization of scalar
restriction. Its right side is the original module-presheaf map. The underlying
additive presheaf has the same section map, so this is precisely horizontal. -/
theorem completedHorizontal {W : Scheme.{t}}
    (M : coefficientSequenceModules l E W) (m n : ℕ) (hmn : n ≤ m)
    (U : W.ProEtᵒᵖ) :
    HEq (fun x ↦ ((((coefficientSequenceRestriction l E W).obj M).map
      (homOfLE hmn).op).val.app U) x)
      (fun x : M.val.obj (op (m, U.unop)) ↦
        horizontal l E M hmn U.unop x) := by
  have hU := (coefficientSequenceRestriction_exists l E W).exists.choose_spec
  exact (hU.2.1 M m n hmn U).trans
    (heq_of_eq (section_map_agrees M.val
      (Prod.mkHom (homOfLE hmn) (𝟙 U.unop)).op))

end WeilConjectures.StrictQuotient

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation

/-! # Ordinary inverse-image evaluation preserves the unit

Source: Stacks Project, Tag 03DA; Zheng 4.1.
(blueprint: lem-weil-compact-support-ordinary-pullback-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] constantSheaf presheafToSheaf
attribute [local irreducible] ProEtale.VaryingRing.moduleAdj Functor.leftAdjoint
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The native unit equation in the ordinary coefficient-system coordinates.
Source: Stacks Tag 03DA; Zheng 4.1.
(blueprint: lem-weil-compact-support-ordinary-pullback-unit).
Proof: specialize the defining unit normalization of moduleEvalG to the positive
coefficient tower. The sequence-site evaluation and the normalized finite-coefficient
evaluation have identical module carriers and the specified ring identifications. -/
theorem compactSupportOrdinaryPullbackUnit {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (N : coefficientSequenceModules.{u, u} l E Y) :
    (coefficientSequenceEvaluation l E Y n).map
        ((ProEtale.VaryingRing.moduleAdj (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) f).unit.app N) ≫
      (ProEtale.VaryingRing.moduleEvalP (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f n).hom.app
          ((ProEtale.VaryingRing.pull (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) f).obj N) ≫
      (ProEtale.StrictTower.moduleDirectImage (compactSupportSystemLevel l E n) f).map
        ((ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) f n).hom.app N) =
    (proEtaleConstantRingAdjunction (Padic.coefficientExtensionRing l E (n + 1)) f).unit.app
      ((coefficientSequenceEvaluation l E Y n).obj N) := by
  exact (ProEtale.VaryingRing.moduleEvalG_existsUnique (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) f n).choose_spec.1 N

end WeilConjectures

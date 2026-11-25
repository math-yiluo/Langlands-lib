/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Exceptional.ExceptionalFiniteRealization
/-! # Strict-presentation proper derived comparison
Source: blueprint def-pur-adic-support-realization.
(blueprint: lem-pur-adic-support-proper-derived-adapter).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
attribute [local instance 5000] strictEtaleLevelDerived strictEtaleSystemDerived

namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y)
section CompactSupport
variable (c : Compactification g)
  (S : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c)

set_option linter.unusedVariables false in
/-- The proper derived comparison is also available with the strict coefficient
presentation used by the compact-support level.
Source: blueprint def-pur-adic-support-realization
(blueprint: lem-pur-adic-support-proper-derived-adapter).
Proof: the uniquely normalized derived right comparison of
`def-pur-adic-etale-realization`, specialized to the morphism `c.g`, the
ordinary-image record `S.properImage` and the derived record
`S.properDerived.level n`, has exactly the required type; take it as the
witness, the remaining predicate being `True`. -/
theorem integralExceptionalEtaleProperDerivedRight_exists (n : ℕ) :
    ∃ e : (S.properDerived.level n).direct ⋙
      (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E c.Z n).mapDerivedCategory ⋙
        (Etale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))) c.g).rightDerivedFunctor,
      True := by
  exact ⟨integralExceptionalEtaleDerivedRight l E c.g S.properImage n
    (S.properDerived.level n), trivial⟩

end CompactSupport
end WeilConjectures

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientNative
import WeilConjectures.SixFunctors.Compact.CompactSupportRestrictionIdentity
import WeilConjectures.SixFunctors.Compact.CompactSupportFiniteCoefficientCocycle

/-! # Normalized coefficient squares in canonical quotient types

Source: the compact-support coefficient comparison, blueprint Step 5; Stacks Tag 03DA
(blueprint: lem-coef-compact-support-quotient-comparison-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory Padic.coefficientExtensionIdeal

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The normalized identity square with the actual equal-level quotient cast.
Source: the identity coefficient normalization, Stacks Tag 03DA
(blueprint: lem-coef-compact-support-quotient-comparison-laws).
Proof: specialize the finite identity normalization to the quotient coefficient ring
and its equal-level factor. The canonical wrappers have the original maps as values. -/
theorem compactSupportQuotientNativeComparison_id
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ)
    (H : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1))) :
    (compactSupportQuotientNativeComparison l E c n n le_rfl).hom.app H ≫
        (compactSupportQuotientNativeResId l E Y n).hom.app
          ((sfAmbientCompactSupportCandidate
            (Padic.coefficientExtensionRing l E (n + 1)) c).obj H) =
      (sfAmbientCompactSupportCandidate
        (Padic.coefficientExtensionRing l E (n + 1)) c).map
          ((compactSupportQuotientNativeResId l E X n).hom.app H) := by
  exact compactSupportRestriction_identity c
    (Padic.coefficientExtensionRing l E (n + 1))
    (compactSupportLevelQuotient l E n n le_rfl)
    (compactSupportQuotient_self l E n) H

/-- The normalized composition square with the actual three-level quotient cast.
Source: the compact-support coefficient composition square, Stacks Tag 03DA
(blueprint: lem-coef-compact-support-quotient-comparison-laws).
Proof: specialize the specified coefficient square to the two quotient maps and
their direct composite. The quotient-factor equality is the required cast. -/
theorem compactSupportQuotientNativeComparison_comp
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hl : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (c : Compactification f) (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m)
    (H : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1))) :
    (sfAmbientCompactSupportCandidate
      (Padic.coefficientExtensionRing l E (r + 1)) c).map
        ((compactSupportQuotientNativeResComp l E X r m n hrm hmn).hom.app H) ≫
          (compactSupportQuotientNativeComparison l E c r n (hmn.trans hrm)).hom.app H =
      (compactSupportQuotientNativeComparison l E c r m hrm).hom.app
          ((compactSupportQuotientNativeRestriction l E X m n hmn).obj H) ≫
        (compactSupportQuotientNativeRestriction l E Y r m hrm).map
          ((compactSupportQuotientNativeComparison l E c m n hmn).hom.app H) ≫
        (compactSupportQuotientNativeResComp l E Y r m n hrm hmn).hom.app
          ((sfAmbientCompactSupportCandidate
            (Padic.coefficientExtensionRing l E (n + 1)) c).obj H) := by
  exact compactSupportRestriction_comp_cast l f hl c
    (compactSupportLevelQuotient l E r m hrm)
    (compactSupportLevelQuotient l E m n hmn)
    (compactSupportLevelQuotient l E r n (hmn.trans hrm))
    (compactSupportQuotient_comp l E r m n hrm hmn) H

end WeilConjectures

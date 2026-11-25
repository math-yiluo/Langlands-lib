/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standing.StandingExceptionalComposition
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-!
# Finite-coefficient exceptional composition

Source: blueprint proposition-compatibility-purity-composition--1, proof Step 1 and
proposition-composition-open-restriction-compactifications-f--1 (blueprint:
def-pur-finite-exceptional-composition).

This module owns the finite-coefficient presentation of the canonical compact-support
compositor used by the diagonal pasting construction. It is the adjunction conjugate of
the specified unbounded etale compositor, with no arbitrary natural isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The adjunction conjugate of the specified compact-support compositor.
Source: blueprint proposition-compatibility-purity-composition--1, proof Step 1 and
proposition-composition-open-restriction-compactifications-f--1 (blueprint:
def-pur-finite-exceptional-composition). The underlying lower-shriek map is the canonical
`Etale.unboundedEtaleLowerShriekCompIso`; conjugation uses the two published etale
right-derived upper-shriek adjunctions and their actual composite.
-/
def finiteExceptionalComposition (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCompactification f]
    [HasCompactification g] [HasCompactification (f ≫ g)] [QuasiCompact f]
    [QuasiCompact (f ≫ g)] :
    Etale.rightDerivedUpperShriek Λ (f ≫ g) ≅
      Etale.rightDerivedUpperShriek Λ g ⋙
        Etale.rightDerivedUpperShriek Λ f :=
  conjugateIsoEquiv
    (Etale.rightDerivedUpperShriekAdjunction Λ (f ≫ g))
    ((Etale.rightDerivedUpperShriekAdjunction Λ f).comp
      (Etale.rightDerivedUpperShriekAdjunction Λ g))
    (Etale.unboundedEtaleLowerShriekCompIso Λ f g)

end WeilConjectures.PurityFiniteSetting

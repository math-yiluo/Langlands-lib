/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Exactness of the pullback of étale sheaves

For an arbitrary morphism of schemes `g : Z ⟶ Y` and a Grothendieck abelian coefficient
category `A` (for instance `A = Ab`), the pullback `g^* : Sh(Y_ét, A) ⥤ Sh(Z_ét, A)` is
exact: it preserves finite limits (`AlgebraicGeometry.Etale.preservesFiniteLimits_upperStar`)
and, being left adjoint to `g_*`, all colimits.

## Main results

- `AlgebraicGeometry.Etale.upperStar_exact`: `g^*` preserves finite limits and finite colimits.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The pullback `g^*` of étale sheaves along an arbitrary morphism of schemes `g` is exact:
it is left exact, being the composite of the inclusion into presheaves, the left Kan extension
along the opposite of base change (a filtered colimit, exact in the Grothendieck abelian `A`)
and sheafification, and it is right exact, being left adjoint to `g_*`. For `A = Ab` this is
the exactness of `g⁻¹ : Ab(Y_ét) ⥤ Ab(Z_ét)`. (blueprint: `prop-weil-pbc-inverse-image-exact`) -/
lemma upperStar_exact :
    PreservesFiniteLimits (g)^*[A] ∧ PreservesFiniteColimits (g)^*[A] :=
  ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Etale

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect

/-!
# Derived pullback along an étale morphism commutes with the derived internal hom

For an étale morphism `u : U ⟶ X` and finite coefficients `Λ`, the comparison
`Lu^* RHom(M, N) ⟶ RHom(Lu^* M, Lu^* N)` of the monoidal functor `Lu^*` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_ihomComparison_leftDerivedUpperStar_of_etale`, blueprint
`prose-03-02`). It is conjugate to the projection map of the derived
adjunction `D(u_!) ⊣ Lu^*`, which is an isomorphism by the derived projection formula for étale
morphisms (`AlgebraicGeometry.Etale.isIso_projectionMap_derivedEtaleLowerShriek`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product: otherwise the monoidal structures found by instance
-- search differ from the ones in these definitions, and unifying them is very expensive.
attribute [local instance high] SymmetricCategory.toBraidedCategory

/-- Blueprint `prose-03-02`: Derived pullback, tensor product, and
internal Hom.

For an étale morphism `u : U ⟶ X`, the derived pullback commutes with the derived internal hom:
the comparison `Lu^* RHom(M, N) ⟶ RHom(Lu^* M, Lu^* N)` of the monoidal functor `Lu^*`
(`CategoryTheory.Functor.LaxMonoidal.ihomComparison`) is an isomorphism. The pullback along `u`
is the restriction to the slice site `X_ét/U`, which has an exact left adjoint `u_!`; the
comparison is conjugate to the projection map `u_!(Lu^*M ⊗ᴸ T) ⟶ M ⊗ᴸ u_!T` of the derived
adjunction `D(u_!) ⊣ Lu^*`, an isomorphism by the derived projection formula
(`AlgebraicGeometry.Etale.isIso_projectionMap_derivedEtaleLowerShriek`). -/
theorem isIso_ihomComparison_leftDerivedUpperStar_of_etale {U X : Scheme.{u}}
    (u : U ⟶ X) [Etale u]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    letI := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} Λ) u
    IsIso (Functor.LaxMonoidal.ihomComparison L((u)^*[ModuleCat.{u + 1} Λ]) M) := by
  let := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} Λ) u
  have := isIso_projectionMap_derivedEtaleLowerShriek (A := ModuleCat.{u + 1} Λ) u M
  exact Functor.Monoidal.isIso_ihomComparison_of_isIso_projectionMap
    (derivedEtaleLowerShriekLeftDerivedUpperStarAdjunction u) M

end Etale

end AlgebraicGeometry

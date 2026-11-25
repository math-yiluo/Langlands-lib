/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.KernelAdjunction
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-!
# Towards the projective-line adjunction from the kernel adjunction

First steps of the instantiation of the abstract kernel adjunction
`CategoryTheory.Adjunction.kernelAdjunction` for `q : ℙ¹_S ⟶ S`
(`AlgebraicGeometry.Etale.exists_projectiveLineAdjunction`): the projection map of `Rp_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`) is the projection map
`CategoryTheory.Adjunction.monoidalProjection` of `Lp^* ⊣ Rp_*` for the monoidal structure
`AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal`
(`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap_app_app_eq_monoidalProjection`), so
that it is invertible for proper `p` at finite coefficients
(`AlgebraicGeometry.Etale.isIso_monoidalProjection_of_isProper`); this is the projection formula
hypothesis of `CategoryTheory.Adjunction.traceCounit`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

attribute [local instance] leftDerivedUpperStarMonoidal

section ProjectionMap

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- The projection map of `Rp_*` is the projection map of the adjunction `Lp^* ⊣ Rp_*` for the
monoidal structure of `Lp^*`. -/
lemma rightDerivedLowerStarProjectionMap_app_app_eq_monoidalProjection
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) p).app M).app L =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).monoidalProjection M L :=
  rfl

end ProjectionMap

section ProjectionFormula

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The projection formula for the derived pushforward along a proper morphism, at finite
coefficients, in the form `CategoryTheory.Adjunction.monoidalProjection`. -/
instance isIso_monoidalProjection_of_isProper {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).monoidalProjection M L) := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite Λ p
  rw [← rightDerivedLowerStarProjectionMap_app_app_eq_monoidalProjection]
  infer_instance

end ProjectionFormula

end Etale

end AlgebraicGeometry

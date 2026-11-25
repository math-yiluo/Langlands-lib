/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapUnit
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-!
# The projection map of `Rp_*` at the unit

For `p : X ⟶ Y` and `M` in `D(X_ét)`, the projection map
`Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` (`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`)
is an isomorphism at the unit `L = Λ_Y`
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_tensorUnit`). As it
also commutes with the shifts in `L`
(`AlgebraicGeometry.Etale.commShift_rightDerivedLowerStarProjectionMap_app`), the objects `L` at
which it is an isomorphism are closed under cones.
-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable [Etale.UpperStarPreservesFlat A] {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- The projection map `Rp_*M ⊗ᴸ 𝟙 ⟶ Rp_*(M ⊗ᴸ Lp^*𝟙)` at the unit is an isomorphism. -/
lemma isIso_rightDerivedLowerStarProjectionMap_app_app_tensorUnit
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsIso (((rightDerivedLowerStarProjectionMap A p).app M).app (𝟙_ _)) :=
  letI := leftDerivedUpperStarOplaxMonoidal A p
  have := isIso_leftDerivedUpperStarOplaxMonoidal_η A p
  Adjunction.isIso_rightAdjointProjectionMap_app_app_tensorUnit
    (derivedUpperStarLowerStarAdjunction A p) (leftDerivedUpperStarTensorComparison A p)
    (fun _ _ ↦ rfl) M

end Etale

end AlgebraicGeometry

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.SheafAdjunctionUnitProjection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.SixFunctors.Etale.ScalarExtension.Projection

/-!
# Extension of scalars of étale sheaves is a tensor product

The projection map `K ⊗ S_X ⟶ res (S ⊗_R K)` of
`AlgebraicGeometry.Etale.sheafExtendScalarsProjection` is an isomorphism.

This is the étale counterpart of
`WeilConjectures.SixFunctors.ProEtale.ScalarExtensionProjectionIso`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

-- Use the monoidal structure of the derived tensor product of étale sheaves, see
-- `WeilConjectures.SixFunctors.Etale.ScalarExtension.Monoidal`.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace AlgebraicGeometry.Etale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S] (X : Scheme.{u})

/-- **Extension of scalars is a tensor product**: the projection map `K ⊗ S_X ⟶ res (S ⊗_R K)`
is an isomorphism. -/
instance isIso_sheafExtendScalarsProjection : IsIso (sheafExtendScalarsProjection R S X) := by
  have : X.smallEtaleTopology.PreservesSheafification
      (ModuleCat.restrictScalars.{u + 1} (algebraMap R S)) :=
    Sheaf.preservesSheafification_of_adjunction _
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} (algebraMap R S))
  rw [NatTrans.isIso_iff_isIso_app]
  exact isIso_sheafAdjunction_unitProjection X.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} (algebraMap R S))

end AlgebraicGeometry.Etale

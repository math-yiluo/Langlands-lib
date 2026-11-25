/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.SheafAdjunctionUnitProjection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionProjection

/-!
# Extension of scalars of pro-étale sheaves is a tensor product

The projection map `K ⊗ S_X ⟶ res (S ⊗_R K)` of
`AlgebraicGeometry.ProEtale.sheafExtendScalarsProjection` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S] (X : Scheme.{u})

/-- **Extension of scalars is a tensor product**: the projection map `K ⊗ S_X ⟶ res (S ⊗_R K)`
is an isomorphism. -/
instance isIso_sheafExtendScalarsProjection : IsIso (sheafExtendScalarsProjection R S X) := by
  have : (ProEt.topology X).PreservesSheafification
      (ModuleCat.restrictScalars.{u + 1} (algebraMap R S)) :=
    Sheaf.preservesSheafification_of_adjunction _
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} (algebraMap R S))
  rw [NatTrans.isIso_iff_isIso_app]
  exact isIso_sheafAdjunction_unitProjection (ProEt.topology X)
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} (algebraMap R S))

end AlgebraicGeometry.ProEtale

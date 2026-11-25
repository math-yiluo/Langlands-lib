/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-!
# The derived pullback on module objects commutes with the shifts

Since the pullback `f^*` on module objects is exact, the derived pullback `L((f)^*⟦Λ⟧)` is
isomorphic to the levelwise functor `D((f)^*⟦Λ⟧)`
(`ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`), which commutes with the
shifts and is triangulated. We transport both structures to `L((f)^*⟦Λ⟧)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Shift

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The derived pullback on module objects commutes with the shifts: the structure of the
levelwise functor `D((f)^*⟦Λ⟧)` transported along `L((f)^*⟦Λ⟧) ≅ D((f)^*⟦Λ⟧)`. -/
noncomputable instance : L((f)^*⟦Λ⟧).CommShift ℤ :=
  Functor.CommShift.ofIso (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm ℤ

/-- The identification `L((f)^*⟦Λ⟧) ≅ D((f)^*⟦Λ⟧)` is compatible with the shifts. -/
instance : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm.hom ℤ :=
  Functor.CommShift.ofIso_compatibility _ ℤ

/-- The derived pullback on module objects is triangulated. -/
instance : L((f)^*⟦Λ⟧).IsTriangulated :=
  Functor.isTriangulated_of_iso (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm

end Shift

end AlgebraicGeometry.ProEtale.CondensedRing

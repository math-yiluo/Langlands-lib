/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-!
# Locally free module objects are constructible

A locally free module object over `Λ_X`, for a commutative condensed ring `Λ`, is constructible
with respect to the trivial stratification of `X`
(`ProEtale.IsLocallyFree.isConstructibleModuleObject`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped Obj

namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}}

/-- **A locally free module object over `Λ_X` is constructible**, with respect to the trivial
stratification of `X`: it is locally finitely presented, and so is its pullback along the
identity. -/
theorem IsLocallyFree.isConstructibleModuleObject
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsLocallyFree (condensedRingObj Λ X) M) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M :=
  ⟨Scheme.Stratification.trivial X, fun _ ↦
    (CondensedRing.isLocallyFinitelyPresented_mapMod_iff Λ (𝟙 X) M).2
      (CondensedRing.IsLocallyFinitelyPresented.upperStar Λ (𝟙 X)
        hM.isLocallyFinitelyPresented)⟩

end AlgebraicGeometry.ProEtale

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import WeilConjectures.CategoryTheory.Sites.Point.Flat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.KFlat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!

# Flatness of étale sheaves of `Λ`-modules is checked on stalks

Let `Λ` be a commutative ring. An étale sheaf `F` of `Λ`-modules on a scheme `X` is a flat
object (`CategoryTheory.ObjectProperty.flat`: tensoring with `F` is exact) if and only if
its stalk `F_s` at every geometric point `s` of `X` is a flat object of `ModuleCat Λ`. This is
the site-general criterion `CategoryTheory.GrothendieckTopology.flat_iff_forall_flat_sheafFiber_obj`
applied to the conservative family of geometric points of `X`.

Since the stalk of `g^* F` at `s` is the stalk of `F` at `s ≫ g`
(`AlgebraicGeometry.Etale.upperStarCompUliftSheafFiberIso`), the pullback `g^*` preserves
flat sheaves of `Λ`-modules, which is the instance
`AlgebraicGeometry.Etale.UpperStarPreservesFlat (ModuleCat Λ)`.

The monoidal structure on étale sheaves is the global instance
`CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall`.

## Main results

- `AlgebraicGeometry.Etale.flat_iff_forall_flat_sheafFiber_obj`: an étale sheaf of
  `Λ`-modules is flat if and only if all its stalks at geometric points are flat.
- `AlgebraicGeometry.Etale.upperStarPreservesFlat_moduleCat`: for every morphism of
  schemes `g`, the pullback `g^*` sends flat étale sheaves of `Λ`-modules to flat ones.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

namespace Etale

/-- **Flatness of étale sheaves of `Λ`-modules is checked on stalks.** An étale sheaf of
`Λ`-modules is flat if and only if its stalk at every geometric point is flat. -/
theorem flat_iff_forall_flat_sheafFiber_obj
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ObjectProperty.flat F ↔ ∀ {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      ObjectProperty.flat ((pointSmallEtale s).ulift.{u + 1}.sheafFiber.obj F) := by
  refine ⟨fun hF _ _ _ s ↦ (pointSmallEtale s).ulift.flat_sheafFiber_obj hF, fun hF ↦ ?_⟩
  refine GrothendieckTopology.flat_of_forall_flat_sheafFiber_obj
    (jointlyReflectIsomorphisms_ulift_pointSmallEtale X (ModuleCat.{u + 1} Λ)) F ?_
  rintro ⟨-, ⟨x⟩⟩
  exact hF (X.algClosurePoint x)

/-- **The pullback of étale sheaves of `Λ`-modules preserves flatness.** For every morphism
of schemes `g`, the pullback `g^*` sends flat étale sheaves of `Λ`-modules to flat ones. -/
instance upperStarPreservesFlat_moduleCat : UpperStarPreservesFlat (ModuleCat.{u + 1} Λ) where
  -- the stalk of `g^* F` at `s` is the stalk of `F` at `s ≫ g`
  preservesFlat g := ⟨fun {F} hF ↦ (flat_iff_forall_flat_sheafFiber_obj _).2 fun s ↦
    ObjectProperty.prop_of_iso _ ((upperStarCompUliftSheafFiberIso _ g s).app F).symm
      ((flat_iff_forall_flat_sheafFiber_obj F).1 hF (s ≫ g))⟩

end Etale

end AlgebraicGeometry

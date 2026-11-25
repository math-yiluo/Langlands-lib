/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.WeaklyEtaleProjection

/-!
# The derived pullback along a weakly étale morphism commutes with internal homs

Let `Λ` be a commutative condensed ring and `g : W ⟶ X` a weakly étale morphism of schemes. On
the derived categories of module objects over `Λ`, the comparison
`Lg^* RHom(M, N) ⟶ RHom(Lg^* M, Lg^* N)` of the monoidal functor `Lg^*` is an isomorphism
(`ProEtale.CondensedRing.isIso_ihomComparison_leftDerivedUpperStar_of_weaklyEtale`): the site of
`W` is the localization of the site of `X` at `W` (Bhatt–Scholze, Lemma 6.2.3), and the pullback
`g^*` has an exact left adjoint, the extension by zero `g_!`, satisfying the projection formula.

This file does not import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {W X : Scheme.{u}} (g : W ⟶ X) [WeaklyEtale g]

/-- **The derived pullback along a weakly étale morphism commutes with internal homs**: the
comparison `Lg^* RHom(M, N) ⟶ RHom(Lg^* M, Lg^* N)` of the monoidal functor `Lg^*` is an
isomorphism. -/
theorem isIso_ihomComparison_leftDerivedUpperStar_of_weaklyEtale
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    IsIso (Functor.LaxMonoidal.ihomComparison L((g)^*⟦Λ⟧) M) :=
  Functor.Monoidal.isIso_ihomComparison_of_isIso_projectionMap
    (derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction Λ g) M

end AlgebraicGeometry.ProEtale.CondensedRing

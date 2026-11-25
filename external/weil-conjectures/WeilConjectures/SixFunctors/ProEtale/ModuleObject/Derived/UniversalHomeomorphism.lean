/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomologyCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.TopologicalInvariance

/-!

# Derived pullback along universal homeomorphisms reflects isomorphisms

Let `Λ` be a commutative condensed ring and `r : X ⟶ Y` a universal homeomorphism of schemes. By
topological invariance of the small pro-étale topos, the pullback `r^*` of module objects over
`Λ` is an equivalence of categories
(`ProEtale.CondensedRing.isEquivalence_upperStar_of_isUniversalHomeomorphism`). Since the derived
pullback `L(r^*)` commutes with the homology functors and a morphism of the derived category is an
isomorphism as soon as it induces isomorphisms on all homology objects, the derived pullback
`L(r^*)` reflects isomorphisms
(`ProEtale.CondensedRing.isIso_of_isIso_leftDerivedUpperStar_map`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The derived pullback `L(r^*)` of module objects over `Λ` along a universal homeomorphism `r`
reflects isomorphisms: the homology of `L(r^*)(g)` is `r^*` applied to the homology of `g`, and
`r^*` is an equivalence. -/
theorem isIso_of_isIso_leftDerivedUpperStar_map {X Y : Scheme.{u}} (r : X ⟶ Y)
    [IsUniversalHomeomorphism r]
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))}
    (g : K ⟶ L) (h : IsIso (L((r)^*⟦Λ⟧).map g)) : IsIso g := by
  have := isEquivalence_upperStar_of_isUniversalHomeomorphism Λ r
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso ((r)^*⟦Λ⟧.map ((DerivedCategory.homologyFunctor _ n).map g)) :=
    (NatIso.isIso_map_iff (leftDerivedUpperStarHomologyIso Λ r n) g).2 (by
      rw [Functor.comp_map]
      infer_instance)
  exact isIso_of_reflects_iso _ (r)^*⟦Λ⟧

/-- The derived pullback along a universal homeomorphism reflects isomorphisms. -/
instance reflectsIsomorphisms_leftDerivedUpperStar {X Y : Scheme.{u}} (r : X ⟶ Y)
    [IsUniversalHomeomorphism r] : L((r)^*⟦Λ⟧).ReflectsIsomorphisms where
  reflects g h := isIso_of_isIso_leftDerivedUpperStar_map Λ r g h

end AlgebraicGeometry.ProEtale.CondensedRing

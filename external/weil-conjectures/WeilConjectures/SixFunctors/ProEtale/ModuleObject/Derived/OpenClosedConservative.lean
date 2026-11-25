/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed

/-!

# Open–closed detection and vanishing on the ambient derived categories of module objects

Let `Λ` be a commutative condensed ring, `j : U ⟶ X` a quasi-compact open immersion and
`i : Z ⟶ X` a closed immersion onto the complement of its range. This file lifts the
sheaf-level statements of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed` to the
derived categories `D(Mod_{Λ_X})`:

* the derived restrictions `Lj^*` and `Li^*` jointly reflect isomorphisms
  (`ProEtale.CondensedRing.jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl`);
* `Lg^* (j_! K)` vanishes when the range of `g` misses the range of the open immersion `j`
  (`ProEtale.CondensedRing.isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint`).

Since the pullbacks and the extension by zero are exact on module objects, both follow on
homology objects from the sheaf-level statements, through the isomorphisms
`L(g^*) ≅ D(g^*)` (`ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`).

The versions on bounded constructible complexes are in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed`. This file does not import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, so that the
latter can use these statements.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Derived

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [QuasiCompact j]

/-- The derived restrictions `Lj^*` and `Li^*` to a quasi-compact open and its closed
complement jointly reflect isomorphisms of `D(Mod_{Λ_X})`. -/
theorem jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    JointlyReflectIsomorphisms (pairFunctor L((j)^*⟦Λ⟧) L((i)^*⟦Λ⟧)) :=
  (Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory _ _
    (jointlyReflectIsomorphisms_upperStar_of_isCompl Λ i j hij)).pairFunctor_of_iso
    (leftDerivedUpperStarIsoMapDerivedCategory Λ j).symm
    (leftDerivedUpperStarIsoMapDerivedCategory Λ i).symm

end Derived

/-- `Lg^* (j_! K)` vanishes in `D(Mod_{Λ_W})` when the range of `g : W ⟶ X` misses the range of
the open immersion `j : U ⟶ X`. -/
lemma isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint {U W X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (g : W ⟶ X)
    (hjg : Disjoint (Set.range j.base) (Set.range g.base))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) :
    IsZero (L((g)^*⟦Λ⟧).obj (D((j)_!open⟦Λ⟧).obj K)) :=
  (Functor.isZero_mapDerivedCategory_obj _ _ fun n ↦
    (isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint Λ j g hjg
      ((DerivedCategory.homologyFunctor _ n).obj K)).of_iso
      ((g)^*⟦Λ⟧.mapIso (((j)_!open⟦Λ⟧.mapDerivedCategoryHomologyFunctorIso n).symm.app
        K))).of_iso ((leftDerivedUpperStarIsoMapDerivedCategory Λ g).app _)

end AlgebraicGeometry.ProEtale.CondensedRing

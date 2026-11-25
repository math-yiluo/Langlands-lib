/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.RecollementTriangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleClosedPushforward
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedConservative
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift

/-!
# The open–closed triangle on the ambient derived categories of module objects

Let `Λ` be a commutative condensed ring, `j : U ⟶ X` a quasi-compact open immersion and
`i : Z ⟶ X` a closed immersion onto its complement. On the ambient derived category
`D(Mod_{Λ_X})`, for every complex `K`, the counit `j_! Lj^* K ⟶ K` of `Dj_! ⊣ Lj^*` and the unit
`K ⟶ Ri_* Li^* K` of `Li^* ⊣ Ri_*` extend to a distinguished triangle
(`ProEtale.CondensedRing.exists_distTriang_openClosed_derived`).

This follows from the joint conservativity of `Lj^*` and `Li^*`
(`ProEtale.CondensedRing.jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl`), the full
faithfulness of `Dj_!` and of `Ri_*`, and the vanishing of `Lj^* Ri_*` and of `Li^* Dj_!`. This
file only depends on the derived six operations on module objects, not on the localizing
subcategories, so that it can be used below them in the import hierarchy.
-/
@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X U Z : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (i : Z ⟶ X)
  [IsClosedImmersion i] (hij : IsCompl (Set.range i.base) (Set.range j.base))

include hij in
/-- **The open–closed triangle** `Dj_! Lj^* K ⟶ K ⟶ Ri_* Li^* K ⟶` on the ambient derived
category of module objects, for a quasi-compact open immersion `j` and a closed immersion `i`
onto its complement. -/
theorem exists_distTriang_openClosed_derived
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    ∃ δ, Triangle.mk
      ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' Λ j).counit.app K)
      ((derivedUpperStarLowerStarAdjunction Λ i).unit.app K) δ ∈ distTriang _ := by
  have hN : IsZero ((L((j)^*⟦Λ⟧)).obj ((R((i)_*⟦Λ⟧)).obj ((L((i)^*⟦Λ⟧)).obj K))) :=
    isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint Λ j i
      hij.symm.disjoint _
  have hA : IsZero ((L((i)^*⟦Λ⟧)).obj (D((j)_!open⟦Λ⟧).obj ((L((j)^*⟦Λ⟧)).obj K))) :=
    isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint Λ j i
      hij.symm.disjoint _
  have hfg : (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' Λ j).counit.app K ≫
      (derivedUpperStarLowerStarAdjunction Λ i).unit.app K = 0 :=
    ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' Λ j).homEquiv _ _).injective
      (hN.eq_of_tgt _ _)
  have h₁ : IsIso ((L((j)^*⟦Λ⟧)).map
      ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' Λ j).counit.app K)) :=
    IsIso.of_isIso_fac_left (hh := IsIso.id _)
      ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' Λ
        j).right_triangle_components K)
  have h₂ : IsIso ((L((i)^*⟦Λ⟧)).map ((derivedUpperStarLowerStarAdjunction Λ i).unit.app K)) :=
    IsIso.of_isIso_fac_right (hh := IsIso.id _)
      ((derivedUpperStarLowerStarAdjunction Λ i).left_triangle_components K)
  exact exists_distTriang_of_jointlyReflectIsomorphisms
    (jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl Λ i j hij) _ _ hfg h₁ hN hA h₂

end AlgebraicGeometry.ProEtale.CondensedRing

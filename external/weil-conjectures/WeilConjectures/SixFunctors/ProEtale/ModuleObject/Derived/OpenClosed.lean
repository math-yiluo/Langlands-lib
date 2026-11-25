/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedConservative
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed

/-!

# Open–closed detection and vanishing on bounded constructible complexes

Let `Λ` be a commutative condensed ring, `j : U ⟶ X` a quasi-compact open immersion and
`i : Z ⟶ X` a closed immersion onto the complement of its range. This file lifts the statements on
the ambient derived categories `D(Mod_{Λ_X})` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedConservative` to the bounded
constructible derived categories `Dᵇc(X)⟦Λ⟧`:

* the restrictions `Lj^*` and `Li^*` jointly reflect isomorphisms
  (`ProEtale.CondensedRing.isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl`, from
  `ProEtale.CondensedRing.jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl`);
* `Lg^* (j_! K)` vanishes when the range of `g` misses the range of the open immersion `j`
  (`ProEtale.CondensedRing.isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek`, from
  `ProEtale.CondensedRing.isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint`).
* morphisms from a shifted extension by zero `(j_! N)[n]` to `Ri_* M` vanish when the ranges of
  `j` and `i` are disjoint
  (`ProEtale.CondensedRing.eq_zero_of_shift_openImmersionLowerShriek_to_lowerStar`).

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

include ℓ k

/-- **Open–closed detection on bounded constructible complexes**: for a quasi-compact open
immersion `j : U ⟶ X` and a closed immersion `i : Z ⟶ X` onto its complement, a morphism `φ`
of `Dᵇc(X)⟦Λ⟧` such that `Lj^* φ` and `Li^* φ` are isomorphisms is an isomorphism. -/
theorem isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl
    {Z U X : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (j : U ⟶ X) [QuasiCompact j.left]
    (hij : IsCompl (Set.range i.left.base) (Set.range j.left.base))
    {K K' : Dᵇc(X.left)⟦Λ⟧} (φ : K ⟶ K')
    (hj : IsIso ((boundedConstructibleUpperStar Λ ℓ j).map φ))
    (hi : IsIso ((boundedConstructibleUpperStar Λ ℓ i).map φ)) : IsIso φ := by
  have hι : IsIso ((boundedConstructible (condensedRingObj Λ X.left)).ι.map φ) :=
    (jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl Λ i.left j.left
      hij).isIso_of_pairFunctor _
      ((NatIso.isIso_map_iff (boundedConstructibleUpperStarCompatibility Λ ℓ j) φ).1
        (by rw [Functor.comp_map]; infer_instance))
      ((NatIso.isIso_map_iff (boundedConstructibleUpperStarCompatibility Λ ℓ i) φ).1
        (by rw [Functor.comp_map]; infer_instance))
  exact isIso_of_reflects_iso φ (boundedConstructible (condensedRingObj Λ X.left)).ι

/-- **`Lg^* (j_! K)` vanishes on bounded constructible complexes** when the range of `g` misses
the range of the open immersion `j`. -/
lemma isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek
    {U W X : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left] (g : W ⟶ X)
    (hjg : Disjoint (Set.range j.left.base) (Set.range g.left.base)) (K : Dᵇc(U.left)⟦Λ⟧) :
    IsZero ((boundedConstructibleUpperStar Λ ℓ g).obj
      ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj K)) := by
  have h : IsZero ((boundedConstructible (condensedRingObj Λ W.left)).ι.obj
      ((boundedConstructibleUpperStar Λ ℓ g).obj
        ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj K))) :=
    (isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint Λ j.left g.left hjg
      K.obj).of_iso ((boundedConstructibleUpperStarCompatibility Λ ℓ g).app _ ≪≫
        L((g.left)^*⟦Λ⟧).mapIso
          ((boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ j).app K))
  rw [IsZero.iff_id_eq_zero] at h ⊢
  exact (boundedConstructible (condensedRingObj Λ W.left)).ι.map_injective (by simpa using h)

/-- Maps from a shifted extension by zero `(j_! N)[n]` to a pushforward `Ri_* M` vanish when the
range of the closed immersion `i` misses the range of the open immersion `j`: by the adjunction
`Li^* ⊣ Ri_*` they correspond to maps out of `(Li^* j_! N)[n] = 0`. -/
lemma eq_zero_of_shift_openImmersionLowerShriek_to_lowerStar {U Z X : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left] (i : Z ⟶ X)
    (hji : Disjoint (Set.range j.left.base) (Set.range i.left.base)) (N : Dᵇc(U.left)⟦Λ⟧)
    (n : ℤ) (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj Λ Z.left)))
    (φ : (shiftFunctor _ n).obj ((boundedConstructible (condensedRingObj Λ X.left)).ι.obj
      ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj N)) ⟶
        R((i.left)_*⟦Λ⟧).obj M) : φ = 0 := by
  have h₀ : IsZero (L((i.left)^*⟦Λ⟧).obj ((boundedConstructible
      (condensedRingObj Λ X.left)).ι.obj ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ
        j).obj N))) :=
    (isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint Λ j.left i.left hji
      N.obj).of_iso (L((i.left)^*⟦Λ⟧).mapIso
        ((boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ j).app N))
  have h₁ : IsZero (L((i.left)^*⟦Λ⟧).obj ((shiftFunctor _ n).obj ((boundedConstructible
      (condensedRingObj Λ X.left)).ι.obj ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ
        j).obj N)))) :=
    ((shiftFunctor _ n).map_isZero h₀).of_iso ((L((i.left)^*⟦Λ⟧).commShiftIso n).app _)
  rw [← ((derivedUpperStarLowerStarAdjunction Λ i.left).homEquiv _ _).apply_symm_apply φ,
    h₁.eq_of_src (((derivedUpperStarLowerStarAdjunction Λ i.left).homEquiv _ _).symm φ) 0,
    Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]


end BoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing

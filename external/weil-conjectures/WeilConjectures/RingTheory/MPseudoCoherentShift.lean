/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.MPseudoCoherent

/-!
# Shifting finite-free approximations

Source: Stacks Project, Tag 064R, rotation argument for assertions (2) and (3).
(blueprint: lem-pc-ring-m-pseudo-coherent-shift).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace DerivedCategory

private theorem pseudoCoherent_of_iso
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (m : ℤ) {C D : DerivedCategory (ModuleCat.{v} R)} (e : C ≅ D)
    (h : IsMPseudoCoherent m C) : IsMPseudoCoherent m D := by
  obtain ⟨E, a, b, hGE, hLE, hfree, f, hiso, hepi⟩ := h
  refine ⟨E, a, b, hGE, hLE, hfree, f ≫ e.hom, ?_, ?_⟩
  · intro i hi
    have := hiso i hi
    simp only [Functor.map_comp]
    infer_instance
  · have := hepi
    simp only [Functor.map_comp]
    infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem pseudoCoherent_shift
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (m n : ℤ) (C : DerivedCategory (ModuleCat.{v} R))
    (h : IsMPseudoCoherent m C) : IsMPseudoCoherent (m - n) (C⟦n⟧) := by
  obtain ⟨E, a, b, hGE, hLE, hfree, f, hiso, hepi⟩ := h
  have := hGE
  have := hLE
  refine ⟨E⟦n⟧, a - n, b - n,
    CochainComplex.isStrictlyGE_shift E a n (a - n) (by omega),
    CochainComplex.isStrictlyLE_shift E b n (b - n) (by omega), ?_,
    (Q.commShiftIso n).hom.app E ≫ f⟦n⟧', ?_, ?_⟩
  · intro i
    have := (hfree (n + i)).1
    have := (hfree (n + i)).2
    let e := CategoryTheory.Iso.toLinearEquiv (E.shiftFunctorObjXIso n i (n + i) (by omega)).symm
    exact ⟨Module.Free.of_equiv e, Module.Finite.equiv e⟩
  · intro i hi
    have : IsIso ((homologyFunctor (ModuleCat.{v} R) i).map (f⟦n⟧')) :=
      (NatIso.isIso_map_iff
        ((homologyFunctor (ModuleCat.{v} R) 0).shiftIso n i (n + i) rfl) f).mpr
        (by simpa only [shift_homologyFunctor] using hiso (n + i) (by omega))
    simp only [Functor.map_comp]
    infer_instance
  · have : Epi ((homologyFunctor (ModuleCat.{v} R) (n + (m - n))).map f) := by
      have hidx : n + (m - n) = m := by omega
      rw [hidx]
      exact hepi
    have : Epi ((homologyFunctor (ModuleCat.{v} R) (m - n)).map (f⟦n⟧')) := by
      change Epi ((shiftFunctor (DerivedCategory (ModuleCat.{v} R)) n ⋙
        (homologyFunctor (ModuleCat.{v} R) 0).shift (m - n)).map f)
      rw [← NatIso.naturality_2
        ((homologyFunctor (ModuleCat.{v} R) 0).shiftIso n (m - n)
          (n + (m - n)) rfl) f]
      simp only [shift_homologyFunctor]
      infer_instance
    simp only [Functor.map_comp]
    infer_instance

/-- Shift the witness complex and its map. A shift preserves boundedness, freeness,
 and finiteness, and `Hⁱ(C[1]) = Hⁱ⁺¹(C)` gives precisely the new approximation degree.
Source: Stacks Project, Tag 064R, proof of assertions (2) and (3).
(blueprint: lem-pc-ring-m-pseudo-coherent-shift).

Proof: for the forward direction choose a finite-free witness for `C[1]` through
 degree `m`, shift it by `-1`, and compose the shifted map with the canonical
 isomorphism `C[1][-1] ≅ C`. The new bounds are the old bounds plus one. The
 cohomology shift isomorphisms identify its map in degree `i` with the old map
 in degree `i - 1`, so it is an isomorphism for `i > m + 1` and epi at `m + 1`.
 For the reverse direction shift a witness for `C` by `1`; the bounds decrease
 by one. Identify the homology map in degree `i` with the old one in degree
 `i + 1`. These identifications give the required isomorphisms and epimorphism.
 The termwise shift isomorphisms preserve finite free modules in both directions. -/
theorem isMPseudoCoherent_shift_one_iff
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (m : ℤ) (C : DerivedCategory (ModuleCat.{v} R)) :
    IsMPseudoCoherent m (C⟦(1 : ℤ)⟧) ↔ IsMPseudoCoherent (m + 1) C := by
  constructor
  · intro h
    have h' := pseudoCoherent_shift m (-1) (C⟦(1 : ℤ)⟧) h
    have h'' := pseudoCoherent_of_iso (m - (-1))
      ((shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{v} R)) 1 (-1) (by omega)).app C)
      h'
    simpa using h''
  · intro h
    have h' := pseudoCoherent_shift (m + 1) 1 C h
    simpa using h'

end DerivedCategory

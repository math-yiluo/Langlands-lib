/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Depth over a quotient ring

Source: Stacks Project, Algebra, Lemma Tag 0AUK (lemma-depth-goes-down-finite),
applied to the finite ring map `R → R ⧸ I`
(blueprint: lem-weil-pbc-depth-over-quotient-ring).
-/

@[expose] public section

universe u v

namespace IsLocalRing

/-- Surjective scalar change preserves depth: the maximal ideals generate the same
submodule and corresponding regular sequences have equal lengths. This is the direct
quotient argument from Stacks Tags 00LF and 00LI, generalised to a surjective algebra map. -/
private theorem depth_eq_of_surjective
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite R M] [Module.Finite S M]
    (hf : Function.Surjective (algebraMap R S)) :
    depth (R := S) M = depth (R := R) M := by
  have : IsLocalHom (algebraMap R S) := IsLocalHom.of_surjective _ hf
  have hmax := map_maximalIdeal_of_surjective (algebraMap R S) hf
  have hsmul : (maximalIdeal S • (⊤ : Submodule S M) = ⊤) ↔
      (maximalIdeal R • (⊤ : Submodule R M) = ⊤) := by
    rw [← Submodule.restrictScalars_inj R, Submodule.restrictScalars_top,
      ← hmax, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
  have hreg (rs : List R) : RingTheory.Sequence.IsRegular M rs ↔
      RingTheory.Sequence.IsRegular M (rs.map (algebraMap R S)) :=
    (AddEquiv.refl M).isRegular_congr <| List.forall₂_map_right_iff.mpr <|
      List.forall₂_same.mpr fun r _ x => (algebraMap_smul S r x).symm
  have hsets :
      {n : ℕ∞ | ∃ rs : List S, RingTheory.Sequence.IsRegular M rs ∧
        (∀ x ∈ rs, x ∈ maximalIdeal S) ∧ n = (rs.length : ℕ∞)} =
      {n : ℕ∞ | ∃ rs : List R, RingTheory.Sequence.IsRegular M rs ∧
        (∀ x ∈ rs, x ∈ maximalIdeal R) ∧ n = (rs.length : ℕ∞)} := by
    ext n
    constructor
    · rintro ⟨ss, hss, hm, hn⟩
      obtain ⟨rs, rfl⟩ := hf.list_map ss
      refine ⟨rs, (hreg rs).mpr hss, ?_, ?_⟩
      · intro r hr
        have := hm _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
        change r ∈ Ideal.comap (algebraMap R S) (maximalIdeal S) at this
        rwa [maximalIdeal_comap] at this
      · simpa only [List.length_map] using hn
    · rintro ⟨rs, hrs, hm, hn⟩
      refine ⟨rs.map (algebraMap R S), (hreg rs).mp hrs, ?_, ?_⟩
      · intro s hs
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
        rw [← hmax]
        exact Ideal.mem_map_of_mem (algebraMap R S) (hm r hr)
      · simpa only [List.length_map] using hn
  unfold depth Ideal.depth
  rw [hsets]
  split_ifs with hS hR hR
  · rfl
  · exact False.elim (hR (hsmul.mp hS))
  · exact False.elim (hS (hsmul.mpr hR))
  · rfl

/-- Let `R` be a Noetherian local ring, `I ≤ maximalIdeal R` an ideal and `M` a finite
`R`-module with `I M = 0` (`Module.IsTorsionBySet R M I`). Then `R ⧸ I` is local (as
`I ≠ ⊤`), `M` is a finite `R ⧸ I`-module by Mathlib's `Module.IsTorsionBySet.module`,
`(r mod I) • m = r • m`, and the depth of `M` over `R ⧸ I` equals its depth over `R`;
in particular (for `M = R ⧸ I`) the depth of the local ring `R ⧸ I` equals the depth of
`R ⧸ I` as an `R`-module (blueprint: lem-weil-pbc-depth-over-quotient-ring).

Proof (Stacks Tag 0AUK for the finite ring map `R → R ⧸ I`, whose only maximal ideal is
`m ⧸ I`): the maximal ideal of `R ⧸ I` is the image of `m`, so `(m ⧸ I) M = m M` and the
clause `I M = M` of the depth definition holds over one ring iff over the other. For
`f₁, …, f_r ∈ m` with images `f̄ᵢ ∈ m ⧸ I`, multiplication by `fᵢ` and by `f̄ᵢ` on each
`M ⧸ (f₁, …, f_{i-1}) M` is the same map, so `f₁, …, f_r` is `M`-regular over `R` iff
`f̄₁, …, f̄_r` is `M`-regular over `R ⧸ I`; every sequence in `m ⧸ I` lifts to `m`. Hence
the sets of lengths of regular sequences agree and the two depths are equal. -/
theorem depth_over_quotient_ring
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≤ maximalIdeal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hIM : Module.IsTorsionBySet R M (I : Set R)) :
    letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI)
    letI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    letI : Module (R ⧸ I) M := hIM.module
    haveI : Module.Finite (R ⧸ I) M := Module.Finite.of_restrictScalars_finite R (R ⧸ I) M
    depth (R := R ⧸ I) M = depth (R := R) M ∧
      depth (R := R ⧸ I) (R ⧸ I) = depth (R := R) (R ⧸ I) := by
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI)
  let : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : Module (R ⧸ I) M := hIM.module
  have : Module.Finite (R ⧸ I) M :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ I) M
  exact ⟨depth_eq_of_surjective Ideal.Quotient.mk_surjective,
    depth_eq_of_surjective Ideal.Quotient.mk_surjective⟩

end IsLocalRing

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SingularIdeal
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.AnnihilatorElementFlatBaseChange
import Mathlib.RingTheory.Smooth.Flat

/-!
# Relative singular-ideal containment from an annihilator bound

Source: Stacks Project, Tag 07CT, second paragraph.
(blueprint: lem-weil-pbc-singular-ideals-relative-bound).
-/

@[expose] public section

universe u v w
namespace Algebra

/-- The base annihilator equality persists under a flat algebra map, by Tag 07T8. -/
private theorem annihilator_eq_of_flat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (π : R) (hR : ∀ r : R, r * π = 0 ↔ r * π ^ 2 = 0) :
    ∀ x : S, (algebraMap R S π) ^ 2 * x = 0 → algebraMap R S π * x = 0 := by
  have hAnn : Module.annihilator R (Ideal.span ({π} : Set R)) =
      Module.annihilator R (Ideal.span ({π ^ 2} : Set R)) := by
    ext r
    change r ∈ (Submodule.span R ({π} : Set R)).annihilator ↔
      r ∈ (Submodule.span R ({π ^ 2} : Set R)).annihilator
    simp only [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
    exact hR r
  have heq : Module.annihilator S (Ideal.span ({algebraMap R S π} : Set S)) =
      Module.annihilator S (Ideal.span ({(algebraMap R S π) ^ 2} : Set S)) := by
    rw [RingHom.annihilator_element_flat_base_change (algebraMap R S)
        (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat R S)),
      ← map_pow, RingHom.annihilator_element_flat_base_change
        (algebraMap R S)
        (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat R S)), hAnn]
  intro x hx
  have hm : x ∈ Module.annihilator S
      (Ideal.span ({(algebraMap R S π) ^ 2} : Set S)) := by
    change x ∈ (Submodule.span S ({(algebraMap R S π) ^ 2} : Set S)).annihilator
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
    simpa only [mul_comm] using hx
  rw [← heq] at hm
  change x ∈ (Submodule.span S ({algebraMap R S π} : Set S)).annihilator at hm
  rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul] at hm
  simpa only [mul_comm] using hm

/-- Finitely many generators permit one common power to clear all denominators. -/
private theorem exists_uniform_power
    {D : Type v} [CommRing D] (I : Ideal D) (hI : I.FG) (g p : D)
    (h : ∀ x ∈ I, ∃ n : ℕ, g ^ n * (p * x) = 0) :
    ∃ n : ℕ, ∀ x ∈ I, g ^ n * (p * x) = 0 := by
  classical
  obtain ⟨s, hs⟩ := hI
  have hf : ∀ t : Finset D, (∀ x ∈ t, ∃ n : ℕ, g ^ n * (p * x) = 0) →
      ∃ n : ℕ, ∀ x ∈ t, g ^ n * (p * x) = 0 := by
    intro t
    induction t using Finset.induction with
    | empty => simp
    | insert a t ha ih =>
      intro ht
      obtain ⟨n, hn⟩ := ht a (Finset.mem_insert_self _ _)
      obtain ⟨m, hm⟩ := ih (fun x hx ↦ ht x (Finset.mem_insert_of_mem hx))
      refine ⟨n + m, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [pow_add, mul_comm (g ^ n), mul_assoc, hn, mul_zero]
      · rw [pow_add, mul_assoc, hm x hx, mul_zero]
  obtain ⟨n, hn⟩ := hf s (fun x hx ↦ h x (hs ▸ Submodule.subset_span hx))
  refine ⟨n, ?_⟩
  have hle : I ≤ LinearMap.ker (LinearMap.mulLeft D (g ^ n * p)) := by
    rw [← hs]
    apply Submodule.span_le.mpr
    intro x hx
    change (g ^ n * p) * x = 0
    simpa only [mul_assoc] using hn x hx
  intro x hx
  simpa only [LinearMap.mem_ker, LinearMap.mulLeft_apply, mul_assoc] using hle hx

/-- Relative singular-ideal containment from an annihilator bound.

Source: Stacks Project, Tag 07CT, second paragraph. For a smooth localization element
`g`, flat base change identifies the annihilators of `π` and `π²` in `D_g`.
Thus each element of `Ann_D(π²)` is killed by `π` after localization. Clear the
localization denominators, and use finite generation of that ideal over the Noetherian
ring `D` to obtain one power of `g` which annihilates all these products. This power
belongs to the set in the assumed bound. Hence the image of every smooth generator
belongs to the radical relative singular ideal. Span and radical monotonicity give
containment for the entire singular ideal.
(blueprint: lem-weil-pbc-singular-ideals-relative-bound)
-/
theorem singularIdeal_map_le_relative_of_annihilator_bound
    (R : Type u) (D : Type v) (B : Type w)
    [CommRing R] [CommRing D] [CommRing B]
    [Algebra R D] [Algebra R B] [IsNoetherianRing R] [FinitePresentation R D]
    (dB : D →ₐ[R] B)
    (hfp : @FinitePresentation D B _ _ dB.toRingHom.toAlgebra)
    (π : R) (hR : ∀ r : R, r * π = 0 ↔ r * π ^ 2 = 0)
    (hbound : Ideal.span (dB ''
      {r : D | ∀ x : D, (algebraMap R D π) ^ 2 * x = 0 →
        r * algebraMap R D π * x = 0}) ≤
      @singularIdeal D B _ _ dB.toRingHom.toAlgebra) :
    Ideal.map dB.toRingHom (singularIdeal R D) ≤
      @singularIdeal D B _ _ dB.toRingHom.toAlgebra := by
  obtain ⟨_⟩ := hfp
  have : IsNoetherianRing D := FiniteType.isNoetherianRing R D
  let J := @singularIdeal D B _ _ dB.toRingHom.toAlgebra
  have hJ : J.IsRadical := @singularIdeal_isRadical D B _ _ dB.toRingHom.toAlgebra
  rw [Ideal.map_le_iff_le_comap]
  change (Ideal.span (smoothElements R D)).radical ≤ Ideal.comap dB.toRingHom J
  apply (hJ.comap dB.toRingHom).radical_le_iff.mpr
  apply Ideal.span_le.mpr
  intro g hg
  have : Smooth R (Localization.Away g) := hg
  let p := algebraMap R D π
  let I : Ideal D := Module.annihilator D (Ideal.span ({p ^ 2} : Set D))
  have hp : ∀ x ∈ I, ∃ n : ℕ, g ^ n * (p * x) = 0 := by
    intro x hx
    have hx' : p ^ 2 * x = 0 := by
      change x ∈ (Submodule.span D ({p ^ 2} : Set D)).annihilator at hx
      rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul] at hx
      simpa only [mul_comm] using hx
    have hz : algebraMap D (Localization.Away g) (p * x) = 0 := by
      have h := annihilator_eq_of_flat π hR (algebraMap D (Localization.Away g) x)
      have hpx : algebraMap D (Localization.Away g) p =
          algebraMap R (Localization.Away g) π := by
        exact (IsScalarTower.algebraMap_apply R D (Localization.Away g) π).symm
      rw [map_mul, hpx]
      apply h
      rw [← hpx, ← map_pow, ← map_mul, hx', map_zero]
    obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers g) (Localization.Away g) _).mp hz
    exact ⟨n, hn⟩
  obtain ⟨n, hn⟩ := exists_uniform_power I I.fg_of_isNoetherianRing g p hp
  have hgn : g ^ n ∈ {r : D | ∀ x : D, p ^ 2 * x = 0 → r * p * x = 0} := by
    intro x hx
    have hxI : x ∈ I := by
      change x ∈ (Submodule.span D ({p ^ 2} : Set D)).annihilator
      rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
      simpa only [mul_comm] using hx
    simpa only [mul_assoc] using hn x hxI
  have hm : dB (g ^ n) ∈ J :=
    hbound (Ideal.subset_span (Set.mem_image_of_mem dB hgn))
  change dB g ∈ J
  apply hJ
  exact Ideal.mem_radical_iff.mpr ⟨n, by
    simpa only [map_pow] using hm⟩

end Algebra

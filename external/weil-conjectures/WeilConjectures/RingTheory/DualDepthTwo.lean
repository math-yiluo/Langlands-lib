/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Nakayama

/-! # Depth two for a finite module's dual

Source: Stacks Project, Tag 0AV5(2), specialized to Hom_R(N,R).
-/

@[expose] public section

universe u v

namespace IsLocalRing

open scoped Pointwise

private theorem dual_regular {R : Type u} [CommRing R]
    {N : Type v} [AddCommGroup N] [Module R N] {x : R}
    (hx : IsSMulRegular R x) : IsSMulRegular (Module.Dual R N) x := by
  intro f g h
  ext n
  apply hx
  exact congrArg (fun k : Module.Dual R N ↦ k n) h

private theorem dual_mem_smul_top {R : Type u} [CommRing R]
    {N : Type v} [AddCommGroup N] [Module R N] {x : R}
    (hx : IsSMulRegular R x) (f : Module.Dual R N)
    (hf : ∀ n, f n ∈ x • (⊤ : Submodule R R)) :
    f ∈ x • (⊤ : Submodule R (Module.Dual R N)) := by
  let l : R →ₗ[R] R := LinearMap.lsmul R R x
  let e : R ≃ₗ[R] LinearMap.range l := LinearEquiv.ofInjective l hx
  have hf' (n : N) : f n ∈ LinearMap.range l := by
    obtain ⟨r, _, hr⟩ := (Submodule.mem_smul_pointwise_iff_exists (f n) x ⊤).mp (hf n)
    exact ⟨r, hr⟩
  let g : Module.Dual R N := e.symm.toLinearMap ∘ₗ f.codRestrict (LinearMap.range l) hf'
  apply (Submodule.mem_smul_pointwise_iff_exists f x ⊤).mpr
  refine ⟨g, Submodule.mem_top, ?_⟩
  ext n
  exact congrArg Subtype.val (e.apply_symm_apply ⟨f n, hf' n⟩)

private theorem dual_regular_mod {R : Type u} [CommRing R]
    {N : Type v} [AddCommGroup N] [Module R N] {x y : R}
    (hx : IsSMulRegular R x) (hy : IsSMulRegular (QuotSMulTop x R) y) :
    IsSMulRegular (QuotSMulTop x (Module.Dual R N)) y := by
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ y).mpr
  intro f hf
  obtain ⟨g, _, hg⟩ :=
    (Submodule.mem_smul_pointwise_iff_exists (y • f) x ⊤).mp hf
  apply dual_mem_smul_top hx f
  intro n
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ y).mp hy
  exact (Submodule.mem_smul_pointwise_iff_exists (y • f n) x ⊤).mpr
    ⟨g n, Submodule.mem_top, congrArg (fun k : Module.Dual R N ↦ k n) hg⟩

private theorem regular_pair_of_depth {R : Type u} [CommRing R] [IsLocalRing R]
    (hR : (2 : ℕ∞) ≤ depth (R := R) R) :
    ∃ x y : R, x ∈ maximalIdeal R ∧ y ∈ maximalIdeal R ∧
      IsSMulRegular R x ∧ IsSMulRegular (QuotSMulTop x R) y := by
  classical
  have hm : maximalIdeal R • (⊤ : Submodule R R) ≠ ⊤ := by
    simpa using (maximalIdeal.isMaximal R).ne_top
  have hex : ∃ rs : List R, RingTheory.Sequence.IsRegular R rs ∧
      (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ 2 ≤ rs.length := by
    by_contra! h
    have hle : depth (R := R) R ≤ (1 : ℕ∞) := by
      simp only [depth, Ideal.depth, ite_eq_right hm]
      apply sSup_le
      rintro n ⟨rs, hreg, hmem, rfl⟩
      have hlen : rs.length ≤ 1 := by have := h rs hreg hmem; omega
      exact_mod_cast hlen
    have : (2 : ℕ∞) ≤ 1 := hR.trans hle
    norm_num at this
  obtain ⟨rs, hreg, hmem, hlen⟩ := hex
  cases rs with
  | nil => simp at hlen
  | cons x xs =>
    cases xs with
    | nil => simp at hlen
    | cons y ys =>
      have h₁ := (RingTheory.Sequence.isWeaklyRegular_cons_iff R x (y :: ys)).mp
        hreg.toIsWeaklyRegular
      have h₂ := (RingTheory.Sequence.isWeaklyRegular_cons_iff
        (QuotSMulTop x R) y ys).mp h₁.2
      exact ⟨x, y, hmem x (by simp), hmem y (by simp), h₁.1, h₂.1⟩

/-- A dual over a Noetherian local ring of depth at least two has depth at least two.
Source: Stacks Project, Tag 0AV5(2), used by Tags 0EBA and 0EY6.
(blueprint: new-local-dual-depth-two)

Proof: Extract a regular pair x,y in the maximal ideal from the definition of
depth as the supremum of regular-sequence lengths. Multiplication by x on
Hom_R(N,R) is injective pointwise. Suppose y*f = x*g. Regularity of y on R/xR
implies f(n) is in xR for every n. Since x is regular, its multiplication map
identifies R with xR. Compose f, corestricted to xR, with this linear inverse
to get a linear map f' with x*f' = f. This proves that y is regular on
Hom_R(N,R)/x Hom_R(N,R). The dual is finite by Noetherianity; if it is nonzero,
Nakayama makes the weakly regular pair a regular sequence. Its length gives
the depth bound. The zero dual has infinite depth. This is the pointwise form
of the kernel calculation in Tag 0AV5, and uses no domain or reflexivity
hypothesis. All inverse data is determined uniquely by an injective map. -/
theorem dual_depth_ge_two (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hR : (2 : ℕ∞) ≤ depth (R := R) R) :
    (2 : ℕ∞) ≤ depth (R := R) (Module.Dual R N) := by
  classical
  by_cases hzero : Subsingleton (Module.Dual R N)
  · have := hzero
    have hm : maximalIdeal R • (⊤ : Submodule R (Module.Dual R N)) = ⊤ := by
      apply Submodule.eq_top_iff'.mpr
      intro f
      rw [Subsingleton.elim f 0]
      exact Submodule.zero_mem _
    unfold depth Ideal.depth
    rw [ite_eq_left hm]
    exact le_top
  · have : Nontrivial (Module.Dual R N) := not_subsingleton_iff_nontrivial.mp hzero
    obtain ⟨x, y, hxmem, hymem, hx, hy⟩ := regular_pair_of_depth hR
    have hmem : ∀ r ∈ [x, y], r ∈ maximalIdeal R := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hxmem
      · exact hymem
    have hweak : RingTheory.Sequence.IsWeaklyRegular (Module.Dual R N) [x, y] := by
      rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
        RingTheory.Sequence.isWeaklyRegular_singleton_iff]
      exact ⟨dual_regular hx, dual_regular_mod hx hy⟩
    have hreg := (isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr hweak
    have hm : maximalIdeal R • (⊤ : Submodule R (Module.Dual R N)) ≠ ⊤ :=
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (maximalIdeal_le_jacobson (Module.annihilator R (Module.Dual R N)))).symm
    simp only [depth, Ideal.depth, ite_eq_right hm]
    exact le_sSup ⟨[x, y], hreg, hmem, by simp⟩

end IsLocalRing

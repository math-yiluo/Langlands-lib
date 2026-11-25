/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# A uniform annihilator for a finite module with zero localization

Source: Stacks Project, Exercise 076A and the proof of Lemma 07FC
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

universe u v

namespace Module

/-- A finitely generated module whose localization at a multiplicative subset is zero
is annihilated by one element of that subset. Source: Stacks Project, Exercise 076A,
and the uniform-annihilator form used in the proof of Lemma 07FC.
(blueprint: theorem-finite-etale-covers-proper-henselian--2)

Proof:
1. Choose finitely many generators `m₁, …, mₙ` using
   `def-weil-finitely-generated-module`; every element is a linear combination of them.
2. Each generator maps to zero in the localization. The kernel description in
   `def-weil-pbc-module-localization` supplies `tᵢ ∈ S` with `tᵢ • mᵢ = 0`.
3. Let `s` be the product of the `tᵢ`, with empty product `1`. Multiplicativity gives
   `s ∈ S`. Commutativity shows that `s` kills every generator, and linearity then
   shows that it kills every linear combination, hence every element of `M`. -/
theorem exists_annihilator_of_subsingleton_localizedModule
    {A : Type u} [CommRing A] (S : Submonoid A)
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hzero : Subsingleton (LocalizedModule S M)) :
    ∃ s ∈ S, ∀ m : M, s • m = 0 := by
  classical
  have hkill := (LocalizedModule.subsingleton_iff (S := S) (M := M)).mp hzero
  obtain ⟨g, hg⟩ := Module.Finite.fg_top (R := A) (M := M)
  have hfinite : ∀ t : Finset M, ∃ s ∈ S, ∀ m ∈ t, s • m = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨1, S.one_mem, by simp⟩
    | @insert m t hmt ih =>
      obtain ⟨s, hs, hst⟩ := ih
      obtain ⟨r, hr, hrm⟩ := hkill m
      refine ⟨s * r, S.mul_mem hs hr, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [mul_smul, hrm, smul_zero]
      · rw [mul_comm, mul_smul, hst x hx, smul_zero]
  obtain ⟨s, hs, hsg⟩ := hfinite g
  refine ⟨s, hs, ?_⟩
  intro m
  have hm : m ∈ Submodule.span A (g : Set M) := by rw [hg]; trivial
  induction hm using Submodule.span_induction with
  | mem x hx => exact hsg x hx
  | zero => exact smul_zero s
  | add x y hx hy ihx ihy => rw [smul_add, ihx, ihy, add_zero]
  | smul a x hx ih => rw [smul_comm s a x, ih, smul_zero]

end Module

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Annihilators under flat base change and localization

- `Module.Flat.annihilator_span_singleton_algebraMap`: for a flat ring map `R → S` and `x ∈ R`,
  `Ann_S(x) = Ann_R(x) S` (Stacks 07T8, first part).
- `Module.annihilator_localizedModule_away`: for a finite `A`-module `M` and `f ∈ A`,
  `Ann_{A_f}(M_f) = Ann_A(M) A_f`.
-/

@[expose] public section

open Module

/-- For a flat ring map `R → S` and `x ∈ R`, the annihilator of `x` in `S` is the extension of
the annihilator of `x` in `R`: `Ann_S(φ x) = Ann_R(x) S`.
(blueprint: `lem-weil-pbc-annihilator-element-flat-base-change`) -/
theorem Module.Flat.annihilator_span_singleton_algebraMap {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (x : R) :
    (Ideal.span {algebraMap R S x}).annihilator =
      (Ideal.span {x}).annihilator.map (algebraMap R S) := by
  apply le_antisymm
  · intro s hs
    rw [Ideal.span, Submodule.mem_annihilator_span_singleton, smul_eq_mul] at hs
    have hrel : ∑ _i : Fin 1, x • s = 0 := by
      simp [Algebra.smul_def, mul_comm, hs]
    obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
      (f := fun _ : Fin 1 ↦ x) (x := fun _ : Fin 1 ↦ s) hrel
    rw [show s = _ from hy 0]
    refine sum_mem fun j _ ↦ ?_
    rw [Algebra.smul_def, mul_comm]
    refine Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [Ideal.span, Submodule.mem_annihilator_span_singleton, smul_eq_mul, mul_comm]
    simpa using ha j
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Ideal.span, Submodule.mem_annihilator_span_singleton, smul_eq_mul,
      ← map_mul]
    rw [Ideal.span, Submodule.mem_annihilator_span_singleton, smul_eq_mul] at hr
    rw [hr, map_zero]

/-- For a finite `A`-module `M` and `f ∈ A`, the annihilator of the localization `M_f` over `A_f`
is the extension of the annihilator of `M`: `Ann_{A_f}(M_f) = Ann_A(M) A_f`.
(blueprint: `lem-weil-pbc-annihilator-localization-finite`) -/
theorem Module.annihilator_localizedModule_away {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] [Module.Finite A M] (f : A) :
    Module.annihilator (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) =
      (Module.annihilator A M).map (algebraMap A (Localization.Away f)) := by
  apply le_antisymm
  · intro x hx
    induction x using Localization.induction_on with | H p => ?_
    obtain ⟨a, ⟨_, e, rfl⟩⟩ := p
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := M)
    have key : ∀ m : M, ∃ n : ℕ, (f ^ n * a) • m = 0 := by
      intro m
      have h0 := Module.mem_annihilator.mp hx (LocalizedModule.mk m 1)
      rw [LocalizedModule.mk_smul_mk, ← LocalizedModule.zero_mk (1 : Submonoid.powers f),
        LocalizedModule.mk_eq] at h0
      obtain ⟨⟨_, n, rfl⟩, hn⟩ := h0
      refine ⟨n, ?_⟩
      simpa [Submonoid.smul_def, smul_smul] using hn
    choose n hn using key
    have hmem : f ^ (s.sup n) * a ∈ Module.annihilator A M := by
      rw [Module.mem_annihilator]
      intro m
      have hm : m ∈ Submodule.span A (s : Set M) := hs ▸ Submodule.mem_top
      induction hm using Submodule.span_induction with
      | mem m hm =>
        rw [mul_smul, ← Nat.sub_add_cancel (Finset.le_sup (f := n) hm), pow_add, mul_smul]
        simp only [mul_smul] at hn
        rw [hn m, smul_zero]
      | zero => exact smul_zero _
      | add m₁ m₂ _ _ h₁ h₂ => rw [smul_add, h₁, h₂, add_zero]
      | smul r m _ h => rw [smul_comm, h, smul_zero]
    have hx : Localization.mk a ⟨f ^ e, pow_mem (Submonoid.mem_powers f) e⟩ =
        Localization.mk 1 ⟨f ^ (s.sup n + e), pow_mem (Submonoid.mem_powers f) _⟩ *
          algebraMap A (Localization.Away f) (f ^ (s.sup n) * a) := by
      rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, Localization.mk_eq_mk_iff,
        Localization.r_iff_exists]
      exact ⟨1, by simp [pow_add]; ring⟩
    rw [hx]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hmem)
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Module.mem_annihilator]
    intro y
    induction y using LocalizedModule.induction_on with
    | h m t =>
      rw [← Localization.mk_one_eq_algebraMap, LocalizedModule.mk_smul_mk,
        Module.mem_annihilator.mp ha, LocalizedModule.zero_mk]

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.IntegersAlgebra

/-!
# Approximation of `𝒪_E`-valued functions by locally constant natural numbers

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` such that `ℤ_ℓ → 𝒪_E` is surjective (i.e.
`E = ℚ_ℓ`), and `𝒪_E` carry its `ℓ`-adic topology
(`PadicAlgCl.integersLAdicTopology`). Every continuous function `f : W → 𝒪_E` on a topological
space `W` is, for every `k`, of the form `g + ℓᵏ s` with `s` continuous and `g` locally constant
with values in `ℕ` (`PadicAlgCl.exists_locally_natCast_add_pow_smul`): take for `g` the natural
number representing the residue of `f` modulo `ℓᵏ`.
-/

@[expose] public section

open Topology

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : IntermediateField ℚ_[l] (PadicAlgCl l))

/-- The inclusion `ℤ_ℓ → 𝒪_E` is injective. -/
lemma injective_integersPadicIntHom : Function.Injective (integersPadicIntHom l E) := by
  intro a b h
  have h' := congrArg (algebraMap (integers l E) (PadicAlgCl l)) h
  rw [algebraMap_integersPadicIntHom, algebraMap_integersPadicIntHom] at h'
  exact PadicInt.ext ((algebraMap ℚ_[l] (PadicAlgCl l)).injective h')

/-- A `p`-adic integer is congruent modulo `pᵏ` to the natural number representing its residue
modulo `pᵏ`. -/
lemma padicInt_sub_val_toZModPow_mem (z : ℤ_[l]) (k : ℕ) :
    z - ((PadicInt.toZModPow k z).val : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ k} := by
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val,
    sub_self]

/-- The residue modulo `pᵏ` of a `p`-adic integer is locally constant. -/
lemma padicInt_eventually_toZModPow_eq (z : ℤ_[l]) (k : ℕ) :
    ∀ᶠ y in 𝓝 z, PadicInt.toZModPow k y = PadicInt.toZModPow k z := by
  have hO : IsOpen (Metric.closedBall z ((l : ℝ) ^ (-(k : ℤ)))) :=
    IsUltrametricDist.isOpen_closedBall z
      (zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _).ne'
  filter_upwards [hO.mem_nhds (Metric.mem_closedBall_self (by positivity))] with y hy
  rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hy
  exact hy

variable {l E}

variable (l E) in
/-- The `ℓ`-adic topology on the ring of integers `𝒪_E`, restricted from `ℚ̄_ℓ`. -/
noncomputable abbrev integersLAdicTopology : TopologicalSpace (integers l E) :=
  letI := normedFieldOfAlgebra l E
  inferInstance

/-- **Approximation by locally constant natural numbers**: if `ℤ_ℓ → 𝒪_E` is surjective, every
continuous `f : W → 𝒪_E` is `g + ℓᵏ s` with `s` continuous and `g` locally constant with values
in `ℕ`. -/
theorem exists_locally_natCast_add_pow_smul [FiniteDimensional ℚ_[l] E]
    [τ : TopologicalSpace (integers l E)] [IsTopologicalRing (integers l E)]
    (hτ : τ = integersLAdicTopology l E)
    (hsurj : Function.Surjective (integersPadicIntHom l E)) {W : Type*} [TopologicalSpace W]
    (k : ℕ) (f : C(W, integers l E)) :
    ∃ g s : C(W, integers l E), (∀ x, f x = g x + l ^ k • s x) ∧
      ∀ x, ∃ O : Set W, IsOpen O ∧ x ∈ O ∧ ∃ n : ℕ, ∀ y ∈ O, g y = n := by
  subst hτ
  let := normedFieldOfAlgebra l E
  have := compactSpace_integers l E
  let κ := integersPadicIntHom l E
  have hκ : Continuous κ := continuous_integersPadicIntHom l E
  let h : ℤ_[l] ≃ₜ integers l E :=
    hκ.homeoOfEquivCompactToT2 (f := Equiv.ofBijective κ ⟨injective_integersPadicIntHom l E,
      hsurj⟩)
  let f' : C(W, ℤ_[l]) := (h.symm : C(integers l E, ℤ_[l])).comp f
  have hf' (x : W) : κ (f' x) = f x := h.apply_symm_apply (f x)
  let gN (x : W) : ℕ := (PadicInt.toZModPow k (f' x)).val
  have hloc (x : W) : ∀ᶠ y in 𝓝 x, gN y = gN x := by
    filter_upwards [f'.continuous.continuousAt.eventually
      (padicInt_eventually_toZModPow_eq l (f' x) k)] with y hy
    simp only [gN, hy]
  have hcont {T : Type} [TopologicalSpace T] (φ : ℕ → T) : Continuous fun x ↦ φ (gN x) :=
    continuous_iff_continuousAt.2 fun x ↦ (continuousAt_const (y := φ (gN x))).congr (by
      filter_upwards [hloc x] with y hy
      rw [hy])
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hmem (x : W) : ‖((f' x : ℚ_[l]) - gN x) / (l : ℚ_[l]) ^ k‖ ≤ 1 := by
    have h1 := ((f' x - gN x).norm_le_pow_iff_mem_span_pow k).2
      (padicInt_sub_val_toZModPow_mem l (f' x) k)
    rw [norm_div, norm_pow, Padic.norm_p, div_le_one (by positivity)]
    rw [PadicInt.norm_def] at h1
    push_cast at h1
    rw [zpow_neg, zpow_natCast, ← inv_pow] at h1
    exact h1
  let s' : C(W, ℤ_[l]) :=
    ⟨fun x ↦ ⟨((f' x : ℚ_[l]) - gN x) / (l : ℚ_[l]) ^ k, hmem x⟩,
      Continuous.subtype_mk (((continuous_subtype_val.comp f'.continuous).sub
        (hcont (T := ℚ_[l]) fun n ↦ (n : ℚ_[l]))).div_const _) _⟩
  refine ⟨⟨fun x ↦ κ (gN x), hcont fun n ↦ κ n⟩, ⟨fun x ↦ κ (s' x), hκ.comp s'.continuous⟩, ?_,
    fun x ↦ ?_⟩
  · intro x
    have hl : (l : ℚ_[l]) ^ k ≠ 0 :=
      pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
    have e : f' x = gN x + (l : ℤ_[l]) ^ k * s' x := by
      refine PadicInt.ext ?_
      change (f' x : ℚ_[l]) =
        gN x + (l : ℚ_[l]) ^ k * (((f' x : ℚ_[l]) - gN x) / (l : ℚ_[l]) ^ k)
      field_simp
      ring
    change f x = κ (gN x) + l ^ k • κ (s' x)
    rw [← hf', e, map_add, map_mul, map_pow, map_natCast, map_natCast, nsmul_eq_mul,
      Nat.cast_pow]
  · obtain ⟨O, hOc, hO, hxO⟩ := mem_nhds_iff.1 (hloc x)
    exact ⟨O, hO, hxO, gN x, fun y hy ↦ by
      change κ (gN y) = _
      rw [show gN y = gN x from hOc hy, map_natCast]⟩

end PadicAlgCl

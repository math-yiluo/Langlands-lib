/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-!

# `n`-th roots in profinite groups of order prime to `n`

In a compact Hausdorff group in which every neighbourhood of `1` contains an open normal subgroup
`N` with `|G ⧸ N|` prime to `n` (e.g. a pro-`p` group and `n` prime to `p`), every element is an
`n`-th power: the image of `x ↦ x ^ n` is compact, hence closed, and it is dense since `x ↦ x ^ n`
is a bijection of each finite quotient `G ⧸ N` (`powCoprime`).

This is the divisibility of the pro-`p` kernel `P'` of the map of inertia groups by powers of
`ℓ ≠ p`, used for the finiteness of its action on `ℚ̄_ℓ`-nearby cycles (SGA 4½, [Th. finitude],
§3.7).

-/

@[expose] public section

open Topology

/-- **`n`-th roots in profinite groups of order prime to `n`**: in a compact Hausdorff group in
which every neighbourhood of `1` contains an open normal subgroup `N` with `|G ⧸ N|` prime to `n`,
every element is an `n`-th power. -/
theorem exists_pow_eq_of_forall_nhds_one {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] {n : ℕ}
    (hN : ∀ U ∈ 𝓝 (1 : G), ∃ N : Subgroup G, N.Normal ∧ (N : Set G) ⊆ U ∧
      (Nat.card (G ⧸ N)).Coprime n) (σ : G) : ∃ τ, τ ^ n = σ := by
  have hclosed : IsClosed (Set.range fun x : G ↦ x ^ n) :=
    (isCompact_range (continuous_pow n)).isClosed
  suffices σ ∈ closure (Set.range fun x : G ↦ x ^ n) by
    rw [hclosed.closure_eq] at this
    exact this
  rw [mem_closure_iff_nhds]
  intro U hU
  have hU' : (fun x ↦ σ * x) ⁻¹' U ∈ 𝓝 (1 : G) :=
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨N, hNn, hNU, hcop⟩ := hN _ hU'
  let y := (powCoprime hcop).symm (σ : G ⧸ N)
  have hy : (y.out : G ⧸ N) ^ n = (σ : G ⧸ N) := by
    rw [QuotientGroup.out_eq']
    exact (powCoprime hcop).apply_symm_apply _
  refine ⟨y.out ^ n, ?_, y.out, rfl⟩
  have hmem : σ⁻¹ * y.out ^ n ∈ N := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_pow, hy]
  simpa using hNU hmem

/-- **Roots in normal subgroups of finite index**: if every element of `G` is an `n`-th power,
then every element of a normal subgroup `N` of finite index is the `n`-th power of an element of
`N`: `x ↦ x ^ n` is surjective, hence injective, on the finite quotient `G ⧸ N`. -/
theorem Subgroup.exists_mem_pow_eq_of_forall_exists_pow {G : Type*} [Group G] {n : ℕ}
    (hdiv : ∀ σ : G, ∃ τ, τ ^ n = σ) (N : Subgroup G) [N.Normal] [N.FiniteIndex] {σ : G}
    (hσ : σ ∈ N) : ∃ τ ∈ N, τ ^ n = σ := by
  obtain ⟨τ, rfl⟩ := hdiv σ
  refine ⟨τ, ?_, rfl⟩
  have hsurj : Function.Surjective fun x : G ⧸ N ↦ x ^ n := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨z, rfl⟩ := hdiv y
      exact ⟨z, by simp⟩
  have hinj := Finite.injective_iff_surjective.mpr hsurj
  have h1 : ((τ : G ⧸ N)) ^ n = (1 : G ⧸ N) ^ n := by
    rw [one_pow, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hσ
  exact (QuotientGroup.eq_one_iff _).mp (hinj h1)

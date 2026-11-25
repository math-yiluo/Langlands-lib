/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite free resolutions over Noetherian rings

Source: Stacks Project, Algebra, Lemma 10.71.1 (Tag 00LP), part (2)
(blueprint: lem-weil-pbc-finite-free-resolution-noetherian).
-/

@[expose] public section

universe u v

namespace Module

/-- Every finite module over a (left) Noetherian ring admits an infinite resolution
by finite free modules. Source: Stacks Project, Algebra, Lemma 10.71.1 (Tag 00LP), part (2)
(blueprint: lem-weil-pbc-finite-free-resolution-noetherian).

Proof plan, following the four steps of the node:
1. Choose finitely many generators of `M` (def-weil-finitely-generated-module) and send
   the standard basis of `R^{n₀}` to them. This gives a surjective augmentation `ε`.
2. The kernel of any map out of a finite free module is finitely generated, since `R`
   is Noetherian (def-weil-pbc-noetherian-ring and
   lem-weil-pbc-noetherian-submodule-finite). Choose a finite free surjection onto this
   kernel and compose it with the kernel's inclusion to obtain the next differential.
3. Iterate this construction recursively for every natural-number degree, obtaining
   the sequence of ranks and differentials with image equal to the preceding kernel.
4. Surjectivity gives exactness at `M`; the kernel-image equalities give exactness at
   every free term, and also imply that consecutive maps compose to zero.

The finite function module `Fin (n i) → R` represents `R^{⊕ nᵢ}`. The map `d i` is the
node's `d_{i+1}`, so its target is the free term of degree `i`. -/
theorem exists_finite_free_resolution
    (R : Type u) [Ring R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (n : ℕ → ℕ) (ε : (Fin (n 0) → R) →ₗ[R] M)
      (d : ∀ i : ℕ, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R)),
      Function.Surjective ε ∧ LinearMap.ker ε = LinearMap.range (d 0) ∧
        ∀ i : ℕ, LinearMap.ker (d i) = LinearMap.range (d (i + 1)) := by
  classical
  obtain ⟨n₀, ε, hε⟩ := Module.Finite.exists_fin' R M
  have covers (n : ℕ) (K : Submodule R (Fin n → R)) :
      ∃ (m : ℕ) (f : (Fin m → R) →ₗ[R] (Fin n → R)), LinearMap.range f = K := by
    exact (Submodule.fg_iff_exists_fin_linearMap R (Fin n → R)).mp
      (Submodule.FG.of_le Module.Finite.fg_top le_top)
  -- A state records a finite free term and the kernel to be covered next.
  choose rank map range_map using covers
  let next : (Σ n : ℕ, Submodule R (Fin n → R)) →
      (Σ n : ℕ, Submodule R (Fin n → R)) :=
    fun s ↦ ⟨rank s.1 s.2, LinearMap.ker (map s.1 s.2)⟩
  -- The successor stores precisely the kernel of the map just chosen.
  let s : ℕ → Σ n : ℕ, Submodule R (Fin n → R) :=
    Nat.rec ⟨n₀, LinearMap.ker ε⟩ (fun _ t ↦ next t)
  refine ⟨fun i ↦ (s i).1, ε, fun i ↦ map (s i).1 (s i).2, hε, ?_, ?_⟩
  · exact (range_map n₀ (LinearMap.ker ε)).symm
  · intro i
    exact (range_map (s (i + 1)).1 (s (i + 1)).2).symm

end Module

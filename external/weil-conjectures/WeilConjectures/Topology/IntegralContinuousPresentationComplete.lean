/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ExtremallyDisconnected
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.FunProp

/-! # Completeness of continuous finite presentations

A compatible sequence modulo powers of a scalar has a continuous representative
on a compact extremally disconnected test space.
-/

@[expose] public section
set_option autoImplicit false
namespace ContinuousMap

/-- Compatible classes in a continuous finite presentation have a continuous limit.
Source: Hemo--Richarz--Scholbach, Proposition 5.1, finite-presentation substep.
(blueprint: lem-sp-integral-continuous-presentation-complete).

Proof. Put the representative and all matrix and divisibility witnesses in a
product of copies of the compact coefficient ring. The congruences are closed
conditions. Every finite family is solved by a sufficiently late sequence term
and its compatibility witnesses. Compactness gives a simultaneous solution over
each point. The closed total solution space is compact Hausdorff and surjects onto
the test space. Extremal disconnectedness splits this surjection continuously;
its coordinates give the required continuous functions. Empty matrices, an empty
test space, and arbitrary scalars are included. -/
theorem exists_matrix_limit_of_compatible
    {S : Type*} {R : Type} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [ExtremallyDisconnected S] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CompactSpace R] [T2Space R]
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) C(S, R))
    (b : ℕ → Fin n → C(S, R)) (r : R)
    (hb : ∀ k l : ℕ, k ≤ l →
      ∃ a : Fin m → C(S, R), ∃ c : Fin n → C(S, R),
        ∀ i, b l i = b k i + (∑ j, A i j * a j) + r ^ (k + 1) • c i) :
    ∃ x : Fin n → C(S, R), ∀ k : ℕ,
      ∃ a : Fin m → C(S, R), ∃ c : Fin n → C(S, R),
        ∀ i, x i = b k i + (∑ j, A i j * a j) + r ^ (k + 1) • c i := by
  classical
  let V := (Fin n → R) × ((ℕ → Fin m → R) × (ℕ → Fin n → R))
  let Z := {z : S × V | ∀ k i, z.2.1 i =
    b k i z.1 + (∑ j, A i j z.1 * z.2.2.1 k j) + r ^ (k + 1) * z.2.2.2 k i}
  have hZ : IsClosed Z := by
    change IsClosed {z : S × V | ∀ k i, _}
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro k
    apply isClosed_iInter
    intro i
    apply isClosed_eq
    · dsimp [V]
      fun_prop
    · apply Continuous.add
      · apply Continuous.add
        · exact (b k i).continuous.comp continuous_fst
        · apply continuous_finsetSum
          intro j _
          exact ((A i j).continuous.comp continuous_fst).mul (by dsimp [V]; fun_prop)
      · dsimp [V]
        fun_prop
  let : CompactSpace Z := isCompact_iff_compactSpace.mp hZ.isCompact
  have hp : Function.Surjective (fun z : Z ↦ z.val.1) := by
    intro s
    let B (k : ℕ) : Set V := {z | ∀ i, z.1 i =
      b k i s + (∑ j, A i j s * z.2.1 k j) + r ^ (k + 1) * z.2.2 k i}
    have hB (k : ℕ) : IsClosed (B k) := by
      change IsClosed {z : V | ∀ i, _}
      simp only [Set.ofPred_forall]
      apply isClosed_iInter
      intro i
      apply isClosed_eq
      · dsimp [V]
        fun_prop
      · dsimp [V]
        fun_prop
    have hfin (t : Finset ℕ) : (⋂ k ∈ t, B k).Nonempty := by
      let l := t.sup id
      have hparts : ∀ k : ℕ,
          ∃ a : Fin m → C(S, R), ∃ c : Fin n → C(S, R),
            k ≤ l → ∀ i,
              b l i = b k i + (∑ j, A i j * a j) + r ^ (k + 1) • c i := by
        intro k
        by_cases hk : k ≤ l
        · obtain ⟨a, c, h⟩ := hb k l hk
          exact ⟨a, c, fun _ ↦ h⟩
        · exact ⟨0, 0, fun h ↦ (hk h).elim⟩
      choose a c hac using hparts
      refine ⟨(fun i ↦ b l i s, (fun k j ↦ a k j s, fun k i ↦ c k i s)), ?_⟩
      simp only [Set.mem_iInter]
      intro k hk i
      have hkl : k ≤ l := Finset.le_sup (f := id) hk
      simpa using congrArg (fun f : C(S, R) ↦ f s) (hac k hkl i)
    obtain ⟨z, hz⟩ := CompactSpace.iInter_nonempty hB hfin
    refine ⟨⟨(s, z), ?_⟩, rfl⟩
    exact fun k ↦ Set.mem_iInter.mp hz k
  dsimp [V] at *
  obtain ⟨t, ht, hsec⟩ := CompactT2.ExtremallyDisconnected.projective
    (A := S) continuous_id (continuous_fst.comp continuous_subtype_val) hp
  let x : Fin n → C(S, R) := fun i ↦ ⟨fun s ↦ (t s).val.2.1 i, by fun_prop⟩
  refine ⟨x, fun k ↦ ?_⟩
  let a : Fin m → C(S, R) := fun j ↦ ⟨fun s ↦ (t s).val.2.2.1 k j, by fun_prop⟩
  let c : Fin n → C(S, R) := fun i ↦ ⟨fun s ↦ (t s).val.2.2.2 k i, by fun_prop⟩
  refine ⟨a, c, fun i ↦ ?_⟩
  apply ContinuousMap.ext
  intro s
  have hs : (t s).val.1 = s := congrFun hsec s
  simpa [x, a, c, hs] using (t s).property k i

end ContinuousMap

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.Spectral.Hom
import Mathlib.Topology.Category.TopCat.Limits.Konig
import WeilConjectures.SixFunctors.ConstructibleTopologyHausdorff

@[expose] public section

universe u v

namespace Topology

/-- The inclusion and finite equality clauses in spectral inverse-limit descent.
This is the strict lower-level core of `spectralLimit_descend_opens`; its proof follows
Stacks Project, Topology, Lemma 0A30, parts (2)--(4), using the constructibly closed
nonempty compatible-point lemma for part (2), then finite unions and intersections.
(blueprint: lem-weil-pbc-spectral-limit-descend-inclusion-relations)

Proof in words: for an inclusion, take the constructibly closed differences over the
cofinal upper tail. If every difference were nonempty, the compatible-point theorem
would give a family contradicting the inclusion on X. Thus one difference is empty.
Apply this inclusion result in both directions to the finite union or intersection of
the given compact opens, then pass to a common upper stage. -/
theorem spectralLimit_descend_inclusion_relations
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : I → Type u) [∀ i : I, TopologicalSpace (S i)] [∀ i : I, SpectralSpace (S i)]
    (f : ∀ (i j : I), i ≤ j → S j → S i)
    (hf : ∀ (i j : I) (h : i ≤ j), IsSpectralMap (f i j h))
    (hfid : ∀ (i : I) (x : S i), f i i le_rfl x = x)
    (hfcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (x : S k),
      f i j hij (f j k hjk x) = f i k (hij.trans hjk) x)
    (X : Type v) [TopologicalSpace X] (p : ∀ i : I, X → S i)
    (hpcomp : ∀ (i j : I) (h : i ≤ j) (x : X), f i j h (p j x) = p i x)
    (hlimit : ∀ a : ∀ i : I, S i,
      (∀ (i j : I) (h : i ≤ j), f i j h (a j) = a i) →
      ∃! x : X, ∀ i : I, p i x = a i) :
    (∀ (i j : I) (U : Set (S i)) (V : Set (S j)),
      IsOpen U → IsCompact U → IsOpen V → IsCompact V →
      p i ⁻¹' U ⊆ p j ⁻¹' V →
      ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
        f i k hik ⁻¹' U ⊆ f j k hjk ⁻¹' V) ∧
    (∀ (i : I) (n : ℕ) (U : Set (S i)) (V : Fin n → Set (S i)),
      IsOpen U → IsCompact U → (∀ l : Fin n, IsOpen (V l) ∧ IsCompact (V l)) →
      p i ⁻¹' U = ⋃ l : Fin n, p i ⁻¹' V l →
      ∃ (j : I) (hij : i ≤ j),
        f i j hij ⁻¹' U = ⋃ l : Fin n, f i j hij ⁻¹' V l) ∧
    (∀ (i : I) (n : ℕ) (U : Set (S i)) (V : Fin n → Set (S i)),
      IsOpen U → IsCompact U → (∀ l : Fin n, IsOpen (V l) ∧ IsCompact (V l)) →
      p i ⁻¹' U = ⋂ l : Fin n, p i ⁻¹' V l →
      ∃ (j : I) (hij : i ≤ j),
        f i j hij ⁻¹' U = ⋂ l : Fin n, f i j hij ⁻¹' V l) := by
  sorry

end Topology

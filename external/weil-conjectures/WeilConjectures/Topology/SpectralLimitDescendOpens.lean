/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
import WeilConjectures.Topology.SpectralLimitDescendInclusionRelations

/-!
# Descent of compact opens in directed limits of spectral spaces

Source: Stacks Project, Topology, Lemma 0A30 (`lemma-descend-opens`), specialized to a
nonempty directed set (blueprint: lem-weil-pbc-spectral-limit-descend-opens).
-/

@[expose] public section

universe u v

namespace Topology

/-- Compact opens, inclusions between them, and finite union/intersection equalities descend
from a directed limit of spectral spaces to a stage.
Source: Stacks Project, Topology, Lemma 0A30
(blueprint: lem-weil-pbc-spectral-limit-descend-opens).

Proof outline:
1. The preimages of compact opens at stages form a basis: the initial topology gives
   generation by preimages of opens, and the compact-open bases at stages refine these.
   Directedness puts finitely many stages at one common stage. Spectral transition maps
   preserve compact opens, whose finite unions and intersections are compact open
   (`def-weil-spectral-space`). This includes the empty union and empty intersection.
2. Cover a compact open of the limit by this basis. Compactness reduces the cover to a
   finite union, which comes from one stage by step 1. This proves the first clause.
3. For an inclusion of two pulled-back compact opens, pass to the directed upper tail
   above both indices. At each stage take the difference of the two pulled-back opens.
   These differences are constructibly closed (`def-weil-pbc-constructible-topology`)
   and transition maps carry each difference into the preceding one.
4. If every difference were nonempty, the compatible-point theorem
   `lem-weil-pbc-spectral-limit-constructible-closed-nonempty` would give compatible
   points on the tail. Extend them to all indices using common upper bounds and the
   transition identities. The unique-point limit hypothesis gives a point of the limit
   in the first pulled-back open but outside the second, a contradiction. Thus some
   difference is empty, proving descent of inclusion.
5. For a finite union or intersection equality, combine the family into one compact
   open at the given stage (including the empty family). Apply inclusion descent twice
   and pass to a common upper bound. Preimages preserve unions and intersections, so
   the two inclusions give the requested equality. -/
theorem spectralLimit_descend_opens
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : I → Type u) [∀ i : I, TopologicalSpace (S i)] [∀ i : I, SpectralSpace (S i)]
    (f : ∀ (i j : I), i ≤ j → S j → S i)
    (hf : ∀ (i j : I) (h : i ≤ j), IsSpectralMap (f i j h))
    (hfid : ∀ (i : I) (x : S i), f i i le_rfl x = x)
    (hfcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (x : S k),
      f i j hij (f j k hjk x) = f i k (hij.trans hjk) x)
    (X : Type v) [TopologicalSpace X] (p : ∀ i : I, X → S i)
    (hp : ∀ i : I, Continuous (p i))
    (hpcomp : ∀ (i j : I) (h : i ≤ j) (x : X), f i j h (p j x) = p i x)
    (hlimit : ∀ a : ∀ i : I, S i,
      (∀ (i j : I) (h : i ≤ j), f i j h (a j) = a i) →
      ∃! x : X, ∀ i : I, p i x = a i)
    (htop : ‹TopologicalSpace X› =
      ⨅ i : I, TopologicalSpace.induced (p i) inferInstance) :
    (∀ U : Set X, IsOpen U → IsCompact U →
      ∃ (i : I) (V : Set (S i)), IsOpen V ∧ IsCompact V ∧ p i ⁻¹' V = U) ∧
    (∀ (i j : I) (U : Set (S i)) (V : Set (S j)),
      IsOpen U → IsCompact U → IsOpen V → IsCompact V →
      p i ⁻¹' U ⊆ p j ⁻¹' V →
      ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k), f i k hik ⁻¹' U ⊆ f j k hjk ⁻¹' V) ∧
    (∀ (i : I) (n : ℕ) (U : Set (S i)) (V : Fin n → Set (S i)),
      IsOpen U → IsCompact U → (∀ l : Fin n, IsOpen (V l) ∧ IsCompact (V l)) →
      p i ⁻¹' U = ⋃ l : Fin n, p i ⁻¹' V l →
      ∃ (j : I) (hij : i ≤ j), f i j hij ⁻¹' U = ⋃ l : Fin n, f i j hij ⁻¹' V l) ∧
    (∀ (i : I) (n : ℕ) (U : Set (S i)) (V : Fin n → Set (S i)),
      IsOpen U → IsCompact U → (∀ l : Fin n, IsOpen (V l) ∧ IsCompact (V l)) →
      p i ⁻¹' U = ⋂ l : Fin n, p i ⁻¹' V l →
      ∃ (j : I) (hij : i ≤ j), f i j hij ⁻¹' U = ⋂ l : Fin n, f i j hij ⁻¹' V l) := by
  classical
  have hcombine : ∀ (U : ∀ i, Set (S i)) (F : Finset I),
      (∀ (i : I), i ∈ F → IsOpen (U i) ∧ IsCompact (U i)) →
      ∃ (k : I) (W : Set (S k)), IsOpen W ∧ IsCompact W ∧
        p k ⁻¹' W = ⋂ i ∈ F, p i ⁻¹' U i := by
    intro U F hUF
    induction F using Finset.induction_on with
    | empty =>
        obtain ⟨k⟩ := ‹Nonempty I›
        refine ⟨k, Set.univ, isOpen_univ, isCompact_univ, ?_⟩
        simp
    | @insert a F ha ih =>
        obtain ⟨k, W, hWo, hWc, hWeq⟩ := ih (fun i hi => hUF i (Finset.mem_insert_of_mem hi))
        obtain ⟨k', hak', hkk'⟩ := directed_of (· ≤ ·) a k
        let W' := f a k' hak' ⁻¹' U a ∩ f k k' hkk' ⁻¹' W
        have hWo' : IsOpen W' :=
          ((hf a k' hak').continuous.isOpen_preimage _ (hUF a (by simp)).1).inter
            ((hf k k' hkk').continuous.isOpen_preimage _ hWo)
        have hWc' : IsCompact W' :=
          (inferInstance : SpectralSpace (S k')).inter_isCompact _ _
            ((hf a k' hak').continuous.isOpen_preimage _ (hUF a (by simp)).1)
            ((hf a k' hak').isCompact_preimage_of_isOpen (hUF a (by simp)).1
              (hUF a (by simp)).2)
            ((hf k k' hkk').continuous.isOpen_preimage _ hWo)
            ((hf k k' hkk').isCompact_preimage_of_isOpen hWo hWc)
        refine ⟨k', W', hWo', hWc', ?_⟩
        rw [Set.preimage_inter]
        have haeq : p k' ⁻¹' (f a k' hak' ⁻¹' U a) = p a ⁻¹' U a := by
          ext x
          simp [hpcomp]
        have hkeq : p k' ⁻¹' (f k k' hkk' ⁻¹' W) = p k ⁻¹' W := by
          ext x
          simp [hpcomp]
        rw [haeq, hkeq, hWeq]
        simp
  have hC : @TopologicalSpace.IsTopologicalBasis X
      (⨅ i : I, TopologicalSpace.induced (p i) inferInstance)
      {B | ∃ (U : ∀ i, Set (S i)) (F : Finset I),
        (∀ i ∈ F, U i ∈ {U : Set (S i) | IsOpen U ∧ IsCompact U}) ∧
        B = ⋂ i ∈ F, p i ⁻¹' U i} := by
    exact IsTopologicalBasis.iInf_induced
      (fun i => (inferInstance : SpectralSpace (S i)).isTopologicalBasis) p
  have hdesc : ∀ (B : Set X),
      (∃ (U : ∀ i, Set (S i)) (F : Finset I),
        (∀ (i : I), i ∈ F → IsOpen (U i) ∧ IsCompact (U i)) ∧
        B = ⋂ i ∈ F, p i ⁻¹' U i) →
      ∃ (i : I) (V : Set (S i)), IsOpen V ∧ IsCompact V ∧ p i ⁻¹' V = B := by
    intro B hB
    rcases hB with ⟨U, F, hUF, rfl⟩
    exact hcombine U F hUF
  have hUnion : ∀ (Bs : Finset {B : Set X //
      ∃ (U : ∀ i, Set (S i)) (F : Finset I),
        (∀ (i : I), i ∈ F → IsOpen (U i) ∧ IsCompact (U i)) ∧
        B = ⋂ i ∈ F, p i ⁻¹' U i}),
      ∃ (k : I) (W : Set (S k)), IsOpen W ∧ IsCompact W ∧
        p k ⁻¹' W = ⋃ B ∈ Bs, (B : Set X) := by
    intro Bs
    induction Bs using Finset.induction_on with
    | empty =>
        obtain ⟨k⟩ := ‹Nonempty I›
        refine ⟨k, ∅, isOpen_empty, isCompact_empty, ?_⟩
        simp
    | @insert B Bs hBnot hBs =>
        obtain ⟨k, W, hWo, hWc, hWeq⟩ := hBs
        obtain ⟨i, V, hVo, hVc, hVeq⟩ := hdesc B.1 B.2
        obtain ⟨k', hik', hkk'⟩ := directed_of (· ≤ ·) i k
        let W' := f i k' hik' ⁻¹' V ∪ f k k' hkk' ⁻¹' W
        have hWo' : IsOpen W' :=
          ((hf i k' hik').continuous.isOpen_preimage _ hVo).union
            ((hf k k' hkk').continuous.isOpen_preimage _ hWo)
        have hWc' : IsCompact W' :=
          (hf i k' hik').isCompact_preimage_of_isOpen hVo hVc |>.union
            ((hf k k' hkk').isCompact_preimage_of_isOpen hWo hWc)
        refine ⟨k', W', hWo', hWc', ?_⟩
        rw [Set.preimage_union]
        have hVeq' : p k' ⁻¹' (f i k' hik' ⁻¹' V) = p i ⁻¹' V := by
          ext x
          simp [hpcomp]
        have hWeq' : p k' ⁻¹' (f k k' hkk' ⁻¹' W) = p k ⁻¹' W := by
          ext x
          simp [hpcomp]
        rw [hVeq', hWeq', hVeq, hWeq]
        simp
  have hfirst : ∀ (U : Set X), IsOpen U → IsCompact U →
      ∃ (i : I) (V : Set (S i)), IsOpen V ∧ IsCompact V ∧ p i ⁻¹' V = U := by
    intro U hUo hUc
    let C : Set (Set X) := {B | ∃ (W : ∀ i, Set (S i)) (F : Finset I),
      (∀ (i : I), i ∈ F → IsOpen (W i) ∧ IsCompact (W i)) ∧
      B = ⋂ i ∈ F, p i ⁻¹' W i}
    have hCmem : ∀ B, B ∈ C → IsOpen B := by
      intro B hB
      rcases hdesc B hB with ⟨i, V, hVo, hVc, rfl⟩
      exact hp i |>.isOpen_preimage V hVo
    let A : Type v := {B : Set X // B ∈ C ∧ B ⊆ U}
    have hcover : U ⊆ ⋃ a : A, (a : Set X) := by
      have hUo' : @IsOpen X (⨅ i : I, TopologicalSpace.induced (p i) inferInstance) U := by
        rw [← htop]
        exact hUo
      intro x hx
      have hbasis := TopologicalSpace.IsTopologicalBasis.isOpen_iff
        (t := (⨅ i : I, TopologicalSpace.induced (p i) inferInstance)) (s := U) hC
      rcases (hbasis.mp hUo' x hx) with ⟨B, hBC, hxB, hBU⟩
      have hBmem : B ∈ C := hBC
      exact Set.mem_iUnion.2 ⟨⟨B, hBmem, hBU⟩, hxB⟩
    have hopen : ∀ a : A, IsOpen (a : Set X) := by
      intro a
      exact hCmem a.1 a.2.1
    obtain ⟨t, ht⟩ := hUc.elim_finite_subcover (fun a : A => (a : Set X)) hopen hcover
    let t' : Finset {B : Set X //
        ∃ (W : ∀ i, Set (S i)) (F : Finset I),
          (∀ (i : I), i ∈ F → IsOpen (W i) ∧ IsCompact (W i)) ∧
          B = ⋂ i ∈ F, p i ⁻¹' W i} :=
      t.image (fun a : A => (⟨a.1, a.2.1⟩ : {B : Set X //
        ∃ (W : ∀ i, Set (S i)) (F : Finset I),
          (∀ (i : I), i ∈ F → IsOpen (W i) ∧ IsCompact (W i)) ∧
          B = ⋂ i ∈ F, p i ⁻¹' W i}))
    obtain ⟨k, W, hWo, hWc, hWeq⟩ := hUnion t'
    refine ⟨k, W, hWo, hWc, ?_⟩
    apply Set.Subset.antisymm
    · rw [hWeq]
      intro x hx
      simp only [Set.mem_iUnion] at hx
      rcases hx with ⟨B, hBt, hxB⟩
      have hBt' : B ∈ t.image (fun a : A => (⟨a.1, a.2.1⟩ : {B : Set X //
        ∃ (W : ∀ i, Set (S i)) (F : Finset I),
          (∀ (i : I), i ∈ F → IsOpen (W i) ∧ IsCompact (W i)) ∧
          B = ⋂ i ∈ F, p i ⁻¹' W i})) := by
        simpa [t'] using hBt
      rcases Finset.mem_image.1 hBt' with ⟨a, ha, hEq⟩
      subst B
      exact a.2.2 hxB
    · intro x hx
      have hx' : x ∈ ⋃ a : A, (a : Set X) := hcover hx
      rcases Set.mem_iUnion.1 hx' with ⟨a, hax⟩
      have hax' : x ∈ ⋃ a ∈ t, (a : Set X) := ht hx
      rcases Set.mem_iUnion.1 hax' with ⟨a', hax'⟩
      rcases Set.mem_iUnion.1 hax' with ⟨hat', hax'⟩
      rw [hWeq]
      apply Set.mem_iUnion.2
      refine ⟨⟨a'.1, a'.2.1⟩, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨Finset.mem_image.2 ⟨a', hat', rfl⟩, hax'⟩
  exact ⟨hfirst, spectralLimit_descend_inclusion_relations S f hf hfid hfcomp X p hpcomp hlimit⟩

end Topology

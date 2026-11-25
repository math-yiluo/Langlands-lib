/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
public import Mathlib.Topology.Spectral.ConstructibleTopology
public import Mathlib.Topology.Constructions
import WeilConjectures.SixFunctors.ConstructibleTopologyHausdorff
import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.Spectral.Hom
import WeilConjectures.Mathlib.Topology.Spectral.ConstructibleTopology
public import Mathlib.Topology.WithTopology

/-!
# Quasi-compact limits of constructibly closed subsets

Source: Stacks Project, Topology, Tag 0A2V, parts (1) and (2)
(blueprint: lem-weil-pbc-spectral-limit-constructible-closed-quasi-compact).
-/

@[expose] public section

universe u v w

/-- A spectral map of spectral spaces is continuous for their constructible topologies.
Source: Stacks Project, Topology, Lemma 5.23.3, Tag 0A2S, part (1).
(blueprint: lem-weil-pbc-spectral-map-constructible-continuous)

Proof: For a quasi-compact open `W` in the target, its preimage is open by continuity
and quasi-compact by the spectral-map hypothesis, hence open in the constructible topology
of the source (`def-weil-pbc-constructible-topology`). The preimage of the complement of `W`
is the complement of this quasi-compact open preimage, hence also subbasic and open in the
constructible topology. These two cases cover the subbasis of the target's constructible
topology, so the subbasis criterion (`lem-weil-pbc-continuous-iff-subbase`) gives continuity.
Equivalently, the preimage of every constructibly open subset of the target is constructibly
open in the source. -/
theorem IsSpectralMap.continuous_constructibleTopology
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [SpectralSpace X] [SpectralSpace Y] {f : X → Y} (hf : IsSpectralMap f) :
    @Continuous X Y (constructibleTopology X) (constructibleTopology Y) f := by
  rw [continuous_generateFrom_iff]
  intro s hs
  rcases hs with hs | hs
  · exact IsCompact.isOpen_constructibleTopology_of_isOpen
      (hf.isCompact_preimage_of_isOpen hs.1 hs.2)
      (hf.continuous.isOpen_preimage s hs.1)
  · apply IsCompact.isOpen_constructibleTopology_of_isClosed
    · rw [← Set.preimage_compl]
      exact hf.isCompact_preimage_of_isOpen hs.1.isOpen_compl hs.2
    · exact hs.1.preimage hf.continuous

namespace Topology

-- These diagram axioms are redundant for compactness; keep the existing interface.
set_option linter.unusedVariables false in
/-- For an inverse system of spectral spaces indexed by any preorder, constructibly closed
compatible subsets have a quasi-compact limit, and the whole limit is quasi-compact.
Source: Stacks Project, Topology, Tag 0A2V, parts (1) and (2)
(blueprint: lem-weil-pbc-spectral-limit-constructible-closed-quasi-compact).

Proof outline:
1. Equip each stage with its constructible topology (def-weil-pbc-constructible-topology).
   It is compact and Hausdorff by lem-weil-pbc-spectral-constructible-topology-quasi-compact
   and lem-weil-pbc-spectral-constructible-topology-hausdorff. The transition maps are
   continuous by lem-weil-pbc-spectral-map-constructible-continuous.
2. The identity from the constructible topology to the original topology is continuous:
   compact opens form a basis (def-weil-spectral-space) and are constructibly open.
3. The product of the constructible spaces is compact by
   lem-weil-pbc-tychonoff-product-quasi-compact.
4. Inside this product, families lying in every Z_i and satisfying every compatibility
   equation form a closed subset: coordinate inverse images of Z_i are closed, and the
   equations are closed equalizers by lem-weil-pbc-hausdorff-equalizer-closed.
5. This closed subset is compact by lem-weil-pbc-closed-in-quasi-compact.
6. Unique realization of compatible families gives a map from this subset to X whose
   image is exactly the set of points whose projections lie in all Z_i.
7. Each coordinate of this map is continuous by step 2. The initial topology of X gives
   its continuity by lem-weil-pbc-initial-topology-continuity.
8. Its image is compact by lem-weil-pbc-continuous-image-quasi-compact. Taking every Z_i
   to be the whole stage gives compactness of X as well. -/
theorem isCompact_limit_constructibleClosed
    {I : Type u} [Preorder I] (Y : I → Type v)
    [tY : ∀ i : I, TopologicalSpace (Y i)] [∀ i : I, SpectralSpace (Y i)]
    (f : ∀ (i j : I), i ≤ j → Y j → Y i)
    (hf : ∀ (i j : I) (h : i ≤ j), IsSpectralMap (f i j h))
    (hf_id : ∀ (i : I) (x : Y i), f i i le_rfl x = x)
    (hf_comp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (x : Y k),
      f i j hij (f j k hjk x) = f i k (le_trans hij hjk) x)
    {X : Type w} [tX : TopologicalSpace X] (p : ∀ i : I, X → Y i)
    (hp : ∀ i : I, Continuous (p i))
    (hp_compat : ∀ (i j : I) (h : i ≤ j) (x : X), f i j h (p j x) = p i x)
    (hlimit : ∀ y : (∀ i : I, Y i),
      (∀ (i j : I) (h : i ≤ j), f i j h (y j) = y i) →
      ∃! x : X, ∀ i : I, p i x = y i)
    (htop : tX = ⨅ i : I, TopologicalSpace.induced (p i) (tY i))
    (Z : ∀ i : I, Set (Y i))
    (hZ : ∀ i : I, IsClosed[constructibleTopology (Y i)] (Z i))
    (hZ_compat : ∀ (i j : I) (h : i ≤ j), f i j h '' Z j ⊆ Z i) :
    IsCompact {x : X | ∀ i : I, p i x ∈ Z i} ∧ CompactSpace X := by
  classical
  let cY : ∀ i : I, TopologicalSpace (Y i) := fun i ↦ constructibleTopology (Y i)
  let : ∀ i : I, TopologicalSpace (Y i) := tY
  have hc : ∀ i : I, @CompactSpace (Y i) (cY i) := by
    intro i
    exact @Function.Surjective.compactSpace (WithConstructibleTopology (Y i)) (Y i)
      _ (cY i) _ (WithTopology.continuous_ofTopology _) inferInstance
      (WithTopology.ofTopology_surjective _)
  have ht : ∀ i : I, @T2Space (Y i) (cY i) := fun i ↦
    t2Space_constructibleTopology (Y i)
  have hf' : ∀ (i j : I) (h : i ≤ j),
      @Continuous (Y j) (Y i) (cY j) (cY i) (f i j h) := fun i j h ↦
    (hf i j h).continuous_constructibleTopology
  have hid : ∀ i : I, @Continuous (Y i) (Y i) (cY i) (tY i) id := by
    intro i
    exact continuous_id_of_le constructibleTopology_le
  let : ∀ i : I, TopologicalSpace (Y i) := cY
  let : ∀ i : I, CompactSpace (Y i) := hc
  let : ∀ i : I, T2Space (Y i) := ht
  let L : Set (∀ i : I, Y i) :=
    {y | ∀ (i j : I) (h : i ≤ j), f i j h (y j) = y i}
  have hL : IsClosed L := by
    simp only [L, Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun h ↦
      isClosed_eq ((hf' i j h).comp (continuous_apply j)) (continuous_apply i)
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL.isCompact
  let realize : L → X := fun y ↦ (hlimit y.val y.property).choose
  have hrealize_spec (y : L) (i : I) : p i (realize y) = y.val i :=
    (hlimit y.val y.property).choose_spec.1 i
  have hrealize : Continuous realize := by
    rw [htop, continuous_iInf_rng]
    intro i
    rw [continuous_induced_rng]
    have heq : p i ∘ realize = fun y : L ↦ y.val i :=
      funext fun y ↦ hrealize_spec y i
    rw [heq]
    exact @Continuous.comp L (Y i) (Y i) _ (cY i) (tY i)
      (fun y : L ↦ y.val i) id (hid i)
      ((continuous_apply i).comp continuous_subtype_val)
  have hrealize_surj : Function.Surjective realize := by
    intro x
    let y : L := ⟨fun i ↦ p i x, fun i j h ↦ hp_compat i j h x⟩
    refine ⟨y, ?_⟩
    exact ((hlimit y.val y.property).choose_spec.2 x (fun _ ↦ rfl)).symm
  have hclosed : IsClosed {y : L | ∀ i : I, y.val i ∈ Z i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦
      (hZ i).preimage ((continuous_apply i).comp continuous_subtype_val)
  have himage : realize '' {y : L | ∀ i : I, y.val i ∈ Z i} =
      {x : X | ∀ i : I, p i x ∈ Z i} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      rw [hrealize_spec]
      exact hy i
    · intro hx
      obtain ⟨y, rfl⟩ := hrealize_surj x
      refine ⟨y, ?_, rfl⟩
      intro i
      rw [← hrealize_spec]
      exact hx i
  exact ⟨himage ▸ hclosed.isCompact.image hrealize,
    Function.Surjective.compactSpace hrealize hrealize_surj⟩

end Topology

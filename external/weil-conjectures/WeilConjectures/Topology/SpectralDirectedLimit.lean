/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
public import Mathlib.Order.Directed
import WeilConjectures.Topology.SpectralLimitConstructibleClosed

/-!
# Directed inverse limits of spectral spaces

Source: Stacks Project, Topology, Tag 0A2Z, in the directed-set case
(blueprint: lem-weil-pbc-spectral-directed-limit-spectral).
-/

@[expose] public section

universe u v

namespace Topology

/-- A directed inverse limit of spectral spaces with spectral transition maps is spectral,
and its projections are spectral. Source: Stacks Project, Topology, Tag 0A2Z
(blueprint: lem-weil-pbc-spectral-directed-limit-spectral).

Proof:
1. The initial topology and directedness give a basis of inverse images of compact opens
from single stages. A common upper bound combines two such opens into a single inverse image.
2. For a compact open `U` at stage `i`, use the constructibly closed subsets
`f i j ⁻¹' U` for `i ≤ j` and the whole stage otherwise. The compatible-subset compactness
lemma `lem-weil-pbc-spectral-limit-constructible-closed-quasi-compact` (Tag 0A2V), with
`def-weil-pbc-constructible-topology`, makes their inverse limit `p i ⁻¹' U` compact.
The same lemma applied to whole stages makes the limit compact.
3. Use `PrespectralSpace.of_isTopologicalBasis` for prespectrality. The basic opens
are closed under intersection by Step 1, and are compact by Step 2. Apply
`QuasiSeparatedSpace.of_isTopologicalBasis`, which covers compact opens by finitely
many basis members and distributes intersections over those finite unions.
4. Step 2 and continuity give spectral projections. Together with Step 3 these are
the compactness, prespectrality, and quasi-separatedness clauses of
`def-weil-spectral-space`. No separate compact-open descent theorem is needed.
5. For an irreducible closed subset `Z`, the closures of its images in the stages are
irreducible by `lem-weil-pbc-irreducible-continuous-image` and
`lem-weil-pbc-irreducible-closure`. Their unique generic points are compatible, hence lift
to a limit point. A basic-open neighbourhood argument shows that this point belongs to
`Z` and its closure equals `Z`.
6. Inseparable points have inseparable images in every stage, so their images agree
by T0 separation. Injectivity of the tuple map therefore makes the limit T0. With
Step 5 this gives sobriety and uniqueness of generic points, completing spectrality.
-/
theorem spectralSpace_directedLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (Y : I → Type u) [∀ i : I, TopologicalSpace (Y i)] [∀ i : I, SpectralSpace (Y i)]
    (f : ∀ (i j : I), i ≤ j → Y j → Y i)
    (hf : ∀ (i j : I) (h : i ≤ j), IsSpectralMap (f i j h))
    (hf_id : ∀ i : I, f i i le_rfl = id)
    (hf_comp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k),
      f i j hij ∘ f j k hjk = f i k (le_trans hij hjk))
    (X : Type v) [tX : TopologicalSpace X] (p : ∀ i : I, X → Y i)
    (hp : ∀ i : I, Continuous (p i))
    (hp_compat : ∀ (i j : I) (h : i ≤ j), f i j h ∘ p j = p i)
    (hp_injective : Function.Injective (fun x : X => fun i : I => p i x))
    (hp_surjective : ∀ s : ∀ i : I, Y i,
      (∀ (i j : I) (h : i ≤ j), f i j h (s j) = s i) →
      ∃ x : X, ∀ i : I, p i x = s i)
    (h_initial : tX = ⨅ i : I, TopologicalSpace.induced (p i) inferInstance) :
    SpectralSpace X ∧ ∀ i : I, IsSpectralMap (p i) := by
  open Set TopologicalSpace in
  classical
  have hid (i : I) (y : Y i) : f i i le_rfl y = y := congrFun (hf_id i) y
  have hcomp (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (y : Y k) :
      f i j hij (f j k hjk y) = f i k (le_trans hij hjk) y :=
    congrFun (hf_comp i j k hij hjk) y
  have hcompat (i j : I) (h : i ≤ j) (x : X) : f i j h (p j x) = p i x :=
    congrFun (hp_compat i j h) x
  have hlimit (s : ∀ i : I, Y i)
      (hs : ∀ (i j : I) (h : i ≤ j), f i j h (s j) = s i) :
      ∃! x : X, ∀ i : I, p i x = s i := by
    obtain ⟨x, hx⟩ := hp_surjective s hs
    exact ⟨x, hx, fun y hy ↦ hp_injective (funext fun i ↦ (hy i).trans (hx i).symm)⟩
  have hproj (i : I) (U : Set (Y i)) (ho : IsOpen U) (hc : IsCompact U) :
      IsCompact (p i ⁻¹' U) := by
    let Z : ∀ j : I, Set (Y j) := fun j ↦
      if h : i ≤ j then f i j h ⁻¹' U else univ
    have hZ (j : I) : IsClosed[constructibleTopology (Y j)] (Z j) := by
      dsimp only [Z]
      split_ifs with h
      · refine @IsClosed.mk (Y j) (constructibleTopology (Y j)) _ ?_
        apply TopologicalSpace.isOpen_generateFrom_of_mem
        right
        exact ⟨(ho.preimage (hf i j h).continuous).isClosed_compl, by
          simpa only [compl_compl] using (hf i j h).isCompact_preimage_of_isOpen ho hc⟩
      · exact @isClosed_univ (Y j) (constructibleTopology (Y j))
    have hZcompat (j k : I) (h : j ≤ k) : f j k h '' Z k ⊆ Z j := by
      rintro _ ⟨y, hy, rfl⟩
      dsimp only [Z] at *
      split_ifs with hij
      · have hik := le_trans hij h
        rw [dite_eq_left hik] at hy
        change f i j hij (f j k h y) ∈ U
        rwa [hcomp]
      · exact mem_univ _
    have hset : {x : X | ∀ j : I, p j x ∈ Z j} = p i ⁻¹' U := by
      ext x
      constructor
      · intro hx
        have hi := hx i
        simpa [Z, hid] using hi
      · intro hx j
        dsimp only [Z]
        split_ifs with h
        · change f i j h (p j x) ∈ U
          rwa [hcompat]
        · exact mem_univ _
    rw [← hset]
    exact (isCompact_limit_constructibleClosed Y f hf hid hcomp p hp hcompat hlimit
      h_initial Z hZ hZcompat).1
  have hcompact : CompactSpace X :=
    (isCompact_limit_constructibleClosed Y f hf hid hcomp p hp hcompat hlimit
      h_initial (fun i ↦ univ) (fun i ↦ @isClosed_univ (Y i) (constructibleTopology (Y i)))
      (fun _ _ _ ↦ subset_univ _)).2
  let B : Set (Set X) :=
    {S | ∃ (i : I) (U : Set (Y i)), IsOpen U ∧ IsCompact U ∧ p i ⁻¹' U = S}
  have hopen : ∀ S ∈ B, IsOpen S := by
    rintro _ ⟨i, U, ho, hc, rfl⟩
    exact ho.preimage (hp i)
  have hbcompact : ∀ S ∈ B, IsCompact S := by
    rintro _ ⟨i, U, ho, hc, rfl⟩
    exact hproj i U ho hc
  have hinter : ∀ S ∈ B, ∀ T ∈ B, S ∩ T ∈ B := by
    rintro _ ⟨i, U, hUo, hUc, rfl⟩ _ ⟨j, V, hVo, hVc, rfl⟩
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    let W := f i k hik ⁻¹' U ∩ f j k hjk ⁻¹' V
    have hWo : IsOpen W :=
      (hUo.preimage (hf i k hik).continuous).inter (hVo.preimage (hf j k hjk).continuous)
    have hWc : IsCompact W :=
      ((hf i k hik).isCompact_preimage_of_isOpen hUo hUc).inter_of_isOpen
        ((hf j k hjk).isCompact_preimage_of_isOpen hVo hVc)
        (hUo.preimage (hf i k hik).continuous) (hVo.preimage (hf j k hjk).continuous)
    refine ⟨k, W, hWo, hWc, ?_⟩
    ext x
    simp only [W, mem_preimage, mem_inter_iff, hcompat]
  have hgen : tX = generateFrom B := by
    apply le_antisymm (le_generateFrom hopen)
    rw [h_initial]
    apply le_iInf
    intro i
    rw [(PrespectralSpace.isTopologicalBasis (X := Y i)).eq_generateFrom,
      induced_generateFrom_eq]
    apply generateFrom_anti
    rintro _ ⟨U, ⟨ho, hc⟩, rfl⟩
    exact ⟨i, U, ho, hc, rfl⟩
  have huniv : univ ∈ B := by
    obtain ⟨i⟩ := ‹Nonempty I›
    exact ⟨i, univ, isOpen_univ, isCompact_univ, preimage_univ⟩
  have hbasis : IsTopologicalBasis B := by
    simpa only [insert_eq_of_mem huniv] using
      isTopologicalBasis_of_subbasis_of_inter hgen (fun {_} hs {_} ht ↦ hinter _ hs _ ht)
  have hpre : PrespectralSpace X := .of_isTopologicalBasis hbasis hbcompact
  have hqs : QuasiSeparatedSpace X := by
    have hrange : range (fun S : B ↦ (S : Set X)) = B := by ext; simp
    apply QuasiSeparatedSpace.of_isTopologicalBasis (b := fun S : B ↦ (S : Set X))
      (hrange.symm ▸ hbasis)
    intro S T
    exact hbcompact _ (hinter _ S.2 _ T.2)
  have ht0 : T0Space X :=
    ⟨fun {_ _} hxy ↦ hp_injective (funext fun i ↦ (hxy.map (hp i)).eq)⟩
  have hsober : QuasiSober X := by
    constructor
    intro Z hZ hZclosed
    let H (i : I) : IsIrreducible (p i '' Z) := hZ.image (p i) (hp i).continuousOn
    let g (i : I) : Y i := (H i).genericPoint
    have hg (i : I) : IsGenericPoint (g i) (closure (p i '' Z)) :=
      (H i).isGenericPoint_genericPoint_closure
    have hgcompat (i j : I) (h : i ≤ j) : f i j h (g j) = g i := by
      apply IsGenericPoint.eq _ (hg i)
      have hm := (hg j).image (hf i j h).continuous
      simpa only [closure_image_closure (hf i j h).continuous, ← image_comp,
        hp_compat] using hm
    obtain ⟨x, hx⟩ := hp_surjective g hgcompat
    have hxZ : x ∈ Z := by
      by_contra hn
      obtain ⟨S, hS, hxS, hSZ⟩ :=
        hbasis.exists_subset_of_mem_open hn hZclosed.isOpen_compl
      obtain ⟨i, U, ho, hc, rfl⟩ := hS
      have hxi : g i ∈ U := (hx i) ▸ hxS
      obtain ⟨y, hyU, z, hzZ, hzy⟩ := mem_closure_iff.mp (hg i).mem U ho hxi
      exact hSZ (show z ∈ p i ⁻¹' U by simpa only [mem_preimage, hzy] using hyU) hzZ
    refine ⟨x, subset_antisymm (closure_minimal (singleton_subset_iff.mpr hxZ) hZclosed) ?_⟩
    intro z hz
    apply mem_closure_iff.mpr
    intro W hWo hzW
    obtain ⟨S, hS, hzS, hSW⟩ := hbasis.exists_subset_of_mem_open hzW hWo
    obtain ⟨i, U, ho, hc, rfl⟩ := hS
    have hgi : g i ∈ U := (hg i).mem_open_set_iff ho |>.mpr
      ⟨p i z, subset_closure (mem_image_of_mem _ hz), hzS⟩
    refine ⟨x, hSW ?_, mem_singleton x⟩
    simpa only [mem_preimage, hx i] using hgi
  refine ⟨?_, fun i ↦ ⟨hp i, fun U ho hc ↦ hproj i U ho hc⟩⟩
  exact { toT0Space := ht0
          toCompactSpace := hcompact
          toQuasiSober := hsober
          toQuasiSeparatedSpace := hqs
          toPrespectralSpace := hpre }

end Topology

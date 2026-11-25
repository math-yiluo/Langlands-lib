/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Separation.Regular

/-!
# Bijective clopen pullback between profinite spaces

Source: agent consequence of Stacks Project, `topology.tex`, Tag 08ZZ
(lemma-profinite-refine-open-covering), using its pointwise clopen-basis consequence.
The criterion below is not the finite-refinement assertion of that tag.
(blueprint: lem-sfb-profinite-clopen-pullback-bijective-open).
-/

@[expose] public section

universe u v

/-- A continuous map between compact Hausdorff totally disconnected spaces whose
inverse image on clopens is bijective is injective, surjective and open. The image of
each source clopen is the unique target clopen with that inverse image. Empty spaces
are permitted.

Source: agent separation and finite-subcover consequence of Stacks Project,
`topology.tex`, Tag 08ZZ (lemma-profinite-refine-open-covering), using its pointwise
clopen-basis consequence (blueprint: lem-sfb-profinite-clopen-pullback-bijective-open).

Proof for stage 3:
1. For distinct points of P, Hausdorffness and `lem-weil-pbc-profinite-clopen-basis`
   give a clopen containing one and excluding the other. Surjectivity of clopen
   pullback expresses it as an inverse image. Equal images of the two points would
   give equal membership in that inverse image, a contradiction. Thus h is injective.
2. If q in Q is outside h(P), Hausdorffness and
   `lem-weil-pbc-profinite-clopen-basis` give, around every image point, a clopen
   excluding q. The inverse images of all clopens excluding q cover P. Compactness
   gives finitely many whose inverse images still cover P. Their union W is clopen,
   excludes q and has the same inverse image as Q. Injectivity of clopen pullback
   forces W = Q, a contradiction. The finite subcover may be empty; the argument
   still applies. Hence h is surjective.
3. For a source clopen U, surjectivity of clopen pullback gives a target clopen V
   with inverse image U. Surjectivity of h implies h(U) = V. Injectivity of clopen
   pullback makes this V unique, proving the image and uniqueness clauses.
4. By `lem-weil-pbc-profinite-clopen-basis`, each open subset of P is a union of
   clopens contained in it. Images commute with unions, and step 3 makes the images
   of those clopens open. Thus h is open, including the empty-union case. -/
theorem bijective_and_isOpenMap_of_bijective_clopen_preimage
    {P : Type u} {Q : Type v} [TopologicalSpace P] [TopologicalSpace Q]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]
    {h : P → Q} (hh : Continuous h)
    (hclop : Function.Bijective
      (fun V : TopologicalSpace.Clopens Q ↦
        (⟨h ⁻¹' (V : Set Q), V.isClopen.preimage hh⟩ : TopologicalSpace.Clopens P))) :
    Function.Injective h ∧ Function.Surjective h ∧
      (∀ U : TopologicalSpace.Clopens P,
        IsClopen (h '' (U : Set P)) ∧
          h ⁻¹' (h '' (U : Set P)) = (U : Set P) ∧
          ∀ V : TopologicalSpace.Clopens Q,
            h ⁻¹' (V : Set Q) = (U : Set P) → (V : Set Q) = h '' (U : Set P)) ∧
      IsOpenMap h := by
  let pull : TopologicalSpace.Clopens Q → TopologicalSpace.Clopens P :=
    fun V ↦ ⟨h ⁻¹' (V : Set Q), V.isClopen.preimage hh⟩
  have hinj : Function.Injective h := by
    intro x y hxy
    by_contra hne
    obtain ⟨U, hU, hxU, hUy⟩ := exists_isClopen_mem_of_isOpen
      (isClosed_singleton (x := y)).isOpen_compl
      (show x ∈ ({y} : Set P)ᶜ from hne)
    obtain ⟨V, hV⟩ := hclop.2 (⟨U, hU⟩ : TopologicalSpace.Clopens P)
    have hpre : h ⁻¹' (V : Set Q) = U := congrArg SetLike.coe hV
    have hxV : h x ∈ V := by
      change x ∈ h ⁻¹' (V : Set Q)
      rw [hpre]
      exact hxU
    have hyU : y ∈ U := by
      rw [← hpre]
      change h y ∈ V
      rwa [← hxy]
    exact hUy hyU (Set.mem_singleton y)
  have hsurj : Function.Surjective h := by
    intro q
    by_contra hq
    have hclosed : IsClosed (Set.range h) := by
      simpa only [Set.image_univ] using hh.isClosedMap Set.univ isClosed_univ
    obtain ⟨V, hV, hqV, hVr⟩ := exists_isClopen_mem_of_isOpen
      hclosed.isOpen_compl (show q ∈ (Set.range h)ᶜ from hq)
    have hpre : h ⁻¹' V = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hVr hx ⟨x, rfl⟩
    have hpull : pull ⟨V, hV⟩ = pull ⊥ := by
      apply TopologicalSpace.Clopens.ext
      exact hpre
    have hVempty : (⟨V, hV⟩ : TopologicalSpace.Clopens Q) = ⊥ := hclop.1 hpull
    have : V = ∅ := congrArg SetLike.coe hVempty
    simp only [this, Set.mem_empty_iff_false] at hqV
  have himages : ∀ U : TopologicalSpace.Clopens P,
      IsClopen (h '' (U : Set P)) ∧
        h ⁻¹' (h '' (U : Set P)) = (U : Set P) ∧
        ∀ V : TopologicalSpace.Clopens Q,
          h ⁻¹' (V : Set Q) = (U : Set P) → (V : Set Q) = h '' (U : Set P) := by
    intro U
    obtain ⟨V, hV⟩ := hclop.2 U
    have hpre : h ⁻¹' (V : Set Q) = (U : Set P) := congrArg SetLike.coe hV
    have himage : h '' (U : Set P) = (V : Set Q) := by
      rw [← hpre, Set.image_preimage_eq _ hsurj]
    refine ⟨himage ▸ V.isClopen, ?_, ?_⟩
    · rw [himage]
      exact hpre
    · intro W hW
      rw [← hW, Set.image_preimage_eq _ hsurj]
  refine ⟨hinj, hsurj, himages, ?_⟩
  apply isTopologicalBasis_isClopen.isOpenMap_iff.mpr
  intro U hU
  exact (himages ⟨U, hU⟩).1.isOpen

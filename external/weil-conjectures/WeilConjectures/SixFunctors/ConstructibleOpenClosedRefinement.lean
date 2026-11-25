/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.SixFunctors.ExistsFiniteRefinementTree
import WeilConjectures.Topology.ConstructibleIsRetrocompact

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry.Scheme

/-! # Finite open--closed refinement through constructible strata

Source: Stacks Project, Topology, Tags 005H, 09YH, and 09Y4; Schemes, Tags
01ZG, 01KO, 01J3, 03GI, 01JR, 01JT, and 01JY
(auxiliary; not a blueprint node).

## Main statement

* `exists_finite_open_closed_refinement`: factor finitely many constructible
  immersed partitions through quasi-compact open--closed pieces and a finite
  binary pullback tree.  This declaration is statement-only in stage 2.
-/

private theorem exists_constructible_cut
    {W S : Scheme.{u}} [CompactSpace W] [QuasiSeparatedSpace W]
    (s : S ⟶ W) [IsImmersion s]
    (hc : Topology.IsConstructible (Set.range s.base)) :
    ∃ (O Q Z : Scheme.{u}) (o : O ⟶ W) (c : S ⟶ O)
      (q : Q ⟶ O) (z : Z ⟶ W),
      IsOpenImmersion o ∧ IsClosedImmersion c ∧ IsOpenImmersion q ∧
      IsClosedImmersion z ∧ c ≫ o = s ∧ QuasiCompact o ∧ QuasiCompact q ∧
      Set.range (q ≫ o).base = Set.range o.base \ Set.range s.base ∧
      Set.range z.base = (Set.range o.base)ᶜ := by
  classical
  have hE : IsCompact (Set.range s.base) := by
    simpa using hc.isRetrocompact isCompact_univ isOpen_univ
  have : CompactSpace S := by
    rw [← isCompact_univ_iff]
    apply s.isEmbedding.isCompact_iff.mpr
    simpa using hE
  obtain ⟨U, c, hU, hclosed, hfac⟩ := s.exists_isCompact_isClosedImmersion
  have : IsClosedImmersion c := hclosed
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have : QuasiSeparatedSpace U.toScheme := quasiSeparatedSpace_of_quasiSeparated U.ι
  let D : U.toScheme.Opens := ⟨(Set.range c)ᶜ, c.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hD : IsCompact (D : Set U.toScheme) := by
    apply U.ι.isEmbedding.isCompact_iff.mpr
    have himage : U.ι '' (D : Set U.toScheme) = (Set.range s.base)ᶜ ∩ (U : Set W) := by
      rw [← hfac]
      ext x
      simp only [D, TopologicalSpace.Opens.coe_mk, Scheme.Hom.comp_base, TopCat.coe_comp,
        Set.mem_image, Set.mem_compl_iff, Set.mem_range, Function.comp_apply, Set.mem_inter_iff]
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨?_, y.property⟩
        rintro ⟨t, ht⟩
        exact hy ⟨t, U.ι.isEmbedding.injective ht⟩
      · rintro ⟨hx, hxU⟩
        refine ⟨⟨x, hxU⟩, ?_, rfl⟩
        rintro ⟨t, ht⟩
        exact hx ⟨t, congrArg U.ι ht⟩
    rw [himage]
    exact hc.compl.isRetrocompact hU U.isOpen
  have : CompactSpace D.toScheme := isCompact_iff_compactSpace.mp hD
  let I := IdealSheafData.vanishingIdeal
    (⟨(U : Set W)ᶜ, U.isOpen.isClosed_compl⟩ : TopologicalSpace.Closeds W)
  refine ⟨U.toScheme, D.toScheme, I.subscheme, U.ι, c, D.ι, I.subschemeι,
    inferInstance, hclosed, inferInstance, inferInstance, hfac,
    inferInstance, inferInstance, ?_, ?_⟩
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    rw [← hfac]
    ext x
    simp only [D, TopologicalSpace.Opens.coe_mk, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.mem_image, Set.mem_compl_iff, Set.mem_range, Function.comp_apply,
      Set.mem_sdiff, Scheme.Opens.range_ι]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property, ?_⟩
      rintro ⟨t, ht⟩
      exact hy ⟨t, U.ι.isEmbedding.injective ht⟩
    · rintro ⟨hxU, hx⟩
      refine ⟨⟨x, hxU⟩, ?_, rfl⟩
      rintro ⟨t, ht⟩
      exact hx ⟨t, congrArg U.ι ht⟩
  · simp [I]

/-- Finite open--closed refinement through constructible strata.

Source: Stacks Project, Topology, Tags 005H, 09YH, and 09Y4; Schemes, Tags
01ZG, 01KO, 01J3, 03GI, 01JR, 01JT, and 01JY
(auxiliary; not a blueprint node).

Proof (all deferred to stage 3):
1. Write `E = range s`.  Constructible sets are retrocompact (Topology Tag 09YH); on the
   quasi-compact open `W` itself this makes `E` quasi-compact.  An immersion is a closed
   immersion followed by an open immersion, each a homeomorphism onto its image, so `S` is
   homeomorphic to `E` and quasi-compact.
2. The closed-immersion neighbourhood theorem (Limits Tag 01ZG, shrinking argument) applied
   to `s` with quasi-compact source gives a quasi-compact open `O ⊆ W` and a closed
   immersion `c : S ⟶ O` with `c ≫ o = s`.  Put `Q = O \ E`, an open subscheme of `O`.  By
   Boolean closure (Tag 005H) `W \ E` is constructible; its retrocompactness on the
   quasi-compact open `O` makes `Q = (W \ E) ∩ O` quasi-compact.
3. Open and closed subschemes of a quasi-separated scheme are quasi-separated (Schemes Tag
   01KO, by the affine-cover criterion, the affine description of closed immersions and
   compactness of closed subsets of quasi-compact spaces).
4. Let `Z ⟶ W` be the reduced induced closed subscheme on `W \ O` (Schemes Tag 01J3); it is
   quasi-compact (closed in `W`) and quasi-separated by step 3.  `O, S, Q` are qcqs by
   steps 1--3.  Each of `o, z, c, q` has quasi-compact source and quasi-separated target,
   hence is quasi-compact (Tag 03GI (1)).
5. Images of these pullbacks are set-theoretic inverse images: for opens by Tag 01JR; for a
   closed immersion `Z ⟶ X` and `f : T ⟶ X`, by Tag 01JT the points over `t` and `z`
   are the primes of `κ(t) ⊗_{κ(f t)} κ(z) ≅ κ(t)` when `f t` is the image of `z`, so the
   image of `T ×_X Z ⟶ T` is `f⁻¹(Z)`, also for nonreduced `Z`.
6. Replacement of a current leaf `t : T ⟶ W` for one index: the children of `T` are
   `A = T ×_W O` (open) and `D = T ×_W Z` (closed); the children of `A` are
   `B = A ×_O Q` (open) and `C = A ×_O S` (closed), by base change of open and closed
   immersions (Tag 01JY).  By step 5 the images are complementary; `C ⟶ S` is the second
   projection and its composite to `W` is the structural map.  `D, B, C` have images
   outside `O`, in `O \ E`, and in `E`; only `C` meets `E`.  Empty children are allowed.
7. The four child arrows are quasi-compact by base change (Tag 01K5); for quasi-compact `T`,
   Tag 03GI (2) makes `A, D`, then `B, C` quasi-compact, and step 3 makes them
   quasi-separated.  Every vertex stays a closed subscheme of an open subscheme of `W`
   (restriction to opens, composition of closed immersions, Morphisms Tag 01QS).
8. Enumerate all strata of all partitions and process them one by one from the one-vertex
   tree `W` (Topology Tag 09Y4), keeping the invariant: a finite binary tree of qcqs
   locally closed vertices with quasi-compact arrows, terminal images disjoint and covering
   `W`, and for each processed stratum every terminal vertex avoids `E` or has a recorded
   factorization through `S` (kept by composing with later projections).  With no strata
   no replacement is made and the tree is the single leaf `W`.
9. A nonempty final leaf has a point lying in some stratum of each partition; the invariant
   excludes avoidance, so the recorded projection gives `f : V ⟶ S` with `f ≫ s` the
   canonical map.  The nonempty leaves partition `W`; for empty `W` or no partitions the
   remaining clauses are vacuous.
-/
theorem exists_finite_open_closed_refinement
    {W : Scheme.{u}} [CompactSpace W] [QuasiSeparatedSpace W]
    (m : ℕ) (n : Fin m → ℕ)
    (S : ∀ a : Fin m, Fin (n a) → Scheme.{u})
    (s : ∀ (a : Fin m) (j : Fin (n a)), S a j ⟶ W)
    (hs : ∀ (a : Fin m) (j : Fin (n a)), IsImmersion (s a j))
    (hc : ∀ (a : Fin m) (j : Fin (n a)),
      Topology.IsConstructible (Set.range (s a j).base))
    (hcover : ∀ a : Fin m,
      (⋃ j : Fin (n a), Set.range (s a j).base) = Set.univ)
    (hdisjoint : ∀ a : Fin m,
      Pairwise (fun j k : Fin (n a) ↦
        Disjoint (Set.range (s a j).base) (Set.range (s a k).base))) :
    ∃ (O Q Z : ∀ a : Fin m, Fin (n a) → Scheme.{u})
      (o : ∀ (a : Fin m) (j : Fin (n a)), O a j ⟶ W)
      (c : ∀ (a : Fin m) (j : Fin (n a)), S a j ⟶ O a j)
      (q : ∀ (a : Fin m) (j : Fin (n a)), Q a j ⟶ O a j)
      (z : ∀ (a : Fin m) (j : Fin (n a)), Z a j ⟶ W),
      (∀ a j, IsOpenImmersion (o a j)) ∧
      (∀ a j, IsClosedImmersion (c a j)) ∧
      (∀ a j, IsOpenImmersion (q a j)) ∧
      (∀ a j, IsClosedImmersion (z a j)) ∧
      (∀ a j, c a j ≫ o a j = s a j) ∧
      (∀ a j, QuasiCompact (o a j)) ∧
      (∀ a j, QuasiCompact (q a j)) ∧
      (∀ a j, Set.range ((q a j ≫ o a j).base) =
        Set.range (o a j).base \ Set.range (s a j).base) ∧
      (∀ a j, Set.range (z a j).base = (Set.range (o a j).base)ᶜ) ∧
      ∃ (N : ℕ) (V : Fin N → Scheme.{u}) (toW : ∀ v : Fin N, V v ⟶ W)
        (root : Fin N) (parent left right : Fin N → Fin N)
        (leftEdge : ∀ v : Fin N, V (left v) ⟶ V v)
        (rightEdge : ∀ v : Fin N, V (right v) ⟶ V v)
        (leaf : Fin N → Prop),
        (∃ e : V root ≅ W, e.hom = toW root) ∧ parent root = root ∧
        (∀ v, v ≠ root → (parent v).val < v.val) ∧
        (∀ v, ¬ leaf v → leftEdge v ≫ toW v = toW (left v)) ∧
        (∀ v, ¬ leaf v → rightEdge v ≫ toW v = toW (right v)) ∧
        (∀ v, CompactSpace (V v)) ∧
        (∀ v, QuasiSeparatedSpace (V v)) ∧
        (∀ v, IsImmersion (toW v)) ∧
        (∀ v, v ≠ root →
          left (parent v) = v ∨ right (parent v) = v) ∧
        (∀ v, leaf v ↔ ∀ w, w ≠ root → parent w ≠ v) ∧
        (∀ v, ¬ leaf v → left v ≠ right v ∧
          v.val < (left v).val ∧ v.val < (right v).val ∧
          parent (left v) = v ∧ parent (right v) = v ∧
          IsOpenImmersion (leftEdge v) ∧
          IsClosedImmersion (rightEdge v) ∧
          QuasiCompact (leftEdge v) ∧ QuasiCompact (rightEdge v) ∧
          Set.range (leftEdge v).base ∪ Set.range (rightEdge v).base = Set.univ ∧
          Disjoint (Set.range (leftEdge v).base)
            (Set.range (rightEdge v).base)) ∧
        (∀ v, ¬ leaf v →
          ∃ a : Fin m, ∃ j : Fin (n a),
            ((∃ h₁ : V (left v) = pullback (toW v) (o a j),
                ∃ h₂ : V (right v) = pullback (toW v) (z a j),
                leftEdge v = eqToHom h₁ ≫ pullback.fst (toW v) (o a j) ∧
                rightEdge v = eqToHom h₂ ≫ pullback.fst (toW v) (z a j)) ∨
             (∃ f : V v ⟶ O a j,
                f ≫ o a j = toW v ∧
                ∃ h₁ : V (left v) = pullback f (q a j),
                ∃ h₂ : V (right v) = pullback f (c a j),
                leftEdge v = eqToHom h₁ ≫ pullback.fst f (q a j) ∧
                rightEdge v = eqToHom h₂ ≫ pullback.fst f (c a j)))) ∧
        (∀ x : W, ∃ v : Fin N, leaf v ∧ Nonempty (V v) ∧
          x ∈ Set.range (toW v).base) ∧
        (∀ v w, leaf v → leaf w → v ≠ w →
          Disjoint (Set.range (toW v).base) (Set.range (toW w).base)) ∧
        (∀ v, leaf v → Nonempty (V v) →
          ∀ a : Fin m, ∃ j : Fin (n a), ∃ f : V v ⟶ S a j,
            f ≫ s a j = toW v) := by
  classical
  have _ := hdisjoint
  choose O Q Z o c q z ho hc hq hz hco hOo hQq hr hzr using
    fun (a : Fin m) (j : Fin (n a)) ↦
      exists_constructible_cut (W := W) (S := S a j) (s a j) (hc a j)
  refine ⟨O, Q, Z, o, c, q, z, ho, hc, hq, hz, hco, hOo, hQq, hr, hzr, ?_⟩
  exact exists_finite_refinement_tree m n S s O Q Z o c q z ho hc hq hz hco hcover hOo hQq hr hzr

end AlgebraicGeometry.Scheme

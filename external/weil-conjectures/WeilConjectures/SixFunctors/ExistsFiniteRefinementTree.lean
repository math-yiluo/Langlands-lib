/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.SixFunctors.SchemeRefinementTreeEncoding
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Constructing finite pullback refinement trees

Source: Stacks Project, Topology, Tag 09Y4, realized by complementary scheme pullbacks.
(auxiliary; not a blueprint node)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry.Scheme
/-- Finite binary pullback tree construction from already chosen open/closed refinements.
Source: Stacks Project, Topology, Tag 09Y4.
(auxiliary; not a blueprint node).
The proof iterates the complementary open/closed pullback split over the finitely many strata
and records the parent, child, compactness, disjointness, covering, and factorization invariants.
-/
theorem exists_finite_refinement_tree
    {W : Scheme.{u}} [CompactSpace W] [QuasiSeparatedSpace W]
    (m : ℕ) (n : Fin m → ℕ)
    (S : ∀ a : Fin m, Fin (n a) → Scheme.{u})
    (s : ∀ (a : Fin m) (j : Fin (n a)), S a j ⟶ W)
    (O Q Z : ∀ a : Fin m, Fin (n a) → Scheme.{u})
    (o : ∀ (a : Fin m) (j : Fin (n a)), O a j ⟶ W)
    (c : ∀ (a : Fin m) (j : Fin (n a)), S a j ⟶ O a j)
    (q : ∀ (a : Fin m) (j : Fin (n a)), Q a j ⟶ O a j)
    (z : ∀ (a : Fin m) (j : Fin (n a)), Z a j ⟶ W)
    (ho : ∀ a j, IsOpenImmersion (o a j))
    (hc : ∀ a j, IsClosedImmersion (c a j))
    (hq : ∀ a j, IsOpenImmersion (q a j))
    (hz : ∀ a j, IsClosedImmersion (z a j))
    (hco : ∀ a j, c a j ≫ o a j = s a j)
    (hcover : ∀ a : Fin m, (⋃ j : Fin (n a), Set.range (s a j).base) = Set.univ)
    (hoqc : ∀ a j, QuasiCompact (o a j))
    (hqqc : ∀ a j, QuasiCompact (q a j))
    (hqr : ∀ a j, Set.range (q a j ≫ o a j).base =
      Set.range (o a j).base \ Set.range (s a j).base)
    (hzr : ∀ a j, Set.range (z a j).base = (Set.range (o a j).base)ᶜ) :
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
  let allowed := fun (T : Scheme.{u}) (t : T ⟶ W) (L R : Scheme.{u})
      (l : L ⟶ T) (r : R ⟶ T) ↦
    ∃ a : Fin m, ∃ j : Fin (n a),
      ((∃ h₁ : L = pullback t (o a j), ∃ h₂ : R = pullback t (z a j),
          l = eqToHom h₁ ≫ pullback.fst t (o a j) ∧
          r = eqToHom h₂ ≫ pullback.fst t (z a j)) ∨
       (∃ f : T ⟶ O a j, f ≫ o a j = t ∧
          ∃ h₁ : L = pullback f (q a j), ∃ h₂ : R = pullback f (c a j),
          l = eqToHom h₁ ≫ pullback.fst f (q a j) ∧
          r = eqToHom h₂ ≫ pullback.fst f (c a j)))
  let resolved := fun (k : (a : Fin m) × Fin (n a)) (T : Scheme.{u}) (t : T ⟶ W) ↦
    Disjoint (Set.range t.base) (Set.range (s k.1 k.2).base) ∨
      ∃ f : T ⟶ S k.1 k.2, f ≫ s k.1 k.2 = t
  have resolved_comp (k : (a : Fin m) × Fin (n a))
      {T R : Scheme.{u}} (t : T ⟶ W) (r : R ⟶ T)
      (ht : resolved k T t) : resolved k R (r ≫ t) := by
    rcases ht with ht | ⟨f, hf⟩
    · left
      apply Set.disjoint_left.mpr
      rintro x ⟨y, rfl⟩ hx
      exact Set.disjoint_left.mp ht ⟨r y, rfl⟩ hx
    · exact Or.inr ⟨r ≫ f, by rw [Category.assoc, hf]⟩
  have step (k : (a : Fin m) × Fin (n a)) (T : Scheme.{u}) (t : T ⟶ W)
      (hcompact : CompactSpace T) (hqs : QuasiSeparatedSpace T) (himm : IsImmersion t) :
      ∃ tree : SchemeRefinementTree W allowed T t,
        tree.AllLeaves (fun R r ↦
          (∃ p : R ⟶ T, p ≫ t = r) ∧ resolved k R r) := by
    let :=  hcompact
    let :=  hqs
    let :=  himm
    let a := k.1
    let j := k.2
    have :=  ho a j
    have :=  hc a j
    have :=  hq a j
    have :=  hz a j
    have :=  hoqc a j
    have :=  hqqc a j
    let A := pullback t (o a j)
    let D := pullback t (z a j)
    let p : A ⟶ T := pullback.fst t (o a j)
    let d : D ⟶ T := pullback.fst t (z a j)
    let f : A ⟶ O a j := pullback.snd t (o a j)
    let B := pullback f (q a j)
    let C := pullback f (c a j)
    let b : B ⟶ A := pullback.fst f (q a j)
    let c' : C ⟶ A := pullback.fst f (c a j)
    have : CompactSpace A := inferInstance
    have : CompactSpace D := inferInstance
    have : QuasiSeparatedSpace A := quasiSeparatedSpace_of_quasiSeparated p
    have : QuasiSeparatedSpace D := quasiSeparatedSpace_of_quasiSeparated d
    have : CompactSpace B := inferInstance
    have : CompactSpace C := inferInstance
    have : QuasiSeparatedSpace B := quasiSeparatedSpace_of_quasiSeparated b
    have : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated c'
    have hfc : f ≫ o a j = p ≫ t := (pullback.condition (f := t) (g := o a j)).symm
    have hqr' : Set.range (q a j).base = (Set.range (c a j).base)ᶜ := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩ ⟨v, hv⟩
        have hy : o a j (q a j y) ∈ Set.range (q a j ≫ o a j).base := ⟨y, rfl⟩
        rw [hqr a j] at hy
        apply hy.2
        refine ⟨v, ?_⟩
        rw [← hco a j]
        exact congrArg (o a j) hv
      · intro hx
        have hxW : o a j x ∈ Set.range (q a j ≫ o a j).base := by
          rw [hqr a j]
          refine ⟨⟨x, rfl⟩, ?_⟩
          rintro ⟨v, hv⟩
          apply hx
          refine ⟨v, (o a j).isEmbedding.injective ?_⟩
          simpa only [← hco a j, Scheme.Hom.comp_apply] using hv
        obtain ⟨y, hy⟩ := hxW
        exact ⟨y, (o a j).isEmbedding.injective hy⟩
    have houter : Set.range p.base ∪ Set.range d.base = Set.univ ∧
        Disjoint (Set.range p.base) (Set.range d.base) := by
      change Set.range (pullback.fst t (o a j)).base ∪
          Set.range (pullback.fst t (z a j)).base = Set.univ ∧
        Disjoint (Set.range (pullback.fst t (o a j)).base)
          (Set.range (pullback.fst t (z a j)).base)
      simp only [Scheme.Pullback.range_fst, hzr, Set.preimage_compl]
      exact ⟨Set.union_compl_self _, disjoint_compl_right⟩
    have hinner : Set.range b.base ∪ Set.range c'.base = Set.univ ∧
        Disjoint (Set.range b.base) (Set.range c'.base) := by
      change Set.range (pullback.fst f (q a j)).base ∪
          Set.range (pullback.fst f (c a j)).base = Set.univ ∧
        Disjoint (Set.range (pullback.fst f (q a j)).base)
          (Set.range (pullback.fst f (c a j)).base)
      simp only [Scheme.Pullback.range_fst, hqr', Set.preimage_compl]
      exact ⟨Set.compl_union_self _, disjoint_compl_left⟩
    refine ⟨.node t p d inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance houter.1 houter.2
      ⟨a, j, Or.inl ⟨rfl, rfl, by simp [p], by simp [d]⟩⟩
      (.node (p ≫ t) b c' inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance hinner.1 hinner.2
        ⟨a, j, Or.inr ⟨f, hfc, rfl, rfl, by simp [b], by simp [c']⟩⟩
        (.tip _ inferInstance inferInstance inferInstance)
        (.tip _ inferInstance inferInstance inferInstance))
      (.tip _ inferInstance inferInstance inferInstance), ?_⟩
    change ((_ ∧ resolved k B (b ≫ p ≫ t)) ∧
      (_ ∧ resolved k C (c' ≫ p ≫ t))) ∧ (_ ∧ resolved k D (d ≫ t))
    refine ⟨⟨⟨⟨b ≫ p, (Category.assoc ..)⟩, ?_⟩,
      ⟨⟨c' ≫ p, (Category.assoc ..)⟩, ?_⟩⟩, ⟨⟨d, rfl⟩, ?_⟩⟩
    · left
      have hb : b ≫ p ≫ t = pullback.snd f (q a j) ≫ q a j ≫ o a j := by
        change pullback.fst f (q a j) ≫ p ≫ t = _
        rw [← hfc, ← Category.assoc, pullback.condition, Category.assoc]
      apply Set.disjoint_left.mpr
      rintro x ⟨y, rfl⟩ hx
      have hy : (b ≫ p ≫ t) y ∈ Set.range (q a j ≫ o a j).base := by
        rw [hb]
        exact ⟨pullback.snd f (q a j) y, rfl⟩
      rw [hqr a j] at hy
      exact hy.2 hx
    · right
      refine ⟨pullback.snd f (c a j), ?_⟩
      change pullback.snd f (c a j) ≫ s a j = c' ≫ p ≫ t
      rw [← hco a j, ← Category.assoc, ← pullback.condition, Category.assoc, hfc]
    · left
      have hd : Set.range (d ≫ t).base =
          Set.range t.base ∩ (Set.range (o a j).base)ᶜ := by
        change Set.range (pullback.fst t (z a j) ≫ t).base = _
        rw [Scheme.Pullback.range_fst_comp, hzr a j]
      apply Set.disjoint_left.mpr
      intro x hx hxS
      have hxO := (hd ▸ hx).2
      obtain ⟨v, rfl⟩ := hxS
      apply hxO
      refine ⟨c a j v, ?_⟩
      exact congrArg (fun g : S a j ⟶ W ↦ g v) (hco a j)
  have build (K : Finset ((a : Fin m) × Fin (n a))) :
      ∃ tree : SchemeRefinementTree W allowed W (𝟙 W),
        tree.AllLeaves (fun T t ↦ ∀ k ∈ K, resolved k T t) := by
    induction K using Finset.induction_on with
    | empty =>
      exact ⟨.tip _ inferInstance inferInstance inferInstance, by simp [
        SchemeRefinementTree.AllLeaves]⟩
    | @insert k K hk ih =>
      obtain ⟨tree, htree⟩ := ih
      choose replacement hreplacement using step k
      refine ⟨tree.bind replacement, SchemeRefinementTree.allLeaves_bind replacement ?_ tree
        htree⟩
      intro T t hcompact hqs himm hprocessed
      apply SchemeRefinementTree.allLeaves_mono _ (replacement T t hcompact hqs himm)
        (hreplacement T t hcompact hqs himm)
      rintro R r ⟨⟨p, hp⟩, hnew⟩ i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hnew
      · rw [← hp]
        exact resolved_comp i t p (hprocessed i hi)
  obtain ⟨tree, htree⟩ := build Finset.univ
  have hleaf : tree.AllLeaves (fun T t ↦ Nonempty T →
      ∀ a : Fin m, ∃ j : Fin (n a), ∃ f : T ⟶ S a j, f ≫ s a j = t) := by
    apply SchemeRefinementTree.allLeaves_mono _ tree htree
    intro T t ht hT a
    obtain ⟨x⟩ := hT
    have hx : t x ∈ ⋃ j : Fin (n a), Set.range (s a j).base := by
      rw [hcover a]
      exact Set.mem_univ _
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    rcases ht ⟨a, j⟩ (Finset.mem_univ _) with havoid | hfactor
    · exact False.elim (Set.disjoint_left.mp havoid ⟨x, rfl⟩ hj)
    · exact ⟨j, hfactor⟩
  exact tree.exists_fin_encoding hleaf
end AlgebraicGeometry.Scheme

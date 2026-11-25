/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.SchemeRefinementTree
import Mathlib.Data.Fintype.Sort

/-!
# Numbering the vertices of a finite scheme refinement tree

Source: the finite binary tree underlying Stacks Project, Topology, Tag 09Y4.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.SchemeRefinementTree

private structure Layout {W : Scheme.{u}}
    (allowed : ∀ (T : Scheme.{u}), (T ⟶ W) → ∀ (L R : Scheme.{u}),
      (L ⟶ T) → (R ⟶ T) → Prop)
    (P : ∀ (T : Scheme.{u}), (T ⟶ W) → Prop) (T : Scheme.{u}) (t : T ⟶ W) where
  α : Type
  finite : Fintype α
  order : LinearOrder α
  V : α → Scheme.{u}
  toW : ∀ v, V v ⟶ W
  root : α
  parent : α → α
  left : α → α
  right : α → α
  leftEdge : ∀ v, V (left v) ⟶ V v
  rightEdge : ∀ v, V (right v) ⟶ V v
  leaf : α → Prop
  root_scheme : V root = T
  root_map : eqToHom root_scheme ≫ t = toW root
  root_min : ∀ v, @LE.le α order.toLE root v
  parent_root : parent root = root
  parent_lt : ∀ v, v ≠ root → @LT.lt α order.toLT (parent v) v
  left_map : ∀ v, ¬ leaf v → leftEdge v ≫ toW v = toW (left v)
  right_map : ∀ v, ¬ leaf v → rightEdge v ≫ toW v = toW (right v)
  compact : ∀ v, CompactSpace (V v)
  qs : ∀ v, QuasiSeparatedSpace (V v)
  immersion : ∀ v, IsImmersion (toW v)
  child : ∀ v, v ≠ root → left (parent v) = v ∨ right (parent v) = v
  leaf_self : ∀ v, leaf v → left v = v ∧ right v = v
  split : ∀ v, ¬ leaf v → left v ≠ right v ∧
    @LT.lt α order.toLT v (left v) ∧ @LT.lt α order.toLT v (right v) ∧
    parent (left v) = v ∧ parent (right v) = v ∧
    IsOpenImmersion (leftEdge v) ∧ IsClosedImmersion (rightEdge v) ∧
    QuasiCompact (leftEdge v) ∧ QuasiCompact (rightEdge v) ∧
    Set.range (leftEdge v).base ∪ Set.range (rightEdge v).base = Set.univ ∧
    Disjoint (Set.range (leftEdge v).base) (Set.range (rightEdge v).base)
  admissible : ∀ v, ¬ leaf v →
    allowed (V v) (toW v) (V (left v)) (V (right v)) (leftEdge v) (rightEdge v)
  cover : ∀ x : T, ∃ v, leaf v ∧ Nonempty (V v) ∧ t x ∈ Set.range (toW v).base
  disjoint : ∀ v w, leaf v → leaf w → v ≠ w →
    Disjoint (Set.range (toW v).base) (Set.range (toW w).base)
  subset : ∀ v, Set.range (toW v).base ⊆ Set.range t.base
  predicate : ∀ v, leaf v → P (V v) (toW v)

attribute [instance] Layout.finite Layout.order

private theorem nonempty_layout
    {W : Scheme.{u}}
    {allowed : ∀ (T : Scheme.{u}), (T ⟶ W) → ∀ (L R : Scheme.{u}),
      (L ⟶ T) → (R ⟶ T) → Prop}
    {P : ∀ (T : Scheme.{u}), (T ⟶ W) → Prop}
    {T : Scheme.{u}} {t : T ⟶ W}
    (tree : SchemeRefinementTree W allowed T t) (htree : AllLeaves P tree) :
    Nonempty (Layout allowed P T t) := by
  classical
  induction tree with
  | tip t hcompact hqs himm =>
    exact ⟨{
      α := Unit
      finite := inferInstance
      order := inferInstance
      V := fun _ ↦ _
      toW := fun _ ↦ t
      root := ()
      parent := id
      left := id
      right := id
      leftEdge := fun _ ↦ 𝟙 _
      rightEdge := fun _ ↦ 𝟙 _
      leaf := fun _ ↦ True
      root_scheme := rfl
      root_map := by simp
      root_min := by simp
      parent_root := rfl
      parent_lt := by simp
      left_map := by simp
      right_map := by simp
      compact := fun _ ↦ hcompact
      qs := fun _ ↦ hqs
      immersion := fun _ ↦ himm
      child := by simp
      leaf_self := by simp
      split := by simp
      admissible := by simp
      cover := fun x ↦ ⟨(), trivial, ⟨x⟩, ⟨x, rfl⟩⟩
      disjoint := by simp
      subset := fun _ ↦ Set.Subset.rfl
      predicate := fun _ _ ↦ htree }⟩
  | @node T L R t l r hcompact hqs himm hl hr hlqc hrqc hcover hd ha tl tr ihl ihr =>
    obtain ⟨A⟩ := ihl htree.1
    obtain ⟨B⟩ := ihr htree.2
    rcases A with ⟨α, fα, oα, Va, ta, rootA, pa, la, ra, ea, fa, leafa,
      hVa, hta, hminA, hpa, hpltA, hla, hra, hca, hqa, hia, hchildA, hselfA,
      hsplitA, hadmA, hcoverA, hdisA, hsubA, hpredA⟩
    rcases B with ⟨β, fβ, oβ, Vb, tb, rootB, pb, lb, rb, eb, fb, leafb,
      hVb, htb, hminB, hpb, hpltB, hlb, hrb, hcb, hqb, hib, hchildB, hselfB,
      hsplitB, hadmB, hcoverB, hdisB, hsubB, hpredB⟩
    cases hVa
    cases hVb
    simp only [eqToHom_refl, Category.id_comp] at hta htb
    let := fα
    let := oα
    let := fβ
    let := oβ
    let γ := Unit ⊕ₗ (α ⊕ₗ β)
    let root : γ := Sum.inl ()
    let ia : α → γ := fun v ↦ Sum.inr (Sum.inl v)
    let ib : β → γ := fun v ↦ Sum.inr (Sum.inr v)
    let V : γ → Scheme.{u} := Sum.elim (fun _ ↦ T) (Sum.elim Va Vb)
    let toW : ∀ v, V v ⟶ W := fun v ↦ match v with
      | .inl _ => t
      | .inr (.inl v) => ta v
      | .inr (.inr v) => tb v
    let parent : γ → γ := Sum.elim (fun _ ↦ root) (Sum.elim
      (fun v ↦ if v = rootA then root else ia (pa v))
      (fun v ↦ if v = rootB then root else ib (pb v)))
    let left : γ → γ := Sum.elim (fun _ ↦ ia rootA)
      (Sum.elim (fun v ↦ ia (la v)) (fun v ↦ ib (lb v)))
    let right : γ → γ := Sum.elim (fun _ ↦ ib rootB)
      (Sum.elim (fun v ↦ ia (ra v)) (fun v ↦ ib (rb v)))
    let leftEdge : ∀ v, V (left v) ⟶ V v := fun v ↦ match v with
      | .inl _ => l
      | .inr (.inl v) => ea v
      | .inr (.inr v) => eb v
    let rightEdge : ∀ v, V (right v) ⟶ V v := fun v ↦ match v with
      | .inl _ => r
      | .inr (.inl v) => fa v
      | .inr (.inr v) => fb v
    let leaf : γ → Prop := Sum.elim (fun _ ↦ False) (Sum.elim leafa leafb)
    have hcross : Disjoint (Set.range (l ≫ t).base) (Set.range (r ≫ t).base) := by
      apply Set.disjoint_left.mpr
      rintro x ⟨a, ha'⟩ ⟨b, hb'⟩
      have : IsImmersion t := himm
      have hab : l a = r b := t.isEmbedding.injective (ha'.trans hb'.symm)
      exact Set.disjoint_left.mp hd ⟨a, rfl⟩ ⟨b, hab.symm⟩
    refine ⟨{
      α := γ
      finite := inferInstance
      order := inferInstance
      V := V
      toW := toW
      root := root
      parent := parent
      left := left
      right := right
      leftEdge := leftEdge
      rightEdge := rightEdge
      leaf := leaf
      root_scheme := rfl
      root_map := by simp [root, toW]
      root_min := ?_
      parent_root := rfl
      parent_lt := ?_
      left_map := ?_
      right_map := ?_
      compact := ?_
      qs := ?_
      immersion := ?_
      child := ?_
      leaf_self := ?_
      split := ?_
      admissible := ?_
      cover := ?_
      disjoint := ?_
      subset := ?_
      predicate := ?_ }⟩
    · rintro (⟨⟩ | v)
      · exact le_rfl
      · exact Sum.Lex.sep _ _
    · rintro (⟨⟩ | (v | v)) hv
      · exact (hv rfl).elim
      · by_cases h : v = rootA
        · subst v
          simp only [parent, Sum.elim_inr, Sum.elim_inl]
          exact Sum.Lex.sep _ _
        · simp only [parent, Sum.elim_inr, Sum.elim_inl, ite_eq_right h]
          exact Sum.Lex.inr (Sum.Lex.inl (hpltA v h))
      · by_cases h : v = rootB
        · subst v
          simp only [parent, Sum.elim_inr]
          exact Sum.Lex.sep _ _
        · simp only [parent, Sum.elim_inr, ite_eq_right h]
          exact Sum.Lex.inr (Sum.Lex.inr (hpltB v h))
    · rintro (⟨⟩ | (v | v)) hv
      · exact hta
      · exact hla v hv
      · exact hlb v hv
    · rintro (⟨⟩ | (v | v)) hv
      · exact htb
      · exact hra v hv
      · exact hrb v hv
    · rintro (⟨⟩ | (v | v))
      · exact hcompact
      · exact hca v
      · exact hcb v
    · rintro (⟨⟩ | (v | v))
      · exact hqs
      · exact hqa v
      · exact hqb v
    · rintro (⟨⟩ | (v | v))
      · exact himm
      · exact hia v
      · exact hib v
    · rintro (⟨⟩ | (v | v)) hv
      · exact (hv rfl).elim
      · by_cases h : v = rootA
        · subst v
          exact Or.inl (by simp [parent, left, root, ia])
        · simpa [parent, h, left, right, ia] using
            (hchildA v h).imp (congrArg ia) (congrArg ia)
      · by_cases h : v = rootB
        · subst v
          exact Or.inr (by simp [parent, right, root, ib])
        · simpa [parent, h, left, right, ib] using
            (hchildB v h).imp (congrArg ib) (congrArg ib)
    · rintro (⟨⟩ | (v | v)) hv
      · exact hv.elim
      · exact ⟨congrArg ia (hselfA v hv).1, congrArg ia (hselfA v hv).2⟩
      · exact ⟨congrArg ib (hselfB v hv).1, congrArg ib (hselfB v hv).2⟩
    · rintro (⟨⟩ | (v | v)) hv
      · exact ⟨by
          change Sum.inr (Sum.inl rootA) ≠ Sum.inr (Sum.inr rootB)
          intro h
          have inj : Function.Injective (fun x : α ⊕ₗ β ↦ (Sum.inr x : γ)) :=
            Sum.inr_injective
          exact Sum.inl_ne_inr (inj h), Sum.Lex.sep _ _, Sum.Lex.sep _ _,
          by simp [parent, left, ia, root], by simp [parent, right, ib, root],
          hl, hr, hlqc, hrqc, hcover, hd⟩
      · obtain ⟨hne, hltl, hltr, hpl, hpr, hopen, hclosed, hqc1, hqc2, hcov, hdis⟩ :=
          hsplitA v hv
        have hnl : la v ≠ rootA := ne_of_gt (lt_of_le_of_lt (hminA v) hltl)
        have hnr : ra v ≠ rootA := ne_of_gt (lt_of_le_of_lt (hminA v) hltr)
        exact ⟨by exact fun h ↦ hne (Sum.inl.inj (Sum.inr.inj h)),
          Sum.Lex.inr (Sum.Lex.inl hltl), Sum.Lex.inr (Sum.Lex.inl hltr),
          by simp [parent, left, ia, hnl, hpl], by simp [parent, right, ia, hnr, hpr],
          hopen, hclosed, hqc1, hqc2, hcov, hdis⟩
      · obtain ⟨hne, hltl, hltr, hpl, hpr, hopen, hclosed, hqc1, hqc2, hcov, hdis⟩ :=
          hsplitB v hv
        have hnl : lb v ≠ rootB := ne_of_gt (lt_of_le_of_lt (hminB v) hltl)
        have hnr : rb v ≠ rootB := ne_of_gt (lt_of_le_of_lt (hminB v) hltr)
        exact ⟨by exact fun h ↦ hne (Sum.inr.inj (Sum.inr.inj h)),
          Sum.Lex.inr (Sum.Lex.inr hltl), Sum.Lex.inr (Sum.Lex.inr hltr),
          by simp [parent, left, ib, hnl, hpl], by simp [parent, right, ib, hnr, hpr],
          hopen, hclosed, hqc1, hqc2, hcov, hdis⟩
    · rintro (⟨⟩ | (v | v)) hv
      · exact ha
      · exact hadmA v hv
      · exact hadmB v hv
    · intro x
      have hx : x ∈ Set.range l.base ∪ Set.range r.base := hcover.symm ▸ Set.mem_univ x
      rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · obtain ⟨v, hv, hne, hm⟩ := hcoverA y
        exact ⟨ia v, hv, hne, hm⟩
      · obtain ⟨v, hv, hne, hm⟩ := hcoverB y
        exact ⟨ib v, hv, hne, hm⟩
    · rintro (⟨⟩ | (v | v)) (⟨⟩ | (w | w)) hv hw hn
      all_goals try { change False at hv; contradiction }
      all_goals try { change False at hw; contradiction }
      · exact hdisA v w hv hw (fun h ↦ hn (congrArg ia h))
      · exact hcross.mono (hsubA v) (hsubB w)
      · exact hcross.symm.mono (hsubB v) (hsubA w)
      · exact hdisB v w hv hw (fun h ↦ hn (congrArg ib h))
    · rintro (⟨⟩ | (v | v)) x hx
      · exact hx
      · obtain ⟨y, hy⟩ := hsubA v hx
        exact ⟨l y, hy⟩
      · obtain ⟨y, hy⟩ := hsubB v hx
        exact ⟨r y, hy⟩
    · rintro (⟨⟩ | (v | v)) hv
      · exact hv.elim
      · exact hpredA v hv
      · exact hpredB v hv

private theorem Layout.leaf_iff
    {W : Scheme.{u}}
    {allowed : ∀ (T : Scheme.{u}), (T ⟶ W) → ∀ (L R : Scheme.{u}),
      (L ⟶ T) → (R ⟶ T) → Prop}
    {P : ∀ (T : Scheme.{u}), (T ⟶ W) → Prop}
    {T : Scheme.{u}} {t : T ⟶ W} (A : Layout allowed P T t) (v : A.α) :
    A.leaf v ↔ ∀ w, w ≠ A.root → A.parent w ≠ v := by
  constructor
  · intro hv w hw hp
    have hc := A.child w hw
    rw [hp] at hc
    have hvw : v = w := by
      rcases hc with hc | hc
      · exact (A.leaf_self v hv).1.symm.trans hc
      · exact (A.leaf_self v hv).2.symm.trans hc
    have hh := A.parent_lt w hw
    rw [hp, hvw] at hh
    exact lt_irrefl _ hh
  · intro hv
    by_contra hn
    have hs := A.split v hn
    have hchild : A.left v ≠ A.root :=
      ne_of_gt (lt_of_le_of_lt (A.root_min v) hs.2.1)
    exact hv (A.left v) hchild hs.2.2.2.1

private theorem transport_map {ι : Type} (V : ι → Scheme.{u})
    {W : Scheme.{u}} (t : ∀ v, V v ⟶ W) {a b : ι} (h : a = b) :
    eqToHom (congrArg V h) ≫ t b = t a := by
  subst b
  simp

private theorem transport_split {ι : Type} (V : ι → Scheme.{u})
    {T : Scheme.{u}} {a b c d : ι} (h : a = b) (k : c = d)
    (l : V b ⟶ T) (r : V d ⟶ T)
    (hs : IsOpenImmersion l ∧ IsClosedImmersion r ∧ QuasiCompact l ∧
      QuasiCompact r ∧ Set.range l.base ∪ Set.range r.base = Set.univ ∧
      Disjoint (Set.range l.base) (Set.range r.base)) :
    IsOpenImmersion (eqToHom (congrArg V h) ≫ l) ∧
    IsClosedImmersion (eqToHom (congrArg V k) ≫ r) ∧
    QuasiCompact (eqToHom (congrArg V h) ≫ l) ∧
    QuasiCompact (eqToHom (congrArg V k) ≫ r) ∧
    Set.range (eqToHom (congrArg V h) ≫ l).base ∪
      Set.range (eqToHom (congrArg V k) ≫ r).base = Set.univ ∧
    Disjoint (Set.range (eqToHom (congrArg V h) ≫ l).base)
      (Set.range (eqToHom (congrArg V k) ≫ r).base) := by
  subst b d
  simpa using hs

private theorem transport_allowed {ι : Type} (V : ι → Scheme.{u})
    {W T : Scheme.{u}} (t : T ⟶ W)
    (allowed : ∀ (T : Scheme.{u}), (T ⟶ W) → ∀ (L R : Scheme.{u}),
      (L ⟶ T) → (R ⟶ T) → Prop)
    {a b c d : ι} (h : a = b) (k : c = d) (l : V b ⟶ T) (r : V d ⟶ T)
    (ha : allowed T t (V b) (V d) l r) :
    allowed T t (V a) (V c) (eqToHom (congrArg V h) ≫ l)
      (eqToHom (congrArg V k) ≫ r) := by
  subst b d
  simpa using ha

private theorem transport_root {ι : Type} (V : ι → Scheme.{u})
    {W : Scheme.{u}} (t : ∀ v, V v ⟶ W) {a b : ι} (h : a = b)
    (hroot : V b = W) (ht : eqToHom hroot = t b) :
    ∃ e : V a ≅ W, e.hom = t a := by
  subst b
  exact ⟨eqToIso hroot, ht⟩

private theorem transport_mem {ι : Type} (V : ι → Scheme.{u})
    {W : Scheme.{u}} (t : ∀ v, V v ⟶ W) {a b : ι} (h : a = b) (x : W)
    (hx : x ∈ Set.range (t b).base) : x ∈ Set.range (t a).base := by
  subst b
  exact hx

/-- A recursive finite splitting tree can be numbered in parent-before-child order.

Source: Stacks Project, Topology, Tag 09Y4, finite refinement tree bookkeeping.
(auxiliary; not a blueprint node).

Proof: Recursively count one vertex for a tip and one plus the two child counts for a node.
Use preorder numbering: the root is zero, left subtree labels follow it, and right subtree
labels follow the entire left subtree. Transport schemes, structural maps, and branch maps
along these finite-index injections. At a tip choose both children and its parent to be
itself and the two unused edges to be identities. At a node set its two children to the
roots of the numbered subtrees. The parent of every other vertex is its subtree parent,
except at the two child roots where it is the new root. Index inequalities follow from
these offsets, and the leaf characterization follows by induction on the tree. The
root isomorphism is the identity. Vertex and branch properties and admissibility are
stored in the recursive constructors and transport to these labels. For covering, lift
a point into one of the complementary child images and apply that subtree's covering
induction hypothesis. Leaves in distinct subtrees have disjoint images by the disjoint
child ranges; within one subtree use its disjointness and injectivity of the child
immersion. Structural maps commute by associativity. Finally `AllLeaves P` transfers
the predicate at each tip to its numerical label. This also handles a single tip and
empty schemes without making a nonemptiness assumption.
-/
theorem exists_fin_encoding
    {W : Scheme.{u}}
    {allowed : ∀ (T : Scheme.{u}), (T ⟶ W) → ∀ (L R : Scheme.{u}),
      (L ⟶ T) → (R ⟶ T) → Prop}
    {P : ∀ (T : Scheme.{u}), (T ⟶ W) → Prop}
    (tree : SchemeRefinementTree W allowed W (𝟙 W))
    (htree : AllLeaves P tree) :
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
          allowed (V v) (toW v) (V (left v)) (V (right v))
            (leftEdge v) (rightEdge v)) ∧
        (∀ x : W, ∃ v : Fin N, leaf v ∧ Nonempty (V v) ∧
          x ∈ Set.range (toW v).base) ∧
        (∀ v w, leaf v → leaf w → v ≠ w →
          Disjoint (Set.range (toW v).base) (Set.range (toW w).base)) ∧
        (∀ v, leaf v → P (V v) (toW v)) := by
  classical
  obtain ⟨A⟩ := nonempty_layout tree htree
  let e : Fin (Fintype.card A.α) ≃o A.α := Fintype.orderIsoFinOfCardEq A.α rfl
  let V : Fin (Fintype.card A.α) → Scheme.{u} := fun v ↦ A.V (e v)
  let toW : ∀ v, V v ⟶ W := fun v ↦ A.toW (e v)
  let root := e.symm A.root
  let parent := fun v ↦ e.symm (A.parent (e v))
  let left := fun v ↦ e.symm (A.left (e v))
  let right := fun v ↦ e.symm (A.right (e v))
  let leftEdge : ∀ v, V (left v) ⟶ V v := fun v ↦
    eqToHom (congrArg A.V (e.apply_symm_apply _)) ≫ A.leftEdge (e v)
  let rightEdge : ∀ v, V (right v) ⟶ V v := fun v ↦
    eqToHom (congrArg A.V (e.apply_symm_apply _)) ≫ A.rightEdge (e v)
  let leaf := fun v ↦ A.leaf (e v)
  have hne (v) (hv : v ≠ root) : e v ≠ A.root := by
    intro h
    apply hv
    simpa [root] using congrArg e.symm h
  refine ⟨Fintype.card A.α, V, toW, root, parent, left, right, leftEdge, rightEdge,
    leaf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact transport_root A.V A.toW (e.apply_symm_apply _) A.root_scheme
      (by simpa using A.root_map)
  · simp [parent, root, A.parent_root]
  · intro v hv
    simpa [parent] using e.symm.strictMono (A.parent_lt (e v) (hne v hv))
  · intro v hv
    dsimp [leftEdge, toW, left, V]
    rw [Category.assoc, A.left_map (e v) hv]
    exact transport_map A.V A.toW (e.apply_symm_apply _)
  · intro v hv
    dsimp [rightEdge, toW, right, V]
    rw [Category.assoc, A.right_map (e v) hv]
    exact transport_map A.V A.toW (e.apply_symm_apply _)
  · exact fun v ↦ A.compact (e v)
  · exact fun v ↦ A.qs (e v)
  · exact fun v ↦ A.immersion (e v)
  · intro v hv
    rcases A.child (e v) (hne v hv) with h | h
    · left
      simpa [left, parent] using congrArg e.symm h
    · right
      simpa [right, parent] using congrArg e.symm h
  · intro v
    constructor
    · intro hv w hw hp
      apply (A.leaf_iff (e v)).mp hv (e w) (hne w hw)
      simpa [parent] using congrArg e hp
    · intro hv
      apply (A.leaf_iff (e v)).mpr
      intro w hw hp
      apply hv (e.symm w)
      · intro h
        apply hw
        simpa [root] using congrArg e h
      · simp [parent, hp]
  · intro v hv
    obtain ⟨hneq, hltl, hltr, hpl, hpr, hopen, hclosed, hqc1, hqc2, hcov, hdis⟩ :=
      A.split (e v) hv
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      apply hneq
      simpa [left, right] using congrArg e h
    · simpa [left] using e.symm.strictMono hltl
    · simpa [right] using e.symm.strictMono hltr
    · simp [parent, left, hpl]
    · simp [parent, right, hpr]
    · exact transport_split A.V (e.apply_symm_apply _) (e.apply_symm_apply _)
        (A.leftEdge (e v)) (A.rightEdge (e v))
        ⟨hopen, hclosed, hqc1, hqc2, hcov, hdis⟩
  · intro v hv
    exact transport_allowed A.V (A.toW (e v)) allowed
      (e.apply_symm_apply _) (e.apply_symm_apply _)
      (A.leftEdge (e v)) (A.rightEdge (e v)) (A.admissible (e v) hv)
  · intro x
    obtain ⟨v, hv, hnonempty, hm⟩ := A.cover x
    refine ⟨e.symm v, by simpa [leaf] using hv, by simpa [V] using hnonempty, ?_⟩
    exact transport_mem A.V A.toW (e.apply_symm_apply _) x (by simpa using hm)
  · intro v w hv hw hn
    exact A.disjoint (e v) (e w) hv hw (fun h ↦ hn (e.injective h))
  · exact fun v hv ↦ A.predicate (e v) hv

end AlgebraicGeometry.Scheme.SchemeRefinementTree

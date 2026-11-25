/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Recursive scheme refinement trees

The data of a finite open/closed splitting tree, before assigning numerical vertex labels.
Source: the binary refinement construction in Stacks Project, Topology, Tag 09Y4.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A finite splitting tree with prescribed admissible branches. The scheme at every vertex
is qcqs and immersed in the ambient scheme; each split is complementary and quasi-compact.
Source: Stacks Project, Topology, Tag 09Y4.
(auxiliary; not a blueprint node) -/
inductive SchemeRefinementTree (W : Scheme.{u})
    (allowed : ∀ (T : Scheme.{u}), (T ⟶ W) → ∀ (L R : Scheme.{u}),
      (L ⟶ T) → (R ⟶ T) → Prop) :
    ∀ (T : Scheme.{u}), (T ⟶ W) → Type (u + 1) where
  | tip {T : Scheme.{u}} (t : T ⟶ W) (hcompact : CompactSpace T)
      (hqs : QuasiSeparatedSpace T) (himm : IsImmersion t) :
      SchemeRefinementTree W allowed T t
  | node {T L R : Scheme.{u}} (t : T ⟶ W) (l : L ⟶ T) (r : R ⟶ T)
      (hcompact : CompactSpace T) (hqs : QuasiSeparatedSpace T) (himm : IsImmersion t)
      (hl : IsOpenImmersion l) (hr : IsClosedImmersion r)
      (hlqc : QuasiCompact l) (hrqc : QuasiCompact r)
      (hcover : Set.range l.base ∪ Set.range r.base = Set.univ)
      (hdisjoint : Disjoint (Set.range l.base) (Set.range r.base))
      (hallowed : allowed T t L R l r)
      (left : SchemeRefinementTree W allowed L (l ≫ t))
      (right : SchemeRefinementTree W allowed R (r ≫ t)) :
      SchemeRefinementTree W allowed T t

namespace SchemeRefinementTree

variable {W : Scheme.{u}}
  {allowed : ∀ (T : Scheme.{u}), (T ⟶ W) → ∀ (L R : Scheme.{u}),
    (L ⟶ T) → (R ⟶ T) → Prop}

/-- A predicate holds at every leaf of a recursive refinement tree. -/
def AllLeaves (P : ∀ (T : Scheme.{u}), (T ⟶ W) → Prop) :
    ∀ {T : Scheme.{u}} {t : T ⟶ W}, SchemeRefinementTree W allowed T t → Prop
  | _, _, .tip t _ _ _ => P _ t
  | _, _, .node _ _ _ _ _ _ _ _ _ _ _ _ _ left right =>
      AllLeaves P left ∧ AllLeaves P right

/-- Replace every leaf by a prescribed refinement. -/
def bind (replacement : ∀ (T : Scheme.{u}) (t : T ⟶ W),
    CompactSpace T → QuasiSeparatedSpace T → IsImmersion t →
      SchemeRefinementTree W allowed T t) :
    ∀ {T : Scheme.{u}} {t : T ⟶ W}, SchemeRefinementTree W allowed T t →
      SchemeRefinementTree W allowed T t
  | _, _, .tip t hcompact hqs himm => replacement _ t hcompact hqs himm
  | _, _, .node t l r hcompact hqs himm hl hr hlqc hrqc hcover hdisjoint ha left right =>
      .node t l r hcompact hqs himm hl hr hlqc hrqc hcover hdisjoint ha
        (bind replacement left) (bind replacement right)

theorem allLeaves_bind {P Q : ∀ (T : Scheme.{u}), (T ⟶ W) → Prop}
    (replacement : ∀ (T : Scheme.{u}) (t : T ⟶ W),
      CompactSpace T → QuasiSeparatedSpace T → IsImmersion t →
        SchemeRefinementTree W allowed T t)
    (h : ∀ T t hcompact hqs himm, P T t →
      AllLeaves Q (replacement T t hcompact hqs himm))
    {T : Scheme.{u}} {t : T ⟶ W} (tree : SchemeRefinementTree W allowed T t)
    (htree : AllLeaves P tree) : AllLeaves Q (bind replacement tree) := by
  induction tree with
  | tip t hcompact hqs himm => exact h _ t hcompact hqs himm htree
  | node t l r hcompact hqs himm hl hr hlqc hrqc hcover hd ha left right ihl ihr =>
    exact ⟨ihl htree.1, ihr htree.2⟩

theorem allLeaves_mono {P Q : ∀ (T : Scheme.{u}), (T ⟶ W) → Prop}
    (h : ∀ T t, P T t → Q T t)
    {T : Scheme.{u}} {t : T ⟶ W} (tree : SchemeRefinementTree W allowed T t)
    (htree : AllLeaves P tree) : AllLeaves Q tree := by
  induction tree with
  | tip t _ _ _ => exact h _ t htree
  | node t l r hcompact hqs himm hl hr hlqc hrqc hcover hd ha left right ihl ihr =>
    exact ⟨ihl htree.1, ihr htree.2⟩

end SchemeRefinementTree
end AlgebraicGeometry.Scheme

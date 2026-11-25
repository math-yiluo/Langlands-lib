/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sets.Opens
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Gluing on cofinal coverings of a basis

Source: Stacks Project, Sheaves on Spaces, Tags 009J, 009K and 009L
(blueprint: lem-weil-pbc-basis-sheaf-cofinal-coverings).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory Opposite TopologicalSpace

namespace TopologicalSpace.Opens

/-- Source: Stacks Project, Tags 009K and 009L.
(blueprint: lem-weil-pbc-basis-sheaf-cofinal-coverings)
A presheaf of sets on an intersection-closed basis glues on all coverings if it glues on
cofinally many coverings. Families are indexed by arbitrary types, including empty types.
The predicate `C U I V` selects the cofinal coverings; it is only used when `V` covers `U`.
The local notation `meet` is intersection in the basis, and `res` is the functor's restriction.

Proof:
1. Refine an arbitrary covering `V` of `U` by a selected covering `W`, with refinement map
   `α`. All pairwise intersections belong to the basis by the intersection hypothesis.
2. Sections agreeing on `V` agree on `W` by functoriality. Uniqueness of gluing on `W`
   therefore gives uniqueness on every covering of every basis member.
3. Given a compatible family `s`, restrict `s (α j)` to `W j`. The resulting family is
   compatible on intersections by transitivity of restrictions and compatibility of `s`.
   Gluing on the selected covering gives a section `t` over `U`.
4. For each `i`, the intersections of `V i` with all `W j` cover `V i`. The restrictions
   of `t` and `s i` agree there by compatibility and functoriality. Apply the uniqueness
   from step 2 over `V i` to obtain that `t` restricts to `s i`.
5. Step 4 gives existence and step 2 gives uniqueness on the original covering.
For the empty covering of the empty basis member, a refinement has empty index type,
and the selected gluing condition forces the set of sections to have exactly one element.
No subsidiary nodes are used: all five steps of the blueprint proof are elementary. -/
theorem gluing_of_cofinal_coverings
    {X : Type u} [TopologicalSpace X] (B : Set (Opens X))
    (hB : IsBasis B)
    (hcap : ∀ U V : B, U.val ⊓ V.val ∈ B)
    (F : Bᵒᵖ ⥤ Type v)
    (C : ∀ U : B, ∀ I : Type w, (I → {V : B // V ≤ U}) → Prop) :
    let meet : B → B → B := fun U V ↦ ⟨U.val ⊓ V.val, hcap U V⟩
    let res : ∀ U V : B, V ≤ U → F.obj (op U) → F.obj (op V) :=
      fun _ _ h ↦ F.map (homOfLE h).op
    (∀ (U : B) (I : Type w) (V : I → {W : B // W ≤ U}),
      (⨆ i, (V i).val.val) = U.val →
      ∃ (J : Type w) (W : J → {Z : B // Z ≤ U}),
        (⨆ j, (W j).val.val) = U.val ∧ C U J W ∧
        ∃ α : J → I, ∀ j, (W j).val ≤ (V (α j)).val) →
    (∀ (U : B) (I : Type w) (V : I → {W : B // W ≤ U}),
      (⨆ i, (V i).val.val) = U.val → C U I V →
      ∀ s : ∀ i, F.obj (op (V i).val),
        (∀ i j,
          res (V i).val (meet (V i).val (V j).val)
            (inf_le_left (a := (V i).val.val) (b := (V j).val.val)) (s i) =
          res (V j).val (meet (V i).val (V j).val)
            (inf_le_right (a := (V i).val.val) (b := (V j).val.val)) (s j)) →
        ∃! t : F.obj (op U), ∀ i, res U (V i).val (V i).property t = s i) →
    ∀ (U : B) (I : Type w) (V : I → {W : B // W ≤ U}),
      (⨆ i, (V i).val.val) = U.val →
      ∀ s : ∀ i, F.obj (op (V i).val),
        (∀ i j,
          res (V i).val (meet (V i).val (V j).val)
            (inf_le_left (a := (V i).val.val) (b := (V j).val.val)) (s i) =
          res (V j).val (meet (V i).val (V j).val)
            (inf_le_right (a := (V i).val.val) (b := (V j).val.val)) (s j)) →
        ∃! t : F.obj (op U), ∀ i, res U (V i).val (V i).property t = s i := by
  -- The argument only needs the intersection-closed family of opens.
  have _ := hB
  intro meet res hcofinal hglue
  have res_comp (A D E : B) (hDA : D ≤ A) (hED : E ≤ D)
      (t : F.obj (op A)) :
      res D E hED (res A D hDA t) = res A E (le_trans hED hDA) t := by
    exact (F.map_comp_apply (homOfLE hDA).op (homOfLE hED).op t).symm
  -- Uniqueness descends from a selected refinement to every covering.
  have separated (U : B) (I : Type w) (V : I → {W : B // W ≤ U})
      (hV : (⨆ i, (V i).val.val) = U.val) (a b : F.obj (op U))
      (hab : ∀ i, res U (V i).val (V i).property a =
        res U (V i).val (V i).property b) : a = b := by
    obtain ⟨J, W, hW, hC, α, hα⟩ := hcofinal U I V hV
    have hcompat : ∀ j k,
        res (W j).val (meet (W j).val (W k).val)
        (inf_le_left (a := (W j).val.val) (b := (W k).val.val))
          (res U (W j).val (W j).property a) =
        res (W k).val (meet (W j).val (W k).val)
        (inf_le_right (a := (W j).val.val) (b := (W k).val.val))
          (res U (W k).val (W k).property a) := by
      intro j k
      rw [res_comp, res_comp]
    obtain ⟨t, _, ht⟩ := hglue U J W hW hC
      (fun j ↦ res U (W j).val (W j).property a) hcompat
    have hb : ∀ j, res U (W j).val (W j).property b =
        res U (W j).val (W j).property a := by
      intro j
      rw [← res_comp U (V (α j)).val (W j).val (V (α j)).property (hα j),
        ← res_comp U (V (α j)).val (W j).val (V (α j)).property (hα j), hab]
    exact (ht a (fun _ ↦ rfl)).trans (ht b hb).symm
  -- Glue the original family on a selected refinement.
  intro U I V hV s hs
  obtain ⟨J, W, hW, hC, α, hα⟩ := hcofinal U I V hV
  let r : ∀ j, F.obj (op (W j).val) :=
    fun j ↦ res (V (α j)).val (W j).val (hα j) (s (α j))
  have hr : ∀ j k,
      res (W j).val (meet (W j).val (W k).val)
        (inf_le_left (a := (W j).val.val) (b := (W k).val.val)) (r j) =
      res (W k).val (meet (W j).val (W k).val)
        (inf_le_right (a := (W j).val.val) (b := (W k).val.val)) (r k) := by
    intro j k
    have hmeet : meet (W j).val (W k).val ≤
        meet (V (α j)).val (V (α k)).val := by
      exact inf_le_inf (show (W j).val.val ≤ (V (α j)).val.val from hα j)
        (show (W k).val.val ≤ (V (α k)).val.val from hα k)
    have h := congrArg
      (res (meet (V (α j)).val (V (α k)).val)
        (meet (W j).val (W k).val) hmeet) (hs (α j) (α k))
    dsimp only [r]
    rw [res_comp, res_comp]
    simpa only [res_comp] using h
  obtain ⟨t, ht, _⟩ := hglue U J W hW hC r hr
  -- Intersections with the refinement cover each original member.
  have htV : ∀ i, res U (V i).val (V i).property t = s i := by
    intro i
    let Z : J → {Z : B // Z ≤ (V i).val} :=
      fun j ↦ ⟨meet (V i).val (W j).val,
        inf_le_left (a := (V i).val.val) (b := (W j).val.val)⟩
    have hZ : (⨆ j, (Z j).val.val) = (V i).val.val := by
      change (⨆ j, (V i).val.val ⊓ (W j).val.val) = (V i).val.val
      rw [← inf_iSup_eq, hW, inf_eq_left.mpr (V i).property]
    apply separated (V i).val J Z hZ
    intro j
    have hmeet : (Z j).val ≤ meet (V i).val (V (α j)).val := by
      exact inf_le_inf (le_rfl : (V i).val.val ≤ (V i).val.val)
        (show (W j).val.val ≤ (V (α j)).val.val from hα j)
    have hZW : (Z j).val ≤ (W j).val :=
      inf_le_right (a := (V i).val.val) (b := (W j).val.val)
    have h := congrArg
      (res (meet (V i).val (V (α j)).val) (Z j).val hmeet) (hs i (α j))
    calc
      res (V i).val (Z j).val (Z j).property
          (res U (V i).val (V i).property t) =
          res U (Z j).val (le_trans (Z j).property (V i).property) t :=
        res_comp _ _ _ _ _ _
      _ = res (W j).val (Z j).val hZW
          (res U (W j).val (W j).property t) := (res_comp _ _ _ _ _ _).symm
      _ = res (W j).val (Z j).val hZW (r j) := by rw [ht]
      _ = res (V (α j)).val (Z j).val (le_trans hZW (hα j))
          (s (α j)) := res_comp _ _ _ _ _ _
      _ = res (V i).val (Z j).val (Z j).property (s i) := by
        simpa only [res_comp] using h.symm
  refine ⟨t, htV, ?_⟩
  intro t' ht'
  exact separated U I V hV t' t (fun i ↦ (ht' i).trans (htV i).symm)

end TopologicalSpace.Opens

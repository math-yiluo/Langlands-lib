/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Matching sections on a locally directed family of opens

Source: Stacks Project, Sheaves, Tags 00AL and 04TN; Constructions, Tag 01LI.
(blueprint: lem-trf-directed-sheaf-matching-sections)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory TopologicalSpace Opposite

namespace TopCat.Sheaf

noncomputable section

variable {T : TopCat.{u}}

/-- Restriction of a section, with its inclusion expressed as an inequality. -/
def restrictSection (P : Sheaf (Type (max u w)) T) {V W : Opens T} (h : W ≤ V)
    (s : P.obj.obj (op V)) : P.obj.obj (op W) :=
  P.obj.map (homOfLE h).op s

@[simp]
theorem restrictSection_trans (P : Sheaf (Type (max u w)) T)
    {V W Z : Opens T} (h : W ≤ V) (k : Z ≤ W) (s : P.obj.obj (op V)) :
    P.restrictSection k (P.restrictSection h s) = P.restrictSection (k.trans h) s := by
  exact (congrArg (fun f ↦ f s) (P.obj.map_comp (homOfLE h).op (homOfLE k).op)).symm

theorem restrictSection_naturality {P Q : Sheaf (Type (max u w)) T} (r : P ⟶ Q)
    {V W : Opens T} (h : W ≤ V) (s : P.obj.obj (op V)) :
    Q.restrictSection h (r.hom.app (op V) s) =
      r.hom.app (op W) (P.restrictSection h s) := by
  exact (congrArg (fun f ↦ f s) (r.hom.naturality (homOfLE h).op)).symm

variable {I : Type u} [Category.{v} I]
  (U : I → Opens T)
  (hU : ∀ {i j : I}, (i ⟶ j) → U i ≤ U j)
  (hdir : ∀ (i j : I) (x : T), x ∈ U i → x ∈ U j →
    ∃ (k : I), Nonempty (k ⟶ i) ∧ Nonempty (k ⟶ j) ∧ x ∈ U k)
  (P : I → Sheaf (Type (max u w)) T)
  (r : ∀ {i j : I}, (i ⟶ j) → (P j ⟶ P i))
  (hr : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), r (f ≫ g) = r g ≫ r f)
  (hlocal : ∀ {i j : I} (f : i ⟶ j) (V : Opens T), V ≤ U i →
    Function.Bijective ((r f).hom.app (op V)))
  (hsupport : ∀ (i : I) (V : Opens T),
    Function.Bijective ((P i).restrictSection (inf_le_left : V ⊓ U i ≤ V)))

/-- The common lower members, indexed without using the hom universe. -/
def CommonLower (i j : I) := {k : I // Nonempty (k ⟶ i) ∧ Nonempty (k ⟶ j)}

include hU hdir in
private theorem commonLower_cover (i j : I) (V : Opens T) (hi : V ≤ U i) :
    ⨆ a : CommonLower i j, V ⊓ U a.val = V ⊓ U j := by
  apply le_antisymm
  · apply iSup_le
    intro a
    exact inf_le_inf_left V (hU a.property.2.some)
  · intro x hx
    obtain ⟨k, hki, hkj, hk⟩ := hdir i j x (hi hx.1) hx.2
    exact Opens.mem_iSup.mpr ⟨⟨k, hki, hkj⟩, hx.1, hk⟩

/-- A matching family has one section on every member's pushforward. -/
def IsMatching (V : Opens T) (s : ∀ i, (P i).obj.obj (op V)) : Prop :=
  ∀ {i j : I} (f : i ⟶ j), (r f).hom.app (op V) (s j) = s i

include hU hdir hlocal hsupport in
/-- A matching family is determined by its component on any member containing the open. -/
theorem matching_ext (i : I) (V : Opens T) (hi : V ≤ U i)
    (s t : ∀ j, (P j).obj.obj (op V))
    (hs : IsMatching P r V s) (ht : IsMatching P r V t) (h : s i = t i) : s = t := by
  funext j
  apply (hsupport j V).injective
  apply (P j).eq_of_locally_eq' (fun a : CommonLower i j ↦ V ⊓ U a.val) (V ⊓ U j)
    (fun a ↦ homOfLE (inf_le_inf_left V (hU a.property.2.some)))
    (by rw [commonLower_cover U hU hdir i j V hi])
  intro a
  change (P j).restrictSection _ ((P j).restrictSection _ (s j)) =
    (P j).restrictSection _ ((P j).restrictSection _ (t j))
  rw [restrictSection_trans, restrictSection_trans]
  apply (hlocal a.property.2.some (V ⊓ U a.val) inf_le_right).injective
  rw [← restrictSection_naturality, ← restrictSection_naturality, hs, ht]
  rw [← hs a.property.1.some, ← ht a.property.1.some, h]

include hr in
private theorem transition_comp_apply {i j k : I} (f : i ⟶ j) (g : j ⟶ k)
    (V : Opens T) (s : (P k).obj.obj (op V)) :
    (r (f ≫ g)).hom.app (op V) s =
      (r f).hom.app (op V) ((r g).hom.app (op V) s) := by
  rw [hr]
  rfl

include hr in
private theorem refine_transition_eq {i j k l : I}
    (p : k ⟶ i) (q : k ⟶ j) (a : l ⟶ k)
    {V W : Opens T} (h : W ≤ V)
    (x : (P i).obj.obj (op V)) (y : (P j).obj.obj (op V))
    (e : (r q).hom.app (op V) y = (r p).hom.app (op V) x) :
    (r (a ≫ q)).hom.app (op W) ((P j).restrictSection h y) =
      (r (a ≫ p)).hom.app (op W) ((P i).restrictSection h x) := by
  simp only [transition_comp_apply P r hr, ← restrictSection_naturality, e]

variable [Quiver.IsThin I]

include hU hdir hr hlocal hsupport in
private theorem exists_extension (i j : I) (V : Opens T) (hi : V ≤ U i)
    (x : (P i).obj.obj (op V)) :
    ∃ y : (P j).obj.obj (op V),
      ∀ {k : I} (p : k ⟶ i) (q : k ⟶ j),
        (r q).hom.app (op (V ⊓ U k)) ((P j).restrictSection inf_le_left y) =
          (r p).hom.app (op (V ⊓ U k)) ((P i).restrictSection inf_le_left x) := by
  classical
  let A := CommonLower i j
  let O (a : A) : Opens T := V ⊓ U a.val
  let val (a : A) : (P j).obj.obj (op (O a)) :=
    (Equiv.ofBijective ((r a.property.2.some).hom.app (op (O a)))
      (hlocal a.property.2.some (O a) inf_le_right)).symm
        ((r a.property.1.some).hom.app (op (O a))
          ((P i).restrictSection inf_le_left x))
  have hv (a : A) : (r a.property.2.some).hom.app (op (O a)) (val a) =
      (r a.property.1.some).hom.app (op (O a))
        ((P i).restrictSection inf_le_left x) := by
    exact (Equiv.ofBijective ((r a.property.2.some).hom.app (op (O a)))
      (hlocal a.property.2.some (O a) inf_le_right)).apply_symm_apply _
  have compat (a b : A) :
      (P j).restrictSection (inf_le_left : O a ⊓ O b ≤ O a) (val a) =
        (P j).restrictSection (inf_le_right : O a ⊓ O b ≤ O b) (val b) := by
    let W : Opens T := O a ⊓ O b
    have hWa : W ≤ U a.val := inf_le_left.trans inf_le_right
    have hWb : W ≤ U b.val := inf_le_right.trans inf_le_right
    apply (P j).eq_of_locally_eq' (fun c : CommonLower a.val b.val ↦ W ⊓ U c.val) W
      (fun c ↦ homOfLE inf_le_left)
      (by rw [commonLower_cover U hU hdir a.val b.val W hWa, inf_eq_left.mpr hWb])
    intro c
    change (P j).restrictSection _ ((P j).restrictSection _ (val a)) =
      (P j).restrictSection _ ((P j).restrictSection _ (val b))
    rw [restrictSection_trans, restrictSection_trans]
    let pa : c.val ⟶ a.val := c.property.1.some
    let pb : c.val ⟶ b.val := c.property.2.some
    apply (hlocal (pa ≫ a.property.2.some) (W ⊓ U c.val) inf_le_right).injective
    have ha := refine_transition_eq P r hr a.property.1.some a.property.2.some pa
      (inf_le_left.trans inf_le_left : W ⊓ U c.val ≤ O a)
      ((P i).restrictSection inf_le_left x) (val a) (hv a)
    have hb := refine_transition_eq P r hr b.property.1.some b.property.2.some pb
      (inf_le_left.trans inf_le_right : W ⊓ U c.val ≤ O b)
      ((P i).restrictSection inf_le_left x) (val b) (hv b)
    have eqp : pa ≫ a.property.1.some = pb ≫ b.property.1.some := Subsingleton.elim _ _
    have eqq : pa ≫ a.property.2.some = pb ≫ b.property.2.some := Subsingleton.elim _ _
    simp only [restrictSection_trans] at ha hb
    rw [← eqq, ← eqp] at hb
    exact ha.trans hb.symm
  obtain ⟨z, hz, _⟩ := (P j).existsUnique_gluing' O (V ⊓ U j)
    (fun a ↦ homOfLE (inf_le_inf_left V (hU a.property.2.some)))
    (by rw [commonLower_cover U hU hdir i j V hi]) val (by intro a b; exact compat a b)
  obtain ⟨y, hy⟩ := (hsupport j V).surjective z
  refine ⟨y, ?_⟩
  intro k p q
  let a : A := ⟨k, ⟨p⟩, ⟨q⟩⟩
  have hza := hz a
  change (P j).restrictSection (inf_le_inf_left V (hU a.property.2.some)) z = val a at hza
  rw [← hy, restrictSection_trans] at hza
  have hp : a.property.1.some = p := Subsingleton.elim _ _
  have hq : a.property.2.some = q := Subsingleton.elim _ _
  have ha := hv a
  rw [← hza] at ha
  simpa only [hp, hq] using ha

include hU hdir hr hlocal hsupport in
/-- Every section on a member extends to a unique matching family on an open inside it. -/
theorem existsUnique_matching (i : I) (V : Opens T) (hi : V ≤ U i)
    (x : (P i).obj.obj (op V)) :
    ∃! s : ∀ j, (P j).obj.obj (op V), IsMatching P r V s ∧ s i = x := by
  classical
  choose s hs using fun j ↦ exists_extension U hU hdir P r hr hlocal hsupport i j V hi x
  have matching : IsMatching P r V s := by
    intro j k f
    apply (hsupport j V).injective
    apply (P j).eq_of_locally_eq' (fun a : CommonLower i j ↦ V ⊓ U a.val) (V ⊓ U j)
      (fun a ↦ homOfLE (inf_le_inf_left V (hU a.property.2.some)))
      (by rw [commonLower_cover U hU hdir i j V hi])
    intro a
    change (P j).restrictSection _ ((P j).restrictSection _
        ((r f).hom.app (op V) (s k))) =
      (P j).restrictSection _ ((P j).restrictSection _ (s j))
    rw [restrictSection_trans, restrictSection_trans, restrictSection_naturality]
    apply (hlocal a.property.2.some (V ⊓ U a.val) inf_le_right).injective
    rw [← transition_comp_apply P r hr a.property.2.some f,
      hs k a.property.1.some (a.property.2.some ≫ f), hs j]
  have self : s i = x := by
    apply (hsupport i V).injective
    have e := hs i (𝟙 i) (𝟙 i)
    exact (hlocal (𝟙 i) (V ⊓ U i) inf_le_right).injective e
  refine ⟨s, ⟨matching, self⟩, ?_⟩
  intro t ht
  exact matching_ext U hU hdir P r hlocal hsupport i V hi t s ht.1 matching
    (ht.2.trans self.symm)

end

end TopCat.Sheaf

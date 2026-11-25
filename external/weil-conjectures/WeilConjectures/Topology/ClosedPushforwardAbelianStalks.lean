/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Topology.Sheaves.Functors
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Stalks of closed-subset pushforward for abelian sheaves

Source: Stacks Project, Sheaves, Lemma 00AE (lemma-stalks-closed-pushforward),
abelian-sheaf clause (blueprint: lem-sc-closed-pushforward-abelian-stalks).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace Topology
open TopCat

namespace TopCat

/-- Stalks of the direct image of an abelian sheaf along a closed embedding.

Source: Stacks Project, Sheaves, Lemma 00AE (blueprint: lem-sc-closed-pushforward-abelian-stalks).
Proof (the five steps of the node):
1. The direct image has sections `F(V ∩ C)`, with restrictions those of `F`.
Its germs are represented by these sections, and morphisms act on representatives
(def-weil-pbc-module-stalk).
2. If `x ∉ C`, intersect any representative's neighbourhood with the open complement
of `C`. Its trace on `C` is empty, and `F(∅) = 0` by the empty-cover sheaf axiom.
Thus every germ is zero (def-weil-pbc-module-stalk).
3. For `z ∈ C`, every open neighbourhood in the subspace is `V ∩ C` for an ambient
open neighbourhood `V` of `z`. These traces are cofinal among subspace neighbourhoods;
one can replace `V` by its union with the complement of `C`.
4. The two neighbourhood colimits therefore agree. The canonical map sends the germ
of a section in `F(V ∩ C)` to its germ at `z`. Cofinality gives surjectivity, and the
criterion that equal germs agree after restriction gives injectivity
(def-weil-pbc-module-stalk).
5. Germ maps preserve addition, so the comparison is an abelian-group isomorphism.
Applying a sheaf morphism to a representative and then taking its germ agrees with
first taking the germ and then applying the induced stalk map. This gives the stated
naturality equation (def-weil-pbc-module-stalk).
-/
theorem closedPushforwardAbelianStalks
    {X : TopCat.{u}} (C : Set X) (hC : IsClosed C)
    (F : (TopCat.of C).Sheaf AddCommGrpCat.{u}) :
    (∀ x : X, x ∉ C →
      IsZero (TopCat.Presheaf.stalk
        ((TopCat.Sheaf.pushforward AddCommGrpCat
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)).obj F).1 x)) ∧
    (∀ z : (TopCat.of C),
      IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) F.1 z)) ∧
    (∀ (G : (TopCat.of C).Sheaf AddCommGrpCat.{u}) (φ : F ⟶ G)
      (z : (TopCat.of C)),
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat
        (Subtype.val z)).map
          ((TopCat.Presheaf.pushforward AddCommGrpCat
            (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)).map φ.1) ≫
          TopCat.Presheaf.stalkPushforward AddCommGrpCat
            (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) G.1 z =
        TopCat.Presheaf.stalkPushforward AddCommGrpCat
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) F.1 z ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat z).map φ.1) := by
  let i : TopCat.of C ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let P := (TopCat.Presheaf.pushforward AddCommGrpCat i).obj F.1
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    change IsZero (P.stalk x)
    apply AddCommGrpCat.isZero_iff_subsingleton.mpr
    suffices h : ∀ t : P.stalk x, t = 0 from
      ⟨fun a b ↦ (h a).trans (h b).symm⟩
    intro t
    obtain ⟨V, hV, hxV, s, rfl⟩ :=
      P.exists_le_germ_eq t (V := ⟨Cᶜ, hC.isOpen_compl⟩) hx
    have he : (Opens.map i).obj V = ⊥ := by
      ext z
      exact ⟨fun hz ↦ (hV hz) z.property, fun hz ↦ False.elim hz⟩
    have hz := (F.isTerminalOfEqEmpty he).isZero
    have hs : s = 0 := (AddCommGrpCat.isZero_iff_subsingleton.mp hz).elim _ _
    rw [hs]
    exact map_zero _
  · intro z
    exact Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat Topology.IsInducing.subtypeVal F.1 z
  · intro G φ z
    apply Presheaf.stalk_hom_ext P
    intro V hxV
    change P.germ V (i z) hxV ≫
      (Presheaf.stalkFunctor AddCommGrpCat (i z)).map
        ((Presheaf.pushforward AddCommGrpCat i).map φ.1) ≫
        Presheaf.stalkPushforward AddCommGrpCat i G.1 z =
      P.germ V (i z) hxV ≫ Presheaf.stalkPushforward AddCommGrpCat i F.1 z ≫
        (Presheaf.stalkFunctor AddCommGrpCat z).map φ.1
    rw [Presheaf.stalkFunctor_map_germ_assoc]
    conv_rhs => rw [← Category.assoc]
    erw [Presheaf.stalkPushforward_germ]
    dsimp only [P]
    erw [Presheaf.stalkPushforward_germ, Presheaf.stalkFunctor_map_germ]
    rfl

end TopCat

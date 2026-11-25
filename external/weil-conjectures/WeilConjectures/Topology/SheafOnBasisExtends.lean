/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.Algebra.Category.Grp.Limits

/-!
# Extending a sheaf of abelian groups from a basis

Source: Stacks Project, Sheaves on Spaces, Section 009H, Tags 009N and 009Q
(blueprint: lem-weil-pbc-sheaf-on-basis-extends).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory Opposite TopologicalSpace

namespace TopologicalSpace.Opens

/-- A presheaf of abelian groups with unique gluing on an intersection-closed basis extends
 to a sheaf on the space, with group isomorphisms on basis opens commuting with restrictions.
Source: Stacks Project, Section 009H, Tags 009M, 009N and 009Q
(blueprint: lem-weil-pbc-sheaf-on-basis-extends).

Proof:
1. Include the basis as a full subcategory of opens. Its range is a topological basis,
   so Mathlib's `TopCat.Opens.coverDense_iff_isBasis` makes this inclusion cover dense.
2. For a covering sieve in the induced topology, index all its arrows by their basic
   domains, lifting the index universe to the one in `hglue`. The pushforward sieve
   covers the basic open, so these domains cover it. Sieve compatibility implies
   compatibility on basic intersections. Unique gluing gives the unique amalgamation.
   The forgetful functor from abelian groups reflects limits, so this also proves
   the abelian-group-valued sheaf condition.
3. Mathlib's `Functor.sheafInducedTopologyEquivOfIsCoverDense` constructs the extension.
   The inverse equivalence is restriction to the basis. The inverse unit isomorphism
   gives the required group isomorphisms, and its naturality gives their compatibility
   with restrictions.

Cover indices may be empty. The index universe contains the universe of all basis opens;
coverings with larger index types can be reindexed by their image in the basis, since agreement
on intersections forces equal sections for repeated opens. -/
theorem exists_sheaf_extension_of_basis_gluing
    (X : TopCat.{u}) (B : Set (Opens X)) (hB : IsBasis B)
    (hcap : ∀ U V : B, U.val ⊓ V.val ∈ B)
    (F : Bᵒᵖ ⥤ AddCommGrpCat.{max u v})
    (hglue : ∀ (U : B) (I : Type (max u v w)) (V : I → {W : B // W ≤ U}),
      (⨆ i, (V i).val.val) = U.val →
      ∀ s : ∀ i, F.obj (op (V i).val),
        (∀ i j,
          (F.map (homOfLE
            (show (⟨(V i).val.val ⊓ (V j).val.val, hcap (V i).val (V j).val⟩ : B) ≤
              (V i).val from
              inf_le_left (a := (V i).val.val) (b := (V j).val.val))).op).hom (s i) =
          (F.map (homOfLE
            (show (⟨(V i).val.val ⊓ (V j).val.val, hcap (V i).val (V j).val⟩ : B) ≤
              (V j).val from
              inf_le_right (a := (V i).val.val) (b := (V j).val.val))).op).hom (s j)) →
        ∃! t : F.obj (op U),
          ∀ i, (F.map (homOfLE (V i).property).op).hom t = s i) :
    ∃ Fext : TopCat.Sheaf AddCommGrpCat.{max u v} X,
      ∃ iota : ∀ U : B, Fext.presheaf.obj (op U.val) ≅ F.obj (op U),
        ∀ (U V : B) (hVU : V ≤ U) (t : Fext.presheaf.obj (op U.val)),
          (iota V).hom.hom
              ((Fext.presheaf.map (homOfLE (show V.val ≤ U.val from hVU)).op).hom t) =
            (F.map (homOfLE hVU).op).hom ((iota U).hom.hom t) := by
  classical
  let G : B ⥤ Opens X := (Subtype.mono_coe B).functor
  have hGB : IsBasis (Set.range G.obj) := by
    convert hB using 1
    ext U
    simp only [G, Monotone.functor_obj, Subtype.range_coe]
  let : G.IsCoverDense (Opens.grothendieckTopology X) :=
    (TopCat.Opens.coverDense_iff_isBasis G).2 hGB
  let : G.Full := ⟨fun f ↦ ⟨homOfLE f.le, Subsingleton.elim _ _⟩⟩
  let J := G.inducedTopology (Opens.grothendieckTopology X)
  have hF : CategoryTheory.Presheaf.IsSheaf J F := by
    apply CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp
      (s := forget AddCommGrpCat.{max u v})
    rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
    intro U S hS
    rw [Functor.mem_inducedTopology_iff_of_isCoverDense] at hS
    intro s hs
    let I := ULift.{max u v w} (Σ V : B, {f : V ⟶ U // S f})
    let V : I → {W : B // W ≤ U} := fun i ↦ ⟨i.down.1, i.down.2.1.le⟩
    have hcover : (⨆ i, (V i).val.val) = U.val := by
      apply le_antisymm
      · exact iSup_le fun i ↦ (V i).property
      · intro x hx
        obtain ⟨W, f, ⟨Z, g, k, hg, hk⟩, hxW⟩ := hS x hx
        exact Opens.mem_iSup.mpr ⟨⟨⟨Z, ⟨g, hg⟩⟩⟩, k.le hxW⟩
    let ss : ∀ i, F.obj (op (V i).val) := fun i ↦ s i.down.2.1 i.down.2.2
    have hcompat : ∀ i j,
        (F.map (homOfLE
          (show (⟨(V i).val.val ⊓ (V j).val.val, hcap (V i).val (V j).val⟩ : B) ≤
            (V i).val from
              inf_le_left (a := (V i).val.val) (b := (V j).val.val))).op).hom (ss i) =
        (F.map (homOfLE
          (show (⟨(V i).val.val ⊓ (V j).val.val, hcap (V i).val (V j).val⟩ : B) ≤
            (V j).val from
              inf_le_right (a := (V i).val.val) (b := (V j).val.val))).op).hom (ss j) := by
      intro i j
      exact hs _ _ i.down.2.2 j.down.2.2 (Subsingleton.elim _ _)
    obtain ⟨t, ht, hu⟩ := hglue U I V hcover ss hcompat
    refine ⟨t, ?_, ?_⟩
    · intro W f hf
      exact ht ⟨⟨W, ⟨f, hf⟩⟩⟩
    · intro t' ht'
      apply hu t'
      intro i
      exact ht' i.down.2.1 i.down.2.2
  let E := G.sheafInducedTopologyEquivOfIsCoverDense
    (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}
  let FB : CategoryTheory.Sheaf J AddCommGrpCat.{max u v} := ⟨F, hF⟩
  let FE := E.functor.obj FB
  let e := E.unitIso.symm.app FB
  refine ⟨FE, fun U ↦ ?_, ?_⟩
  · exact (CategoryTheory.sheafToPresheaf J AddCommGrpCat).mapIso e |>.app (op U)
  · intro U V hVU t
    have hn := e.hom.hom.naturality (homOfLE hVU).op
    exact ConcreteCategory.congr_hom hn t

end TopologicalSpace.Opens

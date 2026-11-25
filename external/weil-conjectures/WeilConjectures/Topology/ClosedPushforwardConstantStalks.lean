/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.ClosedPushforwardConstantPresheaf
public import Mathlib.Topology.Sheaves.Stalks
import WeilConjectures.Topology.LocallyConstantGermEvaluation
import WeilConjectures.Topology.LocallyConstantMapsSheaf
import Mathlib.Topology.Sheaves.Functors

/-!
# Stalks of a constant sheaf pushed forward from a closed subset

Source: Stacks Project, Sheaves on Spaces, Tags 006W, 007B and 00AE
(blueprint: lem-weil-pbc-closed-pushforward-constant-stalks).
-/

@[expose] public section

set_option autoImplicit false

universe w

open CategoryTheory Opposite TopologicalSpace

namespace TopCat

/-- The closed direct image is a sheaf; its stalk evaluates bijectively to the coefficient
set on the closed subset, and is a singleton elsewhere.
Source: Stacks Project, Sheaves on Spaces, Tags 006W, 007B and 00AE
(blueprint: lem-weil-pbc-closed-pushforward-constant-stalks).

Proof:
1. Compatible locally constant maps on an open cover glue pointwise. Local constancy is
checked in a covering member containing the point; uniqueness is pointwise. This is
lem-weil-pbc-locally-constant-maps-sheaf (Tag 006W).
2. At a point in C, each neighbourhood in C is the intersection with an ambient open
neighbourhood. Thus representatives and their germ equivalence relations identify the
stalk with that of locally constant maps on C. The unique evaluation map and its
bijectivity follow from lem-weil-pbc-locally-constant-germ-evaluation (Tag 007B).
The stalk and germ use the colimit of def-weil-pbc-category-colimit.
3. Outside C the open complement is a neighbourhood carrying the unique empty map.
Every germ restricts to that map after shrinking into the complement, so the stalk
has exactly one element (Tag 00AE). -/
theorem closed_pushforward_constant_stalks
    (X : TopCat.{w}) (C : Set X) (hC : IsClosed C) (R : Type w) :
    (closedPushforwardConstantPresheaf X C R).IsSheaf ∧
    (∀ (x : X) (hxC : x ∈ C),
      ∃ ev : (closedPushforwardConstantPresheaf X C R).stalk x → R,
        (∀ (V : Opens X) (hxV : x ∈ V)
            (g : LocallyConstant {y : X // y ∈ V ∧ y ∈ C} R),
          ev ((closedPushforwardConstantPresheaf X C R).germ V x hxV g) =
            g ⟨x, hxV, hxC⟩) ∧
        Function.Bijective ev ∧
        (∀ ev' : (closedPushforwardConstantPresheaf X C R).stalk x → R,
          (∀ (V : Opens X) (hxV : x ∈ V)
              (g : LocallyConstant {y : X // y ∈ V ∧ y ∈ C} R),
            ev' ((closedPushforwardConstantPresheaf X C R).germ V x hxV g) =
              g ⟨x, hxV, hxC⟩) → ev' = ev)) ∧
    (∀ (x : X), x ∉ C →
      Nonempty ((closedPushforwardConstantPresheaf X C R).stalk x) ∧
      Subsingleton ((closedPushforwardConstantPresheaf X C R).stalk x)) := by
  let Z := TopCat.of C
  let i : Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let L := locallyConstantMapsPresheaf Z R
  let F := closedPushforwardConstantPresheaf X C R
  let e : F ≅ (Presheaf.pushforward (Type w) i).obj L :=
    NatIso.ofComponents (fun V ↦
      { hom := TypeCat.ofHom (LocallyConstant.comap
          ⟨fun y ↦ ⟨y.1.1, y.2, y.1.2⟩,
            (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩)
        inv := TypeCat.ofHom (LocallyConstant.comap
          ⟨fun y ↦ ⟨⟨y.1, y.2.2⟩, y.2.1⟩,
            (continuous_subtype_val.subtype_mk _).subtype_mk _⟩)
        hom_inv_id := by ext g; rfl
        inv_hom_id := by ext g; rfl }) (by intros; rfl)
  refine ⟨?_, ?_, ?_⟩
  · exact (Presheaf.isSheaf_iso_iff e).mpr
      (Sheaf.pushforward_sheaf_of_sheaf i (locallyConstantMapsPresheaf_isSheaf Z R))
  · intro x hxC
    let z : Z := ⟨x, hxC⟩
    have hi : Topology.IsInducing i := Topology.IsInducing.subtypeVal
    have := Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      (Type w) hi L z
    let q : F.stalk x ≅ L.stalk z :=
      (Presheaf.stalkFunctor (Type w) x).mapIso e ≪≫
        asIso (L.stalkPushforward (Type w) i z)
    obtain ⟨ev, hev, hbij, _⟩ := existsUnique_locallyConstant_germ_evaluation Z z R
    change ∃ ev : F.stalk x → R, _
    refine ⟨ev ∘ q.hom, ?_, ?_, ?_⟩
    · intro V hxV g
      change ev ((L.stalkPushforward (Type w) i z)
        (((Presheaf.stalkFunctor (Type w) x).map e.hom) (F.germ V x hxV g))) = _
      rw [Presheaf.stalkFunctor_map_germ_apply]
      erw [Presheaf.stalkPushforward_germ_apply (Type w) i L V z hxV]
      exact hev _ hxV _
    · exact hbij.comp (ConcreteCategory.bijective_of_isIso q.hom)
    · intro ev' hev'
      funext t
      obtain ⟨V, hxV, g, rfl⟩ := F.exists_germ_eq t
      rw [hev']
      change _ = ev ((L.stalkPushforward (Type w) i z)
        (((Presheaf.stalkFunctor (Type w) x).map e.hom) (F.germ V x hxV g)))
      erw [Presheaf.stalkFunctor_map_germ_apply,
        Presheaf.stalkPushforward_germ_apply (Type w) i L V z hxV, hev]
      rfl
  · intro x hxC
    let V : Opens X := ⟨Cᶜ, hC.isOpen_compl⟩
    have hxV : x ∈ V := hxC
    have empty (U : Opens X) (hU : U ≤ V) : IsEmpty {y : X // y ∈ U ∧ y ∈ C} :=
      ⟨fun y ↦ hU y.2.1 y.2.2⟩
    let g : LocallyConstant {y : X // y ∈ V ∧ y ∈ C} R :=
      letI := empty V le_rfl
      ⟨isEmptyElim, by
        intro S
        have : isEmptyElim ⁻¹' S = (∅ : Set {y : X // y ∈ V ∧ y ∈ C}) := by
          ext y
          exact isEmptyElim y
        rw [this]
        exact isOpen_empty⟩
    refine ⟨⟨F.germ V x hxV g⟩, ⟨?_⟩⟩
    intro a b
    obtain ⟨U, hUV, hxU, s, rfl⟩ := F.exists_le_germ_eq a hxV
    obtain ⟨W, hWV, hxW, t, rfl⟩ := F.exists_le_germ_eq b hxV
    let Q := U ⊓ W
    have hxQ : x ∈ Q := ⟨hxU, hxW⟩
    have := empty Q (inf_le_left.trans hUV)
    have heq : F.map (homOfLE (inf_le_left : Q ≤ U)).op s =
        F.map (homOfLE (inf_le_right : Q ≤ W)).op t := by
      apply LocallyConstant.ext
      intro y
      exact isEmptyElim y
    rw [← F.germ_res_apply (homOfLE (inf_le_left : Q ≤ U)) x hxQ s,
      ← F.germ_res_apply (homOfLE (inf_le_right : Q ≤ W)) x hxQ t, heq]

end TopCat

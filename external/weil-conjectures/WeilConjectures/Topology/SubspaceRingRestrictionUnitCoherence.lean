/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Topology.Homeomorph.Lemmas
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback

/-!
# Restriction units on subspaces

Source: Stacks Project, Sheaves on Spaces, Tags 008F, 008I and 008P.
(blueprint: lem-a1-subspace-ring-restriction-unit-coherence)

The auxiliary maps below are the actual inclusions, adjunction units and ordinary
restriction maps. The three statements give the ring, set and homeomorphism clauses.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat.Sheaf

/-- Inclusion of an arbitrary subspace, Stacks Tags 008F and 008P.
(blueprint: lem-a1-subspace-ring-restriction-unit-coherence) -/
def subspaceInclusion {Z : TopCat.{u}} (E : Set Z) : TopCat.of E ⟶ Z :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Factor the subspace inclusion through an open neighbourhood, Stacks Tag 008I.
(blueprint: lem-a1-subspace-ring-restriction-unit-coherence) -/
def subspaceToOpen {Z : TopCat.{u}} (E : Set Z) (V : Opens Z) (h : E ⊆ V) :
    TopCat.of E ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.1, h x.2⟩, continuous_subtype_val.subtype_mk _⟩

section Coefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (A : Type v) [Category.{u} A]
variable {FA : A → A → Type u} {CA : A → Type u}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u} A FA]
variable [HasColimits A] [HasLimits A] [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

/-- The section map to the whole subspace is the inverse-image unit followed by
restriction from the inverse-image open to the top open. Stacks Tags 008F and 008P.
(blueprint: lem-a1-subspace-ring-restriction-unit-coherence) -/
def subspaceSectionMap {Z : TopCat.{u}} (E : Set Z) (G : Z.Sheaf A)
    (V : Opens Z) (h : E ⊆ V) :
    G.obj.obj (op V) ⟶ ((pullback A (subspaceInclusion E)).obj G).obj.obj (op ⊤) :=
  ((pullbackPushforwardAdjunction A (subspaceInclusion E)).unit.app G).hom.app (op V) ≫
    ((pullback A (subspaceInclusion E)).obj G).obj.map
      (homOfLE (fun x _ ↦ h x.2)).op

/-- The unit on an open of an open neighbourhood, evaluated on its preimage in the
subspace. The last map only identifies the two descriptions of that open.
Source: Stacks Tags 008F, 008I and 008P.
(blueprint: lem-a1-subspace-ring-restriction-unit-coherence) -/
def subspaceOpenUnit {Z : TopCat.{u}} (E : Set Z) (G : Z.Sheaf A)
    (V : Opens Z) (h : E ⊆ V) (B : Opens (TopCat.of V)) :
    G.obj.obj (op (V.isOpenEmbedding.functor.obj B)) ⟶
      ((pullback A (subspaceInclusion E)).obj G).obj.obj
        (op ((Opens.map (subspaceToOpen E V h)).obj B)) :=
  ((pullbackPushforwardAdjunction A (subspaceInclusion E)).unit.app G).hom.app
      (op (V.isOpenEmbedding.functor.obj B)) ≫
    ((pullback A (subspaceInclusion E)).obj G).obj.map
      (homOfLE (fun x hx ↦ ⟨⟨x.1, h x.2⟩, hx, rfl⟩)).op

/-- Ordinary restriction on global sections to an open subspace, with the ambient
image of its top open used by Mathlib's restriction functor. Stacks Tag 008F.
(blueprint: lem-a1-subspace-ring-restriction-unit-coherence) -/
def openRestrictionGlobal {Z : TopCat.{u}} (G : Z.Sheaf A) (V : Opens Z) :
    G.obj.obj (op V) ⟶ ((V.isOpenEmbedding.sheafPullback A).obj G).obj.obj (op ⊤) :=
  G.obj.map (homOfLE (fun _ ⟨y, _, heq⟩ ↦ heq ▸ y.2)).op

private theorem sectionMap_naturality {Z : TopCat.{u}} (E : Set Z) (G : Z.Sheaf A)
    (W V : Opens Z) (hWV : W ≤ V) (hEW : E ⊆ W) :
    G.obj.map (homOfLE hWV).op ≫ subspaceSectionMap A E G W hEW =
      subspaceSectionMap A E G V (fun _x hx ↦ hWV (hEW hx)) := by
  dsimp [subspaceSectionMap]
  have hn := ((pullbackPushforwardAdjunction A (subspaceInclusion E)).unit.app G).hom.naturality
    (homOfLE hWV).op
  dsimp at hn
  rw [← Category.assoc, hn, Category.assoc]
  rw [← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem open_unit {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : Topology.IsOpenEmbedding f) (G : Y.Sheaf A) (B : Opens Y) :
    ((pullbackPushforwardAdjunction A f).unit.app G).hom.app (op B) ≫
      ((hf.sheafPullbackIso A).hom.app G).hom.app (op ((Opens.map f).obj B)) =
      G.obj.map (hf.isOpenMap.adjunction.counit.app B).op := by
  have h := Functor.sheafAdjunctionContinuous_unit_app_hom_sheafPullbackIso_hom
    (Opens.map f) A (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) G
  have hB := NatTrans.congr_app h (op B)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hB
  dsimp only [Topology.IsOpenEmbedding.sheafPullbackIso, Iso.trans_hom,
    NatTrans.comp_app, NatIso.ofComponents_hom_app,
    ObjectProperty.FullSubcategory.comp_hom]
  change _ ≫ (((pullbackIso A f).hom.app G).hom.app _ ≫
    (sheafifyMap (Opens.grothendieckTopology X)
      (hf.isOpenMap.pullbackIso.hom.app G.obj)).app _ ≫
    (isoSheafify (Opens.grothendieckTopology X)
      (TopCat.Presheaf.isSheaf_of_isOpenEmbedding hf G.2)).inv.app _) = _
  change ((pullbackPushforwardAdjunction A f).unit.app G).hom.app (op B) ≫
    ((pullbackIso A f).hom.app G).hom.app (op ((Opens.map f).obj B)) =
    ((Opens.map f).op.lanUnit.app G.obj).app (op B) ≫
      (toSheafify (Opens.grothendieckTopology X)
        ((Opens.map f).op.leftKanExtension G.obj)).app (op ((Opens.map f).obj B)) at hB
  dsimp only [TopCat.Sheaf, TopCat.instCategorySheaf, TopCat.Presheaf, Functor.op_obj] at *
  rw [← Category.assoc, hB, Category.assoc]
  rw [isoSheafify_inv, ← NatTrans.comp_app, sheafifyMap_sheafifyLift]
  rw [← NatTrans.comp_app, toSheafify_sheafifyLift]
  dsimp [IsOpenMap.pullbackIso, IsOpenMap.pullbackObjIso,
    Presheaf.pullbackObjObjOfImageOpen]
  rw [Category.comp_id]
  let j : CostructuredArrow (Opens.map f).op (op ((Opens.map f).obj B)) :=
    CostructuredArrow.mk (𝟙 _)
  have hij : ((Functor.LeftExtension.mk _
      ((Opens.map f).op.leftKanExtensionUnit G.obj)).coconeAt
      (op ((Opens.map f).obj B))).ι.app j =
      ((Opens.map f).op.lanUnit.app G.obj).app (op B) := by
    simp [j, Functor.LeftExtension.coconeAt, Functor.lanUnit]
  rw [← hij, IsColimit.comp_coconePointUniqueUpToIso_hom]
  congr 1

private theorem restriction_coherence
    {Z : TopCat.{u}} (E : Set Z) (G : Z.Sheaf A) :
    (∀ (V B : Opens Z),
      ((pullbackPushforwardAdjunction A V.inclusion').unit.app G).hom.app
          (op B) ≫
        ((V.isOpenEmbedding.sheafPullbackIso A).hom.app G).hom.app
          (op ((Opens.map V.inclusion').obj B)) =
      G.obj.map (V.isOpenEmbedding.isOpenMap.adjunction.counit.app B).op) ∧
    (∀ (V : Opens Z) (h : E ⊆ V),
      ∃ c : (pullback A (subspaceToOpen E V h)).obj
          ((V.isOpenEmbedding.sheafPullback A).obj G) ≅
          (pullback A (subspaceInclusion E)).obj G,
        (∀ B : Opens (TopCat.of V),
          ((pullbackPushforwardAdjunction A (subspaceToOpen E V h)).unit.app
              ((V.isOpenEmbedding.sheafPullback A).obj G)).hom.app (op B) ≫
            c.hom.hom.app (op ((Opens.map (subspaceToOpen E V h)).obj B)) =
          subspaceOpenUnit A E G V h B) ∧
        (∀ c' : (pullback A (subspaceToOpen E V h)).obj
          ((V.isOpenEmbedding.sheafPullback A).obj G) ≅
          (pullback A (subspaceInclusion E)).obj G,
          (∀ B : Opens (TopCat.of V),
          ((pullbackPushforwardAdjunction A (subspaceToOpen E V h)).unit.app
              ((V.isOpenEmbedding.sheafPullback A).obj G)).hom.app (op B) ≫
            c'.hom.hom.app (op ((Opens.map (subspaceToOpen E V h)).obj B)) =
          subspaceOpenUnit A E G V h B) →
          c' = c) ∧
        openRestrictionGlobal A G V ≫
          ((pullbackPushforwardAdjunction A (subspaceToOpen E V h)).unit.app
            ((V.isOpenEmbedding.sheafPullback A).obj G)).hom.app (op ⊤) ≫
          c.hom.hom.app (op ⊤) = subspaceSectionMap A E G V h) ∧
    (∀ (W V : Opens Z) (hWV : W ≤ V) (hEW : E ⊆ W),
      G.obj.map (homOfLE hWV).op ≫ subspaceSectionMap A E G W hEW =
        subspaceSectionMap A E G V (fun _x hx ↦ hWV (hEW hx))) := by
  refine ⟨fun V B ↦ open_unit A V.inclusion' V.isOpenEmbedding G B, ?_,
    fun W V hWV hEW ↦ sectionMap_naturality A E G W V hWV hEW⟩
  intro V h
  let a := (pullbackPushforwardAdjunction A V.inclusion').ofNatIsoLeft
    (V.isOpenEmbedding.sheafPullbackIso A)
  let b := a.comp (pullbackPushforwardAdjunction A (subspaceToOpen E V h))
  let d : pullback A (subspaceInclusion E) ⊣
      pushforward A (subspaceToOpen E V h) ⋙ pushforward A V.inclusion' :=
    pullbackPushforwardAdjunction A (subspaceInclusion E)
  let c := (b.leftAdjointUniq d).app G
  have hc := b.unit_leftAdjointUniq_hom_app d G
  have hcU : ∀ B : Opens (TopCat.of V),
      ((pullbackPushforwardAdjunction A (subspaceToOpen E V h)).unit.app
        ((V.isOpenEmbedding.sheafPullback A).obj G)).hom.app (op B) ≫
        c.hom.hom.app (op ((Opens.map (subspaceToOpen E V h)).obj B)) =
        subspaceOpenUnit A E G V h B := by
    intro B
    have hc0 := hc
    dsimp only [b] at hc0
    rw [Adjunction.comp_unit_app] at hc0
    have hcB := congrArg (fun k ↦ k.hom.app
      (op (V.isOpenEmbedding.functor.obj B))) hc0
    dsimp only [TopCat.Sheaf, TopCat.instCategorySheaf, TopCat.Presheaf] at *
    change ((a.unit.app G).hom.app (op (V.isOpenEmbedding.functor.obj B)) ≫
      ((pullbackPushforwardAdjunction A (subspaceToOpen E V h)).unit.app
        ((V.isOpenEmbedding.sheafPullback A).obj G)).hom.app
          (op ((Opens.map V.inclusion').obj (V.isOpenEmbedding.functor.obj B)))) ≫
      c.hom.hom.app (op ((Opens.map (subspaceInclusion E)).obj
        (V.isOpenEmbedding.functor.obj B))) =
      ((pullbackPushforwardAdjunction A (subspaceInclusion E)).unit.app G).hom.app
        (op (V.isOpenEmbedding.functor.obj B)) at hcB
    have ha : (a.unit.app G).hom.app (op (V.isOpenEmbedding.functor.obj B)) =
        G.obj.map (V.isOpenEmbedding.isOpenMap.adjunction.counit.app
          (V.isOpenEmbedding.functor.obj B)).op :=
      open_unit A V.inclusion' V.isOpenEmbedding G _
    rw [ha] at hcB
    let q := (V.isOpenEmbedding.isOpenMap.adjunction.unit.app B).op
    have hn := ((pullbackPushforwardAdjunction A (subspaceToOpen E V h)).unit.app
      ((V.isOpenEmbedding.sheafPullback A).obj G)).hom.naturality q
    have hn' := c.hom.hom.naturality ((Opens.map (subspaceToOpen E V h)).op.map q)
    have hcB' := congrArg (fun k ↦ k ≫
      ((pullback A (subspaceInclusion E)).obj G).obj.map
        ((Opens.map (subspaceToOpen E V h)).op.map q)) hcB
    dsimp only [TopCat.Sheaf, TopCat.instCategorySheaf, TopCat.Presheaf,
      Functor.id_obj, Functor.comp_obj, pushforward_obj_val] at hn hn' hcB' ⊢
    dsimp [subspaceOpenUnit]
    have htri : G.obj.map
        (V.isOpenEmbedding.isOpenMap.adjunction.counit.app
          (V.isOpenEmbedding.functor.obj B)).op ≫
        ((V.isOpenEmbedding.sheafPullback A).obj G).obj.map q = 𝟙 _ := by
      change G.obj.map _ ≫ G.obj.map _ = _
      rw [← Functor.map_comp]
      exact (congrArg G.obj.map (Subsingleton.elim _ _)).trans (G.obj.map_id _)
    dsimp only [Presheaf.pushforward, Functor.comp_map] at hn
    dsimp only [Functor.whiskeringLeft, Functor.comp_map] at hn
    dsimp only [TopCat.Sheaf, TopCat.instCategorySheaf, TopCat.Presheaf,
      Opens.toTopCat, TopCat.of, Functor.op_obj] at hn hn' hcB' htri ⊢
    simp only [Category.assoc] at hcB'
    erw [← hn'] at hcB'
    erw [← reassoc_of% hn] at hcB'
    simp only [← Category.assoc] at hcB'
    erw [htri, Category.id_comp] at hcB'
    refine hcB'.trans ?_
    apply congrArg (fun k ↦
      ((pullbackPushforwardAdjunction A (subspaceInclusion E)).unit.app G).hom.app
        (op (V.isOpenEmbedding.functor.obj B)) ≫
        ((pullback A (subspaceInclusion E)).obj G).obj.map k)
    exact Subsingleton.elim _ _
  refine ⟨c, hcU, ?_, ?_⟩
  · intro c' hc'
    apply Iso.ext
    apply ((pullbackPushforwardAdjunction A (subspaceToOpen E V h)).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext B
    exact (hc' B.unop).trans (hcU B.unop).symm
  · have htop := hcU ⊤
    dsimp only [TopCat.Sheaf, TopCat.instCategorySheaf, TopCat.Presheaf,
      Opens.map_top] at htop ⊢
    change _ ≫ c.hom.hom.app (op ⊤) = _ at htop
    dsimp only [TopCat.Sheaf, TopCat.instCategorySheaf, TopCat.Presheaf,
      Opens.toTopCat, TopCat.of] at *
    rw [htop]
    dsimp [openRestrictionGlobal, subspaceOpenUnit, subspaceSectionMap]
    have hn := ((pullbackPushforwardAdjunction A (subspaceInclusion E)).unit.app G).hom.naturality
      (show V.isOpenEmbedding.functor.obj ⊤ ⟶ V from
        homOfLE (fun _ ⟨y, _, heq⟩ ↦ heq ▸ y.2)).op
    dsimp at hn
    rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
    congr 1

end Coefficients

set_option linter.unusedVariables false in
set_option linter.unusedVariables false in
/-- Open restriction, unique composition through an open neighbourhood and nested
neighbourhood coherence for sheaves of sets.
Source: Stacks Project, Sheaves on Spaces, Tags 008F, 008I and 008P.
(blueprint: lem-a1-subspace-ring-restriction-unit-coherence)

Proof (node steps 1--3): An open A of V is terminal in its ambient neighbourhood
diagram, so the presheaf inverse image equals ordinary restriction. Sheafification
fixes it. This gives the first unit formula (def-weil-pbc-topological-inverse-image,
def-weil-pbc-category-colimit, def-weil-pbc-sheafification). Compose the adjunctions
for the two inclusions (def-weil-pbc-composite-adjunction). Their composite unit is
the successive application of the two units. Unit-preserving uniqueness of left
adjoints (situation-conventions) gives the composition isomorphism;
the hom bijection for p_V proves uniqueness already for this single G. On B = V
this is the stated global section formula. For nested neighbourhoods, naturality
of the unit in opens gives r_W after restriction equals r_V: both inverse-image
opens are the whole subspace, so the lower restriction is the identity. The set
comparison is the unit-characterized comparison of
lem-weil-pbc-sets-inverse-image-composition, by its uniqueness clause. No point,
nonempty open or nonempty subspace is used. -/
theorem subspace_sets_restriction_unit_coherence
    {Z : TopCat.{u}} (E : Set Z) (G : Z.Sheaf (Type u)) :
    (∀ (V B : Opens Z),
      ((pullbackPushforwardAdjunction (Type u) V.inclusion').unit.app G).hom.app
          (op B) ≫
        ((V.isOpenEmbedding.sheafPullbackIso (Type u)).hom.app G).hom.app
          (op ((Opens.map V.inclusion').obj B)) =
      G.obj.map (V.isOpenEmbedding.isOpenMap.adjunction.counit.app B).op) ∧
    (∀ (V : Opens Z) (h : E ⊆ V),
      ∃ c : (pullback (Type u) (subspaceToOpen E V h)).obj
          ((V.isOpenEmbedding.sheafPullback (Type u)).obj G) ≅
          (pullback (Type u) (subspaceInclusion E)).obj G,
        (∀ B : Opens (TopCat.of V),
          ((pullbackPushforwardAdjunction (Type u) (subspaceToOpen E V h)).unit.app
              ((V.isOpenEmbedding.sheafPullback (Type u)).obj G)).hom.app (op B) ≫
            c.hom.hom.app (op ((Opens.map (subspaceToOpen E V h)).obj B)) =
          subspaceOpenUnit (Type u) E G V h B) ∧
        (∀ c' : (pullback (Type u) (subspaceToOpen E V h)).obj
          ((V.isOpenEmbedding.sheafPullback (Type u)).obj G) ≅
          (pullback (Type u) (subspaceInclusion E)).obj G,
          (∀ B : Opens (TopCat.of V),
          ((pullbackPushforwardAdjunction (Type u) (subspaceToOpen E V h)).unit.app
              ((V.isOpenEmbedding.sheafPullback (Type u)).obj G)).hom.app (op B) ≫
            c'.hom.hom.app (op ((Opens.map (subspaceToOpen E V h)).obj B)) =
          subspaceOpenUnit (Type u) E G V h B) →
          c' = c) ∧
        openRestrictionGlobal (Type u) G V ≫
          ((pullbackPushforwardAdjunction (Type u) (subspaceToOpen E V h)).unit.app
            ((V.isOpenEmbedding.sheafPullback (Type u)).obj G)).hom.app (op ⊤) ≫
          c.hom.hom.app (op ⊤) = subspaceSectionMap (Type u) E G V h) ∧
    (∀ (W V : Opens Z) (hWV : W ≤ V) (hEW : E ⊆ W),
      G.obj.map (homOfLE hWV).op ≫ subspaceSectionMap (Type u) E G W hEW =
        subspaceSectionMap (Type u) E G V (fun x hx ↦ hWV (hEW hx))) := by
  exact restriction_coherence (Type u) E G

section Homeomorphism

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

end Homeomorphism

end TopCat.Sheaf

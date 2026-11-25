/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Topology.AbelianOpenExtensionByZero

/-! # A local section as an integer generator

Source: Stacks Project, Cohomology, Lemma 02UX, first paragraph.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace TopCat

open Sheaf

private theorem extensionSection_naturality {X : TopCat.{u}} (U : Opens X)
    (G H : TopCat.Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U)) (α : G ⟶ H)
    (V : Opens X) (hV : V ≤ U) :
    α.hom.app (op ((Opens.map U.inclusion').obj V)) ≫
        abelianOpenExtensionSection U H V hV =
      abelianOpenExtensionSection U G V hV ≫
        ((abelianOpenExtensionByZero U).map α).hom.app (op V) := by
  classical
  unfold abelianOpenExtensionSection
  erw [Category.assoc]
  have hn := congr_app (toSheafify_naturality (Opens.grothendieckTopology X)
    ((abelianOpenExtensionPresheaf U).map α)) (op V)
  change _ ≫ _ = _ ≫ _ at hn
  change _ = _ ≫ _ ≫ (sheafifyMap (Opens.grothendieckTopology X)
    ((abelianOpenExtensionPresheaf U).map α)).app (op V)
  erw [← hn, ← Category.assoc]
  rw [← Category.assoc]
  apply congrArg (fun f ↦ f ≫
    (toSheafify (Opens.grothendieckTopology X)
      ((abelianOpenExtensionPresheaf U).obj H)).app (op V))
  ext s
  dsimp [abelianOpenExtensionPresheaf, siteExtensionByZeroPresheaf,
    siteExtensionByZeroHom, siteExtensionByZeroHomApp, openSlicePresheaf]
  let : DecidableEq (V ⟶ U) := fun a b ↦ Classical.propDecidable (a = b)
  erw [DirectSum.toAddMonoid_of]
  rfl

private theorem extensionSection_counit {X : TopCat.{u}} (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X) (hV : V ≤ U) :
    abelianOpenExtensionSection U (abelianOpenRestriction U F) V hV ≫
        (abelianOpenCounit U F).hom.app (op V) =
      eqToHom (congrArg (fun W : Opens X ↦ F.obj.obj (op W))
        (openImage_preimage_eq U V hV)) := by
  classical
  unfold abelianOpenExtensionSection abelianOpenCounit
  erw [Category.assoc]
  have hc := congr_app (toSheafify_sheafifyLift (Opens.grothendieckTopology X)
    (abelianOpenPresheafCounit U F) F.property) (op V)
  change _ ≫ _ = _ at hc
  dsimp only [ObjectProperty.homMk_hom]
  erw [hc]
  ext s
  dsimp [abelianOpenPresheafCounit, abelianOpenCounitApp,
    openSlicePresheaf, abelianOpenRestriction, abelianOpenRestrictionPresheaf]
  let : DecidableEq (V ⟶ U) := fun a b ↦ Classical.propDecidable (a = b)
  exact DirectSum.toAddMonoid_of _ _ _


/-- Every section on an open defines an integer extension-by-zero map that lifts its germs.

Source: Stacks Project, Cohomology, Lemma 02UX, first paragraph; Sheaves, Lemma 00A5.
Proof: On the open subspace U, send an integer to its multiple of the restriction of s.
These maps commute with restriction and define a map from the constant presheaf.
Sheafify it, then apply extension by zero and compose with the restriction counit.
For each x in U, take the germ of the image of integer 1 under the sheafification unit
and the canonical extension section. Naturality of the unit and the counit section
formula show that its image is the germ of s. This works for s = 0; for empty U the
last assertion is vacuous. No compactness or basis hypothesis is required.
(blueprint: lem-sc-abelian-sheaf-local-integer-generator). -/
theorem abelianSheaf_local_integer_generator
    (X : TopCat.{u}) (F : X.Sheaf AddCommGrpCat.{u})
    (U : Opens X) (s : F.obj.obj (op U)) :
    ∃ f : (TopCat.Sheaf.abelianOpenExtensionByZero U).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ F,
      ∀ (x : X) (hx : x ∈ U),
        ∃ z : Presheaf.stalk (C := AddCommGrpCat.{u})
            (((TopCat.Sheaf.abelianOpenExtensionByZero U).obj
              ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
                AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).obj) x,
          (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom z =
            Presheaf.germ F.obj U x hx s := by
  classical
  let H := abelianOpenRestriction U F
  let Z := AddCommGrpCat.of (ULift.{u} ℤ)
  let J := Opens.grothendieckTopology ((Opens.toTopCat X).obj U)
  let P : TopCat.Presheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U) :=
    (Functor.const _).obj Z
  have image_le (V : Opens ((Opens.toTopCat X).obj U)) :
      U.isOpenEmbedding.functor.obj V ≤ U := by
    rintro y ⟨z, hz, rfl⟩
    exact z.property
  let η : P ⟶ H.obj :=
    { app := fun V ↦ AddCommGrpCat.ofHom
        { toFun := fun z ↦ z.down • F.obj.map (homOfLE (image_le V.unop)).op s
          map_zero' := by simp
          map_add' := by intros; simp [add_zsmul] }
      naturality := fun V W f ↦ by
        ext z
        dsimp [H, abelianOpenRestriction, abelianOpenRestrictionPresheaf, P]
        rw [map_zsmul, ← AddCommGrpCat.comp_apply, ← F.obj.map_comp]
        rfl }
  let G := (constantSheaf J AddCommGrpCat.{u}).obj Z
  let α : G ⟶ H := ObjectProperty.homMk (sheafifyLift J η H.property)
  let f := (abelianOpenExtensionByZero U).map α ≫ abelianOpenCounit U F
  refine ⟨f, ?_⟩
  intro x hx
  let V := (Opens.map U.inclusion').obj U
  let one : G.obj.obj (op V) := (toSheafify J P).app (op V) ⟨1⟩
  let z := abelianOpenExtensionSection U G U le_rfl one
  refine ⟨Presheaf.germ (((abelianOpenExtensionByZero U).obj G).obj) U x hx z, ?_⟩
  erw [Presheaf.stalkFunctor_map_germ_apply]
  change (Presheaf.germ F.obj U x hx) (((f.hom).app (op U)) z) = _
  suffices hf : ((f.hom).app (op U)) z = s by rw [hf]
  have hh := extensionSection_naturality U G H α U le_rfl
  have hc := extensionSection_counit U F U le_rfl
  have ha := congr_app (toSheafify_sheafifyLift J η H.property) (op V)
  change (toSheafify J P).app (op V) ≫ α.hom.app (op V) = η.app (op V) at ha
  have hv := openImage_preimage_eq U U le_rfl
  have hs :
      F.obj.map (homOfLE (image_le V)).op ≫
        eqToHom (congrArg (fun W : Opens X ↦ F.obj.obj (op W)) hv) =
        𝟙 (F.obj.obj (op U)) := by
    have ht := congrArg op hv
    have hm : F.obj.map (eqToHom ht) =
        eqToHom (congrArg (fun W : Opens X ↦ F.obj.obj (op W)) hv) :=
      eqToHom_map F.obj ht
    rw [← hm, ← F.obj.map_comp]
    have he : (homOfLE (image_le V)).op ≫ eqToHom (congrArg op hv) = 𝟙 (op U) :=
      Subsingleton.elim _ _
    rw [he, F.obj.map_id]
  change (abelianOpenExtensionSection U G U le_rfl ≫
    ((abelianOpenExtensionByZero U).map α).hom.app (op U) ≫
    (abelianOpenCounit U F).hom.app (op U)) one = s
  rw [← Category.assoc, ← hh, Category.assoc, hc]
  change ((toSheafify J P).app (op V) ≫ α.hom.app (op V) ≫ _) ⟨1⟩ = s
  rw [← Category.assoc]
  erw [ha]
  change (eqToHom (congrArg (fun W : Opens X ↦ F.obj.obj (op W)) hv))
    ((1 : ℤ) • F.obj.map (homOfLE (image_le V)).op s) = s
  rw [one_zsmul]
  change (F.obj.map (homOfLE (image_le V)).op ≫ _) s = s
  exact congrArg (fun g ↦ g s) hs

end TopCat

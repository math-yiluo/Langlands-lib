/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Topology.AbelianOpenExtensionByZero
import all WeilConjectures.Topology.AbelianSheafLocalIntegerGenerator

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

/-- Every section is the unit image of a map from the integer extension by zero.
Source: Stacks Project, Sheaves, Lemma 00A5, and Cohomology, Lemma 0A38,
https://stacks.math.columbia.edu/tag/00A5 and https://stacks.math.columbia.edu/tag/0A38
(blueprint: lem-sc-abelian-integer-extension-sections)

Proof: Given a section s of F on U, on each open of U send an integer z to
z times the restriction of s to the image open in X. These additive maps commute
with restriction. Sheafification gives a map from the constant integer sheaf to
F restricted to U. Apply extension by zero and compose with its restriction
counit. Naturality of the sheafification unit and the counit's formula on the
sole direct-sum summand show that the canonical unit maps to s. The construction
works for s = 0 and for empty U, without any compactness assumption. -/
theorem abelianIntegerExtension_section_lift
    (X : TopCat.{u}) (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X)
    (s : F.obj.obj (op U)) :
    ∃ f : (abelianOpenExtensionByZero U).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ F,
      f.hom.app (op U) (abelianOpenExtensionSection U
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) U le_rfl
        ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
          ((Functor.const (Opens ((Opens.toTopCat X).obj U))ᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u} ℤ)))).app
          (op ((Opens.map U.inclusion').obj U)) (ULift.up 1))) = s := by
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
  let V := (Opens.map U.inclusion').obj U
  let one : G.obj.obj (op V) := (toSheafify J P).app (op V) ⟨1⟩
  have hh := TopCat.extensionSection_naturality U G H α U le_rfl
  have hc := TopCat.extensionSection_counit U F U le_rfl
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


end TopCat.Sheaf

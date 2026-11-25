/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheaf
public import Mathlib.Topology.Sheaves.Sheafify

/-! # Extension by zero of abelian sheaves on an open subspace

Source: Stacks Project, Sheaves, Definition 00A4 and Lemma 00A5
(blueprint: def-sc-abelian-open-extension-by-zero).

The direct sum over inclusions is the existing slice-site construction: it has one
summand on opens contained in U and no summands on the other opens.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

namespace TopCat.Sheaf

/-- Pull a presheaf on the open subspace back to the slice of opens over U.
Source: Stacks, Definition 00A4 (blueprint: def-sc-abelian-open-extension-by-zero). -/
def openSlicePresheaf {X : TopCat.{u}} (U : Opens X)
    (G : TopCat.Presheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U)) :
    (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Over.forget U).op ⋙ (Opens.map U.inclusion').op ⋙ G

/-- Extension by zero before sheafification, using the existing slice-site direct sum.
Source: Stacks, Definition 00A4 (blueprint: def-sc-abelian-open-extension-by-zero). -/
def abelianOpenExtensionPresheaf {X : TopCat.{u}} (U : Opens X) :
    TopCat.Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U) ⥤
      TopCat.Presheaf AddCommGrpCat.{u} X :=
  TopCat.Sheaf.forget _ _ ⋙
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
      ((Over.forget U).op ⋙ (Opens.map U.inclusion').op) ⋙
    siteExtensionByZeroPresheaf U

/-- Extension by zero is sheafification of the extension-by-zero presheaf.
Source: Stacks, Definition 00A4 (blueprint: def-sc-abelian-open-extension-by-zero). -/
def abelianOpenExtensionByZero {X : TopCat.{u}} (U : Opens X) :
    TopCat.Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U) ⥤
      TopCat.Sheaf AddCommGrpCat.{u} X :=
  abelianOpenExtensionPresheaf U ⋙
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

/-- Literal restriction to the open subspace, by direct image of its opens.
Source: Stacks, Lemma 00A5 (blueprint: def-sc-abelian-open-extension-by-zero). -/
def abelianOpenRestrictionPresheaf {X : TopCat.{u}} (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    TopCat.Presheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U) :=
  U.isOpenEmbedding.functor.op ⋙ F.obj

/-- Restriction is a sheaf: any open cover in U maps to the same open cover in X;
existence and uniqueness of gluing follow from the sheaf condition for F.
Source: Stacks, Lemma 00A5 (blueprint: def-sc-abelian-open-extension-by-zero). -/
theorem abelianOpenRestriction_isSheaf {X : TopCat.{u}} (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
      (abelianOpenRestrictionPresheaf U F) := by
  exact TopCat.Presheaf.isSheaf_of_isOpenEmbedding U.isOpenEmbedding F.property

/-- Restriction as an abelian sheaf on the open subspace.
Source: Stacks, Lemma 00A5 (blueprint: def-sc-abelian-open-extension-by-zero). -/
def abelianOpenRestriction {X : TopCat.{u}} (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    TopCat.Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U) :=
  ⟨abelianOpenRestrictionPresheaf U F, abelianOpenRestriction_isSheaf U F⟩

/-- An open contained in U is unchanged by taking its preimage in U and its image in X.
Proof: the resulting open is V intersect U, which equals V by the inclusion.
Source: Stacks, Definition 00A4 (blueprint: def-sc-abelian-open-extension-by-zero). -/
theorem openImage_preimage_eq {X : TopCat.{u}} (U V : Opens X) (h : V ≤ U) :
    U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V) = V := by
  apply Opens.ext
  apply Set.ext
  intro x
  simp only [Topology.IsOpenEmbedding.functor, Opens.map, Opens.inclusion']
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, h hx⟩, hx, rfl⟩

open Classical in
/-- The presheaf counit is identity on the sole summand when V lies in U, and zero
when there is no inclusion V into U. Source: Stacks, Lemma 00A5
(blueprint: def-sc-abelian-open-extension-by-zero). -/
def abelianOpenCounitApp {X : TopCat.{u}} (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : (Opens X)ᵒᵖ) :
    ((abelianOpenExtensionPresheaf U).obj (abelianOpenRestriction U F)).obj V ⟶
      F.obj.obj V :=
  AddCommGrpCat.ofHom (DirectSum.toAddMonoid fun φ : V.unop ⟶ U ↦
    (eqToHom (congrArg (fun W : Opens X ↦ F.obj.obj (op W))
      (openImage_preimage_eq U V.unop φ.le))).hom)

/-- Naturality of the presheaf counit follows on each direct-sum injection from the
restriction law of F; the empty-sum case has the unique zero map.
Source: Stacks, Lemma 00A5 (blueprint: def-sc-abelian-open-extension-by-zero). -/
theorem abelianOpenCounitApp_naturality {X : TopCat.{u}} (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) {V W : (Opens X)ᵒᵖ} (a : V ⟶ W) :
    ((abelianOpenExtensionPresheaf U).obj (abelianOpenRestriction U F)).map a ≫
        abelianOpenCounitApp U F W =
      abelianOpenCounitApp U F V ≫ F.obj.map a := by
  classical
  let : DecidableEq (V.unop ⟶ U) := Classical.decEq _
  let : DecidableEq (W.unop ⟶ U) := Classical.decEq _
  apply AddCommGrpCat.hom_ext
  apply DirectSum.addHom_ext
  intro φ x
  simp only [abelianOpenExtensionPresheaf, Functor.comp_obj,
    siteExtensionByZeroPresheaf, siteExtensionByZeroPresheafObj,
    siteExtensionByZeroRestrict, abelianOpenCounitApp, AddCommGrpCat.hom_comp,
    AddCommGrpCat.hom_ofHom, AddMonoidHom.comp_apply]
  erw [DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of,
    DirectSum.toAddMonoid_of]
  -- The two paths are equal already in the thin category of opens.
  let b :
      op (U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V.unop)) ⟶
        op (U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj W.unop)) :=
    (U.isOpenEmbedding.functor.map ((Opens.map U.inclusion').map a.unop)).op
  have eV := congrArg op (openImage_preimage_eq U V.unop φ.le)
  have eW := congrArg op (openImage_preimage_eq U W.unop (a.unop ≫ φ).le)
  have h : b ≫ eqToHom eW = eqToHom eV ≫ a := Subsingleton.elim _ _
  have h' := congrArg (fun f ↦ F.obj.map f) h
  simp only [Functor.map_comp, eqToHom_map] at h'
  exact congrArg (fun f ↦ f.hom x) h'

/-- The presheaf map inducing the counit after sheafification.
Source: Stacks, Lemma 00A5 (blueprint: def-sc-abelian-open-extension-by-zero). -/
def abelianOpenPresheafCounit {X : TopCat.{u}} (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (abelianOpenExtensionPresheaf U).obj (abelianOpenRestriction U F) ⟶ F.obj where
  app V := abelianOpenCounitApp U F V
  naturality _ _ a := abelianOpenCounitApp_naturality U F a

/-- The counit j_! (F restricted to U) to F, induced by the presheaf counit.
Source: Stacks, Lemma 00A5 (blueprint: def-sc-abelian-open-extension-by-zero). -/
def abelianOpenCounit {X : TopCat.{u}} (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (abelianOpenExtensionByZero U).obj (abelianOpenRestriction U F) ⟶ F :=
  ObjectProperty.homMk
    (sheafifyLift (Opens.grothendieckTopology X) (abelianOpenPresheafCounit U F) F.property)

open Classical in
/-- The canonical inclusion of a section over V contained in U into j_! G(V).
Source: Stacks, Definition 00A4 (blueprint: def-sc-abelian-open-extension-by-zero). -/
def abelianOpenExtensionSection {X : TopCat.{u}} (U : Opens X)
    (G : TopCat.Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U))
    (V : Opens X) (h : V ≤ U) :
    G.obj.obj (op ((Opens.map U.inclusion').obj V)) ⟶
      ((abelianOpenExtensionByZero U).obj G).obj.obj (op V) :=
  AddCommGrpCat.ofHom (DirectSum.of
    (fun φ : V ⟶ U ↦ (openSlicePresheaf U G.obj).obj (op (Over.mk φ))) (homOfLE h)) ≫
    (toSheafify (Opens.grothendieckTopology X)
      ((abelianOpenExtensionPresheaf U).obj G)).app (op V)

end TopCat.Sheaf

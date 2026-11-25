/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Topology.AbelianOpenExtensionByZero
import WeilConjectures.Topology.AbelianOpenExtensionIntegerGermCoordinates
import WeilConjectures.Topology.AbelianOpenExtensionByZeroStalks
import Mathlib.Algebra.Category.Grp.Zero

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

/-- A map from the integer extension by zero is determined by the image of
its canonical integer-one section.
Source: Stacks Project, Sheaves, Lemma 00A5, and Cohomology, Lemma 0A38,
https://stacks.math.columbia.edu/tag/00A5 and https://stacks.math.columbia.edu/tag/0A38
(blueprint: lem-sc-abelian-integer-extension-hom-ext)

Proof: At a point of U, the canonical unit germ generates the source stalk:
its integer multiples give every stalk element by the existing integer-germ
coordinates theorem. Naturality carries that germ to the germ of the unit image
in F. Thus equality of the unit images gives equality on the generator, and
additivity gives equality on every stalk element. At a point outside U, the
source stalk is zero, so both stalk maps are the zero map. For a section on any
open of X, the two images therefore have the same germs at every point of that
open. Sheaf separation makes those images equal. Extensionality of additive
maps, natural transformations and sheaf maps gives equality of the original
morphisms. For empty U only the zero-stalk case is used. -/
theorem abelianIntegerExtension_unit_injective
    (X : TopCat.{u}) (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    Function.Injective (fun f : (abelianOpenExtensionByZero U).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ F ↦
      f.hom.app (op U) (abelianOpenExtensionSection U
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) U le_rfl
        ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
          ((Functor.const (Opens ((Opens.toTopCat X).obj U))ᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u} ℤ)))).app
          (op ((Opens.map U.inclusion').obj U)) (ULift.up 1)))) := by
  classical
  intro f g h
  let G := (constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
    AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))
  let E := (abelianOpenExtensionByZero U).obj G
  have stalk_eq (x : X) :
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom =
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map g.hom := by
    apply AddCommGrpCat.hom_ext
    ext t
    by_cases hx : x ∈ U
    · obtain ⟨z, hz, _⟩ :=
        abelianOpenExtension_integer_germ_coordinates X U U le_rfl x hx t
      rw [← hz, map_zsmul, map_zsmul]
      congr 1
      erw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
        TopCat.Presheaf.stalkFunctor_map_germ_apply]
      exact congrArg (fun a ↦ TopCat.Presheaf.germ F.obj U x hx a) h
    · obtain ⟨_, _, _, hzero, _⟩ := abelianOpenExtensionByZero_stalks X U
      have : Subsingleton (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) E.obj x) :=
        AddCommGrpCat.isZero_iff_subsingleton.mp (hzero G x hx)
      have ht : t = 0 := @Subsingleton.elim _ this _ _
      simp only [ht, map_zero]
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  ext s
  apply TopCat.Presheaf.section_ext F V.unop
  intro x hx
  have hs := congrArg (fun k ↦ k (TopCat.Presheaf.germ E.obj V.unop x hx s))
    (stalk_eq x)
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply] at hs
  exact hs

end TopCat.Sheaf

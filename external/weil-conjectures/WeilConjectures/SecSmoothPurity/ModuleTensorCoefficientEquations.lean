/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorExtensionEquation

/-! # Tensor squares for module coefficient change

Source: Stacks Project, sites-modules.tex, Tag 03EL, and
sites-cohomology.tex, Tag 07A4.
(blueprint: lem-pur-module-tensor-coefficient-equations)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe w uC vC uD vD uE vE u v u' v'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.CochainPullback
set_option autoImplicit false
set_option linter.checkUnivs false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}

private theorem mate_pair
    {A : Type u} [Category.{v} A] [MonoidalCategory A]
    {B : Type u'} [Category.{v'} B] [MonoidalCategory B]
    (L : A ⥤ B) (U : B ⥤ A) (adj : L ⊣ U)
    (mu : ∀ X Y : A, L.obj (X ⊗ Y) ⟶ L.obj X ⊗ L.obj Y)
    (hn : ∀ {X X' Y Y' : A} (a : X ⟶ X') (b : Y ⟶ Y'),
      L.map (a ⊗ₘ b) ≫ mu X' Y' = mu X Y ≫ (L.map a ⊗ₘ L.map b))
    (X Y : A) (P Q : B) (a : X ⟶ U.obj P) (b : Y ⟶ U.obj Q) :
    (a ⊗ₘ b) ≫ adj.homEquiv _ _
      (mu (U.obj P) (U.obj Q) ≫ (adj.counit.app P ⊗ₘ adj.counit.app Q)) =
      adj.unit.app (X ⊗ Y) ≫ U.map
        (mu X Y ≫ ((L.map a ≫ adj.counit.app P) ⊗ₘ
          (L.map b ≫ adj.counit.app Q))) := by
  rw [Adjunction.homEquiv_unit, ← Category.assoc, ← adj.unit_naturality]
  rw [Category.assoc, ← U.map_comp, ← Category.assoc, hn]
  simp only [Category.assoc, tensorHom_comp_tensorHom]

private theorem transition_square
    {A : Type u} [Category.{v} A] [MonoidalCategory A]
    {B : Type u'} [Category.{v'} B] [MonoidalCategory B]
    (L : A ⥤ B) (U : B ⥤ A) (adj : L ⊣ U)
    (mu : ∀ X Y : A, L.obj (X ⊗ Y) ⟶ L.obj X ⊗ L.obj Y)
    (hn : ∀ {X X' Y Y' : A} (a : X ⟶ X') (b : Y ⟶ Y'),
      L.map (a ⊗ₘ b) ≫ mu X' Y' = mu X Y ≫ (L.map a ⊗ₘ L.map b))
    (X Y Z : A) (P Q W : B)
    (bP : P ≅ L.obj X) (bQ : Q ≅ L.obj Y) (bW : W ≅ L.obj Z)
    (alpha : Z ⟶ X ⊗ Y) (nu : W ⟶ P ⊗ Q)
    (h : nu ≫ (bP.hom ⊗ₘ bQ.hom) = bW.hom ≫ L.map alpha ≫ mu X Y) :
    alpha ≫ ((adj.unit.app X ≫ U.map bP.inv) ⊗ₘ
      (adj.unit.app Y ≫ U.map bQ.inv)) ≫ adj.homEquiv _ _
        (mu (U.obj P) (U.obj Q) ≫ (adj.counit.app P ⊗ₘ adj.counit.app Q)) =
      (adj.unit.app Z ≫ U.map bW.inv) ≫ U.map nu := by
  have hp : L.map (adj.unit.app X ≫ U.map bP.inv) ≫ adj.counit.app P = bP.inv := by
    exact (adj.homEquiv _ _).symm_apply_apply bP.inv
  have hq : L.map (adj.unit.app Y ≫ U.map bQ.inv) ≫ adj.counit.app Q = bQ.inv := by
    exact (adj.homEquiv _ _).symm_apply_apply bQ.inv
  rw [mate_pair L U adj mu hn, hp, hq]
  rw [← Category.assoc, ← adj.unit_naturality, Category.assoc, ← U.map_comp]
  simp only [Category.assoc, ← U.map_comp]
  congr 1
  apply congrArg U.map
  apply (cancel_epi bW.hom).1
  apply (cancel_mono (bP.hom ⊗ₘ bQ.hom)).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc, tensorHom_comp_tensorHom,
    Iso.inv_hom_id, id_tensorHom_id, Category.comp_id]
  exact h.symm

end CategoryTheory.CochainPullback

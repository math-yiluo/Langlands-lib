/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
/-! # Ordinary complex tensor associativity data

Source: Stacks 07A4 and 0FPT.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe c v r wb d vd s wa b vb a va
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

/-- The ordinary total associator is fixed by its formula on triple tensor generators.
Source: Stacks 07A4; (blueprint: def-coef-complex-tensor-associativity). -/
def CoefficientComplexAssociatorFormula
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    (P Q N : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (a : (coefficientTotalTensor.{r, c, v} J R).obj
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q), N) ≅
      (coefficientTotalTensor.{r, c, v} J R).obj
        (P, (coefficientTotalTensor.{r, c, v} J R).obj (Q, N))) : Prop :=
  ∀ (p q t pq qt n : ℤ) (hpq : p + q = pq) (hqt : q + t = qt)
    (hn : pq + t = n) (hn' : p + qt = n) (V : Cᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) (z : (N.X t).val.obj V),
    (a.hom.f n).val.app V
      (coefficientTensorGenerator.{r, c, v} J R
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) N pq t n hn V
        (coefficientTensorGenerator.{r, c, v} J R P Q p q pq hpq V x y) z) =
    coefficientTensorGenerator.{r, c, v} J R P
      ((coefficientTotalTensor.{r, c, v} J R).obj (Q, N)) p qt n hn' V x
      (coefficientTensorGenerator.{r, c, v} J R Q N q t qt hqt V y z)

/-- Associativity before localization, for total associators fixed on tensor generators.
Source: Stacks 07A4; (blueprint: def-coef-complex-tensor-associativity). -/
def CoefficientComplexTensorAssociativity
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
    [HasSheafify J' AddCommGrpCat.{max d vd s}]
    [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
    (R' : Sheaf J' CommRingCat.{max d vd s})
    (K : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ ⥤
      CochainComplex (RingedTensorModules.{d, vd, s} J' R') ℤ)
    (κ : coefficientTotalTensor.{r, c, v} J R ⋙ K ≅
      K.prod K ⋙ coefficientTotalTensor.{s, d, vd} J' R') : Prop :=
  ∀ (P Q N : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (a : (coefficientTotalTensor.{r, c, v} J R).obj
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q), N) ≅
      (coefficientTotalTensor.{r, c, v} J R).obj
        (P, (coefficientTotalTensor.{r, c, v} J R).obj (Q, N)))
    (b : (coefficientTotalTensor.{s, d, vd} J' R').obj
        ((coefficientTotalTensor.{s, d, vd} J' R').obj (K.obj P, K.obj Q), K.obj N) ≅
      (coefficientTotalTensor.{s, d, vd} J' R').obj
        (K.obj P, (coefficientTotalTensor.{s, d, vd} J' R').obj (K.obj Q, K.obj N))),
    CoefficientComplexAssociatorFormula J R P Q N a →
    CoefficientComplexAssociatorFormula J' R' (K.obj P) (K.obj Q) (K.obj N) b →
    K.map a.hom ≫ κ.hom.app
        (P, (coefficientTotalTensor.{r, c, v} J R).obj (Q, N)) ≫
        (coefficientTotalTensor.{s, d, vd} J' R').map
          (Prod.mkHom (𝟙 (K.obj P)) (κ.hom.app (Q, N))) =
      κ.hom.app ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q), N) ≫
        (coefficientTotalTensor.{s, d, vd} J' R').map
          (Prod.mkHom (κ.hom.app (P, Q)) (𝟙 (K.obj N))) ≫ b.hom

attribute [local implicit_reducible] CategoryTheory.uniformProd

private theorem left_square {B : Type b} [Category.{vb} B] [MonoidalCategory B]
    {A : Type a} [Category.{va} A] [MonoidalCategory A]
    (F : B ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    {X Y Z V W : B} {X' Y' Z' V' W' : A}
    (i : V ⟶ X ⊗ Y) (j : W ⟶ V ⊗ Z)
    (eX : F.obj X ⟶ X') (eY : F.obj Y ⟶ Y') (eZ : F.obj Z ⟶ Z')
    (eV : F.obj V ⟶ V') (eW : F.obj W ⟶ W')
    (i' : V' ⟶ X' ⊗ Y') (j' : W' ⟶ V' ⊗ Z')
    (hi : F.map i ≫ μ.hom.app (X, Y) ≫ (eX ⊗ₘ eY) = eV ≫ i')
    (hj : F.map j ≫ μ.hom.app (V, Z) ≫ (eV ⊗ₘ eZ) = eW ≫ j') :
    F.map (j ≫ (i ▷ Z)) ≫ μ.hom.app (X ⊗ Y, Z) ≫
        (μ.hom.app (X, Y) ▷ F.obj Z) ≫ ((eX ⊗ₘ eY) ⊗ₘ eZ) =
      eW ≫ j' ≫ (i' ▷ Z') := by
  with_unfolding_all
    dsimp only [Functor.comp_obj, Functor.prod_obj] at *
    have hn := μ.hom.naturality (X := (V, Z)) (Y := (X ⊗ Y, Z)) (i, 𝟙 Z)
    change F.map (i ⊗ₘ 𝟙 Z) ≫ μ.hom.app (X ⊗ Y, Z) =
      μ.hom.app (V, Z) ≫ (F.map i ⊗ₘ F.map (𝟙 Z)) at hn
    simp only [F.map_id, tensorHom_id] at hn
    calc
      _ = F.map j ≫ μ.hom.app (V, Z) ≫
          ((F.map i ≫ μ.hom.app (X, Y) ≫ (eX ⊗ₘ eY)) ⊗ₘ eZ) := by
        simp only [F.map_comp, Category.assoc]
        rw [reassoc_of% hn]
        simp only [← tensorHom_id, tensorHom_comp_tensorHom,
          Category.id_comp]
        erw [Category.id_comp]
      _ = F.map j ≫ μ.hom.app (V, Z) ≫ ((eV ≫ i') ⊗ₘ eZ) := by rw [hi]
      _ = (F.map j ≫ μ.hom.app (V, Z) ≫ (eV ⊗ₘ eZ)) ≫ (i' ▷ Z') := by
        simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, Category.assoc]
      _ = _ := by rw [hj]; simp only [Category.assoc]

private theorem right_square {B : Type b} [Category.{vb} B] [MonoidalCategory B]
    {A : Type a} [Category.{va} A] [MonoidalCategory A]
    (F : B ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    {X Y Z V W : B} {X' Y' Z' V' W' : A}
    (i : V ⟶ Y ⊗ Z) (j : W ⟶ X ⊗ V)
    (eX : F.obj X ⟶ X') (eY : F.obj Y ⟶ Y') (eZ : F.obj Z ⟶ Z')
    (eV : F.obj V ⟶ V') (eW : F.obj W ⟶ W')
    (i' : V' ⟶ Y' ⊗ Z') (j' : W' ⟶ X' ⊗ V')
    (hi : F.map i ≫ μ.hom.app (Y, Z) ≫ (eY ⊗ₘ eZ) = eV ≫ i')
    (hj : F.map j ≫ μ.hom.app (X, V) ≫ (eX ⊗ₘ eV) = eW ≫ j') :
    F.map (j ≫ (X ◁ i)) ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (F.obj X ◁ μ.hom.app (Y, Z)) ≫ (eX ⊗ₘ (eY ⊗ₘ eZ)) =
      eW ≫ j' ≫ (X' ◁ i') := by
  with_unfolding_all
    dsimp only [Functor.comp_obj, Functor.prod_obj] at *
    have hn := μ.hom.naturality (X := (X, V)) (Y := (X, Y ⊗ Z)) (𝟙 X, i)
    change F.map (𝟙 X ⊗ₘ i) ≫ μ.hom.app (X, Y ⊗ Z) =
      μ.hom.app (X, V) ≫ (F.map (𝟙 X) ⊗ₘ F.map i) at hn
    simp only [F.map_id, id_tensorHom] at hn
    calc
      _ = F.map j ≫ μ.hom.app (X, V) ≫
          (eX ⊗ₘ (F.map i ≫ μ.hom.app (Y, Z) ≫ (eY ⊗ₘ eZ))) := by
        simp only [F.map_comp, Category.assoc]
        rw [reassoc_of% hn]
        simp only [← id_tensorHom, tensorHom_comp_tensorHom,
          Category.id_comp]
        erw [Category.id_comp]
      _ = F.map j ≫ μ.hom.app (X, V) ≫ (eX ⊗ₘ (eV ≫ i')) := by rw [hi]
      _ = (F.map j ≫ μ.hom.app (X, V) ≫ (eX ⊗ₘ eV)) ≫ (X' ◁ i') := by
        simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.assoc]
      _ = _ := by rw [hj]; simp only [Category.assoc]

private theorem associativity_transport
    {B : Type b} [Category.{vb} B] [MonoidalCategory B]
    {A : Type a} [Category.{va} A] [MonoidalCategory A]
    (F : B ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    {X Y Z V W : B} {X' Y' Z' V' W' : A}
    (l : V ≅ (X ⊗ Y) ⊗ Z) (r : W ≅ X ⊗ (Y ⊗ Z)) (a : V ⟶ W)
    (l' : V' ⟶ (X' ⊗ Y') ⊗ Z') (r' : W' ⟶ X' ⊗ (Y' ⊗ Z')) (a' : V' ⟶ W')
    (eX : F.obj X ≅ X') (eY : F.obj Y ≅ Y') (eZ : F.obj Z ≅ Z')
    (eV : F.obj V ⟶ V') (eW : F.obj W ⟶ W')
    (hB : l.hom ≫ (α_ X Y Z).hom = a ≫ r.hom)
    (hA : l' ≫ (α_ X' Y' Z').hom = a' ≫ r')
    (hL : F.map l.hom ≫ μ.hom.app (X ⊗ Y, Z) ≫
      (μ.hom.app (X, Y) ▷ F.obj Z) ≫ ((eX.hom ⊗ₘ eY.hom) ⊗ₘ eZ.hom) = eV ≫ l')
    (hR : F.map r.hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
      (F.obj X ◁ μ.hom.app (Y, Z)) ≫ (eX.hom ⊗ₘ (eY.hom ⊗ₘ eZ.hom)) = eW ≫ r')
    (hC : F.map a ≫ eW = eV ≫ a') :
    F.map (α_ X Y Z).hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (F.obj X ◁ μ.hom.app (Y, Z)) =
      μ.hom.app (X ⊗ Y, Z) ≫ (μ.hom.app (X, Y) ▷ F.obj Z) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom := by
  with_unfolding_all
    apply (cancel_epi (F.map l.hom)).1
    apply (cancel_mono (eX.hom ⊗ₘ (eY.hom ⊗ₘ eZ.hom))).1
    calc
      _ = F.map a ≫ F.map r.hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
          (F.obj X ◁ μ.hom.app (Y, Z)) ≫ (eX.hom ⊗ₘ (eY.hom ⊗ₘ eZ.hom)) := by
        rw [← F.map_comp_assoc, hB, F.map_comp]
        simp only [Category.assoc]
      _ = F.map a ≫ eW ≫ r' := by rw [hR]
      _ = eV ≫ a' ≫ r' := by rw [reassoc_of% hC]
      _ = eV ≫ l' ≫ (α_ X' Y' Z').hom := by rw [hA]
      _ = F.map l.hom ≫ μ.hom.app (X ⊗ Y, Z) ≫
          (μ.hom.app (X, Y) ▷ F.obj Z) ≫ ((eX.hom ⊗ₘ eY.hom) ⊗ₘ eZ.hom) ≫
            (α_ X' Y' Z').hom := by rw [reassoc_of% hL]
      _ = _ := by
        erw [associator_naturality]
        simp only [Category.assoc]
        rfl

end WeilConjectures

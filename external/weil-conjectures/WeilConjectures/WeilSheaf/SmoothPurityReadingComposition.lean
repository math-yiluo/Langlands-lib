/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.NatIso

/-! # Composing reduction and site-reading squares -/

@[expose] public section

namespace CategoryTheory

/-- A reduction square and a reading square compose through the natural pullback
comparison. The functor arguments keep all source and target objects explicit. -/
lemma purity_reading_composition
    {C₀ C D₀ D : Type*} [Category C₀] [Category C] [Category D₀] [Category D]
    (P : C₀ ⥤ C) (F₀ : C₀ ⥤ D₀) (F : C ⥤ D) (Q : D₀ ⥤ D)
    (α : P ⋙ F ≅ F₀ ⋙ Q)
    {A B : C₀} {V W R S : C} {T₀ : D₀} {T : D}
    (u : P.obj A ⟶ V) (v : V ⟶ W) (rX : W ≅ S) (rY : A ≅ B)
    (q₁ : P.obj B ⟶ R) (q₂ : R ⟶ S)
    (bX : F.obj S ≅ T) (bY : F₀.obj B ≅ T₀) (w : Q.obj T₀ ⟶ T)
    (hred : u ≫ v ≫ rX.hom = P.map rY.hom ≫ q₁ ≫ q₂)
    (hread : F.map q₁ ≫ F.map q₂ ≫ bX.hom =
      α.hom.app B ≫ Q.map bY.hom ≫ w) :
    F.map u ≫ F.map v ≫ (F.mapIso rX ≪≫ bX).hom =
      α.hom.app A ≫ Q.map (F₀.mapIso rY ≪≫ bY).hom ≫ w := by
  have hm := congrArg F.map hred
  have hn := α.hom.naturality rY.hom
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp] at hm
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hm, hread, reassoc_of% hn]

/-- Retain the initial coefficient-comparison component, including its composite
source functor, in the resulting equation. -/
lemma purity_reading_composition_component
    {B₀ C₀ C D₀ D : Type*} [Category B₀] [Category C₀] [Category C]
    [Category D₀] [Category D]
    (P : C₀ ⥤ C) (F₀ : C₀ ⥤ D₀) (F : C ⥤ D) (Q : D₀ ⥤ D)
    (α : P ⋙ F ≅ F₀ ⋙ Q) (E : B₀ ⥤ C₀) (J : B₀ ⥤ C)
    (u : E ⋙ P ⟶ J) (M : B₀)
    {B : C₀} {W R S : C} {T₀ : D₀} {T : D}
    (v : J.obj M ⟶ W) (rX : W ≅ S) (rY : E.obj M ≅ B)
    (q₁ : P.obj B ⟶ R) (q₂ : R ⟶ S)
    (bX : F.obj S ≅ T) (bY : F₀.obj B ≅ T₀) (w : Q.obj T₀ ⟶ T)
    (hred : u.app M ≫ v ≫ rX.hom = P.map rY.hom ≫ q₁ ≫ q₂)
    (hread : F.map q₁ ≫ F.map q₂ ≫ bX.hom =
      α.hom.app B ≫ Q.map bY.hom ≫ w) :
    F.map (u.app M) ≫ F.map v ≫ (F.mapIso rX ≪≫ bX).hom =
      α.hom.app (E.obj M) ≫ Q.map (F₀.mapIso rY ≪≫ bY).hom ≫ w :=
  purity_reading_composition P F₀ F Q α (u.app M) v rX rY q₁ q₂ bX bY w hred hread

/-- Keep the named reading isomorphisms in the conclusion, so applications need
only compare isomorphisms before taking their components. -/
lemma purity_reading_composition_named
    {B₀ C₀ C D₀ D : Type*} [Category B₀] [Category C₀] [Category C]
    [Category D₀] [Category D]
    (P : C₀ ⥤ C) (F₀ : C₀ ⥤ D₀) (F : C ⥤ D) (Q : D₀ ⥤ D)
    (α : P ⋙ F ≅ F₀ ⋙ Q) (E : B₀ ⥤ C₀) (J : B₀ ⥤ C)
    (u : E ⋙ P ⟶ J) (M : B₀)
    {B : C₀} {W R S : C} {T₀ : D₀} {T : D}
    (v : J.obj M ⟶ W) (rX : W ≅ S) (rY : E.obj M ≅ B)
    (q₁ : P.obj B ⟶ R) (q₂ : R ⟶ S)
    (bX : F.obj S ≅ T) (bY : F₀.obj B ≅ T₀) (w : Q.obj T₀ ⟶ T)
    (tX : F.obj W ≅ T) (tY : F₀.obj (E.obj M) ≅ T₀)
    (htX : tX = F.mapIso rX ≪≫ bX) (htY : tY = F₀.mapIso rY ≪≫ bY)
    (hred : u.app M ≫ v ≫ rX.hom = P.map rY.hom ≫ q₁ ≫ q₂)
    (hread : F.map q₁ ≫ F.map q₂ ≫ bX.hom =
      α.hom.app B ≫ Q.map bY.hom ≫ w) :
    F.map (u.app M) ≫ F.map v ≫ tX.hom =
      α.hom.app (E.obj M) ≫ Q.map tY.hom ≫ w := by
  subst tX tY
  exact purity_reading_composition_component P F₀ F Q α E J u M v rX rY
    q₁ q₂ bX bY w hred hread

end CategoryTheory

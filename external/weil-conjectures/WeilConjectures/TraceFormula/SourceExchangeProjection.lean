/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.LeftProjectionComp
public import WeilConjectures.PoincareDuality.ProjectionFormulaCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalShift
public import WeilConjectures.TraceFormula.SourceExchangeTransport

/-!

# Left projection morphisms of compactly supported direct images

The left projection morphisms `A ⊗ Rx_! T ⟶ Rx_! (Lx^* A ⊗ T)` of the compactly supported direct
images compose (`ProEtale.CondensedRing.leftProjection_lowerShriek_comp`), and for a proper `g`
the left projection morphism at the unit is the unit of `Lg^* ⊣ Rg_*`
(`ProEtale.CondensedRing.leftProjection_lowerShriek_unit`). These are steps of the class of the
coefficient pushforward (blueprint `theorem-proper-pushforward-lefschetz-verdier--1`, Step 2).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

lemma Adjunction.map_comp_mateEquiv_app_comp_counit {C₁ C₂ D₁ D₂ : Type*} [Category C₁]
    [Category C₂] [Category D₁] [Category D₂] {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {L₂ : C₂ ⥤ D₂}
    {R₂ : D₂ ⥤ C₂} {G : C₁ ⥤ C₂} {H : D₁ ⥤ D₂} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) {A : C₂} {B : C₁} {Xd : D₁} (γ : A ⟶ G.obj B) (u : B ⟶ R₁.obj Xd) :
    L₂.map (γ ≫ G.map u ≫ (mateEquiv adj₁ adj₂ α).app Xd) ≫ adj₂.counit.app (H.obj Xd) =
      L₂.map γ ≫ α.app B ≫ H.map (L₁.map u ≫ adj₁.counit.app Xd) := by
  have h₁ := mateEquiv_counit adj₁ adj₂ α Xd
  have h₂ := α.naturality u
  simp only [Functor.comp_map] at h₁ h₂
  simp only [Functor.map_comp, Category.assoc, h₁, reassoc_of% h₂]

@[reassoc]
lemma Functor.map_whiskerLeft_hom_app_comp_map_whiskerLeft_inv_app {B C D : Type*} [Category B]
    [Category C] [Category D] [MonoidalCategory C] (F : C ⥤ D) (A : C) {G H : B ⥤ C}
    (e : G ≅ H) (Z : B) : F.map (A ◁ e.hom.app Z) ≫ F.map (A ◁ e.inv.app Z) = 𝟙 _ := by
  rw [← F.map_comp, ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id_app,
    MonoidalCategory.whiskerLeft_id, F.map_id]

lemma Functor.map_map_comp_map_map_assoc_of_eq {B C D : Type*} [Category B] [Category C]
    [Category D] (F : C ⥤ D) (G : B ⥤ C) {X Y Y' Z : B} {x : X ⟶ Y} {y : Y ⟶ Z} {x' : X ⟶ Y'}
    {y' : Y' ⟶ Z} (h : x ≫ y = x' ≫ y') {W : D} (k : F.obj (G.obj Z) ⟶ W) :
    F.map (G.map x) ≫ F.map (G.map y) ≫ k = F.map (G.map x') ≫ F.map (G.map y') ≫ k := by
  rw [← F.map_comp_assoc, ← G.map_comp, h, G.map_comp, F.map_comp_assoc]

lemma Functor.map_comp₃_assoc_of_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Y' Z Z' W : C} {a : X ⟶ Y} {b : Y ⟶ Z} {c : Z ⟶ W} {a' : X ⟶ Y'} {b' : Y' ⟶ Z'}
    {c' : Z' ⟶ W} (h : a ≫ b ≫ c = a' ≫ b' ≫ c') {V : D} (k : F.obj W ⟶ V) :
    F.map a ≫ F.map b ≫ F.map c ≫ k = F.map a' ≫ F.map b' ≫ F.map c' ≫ k := by
  simpa only [Functor.map_comp, Category.assoc] using congrArg (fun t ↦ F.map t ≫ k) h

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Generic

variable {C Y : Over (Spec (.of k))} [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
  [IsSeparated C.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

lemma lowerShriek_map_comp_eqToHom_comp_counit {s t : C ⟶ Y} (h : t = s)
    {N : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj
        ℓ⟧}
    (w : N ⟶ (boundedConstructibleUpperShriek ℓ t).obj M) :
    (boundedConstructibleLowerShriek ℓ s).map
        (w ≫ eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperShriek ℓ r).obj M) h)) ≫
      (boundedConstructibleUpperShriekAdjunction ℓ s).counit.app M =
    eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerShriek ℓ r).obj N) h.symm) ≫
      (boundedConstructibleLowerShriek ℓ t).map w ≫
      (boundedConstructibleUpperShriekAdjunction ℓ t).counit.app M := by
  subst h
  simp

lemma lowerShriek_map_comp_comp_eqToHom_comp_counit {s t : C ⟶ Y} (h : t = s)
    {N N' : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (v : N' ⟶ N)
    (w : N ⟶ (boundedConstructibleUpperShriek ℓ t).obj M) :
    (boundedConstructibleLowerShriek ℓ s).map
        (v ≫ w ≫ eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperShriek ℓ r).obj M) h)) ≫
      (boundedConstructibleUpperShriekAdjunction ℓ s).counit.app M =
    (boundedConstructibleLowerShriek ℓ s).map v ≫
      eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerShriek ℓ r).obj N) h.symm) ≫
      (boundedConstructibleLowerShriek ℓ t).map w ≫
      (boundedConstructibleUpperShriekAdjunction ℓ t).counit.app M := by
  subst h
  simp

variable {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom]

/-- The left projection morphisms of the compactly supported direct images compose. -/
lemma leftProjection_lowerShriek_comp (x : C ⟶ Y) (y : Y ⟶ Z)
    (M : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
        (T : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ (x ≫ y)) M T ≫
        (boundedConstructibleLowerShriek ℓ (x ≫ y)).map
          ((boundedConstructibleUpperStarComp _ ℓ x y).hom.app M ▷ T) =
      M ◁ (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).hom.app T ≫
        Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ y) M
          ((boundedConstructibleLowerShriek ℓ x).obj T) ≫
        (boundedConstructibleLowerShriek ℓ y).map
          (Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ x)
            ((boundedConstructibleUpperStar _ ℓ y).obj M) T) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).inv.app _ :=
  Verdier.leftProjection_comp (boundedConstructibleExceptionalProjection ℓ x)
    (boundedConstructibleExceptionalProjection ℓ y)
    (boundedConstructibleExceptionalProjection ℓ (x ≫ y))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y)
    (boundedConstructibleUpperStarComp _ ℓ x y)
    (fun _ _ ↦ boundedConstructible_braiding_hom_braiding_hom _ _)
    (fun T M ↦ exceptionalProjection_comp ℓ x y T M) M T

/-- The left projection morphism of a proper morphism at the unit point is the unit of the
adjunction. -/
lemma leftProjection_lowerShriek_unit (g : C ⟶ Y) [IsProper g.left]
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    M ◁ ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app (𝟙_ _) ≫
        (boundedConstructibleLowerStar ℓ g).map
          (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ g)).inv ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app (𝟙_ _)) ≫
      Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ g) M (𝟙_ _) =
    (ρ_ M).hom ≫ (boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app M ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app _ ≫
      (boundedConstructibleLowerShriek ℓ g).map (ρ_ _).inv :=
  Verdier.leftProjection_unit (boundedConstructibleUpperStar _ ℓ g)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ g)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g)
    (boundedConstructibleExceptionalProjection ℓ g)
    (fun T M ↦ upperStar_map_exceptionalProjection_comp_counit ℓ g T M)
    (fun A B ↦ boundedConstructibleUpperStar_map_braiding_hom_δ ℓ g A B)
    (fun _ _ ↦ boundedConstructible_braiding_hom_braiding_hom _ _) M

-- the compactly supported direct images are unfolded in the defeq checks
/-- The left projection morphism of a composite `g ≫ b` with `g` proper at the unit point. -/
lemma leftProjection_lowerShriek_comp_unit (g : C ⟶ Y) [IsProper g.left] (b : Y ⟶ Z)
    (M : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    M ◁ (boundedConstructibleLowerShriek ℓ b).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app (𝟙_ _) ≫
          (boundedConstructibleLowerStar ℓ g).map
            (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ g)).inv ≫
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app (𝟙_ _)) ≫
      M ◁ (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv.app (𝟙_ _) ≫
      Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ (g ≫ b)) M (𝟙_ _) =
    Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ b) M (𝟙_ _) ≫
      (boundedConstructibleLowerShriek ℓ b).map
        ((ρ_ ((boundedConstructibleUpperStar _ ℓ b).obj M)).hom ≫
          (boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app
            ((boundedConstructibleUpperStar _ ℓ b).obj M) ≫
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app
            ((boundedConstructibleUpperStar _ ℓ g).obj
                ((boundedConstructibleUpperStar _ ℓ b).obj M)) ≫
          (boundedConstructibleLowerShriek ℓ g).map (ρ_ ((boundedConstructibleUpperStar _ ℓ g).obj
            ((boundedConstructibleUpperStar _ ℓ b).obj M))).inv) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv.app
        ((boundedConstructibleUpperStar _ ℓ g).obj ((boundedConstructibleUpperStar _ ℓ b).obj M) ⊗
          𝟙_ _) ≫
      (boundedConstructibleLowerShriek ℓ (g ≫ b)).map
        ((boundedConstructibleUpperStarComp _ ℓ g b).inv.app M ▷ _) := by
  have hc := leftProjection_lowerShriek_comp ℓ g b M (𝟙_ _)
  have hc' : Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ (g ≫ b)) M
      (𝟙_ _) =
      M ◁ (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).hom.app (𝟙_ _) ≫
        Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ b) M
          ((boundedConstructibleLowerShriek ℓ g).obj (𝟙_ _)) ≫
        (boundedConstructibleLowerShriek ℓ b).map
          (Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ g)
            ((boundedConstructibleUpperStar _ ℓ b).obj M) (𝟙_ _)) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv.app _ ≫
        (boundedConstructibleLowerShriek ℓ (g ≫ b)).map
          ((boundedConstructibleUpperStarComp _ ℓ g b).inv.app M ▷ _) := by
    simp only [← reassoc_of% hc, ← Functor.map_comp, ← comp_whiskerRight, Iso.hom_inv_id_app,
      id_whiskerRight]
    exact (Category.comp_id _).symm.trans (congrArg _ (CategoryTheory.Functor.map_id _ _).symm)
  have hn := Verdier.leftProjection_naturality (boundedConstructibleExceptionalProjection ℓ b) M
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app (𝟙_ _) ≫
      (boundedConstructibleLowerStar ℓ g).map
        (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ g)).inv ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app (𝟙_ _))
  have hu := leftProjection_lowerShriek_unit ℓ g ((boundedConstructibleUpperStar _ ℓ b).obj M)
  have hi : M ◁ (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv.app (𝟙_ _) ≫
      M ◁ (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).hom.app (𝟙_ _) = 𝟙 _ := by
    rw [← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id_app, MonoidalCategory.whiskerLeft_id]
  simp only [hc']
  simp only [← Category.assoc (M ◁ (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv.app
    (𝟙_ _))]
  simp only [hi, Category.id_comp, reassoc_of% hn, ← Functor.map_comp_assoc, hu]

-- the compactly supported direct images are unfolded in the defeq checks
/-- `leftProjection_lowerShriek_comp_unit` for a composite `s = g ≫ b`, mapped by a functor. -/
lemma map_leftProjection_lowerShriek_comp_unit (g : C ⟶ Y) [IsProper g.left] (b : Y ⟶ Z)
    {s : C ⟶ Z} (h : g ≫ b = s) (M : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) {D : Type*}
    [Category D] (F : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ D) {W : D}
    (k : F.obj ((boundedConstructibleLowerShriek ℓ s).obj
      ((boundedConstructibleUpperStar _ ℓ s).obj M ⊗ 𝟙_ _)) ⟶ W) :
    F.map (M ◁ (boundedConstructibleLowerShriek ℓ b).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app (𝟙_ _))) ≫
      F.map (M ◁ (boundedConstructibleLowerShriek ℓ b).map
        ((boundedConstructibleLowerStar ℓ g).map
          (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ g)).inv)) ≫
      F.map (M ◁ (boundedConstructibleLowerShriek ℓ b).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app (𝟙_ _))) ≫
      F.map (M ◁ (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv.app (𝟙_ _)) ≫
      F.map (M ◁ eqToHom (by rw [h])) ≫
      F.map (Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ s) M (𝟙_ _)) ≫
      k =
    F.map (Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ b) M (𝟙_ _)) ≫
      F.map ((boundedConstructibleLowerShriek ℓ b).map (ρ_
          ((boundedConstructibleUpperStar _ ℓ b).obj M)).hom) ≫
      F.map ((boundedConstructibleLowerShriek ℓ b).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app
            ((boundedConstructibleUpperStar _ ℓ b).obj M))) ≫
      F.map ((boundedConstructibleLowerShriek ℓ b).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app
          ((boundedConstructibleUpperStar _ ℓ g).obj
              ((boundedConstructibleUpperStar _ ℓ b).obj M)))) ≫
      F.map ((boundedConstructibleLowerShriek ℓ b).map
        ((boundedConstructibleLowerShriek ℓ g).map (ρ_ ((boundedConstructibleUpperStar _ ℓ g).obj
          ((boundedConstructibleUpperStar _ ℓ b).obj M))).inv)) ≫
      F.map ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv.app
        ((boundedConstructibleUpperStar _ ℓ g).obj ((boundedConstructibleUpperStar _ ℓ b).obj M) ⊗
          𝟙_ _)) ≫
      F.map ((boundedConstructibleLowerShriek ℓ (g ≫ b)).map
        ((boundedConstructibleUpperStarComp _ ℓ g b).inv.app M ▷ _)) ≫
      F.map (eqToHom (by rw [h])) ≫ k := by
  subst h
  have e := congrArg (fun t ↦ F.map t ≫ k) (leftProjection_lowerShriek_comp_unit ℓ g b M)
  simp only [Functor.map_comp, MonoidalCategory.whiskerLeft_comp, Category.assoc] at e
  simpa only [eqToHom_refl, MonoidalCategory.whiskerLeft_id, CategoryTheory.Functor.map_id,
    Category.id_comp] using e

@[reassoc]
lemma eqToHom_comp_lowerShriek_map {s t : C ⟶ Y} (h : s = t)
    {N N' : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (φ : N ⟶ N') :
    eqToHom (by rw [h]) ≫ (boundedConstructibleLowerShriek ℓ t).map φ =
      (boundedConstructibleLowerShriek ℓ s).map φ ≫ eqToHom (by rw [h]) := by
  subst h
  simp

@[reassoc]
lemma whiskerLeft_eqToHom_comp_leftProjection {u v : C ⟶ Y} (h : u = v)
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
        (T : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    M ◁ eqToHom (by rw [h] : (boundedConstructibleLowerShriek ℓ u).obj T =
        (boundedConstructibleLowerShriek ℓ v).obj T) ≫
      Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ v) M T =
    Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ u) M T ≫
      eqToHom (by rw [h]) := by
  subst h
  simp

end Generic

end AlgebraicGeometry.ProEtale.CondensedRing

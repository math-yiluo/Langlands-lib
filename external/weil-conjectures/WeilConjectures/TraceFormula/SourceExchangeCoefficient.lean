/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ProperKunneth
public import WeilConjectures.TraceFormula.SourceExchangeCoherence

/-!

# Coherence for the class of the coefficient pushforward

For `g ≫ b = c ≫ q`, `q ≫ p₁ = p₁' ≫ f` and `q ≫ p₂ = p₂' ≫ f` with `g`, `f` proper, the two
maps `Rp₁_! Rb_! Lb^* Lp₂^* Rf_* K ⟶ Rf_! Rc₁_! Lc₂^* K` built from the unit of `g`, the counit
of `f` and the composition isomorphisms agree
(`ProEtale.CondensedRing.lowerShriek_pushforwardCoeff_coherence`). This is the coherence part of
the class of the coefficient pushforward (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, Step 2).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {C D V W X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  [LocallyOfFiniteType D.hom] [QuasiCompact D.hom] [IsSeparated D.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

section Coefficient

@[reassoc]
lemma lowerShriekComp_inv_app_naturality (x : C ⟶ D) (y : D ⟶ W)
    {M N : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (φ : M ⟶ N) :
    (boundedConstructibleLowerShriek ℓ y).map ((boundedConstructibleLowerShriek ℓ x).map φ) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).inv.app N =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).inv.app M ≫
        (boundedConstructibleLowerShriek ℓ (x ≫ y)).map φ :=
  (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).inv.naturality φ

@[reassoc]
lemma lowerShriekComp_hom_app_naturality (x : C ⟶ D) (y : D ⟶ W)
    {M N : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (φ : M ⟶ N) :
    (boundedConstructibleLowerShriek ℓ (x ≫ y)).map φ ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).hom.app N =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).hom.app M ≫
        (boundedConstructibleLowerShriek ℓ y).map
            ((boundedConstructibleLowerShriek ℓ x).map φ) :=
  (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).hom.naturality φ

@[reassoc]
lemma lowerShriek_map_comp_eqToHom' {u u' : C ⟶ D} (h : u = u')
    {M N : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (φ : M ⟶ N) :
    (boundedConstructibleLowerShriek ℓ u).map φ ≫
        eqToHom (by rw [h] : (boundedConstructibleLowerShriek ℓ u).obj N =
          (boundedConstructibleLowerShriek ℓ u').obj N) =
      eqToHom (by rw [h]) ≫ (boundedConstructibleLowerShriek ℓ u').map φ := by
  subst h
  simp

@[reassoc]
lemma lowerShriekSquareIso_hom_app_naturality {g' : C ⟶ D} {f₀ : D ⟶ W} {f' : C ⟶ X}
    {g₀ : X ⟶ W} (w : g' ≫ f₀ = f' ≫ g₀) {M N : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : M ⟶ N) :
    (boundedConstructibleLowerShriek ℓ f₀).map ((boundedConstructibleLowerShriek ℓ g').map φ) ≫
        (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ w).hom.app N =
      (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ w).hom.app M ≫
        (boundedConstructibleLowerShriek ℓ g₀).map
            ((boundedConstructibleLowerShriek ℓ f').map φ) :=
  (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ w).hom.naturality φ

@[reassoc]
lemma map_lowerShriekComp_inv_app_naturality (x : C ⟶ D) (y : D ⟶ W)
    {M N : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (φ : M ⟶ N) {Z : Type*} [Category Z]
    (F : Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Z) :
    F.map ((boundedConstructibleLowerShriek ℓ y).map
        ((boundedConstructibleLowerShriek ℓ x).map φ)) ≫
        F.map ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).inv.app N) =
      F.map ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).inv.app M) ≫
        F.map ((boundedConstructibleLowerShriek ℓ (x ≫ y)).map φ) := by
  simp only [← F.map_comp, lowerShriekComp_inv_app_naturality]

@[reassoc]
lemma map_lowerShriekComp_hom_app_naturality (x : C ⟶ D) (y : D ⟶ W)
    {M N : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (φ : M ⟶ N) {Z : Type*} [Category Z]
    (F : Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Z) :
    F.map ((boundedConstructibleLowerShriek ℓ (x ≫ y)).map φ) ≫
        F.map ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).hom.app N) =
      F.map ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).hom.app M) ≫
        F.map ((boundedConstructibleLowerShriek ℓ y).map
          ((boundedConstructibleLowerShriek ℓ x).map φ)) := by
  simp only [← F.map_comp, lowerShriekComp_hom_app_naturality]

/-- Moving maps past a cast `Ru_! = R(c ≫ q)_!` and the composition isomorphism of `c ≫ q`. -/
lemma map_lowerShriek_map_comp_eqToHom_comp_lowerShriekComp_hom_app {u : C ⟶ W} (c : C ⟶ V)
    (q : V ⟶ W) (h : u = c ≫ q) {M M' N : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (A : Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
        (T : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (φ₁ : M ⟶ M') (φ₂ : M' ⟶ (boundedConstructibleUpperStar _ ℓ u).obj A ⊗ T)
    (ψ : (boundedConstructibleUpperStar _ ℓ (c ≫ q)).obj A ⊗ T ⟶ N) {Z : Type*} [Category Z]
    (F : Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Z) {E : Z}
    (k : F.obj ((boundedConstructibleLowerShriek ℓ q).obj
      ((boundedConstructibleLowerShriek ℓ c).obj N)) ⟶ E) :
    F.map ((boundedConstructibleLowerShriek ℓ u).map φ₁) ≫
      F.map ((boundedConstructibleLowerShriek ℓ u).map φ₂) ≫
      F.map (eqToHom (by rw [h] : (boundedConstructibleLowerShriek ℓ u).obj
          ((boundedConstructibleUpperStar _ ℓ u).obj A ⊗ T) =
        (boundedConstructibleLowerShriek ℓ (c ≫ q)).obj
          ((boundedConstructibleUpperStar _ ℓ (c ≫ q)).obj A ⊗ T))) ≫
      F.map ((boundedConstructibleLowerShriek ℓ (c ≫ q)).map ψ) ≫
      F.map ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ c q).hom.app N) ≫ k =
    F.map (eqToHom (by rw [h] : (boundedConstructibleLowerShriek ℓ u).obj M =
        (boundedConstructibleLowerShriek ℓ (c ≫ q)).obj M)) ≫
      F.map ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ c q).hom.app M) ≫
      F.map ((boundedConstructibleLowerShriek ℓ q).map
          ((boundedConstructibleLowerShriek ℓ c).map
        (φ₁ ≫ φ₂ ≫ eqToHom (by rw [h]) ≫ ψ))) ≫ k := by
  subst h
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp, Functor.map_comp,
    Category.assoc, map_lowerShriekComp_hom_app_naturality_assoc]

/-- Moving four maps past the inverse composition isomorphism, under a functor. -/
lemma map_lowerShriek_map₄_comp_lowerShriekComp_inv_app (x : C ⟶ D) (y : D ⟶ W)
    {M₀ M₁ M₂ M₃ M₄ : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (a₁ : M₀ ⟶ M₁) (a₂ : M₁ ⟶ M₂)
    (a₃ : M₂ ⟶ M₃) (a₄ : M₃ ⟶ M₄) {Z : Type*} [Category Z]
    (F : Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Z) :
    F.map ((boundedConstructibleLowerShriek ℓ y).map
        ((boundedConstructibleLowerShriek ℓ x).map a₁)) ≫
      F.map ((boundedConstructibleLowerShriek ℓ y).map
          ((boundedConstructibleLowerShriek ℓ x).map a₂)) ≫
      F.map ((boundedConstructibleLowerShriek ℓ y).map
          ((boundedConstructibleLowerShriek ℓ x).map a₃)) ≫
      F.map ((boundedConstructibleLowerShriek ℓ y).map
          ((boundedConstructibleLowerShriek ℓ x).map a₄)) ≫
      F.map ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).inv.app M₄) =
    F.map ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).inv.app M₀) ≫
      F.map ((boundedConstructibleLowerShriek ℓ (x ≫ y)).map (a₁ ≫ a₂ ≫ a₃ ≫ a₄)) := by
  simp only [Functor.map_comp, map_lowerShriekComp_inv_app_naturality_assoc,
    map_lowerShriekComp_inv_app_naturality]

lemma eqToHom_upperStar_tensor {u u' : C ⟶ D} (h : u = u')
    (A : Dᵇc(D.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
        (T : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    eqToHom (by rw [h] : (boundedConstructibleUpperStar _ ℓ u).obj A ⊗ T =
        (boundedConstructibleUpperStar _ ℓ u').obj A ⊗ T) =
      eqToHom (by rw [h] : (boundedConstructibleUpperStar _ ℓ u).obj A =
        (boundedConstructibleUpperStar _ ℓ u').obj A) ▷ T := by
  subst h
  simp

/-- Moving a map past the unit of `Lg^* ⊣ Rg_*` and `Rg_* ≅ Rg_!`. -/
lemma map_unit_comp_lowerShriekIsoLowerStar_inv (g : C ⟶ D) [IsProper g.left]
    {A B : Dᵇc(D.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (u : A ⟶ B)
    {E : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (y : (boundedConstructibleUpperStar _ ℓ g).obj B ⟶ E) {Z : Type*} [Category Z]
    (F : Dᵇc(D.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Z) {T : Z}
    (k : F.obj ((boundedConstructibleLowerShriek ℓ g).obj E) ⟶ T) :
    F.map u ≫
      F.map ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app B ≫
        (boundedConstructibleLowerStar ℓ g).map y) ≫
      F.map ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app E) ≫ k =
    F.map ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app A) ≫
      F.map ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app
        ((boundedConstructibleUpperStar _ ℓ g).obj A)) ≫
      F.map ((boundedConstructibleLowerShriek ℓ g).map
        ((boundedConstructibleUpperStar _ ℓ g).map u ≫ y)) ≫ k := by
  have h₁ := (boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.naturality u
  have h₂ := (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.naturality
    ((boundedConstructibleUpperStar _ ℓ g).map u ≫ y)
  simp only [Functor.comp_map, Functor.id_map] at h₁ h₂
  simp only [← F.map_comp_assoc, Category.assoc]
  rewrite [reassoc_of% h₁, ← (boundedConstructibleLowerStar ℓ g).map_comp_assoc, h₂]
  simp only [Functor.map_comp, Category.assoc]

/-- The coherence part of the class of the coefficient pushforward: for `g ≫ b = c ≫ q`,
`q ≫ p₁ = p₁' ≫ f`, `q ≫ p₂ = p₂' ≫ f` with `g`, `f` proper, the two maps
`Rp₁_! Rb_! Lb^* Lp₂^* Rf_* K ⟶ Rf_! Rc₁_! Lc₂^* K` agree. -/
theorem lowerShriek_pushforwardCoeff_coherence (g : C ⟶ D) [IsProper g.left] (b : D ⟶ W)
    (c : C ⟶ V) (q : V ⟶ W) (f : X ⟶ Y) [IsProper f.left] (p₁ p₂ : W ⟶ Y) (p₁' p₂' : V ⟶ X)
    {b₁ b₂ : D ⟶ Y} {c₁ c₂ : C ⟶ X} (hb₁ : b ≫ p₁ = b₁) (hb₂ : b ≫ p₂ = b₂)
    (hc₁ : c ≫ p₁' = c₁) (hc₂ : c ≫ p₂' = c₂) (hgq : g ≫ b = c ≫ q) (hq₁ : q ≫ p₁ = p₁' ≫ f)
    (hq₂ : q ≫ p₂ = p₂' ≫ f) (w₁ : g ≫ b₁ = c₁ ≫ f) (w₂ : g ≫ b₂ = c₂ ≫ f)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ p₁).map ((boundedConstructibleLowerShriek ℓ b).map
        ((boundedConstructibleUpperStarComp _ ℓ b p₂).inv.app
          ((boundedConstructibleLowerStar ℓ f).obj K))) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ b p₁).inv.app
        ((boundedConstructibleUpperStar _ ℓ (b ≫ p₂)).obj
          ((boundedConstructibleLowerStar ℓ f).obj K)) ≫
      (boundedConstructibleLowerShriek ℓ (b ≫ p₁)).map (eqToHom (by rw [hb₂])) ≫
      eqToHom (by rw [hb₁] : (boundedConstructibleLowerShriek ℓ (b ≫ p₁)).obj
          ((boundedConstructibleUpperStar _ ℓ b₂).obj
              ((boundedConstructibleLowerStar ℓ f).obj K)) =
        (boundedConstructibleLowerShriek ℓ b₁).obj
          ((boundedConstructibleUpperStar _ ℓ b₂).obj
              ((boundedConstructibleLowerStar ℓ f).obj K))) ≫
      (boundedConstructibleLowerShriek ℓ b₁).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app
            ((boundedConstructibleUpperStar _ ℓ b₂).obj
              ((boundedConstructibleLowerStar ℓ f).obj K)) ≫
          (boundedConstructibleLowerStar ℓ g).map
            ((boundedConstructibleUpperStarComp _ ℓ g b₂).inv.app
                ((boundedConstructibleLowerStar ℓ f).obj K) ≫
              eqToHom (by rw [w₂]) ≫
              (boundedConstructibleUpperStarComp _ ℓ c₂ f).hom.app
                ((boundedConstructibleLowerStar ℓ f).obj K) ≫
              (boundedConstructibleUpperStar _ ℓ c₂).map
                ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app K))) ≫
      (boundedConstructibleLowerShriek ℓ b₁).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app
          ((boundedConstructibleUpperStar _ ℓ c₂).obj K)) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b₁).inv.app
        ((boundedConstructibleUpperStar _ ℓ c₂).obj K) ≫
      eqToHom (by rw [w₁]) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c₁ f).hom.app
        ((boundedConstructibleUpperStar _ ℓ c₂).obj K) =
    (boundedConstructibleLowerShriek ℓ p₁).map ((boundedConstructibleLowerShriek ℓ b).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app
          ((boundedConstructibleUpperStar _ ℓ b).obj ((boundedConstructibleUpperStar _ ℓ p₂).obj
            ((boundedConstructibleLowerStar ℓ f).obj K))))) ≫
      (boundedConstructibleLowerShriek ℓ p₁).map ((boundedConstructibleLowerShriek ℓ b).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app
          ((boundedConstructibleUpperStar _ ℓ g).obj ((boundedConstructibleUpperStar _ ℓ b).obj
            ((boundedConstructibleUpperStar _ ℓ p₂).obj
              ((boundedConstructibleLowerStar ℓ f).obj K)))))) ≫
      (boundedConstructibleLowerShriek ℓ p₁).map ((boundedConstructibleLowerShriek ℓ b).map
        ((boundedConstructibleLowerShriek ℓ g).map
          (ρ_ ((boundedConstructibleUpperStar _ ℓ g).obj ((boundedConstructibleUpperStar _ ℓ b).obj
            ((boundedConstructibleUpperStar _ ℓ p₂).obj
              ((boundedConstructibleLowerStar ℓ f).obj K))))).inv)) ≫
      (boundedConstructibleLowerShriek ℓ p₁).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv.app
          ((boundedConstructibleUpperStar _ ℓ g).obj ((boundedConstructibleUpperStar _ ℓ b).obj
            ((boundedConstructibleUpperStar _ ℓ p₂).obj
              ((boundedConstructibleLowerStar ℓ f).obj K))) ⊗ 𝟙_ _)) ≫
      (boundedConstructibleLowerShriek ℓ p₁).map ((boundedConstructibleLowerShriek ℓ (g ≫
          b)).map
        ((boundedConstructibleUpperStarComp _ ℓ g b).inv.app
            ((boundedConstructibleUpperStar _ ℓ p₂).obj
          ((boundedConstructibleLowerStar ℓ f).obj K)) ▷ 𝟙_ _)) ≫
      (boundedConstructibleLowerShriek ℓ p₁).map (eqToHom (by rw [hgq])) ≫
      (boundedConstructibleLowerShriek ℓ p₁).map ((boundedConstructibleLowerShriek ℓ (c ≫
          q)).map
        ((boundedConstructibleUpperStarComp _ ℓ c q).hom.app
            ((boundedConstructibleUpperStar _ ℓ p₂).obj
          ((boundedConstructibleLowerStar ℓ f).obj K)) ▷ 𝟙_ _)) ≫
      (boundedConstructibleLowerShriek ℓ p₁).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ c q).hom.app
          ((boundedConstructibleUpperStar _ ℓ c).obj ((boundedConstructibleUpperStar _ ℓ q).obj
            ((boundedConstructibleUpperStar _ ℓ p₂).obj
              ((boundedConstructibleLowerStar ℓ f).obj K))) ⊗ 𝟙_ _)) ≫
      (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ hq₁).hom.app
        ((boundedConstructibleLowerShriek ℓ c).obj
          ((boundedConstructibleUpperStar _ ℓ c).obj ((boundedConstructibleUpperStar _ ℓ q).obj
            ((boundedConstructibleUpperStar _ ℓ p₂).obj
              ((boundedConstructibleLowerStar ℓ f).obj K))) ⊗ 𝟙_ _)) ≫
      (boundedConstructibleLowerShriek ℓ f).map ((boundedConstructibleLowerShriek ℓ p₁').map
        ((boundedConstructibleLowerShriek ℓ c).map
          ((boundedConstructibleUpperStar _ ℓ c).map (prodUpperStarCounit ℓ hq₂ K) ▷ 𝟙_ _))) ≫
      (boundedConstructibleLowerShriek ℓ f).map ((boundedConstructibleLowerShriek ℓ p₁').map
        ((boundedConstructibleLowerShriek ℓ c).map
          (ρ_ ((boundedConstructibleUpperStar _ ℓ c).obj
            ((boundedConstructibleUpperStar _ ℓ p₂').obj K))).hom)) ≫
      (boundedConstructibleLowerShriek ℓ f).map ((boundedConstructibleLowerShriek ℓ p₁').map
        ((boundedConstructibleLowerShriek ℓ c).map
          ((boundedConstructibleUpperStarComp _ ℓ c p₂').inv.app K))) ≫
      (boundedConstructibleLowerShriek ℓ f).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ c p₁').inv.app
          ((boundedConstructibleUpperStar _ ℓ (c ≫ p₂')).obj K)) ≫
      (boundedConstructibleLowerShriek ℓ f).map
        ((boundedConstructibleLowerShriek ℓ (c ≫ p₁')).map (eqToHom (by rw [hc₂]))) ≫
      (boundedConstructibleLowerShriek ℓ f).map (eqToHom (by rw [hc₁] :
        (boundedConstructibleLowerShriek ℓ (c ≫ p₁')).obj
            ((boundedConstructibleUpperStar _ ℓ c₂).obj K) =
          (boundedConstructibleLowerShriek ℓ c₁).obj
              ((boundedConstructibleUpperStar _ ℓ c₂).obj K))) := by
  subst hb₁ hb₂ hc₁ hc₂
  simp only [eqToHom_refl ((boundedConstructibleUpperStar _ ℓ (b ≫ p₂)).obj
      ((boundedConstructibleLowerStar ℓ f).obj K)),
    eqToHom_refl ((boundedConstructibleLowerShriek ℓ (b ≫ p₁)).obj
      ((boundedConstructibleUpperStar _ ℓ (b ≫ p₂)).obj
          ((boundedConstructibleLowerStar ℓ f).obj K))),
    eqToHom_refl ((boundedConstructibleUpperStar _ ℓ (c ≫ p₂')).obj K),
    eqToHom_refl ((boundedConstructibleLowerShriek ℓ (c ≫ p₁')).obj
      ((boundedConstructibleUpperStar _ ℓ (c ≫ p₂')).obj K))]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  simp only [lowerShriekComp_inv_app_naturality_assoc ℓ b p₁
    ((boundedConstructibleUpperStarComp _ ℓ b p₂).inv.app
        ((boundedConstructibleLowerStar ℓ f).obj K))]
  simp only [map_unit_comp_lowerShriekIsoLowerStar_inv ℓ g
    (E := (boundedConstructibleUpperStar _ ℓ (c ≫ p₂')).obj K)
    ((boundedConstructibleUpperStarComp _ ℓ b p₂).inv.app
        ((boundedConstructibleLowerStar ℓ f).obj K))
    ((boundedConstructibleUpperStarComp _ ℓ g (b ≫ p₂)).inv.app
        ((boundedConstructibleLowerStar ℓ f).obj K) ≫
      eqToHom (by rw [w₂]) ≫
      (boundedConstructibleUpperStarComp _ ℓ (c ≫ p₂') f).hom.app
        ((boundedConstructibleLowerStar ℓ f).obj K) ≫
      (boundedConstructibleUpperStar _ ℓ (c ≫ p₂')).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app K))
    (boundedConstructibleLowerShriek ℓ (b ≫ p₁))]
  dsimp only [Functor.comp_obj]
  simp only [lowerShriekComp_inv_app_naturality_assoc ℓ g (b ≫
      p₁), lowerShriek_map_comp_eqToHom'_assoc ℓ w₁,
    lowerShriekComp_hom_app_naturality ℓ (c ≫ p₁') f]
  dsimp only [Functor.comp_obj]
  simp only [← lowerShriekComp_inv_app_naturality_assoc ℓ b p₁
      (M := (boundedConstructibleUpperStar _ ℓ b).obj ((boundedConstructibleUpperStar _ ℓ p₂).obj
        ((boundedConstructibleLowerStar ℓ f).obj K)))
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app
        ((boundedConstructibleUpperStar _ ℓ b).obj ((boundedConstructibleUpperStar _ ℓ p₂).obj
          ((boundedConstructibleLowerStar ℓ f).obj K))))]
  dsimp only [Functor.comp_obj]
  simp only [← lowerShriekComp_inv_app_naturality_assoc ℓ b p₁
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app
        ((boundedConstructibleUpperStar _ ℓ g).obj ((boundedConstructibleUpperStar _ ℓ b).obj
          ((boundedConstructibleUpperStar _ ℓ p₂).obj
              ((boundedConstructibleLowerStar ℓ f).obj K)))))]
  simp only [lowerShriekComp_pushforwardSquare_assoc ℓ g b c q p₁ p₁' f hgq hq₁ w₁]
  refine whisker_eq _ (whisker_eq _ ?_)
  simp only [map_lowerShriekComp_inv_app_naturality_assoc ℓ g b _
      (boundedConstructibleLowerShriek ℓ p₁)]
  simp only [map_lowerShriek_map_comp_eqToHom_comp_lowerShriekComp_hom_app ℓ c q hgq]
  simp only [lowerShriekSquareIso_hom_app_naturality_assoc ℓ hq₁]
  simp only [map_lowerShriek_map₄_comp_lowerShriekComp_inv_app ℓ c p₁']
  refine whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _ ?_))))
  refine congrArg (fun t ↦ (boundedConstructibleLowerShriek ℓ f).map
    ((boundedConstructibleLowerShriek ℓ (c ≫ p₁')).map t)) ?_
  have hs := boundedConstructibleUpperStarComp_pushforwardSquare ℓ (Profinite.padicAlgClRingObj ℓ)
    g b c q p₂ p₂' f hgq hq₂ w₂ ((boundedConstructibleLowerStar ℓ f).obj K)
  have hε := (boundedConstructibleUpperStarComp _ ℓ c p₂').inv.naturality
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app K)
  simp only [Functor.comp_map] at hε
  dsimp only [Functor.id_obj] at hε
  simp only [eqToHom_upperStar_tensor ℓ hgq]
  simp only [Category.assoc, ← comp_whiskerRight_assoc, ← comp_whiskerRight]
  simp only [MonoidalCategory.rightUnitor_inv_comp_whiskerRight_comp_hom_assoc]
  simp only [prodUpperStarCounit, Functor.map_comp, Category.assoc]
  simp only [hε, reassoc_of% hs]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj]

end Coefficient

end AlgebraicGeometry.ProEtale.CondensedRing

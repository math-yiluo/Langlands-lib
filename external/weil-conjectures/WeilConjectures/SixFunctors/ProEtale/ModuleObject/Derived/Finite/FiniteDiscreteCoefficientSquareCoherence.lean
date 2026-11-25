/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientPullbackIso
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientSheafComposition

/-! # Square coherence for the finite discrete coefficient realization -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local instance] coefficientProfiniteEssentiallySmall

private theorem square_of_composition_maps
    {C : Type*} [Category C] {A B D E P Q R S : C}
    (a : A ⟶ B) (ai : B ⟶ A) (b : D ⟶ E)
    (u : P ⟶ R) (ui : R ⟶ P) (v : Q ⟶ S)
    (e : A ⟶ D) (δ : P ⟶ Q)
    (left : E ⟶ S) (right : B ⟶ R) (pa : A ⟶ P) (pb : D ⟶ Q)
    (hia : ai ≫ a = 𝟙 B) (hui : u ≫ ui = 𝟙 P)
    (hl : b ≫ left = pb ≫ v) (hr : a ≫ right = pa ≫ u)
    (hc : e ≫ pb = pa ≫ δ) :
    ai ≫ e ≫ b ≫ left = right ≫ ui ≫ δ ≫ v := by
  have hr' : right = ai ≫ pa ≫ u := by
    rw [← hr, ← Category.assoc ai a, hia, Category.id_comp]
  rw [hl, ← Category.assoc e pb, hc, hr']
  simp only [Category.assoc]
  rw [reassoc_of% hui]

private theorem square_of_comparison_isos
    {C D I J : Type*} [Category C] [Category D] [Category I] [Category J]
    (F : C ⥤ D) {H₀ H₁ H₂ H₃ : I ⥤ C} {U₀ U₁ U₂ U₃ : J ⥤ D}
    (a : H₀ ≅ H₁) (b : H₂ ≅ H₃) (e : H₀ ≅ H₂)
    (u : U₀ ≅ U₁) (v : U₂ ≅ U₃) (δ : U₀ ≅ U₂) (K : I) (M : J)
    (left : F.obj (H₃.obj K) ⟶ U₃.obj M)
    {Z : D} (right : F.obj (H₁.obj K) ⟶ Z) (right' : Z ⟶ U₁.obj M)
    (pa : F.obj (H₀.obj K) ⟶ U₀.obj M)
    (pb : F.obj (H₂.obj K) ⟶ U₂.obj M)
    (hl : F.map (b.hom.app K) ≫ left = pb ≫ v.hom.app M)
    (hr : F.map (a.hom.app K) ≫ right ≫ right' = pa ≫ u.hom.app M)
    (hc : F.map (e.hom.app K) ≫ pb = pa ≫ δ.hom.app M)
    (ae : H₁ ≅ H₃) (ud : U₁ ≅ U₃)
    (ha : ae = AlgebraicGeometry.ProEtale.CondensedRing.coefficientIsoTransThree a.symm e b)
    (hu : ud =
      AlgebraicGeometry.ProEtale.CondensedRing.coefficientIsoTransThree u.symm δ v) :
    F.map (ae.hom.app K) ≫ left = right ≫ right' ≫ ud.hom.app M := by
  rw [ha, hu]
  change F.map (a.inv.app K ≫ e.hom.app K ≫ b.hom.app K) ≫ left =
    right ≫ right' ≫ u.inv.app M ≫ δ.hom.app M ≫ v.hom.app M
  simpa only [Functor.map_comp, Category.assoc] using
    square_of_composition_maps (F.map (a.hom.app K)) (F.map (a.inv.app K))
      (F.map (b.hom.app K)) (u.hom.app M) (u.inv.app M) (v.hom.app M)
      (F.map (e.hom.app K)) (δ.hom.app M) left (right ≫ right') pa pb
      ((F.mapIso (a.app K)).inv_hom_id) (u.hom_inv_id_app M) hl hr hc

private theorem transport_comp
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    (U₁ L₁ : C₁ ⥤ C₀) (U₂ L₂ : C₂ ⥤ C₁) (U₁₂ L₁₂ : C₂ ⥤ C₀)
    (l₁ : L₁ ≅ U₁) (l₂ : L₂ ≅ U₂) (l₁₂ : L₁₂ ≅ U₁₂)
    (c : U₁₂ ≅ U₂ ⋙ U₁)
    {A A' D D' : C₀} {M M' : C₁} {N N' : C₂}
    (q : A ≅ A') (r : D ≅ D') (s : M ≅ M') (t : N ≅ N')
    (a : A ⟶ D) (a' : A' ⟶ D')
    (p₁ : D' ⟶ U₁.obj M') (p₂ : M' ⟶ U₂.obj N') (p₁₂ : A' ⟶ U₁₂.obj N')
    (hn : a ≫ r.hom = q.hom ≫ a')
    (hc : a' ≫ p₁ ≫ U₁.map p₂ = p₁₂ ≫ c.hom.app N') :
    a ≫ r.hom ≫ p₁ ≫ U₁.map s.inv ≫ l₁.inv.app M ≫
        L₁.map (s.hom ≫ p₂ ≫ U₂.map t.inv ≫ l₂.inv.app N) =
      q.hom ≫ p₁₂ ≫ U₁₂.map t.inv ≫ l₁₂.inv.app N ≫
        l₁₂.hom.app N ≫ c.hom.app N ≫ U₁.map (l₂.inv.app N) ≫
          l₁.inv.app (L₂.obj N) := by
  rw [← l₁.inv.naturality]
  simp only [Functor.map_comp, Category.assoc]
  rw [← U₁.map_comp_assoc, s.inv_hom_id, U₁.map_id, Category.id_comp]
  rw [reassoc_of% l₁₂.inv_hom_id_app]
  rw [← Category.assoc a r.hom, hn]
  simp only [Category.assoc]
  rw [reassoc_of% hc]
  rw [c.hom.naturality_assoc]
  rfl

private noncomputable def comparisonPaste
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (E₂ : C₂ ⥤ C₁) (E₁ : C₁ ⥤ C₀) (I₂ : D₂ ⥤ D₁) (I₁ : D₁ ⥤ D₀)
    (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
    (p₁ : E₁ ⋙ F₀ ≅ F₁ ⋙ I₁) (p₂ : E₂ ⋙ F₁ ≅ F₂ ⋙ I₂) :
    (E₂ ⋙ E₁) ⋙ F₀ ≅ F₂ ⋙ (I₂ ⋙ I₁) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft E₂ p₁ ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight p₂ I₁ ≪≫
    Functor.associator _ _ _

private theorem comparisonPaste_comp
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (E₂ : C₂ ⥤ C₁) (E₁ : C₁ ⥤ C₀) (E : C₂ ⥤ C₀)
    (I₂ : D₂ ⥤ D₁) (I₁ : D₁ ⥤ D₀) (I : D₂ ⥤ D₀)
    (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
    (p₁ : E₁ ⋙ F₀ ≅ F₁ ⋙ I₁) (p₂ : E₂ ⋙ F₁ ≅ F₂ ⋙ I₂)
    (p : E ⋙ F₀ ≅ F₂ ⋙ I) (cE : E ≅ E₂ ⋙ E₁) (cI : I ≅ I₂ ⋙ I₁)
    (h : ∀ K, F₀.map (cE.hom.app K) ≫ p₁.hom.app (E₂.obj K) ≫
      I₁.map (p₂.hom.app K) = p.hom.app K ≫ cI.hom.app (F₂.obj K)) :
    Functor.isoWhiskerRight cE F₀ ≪≫ comparisonPaste E₂ E₁ I₂ I₁ F₀ F₁ F₂ p₁ p₂ =
      p ≪≫ Functor.isoWhiskerLeft F₂ cI := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simpa only [comparisonPaste, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Iso.symm_hom,
    Category.id_comp, Category.comp_id, Category.assoc] using h K

private theorem comparison_iso_square
    {C D I J : Type*} [Category C] [Category D] [Category I] [Category J]
    (F : C ⥤ D) (G : I ⥤ J)
    {H₀ H₁ H₂ H₃ : I ⥤ C} {U₀ U₁ U₂ U₃ : J ⥤ D}
    (a : H₀ ≅ H₁) (b : H₂ ≅ H₃) (e : H₀ ≅ H₂)
    (u : U₀ ≅ U₁) (v : U₂ ≅ U₃) (δ : U₀ ≅ U₂)
    (left : H₃ ⋙ F ≅ G ⋙ U₃) (right : H₁ ⋙ F ≅ G ⋙ U₁)
    (pa : H₀ ⋙ F ≅ G ⋙ U₀) (pb : H₂ ⋙ F ≅ G ⋙ U₂)
    (hl : Functor.isoWhiskerRight b F ≪≫ left = pb ≪≫ Functor.isoWhiskerLeft G v)
    (hr : Functor.isoWhiskerRight a F ≪≫ right = pa ≪≫ Functor.isoWhiskerLeft G u)
    (hc : Functor.isoWhiskerRight e F ≪≫ pb = pa ≪≫ Functor.isoWhiskerLeft G δ)
    (ae : H₁ ≅ H₃) (ud : U₁ ≅ U₃)
    (ha : ae = AlgebraicGeometry.ProEtale.CondensedRing.coefficientIsoTransThree a.symm e b)
    (hu : ud =
      AlgebraicGeometry.ProEtale.CondensedRing.coefficientIsoTransThree u.symm δ v) :
    Functor.isoWhiskerRight ae F ≪≫ left = right ≪≫ Functor.isoWhiskerLeft G ud := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hl' := congrArg (fun t ↦ t.hom.app K) hl
  have hr' := congrArg (fun t ↦ t.hom.app K) hr
  have hc' := congrArg (fun t ↦ t.hom.app K) hc
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at *
  simpa only [Category.id_comp] using
    square_of_comparison_isos F a b e u v δ K (G.obj K)
      (left.hom.app K) (right.hom.app K) (𝟙 _) (pa.hom.app K) (pb.hom.app K)
      hl' (by simpa only [Category.comp_id] using hr') hc' ae ud ha hu

private theorem comparison_square_components
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    (E₁ : C₁ ⥤ C₀) (E₂ : C₂ ⥤ C₀) (E₃ : C₃ ⥤ C₁) (E₄ : C₃ ⥤ C₂)
    (I₁ : D₁ ⥤ D₀) (I₂ : D₂ ⥤ D₀) (I₃ : D₃ ⥤ D₁) (I₄ : D₃ ⥤ D₂)
    (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃)
    (p₁ : E₁ ⋙ F₀ ≅ F₁ ⋙ I₁) (p₂ : E₂ ⋙ F₀ ≅ F₂ ⋙ I₂)
    (p₃ : E₃ ⋙ F₁ ≅ F₃ ⋙ I₃) (p₄ : E₄ ⋙ F₂ ≅ F₃ ⋙ I₄)
    (θ : E₃ ⋙ E₁ ≅ E₄ ⋙ E₂) (φ : I₃ ⋙ I₁ ≅ I₄ ⋙ I₂)
    (h : Functor.isoWhiskerRight θ F₀ ≪≫ comparisonPaste E₄ E₂ I₄ I₂ F₀ F₂ F₃ p₂ p₄ =
      comparisonPaste E₃ E₁ I₃ I₁ F₀ F₁ F₃ p₁ p₃ ≪≫ Functor.isoWhiskerLeft F₃ φ)
    (K : C₃) :
    F₀.map (θ.hom.app K) ≫ p₂.hom.app (E₄.obj K) ≫ I₂.map (p₄.hom.app K) =
      p₁.hom.app (E₃.obj K) ≫ I₁.map (p₃.hom.app K) ≫ φ.hom.app (F₃.obj K) := by
  have H := congrArg (fun t ↦ t.hom.app K) h
  simpa only [comparisonPaste, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Iso.symm_hom,
    Category.id_comp, Category.comp_id, Category.assoc] using H

private theorem comparison_family_congr
    {K : Type*} [Category K] {C D : K → Type*}
    [∀ X, Category (C X)] [∀ X, Category (D X)]
    (E : ∀ {X Y : K}, (X ⟶ Y) → C Y ⥤ C X)
    (I : ∀ {X Y : K}, (X ⟶ Y) → D Y ⥤ D X)
    (F : ∀ X, C X ⥤ D X)
    (p : ∀ {X Y : K} (f : X ⟶ Y), E f ⋙ F X ≅ F Y ⋙ I f)
    {X Y : K} (f g : X ⟶ Y) (h : f = g) (he : E f = E g) (hi : I f = I g) :
    Functor.isoWhiskerRight (eqToIso he) (F X) ≪≫ p g =
      p f ≪≫ Functor.isoWhiskerLeft (F Y) (eqToIso hi) := by
  subst g
  simp

private theorem comparison_family_square
    {K : Type*} [Category K] {C D : K → Type*}
    [∀ X, Category (C X)] [∀ X, Category (D X)]
    (E : ∀ {X Y : K}, (X ⟶ Y) → C Y ⥤ C X)
    (I : ∀ {X Y : K}, (X ⟶ Y) → D Y ⥤ D X)
    (F : ∀ X, C X ⥤ D X)
    (p : ∀ {X Y : K} (f : X ⟶ Y), E f ⋙ F X ≅ F Y ⋙ I f)
    (cE : ∀ {X Y Z : K} (f : X ⟶ Y) (g : Y ⟶ Z), E (f ≫ g) ≅ E g ⋙ E f)
    (cI : ∀ {X Y Z : K} (f : X ⟶ Y) (g : Y ⟶ Z), I (f ≫ g) ≅ I g ⋙ I f)
    (θ : ∀ {X Y X' Y' : K} {f : X ⟶ Y} {g : Y' ⟶ Y}
      {f' : X' ⟶ Y'} {g' : X' ⟶ X}, CommSq g' f' f g → (E g ⋙ E f' ≅ E f ⋙ E g'))
    (φ : ∀ {X Y X' Y' : K} {f : X ⟶ Y} {g : Y' ⟶ Y}
      {f' : X' ⟶ Y'} {g' : X' ⟶ X}, CommSq g' f' f g → (I g ⋙ I f' ≅ I f ⋙ I g'))
    (hθ : ∀ {X Y X' Y' : K} {f : X ⟶ Y} {g : Y' ⟶ Y}
      {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g),
      θ sq = AlgebraicGeometry.ProEtale.CondensedRing.coefficientIsoTransThree (cE f' g).symm
        (eqToIso (congrArg (fun h : X' ⟶ Y ↦ E h) sq.w.symm)) (cE g' f))
    (hφ : ∀ {X Y X' Y' : K} {f : X ⟶ Y} {g : Y' ⟶ Y}
      {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g),
      φ sq = AlgebraicGeometry.ProEtale.CondensedRing.coefficientIsoTransThree
        (cI f' g).symm (eqToIso (congrArg (fun h : X' ⟶ Y ↦ I h) sq.w.symm)) (cI g' f))
    (hcomp : ∀ {X Y Z : K} (f : X ⟶ Y) (g : Y ⟶ Z) (N : C Z),
      (F X).map ((cE f g).hom.app N) ≫ (p f).hom.app ((E g).obj N) ≫
        (I f).map ((p g).hom.app N) =
      (p (f ≫ g)).hom.app N ≫ (cI f g).hom.app ((F Z).obj N)) :
    AlgebraicGeometry.ProEtale.CondensedRing.FunctorComparisonSquare E I F p θ φ := by
  intro X Y X' Y' f g f' g' sq N
  have hp {S T U : K} (f : S ⟶ T) (g : T ⟶ U) :=
    comparisonPaste_comp (E g) (E f) (E (f ≫ g)) (I g) (I f) (I (f ≫ g))
      (F S) (F T) (F U) (p f) (p g) (p (f ≫ g)) (cE f g) (cI f g) (hcomp f g)
  have H := comparison_iso_square (F X') (F Y) (cE f' g) (cE g' f)
    (eqToIso (congrArg (fun h : X' ⟶ Y ↦ E h) sq.w.symm)) (cI f' g) (cI g' f)
    (eqToIso (congrArg (fun h : X' ⟶ Y ↦ I h) sq.w.symm))
    (comparisonPaste (E f) (E g') (I f) (I g') (F X') (F X) (F Y) (p g') (p f))
    (comparisonPaste (E g) (E f') (I g) (I f') (F X') (F Y') (F Y) (p f') (p g))
    (p (f' ≫ g)) (p (g' ≫ f)) (hp g' f) (hp f' g)
    (comparison_family_congr E I F p (f' ≫ g) (g' ≫ f) sq.w.symm
      (congrArg (fun h : X' ⟶ Y ↦ E h) sq.w.symm)
      (congrArg (fun h : X' ⟶ Y ↦ I h) sq.w.symm))
    (θ sq) (φ sq) (hθ sq) (hφ sq)
  exact comparison_square_components (E f') (E g') (E g) (E f)
    (I f') (I g') (I g) (I f) (F X') (F Y') (F X) (F Y)
    (p f') (p g') (p g) (p f) (θ sq) (φ sq) H N

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section GenericSquare

variable (B : Type) [CommRing B]
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
    DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)))
  (p : CoefficientPullbackFamily B Λ F)

private theorem etale_square_eq
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g) :
    Etale.pullbackSquareComparison (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq =
      coefficientIsoTransThree
        (Etale.upperStarPlusComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) f' g).symm
        (eqToIso (congrArg
          (fun h ↦ D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h)) sq.w.symm))
        (Etale.upperStarPlusComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) g' f) := by
  unfold Etale.pullbackSquareComparison
  exact (coefficientIsoTransThree_eq
    (Etale.upperStarPlusComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) f' g).symm
    (eqToIso (congrArg
      (fun h ↦ D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h)) sq.w.symm))
    (Etale.upperStarPlusComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) g' f)).symm

private theorem ambient_square_eq
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g) :
    coefficientAmbientSquare Λ sq =
      coefficientIsoTransThree (coefficientDerivedUpperStarComp Λ f' g).symm
        (eqToIso (congrArg (coefficientDerivedUpperStar Λ) sq.w.symm))
        (coefficientDerivedUpperStarComp Λ g' f) := by
  exact coefficientAmbientSquare_eq Λ sq

private theorem square_of_comp
    (hcomp : ∀ {S T U : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U)
      (K : FiniteDiscreteEtalePlus B U),
      (F S).map
          ((Etale.upperStarPlusComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) f g).hom.app K) ≫
        (p f).hom.app
          (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).obj K) ≫
        (coefficientDerivedUpperStar Λ f).map ((p g).hom.app K) =
      (p (f ≫ g)).hom.app K ≫
        (coefficientDerivedUpperStarComp Λ f g).hom.app ((F U).obj K)) :
    CoefficientPullbackSquare B Λ F p := by
  exact @comparison_family_square Scheme.{u} _
    (fun T ↦ FiniteDiscreteEtalePlus B T)
    (fun T ↦ DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T)))
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
    (fun {_ _} h ↦
      D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h))
    (fun {_ _} h ↦ coefficientDerivedUpperStar Λ h) F p
    (fun {_ _ _} f g ↦ Etale.upperStarPlusComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) f g)
    (fun {_ _ _} f g ↦ coefficientDerivedUpperStarComp Λ f g)
    (fun {_ _ _ _} {_ _ _ _} sq ↦
      Etale.pullbackSquareComparison (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq)
    (fun {_ _ _ _} {_ _ _ _} sq ↦ coefficientAmbientSquare Λ sq)
    (fun {_ _ _ _} {_ _ _ _} sq ↦ etale_square_eq B sq)
    (fun {_ _ _ _} {_ _ _ _} sq ↦ ambient_square_eq Λ sq) hcomp

end GenericSquare

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

variable
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private noncomputable abbrev realizationSheaves (T : Scheme.{u}) :=
  comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) T ⋙
    (finiteDiscreteCoefficientEquivalence B eR G hG T).functor

private theorem derived_sheaf_comp {S T U : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U)
    (K : DerivedCategory (Sheaf U.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} B)))) :
    D(realizationSheaves B eR G hG S).map
        ((Functor.mapDerivedCategoryTriangleIso
          (Etale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) f g)).hom.app K) ≫
      (Functor.mapDerivedCategorySquareIso
        (finiteDiscreteCoefficientSheafPullbackIso B eR G hG f)).hom.app
          (D(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).obj K) ≫
      D(upperStar (Profinite.continuousMapRingObj B) f).map
        ((Functor.mapDerivedCategorySquareIso
          (finiteDiscreteCoefficientSheafPullbackIso B eR G hG g)).hom.app K) =
    (Functor.mapDerivedCategorySquareIso
      (finiteDiscreteCoefficientSheafPullbackIso B eR G hG (f ≫ g))).hom.app K ≫
      (Functor.mapDerivedCategoryTriangleIso
        (upperStarComp (Profinite.continuousMapRingObj B) f g)).hom.app
          (D(realizationSheaves B eR G hG U).obj K) := by
  let t := fun {X Y : Scheme.{u}} (h : X ⟶ Y) ↦
    finiteDiscreteCoefficientSheafPullbackIso B eR G hG h
  have hi (N : Sheaf U.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} B))) :
      (t (f ≫ g)).inv.app N ≫ (realizationSheaves B eR G hG S).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) f g).hom.app N) =
      (upperStarComp (Profinite.continuousMapRingObj B) f g).hom.app
          ((realizationSheaves B eR G hG U).obj N) ≫
        (upperStar (Profinite.continuousMapRingObj B) f).map ((t g).inv.app N) ≫
        (t f).inv.app ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).obj N) := by
    rw [← cancel_epi ((t (f ≫ g)).hom.app N), Iso.hom_inv_id_app_assoc]
    rw [← Category.assoc, ← finiteDiscreteCoefficientSheafPullbackIso_comp B eR G hG f g N]
    dsimp only [t]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app,
      Category.comp_id]
  have H := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (t g).symm (t f).symm (t (f ≫ g)).symm
    (upperStarComp (Profinite.continuousMapRingObj B) f g)
    (Etale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) f g) hi K
  have hs {X Y : Scheme.{u}} (h : X ⟶ Y) :
      Functor.mapDerivedCategorySquareIso (t h).symm =
        (Functor.mapDerivedCategorySquareIso (t h)).symm := by
    apply Iso.ext
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  rw [hs g, hs f, hs (f ≫ g)] at H
  simp only [Iso.symm_hom] at H
  dsimp only [t] at H ⊢
  rw [← cancel_epi ((Functor.mapDerivedCategorySquareIso
    (finiteDiscreteCoefficientSheafPullbackIso B eR G hG (f ≫ g))).inv.app K)]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc, ← Category.assoc, H]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.id_comp]
  rw [← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private noncomputable def realization_combine (T : Scheme.{u}) :
    finiteDiscreteRealization B T (finiteDiscreteCoefficientEquivalence B eR G hG T) ≅
      DerivedCategory.Plus.ι ⋙ D(realizationSheaves B eR G hG T) := by
  unfold finiteDiscreteRealization
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      (Functor.mapDerivedCategoryCompIso
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) T)
        (finiteDiscreteCoefficientEquivalence B eR G hG T).functor)

private theorem pullback_hom {S T : Scheme.{u}} (h : S ⟶ T)
    (K : FiniteDiscreteEtalePlus B T) :
    (finiteDiscreteCoefficientPullbackIso B eR G hG h).hom.app K =
      (realization_combine B eR G hG S).hom.app
          (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).obj K) ≫
        (Functor.mapDerivedCategorySquareIso
          (finiteDiscreteCoefficientSheafPullbackIso B eR G hG h)).hom.app
            (DerivedCategory.Plus.ι.obj K) ≫
        D(upperStar (Profinite.continuousMapRingObj B) h).map
          ((realization_combine B eR G hG T).inv.app K) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory
          (Profinite.continuousMapRingObj B) h).inv.app
            ((finiteDiscreteRealization B T
              (finiteDiscreteCoefficientEquivalence B eR G hG T)).obj K) := by
  unfold finiteDiscreteCoefficientPullbackIso realization_combine
    coefficientDerivedUpperStar finiteDiscreteRealization FiniteDiscreteInternalModules
  dsimp only [id]
  simp only [
    Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryPlusCompatibility,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.refl_hom,
    NatTrans.id_app, Functor.map_comp, Category.id_comp, Category.assoc]
  repeat' erw [CategoryTheory.Functor.map_id]
  repeat' erw [Category.id_comp]

private theorem left_comp_hom {S T U : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U)
    (N : DerivedCategory (Mod (Sheaf (ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj B) U))) :
    (coefficientDerivedUpperStarComp (Profinite.continuousMapRingObj B) f g).hom.app N =
      (leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.continuousMapRingObj B) (f ≫ g)).hom.app N ≫
      (Functor.mapDerivedCategoryTriangleIso
        (upperStarComp (Profinite.continuousMapRingObj B) f g)).hom.app N ≫
      D(upperStar (Profinite.continuousMapRingObj B) f).map
        ((leftDerivedUpperStarIsoMapDerivedCategory
          (Profinite.continuousMapRingObj B) g).inv.app N) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.continuousMapRingObj B) f).inv.app
          ((coefficientDerivedUpperStar (Profinite.continuousMapRingObj B) g).obj N) := by
  unfold coefficientDerivedUpperStarComp leftDerivedUpperStarComp Functor.leftDerivedFunctorNatIso
    Functor.leftDerivedFunctorCompIso
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Functor.mapDerivedCategoryTriangleIso]
  rw [Iso.inv_hom_id_app_assoc]
  rfl

private theorem pullback_comp {S T U : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U)
    (K : FiniteDiscreteEtalePlus B U) :
    (finiteDiscreteRealization B S
        (finiteDiscreteCoefficientEquivalence B eR G hG S)).map
      ((Etale.upperStarPlusComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) f g).hom.app K) ≫
      (finiteDiscreteCoefficientPullbackIso B eR G hG f).hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).obj K) ≫
      (coefficientDerivedUpperStar (Profinite.continuousMapRingObj B) f).map
        ((finiteDiscreteCoefficientPullbackIso B eR G hG g).hom.app K) =
    (finiteDiscreteCoefficientPullbackIso B eR G hG (f ≫ g)).hom.app K ≫
      (coefficientDerivedUpperStarComp (Profinite.continuousMapRingObj B) f g).hom.app
        ((finiteDiscreteRealization B U
          (finiteDiscreteCoefficientEquivalence B eR G hG U)).obj K) := by
  have hc : DerivedCategory.Plus.ι.map
      ((Etale.upperStarPlusComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) f g).hom.app K) =
      (Functor.mapDerivedCategoryTriangleIso
        (Etale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) f g)).hom.app
          (DerivedCategory.Plus.ι.obj K) := by
    simp only [Etale.upperStarPlusComp, Iso.trans_hom, NatTrans.comp_app,
      Functor.map_comp, Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app,
      Functor.mapDerivedCategoryTriangleIso, Iso.symm_hom]
  have hn := (realization_combine B eR G hG S).hom.naturality
    ((Etale.upperStarPlusComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) f g).hom.app K)
  simp only [Functor.comp_map, hc] at hn
  have H := transport_comp
    D(upperStar (Profinite.continuousMapRingObj B) f)
    (coefficientDerivedUpperStar (Profinite.continuousMapRingObj B) f)
    D(upperStar (Profinite.continuousMapRingObj B) g)
    (coefficientDerivedUpperStar (Profinite.continuousMapRingObj B) g)
    D(upperStar (Profinite.continuousMapRingObj B) (f ≫ g))
    (coefficientDerivedUpperStar (Profinite.continuousMapRingObj B) (f ≫ g))
    (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.continuousMapRingObj B) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.continuousMapRingObj B) g)
    (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.continuousMapRingObj B) (f ≫ g))
    (Functor.mapDerivedCategoryTriangleIso
      (upperStarComp (Profinite.continuousMapRingObj B) f g))
    ((realization_combine B eR G hG S).app
      (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) (f ≫ g)).obj K))
    ((realization_combine B eR G hG S).app
      (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).obj
        (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).obj K)))
    ((realization_combine B eR G hG T).app
      (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).obj K))
    ((realization_combine B eR G hG U).app K)
    _ _
    ((Functor.mapDerivedCategorySquareIso
      (finiteDiscreteCoefficientSheafPullbackIso B eR G hG f)).hom.app
        (DerivedCategory.Plus.ι.obj
          (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).obj K)))
    ((Functor.mapDerivedCategorySquareIso
      (finiteDiscreteCoefficientSheafPullbackIso B eR G hG g)).hom.app
        (DerivedCategory.Plus.ι.obj K))
    ((Functor.mapDerivedCategorySquareIso
      (finiteDiscreteCoefficientSheafPullbackIso B eR G hG (f ≫ g))).hom.app
        (DerivedCategory.Plus.ι.obj K)) hn
    (derived_sheaf_comp B eR G hG f g (DerivedCategory.Plus.ι.obj K))
  simpa only [pullback_hom B eR G hG, left_comp_hom B, Category.assoc,
    Iso.app, Functor.comp_obj] using H

set_option backward.isDefEq.respectTransparency true in
/-- The canonical derived coefficient pullback comparison commutes with square transport.
Source: Bhatt--Scholze, Lemma 5.4.1; Proposition 5.3.2
(blueprint: lem-weil-pbc-finite-discrete-coefficient-square-coherence).

Proof in words. Use finiteDiscreteCoefficientRestrictionIso_comp from
the module `FiniteDiscreteCoefficientRestrictionCoherence` for the specified restriction
comparison. Its proof cancels the intermediate encoding isomorphism after forgetting
module actions and uses naturality of restriction composition.
Conjugate this identity through the adjunctions used
in finiteDiscreteCoefficientProEtalePullbackIso. The composition law for conjugation gives
the corresponding identity for the ordinary pullback comparison, including the ordinary
etale/pro-etale comparison. Apply exact functors termwise to complexes and then localize;
Functor.mapDerivedCategorySquareIso_hom_app_comp from the source library gives
the component composition compatibility, while naturality of the derived comparisons
transports the ordinary composition maps. Restrict the etale source to D+ using
mapDerivedCategoryPlusCompatibility.
Finally replace the exact internal pullbacks by their total left derived functors.
Their composition isomorphism is defined by the same replacement, so the replacement
isomorphisms cancel. Transporting along sq.w yields exactly coefficientAmbientSquare.
Thus the resulting equation is the displayed equation for the specified comparison.
-/
theorem finiteDiscreteCoefficientPullbackIso_square
    : CoefficientPullbackSquare B (Profinite.continuousMapRingObj B)
      (fun T ↦ finiteDiscreteRealization B T
        (finiteDiscreteCoefficientEquivalence B eR G hG T))
      (finiteDiscreteCoefficientPullbackIso B eR G hG) := by
  exact square_of_comp B (Profinite.continuousMapRingObj B)
    (fun T ↦ finiteDiscreteRealization B T
      (finiteDiscreteCoefficientEquivalence B eR G hG T))
    (finiteDiscreteCoefficientPullbackIso B eR G hG) (pullback_comp B eR G hG)

end AlgebraicGeometry.ProEtale.CondensedRing

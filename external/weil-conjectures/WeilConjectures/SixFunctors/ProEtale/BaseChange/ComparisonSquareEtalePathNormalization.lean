/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquarePaths
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquarePasting

/-! # Normalization of the etale comparison-square path under exact derivation

These statements use the defining expressions of the comparison isomorphisms of
`SixFunctors/ProEtale/BaseChange/SmoothBaseChange.lean`; they are the inputs of
`AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap` there.
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.ComparisonCore

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  Functor.mapDerivedCategory Functor.mapDerivedCategoryNatIso

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section ExactPath

variable {A B B' C P Q R : Type*}
  [Category A] [Category B] [Category B'] [Category C]
  [Category P] [Category Q] [Category R]
  [Abelian A] [Abelian B] [Abelian B'] [Abelian C]
  [Abelian P] [Abelian Q] [Abelian R]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory B']
  [HasDerivedCategory C] [HasDerivedCategory P] [HasDerivedCategory Q]
  [HasDerivedCategory R]
  (F : A ⥤ B) (G : B ⥤ C) (F' : A ⥤ B') (G' : B' ⥤ C)
  (K₀ : A ⥤ P) (K₁ : B' ⥤ Q) (K₂ : C ⥤ R) (P₁ : P ⥤ Q) (P₂ : Q ⥤ R)
  [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
  [K₀.Additive] [K₁.Additive] [K₂.Additive] [P₁.Additive] [P₂.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits K₀] [PreservesFiniteColimits K₀]
  [PreservesFiniteLimits K₁] [PreservesFiniteColimits K₁]
  [PreservesFiniteLimits K₂] [PreservesFiniteColimits K₂]
  [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁]
  [PreservesFiniteLimits P₂] [PreservesFiniteColimits P₂]

private theorem exact_path (e : F ⋙ G ≅ F' ⋙ G')
    (a : F' ⋙ K₁ ≅ K₀ ⋙ P₁) (b : G' ⋙ K₂ ≅ K₁ ⋙ P₂) :
    (Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso F G) D(K₂)).hom ≫
      (Functor.mapDerivedCategorySquareIso (F₁ := F ⋙ G) (F₂ := K₂)
        (G₁ := K₀) (G₂ := P₁ ⋙ P₂)
        (Functor.isoWhiskerRight e K₂ ≪≫
          Functor.isoWhiskerLeft F' b ≪≫ Functor.isoWhiskerRight a P₂)).hom ≫
      (Functor.isoWhiskerLeft D(K₀) (Functor.mapDerivedCategoryCompIso P₁ P₂)).inv =
    (Functor.isoWhiskerRight (Functor.mapDerivedCategorySquareIso e) D(K₂)).hom ≫
      (Functor.isoWhiskerLeft D(F') (Functor.mapDerivedCategorySquareIso b)).hom ≫
      (Functor.isoWhiskerRight (Functor.mapDerivedCategorySquareIso a) D(P₂)).hom := by
  have hw := Functor.mapDerivedCategoryNatIso_isoWhiskerRight e K₂
  have hp := Functor.mapDerivedCategorySquareIso_paste F' G' P₁ P₂ K₀ K₁ K₂ a b
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapDerivedCategoryNatIso_trans] at hp ⊢
  have hw' : (Functor.mapDerivedCategoryCompIso (F ⋙ G) K₂).hom ≫
      (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight e K₂)).hom =
      Functor.whiskerRight (Functor.mapDerivedCategoryNatIso e).hom D(K₂) ≫
        (Functor.mapDerivedCategoryCompIso (F' ⋙ G') K₂).hom := by
    rw [← Iso.eq_inv_comp, ← Category.assoc, ← Iso.comp_inv_eq]
    exact hw
  simp only [Category.assoc] at hp ⊢
  rw [reassoc_of% hw', reassoc_of% hp]
  simp only [Functor.isoWhiskerRight_hom, Iso.trans_hom, Iso.symm_hom,
    Functor.whiskerRight_comp, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

private theorem exact_path_with_comparisons (e : F ⋙ G ≅ F' ⋙ G')
    (a : F' ⋙ K₁ ≅ K₀ ⋙ P₁) (b : G' ⋙ K₂ ≅ K₁ ⋙ P₂)
    (P₁' : DerivedCategory P ⥤ DerivedCategory Q)
    (P₂' : DerivedCategory Q ⥤ DerivedCategory R)
    (j₁ : P₁' ≅ D(P₁)) (j₂ : P₂' ≅ D(P₂)) (M : DerivedCategory A) :
    (Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso F G) D(K₂)).hom.app M ≫
      (Functor.mapDerivedCategorySquareIso (F₁ := F ⋙ G) (F₂ := K₂)
        (G₁ := K₀) (G₂ := P₁ ⋙ P₂)
        (Functor.isoWhiskerRight e K₂ ≪≫
          Functor.isoWhiskerLeft F' b ≪≫ Functor.isoWhiskerRight a P₂)).hom.app M ≫
      (Functor.mapDerivedCategoryCompIso P₁ P₂).inv.app (D(K₀).obj M) ≫
      D(P₂).map (j₁.inv.app (D(K₀).obj M)) ≫
      j₂.inv.app (P₁'.obj (D(K₀).obj M)) =
    D(K₂).map ((Functor.mapDerivedCategorySquareIso e).hom.app M) ≫
      ((Functor.mapDerivedCategorySquareIso b).hom.app (D(F').obj M) ≫
        j₂.inv.app (D(K₁).obj (D(F').obj M))) ≫
      P₂'.map ((Functor.mapDerivedCategorySquareIso a).hom.app M ≫
        j₁.inv.app (D(K₀).obj M)) := by
  have hp := congr_app (exact_path F G F' G' K₀ K₁ K₂ P₁ P₂ e a b) M
  simp only [NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] at hp ⊢
  rw [reassoc_of% hp]
  simp only [Functor.map_comp, Category.assoc]
  rw [← j₂.inv.naturality_assoc]
  rw [← j₂.inv.naturality]

private noncomputable def exactOrdinaryPath
    (e : F ⋙ G ≅ F' ⋙ G') (a : F' ⋙ K₁ ≅ K₀ ⋙ P₁)
    (b : G' ⋙ K₂ ≅ K₁ ⋙ P₂) :
    (F ⋙ G) ⋙ K₂ ≅ K₀ ⋙ (P₁ ⋙ P₂) :=
  Functor.isoWhiskerRight e K₂ ≪≫
    Functor.isoWhiskerLeft F' b ≪≫ Functor.isoWhiskerRight a P₂

private noncomputable def exactSourceIso :
    D((F ⋙ G) ⋙ K₂) ≅ D(F) ⋙ D(G) ⋙ D(K₂) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso _ _).symm _

private noncomputable def exactTargetIso
    (P₁' : DerivedCategory P ⥤ DerivedCategory Q)
    (P₂' : DerivedCategory Q ⥤ DerivedCategory R)
    (j₁ : P₁' ≅ D(P₁)) (j₂ : P₂' ≅ D(P₂)) :
    D(K₀ ⋙ (P₁ ⋙ P₂)) ≅ D(K₀) ⋙ P₁' ⋙ P₂' :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight j₁.symm _ ≪≫ Functor.isoWhiskerLeft _ j₂.symm)

private noncomputable def exactDerivedPath
    (e : F ⋙ G ≅ F' ⋙ G') (a : F' ⋙ K₁ ≅ K₀ ⋙ P₁)
    (b : G' ⋙ K₂ ≅ K₁ ⋙ P₂)
    (P₁' : DerivedCategory P ⥤ DerivedCategory Q)
    (P₂' : DerivedCategory Q ⥤ DerivedCategory R)
    (j₁ : P₁' ≅ D(P₁)) (j₂ : P₂' ≅ D(P₂)) (M : DerivedCategory.Plus A) :
    (DerivedCategory.Plus.ι ⋙ D(K₂)).obj (D+(G).obj (D+(F).obj M)) ⟶
      P₂'.obj (P₁'.obj ((DerivedCategory.Plus.ι ⋙ D(K₀)).obj M)) :=
  (exactSourceIso F G K₂).inv.app M.obj ≫
    (Functor.mapDerivedCategoryNatIso
      (exactOrdinaryPath F G F' G' K₀ K₁ K₂ P₁ P₂ e a b)).hom.app M.obj ≫
    (exactTargetIso K₀ P₁ P₂ P₁' P₂' j₁ j₂).hom.app M.obj

private theorem exact_path_plus (e : F ⋙ G ≅ F' ⋙ G')
    (a : F' ⋙ K₁ ≅ K₀ ⋙ P₁) (b : G' ⋙ K₂ ≅ K₁ ⋙ P₂)
    (P₁' : DerivedCategory P ⥤ DerivedCategory Q)
    (P₂' : DerivedCategory Q ⥤ DerivedCategory R)
    (j₁ : P₁' ≅ D(P₁)) (j₂ : P₂' ≅ D(P₂)) (M : DerivedCategory.Plus A) :
    @Eq
      ((DerivedCategory.Plus.ι ⋙ D(K₂)).obj (D+(G).obj (D+(F).obj M)) ⟶
        P₂'.obj (P₁'.obj ((DerivedCategory.Plus.ι ⋙ D(K₀)).obj M)))
      (exactDerivedPath F G F' G' K₀ K₁ K₂ P₁ P₂ e a b P₁' P₂' j₁ j₂ M)
      (D(K₂).map ((Functor.mapDerivedCategorySquareIso e).hom.app M.obj) ≫
        ((Functor.mapDerivedCategorySquareIso b).hom.app (D+(F').obj M).obj ≫
          j₂.inv.app (D(K₁).obj (D+(F').obj M).obj)) ≫
        P₂'.map ((Functor.mapDerivedCategorySquareIso a).hom.app M.obj ≫
          j₁.inv.app (D(K₀).obj M.obj))) := by
  dsimp only [Functor.mapDerivedCategoryPlus, ObjectProperty.lift,
    DerivedCategory.Plus.ι, ObjectProperty.ι, inducedFunctor, Functor.comp_obj]
  simpa only [exactDerivedPath, exactSourceIso, exactTargetIso, exactOrdinaryPath,
    Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc] using
    exact_path_with_comparisons F G F' G' K₀ K₁ K₂ P₁ P₂ e a b P₁' P₂' j₁ j₂ M.obj

private theorem restriction_path
    (H H' : A ⥤ C) [H.Additive] [H'.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    (e₁ : H ≅ F ⋙ G) (e₀ : H ≅ H') (e₂ : H' ≅ F' ⋙ G')
    (t : D+(H) ≅ D+(H')) (M : DerivedCategory.Plus A)
    (ht : DerivedCategory.Plus.ι.map (t.hom.app M) =
      (Functor.mapDerivedCategoryNatIso e₀).hom.app M.obj) :
    DerivedCategory.Plus.ι.map
      (((Functor.mapDerivedCategoryPlusNatIso e₁ ≪≫
          Functor.mapDerivedCategoryPlusCompIso F G).symm ≪≫ t ≪≫
        Functor.mapDerivedCategoryPlusNatIso e₂ ≪≫
          Functor.mapDerivedCategoryPlusCompIso F' G').hom.app M) =
    (Functor.mapDerivedCategorySquareIso (F₁ := F) (F₂ := G)
      (G₁ := F') (G₂ := G') (e₁.symm ≪≫ e₀ ≪≫ e₂)).hom.app M.obj := by
  have hcomp : DerivedCategory.Plus.ι.mapIso
      ((Functor.mapDerivedCategoryPlusNatIso e₁ ≪≫
        Functor.mapDerivedCategoryPlusCompIso F G).app M) =
      (Functor.mapDerivedCategoryNatIso e₁ ≪≫
        (Functor.mapDerivedCategoryCompIso F G).symm).app M.obj := by
    apply Iso.ext
    simp only [Functor.mapIso_hom, Iso.app_hom, Iso.trans_hom, NatTrans.comp_app,
      Functor.map_comp, Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]
    rfl
  have hi : DerivedCategory.Plus.ι.map
      ((Functor.mapDerivedCategoryPlusNatIso e₁ ≪≫
        Functor.mapDerivedCategoryPlusCompIso F G).inv.app M) =
      (Functor.mapDerivedCategoryNatIso e₁ ≪≫
        (Functor.mapDerivedCategoryCompIso F G).symm).inv.app M.obj := congrArg Iso.inv hcomp
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp]
  rw [hi, ht, Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]
  simp only [Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm, NatTrans.comp_app, Iso.trans_inv,
    Category.assoc]
  rfl

end ExactPath

private theorem plus_transport (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    DerivedCategory.Plus.ι.map
      ((eqToIso (congrArg (fun a ↦ D+(Etale.upperStar (ModuleCat.{u + 1} Λ) a)) h)).hom.app M) =
    (Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (Etale.upperStar (ModuleCat.{u + 1} Λ)) h))).hom.app M.obj := by
  subst g
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Functor.mapDerivedCategoryNatIso_refl]
  rfl

private theorem plus_square_expansion (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) :
    Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq =
      ((Functor.mapDerivedCategoryPlusNatIso
          (Etale.upperStarComp (ModuleCat.{u + 1} Λ) f' g) ≪≫
        Functor.mapDerivedCategoryPlusCompIso (Etale.upperStar _ g)
          (Etale.upperStar _ f')).symm ≪≫
        eqToIso (congrArg (fun a ↦ D+(Etale.upperStar (ModuleCat.{u + 1} Λ) a))
          sq.w.symm) ≪≫
        Functor.mapDerivedCategoryPlusNatIso
          (Etale.upperStarComp (ModuleCat.{u + 1} Λ) g' f) ≪≫
        Functor.mapDerivedCategoryPlusCompIso (Etale.upperStar _ f)
          (Etale.upperStar _ g')) := by
  unfold Etale.pullbackSquareComparison
  rfl

private theorem square_restrict (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    DerivedCategory.Plus.ι.map
      ((Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq).hom.app M) =
    (Functor.mapDerivedCategorySquareIso (F₁ := Etale.upperStar _ g)
      (F₂ := Etale.upperStar _ f') (G₁ := Etale.upperStar _ f)
      (G₂ := Etale.upperStar _ g')
      ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) f' g).symm ≪≫
        eqToIso (congrArg (Etale.upperStar (ModuleCat.{u + 1} Λ)) sq.w.symm) ≪≫
          Etale.upperStarComp (ModuleCat.{u + 1} Λ) g' f)).hom.app M.obj := by
  have h := restriction_path
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g)
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f')
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f)
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g')
    (Etale.upperStar (ModuleCat.{u + 1} Λ) (f' ≫ g))
    (Etale.upperStar (ModuleCat.{u + 1} Λ) (g' ≫ f))
    (Etale.upperStarComp (ModuleCat.{u + 1} Λ) f' g)
    (eqToIso (congrArg (Etale.upperStar (ModuleCat.{u + 1} Λ)) sq.w.symm))
    (Etale.upperStarComp (ModuleCat.{u + 1} Λ) g' f)
    (eqToIso (congrArg (fun a ↦ D+(Etale.upperStar (ModuleCat.{u + 1} Λ) a))
      sq.w.symm)) M (plus_transport Λ sq.w.symm M)
  have hp := congrArg (fun e ↦ DerivedCategory.Plus.ι.map (e.hom.app M))
    (plus_square_expansion Λ sq)
  exact hp.trans h

private theorem edge_derived (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (  (fun {U V : Scheme.{u}} (g : U ⟶ V) (Λ : Type (u + 1)) [CommRing Λ] ↦
    Functor.isoWhiskerRight
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusCompatibility
        D(ν^*(U)[ModuleCat.{u + 1} Λ]) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Functor.mapDerivedCategoryCompIso _ _ ≪≫
          Functor.mapDerivedCategoryNatIso
            (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ D(ν^*(V)[ModuleCat.{u + 1} Λ]))
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).symm
) f Λ).hom.app M =
      (Functor.mapDerivedCategorySquareIso
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).symm).hom.app M.obj ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f).inv.app
        (D(ν^*(Y)[ModuleCat.{u + 1} Λ]).obj M.obj) := by
  simp only [ Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.trans_hom, Iso.symm_hom,
    Iso.refl_hom, NatTrans.comp_app, NatTrans.id_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

private theorem etale_path_expansion (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) :
    comparisonSquareEtalePath Λ sq =
      exactOrdinaryPath
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g)
        (Etale.upperStar (ModuleCat.{u + 1} Λ) f')
        (Etale.upperStar (ModuleCat.{u + 1} Λ) f)
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g')
        (ν^*(Y)[ModuleCat.{u + 1} Λ]) (ν^*(X)[ModuleCat.{u + 1} Λ])
        (ν^*(X')[ModuleCat.{u + 1} Λ])
        (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f)
        (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g')
        (etaleComparisonSquare (ModuleCat.{u + 1} Λ) sq)
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).symm
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g').symm := by
  rfl

private theorem source_expansion (Λ : Type (u + 1)) [CommRing Λ]
    {X' Y' Y : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') :
    comparisonSquareSourceIso Λ g f' =
      exactSourceIso (Etale.upperStar (ModuleCat.{u + 1} Λ) g)
        (Etale.upperStar (ModuleCat.{u + 1} Λ) f')
        (ν^*(X')[ModuleCat.{u + 1} Λ]) := by
  rfl

private theorem target_expansion (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} (g' : X' ⟶ X) (f : X ⟶ Y) :
    comparisonSquareTargetIso Λ g' f =
      exactTargetIso (ν^*(Y)[ModuleCat.{u + 1} Λ])
        (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f)
        (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g')
        L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f)
        L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g')
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f)
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g') := by
  rfl

private theorem derived_path_expansion (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    comparisonSquareDerivedPath Λ g' f' f g (comparisonSquareEtalePath Λ sq) M =
    exactDerivedPath
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g)
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f')
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f)
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g')
    (ν^*(Y)[ModuleCat.{u + 1} Λ]) (ν^*(X)[ModuleCat.{u + 1} Λ])
    (ν^*(X')[ModuleCat.{u + 1} Λ])
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f)
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g')
    (etaleComparisonSquare (ModuleCat.{u + 1} Λ) sq)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).symm
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g').symm
    L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f)
    L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g')
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g') M := by
  unfold comparisonSquareDerivedPath
  rw [etale_path_expansion, source_expansion, target_expansion]
  rfl

private theorem normalization_aux
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (α : (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f')).obj
        ((D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g)).obj M) ⟶
      (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g')).obj
        ((D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f)).obj M))
    (ht : DerivedCategory.Plus.ι.map α =
      (Functor.mapDerivedCategorySquareIso
        (F₁ := Etale.upperStar (ModuleCat.{u + 1} Λ) g)
        (F₂ := Etale.upperStar (ModuleCat.{u + 1} Λ) f')
        (G₁ := Etale.upperStar (ModuleCat.{u + 1} Λ) f)
        (G₂ := Etale.upperStar (ModuleCat.{u + 1} Λ) g')
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) f' g).symm ≪≫
          eqToIso (congrArg (Etale.upperStar (ModuleCat.{u + 1} Λ)) sq.w.symm) ≪≫
            Etale.upperStarComp (ModuleCat.{u + 1} Λ) g' f)).hom.app
        M.obj) :
    HEq
      (comparisonSquareDerivedPath Λ g' f' f g (comparisonSquareEtalePath Λ
        { toCommSq := sq.toCommSq, isoPullback := sq.isoPullback,
          hom_fst := sq.isoPullback_hom_fst, hom_snd := sq.isoPullback_hom_snd }) M)
      ((DerivedCategory.Plus.ι ⋙ D(ν^*(X')[ModuleCat.{u + 1} Λ])).map
            α ≫
          (  (fun {U V : Scheme.{u}} (g : U ⟶ V) (Λ : Type (u + 1)) [CommRing Λ] ↦
    Functor.isoWhiskerRight
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusCompatibility
        D(ν^*(U)[ModuleCat.{u + 1} Λ]) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Functor.mapDerivedCategoryCompIso _ _ ≪≫
          Functor.mapDerivedCategoryNatIso
            (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ D(ν^*(V)[ModuleCat.{u + 1} Λ]))
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).symm
) g' Λ).hom.app
            (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj M) ≫
          L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').map
            ((  (fun {U V : Scheme.{u}} (g : U ⟶ V) (Λ : Type (u + 1)) [CommRing Λ] ↦
    Functor.isoWhiskerRight
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusCompatibility
        D(ν^*(U)[ModuleCat.{u + 1} Λ]) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Functor.mapDerivedCategoryCompIso _ _ ≪≫
          Functor.mapDerivedCategoryNatIso
            (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ D(ν^*(V)[ModuleCat.{u + 1} Λ]))
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).symm
) f Λ).hom.app M)) := by
  let cs : ChosenCartesianSquare g' f' f g :=
    { toCommSq := sq.toCommSq, isoPullback := sq.isoPullback,
      hom_fst := sq.isoPullback_hom_fst, hom_snd := sq.isoPullback_hom_snd }
  have h := exact_path_plus
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g)
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f')
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f)
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g')
    (ν^*(Y)[ModuleCat.{u + 1} Λ]) (ν^*(X)[ModuleCat.{u + 1} Λ])
    (ν^*(X')[ModuleCat.{u + 1} Λ])
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f)
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g')
    (etaleComparisonSquare (ModuleCat.{u + 1} Λ) cs)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).symm
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g').symm
    L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f)
    L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g')
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g') M
  have hs := congrArg
    (fun t ↦ D(ν^*(X')[ModuleCat.{u + 1} Λ]).map t) ht
  have he := edge_derived Λ g'
    (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj M)
  have hf := congrArg
    (fun t ↦ L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').map t)
    (edge_derived Λ f M)
  have hr := congrArg₂ (fun a b ↦ a ≫ b) hs
    (congrArg₂ (fun a b ↦ a ≫ b) he hf)
  have hh := h.trans hr.symm
  rw [derived_path_expansion Λ cs M]
  simpa only [cs, Functor.comp_map] using heq_of_eq hh

/-- Exact derivation of the ordinary Etale path, with the common source and target
composition factors. This identity concerns one path and assumes no square coherence.
The heterogeneous equality retains the two endpoint presentations; these endpoints
are definitionally equal. It avoids unfolding the derived functor constructions
when joining the two normalization identities.
Source: Stacks, Tag 0B65.

Proof: write C(F,G) for mapDerivedCategoryCompIso F G and J(f) for
leftDerivedUpperStarIsoMapDerivedCategory at f. First expand the ordinary path as
(se whiskered by nu_X') followed by the comparisons at g' and f. Derivation preserves
this composite by mapDerivedCategoryNatIso_trans. Apply
mapDerivedCategoryNatIso_isoWhiskerRight to its first and last factors and
mapDerivedCategoryNatIso_isoWhiskerLeft to its middle factor. The equation
mapDerivedCategoryCompIso_assoc collects the outer C factors into
comparisonSquareSourceIso and the exact-composition part of comparisonSquareTargetIso;
the intermediate C factors cancel with their inverses. The remaining three maps are
D(nu_X') applied to the derived etale square, the derived edge comparison at g', and
D(g'_proet) applied to the derived edge comparison at f.

For the first map, expand se using etaleComparisonSquare and the derived square using
Etale.pullbackSquareComparison and Etale.upperStarPlusComp. The ordinary composition
comparison is Etale.upperStarComp. The equations
Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app and
Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app identify the composition factors;
equality induction on the square's commutativity identifies the middle transports.
For the other maps, comparisonCoefficientPullbackIso is definitionally the inverse of
comparisonUpperStarCompUpperStarIso. Expanding leftDerivedUpperStarComparisonIso gives
exactly its derived image conjugated by C and followed by J(f).inv. Naturality of
J(g').inv moves it past the derived f-comparison, producing L(g') of that comparison.
The two remaining inverse J factors are precisely the final target factor. Evaluate
at M and use associativity and inverse-hom cancellation. No pro-etale square identity
or underived coherence equation is used; identity edges and the zero input satisfy
the same equations. -/
theorem comparisonSquareEtalePath_normalization
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    HEq
      (comparisonSquareDerivedPath Λ g' f' f g (comparisonSquareEtalePath Λ
        { toCommSq := sq.toCommSq, isoPullback := sq.isoPullback,
          hom_fst := sq.isoPullback_hom_fst, hom_snd := sq.isoPullback_hom_snd }) M)
      ((DerivedCategory.Plus.ι ⋙ D(ν^*(X')[ModuleCat.{u + 1} Λ])).map
            ((Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app M) ≫
          (  (fun {U V : Scheme.{u}} (g : U ⟶ V) (Λ : Type (u + 1)) [CommRing Λ] ↦
    Functor.isoWhiskerRight
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusCompatibility
        D(ν^*(U)[ModuleCat.{u + 1} Λ]) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Functor.mapDerivedCategoryCompIso _ _ ≪≫
          Functor.mapDerivedCategoryNatIso
            (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ D(ν^*(V)[ModuleCat.{u + 1} Λ]))
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).symm
) g' Λ).hom.app
            (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj M) ≫
          L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').map
            ((  (fun {U V : Scheme.{u}} (g : U ⟶ V) (Λ : Type (u + 1)) [CommRing Λ] ↦
    Functor.isoWhiskerRight
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusCompatibility
        D(ν^*(U)[ModuleCat.{u + 1} Λ]) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Functor.mapDerivedCategoryCompIso _ _ ≪≫
          Functor.mapDerivedCategoryNatIso
            (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ D(ν^*(V)[ModuleCat.{u + 1} Λ]))
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).symm
) f Λ).hom.app M)) := by
  exact normalization_aux Λ sq M
    ((Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app M)
    (square_restrict Λ sq.toCommSq M)

end AlgebraicGeometry.ProEtale.ComparisonCore

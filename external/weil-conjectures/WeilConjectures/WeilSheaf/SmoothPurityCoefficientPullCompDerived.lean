/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityCoefficientPullCompOrdinary
public import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate

/-! # Derived coefficient composition for restriction and pullback -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

/-- Changing the three vertical functors by natural isomorphisms preserves a coefficient
composition square. -/
lemma purity_restriction_square_comp_transport
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    {A : C₁ ⥤ C₀} {B : C₂ ⥤ C₁} {C : C₂ ⥤ C₀}
    {A' : D₁ ⥤ D₀} {B' : D₂ ⥤ D₁} {C' : D₂ ⥤ D₀}
    {G₀ H₀ : C₀ ⥤ D₀} {G₁ H₁ : C₁ ⥤ D₁} {G₂ H₂ : C₂ ⥤ D₂}
    (e₀ : G₀ ≅ H₀) (e₁ : G₁ ≅ H₁) (e₂ : G₂ ≅ H₂)
    (a : A ⋙ H₀ ≅ H₁ ⋙ A') (b : B ⋙ H₁ ≅ H₂ ⋙ B')
    (c : C ⋙ H₀ ≅ H₂ ⋙ C') (κ : B ⋙ A ≅ C) (κ' : B' ⋙ A' ≅ C')
    (h : ∀ K, H₀.map (κ.inv.app K) ≫ a.hom.app (B.obj K) ≫ A'.map (b.hom.app K) =
      c.hom.app K ≫ κ'.inv.app (H₂.obj K)) (K : C₂) :
    G₀.map (κ.inv.app K) ≫
        (e₀.hom.app (A.obj (B.obj K)) ≫ a.hom.app (B.obj K) ≫
          A'.map (e₁.inv.app (B.obj K))) ≫
        A'.map (e₁.hom.app (B.obj K) ≫ b.hom.app K ≫ B'.map (e₂.inv.app K)) =
      (e₀.hom.app (C.obj K) ≫ c.hom.app K ≫ C'.map (e₂.inv.app K)) ≫
        κ'.inv.app (G₂.obj K) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← A'.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  have hn := e₀.hom.naturality (κ.inv.app K)
  dsimp only [Functor.comp_obj] at hn
  rw [reassoc_of% hn, reassoc_of% (h K)]
  exact congrArg (e₀.hom.app (C.obj K) ≫ c.hom.app K ≫ ·)
    (κ'.inv.naturality (e₂.inv.app K)).symm

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [MonObj Λ''] [IsCommMonObj Λ'']
  (a : Λ ⟶ Λ') [IsMonHom a] (b : Λ' ⟶ Λ'') [IsMonHom b]
  (c : Λ ⟶ Λ'') [IsMonHom c] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Exact restriction/pullback squares compose after passing to the derived category. -/
theorem derivedComapUpperStarSquare_inv_app_of_coefficient_comp (hc : a ≫ b = c)
    (K : DerivedCategory
      (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ'' Y))) :
    D((f)^*⟦Λ⟧).map ((Mod.mapDerivedCategoryComapCompIso
        (coefficientMap a Y) (coefficientMap b Y) (coefficientMap c Y)
        (coefficientMap_comp_eq a b c hc Y)).inv.app K) ≫
      (Functor.mapDerivedCategorySquareIso (comapUpperStarIso a f).symm).hom.app
        (D(Mod.comap (coefficientMap b Y)).obj K) ≫
      D(Mod.comap (coefficientMap a X)).map
        ((Functor.mapDerivedCategorySquareIso (comapUpperStarIso b f).symm).hom.app K) =
    (Functor.mapDerivedCategorySquareIso (comapUpperStarIso c f).symm).hom.app K ≫
      (Mod.mapDerivedCategoryComapCompIso
        (coefficientMap a X) (coefficientMap b X) (coefficientMap c X)
        (coefficientMap_comp_eq a b c hc X)).inv.app (D((f)^*⟦Λ''⟧).obj K) := by
  have h := Functor.mapDerivedCategorySquareIso_comp
    (Mod.comap (coefficientMap b Y)) (Mod.comap (coefficientMap a Y))
    (Mod.comap (coefficientMap c Y))
    (Mod.comap (coefficientMap b X)) (Mod.comap (coefficientMap a X))
    (Mod.comap (coefficientMap c X))
    ((f)^*⟦Λ''⟧) ((f)^*⟦Λ'⟧) ((f)^*⟦Λ⟧)
    (comapUpperStarIso b f).symm (comapUpperStarIso a f).symm
    (comapUpperStarIso c f).symm
    (comapCoefficientMapCompIso a b c hc Y).symm
    (comapCoefficientMapCompIso a b c hc X).symm
    (comapUpperStarIso_inv_app_of_coefficient_comp a b c f hc)
  have hK := congrArg (fun e ↦ e.hom.app K) h
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc,
    Mod.mapDerivedCategoryComapCompIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapDerivedCategoryNatIso_symm, comapCoefficientMapCompIso] using hK

/-- The actual left-derived pullbacks satisfy the same coefficient composition identity. -/
theorem derivedComapLeftDerivedUpperStarIso_hom_app_of_coefficient_comp
    (hc : a ≫ b = c)
    (K : DerivedCategory
      (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ'' Y))) :
    L((f)^*⟦Λ⟧).map ((Mod.mapDerivedCategoryComapCompIso
        (coefficientMap a Y) (coefficientMap b Y) (coefficientMap c Y)
        (coefficientMap_comp_eq a b c hc Y)).inv.app K) ≫
      (derivedComapLeftDerivedUpperStarIso a f).hom.app
        (D(Mod.comap (coefficientMap b Y)).obj K) ≫
      D(Mod.comap (coefficientMap a X)).map
        ((derivedComapLeftDerivedUpperStarIso b f).hom.app K) =
    (derivedComapLeftDerivedUpperStarIso c f).hom.app K ≫
      (Mod.mapDerivedCategoryComapCompIso
        (coefficientMap a X) (coefficientMap b X) (coefficientMap c X)
        (coefficientMap_comp_eq a b c hc X)).inv.app (L((f)^*⟦Λ''⟧).obj K) := by
  exact purity_restriction_square_comp_transport
    (f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory
    (f)^*⟦Λ'⟧.leftDerivedFunctorIsoMapDerivedCategory
    (f)^*⟦Λ''⟧.leftDerivedFunctorIsoMapDerivedCategory
    (Functor.mapDerivedCategorySquareIso (comapUpperStarIso a f).symm)
    (Functor.mapDerivedCategorySquareIso (comapUpperStarIso b f).symm)
    (Functor.mapDerivedCategorySquareIso (comapUpperStarIso c f).symm)
    (Mod.mapDerivedCategoryComapCompIso _ _ _ (coefficientMap_comp_eq a b c hc Y))
    (Mod.mapDerivedCategoryComapCompIso _ _ _ (coefficientMap_comp_eq a b c hc X))
    (derivedComapUpperStarSquare_inv_app_of_coefficient_comp a b c f hc) K

end AlgebraicGeometry.ProEtale.CondensedRing

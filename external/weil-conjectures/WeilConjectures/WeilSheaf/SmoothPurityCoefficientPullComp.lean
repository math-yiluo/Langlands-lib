/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityCoefficientPullCompDerived
public import WeilConjectures.WeilSheaf.SmoothPurityCoefficientPullMate

/-! # Nonflat coefficient changes commute coherently with geometric pullback -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

/-- Inverting the three comparison squares gives the form used by mate composition. -/
lemma purity_inverse_restriction_square_comp
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    {A : C₁ ⥤ C₀} {B : C₂ ⥤ C₁} {C : C₂ ⥤ C₀}
    {A' : D₁ ⥤ D₀} {B' : D₂ ⥤ D₁} {C' : D₂ ⥤ D₀}
    {G₀ : C₀ ⥤ D₀} {G₁ : C₁ ⥤ D₁} {G₂ : C₂ ⥤ D₂}
    (a : A ⋙ G₀ ≅ G₁ ⋙ A') (b : B ⋙ G₁ ≅ G₂ ⋙ B')
    (c : C ⋙ G₀ ≅ G₂ ⋙ C') (κ : B ⋙ A ≅ C) (κ' : B' ⋙ A' ≅ C')
    (h : ∀ K, G₀.map (κ.inv.app K) ≫ a.hom.app (B.obj K) ≫ A'.map (b.hom.app K) =
      c.hom.app K ≫ κ'.inv.app (G₂.obj K)) (K : C₂) :
    c.inv.app K = κ'.inv.app (G₂.obj K) ≫ A'.map (b.inv.app K) ≫
      a.inv.app (B.obj K) ≫ G₀.map (κ.hom.app K) := by
  apply (cancel_epi (c.hom.app K)).mp
  rw [Iso.hom_inv_id_app, ← reassoc_of% (h K)]
  simp only [Functor.comp_obj, ← A'.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc,
    ← G₀.map_comp, Iso.inv_hom_id_app]

/-- Mate composition with named left comparisons, avoiding rewrites through concrete
derived functors when applying the abstract composition theorem. -/
lemma purity_mate_coefficient_comp
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*}
    [Category X₁] [Category X₂] [Category X₃]
    [Category Y₁] [Category Y₂] [Category Y₃]
    {La : X₁ ⥤ X₂} {Ra : X₂ ⥤ X₁} (adja : La ⊣ Ra)
    {Lb : X₂ ⥤ X₃} {Rb : X₃ ⥤ X₂} (adjb : Lb ⊣ Rb)
    {Lc : X₁ ⥤ X₃} {Rc : X₃ ⥤ X₁} (adjc : Lc ⊣ Rc)
    {La' : Y₁ ⥤ Y₂} {Ra' : Y₂ ⥤ Y₁} (adja' : La' ⊣ Ra')
    {Lb' : Y₂ ⥤ Y₃} {Rb' : Y₃ ⥤ Y₂} (adjb' : Lb' ⊣ Rb')
    {Lc' : Y₁ ⥤ Y₃} {Rc' : Y₃ ⥤ Y₁} (adjc' : Lc' ⊣ Rc')
    {P₁ : X₁ ⥤ Y₁} {P₂ : X₂ ⥤ Y₂} {P₃ : X₃ ⥤ Y₃}
    (ea : P₂ ⋙ Ra' ≅ Ra ⋙ P₁) (eb : P₃ ⋙ Rb' ≅ Rb ⋙ P₂)
    (ec : P₃ ⋙ Rc' ≅ Rc ⋙ P₁) (κ : Rb ⋙ Ra ≅ Rc) (κ' : Rb' ⋙ Ra' ≅ Rc')
    (h : ∀ K, ec.hom.app K = κ'.inv.app (P₃.obj K) ≫ Ra'.map (eb.hom.app K) ≫
      ea.hom.app (Rb.obj K) ≫ P₁.map (κ.hom.app K))
    (αa : P₁ ⋙ La' ⟶ La ⋙ P₂) (αb : P₂ ⋙ Lb' ⟶ Lb ⋙ P₃)
    (αc : P₁ ⋙ Lc' ⟶ Lc ⋙ P₃)
    (ha : αa = Adjunction.pushHomOfComapIso adja adja' ea)
    (hb : αb = Adjunction.pushHomOfComapIso adjb adjb' eb)
    (hc : αc = Adjunction.pushHomOfComapIso adjc adjc' ec) (K : X₁) :
    αc.app K = ((conjugateIsoEquiv (adja'.comp adjb') adjc').symm κ').hom.app (P₁.obj K) ≫
      Lb'.map (αa.app K) ≫ αb.app (La.obj K) ≫
      P₃.map (((conjugateIsoEquiv (adja.comp adjb) adjc).symm κ).inv.app K) := by
  rw [ha, hb, hc]
  exact Adjunction.pushHomOfComapIso_app_eq_comp adja adjb adjc adja' adjb' adjc'
    ea eb ec κ κ' h K

end CategoryTheory

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [MonObj Λ''] [IsCommMonObj Λ'']
  (a : Λ ⟶ Λ') [IsMonHom a] (b : Λ' ⟶ Λ'') [IsMonHom b]
  (c : Λ ⟶ Λ'') [IsMonHom c] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical pullback comparison for any composite coefficient change is the
composite of its canonical comparisons. In particular this applies to successive
reductions modulo powers of the coefficient prime. -/
theorem derivedUpperStarExtendScalarsIso_hom_app_of_coefficient_comp
    (hc : a ≫ b = c)
    (K : DerivedCategory
      (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (derivedUpperStarExtendScalarsIso c f).hom.app K =
      (Mod.derivedExtendScalarsCompIso (coefficientMap a X) (coefficientMap b X)
        (coefficientMap c X) (coefficientMap_comp_eq a b c hc X)).hom.app
        (L((f)^*⟦Λ⟧).obj K) ≫
      L(Mod.extendScalars (coefficientMap b X)).map
        ((derivedUpperStarExtendScalarsIso a f).hom.app K) ≫
      (derivedUpperStarExtendScalarsIso b f).hom.app
        (L(Mod.extendScalars (coefficientMap a Y)).obj K) ≫
      L((f)^*⟦Λ''⟧).map ((Mod.derivedExtendScalarsCompIso
        (coefficientMap a Y) (coefficientMap b Y) (coefficientMap c Y)
        (coefficientMap_comp_eq a b c hc Y)).inv.app K) := by
  have h := purity_inverse_restriction_square_comp
    (derivedComapLeftDerivedUpperStarIso a f)
    (derivedComapLeftDerivedUpperStarIso b f)
    (derivedComapLeftDerivedUpperStarIso c f)
    (Mod.mapDerivedCategoryComapCompIso _ _ _ (coefficientMap_comp_eq a b c hc Y))
    (Mod.mapDerivedCategoryComapCompIso _ _ _ (coefficientMap_comp_eq a b c hc X))
    (derivedComapLeftDerivedUpperStarIso_hom_app_of_coefficient_comp a b c f hc)
  exact purity_mate_coefficient_comp
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap b Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap c Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap b X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap c X))
    (derivedComapLeftDerivedUpperStarIso a f).symm
    (derivedComapLeftDerivedUpperStarIso b f).symm
    (derivedComapLeftDerivedUpperStarIso c f).symm
    (Mod.mapDerivedCategoryComapCompIso _ _ _ (coefficientMap_comp_eq a b c hc Y))
    (Mod.mapDerivedCategoryComapCompIso _ _ _ (coefficientMap_comp_eq a b c hc X)) h
    (derivedUpperStarExtendScalarsIso a f).hom
    (derivedUpperStarExtendScalarsIso b f).hom
    (derivedUpperStarExtendScalarsIso c f).hom
    (derivedUpperStarExtendScalarsIso_hom_eq_mate a f)
    (derivedUpperStarExtendScalarsIso_hom_eq_mate b f)
    (derivedUpperStarExtendScalarsIso_hom_eq_mate c f) K

end AlgebraicGeometry.ProEtale.CondensedRing

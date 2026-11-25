/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityCoefficientPullComp
public import WeilConjectures.WeilSheaf.SmoothPurityEquivarianceDetection
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTransition

/-! # Ordinary reduction preserves the transported Weil equation -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

private lemma purity_weil_inverse {C : Type*} [Category C] (G : C ⥤ C)
    {K L : C} (φK : G.obj K ⟶ K) (φL : G.obj L ⟶ L) (e : K ≅ L)
    (h : IsWeilEquivariant G φK φL e.hom) : IsWeilEquivariant G φL φK e.inv := by
  apply (cancel_epi (G.map e.hom)).mp
  simp only [← G.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, ← Category.assoc]
  rw [h]
  simp

/-- A coherent composition comparison is equivariant for transported Weil data. -/
lemma purity_isWeilEquivariant_compositor
    {C D E : Type*} [Category C] [Category D] [Category E]
    {G₀ : C ⥤ C} {G₁ : D ⥤ D} {G₂ : E ⥤ E}
    (T : C ⥤ D) (S : D ⥤ E) (U : C ⥤ E)
    (a : G₀ ⋙ T ≅ T ⋙ G₁) (b : G₁ ⋙ S ≅ S ⋙ G₂)
    (c : G₀ ⋙ U ≅ U ⋙ G₂) (μ : U ≅ T ⋙ S)
    (h : ∀ K, c.hom.app K = μ.hom.app (G₀.obj K) ≫ S.map (a.hom.app K) ≫
      b.hom.app (T.obj K) ≫ G₂.map (μ.inv.app K))
    {K : C} (φ : G₀.obj K ⟶ K) :
    IsWeilEquivariant G₂ (transportWeilDatum U c φ)
      (transportWeilDatum S b (transportWeilDatum T a φ)) (μ.hom.app K) := by
  apply (cancel_epi (c.hom.app K)).mp
  dsimp only [IsWeilEquivariant, transportWeilDatum]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [h K]
  simp only [Functor.comp_obj, Category.assoc, ← G₂.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc,
    ← S.map_comp_assoc, Iso.hom_inv_id_app]
  exact (μ.hom.naturality φ).symm

/-- Reducing a morphism through a coherent coefficient compositor preserves its Weil
equation, regardless of whether the coefficient change is flat. -/
lemma purity_isWeilEquivariant_reduction
    {C D E : Type*} [Category C] [Category D] [Category E]
    {G₀ : C ⥤ C} {G₁ : D ⥤ D} {G₂ : E ⥤ E}
    (T : C ⥤ D) (S : D ⥤ E) (U : C ⥤ E)
    (a : G₀ ⋙ T ≅ T ⋙ G₁) (b : G₁ ⋙ S ≅ S ⋙ G₂)
    (c : G₀ ⋙ U ≅ U ⋙ G₂) (μ : U ≅ T ⋙ S)
    (h : ∀ K, c.hom.app K = μ.hom.app (G₀.obj K) ≫ S.map (a.hom.app K) ≫
      b.hom.app (T.obj K) ≫ G₂.map (μ.inv.app K))
    {K L : C} (φK : G₀.obj K ⟶ K) (φL : G₀.obj L ⟶ L)
    (s : T.obj K ⟶ T.obj L)
    (hs : IsWeilEquivariant G₁ (transportWeilDatum T a φK)
      (transportWeilDatum T a φL) s) :
    IsWeilEquivariant G₂ (transportWeilDatum U c φK) (transportWeilDatum U c φL)
      (μ.hom.app K ≫ S.map s ≫ μ.inv.app L) :=
  (purity_isWeilEquivariant_compositor T S U a b c μ h φK).comp
    ((hs.map S b).comp (purity_weil_inverse G₂ _ _ (μ.app L)
      (purity_isWeilEquivariant_compositor T S U a b c μ h φL)))

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
  (c : Λ ⟶ Λ'') [IsMonHom c] {X : Scheme.{u}} (g : X ⟶ X)

/-- The canonical reduction of a morphism preserves its transported geometric Weil
equation for any pair of composable condensed coefficient changes. -/
theorem isWeilEquivariant_coefficientReduction (hc : a ≫ b = c)
    {K M : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (φK : L((g)^*⟦Λ⟧).obj K ⟶ K) (φM : L((g)^*⟦Λ⟧).obj M ⟶ M)
    (s : L(Mod.extendScalars (coefficientMap a X)).obj K ⟶
      L(Mod.extendScalars (coefficientMap a X)).obj M)
    (hs : IsWeilEquivariant L((g)^*⟦Λ'⟧)
      (transportWeilDatum _ (derivedUpperStarExtendScalarsIso a g) φK)
      (transportWeilDatum _ (derivedUpperStarExtendScalarsIso a g) φM) s) :
    IsWeilEquivariant L((g)^*⟦Λ''⟧)
      (transportWeilDatum _ (derivedUpperStarExtendScalarsIso c g) φK)
      (transportWeilDatum _ (derivedUpperStarExtendScalarsIso c g) φM)
      (Mod.derivedExtendScalarsReduction (coefficientMap a X) (coefficientMap b X)
        (coefficientMap c X) (coefficientMap_comp_eq a b c hc X) s) := by
  have hcomp := derivedUpperStarExtendScalarsIso_hom_app_of_coefficient_comp a b c g hc
  exact purity_isWeilEquivariant_reduction _ _ _
    (derivedUpperStarExtendScalarsIso a g) (derivedUpperStarExtendScalarsIso b g)
    (derivedUpperStarExtendScalarsIso c g)
    (Mod.derivedExtendScalarsCompIso _ _ _ (coefficientMap_comp_eq a b c hc X))
    hcomp φK φM s hs

end AlgebraicGeometry.ProEtale.CondensedRing


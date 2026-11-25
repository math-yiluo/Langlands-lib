/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapModTrace

/-!
# Morphisms between the composites of two monoidal adjunctions on module objects

Let `adj₁ : F₁ ⊣ G₁` and `adj₂ : F₂ ⊣ G₂` be monoidal adjunctions out of the same monoidal
category `C`, and `θ : F₁ ⋙ G₁ ⟶ F₂ ⋙ G₂` a monoidal natural transformation compatible with the
units (`adj₁.unit ≫ θ = adj₂.unit`). In the application `F_i ⊣ G_i` is `g_i^* ⊣ g_{i*}` for two
weakly étale morphisms `g₂ = s ≫ g₁` and `θ` is the restriction along `s`.

Then `θ` is linear over every algebra object `R`: it lifts to a natural transformation
`adj₁.mapModComp R ⟶ adj₂.mapModComp R` of functors on `R`-module objects
(`CategoryTheory.Adjunction.mapModCompHom`), compatible with the units of the lifted adjunctions.
This generalizes `CategoryTheory.Adjunction.mapModAction`, the case `adj₁ = adj₂`.
-/

@[expose] public section

open CategoryTheory Category MonoidalCategory MonObj

namespace CategoryTheory.Adjunction

open scoped Obj

variable {C : Type*} [Category C] [MonoidalCategory C]
  {D₁ : Type*} [Category D₁] [MonoidalCategory D₁] {D₂ : Type*} [Category D₂]
  [MonoidalCategory D₂]
  {F₁ : C ⥤ D₁} {G₁ : D₁ ⥤ C} {adj₁ : F₁ ⊣ G₁} [F₁.Monoidal] [G₁.LaxMonoidal] [adj₁.IsMonoidal]
  {F₂ : C ⥤ D₂} {G₂ : D₂ ⥤ C} {adj₂ : F₂ ⊣ G₂} [F₂.Monoidal] [G₂.LaxMonoidal] [adj₂.IsMonoidal]
  (R : C) [MonObj R] {θ : F₁ ⋙ G₁ ⟶ F₂ ⋙ G₂} [NatTrans.IsMonoidal θ]
  (hθ : adj₁.unit ≫ θ = adj₂.unit)

include hθ in
lemma act_comp_app_eq_of_unit_comp (M : Mod C R) :
    γ[R, ((adj₁.mapModComp R).obj M).X] ≫ θ.app M.X =
      R ◁ θ.app M.X ≫ γ[R, ((adj₂.mapModComp R).obj M).X] := by
  have h := congr_app hθ R
  simp only [NatTrans.comp_app] at h
  rw [act_mapModComp_obj, act_mapModComp_obj, assoc, assoc, θ.naturality,
    NatTrans.IsMonoidal.tensor_assoc]
  simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, h, id_comp]
  erw [comp_id]

/-- A monoidal natural transformation `θ : F₁ ⋙ G₁ ⟶ F₂ ⋙ G₂` compatible with the units, lifted
to `R`-module objects. -/
@[simps]
def mapModCompHom : adj₁.mapModComp R ⟶ adj₂.mapModComp R where
  app M := Mod.homMk (θ.app M.X) (act_comp_app_eq_of_unit_comp R hθ M)
  naturality _ _ φ := Mod.hom_ext _ _ (θ.naturality φ.hom)

/-- The lift of `θ` is compatible with the units of the lifted adjunctions. -/
@[reassoc]
lemma mapModAdjunction_unit_comp_mapModCompHom :
    (adj₁.mapModAdjunction R).unit ≫ mapModCompHom R hθ = (adj₂.mapModAdjunction R).unit := by
  refine NatTrans.ext (funext fun M ↦ Mod.hom_ext _ _ ?_)
  have h := congr_app hθ M.X
  simp only [NatTrans.comp_app] at h
  simp only [Functor.id_obj, NatTrans.comp_app, Functor.comp_obj, Mod.comp_hom',
    mapModAdjunction_unit_app_hom]
  exact h

end CategoryTheory.Adjunction

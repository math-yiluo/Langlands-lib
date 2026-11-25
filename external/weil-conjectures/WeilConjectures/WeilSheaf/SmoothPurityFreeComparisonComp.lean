/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTraceCriterion

/-!
# Composition of free comparisons

The free comparison for an extension by zero followed by a proper pushforward is
the composite of the two free comparisons. Its unit equation follows by naturality.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

variable {C C' D D' E E' : Type*}
  [Category C] [Category C'] [Category D] [Category D'] [Category E] [Category E']
  {I : C ⥤ C'} {U : C' ⥤ C} (adj₁ : I ⊣ U)
  {J : D ⥤ D'} {V : D' ⥤ D} (adj₂ : J ⊣ V)
  {K : E ⥤ E'} {W : E' ⥤ E} (adj₃ : K ⊣ W)
  (R₁ : C' ⥤ D') (r₁ : C ⥤ D) (e₁ : R₁ ⋙ V ≅ U ⋙ r₁)
  (R₂ : D' ⥤ E') (r₂ : D ⥤ E) (e₂ : R₂ ⋙ W ≅ V ⋙ r₂)

/-- Paste two comparison squares with forgetful functors. -/
noncomputable def traceCompForgetIso : (R₁ ⋙ R₂) ⋙ W ≅ U ⋙ (r₁ ⋙ r₂) :=
  NatIso.ofComponents (fun A ↦ e₂.app (R₁.obj A) ≪≫ r₂.mapIso (e₁.app A)) (fun f ↦ by
    simp only [Functor.comp_map, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
    have hn₂ := e₂.hom.naturality (R₁.map f)
    have hn₁ := e₁.hom.naturality f
    simp only [Functor.comp_map] at hn₂ hn₁
    rw [reassoc_of% hn₂, ← r₂.map_comp, hn₁, r₂.map_comp])

/-- The pasted free comparison respects the free units whenever its two factors do. -/
theorem unit_app_comp_map_compFreeComparison (X : C)
    (β₁ : J.obj (r₁.obj X) ≅ R₁.obj (I.obj X))
    (β₂ : K.obj (r₂.obj (r₁.obj X)) ≅ R₂.obj (J.obj (r₁.obj X)))
    (h₁ : adj₂.unit.app (r₁.obj X) ≫ V.map β₁.hom =
      r₁.map (adj₁.unit.app X) ≫ e₁.inv.app (I.obj X))
    (h₂ : adj₃.unit.app (r₂.obj (r₁.obj X)) ≫ W.map β₂.hom =
      r₂.map (adj₂.unit.app (r₁.obj X)) ≫ e₂.inv.app (J.obj (r₁.obj X))) :
    adj₃.unit.app ((r₁ ⋙ r₂).obj X) ≫ W.map (β₂ ≪≫ R₂.mapIso β₁).hom =
      (r₁ ⋙ r₂).map (adj₁.unit.app X) ≫
        (traceCompForgetIso R₁ r₁ e₁ R₂ r₂ e₂).inv.app (I.obj X) := by
  simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp]
  rw [reassoc_of% h₂]
  have hn := e₂.inv.naturality β₁.hom
  simp only [Functor.comp_map] at hn
  rw [← hn]
  rw [← r₂.map_comp_assoc, h₁, r₂.map_comp, Category.assoc]
  rfl

end CategoryTheory.Adjunction

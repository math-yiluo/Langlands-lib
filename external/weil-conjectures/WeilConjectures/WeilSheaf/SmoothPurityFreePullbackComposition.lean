/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Composition of free-module pullback comparisons -/

@[expose] public section

namespace CategoryTheory

variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
  [Category A₀] [Category A₁] [Category A₂]
  [Category B₀] [Category B₁] [Category B₂]
  {P₀₁ : A₀ ⥤ A₁} {RP₀₁ : A₁ ⥤ A₀} (p₀₁ : P₀₁ ⊣ RP₀₁)
  {P₁₂ : A₁ ⥤ A₂} {RP₁₂ : A₂ ⥤ A₁} (p₁₂ : P₁₂ ⊣ RP₁₂)
  {P₀₂ : A₀ ⥤ A₂} {RP₀₂ : A₂ ⥤ A₀} (p₀₂ : P₀₂ ⊣ RP₀₂)
  {Q₀₁ : B₀ ⥤ B₁} {RQ₀₁ : B₁ ⥤ B₀} (q₀₁ : Q₀₁ ⊣ RQ₀₁)
  {Q₁₂ : B₁ ⥤ B₂} {RQ₁₂ : B₂ ⥤ B₁} (q₁₂ : Q₁₂ ⊣ RQ₁₂)
  {Q₀₂ : B₀ ⥤ B₂} {RQ₀₂ : B₂ ⥤ B₀} (q₀₂ : Q₀₂ ⊣ RQ₀₂)
  {F₀ : A₀ ⥤ B₀} {RF₀ : B₀ ⥤ A₀} (f₀ : F₀ ⊣ RF₀)
  {F₁ : A₁ ⥤ B₁} {RF₁ : B₁ ⥤ A₁} (f₁ : F₁ ⊣ RF₁)
  {F₂ : A₂ ⥤ B₂} {RF₂ : B₂ ⥤ A₂} (f₂ : F₂ ⊣ RF₂)

/-- Pullback composition is compatible with the free comparison whenever the
corresponding pushforward composition is compatible with forgetting coefficients. -/
lemma purity_free_pullback_composition
    (a : P₀₂ ≅ P₀₁ ⋙ P₁₂) (b : Q₀₂ ≅ Q₀₁ ⋙ Q₁₂)
    (t₀₁ : F₀ ⋙ Q₀₁ ≅ P₀₁ ⋙ F₁) (t₁₂ : F₁ ⋙ Q₁₂ ≅ P₁₂ ⋙ F₂)
    (t₀₂ : F₀ ⋙ Q₀₂ ≅ P₀₂ ⋙ F₂)
    (h : ∀ N : B₂,
      (conjugateIsoEquiv (p₀₁.comp p₁₂) p₀₂ a).hom.app (RF₂.obj N) ≫
          (conjugateIsoEquiv (p₀₂.comp f₂) (f₀.comp q₀₂) t₀₂).hom.app N =
        RP₀₁.map ((conjugateIsoEquiv (p₁₂.comp f₂) (f₁.comp q₁₂) t₁₂).hom.app N) ≫
          (conjugateIsoEquiv (p₀₁.comp f₁) (f₀.comp q₀₁) t₀₁).hom.app (RQ₁₂.obj N) ≫
          RF₀.map ((conjugateIsoEquiv (q₀₁.comp q₁₂) q₀₂ b).hom.app N))
    (M : A₀) :
    b.hom.app (F₀.obj M) ≫ Q₁₂.map (t₀₁.hom.app M) ≫ t₁₂.hom.app (P₀₁.obj M) =
      t₀₂.hom.app M ≫ F₂.map (a.hom.app M) := by
  let α : F₀ ⋙ Q₀₂ ≅ P₀₁ ⋙ (P₁₂ ⋙ F₂) :=
    Functor.isoWhiskerLeft F₀ b ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight t₀₁ Q₁₂ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft P₀₁ t₁₂
  let β : F₀ ⋙ Q₀₂ ≅ P₀₁ ⋙ (P₁₂ ⋙ F₂) :=
    t₀₂ ≪≫ Functor.isoWhiskerRight a F₂ ≪≫ Functor.associator _ _ _
  have hh : α = β := by
    apply (conjugateIsoEquiv (p₀₁.comp (p₁₂.comp f₂)) (f₀.comp q₀₂)).injective
    dsimp only [α, β]
    rw [conjugateIsoEquiv_trans _ (f₀.comp (q₀₁.comp q₁₂)),
      conjugateIsoEquiv_trans _ ((f₀.comp q₀₁).comp q₁₂),
      conjugateIsoEquiv_trans _ ((p₀₁.comp f₁).comp q₁₂),
      conjugateIsoEquiv_trans _ (p₀₁.comp (f₁.comp q₁₂)),
      conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_isoWhiskerRight,
      conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_associator,
      conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_associator]
    rw [conjugateIsoEquiv_trans _ (p₀₂.comp f₂),
      conjugateIsoEquiv_trans _ ((p₀₁.comp p₁₂).comp f₂),
      conjugateIsoEquiv_associator, conjugateIsoEquiv_isoWhiskerRight]
    ext N
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
      Category.id_comp, Category.comp_id, Category.assoc] using (h N).symm
  have hhM := congrArg (fun e ↦ e.hom.app M) hh
  simpa only [α, β, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    Category.id_comp, Category.comp_id, Category.assoc] using hhM

end CategoryTheory

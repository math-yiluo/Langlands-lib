/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendChangeTransfer

/-! # Normalization of the ordinary coefficient-composition comparison -/

@[expose] public section

universe u v

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory

/-- The unique left-adjoint comparison is conjugate to the specified comparison
of right adjoints used to transport the second adjunction. -/
lemma purity_conjugate_leftAdjointUniq_ofNatIsoRight
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (e : R₂ ≅ R₁) :
    conjugateIsoEquiv adj₂ adj₁ (adj₁.leftAdjointUniq (adj₂.ofNatIsoRight e)) = e := by
  apply Iso.ext
  apply conjugateEquiv_eq_of_unit
  intro M
  have h := Adjunction.unit_leftAdjointUniq_hom_app adj₁ (adj₂.ofNatIsoRight e) M
  simpa only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app] using h.symm

namespace Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R S T : C} [MonObj R] [MonObj S] [MonObj T] [IsCommMonObj R] [IsCommMonObj S]
  {a : R ⟶ S} {b : S ⟶ T} {c : R ⟶ T} [IsMonHom a] [IsMonHom b] [IsMonHom c]

/-- The ordinary scalar-composition iso is the conjugate of the restriction-composition
iso, with exactly the normalization used by finite Tate reduction. -/
lemma purity_conjugate_extendScalarsCompIsoOfEq (h : a ≫ b = c) :
    conjugateIsoEquiv (extendRestrictAdjunction c)
        ((extendRestrictAdjunction a).comp (extendRestrictAdjunction b))
        (extendScalarsCompIsoOfEq h) =
      (comapCongr h).symm ≪≫ comapComp a b := by
  rw [extendScalarsCompIsoOfEq,
    conjugateIsoEquiv_trans _ (extendRestrictAdjunction (a ≫ b)),
    extendScalarsIsoOfEq, purity_conjugate_leftAdjointUniq_ofNatIsoRight,
    conjugateIsoEquiv_iso_symm, extendScalarsComp,
    purity_conjugate_leftAdjointUniq_ofNatIsoRight]
  rfl

end Mod

end CategoryTheory

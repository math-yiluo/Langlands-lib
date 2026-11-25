/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedAdjunction
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointFree
public import WeilConjectures.CategoryTheory.Adjunction.FreeComparisonComp
public import WeilConjectures.CategoryTheory.DerivedCategory.FreeComparisonMapDerivedCategory
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraFreeComparison

/-! # Free Weil objects and an exact functor followed by a derived direct image -/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

universe v

variable {C D E : Type*} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  [Abelian C] [IsGrothendieckAbelian.{v} C]
  [Abelian D] [IsGrothendieckAbelian.{v} D]
  [Abelian E] [IsGrothendieckAbelian.{v} E]
  {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  {H : E ⥤ E} [H.Additive] [H.IsEquivalence]
  {L₁ : C ⥤ D} [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [PreservesColimitsOfShape (Discrete ℤ) L₁]
  {L₂ : D ⥤ E} [L₂.Additive]
  (e₁ : L₁ ⋙ G ≅ F ⋙ L₁) (e₂ : L₂ ⋙ H ≅ G ⋙ L₂)
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{v} D] [HasDerivedCategory.{v} E]
  [HasDerivedCategory.{v} (IsoAlgebra F)] [HasDerivedCategory.{v} (IsoAlgebra G)]
  [HasDerivedCategory.{v} (IsoAlgebra H)]
  [Abelian.HasKInjectiveResolutions D] [Abelian.HasKInjectiveResolutions (IsoAlgebra G)]

/-- The forget comparison for the exact-then-derived presentation of compact support. -/
noncomputable def exactRightDerivedForgetIso :
    ((mapOfNatIso e₁).mapDerivedCategory ⋙ (mapOfNatIso e₂).rightDerivedFunctor) ⋙
        (forget H).mapDerivedCategory ≅
      (forget F).mapDerivedCategory ⋙ (L₁.mapDerivedCategory ⋙ L₂.rightDerivedFunctor) :=
  Adjunction.compForgetIso
    (Functor.mapDerivedCategoryCompForgetIso (mapOfNatIsoCompForgetIso e₁))
    (derivedForgetCommIso e₂)

/-- Exact extension by zero and a direct image preserving bounded-below coproducts
commute with free Weil objects on every bounded complex. -/
theorem isIso_freeComparison_exact_rightDerived
    (hcoprod : ∀ (X : ℤ → DerivedCategory D) (a : ℤ), (∀ n, (X n).IsGE a) →
      PreservesColimit (Discrete.functor X) L₂.rightDerivedFunctor)
    (K : DerivedCategory C) (hK : DerivedCategory.TStructure.t.bounded K) :
    IsIso (Adjunction.freeComparison (freeWeilDerivedAdjunction F)
      (freeWeilDerivedAdjunction H)
      ((mapOfNatIso e₁).mapDerivedCategory ⋙ (mapOfNatIso e₂).rightDerivedFunctor)
      (L₁.mapDerivedCategory ⋙ L₂.rightDerivedFunctor)
      (exactRightDerivedForgetIso e₁ e₂) K) := by
  refine Adjunction.isIso_freeComparison_comp
    (freeWeilDerivedAdjunction F) (freeWeilDerivedAdjunction G)
    (freeWeilDerivedAdjunction H) _ _ K ?_ ?_
  · exact Adjunction.isIso_freeComparison_mapDerivedCategory _ _ _
      (fun S ↦ isIso_freeComparison_mapOfNatIso e₁ S) K
  · obtain ⟨a, ha⟩ := (L₁.bounded_mapDerivedCategory_obj hK).1
    have := ha
    exact isIso_derivedFreeComparison e₂ hcoprod _ a

/-- A compact-support trace is universal on Weil complexes if it is universal on
the shifts of the geometric carrier of the source. -/
theorem bijective_map_comp_exact_rightDerived_of_bounded
    (hcoprod : ∀ (X : ℤ → DerivedCategory D) (a : ℤ), (∀ n, (X n).IsGE a) →
      PreservesColimit (Discrete.functor X) L₂.rightDerivedFunctor)
    {P : DerivedCategory (IsoAlgebra F)} {T : DerivedCategory (IsoAlgebra H)}
    (ε : ((mapOfNatIso e₁).mapDerivedCategory ⋙
      (mapOfNatIso e₂).rightDerivedFunctor).obj P ⟶ T)
    (K : DerivedCategory (IsoAlgebra F))
    (hK : DerivedCategory.TStructure.t.bounded ((forget F).mapDerivedCategory.obj K))
    (h : ∀ n : ℤ, Function.Bijective fun φ : (shiftFunctor _ n).obj
        ((forget F).mapDerivedCategory.obj K) ⟶ (forget F).mapDerivedCategory.obj P ↦
      (L₁.mapDerivedCategory ⋙ L₂.rightDerivedFunctor).map φ ≫
        (exactRightDerivedForgetIso e₁ e₂).inv.app P ≫
        (forget H).mapDerivedCategory.map ε) :
    Function.Bijective fun φ : K ⟶ P ↦
      ((mapOfNatIso e₁).mapDerivedCategory ⋙ (mapOfNatIso e₂).rightDerivedFunctor).map φ ≫ ε := by
  refine bijective_map_comp_of_bijective_forget F H _ _
    (exactRightDerivedForgetIso e₁ e₂) ε K ?_ h
  intro n
  exact isIso_freeComparison_exact_rightDerived e₁ e₂ hcoprod _
    (ObjectProperty.le_shift (P := DerivedCategory.TStructure.t.bounded) n _ hK)

end CategoryTheory.Endofunctor.IsoAlgebra

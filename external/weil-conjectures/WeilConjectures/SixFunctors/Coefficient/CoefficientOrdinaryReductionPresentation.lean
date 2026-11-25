/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryQuotientModel
public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionComparison
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Strict quotient-system presentations of coefficient reduction

Source: Stacks 06YY, 07A6 and 0941.

For a reduction functor with its normalized adjunction to the total limit, the ordinary
quotient system of a flat-term K-flat complex is a strict tensor presentation: its
finite evaluations, horizontal maps and whole-system unit are the prescribed ones.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.OrdinaryQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

private theorem constantLimitUnit_eq
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    (constantLimitUnit l E W).app I =
      DerivedCategory.Q.map ((termwiseLimitComparison l E W).inv.app I) ≫
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
          scalarReductionSource l E W).rightDerivedFunctorUnitQ I := by
  simp [constantLimitUnit, Functor.rightDerivedFunctorUnitQ,
    Functor.mapHomotopyCategoryFactors]

/-- The ordinary quotient system of a flat-term K-flat complex is a strict tensor
presentation of any reduction functor which is normalized by the unit projection.
Source: Stacks 06YY, 07A6 and 0941. -/
theorem strictReductionTensorPresentation (M : OrdinaryModel l E W)
    (L : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W)
    (adj : L ⊣ coefficientSequenceLimit l E W)
    (ρ : ∀ n : ℕ, L ⋙ coefficientSequenceDerivedEvaluation l E W n ≅
      coefficientFiniteDerivedExtension l E W n)
    (hunitproj : ∀ (P : DerivedCategory (scalarReductionSource l E W)) (n : ℕ),
      adj.unit.app P ≫ (coefficientSequenceProjection l E W n).app (L.obj P) =
        (coefficientFiniteAdjunction l E W n).unit.app P ≫
          (coefficientFiniteDerivedRestriction l E W n).map ((ρ n).inv.app P))
    (ε : DerivedCategory.Q ⋙ L ⟶ M.quotient l E W ⋙ DerivedCategory.Q)
    (hhom : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
      (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (f : (M.quotient l E W).obj Q ⟶ I),
      adj.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
          (ε.app Q ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
            ((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
          (systemLimitUnit l E W M (constantLimitUnit l E W)).app I)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (fP : ∀ p : ℤ, (P.X p).IsFlatOnSite)
    [IsIso (ε.app P)] :
    CoefficientStrictReductionTensorPresentation l E W L adj ρ P hP
      ((M.quotient l E W).obj P) (asIso (ε.app P))
      (fun n ↦ (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P) where
  finite n := finiteComparison_of_unit l E W M L adj ρ hunitproj ε hhom P hP fP n
  horizontal m n h := by
    apply HomologicalComplex.hom_ext
    intro i
    exact M.transition (P.X i) h
  adjunction := by
    unfold CoefficientStrictReductionUnitPresentation
    let C := (M.quotient l E W).obj P
    let I := (tower l E W).obj C
    refine ⟨(M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P ≫
      M.limitComparison.hom.app C ≫ (termwiseLimitComparison l E W).inv.app I ≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (coefficientSequenceRestriction l E W ⋙
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)))
          (.up ℤ)).hom.app C, ?_, ?_⟩
    · have hu := reductionComparison_unit l E W M (constantLimitUnit l E W) L adj ε hhom P
      refine Eq.trans hu ?_
      dsimp only [systemLimitUnit, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app]
      rw [constantLimitUnit_eq]
      simp only [Functor.map_comp, Category.assoc]
      have hcancel : DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (coefficientSequenceRestriction l E W ⋙
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)))
          (.up ℤ)).hom.app C) ≫ DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (coefficientSequenceRestriction l E W ⋙
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)))
          (.up ℤ)).inv.app C) = 𝟙 _ := by
        rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
      rw [reassoc_of% hcancel]
      dsimp only [Functor.rightDerivedFunctorUnitQ, coefficientConstantTowerLimit]
      erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
      rfl
    · intro n
      have hu := ordinary_unit l E W M P n
      have hcπ : (termwiseLimitComparison l E W).inv.app I ≫
          (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I =
            limit.π I.asFunctor (op n) := by
        apply (cancel_epi ((termwiseLimitComparison l E W).hom.app I)).mp
        rw [Iso.hom_inv_id_app_assoc]
        apply HomologicalComplex.hom_ext
        intro p
        exact (termwiseLimitComparison_projection l E W I n p).symm
      have hπ2 : (Functor.mapHomologicalComplexCompIso
          (Iso.refl (coefficientSequenceRestriction l E W ⋙
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)))
          (.up ℤ)).hom.app C ≫ (NatTrans.mapHomologicalComplex
            (Functor.whiskerLeft (coefficientSequenceRestriction l E W) (lim.π (op n)))
            (.up ℤ)).app C =
          (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I := by
        ext p : 1
        simp only [Functor.comp_obj, Functor.mapHomologicalComplexCompIso,
          HomologicalComplex.comp_f,
          NatIso.mapHomologicalComplex_hom_app_f, Iso.refl_hom, NatTrans.id_app, lim_obj,
          NatTrans.mapHomologicalComplex_app_f, Functor.whiskerLeft_app, lim.π_app, C, I]
        exact Category.id_comp _
      simp only [Category.assoc] at hu ⊢
      rw [reassoc_of% hπ2, reassoc_of% hcπ]
      exact hu

end WeilConjectures.OrdinaryQuotient

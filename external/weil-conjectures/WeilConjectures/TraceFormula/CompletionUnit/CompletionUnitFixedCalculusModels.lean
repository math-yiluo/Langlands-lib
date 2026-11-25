/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitDerivedAdjunctionComparison
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitCanonicalModels
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFiniteMateComparison

/-! # Completion models for a specified coefficient calculus

Source: Stacks 07A6, 09T5, 0D6E and 0941. The construction only uses coefficient
adjunctions, so no invertibility condition on the characteristic of the scheme is needed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  SheafOfModules.monoidalCategory CategoryTheory.Limits.limit

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.CompletionUnit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

private theorem fixedDerivedComparison
    (S : CoefficientDerivedSystemCalculus l E W) (M : OrdinaryModel l E W)
    (c : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ) ≅ roosLimitFunctor)
    (hc : ∀ (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      (n : ℕ) (p : ℤ),
      (c.hom.app Z ≫ limit.π Z.asFunctor (op n)).f p = limit.π (Z.X p) (op n))
    (η : roosLimitFunctor ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W)
    (hηnorm : ∀ (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      [J.IsKInjective], η.app J ≫
        ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
          scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom =
        DerivedCategory.Q.map (c.inv.app J)) :
    (∀ (I : CochainComplex (coefficientSequenceModules l E W) ℤ),
      I.IsKInjective → IsIso ((systemLimitUnit l E W M η).app I)) ∧
    ∃ (ε : DerivedCategory.Q ⋙ S.reduction ⟶ M.quotient l E W ⋙ DerivedCategory.Q),
      S.reduction.IsLeftDerivedFunctor ε
        (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ)) ∧
      (∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ),
        Q.IsKFlatIndependentCoefficients → (∀ p : ℤ, (Q.X p).IsFlatOnSite) →
          IsIso (ε.app Q)) ∧
      (∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
        (hQ : Q.IsKFlatIndependentCoefficients)
        (_hflat : ∀ p : ℤ, (Q.X p).IsFlatOnSite) (n : ℕ),
        (coefficientSequenceDerivedEvaluation l E W n).map (ε.app Q) ≫
            (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app
              ((M.quotient l E W).obj Q) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app Q) =
          (S.reductionEvaluation n).hom.app (DerivedCategory.Q.obj Q) ≫
            (coefficientFiniteReductionModel l E W Q hQ n).hom) ∧
      (∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
        (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
        (a : (M.quotient l E W).obj Q ⟶ I),
        S.adjunction.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
            (ε.app Q ≫ DerivedCategory.Q.map a) =
          DerivedCategory.Q.map
              ((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I a) ≫
            (systemLimitUnit l E W M η).app I) := by
  have hsys := systemLimitUnit_isIso l E W M c η hηnorm
  have hδ : (coefficientSequenceLimit l E W).IsRightDerivedFunctor
      (systemLimitUnit l E W M η)
      (HomologicalComplex.quasiIso (coefficientSequenceModules l E W) (.up ℤ)) := by
    apply (CategoryTheory.derives (ordinaryLimit l E W)).isRightDerivedFunctor_of_isIso
      (systemLimitUnit l E W M η)
    intro I
    exact hsys I.obj I.property
  obtain ⟨L, ε, a, hε, hcomp, hhom⟩ :=
    tensor_derived_exists l E W S M (systemLimitUnit l E W M η) hδ
  let e := S.adjunction.leftAdjointUniq a
  let ε' : DerivedCategory.Q ⋙ S.reduction ⟶ M.quotient l E W ⋙ DerivedCategory.Q :=
    Functor.whiskerLeft DerivedCategory.Q e.hom ≫ ε
  have hε' : S.reduction.IsLeftDerivedFunctor ε'
      (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ)) :=
    (Functor.isLeftDerivedFunctor_iff_of_iso
      (LF := S.reduction) (LF' := L) (α := ε') ε
      (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ)) e rfl).2 hε
  have hhom' : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
      (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (f : (M.quotient l E W).obj Q ⟶ I),
      S.adjunction.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
        (ε'.app Q ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
        ((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
          (systemLimitUnit l E W M η).app I := by
    intro Q I f
    rw [← hhom Q I f]
    change S.adjunction.homEquiv _ _
      ((e.hom.app (DerivedCategory.Q.obj Q) ≫ ε.app Q) ≫ DerivedCategory.Q.map f) = _
    rw [Category.assoc, S.adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
    rw [show S.adjunction.unit.app (DerivedCategory.Q.obj Q) ≫
      (coefficientSequenceLimit l E W).map (e.hom.app (DerivedCategory.Q.obj Q)) =
        a.unit.app (DerivedCategory.Q.obj Q) from
          S.adjunction.unit_leftAdjointUniq_hom_app a _]
    exact (a.homEquiv_unit _ _ _).symm
  refine ⟨hsys, ε', hε', ?_, ?_, hhom'⟩
  · intro Q hQ hf
    have := hcomp Q hQ hf
    dsimp only [ε', NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  · apply finiteComparison_of_unit l E W S M c hc η hηnorm ε'
    intro Q
    have h := hhom' Q ((M.quotient l E W).obj Q) (𝟙 _)
    have hid : ε'.app Q ≫ DerivedCategory.Q.map
        (𝟙 ((M.quotient l E W).obj Q)) = ε'.app Q := by
      rw [(DerivedCategory.Q (C := coefficientSequenceModules l E W)).map_id]
      exact Category.comp_id _
    have hh := (congrArg (S.adjunction.homEquiv (DerivedCategory.Q.obj Q)
      (DerivedCategory.Q.obj ((M.quotient l E W).obj Q))) hid).symm.trans h
    have hs (I : CochainComplex (coefficientSequenceModules l E W) ℤ) :
        (systemLimitUnit l E W M η).app I =
          DerivedCategory.Q.map (M.limitComparison.hom.app I) ≫
            η.app ((tower l E W).obj I) ≫
            (coefficientConstantTowerLimit l E W).map
              ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app I) := rfl
    rw [hs] at hh
    simp only [Adjunction.homEquiv_id] at hh
    convert hh using 1
    rfl

/-- Construct the ordinary quotient adjunction and its compatible derived model for
any specified calculus. Source: Stacks 07A6, 09T5, 0D6E and 0941.
(blueprint: lem-trf-completion-unit-fixed-calculus-models).

Proof: derive the ordinary quotient tensor/limit adjunction on flat-term K-flat
complexes and K-injective systems. Compare its left adjoint with S.reduction by
uniqueness of left adjoints to the fixed total limit. Transport its universal
comparison and Hom equation. Finite adjunction mates give reduction_evaluation.
The canonical right-derived limit unit and strict Roos comparison supply the
remaining fields. All constructions are over the coefficient sheaf, so they
also apply in residue characteristic l and to the empty scheme. -/
theorem fixedCalculusModels (S : CoefficientDerivedSystemCalculus l E W) :
    ∃ M : OrdinaryModel l E W, Nonempty (DerivedModel l E W S M) := by
  obtain ⟨M⟩ := ordinaryModel_exists l E W
  obtain ⟨r, hr⟩ := constantRoosComparison_exists l E W
  obtain ⟨hI, ε, hε, hflat, heval, hhom⟩ :=
    fixedDerivedComparison l E W S M
      (termwiseLimitComparison l E W) (termwiseLimitComparison_projection l E W)
      (constantLimitUnit l E W) (constantLimitUnit_normalization l E W)
  refine ⟨M, ⟨{
    towerLimitComparison := termwiseLimitComparison l E W
    towerLimitComparison_projection := termwiseLimitComparison_projection l E W
    limitUnit := constantLimitUnit l E W
    limitUnit_normalization := constantLimitUnit_normalization l E W
    roos := r
    roos_normalization := hr
    systemUnit := systemLimitUnit l E W M (constantLimitUnit l E W)
    system_isIso := hI
    systemUnit_composition := fun I ↦ rfl
    reductionComparison := ε
    reduction_isLeftDerived := hε
    reduction_isIso := hflat
    reduction_evaluation := heval
    hom_normalization := hhom }⟩⟩

end WeilConjectures.CompletionUnit

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenQuotientScalarComparisonLevelData

/-! # Assembly of the strict open scalar comparison

Source: Stacks Project, Tags 0E8I and 0941.
(blueprint: lem-sf-open-quotient-scalar-comparison-assembly).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Compatible finite-level comparisons assemble to one natural strict-tower
comparison. The assembly is by `NatIso.ofComponents`; successor transition
compatibility supplies the naturality equation and the component formula descends
unchanged to the tower.
Source: Stacks Tags 0E8I and 0941.
(blueprint: lem-sf-open-quotient-scalar-comparison-assembly). -/
theorem openQuotientScalarComparisonAssembly
    (o : IntegralOpenReduction.Operations l E j)
    (tc : IntegralOpenReduction.TensorComparison l E j o)
    (sc : ScalarCompatibility l E j o)
    (d : ScalarComparisonLevelData l E j o tc sc) :
    Nonempty (ScalarComparison l E j o sc tc) := by
  let α (Q : CochainComplex (scalarReductionSource l E U) ℤ) :
      (reductionTower l E X).obj ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) ⟶
        (extendTower l E j o).obj ((reductionTower l E U).obj Q) :=
    NatTrans.ofOpSequence (fun n ↦ (d.level n Q).hom) (by
      intro n
      change ((Functor.ofOpSequence (unrestrictedIntegralTransition l E X)).map
          (homOfLE (Nat.le_add_right n 1)).op).app
            ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) ≫
              (d.level n Q).hom =
        (d.level (n + 1) Q).hom ≫
          (OpenSemilinearTensor.extensionComplex l E j o).map
            (((Functor.ofOpSequence (unrestrictedIntegralTransition l E U)).map
              (homOfLE (Nat.le_add_right n 1)).op).app Q)
      rw [Functor.ofOpSequence_map_homOfLE_succ,
        Functor.ofOpSequence_map_homOfLE_succ]
      apply HomologicalComplex.hom_ext
      intro i
      exact d.transition n Q i)
  have hα (Q : CochainComplex (scalarReductionSource l E U) ℤ) : IsIso (α Q) := by
    have (n : ℕᵒᵖ) : IsIso ((α Q).app n) := by
      change IsIso (d.level n.unop Q).hom
      infer_instance
    exact NatIso.isIso_of_isIso_app (α Q)
  let e : OpenSemilinearTensor.extensionComplex l E j o ⋙ reductionTower l E X ≅
      reductionTower l E U ⋙ extendTower l E j o :=
    NatIso.ofComponents (fun Q ↦ @asIso _ _ _ _ (α Q) (hα Q)) (by
      intro P Q a
      apply NatTrans.ext
      funext n
      apply HomologicalComplex.hom_ext
      intro i
      change ((unrestrictedIntegralComplexFunctor l E X n.unop).map
          ((OpenSemilinearTensor.extensionComplex l E j o).map a)).f i ≫
            (d.level n.unop Q).hom.f i =
        (d.level n.unop P).hom.f i ≫
          ((OpenSemilinearTensor.extensionComplex l E j o).map
            ((unrestrictedIntegralComplexFunctor l E U n.unop).map a)).f i
      rw [d.components, d.components]
      change (scalarReductionRestriction l E X n.unop).map
          ((scalarReductionExtension l E X n.unop).map
            ((IntegralOpenReduction.extension l E j o).map (a.f i))) ≫
          ((scalarReductionRestriction l E X n.unop).map
            ((tc.ordinary n.unop).hom.app (Q.X i)) ≫
              (sc.finite n.unop).hom.app
                ((scalarReductionExtension l E U n.unop).obj (Q.X i))) =
        ((scalarReductionRestriction l E X n.unop).map
          ((tc.ordinary n.unop).hom.app (P.X i)) ≫
            (sc.finite n.unop).hom.app
              ((scalarReductionExtension l E U n.unop).obj (P.X i))) ≫
          (IntegralOpenReduction.extension l E j o).map
            ((scalarReductionRestriction l E U n.unop).map
              ((scalarReductionExtension l E U n.unop).map (a.f i)))
      calc
        _ = (scalarReductionRestriction l E X n.unop).map
            ((scalarReductionExtension l E X n.unop).map
                ((IntegralOpenReduction.extension l E j o).map (a.f i)) ≫
              (tc.ordinary n.unop).hom.app (Q.X i)) ≫
            (sc.finite n.unop).hom.app
              ((scalarReductionExtension l E U n.unop).obj (Q.X i)) := by
          rw [Functor.map_comp, Category.assoc]
        _ = (scalarReductionRestriction l E X n.unop).map
            ((tc.ordinary n.unop).hom.app (P.X i) ≫
              (IntegralOpenReduction.finiteExtension l E j o n.unop).map
                ((scalarReductionExtension l E U n.unop).map (a.f i))) ≫
            (sc.finite n.unop).hom.app
              ((scalarReductionExtension l E U n.unop).obj (Q.X i)) :=
          congrArg (fun f ↦ (scalarReductionRestriction l E X n.unop).map f ≫
            (sc.finite n.unop).hom.app
              ((scalarReductionExtension l E U n.unop).obj (Q.X i)))
            ((tc.ordinary n.unop).hom.naturality (a.f i))
        _ = (scalarReductionRestriction l E X n.unop).map
            ((tc.ordinary n.unop).hom.app (P.X i)) ≫
            ((scalarReductionRestriction l E X n.unop).map
                ((IntegralOpenReduction.finiteExtension l E j o n.unop).map
                  ((scalarReductionExtension l E U n.unop).map (a.f i))) ≫
              (sc.finite n.unop).hom.app
                ((scalarReductionExtension l E U n.unop).obj (Q.X i))) := by
          rw [Functor.map_comp, Category.assoc]
        _ = (scalarReductionRestriction l E X n.unop).map
            ((tc.ordinary n.unop).hom.app (P.X i)) ≫
            ((sc.finite n.unop).hom.app
                ((scalarReductionExtension l E U n.unop).obj (P.X i)) ≫
              (IntegralOpenReduction.extension l E j o).map
                ((scalarReductionRestriction l E U n.unop).map
                  ((scalarReductionExtension l E U n.unop).map (a.f i)))) :=
          congrArg (fun f ↦ (scalarReductionRestriction l E X n.unop).map
            ((tc.ordinary n.unop).hom.app (P.X i)) ≫ f)
            ((sc.finite n.unop).hom.naturality
              ((scalarReductionExtension l E U n.unop).map (a.f i)))
        _ = _ := (Category.assoc _ _ _).symm)
  exact ⟨⟨e, fun Q n i ↦ d.components n Q i⟩⟩

end WeilConjectures.OpenTensorQuotient

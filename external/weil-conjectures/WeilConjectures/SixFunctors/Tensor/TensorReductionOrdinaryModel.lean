/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import WeilConjectures.SixFunctors.Tensor.TensorReductionStrictDerivedSquare
import WeilConjectures.SixFunctors.Tensor.TensorReductionStrictFiniteEquation

/-! # The coherent reduction tensor map on ordinary quotient representatives

Source: Stacks 07A4, 07A6 and 0941; the simultaneous representative normalization
of the coefficient-system calculus.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  coefficientTotalTensor CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory pullbackTensorCalculus
attribute [local irreducible] pullbackTensorReductionModel pullbackTensorSystemModel
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem cancel_final_comparison
    {C : Type*} [Category C] {A B D H K Z : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ H) (e : Z ≅ H) (f : A ⟶ K) (g : K ⟶ Z)
    (h : a ≫ b ≫ c = f ≫ g ≫ e.hom) : a ≫ b ≫ c ≫ e.inv = f ≫ g := by
  apply (cancel_mono e.hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- The balanced reduction tensor comparison is computed by a strict chain map
on the fixed ordinary quotient representatives. Its finite components are the
ordinary scalar tensor comparison. This is an equation in the coherent system
derived category before applying any limit or adjunction transpose.

Source: Stacks 07A4 and 0941; simultaneous tensor normalization of
lem-coef-derived-system-evaluation-calculus.

Proof: identify ordinary reduction with extension to the sequence ring by its
adjunction to the ordinary limit. At each level the balanced rule
b tensor (x tensor y) maps to (b tensor x) tensor (1 tensor y); tensor
sheafification and the direct-sum totalization extend it to a cochain map.
The scalar balancing relations, Leibniz signs and quotient transitions are
preserved by this rule, so it defines the coherent map psi. Its nth evaluated
component, under reductionEvaluationComplex and
coefficientEvaluationTensorIso, is coefficientScalarTensorIso. These identities
commute with every quotient transition, since on local pure tensors both routes
reduce the two factors. Transport the simultaneous strict tensor normalization
to the fixed ordinary representatives using the adjunction-normalized reduction
models and naturality of the K-flat tensor comparisons. Goodness of P, Q and
T means these ordinary complexes compute all three derived reductions;
pullbackTensorReductionGood gives the K-flat system tensor representatives.
The normalized derived tensor comparison therefore computes the same balanced
rule, as a map of whole coherent systems. This gives the displayed
whole coherent-system square, before finite evaluation or taking a limit.
The second clause records the chain-level finite-component normalization; it is
stronger than a statement merely about finite derived evaluations.
(blueprint: lem-coef-tensor-reduction-ordinary-model). -/
theorem tensorReduction_ordinaryModel (W : Scheme.{u})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
    (hT : integralOperationsGoodComplex l E W
      ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj (P.obj, Q.obj))) :
    let S := pullbackTensorCalculus l E W
    let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P.obj, Q.obj)
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let B := (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P.obj, G.obj Q.obj)
    ∃ ψ : G.obj T ⟶ B,
      S.reduction.map ((S.integralTensorModel.iso (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) S.integralClosed
          P.obj Q.obj P.property.1 Q.property.1).hom) ≫
        S.reductionTensor.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        S.systemClosed.tensor.map
          (Prod.mkHom ((pullbackTensorReductionModel l E W).hom.app P)
            ((pullbackTensorReductionModel l E W).hom.app Q)) ≫
        (pullbackTensorSystemModel l E W _ _
          (pullbackTensorReductionGood l E W P)
          (pullbackTensorReductionGood l E W Q)).inv =
      (pullbackTensorReductionModel l E W).hom.app ⟨T, hT⟩ ≫
        DerivedCategory.Q.map ψ ∧
      ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map ψ ≫
          (coefficientEvaluationTensorIso l E W n (G.obj P.obj) (G.obj Q.obj)).hom ≫
          (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W n)).map
            (Prod.mkHom ((pullbackTensorReductionEvaluationComplex l E W n).inv.app P.obj)
              ((pullbackTensorReductionEvaluationComplex l E W n).inv.app Q.obj)) =
        (pullbackTensorReductionEvaluationComplex l E W n).inv.app T ≫
          (coefficientScalarTensorIso l E W n P.obj Q.obj).hom := by
  dsimp only
  refine ⟨tensorReductionStrictMap l E W P.obj Q.obj, ?_,
    tensorReductionStrictMap_finite l E W P.obj Q.obj⟩
  exact cancel_final_comparison _ _ _ _ _ _
    (tensorReductionStrictMap_derived_square l E W P Q hT)

end WeilConjectures

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenTensorQuotientData
public import WeilConjectures.SmoothPurity.CompletedOpenTensor.CompletedOpenTensorRepresentatives
import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenTensorQuotientScalarCompatibility
import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenTensorQuotientCoefficientComparisons
import WeilConjectures.SixFunctors.OpenFactorCoherence.TensorCompletionModelExistence
import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenTensorQuotientRoosNormalization

/-! # Strict quotient tensor comparison on compatible open models

Source: Stacks Tags 0E8I, 0GL1 and 0941; Bhatt--Scholze Definition 3.4.10.
(blueprint: lem-sf-open-quotient-normalized-cochains).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] SheafOfModules.monoidalCategory

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  scalarReductionExistence scalarReductionExtension
  scalarUnitTower

private def augmentationOfBalanced (W : Scheme.{u})
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) (b : Balanced l E W P Q) :
    Augmentation l E W P Q where
  map := scalarUnitTower l E W ((OpenSemilinearTensor.total l E W).obj (P, Q)) ≫
    b.iso.hom
  sections := by
    intro n p q V x y
    change (((b.iso.hom.app (op n)).f (p + q)).val.app V)
      ((((scalarUnitTower l E W
        ((OpenSemilinearTensor.total l E W).obj (P, Q))).app (op n)).f (p + q)).val.app V
          (totalSection l E W P Q p q V x y)) = _
    rw [scalarUnitTower_sections]
    exact b.coefficients n p q V x y 1

private theorem coefficient_reduction
    (o : IntegralOpenReduction.Operations l E j)
    (tc : OpenSemilinearTensor.TotalComparison l E j o)
    (sc : ScalarCompatibility l E j o)
    (st : IntegralOpenReduction.TensorComparison l E j o)
    (r : ScalarComparison l E j o sc st)
    (Q : CochainComplex (scalarReductionSource l E U) ℤ)
    (F : CochainComplex (scalarReductionSource l E X) ℤ)
    (bX : Balanced l E X ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) F)
    (bU : Balanced l E U Q ((OpenSemilinearTensor.restrictionComplex l E j o).obj F))
    (d : CoefficientComparisons l E j o tc sc st r Q F bX bU) :
    bX.iso.hom ≫ d.gamma.hom =
      (reductionTower l E X).map (tc.chain Q F).hom ≫
        r.iso.hom.app ((OpenSemilinearTensor.total l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)) ≫
        (extendTower l E j o).map bU.iso.hom := by
  apply NatTrans.ext
  funext n
  apply HomologicalComplex.hom_ext
  intro i
  exact eq_of_heq (d.reduction n i)

private def augmentedLowerRoute
    (o : IntegralOpenReduction.Operations l E j)
    (tc : OpenSemilinearTensor.TotalComparison l E j o)
    (Q : CochainComplex (scalarReductionSource l E U) ℤ)
    (F : CochainComplex (scalarReductionSource l E X) ℤ)
    (a : Augmentation l E U Q ((OpenSemilinearTensor.restrictionComplex l E j o).obj F)) :
    (Functor.const ℕᵒᵖ).obj ((OpenSemilinearTensor.total l E X).obj
      ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F)) ⟶
    (extendTower l E j o).obj ((integralOperationsTensorTowerFunctor l E U).obj
      (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)) :=
  (Functor.const ℕᵒᵖ).map (tc.chain Q F).hom ≫
    (Functor.constComp ℕᵒᵖ _ (OpenSemilinearTensor.extensionComplex l E j o)).inv ≫
      Functor.whiskerRight a.map (OpenSemilinearTensor.extensionComplex l E j o)

private theorem augmentation_square
    (o : IntegralOpenReduction.Operations l E j)
    (tc : OpenSemilinearTensor.TotalComparison l E j o)
    (sc : ScalarCompatibility l E j o)
    (st : IntegralOpenReduction.TensorComparison l E j o)
    (r : ScalarComparison l E j o sc st)
    (hr : ∀ P : CochainComplex (scalarReductionSource l E U) ℤ,
      scalarUnitTower l E X ((OpenSemilinearTensor.extensionComplex l E j o).obj P) ≫
          r.iso.hom.app P =
        (Functor.constComp ℕᵒᵖ P (OpenSemilinearTensor.extensionComplex l E j o)).inv ≫
          Functor.whiskerRight (scalarUnitTower l E U P)
            (OpenSemilinearTensor.extensionComplex l E j o))
    (Q : CochainComplex (scalarReductionSource l E U) ℤ)
    (F : CochainComplex (scalarReductionSource l E X) ℤ)
    (bX : Balanced l E X ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) F)
    (bU : Balanced l E U Q ((OpenSemilinearTensor.restrictionComplex l E j o).obj F))
    (d : CoefficientComparisons l E j o tc sc st r Q F bX bU) :
    (augmentationOfBalanced l E X _ _ bX).map ≫ d.gamma.hom =
      augmentedLowerRoute l E j o tc Q F
        (augmentationOfBalanced l E U _ _ bU) := by
  let H := (OpenSemilinearTensor.total l E U).obj
    (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)
  change (scalarUnitTower l E X _ ≫ bX.iso.hom) ≫ d.gamma.hom =
    (Functor.const ℕᵒᵖ).map (tc.chain Q F).hom ≫
      (Functor.constComp ℕᵒᵖ H (OpenSemilinearTensor.extensionComplex l E j o)).inv ≫
        Functor.whiskerRight (scalarUnitTower l E U H ≫ bU.iso.hom)
          (OpenSemilinearTensor.extensionComplex l E j o)
  rw [Category.assoc, coefficient_reduction l E j o tc sc st r Q F bX bU d,
    Functor.whiskerRight_comp]
  have hn := scalarUnitTower_natural l E X (tc.chain Q F).hom
  have hu := hr H
  calc
    _ = (scalarUnitTower l E X _ ≫ (reductionTower l E X).map (tc.chain Q F).hom) ≫
        r.iso.hom.app H ≫ (extendTower l E j o).map bU.iso.hom := by
      simp only [H, Category.assoc]
    _ = ((Functor.const ℕᵒᵖ).map (tc.chain Q F).hom ≫ scalarUnitTower l E X _) ≫
        r.iso.hom.app H ≫ (extendTower l E j o).map bU.iso.hom := by rw [← hn]
    _ = _ := by
      simpa only [H, extendTower, Functor.whiskeringRight_obj_map, Category.assoc] using
        congrArg (fun f ↦ (Functor.const ℕᵒᵖ).map (tc.chain Q F).hom ≫ f ≫
          (extendTower l E j o).map bU.iso.hom) hu

/-- Strict coefficient restriction, balancing, and scalar-unit augmentation on the
already compatible open models. No geometric preservation or choice of derived
open operations is asserted here.

Source: Stacks Tags 0E8I, 0GL1 and 0941; Bhatt--Scholze Definition 3.4.10.
(blueprint: lem-sf-open-quotient-normalized-cochains).

Proof: take normalized tensor-completion presentations on X and U from their
existing model-existence theorem. Global invertibility supplies the residue-field
invertibility needed there. The scalar-unit compatibility lemma supplies sc and r
with their finite component and system evaluation equations.

The normalized integral tensor-tower comparison gives balancing isomorphisms on
both pairs, with formula (x tensor y) tensor a sent to (x tensor a) tensor (y tensor 1).
Conjugate the fixed integral chain comparison through these balancing maps and r
to obtain gamma. Completed-to-finite scalar restriction is fully faithful because
the coefficient projection is locally surjective. Lift gamma, after removing the
finite scalar compatibility, to finiteGamma. The lifting equation gives its scalar
restriction formula; cancellation of balancing gives reduction. This construction
retains all quotient transitions and the signed unbounded total differential.

Define upper and lower by the scalar-adjunction units followed by balancing.
Their coefficient formulas give the required sections formulas. Define lowerRoute
by the constant tower of the integral chain map followed by extension of lower.
Naturality of the scalar unit, the reduction equation and scalar-unit compatibility
give square. Applying transpose and localization gives derivedSquare by
functoriality of composition. Finally the sections formulas for upper and lower
agree with the first Roos coordinates specified by Tensor.canonical. Tensor and
sheafification universal properties and total-sum extensionality give equality of
the degree maps, proving both RoosNormalization assertions. No limit is interchanged
with extension and no faithfulness of separate derived evaluations is used.
Zero complexes, the empty open and identity open are included. -/
theorem openQuotientNormalizedCochains [IsNoetherian X] [IsNoetherian U]
    (hlX : IsUnit (l : Γ(X, ⊤))) (hlU : IsUnit (l : Γ(U, ⊤)))
    (C : CompletedOpenTensor.Context l E j) :
    ∃ (tensorX : OpenFactorCoherence.Tensor l E X)
      (tensorU : OpenFactorCoherence.Tensor l E U)
      (sc : ScalarCompatibility l E j C.operations)
      (r : ScalarComparison l E j C.operations sc C.coefficients),
      ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ)
        (F : CochainComplex (scalarReductionSource l E X) ℤ),
        integralOperationsGoodComplex l E U Q → integralOperationsGoodComplex l E X F →
        sfIntegralConstructible l E U (DerivedCategory.Q.obj Q) →
        sfIntegralConstructible l E X (DerivedCategory.Q.obj F) →
        ∃ z : StrictSquare l E j C.operations C.strictOpen.totalComparison sc C.coefficients r
            Q F,
          RoosNormalization l E X tensorX
            ((OpenSemilinearTensor.extensionComplex l E j C.operations).obj Q) F z.upper ∧
          RoosNormalization l E U tensorU Q
            ((OpenSemilinearTensor.restrictionComplex l E j C.operations).obj F) z.lower := by
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (show IsUnit (l : X.residueField x) from by
      simpa only [map_natCast] using
        hlX.map ((X.presheaf.germ ⊤ x (by trivial)) ≫ X.residue x).hom).invertible
  let : ∀ x : U, Invertible (l : U.residueField x) := fun x ↦
    (show IsUnit (l : U.residueField x) from by
      simpa only [map_natCast] using
        hlU.map ((U.presheaf.germ ⊤ x (by trivial)) ≫ U.residue x).hom).invertible
  obtain ⟨tensorX⟩ := OpenFactorCoherence.tensorCompletionModel_nonempty l E X
  obtain ⟨tensorU⟩ := OpenFactorCoherence.tensorCompletionModel_nonempty l E U
  obtain ⟨sc, r, hr⟩ := openQuotientScalarUnitCompatibility l E j C.operations C.coefficients
  refine ⟨tensorX, tensorU, sc, r, ?_⟩
  intro Q F _hQ _hF _hcQ _hcF
  obtain ⟨bX⟩ := balanced_nonempty l E X
    ((OpenSemilinearTensor.extensionComplex l E j C.operations).obj Q) F
  obtain ⟨bU⟩ := balanced_nonempty l E U Q
    ((OpenSemilinearTensor.restrictionComplex l E j C.operations).obj F)
  obtain ⟨d⟩ := openQuotientCoefficientComparisons l E j C.operations
    C.strictOpen.totalComparison sc C.coefficients r Q F bX bU
  let aX := augmentationOfBalanced l E X _ _ bX
  let aU := augmentationOfBalanced l E U _ _ bU
  have hs : aX.map ≫ d.gamma.hom =
      augmentedLowerRoute l E j C.operations C.strictOpen.totalComparison Q F aU :=
    augmentation_square l E j C.operations C.strictOpen.totalComparison sc C.coefficients
      r hr Q F bX bU d
  let z : StrictSquare l E j C.operations C.strictOpen.totalComparison sc C.coefficients r
      Q F :=
    { balancingX := bX
      balancingU := bU
      upper := aX
      lower := aU
      gamma := d.gamma
      finiteGamma := d.finiteGamma
      finiteGammaRestriction := d.finiteGammaRestriction
      reduction := d.reduction
      lowerRoute := augmentedLowerRoute l E j C.operations C.strictOpen.totalComparison Q F aU
      lowerRouteFormula := by
        intro n i
        apply heq_of_eq
        change (C.strictOpen.totalComparison.chain Q F).hom.f i ≫
          (𝟙 _ ≫ (IntegralOpenReduction.extension l E j C.operations).map
            ((aU.map.app n).f i)) = _
        exact congrArg
          (fun f ↦ (C.strictOpen.totalComparison.chain Q F).hom.f i ≫ f)
          (Category.id_comp
            ((IntegralOpenReduction.extension l E j C.operations).map ((aU.map.app n).f i)))
      square := hs
      derivedSquare := by
        rw [← Functor.map_comp, ← Functor.map_comp, hs] }
  exact ⟨z, augmentation_roos_normalized l E X tensorX _ _ aX,
    augmentation_roos_normalized l E U tensorU _ _ aU⟩

end WeilConjectures.OpenTensorQuotient

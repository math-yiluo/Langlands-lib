/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs
import all WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientNormalization
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedScalarTensorSubstitution
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedScalarPullbackSubstitution

/-! # Quotient realization steps

Source: integral comparison proof, quotient normalization and coherent substitution.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
attribute [-instance] WeilConjectures.SemilinearSections.locallyBijective
attribute [-instance] WeilConjectures.finiteSystemSequenceSmall
attribute [-instance] AlgebraicGeometry.ProEtale.VaryingRing.sequenceSiteSmall
attribute [instance 4000] SheafOfModules.monoidalCategory
attribute [instance 4000] HomologicalComplex.monoidalCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open MonoidalCategory
namespace WeilConjectures.CompletedQuotient
universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] tensorSubstitution comparison pullBridge pullSubstitution
  substitution transport strictMap scalarSubstitution scalarBeta scalarTransport
  scalarLeft scalarRight ScalarIdentity ScalarComposition ScalarAssociation NaturalSubstitution
  ScalarGood StrictCoherence ScalarLimitImage reduction
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local implicit_reducible] value expression IntegralCoherence.value scalarQuotients

attribute [local implicit_reducible] integralScalarExtension integralScalarExtensionOfUniverses
  integralComparisonDerivedSequenceScalar sfConstructibleIntegralScalarExtension substituteInputs
  ScalarExtensionTower.tensor coefficientTotalTensor sourceExpression targetExpression
  constructibleIntegralPullback constructibleIntegralTensor IntegralCoherence.complexMonoidal
  SheafOfModules.cochainModulesMonoidal

/-- The uncancelled completed scalar left coordinate.
Source: Stacks 07A4 and 0941; quotient scalar-route proof.
(blueprint: lem-pur-completed-scalar-left-coordinate).

Proof: apply the pullback scalar substitution law to the tensor of the inputs, then the tensor
scalar substitution law at Y. Naturality of pullback substitution moves the tensor scalar
comparison across the strict sigma factor. -/
theorem scalarRouteLeftCoordinate
    {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ : ∀ i : Fin 3, DerivedCategory.Q.obj (P i).obj ≅ (M i).obj)
    (good : GoodExpressions l E h f P)
    (ρX : IntegralComparisonRoosModel l L X) (ρY : IntegralComparisonRoosModel l L Y)
    (SX : IntegralComparisonScalarModel l E L ι X (pullbackTensorCalculus l E X) ρX)
    (SY : IntegralComparisonScalarModel l E L ι Y (pullbackTensorCalculus l E Y) ρY)
    (goodL : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      StrictQuotient.SystemGood l L (strictValue l L (scalarQuotients l E L ι P) A))  :
    scalarSubstitution l E L ι SX
        (strictValue l E (fun i ↦ quotient l E (P i).obj) (sourceExpression h f))
        (substitution l E P (fun i ↦ (M i).obj) φ good (sourceExpression h f)) ≫
      (coefficientSequenceLimit l L X).map (DerivedCategory.Q.map
        (scalarLeft l E L ι f (quotient l E (P 0).obj)
          (quotient l E (P 1).obj)).hom) =
    (integralPullbackScalarComparison l E L ι f
        ((constructibleIntegralTensor l E Y).obj (M 0, M 1))).hom.hom ≫
      (integralDerivedPullback l L f).map
        (integralTensorScalarComparison l E L ι Y (M 0) (M 1)).hom.hom ≫
      scalarBeta l E L ι M P φ good SY goodL (sourceExpression h f) ≫
      (coefficientSequenceLimit l L X).map (DerivedCategory.Q.map
        (comparison l L f ((scalarQuotients l E L ι P) 0)
          ((scalarQuotients l E L ι P) 1)).hom) := by
  let A (i : Fin 3) : StrictQuotient.Complex l E Y := quotient l E (P i).obj
  let β (i : Fin 3) : (M i).obj ⟶
      (coefficientSequenceLimit l E Y).obj (DerivedCategory.Q.obj (A i)) :=
    (pullbackTensorCalculus l E Y).adjunction.unit.app (M i).obj ≫
      (coefficientSequenceLimit l E Y).map
        ((pullbackTensorCalculus l E Y).reduction.map (φ i).inv ≫
          (pullbackTensorReductionModel l E Y).hom.app (P i))
  let C (i : Fin 3) : StrictQuotient.Complex l L Y :=
    (ScalarExtensionTower.scalar l E L ι Y).obj (A i)
  let βs (i : Fin 3) := scalarSubstitution l E L ι SY (A i) (β i)
  let LE := coefficientSequenceLimit l E X
  let LL := coefficientSequenceLimit l L X
  dsimp only [substitution, substituteInputs, sourceExpression, targetExpression, scalarBeta]
  have hp := completedScalarPullbackSubstitution l E L ι f SX SY
    ((constructibleIntegralTensor l E Y).obj (M 0, M 1))
    (StrictQuotient.total l E (A 0) (A 1)) (good (.tensor (.input 0) (.input 1)))
    (tensorSubstitution l E (A 0) (A 1) (good (.input 0)) (good (.input 1)) (β 0) (β 1))
  have ht := completedScalarTensorSubstitution l E L ι SY (M 0) (M 1)
    (A 0) (A 1) (good (.input 0)) (good (.input 1))
    (goodL (.input 0)) (goodL (.input 1)) (β 0) (β 1)
  have hn := pull_substitution_naturality l L f
    (scalarSubstitution l E L ι SY (StrictQuotient.total l E (A 0) (A 1))
      (tensorSubstitution l E (A 0) (A 1) (good (.input 0)) (good (.input 1))
        (β 0) (β 1)))
    (tensorSubstitution l L (C 0) (C 1) (goodL (.input 0)) (goodL (.input 1))
      (βs 0) (βs 1))
    (integralTensorScalarComparison l E L ι Y (M 0) (M 1)).hom.hom
    (((ScalarExtensionTower.comparisons l).sigma E L ι Y).hom.app (A 0, A 1)) ht.symm
  change _ ≫ LL.map (DerivedCategory.Q.map (scalarLeft l E L ι f (A 0) (A 1)).hom) = _
  with_unfolding_all
    change scalarSubstitution l E L ι SX
      (StrictQuotient.pull l E f (StrictQuotient.total l E (A 0) (A 1)))
      (pullSubstitution l E f (StrictQuotient.total l E (A 0) (A 1))
        (tensorSubstitution l E (A 0) (A 1) (good (.input 0)) (good (.input 1))
          (β 0) (β 1))) ≫
        LL.map (DerivedCategory.Q.map (scalarLeft l E L ι f (A 0) (A 1)).hom) =
      (integralPullbackScalarComparison l E L ι f
        ((constructibleIntegralTensor l E Y).obj (M 0, M 1))).hom.hom ≫
      (integralDerivedPullback l L f).map
        (integralTensorScalarComparison l E L ι Y (M 0) (M 1)).hom.hom ≫
      pullSubstitution l L f (StrictQuotient.total l L (C 0) (C 1))
        (tensorSubstitution l L (C 0) (C 1) (goodL (.input 0)) (goodL (.input 1))
          (βs 0) (βs 1)) ≫
      LL.map (DerivedCategory.Q.map (comparison l L f (C 0) (C 1)).hom)
  with_unfolding_all
    unfold scalarLeft
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp]
    rw [← Category.assoc, ← Category.assoc, hp]
    simp only [Category.assoc]
    rw [← reassoc_of% hn]

end WeilConjectures.CompletedQuotient

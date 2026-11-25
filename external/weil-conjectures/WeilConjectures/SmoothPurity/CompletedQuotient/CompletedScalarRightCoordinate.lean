/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedScalarRightSubstitution

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

private theorem cancel_transport {C : Type*} [Category C] {a b c d : C}
    (s : a ⟶ b) (v : b ⟶ c) (r : d ⟶ c) [IsIso r] :
    (s ≫ v ≫ (asIso r).inv) ≫ r = s ≫ v := by
  change (s ≫ v ≫ (asIso r).inv) ≫ (asIso r).hom = s ≫ v
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

attribute [local irreducible] coefficientSequenceLimit coefficientConstantTowerLimit
  HasDerivedCategory.standard

/-- The uncancelled completed scalar right coordinate.
Source: Stacks 07A4 and 0941; quotient scalar-route proof.
(blueprint: lem-pur-completed-scalar-right-coordinate).

Proof: cancel the inverse target substitution in E transport. Scalar substitution naturality
moves this transported map across the strict E comparison. Apply tensor scalar substitution at X
and the pullback scalar substitution law on each input; tensor substitution naturality combines
the two kappa factors. -/
theorem scalarRouteRightCoordinate
    {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ : ∀ i : Fin 3, DerivedCategory.Q.obj (P i).obj ≅ (M i).obj)
    (good : GoodExpressions l E h f P)
    (invertible : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      IsIso (substitution l E P (fun i ↦ (M i).obj) φ good A))
    (ρX : IntegralComparisonRoosModel l L X) (ρY : IntegralComparisonRoosModel l L Y)
    (SX : IntegralComparisonScalarModel l E L ι X (pullbackTensorCalculus l E X) ρX)
    (SY : IntegralComparisonScalarModel l E L ι Y (pullbackTensorCalculus l E Y) ρY)
    (goodL : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      StrictQuotient.SystemGood l L (strictValue l L (scalarQuotients l E L ι P) A))  :
    scalarSubstitution l E L ι SX
        (strictValue l E (fun i ↦ quotient l E (P i).obj) (sourceExpression h f))
        (substitution l E P (fun i ↦ (M i).obj) φ good (sourceExpression h f)) ≫
      (coefficientSequenceLimit l L X).map (DerivedCategory.Q.map
        (scalarRight l E L ι f (quotient l E (P 0).obj)
          (quotient l E (P 1).obj)).hom) =
    (integralScalarExtension l E L ι X).map
      (transport l E P (fun i ↦ (M i).obj) φ good invertible
        (sourceExpression h f) (targetExpression h f)
        (comparison l E f (quotient l E (P 0).obj) (quotient l E (P 1).obj)).hom) ≫
      (integralTensorScalarComparison l E L ι X
        ((constructibleIntegralPullback l E f).obj (M 0))
        ((constructibleIntegralPullback l E f).obj (M 1))).hom.hom ≫
      (integralCompletedTensor l L X).map (Prod.mkHom
        (integralPullbackScalarComparison l E L ι f (M 0)).hom.hom
        (integralPullbackScalarComparison l E L ι f (M 1)).hom.hom) ≫
      scalarBeta l E L ι M P φ good SY goodL (targetExpression h f) := by
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
  let t :
      (integralDerivedPullback l E f).obj
          ((integralCompletedTensor l E Y).obj ((M 0).obj, (M 1).obj)) ⟶
        (integralCompletedTensor l E X).obj
          ((integralDerivedPullback l E f).obj (M 0).obj,
            (integralDerivedPullback l E f).obj (M 1).obj) :=
    transport l E P (fun i ↦ (M i).obj) φ good invertible
      (sourceExpression h f) (targetExpression h f) (comparison l E f (A 0) (A 1)).hom
  have hc : t ≫ substitution l E P (fun i ↦ (M i).obj) φ good
        (targetExpression h f) =
      substitution l E P (fun i ↦ (M i).obj) φ good (sourceExpression h f) ≫
        LE.map (DerivedCategory.Q.map (comparison l E f (A 0) (A 1)).hom) := by
    dsimp only [t]
    unfold transport
    exact @cancel_transport _ _ _ _ _ _ _ _ _ (invertible (targetExpression h f))
  have hsrc : substitution l E P (fun i ↦ (M i).obj) φ good
        (sourceExpression h f) =
      pullSubstitution l E f (StrictQuotient.total l E (A 0) (A 1))
        (tensorSubstitution l E (A 0) (A 1) (good (.input 0)) (good (.input 1))
          (β 0) (β 1)) := by with_unfolding_all rfl
  have htgt : substitution l E P (fun i ↦ (M i).obj) φ good
        (targetExpression h f) =
      tensorSubstitution l E (StrictQuotient.pull l E f (A 0))
        (StrictQuotient.pull l E f (A 1)) (good (.pullF (.input 0)))
        (good (.pullF (.input 1))) (pullSubstitution l E f (A 0) (β 0))
        (pullSubstitution l E f (A 1) (β 1)) := by with_unfolding_all rfl
  rw [hsrc, htgt] at hc
  with_unfolding_all
    change scalarSubstitution l E L ι SX
      (StrictQuotient.pull l E f (StrictQuotient.total l E (A 0) (A 1)))
      (pullSubstitution l E f (StrictQuotient.total l E (A 0) (A 1))
        (tensorSubstitution l E (A 0) (A 1) (good (.input 0)) (good (.input 1))
          (β 0) (β 1))) ≫
        LL.map (DerivedCategory.Q.map (scalarRight l E L ι f (A 0) (A 1)).hom) =
      (integralScalarExtension l E L ι X).map t ≫
      (integralTensorScalarComparison l E L ι X
        ((constructibleIntegralPullback l E f).obj (M 0))
        ((constructibleIntegralPullback l E f).obj (M 1))).hom.hom ≫
      (integralCompletedTensor l L X).map (Prod.mkHom
        (integralPullbackScalarComparison l E L ι f (M 0)).hom.hom
        (integralPullbackScalarComparison l E L ι f (M 1)).hom.hom) ≫
      tensorSubstitution l L (StrictQuotient.pull l L f (C 0))
        (StrictQuotient.pull l L f (C 1))
        (goodL (.pullF (.input 0))) (goodL (.pullF (.input 1)))
        (pullSubstitution l L f (C 0) (βs 0)) (pullSubstitution l L f (C 1) (βs 1))
  exact scalarRouteRightSubstitution l E L ι f SX SY M A
    (fun i ↦ good (.input i)) (fun i ↦ good (.pullF (.input i)))
    (fun i ↦ goodL (.pullF (.input i))) β t hc

end WeilConjectures.CompletedQuotient

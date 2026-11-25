/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedQuotientPullbackRealizationNormalization
import all WeilConjectures.SmoothPurity.CompletedQuotient.CompletedScalarTensorSubstitution
import all WeilConjectures.TraceFormula.Supporting.AmbientComparisonSystemExistence
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTowerPullbackLimitSquare
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFixedCalculusModels
import WeilConjectures.SmoothPurity.Normalized.NormalizedCompletionRealization

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

attribute [local implicit_reducible] integralScalarExtension integralScalarExtensionOfUniverses
  integralComparisonDerivedSequenceScalar integralComparisonDerivedSequencePullback
  pullbackTensorReferencePullback sfConstructibleIntegralScalarExtension
  constructibleIntegralPullback constructibleIntegralTensor
attribute [local implicit_reducible] value expression IntegralCoherence.value scalarQuotients

attribute [local irreducible] pullbackTensorCalculus integralDerivedPullback
  integralCompletedTensor coefficientTotalTensor SheafOfModules.monoidalCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory

private def fixedModels (W : Bool → Scheme.{u})
    [∀ b, ∀ x : W b, Invertible (l : (W b).residueField x)]
    (ρ : ∀ b, IntegralComparisonRoosModel l E (W b)) :
    CompletedOperations.Models l E W := by
  classical
  have hc (b : Bool) := CompletionUnit.fixedCalculusModels l E (W b)
    (pullbackTensorCalculus l E (W b))
  choose O hD using hc
  let D (b) := Classical.choice (hD b)
  have hu (b : Bool) (x : W b) : IsUnit (l : (W b).presheaf.stalk x) := by
    apply isUnit_of_map_unit (IsLocalRing.residue ((W b).presheaf.stalk x))
    rw [map_natCast]
    with_unfolding_all exact isUnit_of_invertible (l : (W b).residueField x)
  have hn (b : Bool) := normalizedCompletionRealization l E (W b)
    (pullbackTensorCalculus l E (W b)) (O b) (D b) (hu b)
  choose c hcu using hn
  exact {
    calculus := fun b ↦ pullbackTensorCalculus l E (W b)
    system := fun b ↦ Classical.choice (ringedSiteDualityMaps_exists
      (coefficientSequenceTopology (Scheme.ProEt.topology (W b)))
      (coefficientSequenceCommRingSheaf l E (W b)))
    completion := c
    completion_unit := hcu
    roos := ρ
    pullback := fun {a b} f ↦ ⟨completedQuotientPullbackRealization l E f,
      completedQuotientPullbackRealization_normalized l E f (ρ a)⟩ }

attribute [local implicit_reducible] fixedModels

private theorem pullSubstitution_model {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : DerivedCategory (scalarReductionSource l E Y)} (A : StrictQuotient.Complex l E Y)
    (β : K ⟶ (coefficientSequenceLimit l E Y).obj (DerivedCategory.Q.obj A)) :
    pullSubstitution l E f A β =
      (completedQuotientPullbackRealization l E f).hom.app K ≫
        (coefficientSequenceLimit l E X).map
          ((integralComparisonDerivedSequencePullback l E f).map (reduction l E β)) ≫
        (coefficientSequenceLimit l E X).map
          ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app A) := by
  exact completedQuotientPullbackRealization_substitution l E f A β

/-- Scalar extension of a completed pullback substitution in its fixed limit coordinates.
Source: Stacks 07A4 and 0941; quotient scalar-coordinate proof.
(blueprint: lem-pur-completed-scalar-pullback-substitution).

Proof: equip the fixed calculi with normalized completion and pullback models.
Express the reduction of pullSubstitution through its transported realization.
The normalized system scalar/pullback equation and naturality move the strict
kappa factor across reduction of beta. Apply the scalar tower pullback limit
square, and reverse the scalar-reduction and pullback-substitution formulas. -/
theorem completedScalarPullbackSubstitution {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    {ρX : IntegralComparisonRoosModel l L X} {ρY : IntegralComparisonRoosModel l L Y}
    (SX : IntegralComparisonScalarModel l E L ι X (pullbackTensorCalculus l E X) ρX)
    (SY : IntegralComparisonScalarModel l E L ι Y (pullbackTensorCalculus l E Y) ρY)
    (M : sfIntegralConstructibleCategory l E Y)
    (A : StrictQuotient.Complex l E Y) (hA : StrictQuotient.SystemGood l E A)
    (β : M.obj ⟶ (coefficientSequenceLimit l E Y).obj (DerivedCategory.Q.obj A)) :
    scalarSubstitution l E L ι SX (StrictQuotient.pull l E f A)
        (pullSubstitution l E f A β) ≫
      (coefficientSequenceLimit l L X).map (DerivedCategory.Q.map
        ((ScalarExtensionTower.kappa l E L ι f).hom.app A)) =
    (integralPullbackScalarComparison l E L ι f M).hom.hom ≫
      pullSubstitution l L f ((ScalarExtensionTower.scalar l E L ι Y).obj A)
        (scalarSubstitution l E L ι SY A β) := by
  classical
  let W : Bool → Scheme.{u} := fun b ↦ cond b X Y
  let : ∀ b, ∀ x : W b, Invertible (l : (W b).residueField x) := by
    intro b
    cases b <;> infer_instance
  let ρL : ∀ b, IntegralComparisonRoosModel l L (W b) := fun b ↦
    match b with
    | true => ρX
    | false => ρY
  let ρE : ∀ b, IntegralComparisonRoosModel l E (W b) := fun b ↦
    (ambientRoos l E (W b) (pullbackTensorCalculus l E (W b))).some
  let ME := fixedModels l E W ρE
  let ML := fixedModels l L W ρL
  let FE := integralComparisonDerivedSequencePullback l E f
  let FL := integralComparisonDerivedSequencePullback l L f
  let SXD := integralComparisonDerivedSequenceScalar l E L ι X
  let SYD := integralComparisonDerivedSequenceScalar l E L ι Y
  let LL := coefficientSequenceLimit l L X
  let LE := coefficientSequenceLimit l E X
  let α := integralComparisonSystemScalarPullback l E L ι f
  let a := reduction l E β
  let εE := (integralComparisonSequencePullback l E f).mapDerivedCategoryFactors
  let εL := (integralComparisonSequencePullback l L f).mapDerivedCategoryFactors
  have hlim := ScalarExtensionTower.scalarTowerPullbackLimitSquare l E L ι W ME ML
    SX SY f (prime_unit l X) (prime_unit l Y) M
    ((constructibleIntegralPullback l E f).obj M).property.1
  with_unfolding_all
    change (integralPullbackScalarComparison l E L ι f M).hom.hom ≫
        (completedQuotientPullbackRealization l L f).hom.app
          ((integralScalarExtension l E L ι Y).obj M.obj) ≫
        LL.map (FL.map (ScalarExtensionTower.scalarReduction l E L ι Y
          (pullbackTensorCalculus l E Y) (pullbackTensorCalculus l L Y) ρY SY M.obj)) =
      SX.realization.hom.app ((integralDerivedPullback l E f).obj M.obj) ≫
        LL.map (SXD.map (ScalarExtensionTower.pullbackReduction l E W ME f M.obj) ≫
          α.hom.app ((pullbackTensorCalculus l E Y).reduction.obj M.obj)) at hlim
  have hn := (integralComparisonSystemScalarPullback_existsUnique l E L ι f).exists.choose_spec
    A hA.1
  change SXD.map (εE.hom.app A) ≫
      (integralComparisonSequenceScalarModel l E L ι X).ε.app
        (StrictQuotient.pull l E f A) ≫ DerivedCategory.Q.map
        ((ScalarExtensionTower.kappa l E L ι f).hom.app A) =
    α.hom.app (DerivedCategory.Q.obj A) ≫
      FL.map ((integralComparisonSequenceScalarModel l E L ι Y).ε.app A) ≫
      εL.hom.app ((ScalarExtensionTower.scalar l E L ι Y).obj A) at hn
  have hnat := α.hom.naturality a
  change SXD.map (FE.map a) ≫ α.hom.app (DerivedCategory.Q.obj A) =
    α.hom.app ((pullbackTensorCalculus l E Y).reduction.obj M.obj) ≫ FL.map (SYD.map a)
    at hnat
  have hred : reduction l E (pullSubstitution l E f A β) =
      ScalarExtensionTower.pullbackReduction l E W ME f M.obj ≫ FE.map a ≫
        εE.hom.app A := by
    rw [pullSubstitution_model, ← LE.map_comp, reduction_post]
    with_unfolding_all rfl
  conv_lhs => unfold scalarSubstitution
  rw [hred]
  simp only [Functor.map_comp, Category.assoc]
  have hnL := congrArg LL.map hn
  have hnatL := congrArg LL.map hnat
  simp only [Functor.map_comp] at hnL hnatL
  rw [hnL, reassoc_of% hnatL]
  have hh := congrArg (fun k ↦ k ≫ LL.map
    (FL.map (SYD.map a) ≫
      FL.map ((integralComparisonSequenceScalarModel l E L ι Y).ε.app A) ≫
      εL.hom.app ((ScalarExtensionTower.scalar l E L ι Y).obj A))) hlim.symm
  simp only [Functor.map_comp, Category.assoc] at hh ⊢
  rw [hh]
  rw [pullSubstitution_model, scalar_reduction]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end WeilConjectures.CompletedQuotient

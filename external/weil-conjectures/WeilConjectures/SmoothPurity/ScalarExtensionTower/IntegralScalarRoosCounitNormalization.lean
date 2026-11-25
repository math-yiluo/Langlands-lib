/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
public import WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import WeilConjectures.TraceFormula.Scalar.ScalarModelRoosCounitNormalization

/-! # The normalized Roos counit in the ordinary integral scalar model -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction coefficientSequenceLimit
  integralDerivedPullback integralOrdinaryScalar integralComparisonSequenceScalarPullback
  completedIntegralCommRingSheafUnrestricted
  integralOperationsRoos integralOperationsRoosMap scalarRoosMap

attribute [local implicit_reducible] integralScalarExtension integralScalarExtensionOfUniverses
  integralComparisonDerivedSequenceScalar completedOrdinaryScalarComplex
  integralScalarComplexFunctor integralOperationsGoodLocalization
  integralOperationsRoosFunctor integralOperationsPullbackComplexFunctor
  NatIso.mapHomologicalComplex
  integralOperationsPullbackOnGood integralComparisonSequencePullback
  integralComparisonDerivedSequencePullback HomologicalComplex.asFunctor
  HomologicalComplex.complexOfFunctorsToFunctorToComplex

/-- Transport the normalized scalar Roos counit to the ordinary integral scalar model.
Source: Stacks 06YY and 0941, universal derived scalar counits and total limits.
(blueprint: lem-pur-integral-scalar-roos-counit-normalization).

Proof: evaluate the prescribed scalar-completion comparison on the total limit.
Naturality of the derived comparison moves it past the inverse Roos bridge.
Apply the existing normalized scalar Roos counit equation. The prescribed
cochain-counit comparison then gives the ordinary integral scalar factors.
Functoriality and associativity identify the resulting composite. -/
theorem integralScalarRoosCounitNormalization (X : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus l E X)
    (ρE : IntegralComparisonRoosModel l E X)
    (ρL : IntegralComparisonRoosModel l L X)
    (SX : IntegralComparisonScalarModel l E L ι X S ρL)
    (t : integralOrdinaryScalar l E L ι X ≅ completedOrdinaryScalarExtension l E L ι X)
    (e : integralOrdinaryDerivedScalar l E L ι X ≅
      completedDerivedScalarExtension l E L ι X)
    (he : ∀ P : CochainComplex (integralTowerModules l E X) ℤ,
      e.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit l E L ι X P =
        (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app P))
    (hχ : e.hom ≫ completedScalarComparison l E L ι X = scalarCompletion l E L ι X)
    (H : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (a : (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj H).asFunctor
        ⋙ completedOrdinaryScalarComplex l E L ι X ⟶
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l E L ι X).E.mapHomologicalComplex
          (.up ℤ)).obj H)).asFunctor)
    (ha : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
      (x : (H.X i).val.obj (op (n, U.unop))),
      ((a.app (op n)).f i).val.app U
        (completedScalarTensorSection l E L ι X
          (((coefficientSequenceRestriction l E X).obj (H.X i)).obj (op n)) U s
          (integralComparisonRestrictedSection l E X (H.X i) n U x)) =
        integralComparisonRestrictedSection l L X
          ((integralComparisonSequenceScalarModel l E L ι X).E.obj (H.X i)) n U
          (integralComparisonSequenceTensorSection l E L ι X (H.X i) (op (n, U.unop))
            ((completedIntegralCommRingProjectionUnrestricted l L X n).hom.app U s) x)) :
    let Z := integralOperationsRoos
      (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj H).asFunctor
    (integralOrdinaryDerivedScalar l E L ι X).map
        (integralComparisonRoosBridge l E X ρE H).inv ≫
      (scalarCompletion l E L ι X).app
        ((coefficientSequenceLimit l E X).obj (DerivedCategory.Q.obj H)) ≫
      SX.realization.hom.app
        ((coefficientSequenceLimit l E X).obj (DerivedCategory.Q.obj H)) ≫
      (coefficientSequenceLimit l L X).map
        ((integralComparisonDerivedSequenceScalar l E L ι X).map
          (S.adjunction.counit.app (DerivedCategory.Q.obj H))) ≫
      (coefficientSequenceLimit l L X).map
        ((integralComparisonSequenceScalarModel l E L ι X).ε.app H) ≫
      (integralComparisonRoosBridge l L X ρL _).hom =
    (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app Z ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app Z ≫
        scalarRoosMap (completedOrdinaryScalarExtension l E L ι X)
          (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj H).asFunctor
          ≫ integralOperationsRoosMap a) := by
  let B := integralComparisonRoosBridge l E X ρE H
  let M := (coefficientSequenceLimit l E X).obj (DerivedCategory.Q.obj H)
  have hc := NatTrans.congr_app hχ M
  have hn := e.hom.naturality B.inv
  have h := scalarModelRoos_counit_normalization l E L ι X S ρE ρL SX H a ha
  rw [← hc]
  simp only [NatTrans.comp_app, ← Category.assoc]
  rw [hn]
  simp only [Category.assoc]
  rw [h, ← Category.assoc, he]
  simp only [Functor.map_comp, Category.assoc]

end WeilConjectures.ScalarExtensionTower

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.FourierTransform.CompletedLineTensor.CompletedLineTensorCoherence
public import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherence
import WeilConjectures.TraceFormula.Scalar.ScalarModelIteratedStrictCalculation
import WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Scalar model normalization before inverting completion

Source: Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1;
Stacks Project, Tags 06YY and 0941.
(blueprint: lem-trf-scalar-model-associativity)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction coefficientSequenceLimit
  integralScalarExtensionOfUniverses completedDerivedScalarExtension
  completedOrdinaryScalarComplex completedScalarCounit

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] F)
  (X : Scheme.{u})

/-- Ordinary scalar associativity commutes with quotient-normalized realization,
before any completion map is inverted. This holds on the ambient derived category.
Source: Bhatt--Scholze, Definition 3.4.10, Proposition 3.5.1 and Lemma 3.5.7;
Stacks 06YY, 0941, the scalar calculation in steps 8--10 of the parent.
(blueprint: lem-trf-scalar-model-associativity)

Proof: take a flat-term K-flat complex representing K, and a simultaneous strict
quotient presentation for its reduction. The three scalar-model normalizations
identify their realization maps with the Roos maps of the actual quotient tensors.
The initial completion maps have the quotient tensor maps in their unshifted
coordinates and zero shifted coordinates, by quotient_scalar_comparison_descent.
Use integralConeCounitRealization to replace insertion of the whole-system counit
by the original compatible family of quotient maps. The adjuncts of both displayed
arrows then have, at each quotient, the same map on generators:
c tensor (b tensor (a tensor x)) maps to c*j(b)*j(iota(a)) tensor x.
Balancing gives equality on all sections; sheafification preserves it. Multiplication
commutes with quotient transitions, restrictions, and the cochain differential.
Thus this is equality of strict diagram morphisms before localization. The universal
cochain counits identify their localizations with the specified ordinary and system
associators. The adjunction Hom bijection gives the displayed equality. Naturality
and K-flat resolutions transport it to arbitrary K. No separate evaluation functor
is assumed faithful, and no completion chain map is inverted. -/
theorem scalarModelAssociativity
    (SE : CoefficientDerivedSystemCalculus l E X)
    (SL : CoefficientDerivedSystemCalculus l L X)
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (bEL : IntegralComparisonScalarModel l E L ι X SE ρL)
    (bLF : IntegralComparisonScalarModel l L F j X SL ρF)
    (bEF : IntegralComparisonScalarModel l E F (j.comp ι) X SE ρF)
    (K : DerivedCategory (scalarReductionSource l E X)) :
    (completedDerivedScalarExtension l L F j X).map
        ((completedScalarComparison l E L ι X).app K) ≫
      (completedScalarComparison l L F j X).app
        ((integralScalarExtensionOfUniverses l E L ι X).obj K) ≫
      (integralScalarExtensionOfUniverses l L F j X).map (bEL.realization.hom.app K) ≫
      bLF.realization.hom.app
        ((coefficientSequenceLimit l L X).obj
          ((integralComparisonDerivedSequenceScalar l E L ι X).obj (SE.reduction.obj K))) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonDerivedSequenceScalar l L F j X).map
          (SL.adjunction.counit.app
            ((integralComparisonDerivedSequenceScalar l E L ι X).obj (SE.reduction.obj K)))) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonSystemScalarComposition l E L F ι j X).hom.app
          (SE.reduction.obj K)) =
    (CompletedLineTensor.associatorData l E X L ι F j).derived.hom.app K ≫
      (completedScalarComparison l E F (j.comp ι) X).app K ≫ bEF.realization.hom.app K := by
  let B := completedDerivedScalarExtension l L F j X
  let C := integralScalarExtensionOfUniverses l E L ι X
  let D := integralScalarExtensionOfUniverses l L F j X
  let A := integralComparisonDerivedSequenceScalar l E L ι X
  let A' := integralComparisonDerivedSequenceScalar l L F j X
  let T := coefficientSequenceLimit l F X
  let α : completedDerivedScalarExtension l E L ι X ⋙ B ⟶
      SE.reduction ⋙ integralComparisonDerivedSequenceScalar l E F (j.comp ι) X ⋙ T :=
    Functor.whiskerRight (completedScalarComparison l E L ι X) B ≫
      Functor.whiskerLeft C (completedScalarComparison l L F j X) ≫
      Functor.whiskerRight bEL.realization.hom D ≫
      Functor.whiskerLeft (SE.reduction ⋙ A ⋙ coefficientSequenceLimit l L X)
        bLF.realization.hom ≫
      Functor.whiskerLeft (SE.reduction ⋙ A)
        (Functor.whiskerRight (Functor.whiskerRight SL.adjunction.counit A') T) ≫
      Functor.whiskerLeft SE.reduction
        (Functor.whiskerRight
          (integralComparisonSystemScalarComposition l E L F ι j X).hom T)
  let β : completedDerivedScalarExtension l E L ι X ⋙ B ⟶
      SE.reduction ⋙ integralComparisonDerivedSequenceScalar l E F (j.comp ι) X ⋙ T :=
    (CompletedLineTensor.associatorData l E X L ι F j).derived.hom ≫
      completedScalarComparison l E F (j.comp ι) X ≫ bEF.realization.hom
  have h : α = β := by
    let Λ := integralOperationsGoodLocalization l E X
    let W := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
      (integralOperationsGoodComplex l E X).ι
    let : Λ.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E X
    apply Localization.natTrans_ext Λ W
    intro P
    obtain ⟨C₀, e, κ, hC, hcoh⟩ := coherentPrimitiveReductionPresentation l E SE P
    obtain ⟨q, hq, hn⟩ := bEF.normalization P C₀ e κ hC hcoh
    let t := T.map
        ((integralComparisonDerivedSequenceScalar l E F (j.comp ι) X).map e.hom) ≫
      T.map ((integralComparisonSequenceScalarModel l E F (j.comp ι) X).ε.app C₀) ≫
      (integralComparisonRoosBridge l F X ρF _).hom ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom)
    change bEF.realization.hom.app (DerivedCategory.Q.obj P.obj) ≫ t =
      (integralScalarExtensionComparisonOfUniverses l E F (j.comp ι) X).hom.app P at hn
    have : IsIso (bEF.realization.hom.app (DerivedCategory.Q.obj P.obj) ≫ t) := by
      rw [hn]
      infer_instance
    have : IsIso t := IsIso.of_isIso_comp_left
      (bEF.realization.hom.app (DerivedCategory.Q.obj P.obj)) t
    apply (cancel_mono t).1
    have hs := scalarModelIteratedStrictCalculation l E L F ι j X
      SE SL ρL ρF bEL bLF P C₀ e κ hC hcoh q hq
    have hnorm : CompletedLineTensor.IsAssociatorNormalized l E X L ι F j
        (CompletedLineTensor.associatorData l E X L ι F j) := by
      unfold CompletedLineTensor.associatorData
      exact (CompletedLineTensor.associatorData_existsUnique l E X L ι F j).exists.choose_spec
    have ha := hnorm.2 P
    have hc := (completedScalarComparison_existsUnique l E F (j.comp ι) X).exists.choose_spec P
    change (completedScalarComparison l E F (j.comp ι) X).app
      (DerivedCategory.Q.obj P.obj) ≫
        (integralScalarExtensionComparisonOfUniverses l E F (j.comp ι) X).hom.app P = _ at hc
    change α.app (DerivedCategory.Q.obj P.obj) ≫ t =
      β.app (DerivedCategory.Q.obj P.obj) ≫ t
    calc
      α.app (DerivedCategory.Q.obj P.obj) ≫ t =
          B.map (completedScalarCounit l E L ι X P.obj) ≫
            completedScalarCounit l L F j X
              ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ≫
            DerivedCategory.Q.map
              ((CompletedLineTensor.scalarAssociatorComplex l E X L ι F j
                (CompletedLineTensor.associatorData l E X L ι F j).sheaf).hom.app P.obj) ≫
            DerivedCategory.Q.map
              ((completedScalarChainComparison l E F (j.comp ι) X).app P.obj) := by
        simpa only [α, t, B, C, D, A, A', T, NatTrans.comp_app,
          Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj,
          Category.assoc] using hs
      _ = (CompletedLineTensor.associatorData l E X L ι F j).derived.hom.app
          (DerivedCategory.Q.obj P.obj) ≫
            (completedScalarComparison l E F (j.comp ι) X).app
              (DerivedCategory.Q.obj P.obj) ≫
            (integralScalarExtensionComparisonOfUniverses l E F (j.comp ι) X).hom.app P := by
        rw [hc]
        simpa only [B, Category.assoc] using congrArg
          (fun f ↦ f ≫ DerivedCategory.Q.map
            ((completedScalarChainComparison l E F (j.comp ι) X).app P.obj)) ha
      _ = β.app (DerivedCategory.Q.obj P.obj) ≫ t := by
        dsimp only [β, NatTrans.comp_app]
        simp only [Category.assoc, hn]
  exact congrArg (fun τ ↦ τ.app K) h

end WeilConjectures

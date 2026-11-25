/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Scalar completion in a coherent presentation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction coefficientSequenceLimit
  integralOrdinaryScalar completedIntegralCommRingSheafUnrestricted
  integralOperationsRoos integralOperationsRoosMap
attribute [local implicit_reducible] integralScalarExtension integralScalarExtensionOfUniverses
  integralComparisonDerivedSequenceScalar integralScalarComplexFunctor
  integralOperationsGoodLocalization integralOperationsRoosFunctor

/-- Completion in any coherent scalar quotient presentation is the normalized realization.
Source: Stacks 06YY and 0941, coherent quotient comparisons and completion augmentation.
(blueprint: lem-pur-scalar-completion-presentation-normalization).

Proof: compare the supplied qD with the scalar realization's normalized qD on scalar
quotient tensor generators. Tensor-generator extensionality makes their quotient maps equal.
The realization normalization then identifies the presentation composite with its ordinary
comparison. The defining equation of scalarCompletion and cancellation of the presentation
isomorphism give the assertion. No inverse to scalarCompletion is used. -/
theorem scalarCompletionPresentationNormalization (X : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus l E X)
    (ρ : IntegralComparisonRoosModel l L X)
    (SX : IntegralComparisonScalarModel l E L ι X S ρ)
    (R : (integralOperationsGoodComplex.{u, u} l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ)
    (eD : S.reduction.obj (DerivedCategory.Q.obj R.obj) ≅
      DerivedCategory.Q.obj D)
    (κD : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E X n).mapHomologicalComplex (.up ℤ)).obj D ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E X n).obj R.obj)
    (hpD : CoefficientReductionPresentation.{u, u} l E X
      S.toCoefficientDerivedSystemReduction R.obj R.property.1 D eD κD)
    (hcD : IsIntegralComparisonPresentationCoherent.{u, u} l E X
      S R.obj D eD κD)
    (εD : (integralComparisonDerivedSequenceScalar.{u, u} l E L ι X).obj
        (DerivedCategory.Q.obj D) ≅
      DerivedCategory.Q.obj
        (((integralComparisonSequenceScalarModel.{u, u} l E L ι X).E.mapHomologicalComplex
          (.up ℤ)).obj D))
    (hεD : εD.hom = (integralComparisonSequenceScalarModel.{u, u} l E L ι X).ε.app D)
    (qD : (((coefficientSequenceRestriction.{u, u} l L X).mapHomologicalComplex
        (.up ℤ)).obj
      (((integralComparisonSequenceScalarModel.{u, u} l E L ι X).E.mapHomologicalComplex
        (.up ℤ)).obj D)).asFunctor ≅
      (integralScalarTowerFunctor.{u, u} l E L ι X).obj R.obj)
    (hqD : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
        (s : (coefficientSequenceCommRingSheaf l L X).obj.obj (op (n, U.unop)))
        (x : (R.obj.X i).val.obj U),
        ((qD.hom.app (op n)).f i).val.app U
          (integralComparisonRestrictedSection l L X
            ((integralComparisonSequenceScalarModel l E L ι X).E.obj (D.X i)) n U
            (integralComparisonSequenceTensorSection l E L ι X (D.X i)
              (op (n, U.unop)) s
              (integralComparisonSequenceSection l E X (D.X i) n U
                (((κD n).inv.f i).val.app U
                  (unrestrictedIntegralTensorSection l E X n (R.obj.X i) U 1 x))))) =
          integralScalarTensorSection l E L ι X n (R.obj.X i) U s x) :
    let T := coefficientSequenceLimit l L X
    let A := integralComparisonDerivedSequenceScalar l E L ι X
    let SD := ((integralComparisonSequenceScalarModel l E L ι X).E.mapHomologicalComplex
      (.up ℤ)).obj D
    let rD := T.mapIso (A.mapIso eD ≪≫ εD) ≪≫
      integralComparisonRoosBridge l L X ρ SD ≪≫
      DerivedCategory.Q.mapIso (integralOperationsRoosFunctor.mapIso qD)
    (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app R.obj ≫
      DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι X).app R.obj) ≫ rD.inv =
        (scalarCompletion l E L ι X).app (DerivedCategory.Q.obj R.obj) ≫
          SX.realization.hom.app (DerivedCategory.Q.obj R.obj) := by
  classical
  dsimp only
  let T := coefficientSequenceLimit l L X
  let A := integralComparisonDerivedSequenceScalar l E L ι X
  let χ := scalarCompletion l E L ι X
  let SD := ((integralComparisonSequenceScalarModel l E L ι X).E.mapHomologicalComplex
    (.up ℤ)).obj D
  let rD := T.mapIso (A.mapIso eD ≪≫ εD) ≪≫
    integralComparisonRoosBridge l L X ρ SD ≪≫
    DerivedCategory.Q.mapIso (integralOperationsRoosFunctor.mapIso qD)
  obtain ⟨qD', hqD', hSX⟩ := SX.normalization R D eD κD hpD hcD
  have hfix : qD'.inv ≫ qD.hom = 𝟙 _ := by
    apply NatTrans.ext
    funext n
    apply HomologicalComplex.hom_ext
    intro i
    apply integralScalarReduction_hom_ext l E L ι X n.unop (R.obj.X i)
    intro U s x
    let w := integralComparisonRestrictedSection l L X
      ((integralComparisonSequenceScalarModel l E L ι X).E.obj (D.X i)) n.unop U
      (integralComparisonSequenceTensorSection l E L ι X (D.X i)
        (op (n.unop, U.unop)) s
        (integralComparisonSequenceSection l E X (D.X i) n.unop U
          (((κD n.unop).inv.f i).val.app U
            (unrestrictedIntegralTensorSection l E X n.unop (R.obj.X i) U 1 x))))
    have h₁ := hqD' n.unop i U s x
    have h₂ := hqD n.unop i U s x
    have hi : ((qD'.inv.app n).f i).val.app U
        (((qD'.hom.app n).f i).val.app U w) = w :=
      congrArg (fun k ↦ ((k.app n).f i).val.app U w) qD'.hom_inv_id
    change ((qD.hom.app n).f i).val.app U
      (((qD'.inv.app n).f i).val.app U
        (integralScalarTensorSection l E L ι X n.unop (R.obj.X i) U s x)) =
      integralScalarTensorSection l E L ι X n.unop (R.obj.X i) U s x
    exact (congrArg (fun y ↦ ((qD.hom.app n).f i).val.app U
      (((qD'.inv.app n).f i).val.app U y)) h₁.symm).trans
        ((congrArg (fun y ↦ ((qD.hom.app n).f i).val.app U y) hi).trans h₂)
  have heq : qD.hom = qD'.hom := by
    have h := congrArg (qD'.hom ≫ ·) hfix
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
      Category.comp_id] using h
  rw [← heq] at hSX
  have hn : SX.realization.hom.app (DerivedCategory.Q.obj R.obj) ≫ rD.hom =
      (integralScalarExtensionComparison l E L ι X).hom.app R := by
    simpa only [rD, T, A, SD, Iso.trans_hom, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc, hεD, integralScalarExtensionComparison,
      integralScalarExtensionComparisonOfUniverses] using hSX
  have hχ : χ.app (DerivedCategory.Q.obj R.obj) ≫
      (integralScalarExtensionComparison l E L ι X).hom.app R =
      (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app R.obj ≫
        DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι X).app R.obj) := by
    exact (scalarCompletion_existsUnique l E L ι X).exists.choose_spec.1 R
  have hs : (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app R.obj ≫
      DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι X).app R.obj) ≫
      rD.inv = χ.app (DerivedCategory.Q.obj R.obj) ≫
        SX.realization.hom.app (DerivedCategory.Q.obj R.obj) := by
    apply (cancel_mono rD.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hn]
    exact hχ.symm
  exact hs

end WeilConjectures.ScalarExtensionTower

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import WeilConjectures.TraceFormula.Scalar.ScalarModelRoosZeroLiftCore
import WeilConjectures.TraceFormula.Scalar.ScalarModelRoosZeroLiftFactorizationFromCoordinates

/-! # Existence of the normalized scalar Roos lift

Source: Stacks Project, Tags 06YY and 0941; Bhatt--Scholze, Definition 3.4.10
and Proposition 3.5.1.
(blueprint: lem-trf-scalar-model-roos-zero-lift-existence)

This is the realization and transpose part of the scalar Roos lift argument.
It produces the scalar-extended strict map and its zero-shifted coordinate
formula. The construction is independent of a second map `g`; the coordinate
uniqueness argument is isolated in the companion theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction coefficientSequenceLimit
  integralScalarExtensionOfUniverses completedDerivedScalarExtension
  completedOrdinaryScalarExtension completedScalarCounit

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] F) (X : Scheme.{u})

/-- The normalized scalar lift supplied by the realization/transpose construction.

Source: Stacks 06YY, 0941; Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1;
steps 1--2 of `lem-trf-scalar-model-roos-zero-lift`.

Proof in words: apply the proved strict core with the supplied source zero-shift
hypothesis hf. It supplies a lift with zero shifted coordinate and the normalized
quotient coordinates. Apply factorization_from_coordinates directly to this lift,
using the same hf. No intermediate factorized-existence or uniqueness wrapper is
needed. -/
theorem scalarModelRoosZeroLift_existence
    (SL : CoefficientDerivedSystemCalculus l L X)
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (b : IntegralComparisonScalarModel l L F j X SL ρF)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (f : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor)
    (hf : ∀ i : ℤ, f.f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex
          (.up ℤ)).obj D).asFunctor)).v i (i - 1) (by omega) = 0) :
    let hType := (completedOrdinaryScalarComplex l L F j X).obj
      ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ⟶
      integralOperationsRoos
        (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
          (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
            (.up ℤ)).obj D)).asFunctor
    ∃ h : hType,
      (∀ i : ℤ, h.f i ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary
          (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
            (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
              (.up ℤ)).obj D)).asFunctor)).v i (i - 1) (by omega) = 0) ∧
      (∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
        (t : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
        (x : (P.obj.X i).val.obj U) (y : (D.X i).val.obj (op (n, U.unop))),
        ((f.f i ≫ (CochainComplex.mappingCocone.fst (scalarRoosBoundary
          (((coefficientSequenceRestriction l L X).mapHomologicalComplex
            (.up ℤ)).obj D).asFunctor)).f i ≫
          (Pi.π (fun m : ℕ ↦
            (((coefficientSequenceRestriction l L X).mapHomologicalComplex
              (.up ℤ)).obj D).asFunctor.obj (op m)) n).f i).val.app U)
          (completedScalarTensorSection l E L ι X (P.obj.X i) U t x) =
            integralComparisonRestrictedSection l L X (D.X i) n U y →
        ((h.f i ≫ (CochainComplex.mappingCocone.fst (scalarRoosBoundary
          (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
            (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
              (.up ℤ)).obj D)).asFunctor)).f i ≫
          (Pi.π (fun m : ℕ ↦
            (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
              (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
                (.up ℤ)).obj D)).asFunctor.obj (op m)) n).f i).val.app U)
          (completedScalarTensorSection l L F j X
            (((completedOrdinaryScalarComplex l E L ι X).obj P.obj).X i) U s
            (completedScalarTensorSection l E L ι X (P.obj.X i) U t x)) =
        integralComparisonRestrictedSection l F X
          ((integralComparisonSequenceScalarModel l L F j X).E.obj (D.X i)) n U
          (integralComparisonSequenceTensorSection l L F j X (D.X i)
            (op (n, U.unop))
            ((completedIntegralCommRingProjectionUnrestricted l F X n).hom.app U s) y)) ∧
      (completedDerivedScalarExtension l L F j X).map
          (DerivedCategory.Q.map f ≫ (integralComparisonRoosBridge l L X ρL D).inv) ≫
        (completedScalarComparison l L F j X).app
          ((coefficientSequenceLimit l L X).obj (DerivedCategory.Q.obj D)) ≫
        b.realization.hom.app
          ((coefficientSequenceLimit l L X).obj (DerivedCategory.Q.obj D)) ≫
        (coefficientSequenceLimit l F X).map
          ((integralComparisonDerivedSequenceScalar l L F j X).map
            (SL.adjunction.counit.app (DerivedCategory.Q.obj D))) ≫
        (coefficientSequenceLimit l F X).map
          ((integralComparisonSequenceScalarModel l L F j X).ε.app D) ≫
        (integralComparisonRoosBridge l F X ρF _).hom =
      completedScalarCounit l L F j X
        ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ≫ DerivedCategory.Q.map h := by
  simp only
  obtain ⟨h, hh, hcoord⟩ := scalarModelRoosZeroLift_core
    l E L F ι j X SL ρL ρF b P D f hf
  refine ⟨h, hh, hcoord, ?_⟩
  exact scalarModelRoosZeroLift_factorization_from_coordinates
    l E L F ι j X SL ρL ρF b P D f hf h hh hcoord

end WeilConjectures

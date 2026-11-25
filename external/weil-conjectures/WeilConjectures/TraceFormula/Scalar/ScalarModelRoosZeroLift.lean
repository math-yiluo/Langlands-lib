/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import WeilConjectures.TraceFormula.Scalar.ScalarModelRoosZeroLiftExistence
import WeilConjectures.TraceFormula.Scalar.ScalarModelRoosZeroLiftUniqueness

/-! # Scalar change of a zero-shifted Roos lift

Source: Stacks Project, Tags 06YY and 0941; Bhatt--Scholze, Definition 3.4.10
and Proposition 3.5.1.
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

/-- A normalized scalar realization takes a compatible zero-shifted Roos lift to
its scalar-extended lift. This concerns one coefficient map and an arbitrary target
system, without any scalar associator.

Source: Stacks 06YY, 0941; Bhatt--Scholze, Definition 3.4.10, Proposition 3.5.1;
step 2 of lem-trf-scalar-model-iterated-strict-calculation.
(blueprint: lem-trf-scalar-model-roos-zero-lift).

Proof in words: choose a simultaneous strict quotient presentation of the good
ordinary scalar extension of P using SL.reductionModel. Change of rings
preserves its K-flatness and flat terms. Normalize b on that presentation. Under the
constant-tower/limit adjunction the zero-shifted map f is the compatible family
of its unshifted quotient coordinates: resolve its target tower simultaneously
by a K-injective tower, and apply integralConeCounitRealization to that family.
The formula integralComparisonReductionCounit_formula changes this statement to
the actual SL adjunction, including its whole-system coefficient-action counit.
The chain-map equation for f, together with hf, makes these coordinates a
compatible family commuting with the differential and all quotient transitions.
Each coordinate is linear over the completed L coefficient ring; since the target
at level n is a module over its nth quotient, the extension/restriction adjunction
factors it through that quotient tensor complex. The quotient universal property
makes the factors commute with transitions and differentials. Transport them
through the chosen presentation's evaluation isomorphisms. Thus the transpose of
f factors through the strict quotient presentation of the ordinary L extension
of P by the resulting whole-system morphism. Apply ordinary coefficient extension
and its universal cochain counit. Naturality of b.realization, the universal
counit and the Roos bridge identifies the displayed left side with the Roos
lift of this scalar-extended family, preceded by completedScalarCounit. On a
sheafified nested tensor s tensor (t tensor x) its nth coordinate is the quotient of s tensored
with the nth coordinate of f(t tensor x); this is exactly htensor. Both shifted
coordinates vanish by hf and hg. Tensor balancing and sheafification extend
the generator equations, while product and mapping-cocone extensionality give
equality of the strict chain maps. Localizing proves the formula. The zero
complex and repeated coefficient fields satisfy the same formulas; no
invertibility of a completion map or faithfulness of derived evaluations is used. -/
theorem scalarModelRoosZeroLift
    (SL : CoefficientDerivedSystemCalculus l L X)
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (b : IntegralComparisonScalarModel l L F j X SL ρF)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (f : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor)
    (g : (completedOrdinaryScalarComplex l L F j X).obj
      ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ⟶ integralOperationsRoos
      (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
          (.up ℤ)).obj D)).asFunctor)
    (hf : ∀ i : ℤ, f.f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex
          (.up ℤ)).obj D).asFunctor)).v i (i - 1) (by omega) = 0)
    (hg : ∀ i : ℤ, g.f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary
        (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
          (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
            (.up ℤ)).obj D)).asFunctor)).v i (i - 1) (by omega) = 0)
    (htensor : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
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
      ((g.f i ≫ (CochainComplex.mappingCocone.fst (scalarRoosBoundary
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
        (integralComparisonSequenceTensorSection l L F j X (D.X i) (op (n, U.unop))
          ((completedIntegralCommRingProjectionUnrestricted l F X n).hom.app U s) y)) :
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
      ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ≫ DerivedCategory.Q.map g := by
  obtain ⟨h, hh, hrel, hfactor⟩ :=
    scalarModelRoosZeroLift_existence l E L F ι j X SL ρL ρF b P D f hf
  have hcoord : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
      (x : (P.obj.X i).val.obj U),
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
      ((g.f i ≫ (CochainComplex.mappingCocone.fst (scalarRoosBoundary
        (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
          (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
            (.up ℤ)).obj D)).asFunctor)).f i ≫
        (Pi.π (fun m : ℕ ↦
          (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
            (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
              (.up ℤ)).obj D)).asFunctor.obj (op m)) n).f i).val.app U)
        (completedScalarTensorSection l L F j X
          (((completedOrdinaryScalarComplex l E L ι X).obj P.obj).X i) U s
          (completedScalarTensorSection l E L ι X (P.obj.X i) U t x)) := by
    intro n i U s t x
    let z : (((coefficientSequenceRestriction l L X).obj (D.X i)).obj (op n)).val.obj U :=
      ((f.f i ≫ (CochainComplex.mappingCocone.fst (scalarRoosBoundary
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
          D).asFunctor)).f i ≫
        (Pi.π (fun m : ℕ ↦
          (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
            D).asFunctor.obj (op m)) n).f i).val.app U)
        (completedScalarTensorSection l E L ι X (P.obj.X i) U t x)
    let y : (D.X i).val.obj (op (n, U.unop)) :=
      cast (integralComparisonRestrictedSectionType l L X (D.X i) n U) z
    have hy : integralComparisonRestrictedSection l L X (D.X i) n U y = z := by
      dsimp [y, z]
      simp only [integralComparisonRestrictedSection, cast_cast, cast_eq]
    have hy' : z = integralComparisonRestrictedSection l L X (D.X i) n U y := hy.symm
    have hh' := hrel n i U s t x y hy'
    have hg' := htensor n i U s t x y hy'
    exact hh'.trans hg'.symm
  have hq := scalarModelRoosZeroLift_uniqueness l E L F ι j X P D h g hh hg hcoord
  calc
    _ = completedScalarCounit l L F j X
        ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ≫ DerivedCategory.Q.map h := hfactor
    _ = _ := by rw [hq]

end WeilConjectures

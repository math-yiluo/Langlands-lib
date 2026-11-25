/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

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
open MonoidalCategory AlgebraicGeometry.Scheme
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
  pullbackTensorSequenceDerived integralComparisonDerivedSequencePullback
  pullbackTensorReferencePullback

attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] pullbackTensorCalculus integralDerivedPullback
  integralCompletedTensor coefficientTotalTensor SheafOfModules.monoidalCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory

private def derivedPullBridge {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceDerived l E f ≅ integralComparisonDerivedSequencePullback l E f :=
  Functor.mapDerivedCategoryNatIso (eqToIso (sequencePullback_eq l E f))

private theorem derivedPullBridge_factors {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : StrictQuotient.Complex l E Y) :
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app A ≫
      DerivedCategory.Q.map ((pullBridge l E f).hom.app A) =
      (derivedPullBridge l E f).hom.app (DerivedCategory.Q.obj A) ≫
        (integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app A := by
  unfold pullBridge derivedPullBridge
  exact (Functor.mapDerivedCategoryNatIso_fac
    (eqToIso (sequencePullback_eq l E f)) A).symm

/-- The fixed completed pullback realization transported to the comparison interface.
Source: Stacks 03D2, 0941; quotient scalar-coordinate normalization.
(blueprint: def-pur-completed-quotient-pullback-realization).
The transport is the natural isomorphism on derived categories induced by the
proved equality of the two strict sequence inverse-image functors. -/
def completedQuotientPullbackRealization {X Y : Scheme.{u}} (f : X ⟶ Y) :
    integralDerivedPullback l E f ≅ (pullbackTensorCalculus l E Y).reduction ⋙
      integralComparisonDerivedSequencePullback l E f ⋙ coefficientSequenceLimit l E X :=
  pullbackTensorIntegralPullbackModel l E f ≪≫
    Functor.isoWhiskerLeft (pullbackTensorCalculus l E Y).reduction
      (Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso (eqToIso (sequencePullback_eq l E f)))
        (coefficientSequenceLimit l E X))

/-- Substitution through the transported pullback realization.
Source: quotient scalar-coordinate proof, pullback normalization step.
(blueprint: def-pur-completed-quotient-pullback-realization).
Proof: naturality of the derived transport moves the coherent reduction to its
left. The derived quotient factorization formula then converts its last factor
into the quotient image of the strict bridge; functoriality of total limit gives
the defining formula for pullSubstitution. -/
theorem completedQuotientPullbackRealization_substitution {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : DerivedCategory (scalarReductionSource l E Y)} (A : StrictQuotient.Complex l E Y)
    (β : K ⟶ (coefficientSequenceLimit l E Y).obj (DerivedCategory.Q.obj A)) :
    pullSubstitution l E f A β =
      (completedQuotientPullbackRealization l E f).hom.app K ≫
        (coefficientSequenceLimit l E X).map
          ((integralComparisonDerivedSequencePullback l E f).map (reduction l E β)) ≫
        (coefficientSequenceLimit l E X).map
          ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app A) := by
  let LL := coefficientSequenceLimit l E X
  let b := derivedPullBridge l E f
  unfold pullSubstitution completedQuotientPullbackRealization
  change _ ≫ LL.map _ ≫ LL.map _ =
    (_ ≫ LL.map (b.hom.app ((pullbackTensorCalculus l E Y).reduction.obj K))) ≫
      LL.map _ ≫ LL.map _
  simp only [Category.assoc, ← LL.map_comp]
  rw [← reassoc_of% b.hom.naturality]
  rw [← derivedPullBridge_factors]

end WeilConjectures.CompletedQuotient

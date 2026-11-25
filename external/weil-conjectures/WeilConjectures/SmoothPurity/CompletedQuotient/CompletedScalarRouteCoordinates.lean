/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedScalarStrictSquare
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedScalarLeftCoordinate
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedScalarRightCoordinate

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

/-- The strict scalar square and its two uncancelled substitution coordinates.
Source: Stacks 03EL, 07A4 and 0941; quotient-realization proof steps 6 and 7
(blueprint: lem-pur-completed-scalar-route-coordinates).

Proof: identify the transported strict comparison with the generator-normalized
cochain comparison, using equality of the two chosen inverse-image interfaces
and uniqueness on tensor generators. The strict coefficient square then gives
the first equation: both routes send b tensor (x tensor y) to
(b tensor x) tensor (1 tensor y). This is a chain-system equality, including
all quotient transitions. For the second equation, expand the scalar substitution
at the source and the recursive L substitution at the pullback of the tensor.
The normalized scalar/pullback and scalar/tensor limit squares identify kappa
and sigma with the prescribed completed alpha maps. Naturality moves the leaf
coherent reductions past these comparisons. Applying total limit and its map_comp
law gives the displayed left coordinate. For the third equation use the other
factorization of the strict square: scalar change of c_E followed by sigma_X
and the tensor of the two kappa maps. Expand the E transport and the L target
substitution. The inverse E target substitution cancels its forward factor;
scalar counit naturality identifies the remaining target factors with the
completed tensor scalar comparison and the tensor of completed pullback scalar
comparisons. This gives the right coordinate before cancelling the L target
substitution. The argument never identifies derived maps merely from finite
evaluations, and uses no flatness of finite coefficient maps. -/
theorem completedScalarRouteCoordinates
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
      StrictQuotient.SystemGood l L (strictValue l L (scalarQuotients l E L ι P) A)) :
    (scalarLeft l E L ι f (quotient l E (P 0).obj) (quotient l E (P 1).obj) =
      scalarRight l E L ι f (quotient l E (P 0).obj) (quotient l E (P 1).obj)) ∧
    (scalarSubstitution l E L ι SX
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
          ((scalarQuotients l E L ι P) 1)).hom)) ∧
    (scalarSubstitution l E L ι SX
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
      scalarBeta l E L ι M P φ good SY goodL (targetExpression h f))  := by
  exact ⟨completedScalarStrictSquare l E L ι f
      (quotient l E (P 0).obj) (quotient l E (P 1).obj),
    scalarRouteLeftCoordinate l E L ι h f M P φ good ρX ρY SX SY goodL,
    scalarRouteRightCoordinate l E L ι h f M P φ good invertible ρX ρY SX SY goodL⟩

end WeilConjectures.CompletedQuotient

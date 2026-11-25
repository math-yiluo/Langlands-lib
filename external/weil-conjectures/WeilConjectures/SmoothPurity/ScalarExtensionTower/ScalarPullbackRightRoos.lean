/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarPullbackRoosCoordinates
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarPullbackRightRoosNormalization

/-! # Fixed cochain coordinates for the scalar/pullback calculation

Source: Stacks 06YY, 07A4 and 0941. The coordinates are constructed from the
ordinary scalar/pullback chain map and a coherent quotient presentation.
-/

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

/-- Compute the route using pullback normalization for E and scalar normalization
at X. There is no scalar model at Y or pullback realization with coefficients L.
Source: Stacks 06YY, 07A4, 0941; the right route in realization step 8 of
lem-pur-scalar-extension-tower-coherence.
(blueprint: stage3-pur-scalar-pullback-right-roos).

Proof: first use the E-pullback normalization on C to identify its realization
with the actual strict pullback quotient tower. Transpose through the reduction
adjunction: its coherent counit is precisely pullbackReduction. Resolve this
pulled object by a flat-term K-flat representative and compare its quotient
presentation with the pulled presentation using their whole-system tensor-unit
transposes. Apply SX.normalization on this representative. Naturality of the
scalar cochain counit and of the Roos bridge cancels the resolution comparison.
The scalar/pullback system isomorphism is localized from the strict scalar/unit
association, so its defining cochain equation identifies the output with the
pulled scalar tower. On the nested unit generators q is the same association;
scalarPullbackLevel and its quotient transitions therefore give its strict map.
The zero shifted completion coordinate and scalarRoosMap give exactly
scalarPullbackChain after applying Roos. The scalar completion normalization
then gives the source inverse in scalarPullbackRoosChain. Naturality along eP
transports the result back to K. This calculation involves only SX and the
E-pullback model, and retains entire-system coherence before passing to limits. -/
theorem scalarPullbackRightRoos (W : Bool → Scheme.{u})
    (ME : CompletedOperations.Models.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l L (W true))
    (SX : IntegralComparisonScalarModel.{u, u} l E L ι (W true) (ME.calculus true) ρ)
    (f : W true ⟶ W false)
    (_hX : IsUnit (l : Γ(W true, ⊤))) (_hY : IsUnit (l : Γ(W false, ⊤)))
    (P : (integralOperationsGoodComplex.{u, u} l E (W false)).FullSubcategory)
    (K : sfIntegralConstructibleCategory l E (W false))
    (eP : DerivedCategory.Q.obj P.obj ≅ K.obj)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E (W false)) ℤ)
    (eC : (ME.calculus false).reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E (W false) n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E (W false) n).obj P.obj)
    (hp : CoefficientReductionPresentation.{u, u} l E (W false)
      (ME.calculus false).toCoefficientDerivedSystemReduction P.obj P.property.1 C eC κ)
    (hc : IsIntegralComparisonPresentationCoherent.{u, u} l E (W false)
      (ME.calculus false) P.obj C eC κ)
    (q :
    (((coefficientSequenceRestriction.{u, u} l L (W true)).mapHomologicalComplex (.up ℤ)).obj
      ((((integralComparisonSequencePullback.{u, u} l L f).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel.{u, u} l E L ι (W false)).E.mapHomologicalComplex
          (.up ℤ)).obj C)))).asFunctor ≅
      (integralOperationsPullbackTowerFunctor.{u, u} l L f).obj
        (((integralOrdinaryScalar l E L ι (W false)).mapHomologicalComplex (.up ℤ)).obj P.obj))
    (hq : ScalarPullbackQuotientFormula l E L ι f P C κ q)
    (hF : IsSfDerivedComplete l E (W true)
      ((integralDerivedPullback.{u, u} l E f).obj K.obj)) :
    (SX.realization.hom.app ((integralDerivedPullback.{u, u} l E f).obj K.obj) ≫
      (coefficientSequenceLimit.{u, u} l L (W true)).map
        ((integralComparisonDerivedSequenceScalar.{u, u} l E L ι (W true)).map
          (pullbackReduction l E W ME f K.obj))) ≫
      scalarPullbackRoosCoordinate l E L ι f P C (ME.calculus false) ρ K.obj eP eC q =
    scalarPullbackRoosChain l E L ι f P K.obj eP hF := by
  simpa [scalarPullbackRoosChain, Category.assoc] using
    (scalarPullbackRightRoos_normalized l E L ι W ME ρ SX f _hX _hY P K eP C eC κ hp hc
      q hq hF)

end WeilConjectures.ScalarExtensionTower

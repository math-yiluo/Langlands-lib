/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomSiteBetaRepresentative
public import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomTensorAssociatorModel
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomSiteBetaUnit
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomSiteChainGenerators

/-! # The ordinary scalar/site tensor square before localization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local instance 2000] finiteHomTensorSiteSmall
attribute [local instance] ProEtale.finiteCoefficientIntrinsicMonoidal
  coefficientFiniteQuotientExtensionAdditive
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

-- Keep the fixed ordinary functors abstract while comparing their termwise applications.
attribute [local irreducible] finiteHomEtaleData finiteHomEtaleClosedGeneral
  finiteHomEtaleClosedWitnessRing SheafOfModules.monoidalCategory
  coefficientFiniteQuotientExtension coefficientFiniteQuotientExistence
  coefficientFiniteQuotientDerived coefficientFiniteQuotientDerivedExistence
  ProEtale.etaleSheafExtendScalars ProEtale.finiteCoefficientIntrinsicComparison

/-- The route extending the inverse-image tensor map before applying the mate.
Source: Stacks 07A4; blueprint lemma-change-coefficients-internal-hom--1, final site comparison
(blueprint: lem-coef-finite-hom-site-tensor-chain-equation). -/
@[irreducible] def finiteHomSiteTensorLeftChain
    {n m : ℕ} (h : m ≤ n)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) ℤ)
    (e : (finiteHomTensorExtensionComplex l E X h).obj
        ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
          (integralCoefficientCommRingSheaf l E X n)).obj
            ((finiteHomNuComplex l E X n).obj P, (finiteHomNuComplex l E X n).obj Q)) ≅
      (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X m)).obj
          ((finiteHomTensorExtensionComplex l E X h).obj
            ((finiteHomNuComplex l E X n).obj P),
           (finiteHomTensorExtensionComplex l E X h).obj
            ((finiteHomNuComplex l E X n).obj Q))) :
    (finiteHomTensorExtensionComplex l E X h).obj
        ((finiteHomNuComplex l E X n).obj
          ((finiteHomCochainTensorGeneral _).obj (P, Q))) ⟶
      (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X m)).obj
          ((finiteHomNuComplex l E X m).obj
            (((ProEtale.etaleSheafExtendScalars
                (finiteHomQuotient l E h) X).mapHomologicalComplex (.up ℤ)).obj P),
           (finiteHomNuComplex l E X m).obj
            (((ProEtale.etaleSheafExtendScalars
                (finiteHomQuotient l E h) X).mapHomologicalComplex (.up ℤ)).obj Q)) :=
  (finiteHomTensorExtensionComplex l E X h).map
        (finiteHomNuChainTensor l E X n P Q).hom ≫ e.hom ≫
      (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X m)).map
          (Prod.mkHom
            ((NatTrans.mapHomologicalComplex (finiteHomSiteOrdinaryBeta l E X h)
              (.up ℤ)).app P)
            ((NatTrans.mapHomologicalComplex (finiteHomSiteOrdinaryBeta l E X h)
              (.up ℤ)).app Q))

-- Keep the concrete termwise and total tensor models in one definition.
/-- The route applying the mate before the etale scalar and site tensor maps.
Source: Stacks 07A4; blueprint lemma-change-coefficients-internal-hom--1, final site comparison
(blueprint: lem-coef-finite-hom-site-tensor-chain-equation). -/
@[irreducible] def finiteHomSiteTensorRightChain
    {n m : ℕ} (h : m ≤ n)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) ℤ) :
    (finiteHomTensorExtensionComplex l E X h).obj
        ((finiteHomNuComplex l E X n).obj
          ((finiteHomCochainTensorGeneral _).obj (P, Q))) ⟶
      (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X m)).obj
          ((finiteHomNuComplex l E X m).obj
            (((ProEtale.etaleSheafExtendScalars
                (finiteHomQuotient l E h) X).mapHomologicalComplex (.up ℤ)).obj P),
           (finiteHomNuComplex l E X m).obj
            (((ProEtale.etaleSheafExtendScalars
                (finiteHomQuotient l E h) X).mapHomologicalComplex (.up ℤ)).obj Q)) := by
  let F := ProEtale.etaleSheafExtendScalars (finiteHomQuotient l E h) X
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let T : Fc.obj ((finiteHomCochainTensorGeneral _).obj (P, Q)) ⟶
      (finiteHomCochainTensorGeneral _).obj (Fc.obj P, Fc.obj Q) :=
    HomologicalComplex.mapBifunctorComparison (Functor.OplaxMonoidal.δNatTrans F)
      (.up ℤ) P Q
  exact (NatTrans.mapHomologicalComplex (finiteHomSiteOrdinaryBeta l E X h)
      (.up ℤ)).app ((finiteHomCochainTensorGeneral _).obj (P, Q)) ≫
    (finiteHomNuComplex l E X m).map T ≫
    (finiteHomNuChainTensor l E X m (Fc.obj P) (Fc.obj Q)).hom

-- The adjunction and pure-section reduction crosses the concrete tensor models.
/-- Balanced scalar association commutes with the ordinary site tensor comparison.
Source: Stacks 03EK, 06YN, 07A4; blueprint lemma-change-coefficients-internal-hom--1, final site
paragraph (blueprint: lem-coef-finite-hom-site-tensor-chain-equation).

Proof: in each total degree transpose the two maps by the ordinary scalar
adjunction. Extensionality for the inverse image of a tensor reduces their
transposes to inverse images of pure tensors in individual total summands.
Naturality moves the scalar unit and the inverse-image section past the summand
inclusions. The chain comparison normalization sends the latter to intrinsic
pure total generators. The assumed normalization of e sends the scalar unit
of each such generator to the tensor of the scalar units of its factors.
The mate unit formula sends each of those units to the inverse image of the
etale scalar unit. On the other route the ordinary etale scalar tensorator
sends the scalar unit of a pure total generator to the corresponding generator
of the two scalar units, by the monoidal adjunction unit equation. The site
chain tensorator then gives exactly the same intrinsic generator. Injectivity
of the scalar adjunction, tensor extensionality and total-summand extensionality
conclude. Neither K-flatness nor invertibility of the mate is used. -/
theorem finiteHomSiteTensorChainEquation
    {n m : ℕ} (h : m ≤ n)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) ℤ)
    (e : (finiteHomTensorExtensionComplex l E X h).obj
        ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
          (integralCoefficientCommRingSheaf l E X n)).obj
            ((finiteHomNuComplex l E X n).obj P, (finiteHomNuComplex l E X n).obj Q)) ≅
      (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X m)).obj
          ((finiteHomTensorExtensionComplex l E X h).obj
            ((finiteHomNuComplex l E X n).obj P),
           (finiteHomTensorExtensionComplex l E X h).obj
            ((finiteHomNuComplex l E X n).obj Q)))
    (he : CoefficientScalarTensorGenerators.{u, u + 1, u} (Scheme.ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X n)
      (integralCoefficientCommRingSheaf l E X m)
      (coefficientFiniteQuotientExtension l E X h)
      (hF := coefficientFiniteQuotientExtensionAdditive.{u, u} l E X h)
      (coefficientFiniteQuotientUnitSection l E X h)
      ((finiteHomNuComplex l E X n).obj P) ((finiteHomNuComplex l E X n).obj Q) e) :
    finiteHomSiteTensorLeftChain l E X h P Q e =
      finiteHomSiteTensorRightChain l E X h P Q := by sorry

end WeilConjectures

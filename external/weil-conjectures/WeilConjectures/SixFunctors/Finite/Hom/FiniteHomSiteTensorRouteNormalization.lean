/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomSiteTensorChainEquation

/-! # Localization of the two finite scalar/site tensor routes -/

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
attribute [local instance] coefficientFiniteQuotientExtensionAdditive

/-- The two derived tensor routes have their specified ordinary chain models.
Source: Stacks 06YN, 06YY, 07A4, 07A6; blueprint lemma-change-coefficients-internal-hom--1, final
site-comparison paragraph
(blueprint: lem-coef-finite-hom-site-tensor-route-normalization).

Proof: take e and its generator equation from quotientCalculus.tensor_model on
nu(P), nu(Q). Reflect their K-flatness to the etale site. Use the etale K-flat
tensor presentation and nu's chain tensor isomorphism to identify the total
source with the etale derived tensor. The scalar counit on this K-flat total
and finiteHomNuFactors give the source isomorphism s. Identify the encoded ordinary
mate with the proved fixed-ring ordinary scalar
mate (ordinary_scalar_mate_isIso); the encoding mates are invertible because
the encodings are equivalences. Transfer invertibility back to the intrinsic
ordinary mate. Scalar extension preserves the
intrinsic K-flat models, so the reduced inverse-image complexes are K-flat.
Their intrinsic tensor model comparison, the etale scalar representative maps,
and finiteHomNuFactors give the target isomorphism t. These are comparison
isomorphisms of actual complexes, not arbitrary identifications of objects.
For the first displayed equation substitute nu's tensor normalization at P,Q,
quotientCalculus.tensor_model, and the single-representative mate formula at P
and Q. Naturality moves finiteHomNuFactors through the tensor maps, leaving
the localization of the first chain route. For the second equation substitute
the single-representative mate formula on the total tensor, the all-complex
etale scalar tensor normalization, and nu's tensor normalization on the two
reduced complexes. Functoriality then gives the localization of the second
chain route. Cancel only the counits and tensor-model comparisons already
proved invertible on these K-flat complexes. This proof does not assert that
the two ordinary routes agree; that is the separate chain-equation lemma.
The same computations include identity quotients, zero complexes and empty sites. -/
theorem finiteHomSiteTensorRouteNormalization
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    {n m : ℕ} (h : m ≤ n)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) ℤ)
    (hP : finiteHomKFlat l E X n P) (hQ : finiteHomKFlat l E X n Q) :
    let A := (finiteHomEtaleClosed l E X n).tensor
    let D := (finiteIntrinsicClosed l E X m).tensor
    let F := finiteHomEtaleReduction l E X h
    let G := coefficientFiniteQuotientDerived l E X h
    let U := finiteHomNu l E X n
    let V := finiteHomNu l E X m
    let qp := (finiteHomEtaleQ l E X n).obj P
    let qq := (finiteHomEtaleQ l E X n).obj Q
    ∃ e : (finiteHomTensorExtensionComplex l E X h).obj
        ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
          (integralCoefficientCommRingSheaf l E X n)).obj
            ((finiteHomNuComplex l E X n).obj P, (finiteHomNuComplex l E X n).obj Q)) ≅
      (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X m)).obj
          ((finiteHomTensorExtensionComplex l E X h).obj
            ((finiteHomNuComplex l E X n).obj P),
           (finiteHomTensorExtensionComplex l E X h).obj
            ((finiteHomNuComplex l E X n).obj Q)),
      CoefficientScalarTensorGenerators.{u, u + 1, u} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)
        (integralCoefficientCommRingSheaf l E X m)
        (coefficientFiniteQuotientExtension l E X h)
        (hF := coefficientFiniteQuotientExtensionAdditive.{u, u} l E X h)
        (coefficientFiniteQuotientUnitSection l E X h)
        ((finiteHomNuComplex l E X n).obj P) ((finiteHomNuComplex l E X n).obj Q) e ∧
      ∃ (s : (finiteHomIntrinsicQ l E X m).obj
          ((finiteHomTensorExtensionComplex l E X h).obj
            ((finiteHomNuComplex l E X n).obj
              ((finiteHomCochainTensorGeneral _).obj (P, Q)))) ≅
            G.obj (U.obj (A.obj (qp, qq))))
        (t : D.obj (V.obj (F.obj qp), V.obj (F.obj qq)) ≅
          (finiteHomIntrinsicQ l E X m).obj
            ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
              (integralCoefficientCommRingSheaf l E X m)).obj
                ((finiteHomNuComplex l E X m).obj
                  (((ProEtale.etaleSheafExtendScalars
                      (finiteHomQuotient l E h) X).mapHomologicalComplex (.up ℤ)).obj P),
                 (finiteHomNuComplex l E X m).obj
                  (((ProEtale.etaleSheafExtendScalars
                      (finiteHomQuotient l E h) X).mapHomologicalComplex (.up ℤ)).obj Q)))),
        s.hom ≫
          (G.map ((finiteHomNuTensor l E X n).hom.app (qp, qq)) ≫
            (coefFiniteHomProTensor l E X h).hom.app (U.obj qp, U.obj qq) ≫
            D.map (Prod.mkHom ((finiteHomSiteBeta l E X h).app qp)
              ((finiteHomSiteBeta l E X h).app qq))) ≫ t.hom =
          (finiteHomIntrinsicQ l E X m).map
            (finiteHomSiteTensorLeftChain l E X h P Q e) ∧
        s.hom ≫
          ((finiteHomSiteBeta l E X h).app (A.obj (qp, qq)) ≫
            V.map ((finiteHomEtaleTensor l E X h).hom.app (qp, qq)) ≫
            (finiteHomNuTensor l E X m).hom.app (F.obj qp, F.obj qq)) ≫ t.hom =
          (finiteHomIntrinsicQ l E X m).map
            (finiteHomSiteTensorRightChain l E X h P Q) := by sorry

end WeilConjectures

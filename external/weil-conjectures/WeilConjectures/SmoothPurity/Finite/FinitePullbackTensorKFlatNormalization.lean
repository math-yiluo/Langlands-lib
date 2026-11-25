/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorChainGenerators
import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorKFlatTransport

/-! # Intrinsic pullback tensor normalization on K-flat complexes

Source: Stacks Tags 03EL, 06YY and 07A4.
(blueprint: lem-pur-finite-pullback-tensor-kflat-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open MonoidalCategory TensorProduct
namespace WeilConjectures
attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.mapDerivedCategory finitePullbackTensorConstruction
  coefficientFiniteQuotientDerived coefficientFiniteQuotientModel
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] SheafOfModules.monoidalCategory
  proEtaleTensorPullbackTotalIso CategoryTheory.Functor.mapBifunctorHomologicalComplex
  HomologicalComplex₂.total
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local instance] sfIntrinsicPullback_additive
  coefficientFiniteQuotientExtensionAdditive pullbackTensorCoefficientFinite
  SheafOfModules.monoidalCategory

/-- The total pullback tensor comparison sends inverse-image unit generators to tensors
of inverse-image unit generators. Source: Stacks 03EL and 07A4
(blueprint: lem-pur-finite-pullback-tensor-kflat-normalization). -/
def FinitePullbackTensorGenerators {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ)
    (k : ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
      (.up ℤ)).obj
          ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y)
            (integralCoefficientCommRingSheaf l E Y n)).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)).obj
          (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
            (.up ℤ)).obj P,
           ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
             (.up ℤ)).obj Q)) : Prop :=
  ∀ (p q i : ℤ) (hpq : p + q = i) (U : Y.ProEt)
    (x : (P.X p).val.obj (op U)) (y : (Q.X q).val.obj (op U)),
    (k.hom.f i).val.app (op ((proEtaleBaseChange f).obj U))
      (((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).unit.app
          (((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y)
            (integralCoefficientCommRingSheaf l E Y n)).obj (P, Q)).X i)).val.app (op U)
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
          (integralCoefficientCommRingSheaf l E Y n) P Q p q i hpq (op U) x y)) =
    coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X n)
      (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
        (.up ℤ)).obj P)
      (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
        (.up ℤ)).obj Q) p q i hpq
      (op ((proEtaleBaseChange f).obj U))
      (((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).unit.app (P.X p)).val.app (op U) x)
      (((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).unit.app (Q.X q)).val.app (op U) y)

/-- Intrinsic pullback tensor normalization on K-flat complexes.
Source: Stacks 07A4, proof of lemma-pullback-tensor-product, and 06YY
(blueprint: lem-pur-finite-pullback-tensor-kflat-normalization).
Proof: take the direct-sum total of the inverse of the ordinary tensor pullback
comparison, transported through the unit-normalized finite realization. On each
bidegree its map sends the unit of x tensor y to the tensor of the two units.
Coproduct preservation and the ordinary comparison give a chain isomorphism,
including the signed differentials. For flat-term K-flat inputs the defining
square of proEtaleCanonicalTensorPullback, conjugated by the finite realization
and finite tensor model isomorphisms, is the displayed square. For arbitrary
K-flat inputs choose flat-term K-flat resolutions. Their maps are quasi-isomorphisms;
tensoring with K-flat complexes and exact pullback preserve them. Naturality of
the total comparison and the tensor models transports the flat-term square along
these invertible localized resolution maps. The resulting formula uses the
prescribed coefficient tensor models, not newly chosen model maps. -/
theorem finitePullbackTensor_kflat_normalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E Y n) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E Y n) Q)
    (hFP : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E X n)
      (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
        (.up ℤ)).obj P))
    (hFQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E X n)
      (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
        (.up ℤ)).obj Q)) :
    ∃ k : ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
      (.up ℤ)).obj
          ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y)
            (integralCoefficientCommRingSheaf l E Y n)).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)).obj
          (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
            (.up ℤ)).obj P,
           ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
             (.up ℤ)).obj Q),
      FinitePullbackTensorGenerators l E f n P Q k ∧
      (finiteDerivedPullback l E n f).map
          (coefficientFiniteTensorModelIso l E Y
            (pullbackTensorCalculus l E Y).toCoefficientDerivedSystemTensors n P Q hP hQ).hom ≫
        ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY)
          (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
        (finiteIntrinsicDerivedTensor l E X n).map
          (Prod.mkHom
            ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1))
              f).mapDerivedCategoryFactors.hom.app P)
            ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1))
              f).mapDerivedCategoryFactors.hom.app Q)) =
      (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1))
        f).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map k.hom ≫
        (coefficientFiniteTensorModelIso l E X
          (pullbackTensorCalculus l E X).toCoefficientDerivedSystemTensors
          n _ _ hFP hFQ).hom := by
  refine ⟨finitePullbackTensorChainIso l E f n P Q,
    finitePullbackTensorChain_generators l E f n P Q, ?_⟩
  exact finitePullbackTensor_intrinsic_kflat_square l E f n P Q hP hQ hFP hFQ

end WeilConjectures

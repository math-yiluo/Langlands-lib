/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import all Mathlib.CategoryTheory.Limits.HasLimits

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarFiniteReductionMaps

/-! # Normalized scalar chain maps on finite tensor levels

Source: Stacks, Modules on Sites, Tags 03CZ and 03EL.
(blueprint: lem-pur-integral-scalar-tensor-chain-construction).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection integralCompletedScalarMap
attribute [-instance] scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] integralOperationsSiteSmall
attribute [local instance 3000] integralTowerHasDerivedCategory

attribute [local instance 50000] hasSheafCompose_of_preservesLimitsOfSize

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u+1} W.ProEt := essentiallySmallSelf.{0, u, u+1} _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsCommHasDerivedCategory
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} W

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{u+1} := integralCoefficientAbLocallyBijective.{u, u} W

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] limit scalarAdjunction
  reductionScalarAdjunction finiteScalarModule TensorChainProof.map

private def tensorScalarAdjunct (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    (integralOperationsTensorLevel l E W n).obj (P, Q) ⟶
      ((CategoryTheory.CochainPullback.restrictionFunctor
        (integralCompletedScalarMap l E L ι W)).mapHomologicalComplex (.up ℤ)).obj
        ((integralOperationsTensorLevel l L W n).obj
          ((((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P),
            (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q))) :=
  SheafOfModules.IntegralScalarProof.restrictComplexMap
    (integralOperationsProjection l E W n)
    ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (integralCompletedScalarMap l E L ι W) ≫ integralOperationsProjection l L W n)
    (scalarFiniteRingMap l E L ι W n) (scalarProjectionRingSquare l E L ι W n)
    (TensorChainProof.map (integralCoefficientCommRingSheaf l E W n)
      (integralCoefficientCommRingSheaf l L W n)
      (integralScalarQuotientSheafMap l E L ι W n)
      (finiteScalarComplex l E L ι W n P) (finiteScalarComplex l E L ι W n Q))

private def tensorScalarChain (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj
        ((integralOperationsTensorLevel l E W n).obj (P, Q)) ⟶
      (integralOperationsTensorLevel l L W n).obj
        ((((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P),
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q)) :=
  (((scalarAdjunction l E L ι W).mapHomologicalComplex (.up ℤ)).homEquiv _ _).symm
    (tensorScalarAdjunct l E L ι W n P Q)

private theorem tensorScalarChain_unit (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ)
    (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((tensorScalarChain l E L ι W n P Q).f (p + q)).val.app U
        (integralOrdinaryTensorSection l E L ι W
          (((integralOperationsTensorLevel l E W n).obj (P, Q)).X (p + q)) U 1
          (integralOperationsTotalTensorSection l E W n P Q p q U
            (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
            (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y))) =
      integralOperationsTotalTensorSection l L W n
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P)
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q) p q U
        (unrestrictedIntegralTensorSection l L W n
          ((integralOrdinaryScalar l E L ι W).obj (P.X p)) U 1
          (integralOrdinaryTensorSection l E L ι W (P.X p) U 1 x))
        (unrestrictedIntegralTensorSection l L W n
          ((integralOrdinaryScalar l E L ι W).obj (Q.X q)) U 1
          (integralOrdinaryTensorSection l E L ι W (Q.X q) U 1 y)) := by
  let z := integralOperationsTotalTensorSection l E W n P Q p q U
    (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
    (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y)
  have h0 := (((scalarAdjunction l E L ι W).mapHomologicalComplex (.up ℤ)).homEquiv
    _ _).apply_symm_apply (tensorScalarAdjunct l E L ι W n P Q)
  have h := congrArg (fun t ↦ (t.f (p + q)).val.app U z) h0
  change ((tensorScalarChain l E L ι W n P Q).f (p + q)).val.app U
      (((scalarAdjunction l E L ι W).unit.app
        (((integralOperationsTensorLevel l E W n).obj (P, Q)).X (p + q))).val.app U z) =
    ((tensorScalarAdjunct l E L ι W n P Q).f (p + q)).val.app U z at h
  refine (congrArg (((tensorScalarChain l E L ι W n P Q).f (p + q)).val.app U)
    (scalarAdjunction_unit l E L ι W
      (((integralOperationsTensorLevel l E W n).obj (P, Q)).X (p + q)) U z).symm).trans (h.trans ?_)
  have hp := TensorChainProof.pure
    (integralCoefficientCommRingSheaf l E W n) (integralCoefficientCommRingSheaf l L W n)
    (integralScalarQuotientSheafMap l E L ι W n)
    (finiteScalarComplex l E L ι W n P) (finiteScalarComplex l E L ι W n Q) p q U
    (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
    (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y)
  have he := TensorChainProof.totalPure_eq (integralCoefficientCommRingSheaf l E W n)
    (P := (unrestrictedIntegralFiniteComplex l E W n).obj P)
    (Q := (unrestrictedIntegralFiniteComplex l E W n).obj Q) p q U
    (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
    (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y)
  have hl := TensorChainProof.totalPure_eq (integralCoefficientCommRingSheaf l L W n)
    (P := (unrestrictedIntegralFiniteComplex l L W n).obj
      (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P))
    (Q := (unrestrictedIntegralFiniteComplex l L W n).obj
      (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q)) p q U
    ((finiteScalarModule l E L ι W n (P.X p)).val.app U
      (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x))
    ((finiteScalarModule l E L ι W n (Q.X q)).val.app U
      (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y))
  have hp' := (congrArg
    (((TensorChainProof.map (integralCoefficientCommRingSheaf l E W n)
      (integralCoefficientCommRingSheaf l L W n)
      (integralScalarQuotientSheafMap l E L ι W n)
      (finiteScalarComplex l E L ι W n P) (finiteScalarComplex l E L ι W n Q)).f
        (p + q)).val.app U) he.symm).trans (hp.trans hl)
  have hp'' : ((tensorScalarAdjunct l E L ι W n P Q).f (p + q)).val.app U z =
      integralOperationsTotalTensorSection l L W n
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P)
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q) p q U
        ((finiteScalarModule l E L ι W n (P.X p)).val.app U
          (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x))
        ((finiteScalarModule l E L ι W n (Q.X q)).val.app U
          (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y)) := by
    convert hp' using 1
    rfl
  exact hp''.trans (congrArg₂ (integralOperationsTotalTensorSection l L W n
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P)
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q) p q U)
    (finiteScalarModule_unit l E L ι W n (P.X p) U x)
    (finiteScalarModule_unit l E L ι W n (Q.X q) U y))

end WeilConjectures

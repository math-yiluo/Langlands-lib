/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement

/-! # Normalized maps between finite scalar reductions

Source: Stacks, Modules on Sites, Tags 03CZ and 03EL.
(blueprint: lem-pur-integral-scalar-finite-reduction-unit-map).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
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

private theorem scalarProjectionSquare (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    completedIntegralCommRingProjectionUnrestricted l E W n ≫
        integralScalarQuotientSheafMap l E L ι W n =
      integralCompletedScalarMap l E L ι W ≫
        completedIntegralCommRingProjectionUnrestricted l L W n := by
  simpa only [integralCompletedScalarMap, integralScalarRho] using
    ((integralCompletedScalarMap_existsUnique l E L ι W).exists.choose_spec n).symm

private abbrev scalarFiniteRingMap (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :=
  (sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (integralScalarQuotientSheafMap l E L ι W n)

private def reductionScalarAdjunction (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :=
  (CategoryTheory.CochainPullback.extensionAdjunction
    (completedIntegralCommRingProjectionUnrestricted l E W n)).ofNatIsoLeft
      (tensorPresentation (completedIntegralCommRingProjectionUnrestricted l E W n)
        (unrestrictedIntegralReductionFunctor l E W n)
        (unrestrictedReduction_obj l E W n)
        (fun a ↦ unrestrictedReduction_map l E W n a)).symm

private theorem reductionScalarAdjunction_unit (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((reductionScalarAdjunction l E W n).unit.app M).val.app U x =
      unrestrictedIntegralTensorSection l E W n M U 1 x := by
  exact tensorAdjunction_unit (completedIntegralCommRingProjectionUnrestricted l E W n)
    (unrestrictedIntegralReductionFunctor l E W n)
    (unrestrictedReduction_obj l E W n) (fun a ↦ unrestrictedReduction_map l E W n a) M U x

attribute [local irreducible] reductionScalarAdjunction

private def finiteScalarModule (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (M : integralTowerModules l E W) :
    (unrestrictedIntegralReductionFunctor l E W n).obj M ⟶
      (SheafOfModules.restrictScalars (scalarFiniteRingMap l E L ι W n)).obj
        ((unrestrictedIntegralReductionFunctor l L W n).obj
          ((integralOrdinaryScalar l E L ι W).obj M)) := by
  let a := completedIntegralCommRingProjectionUnrestricted l E W n
  let b := completedIntegralCommRingProjectionUnrestricted l L W n
  let j := integralCompletedScalarMap l E L ι W
  let k := integralScalarQuotientSheafMap l E L ι W n
  let N := (unrestrictedIntegralReductionFunctor l L W n).obj
    ((integralOrdinaryScalar l E L ι W).obj M)
  let e := restrictionCompIso j b (a ≫ k) (scalarProjectionSquare l E L ι W n).symm
  let e' := restrictionCompIso a k (a ≫ k) rfl
  exact ((reductionScalarAdjunction l E W n).homEquiv M _).symm
    ((scalarAdjunction l E L ι W).unit.app M ≫
      (CategoryTheory.CochainPullback.restrictionFunctor j).map
        ((reductionScalarAdjunction l L W n).unit.app
          ((integralOrdinaryScalar l E L ι W).obj M)) ≫ e.hom.app N ≫ e'.inv.app N)

private theorem finiteScalarModule_unit (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    (finiteScalarModule l E L ι W n M).val.app U
        (unrestrictedIntegralTensorSection l E W n M U 1 x) =
      unrestrictedIntegralTensorSection l L W n
        ((integralOrdinaryScalar l E L ι W).obj M) U 1
        (integralOrdinaryTensorSection l E L ι W M U 1 x) := by
  have h := ((reductionScalarAdjunction l E W n).homEquiv _ _).apply_symm_apply
    ((scalarAdjunction l E L ι W).unit.app M ≫
      (CategoryTheory.CochainPullback.restrictionFunctor
        (integralCompletedScalarMap l E L ι W)).map
        ((reductionScalarAdjunction l L W n).unit.app
          ((integralOrdinaryScalar l E L ι W).obj M)) ≫
      (restrictionCompIso (integralCompletedScalarMap l E L ι W)
        (completedIntegralCommRingProjectionUnrestricted l L W n)
        (completedIntegralCommRingProjectionUnrestricted l E W n ≫
          integralScalarQuotientSheafMap l E L ι W n)
        (scalarProjectionSquare l E L ι W n).symm).hom.app _ ≫
      (restrictionCompIso (completedIntegralCommRingProjectionUnrestricted l E W n)
        (integralScalarQuotientSheafMap l E L ι W n) _ rfl).inv.app _)
  have h' := congrArg (fun t ↦ t.val.app U x) h
  change (finiteScalarModule l E L ι W n M).val.app U
    (((reductionScalarAdjunction l E W n).unit.app M).val.app U x) =
      ((reductionScalarAdjunction l L W n).unit.app _).val.app U
        (((scalarAdjunction l E L ι W).unit.app M).val.app U x) at h'
  exact (congrArg ((finiteScalarModule l E L ι W n M).val.app U)
    (reductionScalarAdjunction_unit l E W n M U x).symm).trans
    (h'.trans ((reductionScalarAdjunction_unit l L W n _ U _).trans
      (congrArg (unrestrictedIntegralTensorSection l L W n _ U 1)
        (scalarAdjunction_unit l E L ι W M U x))))

attribute [local irreducible] finiteScalarModule

private theorem reductionScalarMap_tensor (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    {M N : integralTowerModules l E W} (a : M ⟶ N) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((unrestrictedIntegralReductionFunctor l E W n).map a).val.app U
        (unrestrictedIntegralTensorSection l E W n M U 1 x) =
      unrestrictedIntegralTensorSection l E W n N U 1 (a.val.app U x) :=
  tensorSection_map (completedIntegralCommRingProjectionUnrestricted l E W n)
    (unrestrictedIntegralReductionFunctor l E W n) (unrestrictedReduction_obj l E W n)
    (fun a ↦ unrestrictedReduction_map l E W n a) a U 1 x

private theorem finiteScalarModule_naturality (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    {M N : integralTowerModules l E W} (a : M ⟶ N) :
    (unrestrictedIntegralReductionFunctor l E W n).map a ≫ finiteScalarModule l E L ι W n N =
      finiteScalarModule l E L ι W n M ≫
        (SheafOfModules.restrictScalars (scalarFiniteRingMap l E L ι W n)).map
          ((unrestrictedIntegralReductionFunctor l L W n).map
            ((integralOrdinaryScalar l E L ι W).map a)) := by
  apply tensorSection_ext (completedIntegralCommRingProjectionUnrestricted l E W n)
    (unrestrictedIntegralReductionFunctor l E W n) (unrestrictedReduction_obj l E W n)
  intro U x
  change (finiteScalarModule l E L ι W n N).val.app U
      (((unrestrictedIntegralReductionFunctor l E W n).map a).val.app U
        (unrestrictedIntegralTensorSection l E W n M U 1 x)) =
    ((unrestrictedIntegralReductionFunctor l L W n).map
      ((integralOrdinaryScalar l E L ι W).map a)).val.app U
        ((finiteScalarModule l E L ι W n M).val.app U
          (unrestrictedIntegralTensorSection l E W n M U 1 x))
  erw [reductionScalarMap_tensor, finiteScalarModule_unit, finiteScalarModule_unit,
    reductionScalarMap_tensor, scalar_map_tensor]

private def finiteScalarComplex (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E W) ℤ) :
    (unrestrictedIntegralFiniteComplex l E W n).obj P ⟶
      (integralOperationsRestrictionComplex (scalarFiniteRingMap l E L ι W n)).obj
        ((unrestrictedIntegralFiniteComplex l L W n).obj
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P)) where
  f i := finiteScalarModule l E L ι W n (P.X i)
  comm' i j _ := (finiteScalarModule_naturality l E L ι W n (P.d i j)).symm

private def finiteScalarTransformation (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    unrestrictedIntegralFiniteComplex l E W n ⟶
      (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ) ⋙
        unrestrictedIntegralFiniteComplex l L W n ⋙
          integralOperationsRestrictionComplex (scalarFiniteRingMap l E L ι W n) where
  app := finiteScalarComplex l E L ι W n
  naturality _P _Q a := HomologicalComplex.hom_ext _ _
    (fun i ↦ finiteScalarModule_naturality l E L ι W n (a.f i))

private theorem scalarProjectionRingSquare (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    integralOperationsProjection l E W n ≫ scalarFiniteRingMap l E L ι W n =
      (sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralCompletedScalarMap l E L ι W) ≫ integralOperationsProjection l L W n := by
  let c := sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  exact (c.map_comp _ _).symm.trans
    ((congrArg c.map (scalarProjectionSquare l E L ι W n)).trans (c.map_comp _ _))

end WeilConjectures

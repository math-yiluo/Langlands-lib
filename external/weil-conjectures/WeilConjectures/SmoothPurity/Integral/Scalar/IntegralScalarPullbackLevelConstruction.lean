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
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarFiniteReductionMaps
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackLevelReduction

/-! # Construction of the finite scalar pullback map

Source: Stacks, Modules on Sites, Tags 03CZ and 03EL.
(blueprint: lem-pur-integral-scalar-pullback-level-construction).
-/

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
  reductionScalarAdjunction finiteScalarModule

private theorem finiteScalarPullbackSquare {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    scalarFiniteRingMap l E L ι Y n ≫ integralOperationsDirectRingMap l L f n =
      integralOperationsDirectRingMap l E f n ≫
        ((integralOperationsBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
          (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (AlgebraicGeometry.Scheme.ProEt.topology X)).map
            (scalarFiniteRingMap l E L ι X n) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  exact congrArg (fun k ↦ (integralOperationsRingForget).map (k.hom.app V))
    (AlgebraicGeometry.Scheme.directRingMap_naturality.{u, u} f
      (CommRingCat.ofHom
        ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
          ((integralScalarQuotientMap l E L ι n).comp
            (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom))))

private abbrev pullbackModuleFunctor {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) : integralTowerModules l E Y ⥤ integralTowerModules l E X :=
  unrestrictedIntegralReductionFunctor l E Y n ⋙ integralOperationsLevelPullback l E f n ⋙
    SheafOfModules.restrictScalars (integralOperationsProjection l E X n)

private def pullbackFiniteScalarModule {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) (M : integralTowerModules l E Y) :=
  SheafOfModules.IntegralPullbackProof.mateData (integralOperationsBaseChange f)
    (scalarFiniteRingMap l E L ι X n) (scalarFiniteRingMap l E L ι Y n)
    (integralOperationsDirectRingMap l E f n) (integralOperationsDirectRingMap l L f n)
    (finiteScalarPullbackSquare l E L ι f n)
    (integralOperationsPullbackAdjunction l E f n)
    (integralOperationsPullbackAdjunction l L f n)
    (finiteScalarModule l E L ι Y n M)

private def pullbackScalarAdjunct {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) (M : integralTowerModules l E Y) :
    (pullbackModuleFunctor l E f n).obj M ⟶
      (CategoryTheory.CochainPullback.restrictionFunctor
        (integralCompletedScalarMap l E L ι X)).obj
        ((pullbackModuleFunctor l L f n).obj ((integralOrdinaryScalar l E L ι Y).obj M)) := by
  let c := sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let j := integralCompletedScalarMap l E L ι X
  let b := completedIntegralCommRingProjectionUnrestricted l L X n
  have h : integralOperationsProjection l E X n ≫ scalarFiniteRingMap l E L ι X n =
      c.map (j ≫ b) :=
    (c.map_comp _ _).symm.trans (congrArg c.map (scalarProjectionSquare l E L ι X n))
  exact SheafOfModules.IntegralScalarProof.restrictMap
    (integralOperationsProjection l E X n) (c.map (j ≫ b))
    (scalarFiniteRingMap l E L ι X n) h _ _ (pullbackFiniteScalarModule l E L ι f n M) ≫
      (restrictionCompIso j b (j ≫ b) rfl).inv.app _

private def pullbackScalarModule {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) (M : integralTowerModules l E Y) :
    (integralOrdinaryScalar l E L ι X).obj ((pullbackModuleFunctor l E f n).obj M) ⟶
      (pullbackModuleFunctor l L f n).obj ((integralOrdinaryScalar l E L ι Y).obj M) :=
  ((scalarAdjunction l E L ι X).homEquiv _ _).symm
    (pullbackScalarAdjunct l E L ι f n M)

private theorem pullbackScalarModule_unit {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) (M : integralTowerModules l E Y)
    (V : Y.ProEt) (x : M.val.obj (op V)) :
    (pullbackScalarModule l E L ι f n M).val.app
        (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
        (integralOrdinaryTensorSection l E L ι X _ _ 1
          (integralOperationsPullbackGenerator l E f n _ V
            (unrestrictedIntegralTensorSection l E Y n M (op V) 1 x))) =
      integralOperationsPullbackGenerator l L f n _ V
        (unrestrictedIntegralTensorSection l L Y n
          ((integralOrdinaryScalar l E L ι Y).obj M) (op V) 1
          (integralOrdinaryTensorSection l E L ι Y M (op V) 1 x)) := by
  have h := ((scalarAdjunction l E L ι X).homEquiv _ _).apply_symm_apply
    (pullbackScalarAdjunct l E L ι f n M)
  have h' := congrArg (fun t ↦ t.val.app
    (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
    (integralOperationsPullbackGenerator l E f n _ V
      (unrestrictedIntegralTensorSection l E Y n M (op V) 1 x))) h
  change (pullbackScalarModule l E L ι f n M).val.app _
    (((scalarAdjunction l E L ι X).unit.app _).val.app _ _) =
      (pullbackFiniteScalarModule l E L ι f n M).val.app _ _ at h'
  have hs := scalarAdjunction_unit l E L ι X
    ((pullbackModuleFunctor l E f n).obj M)
    (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
    (integralOperationsPullbackGenerator l E f n _ V
      (unrestrictedIntegralTensorSection l E Y n M (op V) 1 x))
  refine (congrArg ((pullbackScalarModule l E L ι f n M).val.app _) hs.symm).trans
    (h'.trans ?_)
  change (pullbackFiniteScalarModule l E L ι f n M).val.app _
      (SheafOfModules.IntegralPullbackProof.unitSection (integralOperationsBaseChange f)
        (integralOperationsDirectRingMap l E f n)
        (integralOperationsPullbackAdjunction l E f n) _ (op V)
        (unrestrictedIntegralTensorSection l E Y n M (op V) 1 x)) = _
  have hp := SheafOfModules.IntegralPullbackProof.mateData_unit_formula
    (integralOperationsBaseChange f)
    (scalarFiniteRingMap l E L ι X n) (scalarFiniteRingMap l E L ι Y n)
    (integralOperationsDirectRingMap l E f n) (integralOperationsDirectRingMap l L f n)
    (finiteScalarPullbackSquare l E L ι f n)
    (integralOperationsPullbackAdjunction l E f n)
    (integralOperationsPullbackAdjunction l L f n)
    (finiteScalarModule l E L ι Y n M) (op V)
    (unrestrictedIntegralTensorSection l E Y n M (op V) 1 x)
  exact hp.trans (congrArg (integralOperationsPullbackGenerator l L f n _ V)
    (finiteScalarModule_unit l E L ι Y n M (op V) x))

attribute [local irreducible] pullbackScalarModule pullbackFiniteScalarModule

private theorem pullbackModuleFunctor_generator {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) {M N : integralTowerModules l E Y} (a : M ⟶ N)
    (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((pullbackModuleFunctor l E f n).map a).val.app
        (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
        (integralOperationsPullbackGenerator l E f n _ V
          (unrestrictedIntegralTensorSection l E Y n M (op V) 1 x)) =
      integralOperationsPullbackGenerator l E f n _ V
        (unrestrictedIntegralTensorSection l E Y n N (op V) 1 (a.val.app (op V) x)) := by
  have h := congrArg (fun k ↦ k.val.app (op V)
    (unrestrictedIntegralTensorSection l E Y n M (op V) 1 x))
    ((integralOperationsPullbackAdjunction l E f n).unit.naturality
      ((unrestrictedIntegralReductionFunctor l E Y n).map a))
  have hr : ((unrestrictedIntegralReductionFunctor l E Y n).map a).val.app (op V)
      (unrestrictedIntegralTensorSection l E Y n M (op V) 1 x) =
      unrestrictedIntegralTensorSection l E Y n N (op V) 1 (a.val.app (op V) x) :=
    tensorSection_map (completedIntegralCommRingProjectionUnrestricted l E Y n)
      (unrestrictedIntegralReductionFunctor l E Y n) (unrestrictedReduction_obj l E Y n)
      (fun a ↦ unrestrictedReduction_map l E Y n a) a (op V) 1 x
  exact h.symm.trans (congrArg (integralOperationsPullbackGenerator l E f n _ V) hr)

private theorem pullbackScalarModule_naturality {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) {M N : integralTowerModules l E Y} (a : M ⟶ N) :
    (integralOrdinaryScalar l E L ι X).map ((pullbackModuleFunctor l E f n).map a) ≫
        pullbackScalarModule l E L ι f n N =
      pullbackScalarModule l E L ι f n M ≫
        (pullbackModuleFunctor l L f n).map ((integralOrdinaryScalar l E L ι Y).map a) := by
  apply scalar_pullback_hom_ext l E L ι f n n (scalarFiniteRingMap l E L ι X n)
    (scalarProjectionRingSquare l E L ι X n) M
  intro V x
  change (pullbackScalarModule l E L ι f n N).val.app _
      (((integralOrdinaryScalar l E L ι X).map
        ((pullbackModuleFunctor l E f n).map a)).val.app _
          (integralOrdinaryTensorSection l E L ι X _ _ 1
            (integralOperationsPullbackGenerator l E f n _ V
              (unrestrictedIntegralTensorSection l E Y n M (op V) 1 x)))) =
    ((pullbackModuleFunctor l L f n).map ((integralOrdinaryScalar l E L ι Y).map a)).val.app _
      ((pullbackScalarModule l E L ι f n M).val.app _
        (integralOrdinaryTensorSection l E L ι X _ _ 1
          (integralOperationsPullbackGenerator l E f n _ V
            (unrestrictedIntegralTensorSection l E Y n M (op V) 1 x))))
  erw [scalar_map_tensor, pullbackModuleFunctor_generator, pullbackScalarModule_unit,
    pullbackScalarModule_unit, pullbackModuleFunctor_generator, scalar_map_tensor]

/-- The normalized finite scalar pullback comparison exists.
Source: Stacks Tags 03CZ and 03D7.
(blueprint: lem-pur-integral-scalar-pullback-level-construction).
Proof: apply the finite coefficient pullback mate to the normalized reduction map,
restrict along the coefficient square, and transpose through ordinary scalar
extension. Naturality on module maps gives chain maps and naturality on complexes;
the three adjunction unit equations give the displayed generator formula. -/
theorem integralScalarPullbackLevel_exists {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    ∃ α : integralOperationsPullbackLevel l E f n ⋙
        (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        integralOperationsPullbackLevel l L f n,
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (V : Y.ProEt)
        (x : (P.X i).val.obj (op V)),
        ((α.app P).f i).val.app (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
          (integralOrdinaryTensorSection l E L ι X
            (((integralOperationsPullbackLevel l E f n).obj P).X i)
            (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V)) 1
            (integralOperationsPullbackGenerator l E f n
              (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
              (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x))) =
        integralOperationsPullbackGenerator l L f n
          (((unrestrictedIntegralFiniteComplex l L Y n).obj
            (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)).X i) V
          (unrestrictedIntegralTensorSection l L Y n
            ((integralOrdinaryScalar l E L ι Y).obj (P.X i)) (op V) 1
            (integralOrdinaryTensorSection l E L ι Y (P.X i) (op V) 1 x)) := by
  let α : integralOperationsPullbackLevel l E f n ⋙
      (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ) ⟶
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ) ⋙
        integralOperationsPullbackLevel l L f n :=
    { app := fun P ↦
        { f := fun i ↦ pullbackScalarModule l E L ι f n (P.X i)
          comm' := fun i j _ ↦ (pullbackScalarModule_naturality l E L ι f n (P.d i j)).symm }
      naturality := fun P Q a ↦ HomologicalComplex.hom_ext _ _
        (fun i ↦ pullbackScalarModule_naturality l E L ι f n (a.f i)) }
  refine ⟨α, ?_⟩
  · intro P i V x
    exact pullbackScalarModule_unit l E L ι f n (P.X i) V x

end WeilConjectures

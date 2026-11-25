/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition

import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackLevelConstruction

/-! # Composition of normalized finite scalar pullback comparisons

The normalized finite-level comparison respects coefficient composition, by its
existing uniqueness property and the tensor formulas for the scalar associator.
(blueprint: lem-pur-integral-scalar-pullback-level-composition)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u a b a' b' v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection integralCompletedScalarMap
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  coefficientTotalTensor
attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor
  integralOperationsTensorTowerFunctor scalarPullbackChain scalarTensorChain
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

variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (j : L →ₐ[ℚ_[l]] F)

attribute [local irreducible] integralOrdinaryScalarComp scalarPullbackLevel scalarPullbackTower
  integralOperationsLevelPullback unrestrictedIntegralReductionFunctor
  AlgebraicGeometry.Scheme.coefficientProEtaleModulePullback Functor.leftAdjoint
attribute [local implicit_reducible] integralOperationsPullbackLevel integralOperationsRestrict
  integralCoefficientSheaf integralCoefficientCommRingSheaf

private theorem pullbackLevel_normalization {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    scalarPullbackLevelNormalization l E L ι f n (scalarPullbackLevel l E L ι f n) := by
  simpa only [scalarPullbackLevel] using
    (scalarPullbackLevel_existsUnique l E L ι f n).exists.choose_spec

/-- Finite scalar pullback maps respect composition of the coefficient embeddings.
Source: Stacks 03EL and 07A4; the finite-generator calculation in the scalar
comparison part of blueprint fix-prop-coherence. Precompose the two successive
comparisons with the inverse scalar associator on X, and postcompose with the
pullback of the associator on Y. Its action on a normalized generator inserts two
unit tensors and then multiplies them. The prescribed normalization and uniqueness
therefore identify it with the direct comparison. Evaluate at P and cancel the
inverse associator.
(blueprint: lem-pur-integral-scalar-pullback-level-composition) -/
theorem integralScalarPullbackLevelComposition {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :
    (((integralOrdinaryScalar l L F j X).mapHomologicalComplex (.up ℤ)).map
        ((scalarPullbackLevel l E L ι f n).app P)) ≫
      (scalarPullbackLevel l L F j f n).app
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (integralOperationsPullbackLevel l F f n).map
        ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι Y F j)
          (.up ℤ)).hom.app P) =
    (NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι X F j)
      (.up ℤ)).hom.app ((integralOperationsPullbackLevel l E f n).obj P) ≫
        (scalarPullbackLevel l E F (j.comp ι) f n).app P := by
  let TE := integralOperationsPullbackLevel l E f n
  let TF := integralOperationsPullbackLevel l F f n
  let TX := (integralOrdinaryScalar l L F j X).mapHomologicalComplex (.up ℤ)
  let SY := (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)
  let aX := NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι X F j) (.up ℤ)
  let aY := NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι Y F j) (.up ℤ)
  let α : TE ⋙ (integralOrdinaryScalar l E F (j.comp ι) X).mapHomologicalComplex (.up ℤ) ⟶
      (integralOrdinaryScalar l E F (j.comp ι) Y).mapHomologicalComplex (.up ℤ) ⋙ TF :=
    Functor.whiskerLeft TE aX.inv ≫
      Functor.whiskerRight (scalarPullbackLevel l E L ι f n) TX ≫
        Functor.whiskerLeft SY (scalarPullbackLevel l L F j f n) ≫
          Functor.whiskerRight aY.hom TF
  have hα : scalarPullbackLevelNormalization l E F (j.comp ι) f n α := by
    intro Q i V x
    dsimp only [α, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex, aX, aY, TX, TE, TF, SY]
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    with_unfolding_all
      have hi := scalar_comp_inv_tensor l E L ι X F j
        (((integralOperationsPullbackLevel l E f n).obj Q).X i)
        (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V)) 1
        (integralOperationsPullbackGenerator l E f n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj Q).X i) V
          (unrestrictedIntegralTensorSection l E Y n (Q.X i) (op V) 1 x))
    rw [hi]
    erw [scalar_map_tensor l L F j X,
      pullbackLevel_normalization l E L ι f n Q i V x,
      pullbackLevel_normalization l L F j f n]
    erw [pullbackModuleFunctor_generator l F f n]
    have h := (integralOrdinaryScalarComp_existsUnique l E L ι Y F j).exists.choose_spec
      (Q.X i) (op V) 1 1 x
    have h' : ((integralOrdinaryScalarComp l E L ι Y F j).hom.app (Q.X i)).val.app (op V)
        (integralOrdinaryTensorSection l L F j Y _ (op V) 1
          (integralOrdinaryTensorSection l E L ι Y (Q.X i) (op V) 1 x)) =
        integralOrdinaryTensorSection l E F (j.comp ι) Y (Q.X i) (op V) 1 x := by
      simpa only [integralOrdinaryScalarComp, map_one, mul_one] using h
    erw [h']
    rfl
  have hu : α = scalarPullbackLevel l E F (j.comp ι) f n :=
    (scalarPullbackLevel_existsUnique l E F (j.comp ι) f n).unique hα
      (pullbackLevel_normalization l E F (j.comp ι) f n)
  apply (cancel_epi (aX.inv.app (TE.obj P))).mp
  dsimp only [aX, TE]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  simpa only [α, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using congrArg (fun τ ↦ τ.app P) hu

end WeilConjectures

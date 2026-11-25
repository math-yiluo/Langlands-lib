/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition

import all Mathlib.CategoryTheory.Limits.HasLimits

import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorLevelReduction
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import all WeilConjectures.SmoothPurity.Integral.IntegralTensorTransitionCompatibility
import all WeilConjectures.SecSmoothPurity.StrictCoefficient.ScalarCalculation.NormalizedScalarTensorTransitionsSupplement

/-! # Composition of normalized finite scalar tensor maps
(blueprint: lem-pur-integral-scalar-tensor-level-tower). -/

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
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  coefficientTotalTensor
attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsPullbackTowerFunctor scalarPullbackChain scalarTensorChain
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

section FiniteLevel

attribute [local irreducible] scalarAdjunction integralOrdinaryScalarComp
  integralOperationsRoos integralOperationsRoosMap
attribute [local implicit_reducible] integralOperationsRoosFunctor
  NatIso.mapHomologicalComplex NatTrans.mapHomologicalComplex
  integralOperationsTensorTowerFunctor integralOperationsTensorComplexFunctor
  integralOperationsTensorLevel integralOperationsRestrict integralOperationsTensorComposite
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
attribute [-instance] SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive
attribute [local instance 2001] integralOperationsFiniteHasMap

private theorem finite_reduction_map_section (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    {M N : integralTowerModules l E W} (f : M ⟶ N) (U : W.ProEtᵒᵖ)
    (x : M.val.obj U) :
    ((unrestrictedIntegralReductionFunctor l E W n).map f).val.app U
        (unrestrictedIntegralTensorSection l E W n M U 1 x) =
      unrestrictedIntegralTensorSection l E W n N U 1 (f.val.app U x) := by
  exact identified_map_section (completedIntegralCommRingProjectionUnrestricted l E W n)
    (unrestrictedIntegralReductionFunctor l E W n)
    (unrestrictedReduction_obj l E W n) (fun f ↦ unrestrictedReduction_map l E W n f)
    f U 1 x

private theorem finite_total_pure (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P).X p).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X q).val.obj U) :
    CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation.totalPure
        ((unrestrictedIntegralFiniteComplex l E W n).obj P)
        ((unrestrictedIntegralFiniteComplex l E W n).obj Q) p q (p + q) rfl U x y =
      integralOperationsTotalTensorSection l E W n P Q p q U x y := by
  exact TensorChainProof.totalPure_eq (integralCoefficientCommRingSheaf l E W n) p q U x y

private theorem finite_tensor_map_section (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    {P Q P' Q' : CochainComplex (integralTowerModules l E W) ℤ}
    (a : P ⟶ P') (b : Q ⟶ Q') (p q : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P).X p).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X q).val.obj U) :
    (((integralOperationsTensorLevel l E W n).map
        (X := (P, Q)) (Y := (P', Q')) (a, b)).f (p + q)).val.app U
        (integralOperationsTotalTensorSection l E W n P Q p q U x y) =
      integralOperationsTotalTensorSection l E W n P' Q' p q U
        ((((unrestrictedIntegralFiniteComplex l E W n).map a).f p).val.app U x)
        ((((unrestrictedIntegralFiniteComplex l E W n).map b).f q).val.app U y) := by
  rw [← finite_total_pure, ← finite_total_pure]
  have h := CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation.totalMap_pure
    ((unrestrictedIntegralFiniteComplex l E W n).map a)
    ((unrestrictedIntegralFiniteComplex l E W n).map b) p q (p + q) rfl U x y
  simp only [integralOperationsTensorLevel, TensorTotalProof.composite_map]
  with_unfolding_all exact h

/-- Normalized finite tensor comparisons respect composition of coefficient maps.
Source: Stacks Tags 03EL, 07A4; scalar comparison proof step 9 in the blueprint.
(blueprint: lem-pur-integral-scalar-tensor-level-tower).
Proof: precompose by the inverse scalar associator and apply the scalar adjunction.
The finite tensor generator extensionality reduces to original pairs of sections.
The unit formula, inverse associator formula and normalized tensor comparisons
compute both sides. The total tensor map acts on the two sections; finite reduction
and the associator multiplication formula identify its output with the direct
comparison, since ring maps preserve one. -/
theorem integralScalarTensorLevelTower (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    ((integralOrdinaryScalar l L F j W).mapHomologicalComplex (.up ℤ)).map
        ((scalarTensorLevel l E L ι W n).app (P, Q)) ≫
      (scalarTensorLevel l L F j W n).app
        ((((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P),
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q)) ≫
      (integralOperationsTensorLevel l F W n).map (CategoryTheory.Prod.mkHom
        ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
          (.up ℤ)).hom.app P)
        ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
          (.up ℤ)).hom.app Q)) =
    (NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
      (.up ℤ)).hom.app ((integralOperationsTensorLevel l E W n).obj (P, Q)) ≫
        (scalarTensorLevel l E F (j.comp ι) W n).app (P, Q) := by
  let κ := NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
    (.up ℤ)
  apply (cancel_epi (κ.inv.app ((integralOperationsTensorLevel l E W n).obj (P, Q)))).mp
  simp only [κ, Iso.inv_hom_id_app_assoc]
  apply HomologicalComplex.hom_ext
  intro k
  apply ((scalarAdjunction l E F (j.comp ι) W).homEquiv _ _).injective
  apply finite_tensor_ext l E W n P Q k
  intro p q hpq U x y
  subst k
  let z : ((((integralOperationsTensorLevel l E W n).obj (P, Q)).X (p + q)).val.obj U) :=
    integralOperationsTotalTensorSection l E W n P Q p q U
      (unrestrictedIntegralTensorSection l E W n _ U 1 x)
      (unrestrictedIntegralTensorSection l E W n _ U 1 y)
  change (((integralOperationsTensorLevel l F W n).map
      (κ.hom.app P, κ.hom.app Q)).f (p + q)).val.app U
      ((((scalarTensorLevel l L F j W n).app _).f (p + q)).val.app U
        (((integralOrdinaryScalar l L F j W).map
          (((scalarTensorLevel l E L ι W n).app (P, Q)).f (p + q))).val.app U
          (((integralOrdinaryScalarComp l E L ι W F j).inv.app _).val.app U
            (((scalarAdjunction l E F (j.comp ι) W).unit.app _).val.app U
              z)))) =
    (((scalarTensorLevel l E F (j.comp ι) W n).app (P, Q)).f (p + q)).val.app U
      (((scalarAdjunction l E F (j.comp ι) W).unit.app _).val.app U
        z)
  rw [scalarAdjunction_unit]
  rw [scalar_comp_inv_tensor]
  erw [scalar_map_tensor]
  have hi := (scalarTensorLevel_existsUnique l E L ι W n).exists.choose_spec
  have hj := (scalarTensorLevel_existsUnique l L F j W n).exists.choose_spec
  have hji := (scalarTensorLevel_existsUnique l E F (j.comp ι) W n).exists.choose_spec
  change scalarTensorLevelNormalization l E L ι W n (scalarTensorLevel l E L ι W n) at hi
  change scalarTensorLevelNormalization l L F j W n (scalarTensorLevel l L F j W n) at hj
  change scalarTensorLevelNormalization l E F (j.comp ι) W n
    (scalarTensorLevel l E F (j.comp ι) W n) at hji
  dsimp only [z]
  erw [hi, hj, finite_tensor_map_section]
  simp only [Functor.mapHomologicalComplex_map_f]
  erw [finite_reduction_map_section, finite_reduction_map_section]
  have hc : ∀ N U c b x,
    ((integralOrdinaryScalarComp l E L ι W F j).hom.app N).val.app U
      (integralOrdinaryTensorSection l L F j W _ U c
        (integralOrdinaryTensorSection l E L ι W N U b x)) =
      integralOrdinaryTensorSection l E F (j.comp ι) W N U
        (c * (integralCompletedScalarMap l L F j W).hom.app U b) x := by
    simpa only [integralOrdinaryScalarComp] using
      (integralOrdinaryScalarComp_existsUnique l E L ι W F j).exists.choose_spec
  erw [hc, hc]
  simp only [map_one, one_mul]
  exact (hji P Q p q U x y).symm

end FiniteLevel

end WeilConjectures

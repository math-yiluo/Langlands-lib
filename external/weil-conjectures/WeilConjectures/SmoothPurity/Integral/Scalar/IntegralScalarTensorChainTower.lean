/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition

import WeilConjectures.SmoothPurity.Supporting.AdditiveRoosHorizontal
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorTowerComposition

/-! # Scalar completed tensor chain comparisons and coefficient towers

Source: Stacks 07A4, 08TC; coefficient-comparison coherence in the blueprint.
(blueprint: lem-pur-integral-scalar-tensor-chain-tower). -/

@[expose] public noncomputable section
set_option autoImplicit false
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

attribute [local irreducible] integralOperationsTensorLevel integralOrdinaryScalarComp
  integralOperationsTensorTowerFunctor integralOperationsRoos integralOperationsRoosMap
attribute [local implicit_reducible] integralOperationsTensorComplexFunctor
  integralOperationsRoosFunctor

/-- The normalized completed-tensor Roos chain maps respect coefficient towers.
Source: Stacks 07A4, 08TC; blueprint scalar comparison proof step 9
(blueprint: lem-pur-integral-scalar-tensor-chain-tower).
Proof: on each bidegree generator the two finite-level routes send
c tensor (b tensor ((1 tensor x) tensor (1 tensor y))) to the tensor of
c*j(b) tensor (1 tensor x) with 1 tensor (1 tensor y). The scalar
associator's multiplication and the two tensor comparison formulas give exactly
this equality. Balanced tensor relations, sheafification, and the coproducts in
total degree extend it to the finite total complex, respecting both signed
differential summands. Consecutive reduction compatibility gives equality of
strict tower maps. Project the Roos comparison onto each of its two product
coordinates. Naturality of the canonical product comparisons and the finite-level
equality identify both routes. Product projections are jointly injective,
so the chain maps agree. Zero complexes, identity extensions and arbitrary
unbounded inputs are included. -/
theorem integralScalarTensorChainTower (W : AlgebraicGeometry.Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    ((integralOrdinaryScalar l L F j W).mapHomologicalComplex (.up ℤ)).map
        (scalarTensorChain l E L ι W P Q) ≫
      scalarTensorChain l L F j W
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P)
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q) ≫
      (integralOperationsTensorComplexFunctor l F W).map (CategoryTheory.Prod.mkHom
        ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
          (.up ℤ)).hom.app P)
        ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
          (.up ℤ)).hom.app Q)) =
    (NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
      (.up ℤ)).hom.app ((integralOperationsTensorComplexFunctor l E W).obj (P, Q)) ≫
        scalarTensorChain l E F (j.comp ι) W P Q := by
  let S := integralOrdinaryScalar l E L ι W
  let T := integralOrdinaryScalar l L F j W
  let U := integralOrdinaryScalar l E F (j.comp ι) W
  let SC := S.mapHomologicalComplex (.up ℤ)
  let TC := T.mapHomologicalComplex (.up ℤ)
  let κ := integralOrdinaryScalarComp l E L ι W F j
  let κC := NatIso.mapHomologicalComplex κ (.up ℤ)
  let X := (integralOperationsTensorTowerFunctor l E W).obj (P, Q)
  let Y := (integralOperationsTensorTowerFunctor l L W).obj (SC.obj P, SC.obj Q)
  let Z := (integralOperationsTensorTowerFunctor l F W).obj
    ((U.mapHomologicalComplex (.up ℤ)).obj P, (U.mapHomologicalComplex (.up ℤ)).obj Q)
  let a := (scalarTensorTower l E L ι W).app (P, Q)
  let b :=
    (scalarTensorTower l L F j W).app (SC.obj P, SC.obj Q) ≫
      (integralOperationsTensorTowerFunctor l F W).map
        (CategoryTheory.Prod.mkHom (κC.hom.app P) (κC.hom.app Q))
  let c :=
    (scalarTensorTower l E F (j.comp ι) W).app (P, Q)
  have h : Functor.whiskerRight a TC ≫ b =
      Functor.whiskerLeft X κC.hom ≫ c := by
    exact integralScalarTensorTowerComposition l E L ι F j W P Q
  have hr := additiveRoosComposite S T U κ X Y Z a b c h
  dsimp only [b] at hr
  rw [integralOperationsRoosMap_comp] at hr
  unfold scalarTensorChain
  dsimp only [a, c, X, Y, Z, S, T, U, SC, TC, κ, κC,
    integralOperationsTensorComplexFunctor, Functor.comp_obj, Functor.comp_map,
    integralOperationsRoosFunctor] at hr ⊢
  simpa only [Category.assoc] using hr

end WeilConjectures

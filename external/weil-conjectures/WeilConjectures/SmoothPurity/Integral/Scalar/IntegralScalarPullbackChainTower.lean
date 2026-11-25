/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackChainTowerComponent

/-! # Scalar pullback chain comparisons and coefficient towers

Source: Stacks 07A4, 08TC; coefficient-comparison coherence in the blueprint.
(blueprint: lem-pur-integral-scalar-pullback-chain-tower). -/

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
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
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

/-- The normalized pullback Roos chain maps commute with coefficient composition.
Source: Stacks 07A4, 08TC; blueprint scalar comparison proof step 9
(blueprint: lem-pur-integral-scalar-pullback-chain-tower).
Proof: first compare the two maps on a finite pullback generator. Both send
c tensor (b tensor f*(1 tensor x)) to f*(c*j(b) tensor (1 tensor x));
the scalar associator multiplies c*j(b), and the two normalized level maps insert
units. Extension/restriction adjunction and sheafification show equality on each
finite level. The consecutive reduction squares identify these as equal maps of
strict towers. For the Roos map, project to every unshifted product coordinate
and then every shifted product coordinate. Both routes are the preceding finite
level equality, since finite free extension preserves the products. The signed
Roos differential is respected by the same reduction squares. Joint injectivity
of the product projections in each degree gives this chain-map equality. This
also covers identity extensions and the zero complex; no completeness or
constructibility of the input complex is needed. -/
theorem integralScalarPullbackChainTower {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ((integralOrdinaryScalar l L F j X).mapHomologicalComplex (.up ℤ)).map
        (scalarPullbackChain l E L ι f P) ≫
      scalarPullbackChain l L F j f
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (integralOperationsPullbackComplexFunctor l F f).map
        ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι Y F j)
          (.up ℤ)).hom.app P) =
    (NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι X F j)
      (.up ℤ)).hom.app ((integralOperationsPullbackComplexFunctor l E f).obj P) ≫
        scalarPullbackChain l E F (j.comp ι) f P := by
  apply HomologicalComplex.hom_ext
  intro i
  exact integralScalarPullbackChainTower_f l E L ι F j f P i

end WeilConjectures

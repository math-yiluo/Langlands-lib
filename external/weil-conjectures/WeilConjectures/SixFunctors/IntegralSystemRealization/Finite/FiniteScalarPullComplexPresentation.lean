/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.IntegralFiniteScalarPullOrdinary
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.FiniteScalarOrdinaryReductionIso
public import WeilConjectures.SixFunctors.PurCompactSupport.ScalarPullCoefficientComplexNormalization
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.FiniteScalarPullPresentation

/-! # Degreewise finite scalar pullback presentations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.Functor.leftAdjoint SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.completed
  WeilConjectures.integralCoefficientSheaf WeilConjectures.integralCoefficientCommRingSheaf
attribute [local instance] WeilConjectures.coefficientFiniteExtensionAdditive
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The ordinary finite scalar presentation square holds degreewise on any complex.
Source: Stacks Tags 07A6, 06YY and 0D6E
(blueprint: lem-sf-finite-scalar-pull-complex-presentation).
Proof: in degree j the complex composition isomorphisms are identities, and the
scalar presentation and pullback presentation are their ordinary components.
The desired component equation is finiteScalarPullPresentation at P.X j.
Extensionality of morphisms of complexes proves the result. No K-flatness is
required; in particular the zero complex and n=0 are included. -/
theorem finiteScalarPullComplexPresentation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
    let := scalarReductionExtensionAdditive.{u, u} l E X n
    let := scalarReductionExtensionAdditive.{u, u} l E Y n
    let a := PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)
    let S := PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)
    let T := proEtaleRingModulePullback f (S.ring Y) (S.ring X) (S.pull f)
    let CY := ((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P
    (PurCompactSupport.scalarPullComplex a f).inv.app P ≫
        (T.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (finiteScalarOrdinaryReductionIso l E Y n).hom
            (.up ℤ)).app P) ≫
        (NatIso.mapHomologicalComplex (PurCompactSupport.finitePullbackIso l E n f)
          (.up ℤ)).hom.app CY =
      (NatTrans.mapHomologicalComplex (finiteScalarOrdinaryReductionIso l E X n).hom
        (.up ℤ)).app (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P) ≫
        ordinaryFiniteScalarPullComplex l E f n P ≫
        (NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E f n)
          (.up ℤ)).hom.app CY := by
  let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  let := scalarReductionExtensionAdditive.{u, u} l E X n
  let := scalarReductionExtensionAdditive.{u, u} l E Y n
  apply HomologicalComplex.hom_ext
  intro j
  dsimp only [PurCompactSupport.scalarPullComplex]
  change (PurCompactSupport.scalarPullModule
      (PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)) f).inv.app (P.X j) ≫
    (proEtaleRingModulePullback f
      ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring Y)
      ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring X)
      ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).pull f)).map
        ((finiteScalarOrdinaryReductionIso l E Y n).hom.app (P.X j)) ≫
      (PurCompactSupport.finitePullbackIso l E n f).hom.app
        ((scalarReductionExtension l E Y n).obj (P.X j)) =
    (finiteScalarOrdinaryReductionIso l E X n).hom.app
        ((integralOrdinaryPull l E f).obj (P.X j)) ≫
      (ordinaryFiniteScalarPull l E f n).hom.app (P.X j) ≫
      (pullbackTensorLevelIntrinsic l E f n).hom.app
        ((scalarReductionExtension l E Y n).obj (P.X j))
  exact finiteScalarPullPresentation l E f n (P.X j)

end WeilConjectures.IntegralSystemRealization

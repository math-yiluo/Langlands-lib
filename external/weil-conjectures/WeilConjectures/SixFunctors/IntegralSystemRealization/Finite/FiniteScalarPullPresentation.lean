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
import WeilConjectures.CategoryTheory.Finite.FiniteScalarPullAdjunctionTransport

/-! # Ordinary finite scalar pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Adjunction.leftAdjointUniq SheafOfModules.monoidalCategory
  WeilConjectures.scalarReductionExistence WeilConjectures.scalarReductionDerivedExistence
  WeilConjectures.scalarReductionExtension
  AlgebraicGeometry.Scheme.pbcScalarAdjunction
  AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction
  AlgebraicGeometry.Scheme.proEtaleRingRestrictionDirectImage
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.completed
  WeilConjectures.integralCoefficientSheaf WeilConjectures.integralCoefficientCommRingSheaf
  WeilConjectures.unrestrictedIntegralReductionFunctor
attribute [local instance] WeilConjectures.coefficientFiniteExtensionAdditive
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem level_intrinsic_uniqueness {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    pullbackTensorLevelIntrinsic l E f n =
      (coefficientProEtaleModuleAdjunction.{u, u} f
        (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))).leftAdjointUniq
          (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1))) := by
  unfold pullbackTensorLevelIntrinsic pullbackTensorUniqueChoice
  apply (pullbackTensorLevelIntrinsic_existsUnique l E f n).unique
    (pullbackTensorLevelIntrinsic_existsUnique l E f n).exists.choose_spec
  intro M U x
  exact congrArg (fun k ↦ k.val.app (op U) x)
    (Adjunction.unit_leftAdjointUniq_hom_app
      (coefficientProEtaleModuleAdjunction.{u, u} f
        (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1)))))
      (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1))) M)

/-- The two ordinary scalar/pullback presentations have the same adjunction mate.
Source: Stacks Tags 06YY and 0D6E
(blueprint: lem-sf-finite-scalar-pull-presentation).

Proof: transpose both sides through the composite scalar and geometric adjunctions.
The scalar presentation isomorphisms transfer the transpose by left-adjoint
uniqueness. The geometric presentation transfers it through finiteDirectImage_eq.
The unit normalization of pullbackTensorLevelIntrinsic identifies its transpose
with the identity for the intrinsic adjunction. Both resulting right comparisons
are finiteScalarRestrictionDirect: the equality transport followed by the identity
on restriction/direct-image sections. Injectivity of the composite Hom equivalence
proves the equality. No resolution, derived category, sequence object, or realization
model is involved. In particular, the argument applies to zero modules and n=0. -/
theorem finiteScalarPullPresentation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : integralTowerModules l E Y) :
    (PurCompactSupport.scalarPullModule
        (PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)) f).inv.app M ≫
      (proEtaleRingModulePullback f
        ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring Y)
        ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring X)
        ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).pull f)).map
          ((finiteScalarOrdinaryReductionIso l E Y n).hom.app M) ≫
      (PurCompactSupport.finitePullbackIso l E n f).hom.app
        ((scalarReductionExtension l E Y n).obj M) =
    (finiteScalarOrdinaryReductionIso l E X n).hom.app
        ((integralOrdinaryPull l E f).obj M) ≫
      (ordinaryFiniteScalarPull l E f n).hom.app M ≫
      (pullbackTensorLevelIntrinsic l E f n).hom.app
        ((scalarReductionExtension l E Y n).obj M) := by
  let a := PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)
  let S := PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)
  let ar := proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f)
  let px := pbcScalarAdjunction (a.map X)
  let py := pbcScalarAdjunction (a.map Y)
  let ax := pullbackTensorFiniteAdjunction l E X n
  let ay := pullbackTensorFiniteAdjunction l E Y n
  let g := proEtaleRingModuleAdjunction f (S.ring Y) (S.ring X) (S.pull f)
  let v := coefficientProEtaleModuleAdjunction.{u, u} f
    (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))
  let i := sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1))
  let e := eqToIso (PurCompactSupport.finiteDirectImage_eq l E n f)
  let d := proEtaleRingRestrictionDirectImage f
    ((PurCompactSupport.completed l E).ring Y) (S.ring Y)
    ((PurCompactSupport.completed l E).ring X) (S.ring X)
    (a.map Y) (a.map X) ((PurCompactSupport.completed l E).pull f) (S.pull f) (a.square f)
  have hlam : (PurCompactSupport.finitePullbackIso l E n f).hom.app
      ((scalarReductionExtension l E Y n).obj M) =
    ((g.ofNatIsoRight e).leftAdjointUniq v).hom.app
        ((scalarReductionExtension l E Y n).obj M) ≫
      (pullbackTensorLevelIntrinsic l E f n).hom.app
        ((scalarReductionExtension l E Y n).obj M) := by
    rw [level_intrinsic_uniqueness l E f n]
    exact (Adjunction.leftAdjointUniq_trans_app (g.ofNatIsoRight e) v i _).symm
  rw [hlam]
  have h := adjunctionSquareTransport
    (S' := scalarReductionExtension l E X n)
    (T' := scalarReductionExtension l E Y n) ar px ax py ay g v d e M
  have hpx : px.leftAdjointUniq ax = finiteScalarOrdinaryReductionIso l E X n := by
    exact finiteScalarOrdinaryReductionIso_eq l E X n
  have hpy : py.leftAdjointUniq ay = finiteScalarOrdinaryReductionIso l E Y n := by
    exact finiteScalarOrdinaryReductionIso_eq l E Y n
  have hq : ((ar.comp px).ofNatIsoRight d.symm).leftAdjointUniq (py.comp g) =
      (PurCompactSupport.scalarPullModule a f).symm := by
    unfold PurCompactSupport.scalarPullModule
    rfl
  have hν : ((ar.comp ax).ofNatIsoRight
      (Functor.isoWhiskerRight e.symm (pbcRestrict (a.map Y)) ≪≫ d).symm).leftAdjointUniq
        (ay.comp v) = ordinaryFiniteScalarPull l E f n := by
    exact (ordinaryFiniteScalarPull_eq l E f n).symm
  dsimp only at h
  rw [hpx, hpy, hq, hν] at h
  have hh := congrArg (fun k ↦ k ≫
    (pullbackTensorLevelIntrinsic l E f n).hom.app
      ((scalarReductionExtension l E Y n).obj M)) h
  simpa only [Iso.symm_hom, Category.assoc] using hh

end WeilConjectures.IntegralSystemRealization

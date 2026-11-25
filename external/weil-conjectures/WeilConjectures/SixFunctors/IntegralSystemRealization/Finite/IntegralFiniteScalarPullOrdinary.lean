/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison

/-! # Ordinary finite scalar pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
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
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.completed
  WeilConjectures.integralCoefficientSheaf WeilConjectures.integralCoefficientCommRingSheaf
attribute [local instance] WeilConjectures.coefficientFiniteExtensionAdditive
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The identity on sections comparing finite direct image and scalar restriction.
Source: Stacks 03D7 and 0D6E
(blueprint: lem-sf-integral-finite-scalar-pull-ordinary). -/
@[irreducible] def finiteScalarRestrictionDirect {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    proEtaleConstantModuleDirectImage f (finiteCoefficientRing l E (n + 1)) ⋙
        scalarReductionRestriction l E Y n ≅
      scalarReductionRestriction l E X n ⋙
        proEtaleRingModuleDirectImage f ((PurCompactSupport.completed l E).ring Y)
          ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f) :=
  Functor.isoWhiskerRight (eqToIso (PurCompactSupport.finiteDirectImage_eq l E n f)).symm
      (pbcRestrict
        ((PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)).map Y)) ≪≫
    proEtaleRingRestrictionDirectImage f
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring X)
      ((PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)).map Y)
      ((PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)).map X)
      ((PurCompactSupport.completed l E).pull f)
      ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).pull f)
      ((PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)).square f)

/-- The ordinary scalar/pullback square, uniquely determined by the right square.
Source: Stacks 03D7 and 06YY
(blueprint: lem-sf-integral-finite-scalar-pull-ordinary). -/
@[irreducible] def ordinaryFiniteScalarPull {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    integralOrdinaryPull l E f ⋙ scalarReductionExtension l E X n ≅
      scalarReductionExtension l E Y n ⋙
        integralOperationsLevelPullback l E f n :=
  (((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f)).comp
      (pullbackTensorFiniteAdjunction l E X n)).ofNatIsoRight
        (finiteScalarRestrictionDirect l E f n).symm).leftAdjointUniq
          ((pullbackTensorFiniteAdjunction l E Y n).comp
            (coefficientProEtaleModuleAdjunction.{u, u} f
              (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))))

/-- Expanded right comparison for the ordinary scalar square, kept as a folding API.
Source: Stacks Tags 06YY and 0D6E
(blueprint: lem-sf-integral-finite-scalar-pull-ordinary). -/
theorem ordinaryFiniteScalarPull_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ordinaryFiniteScalarPull l E f n =
    (((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
          ((PurCompactSupport.completed l E).ring X)
          ((PurCompactSupport.completed l E).pull f)).comp
          (pullbackTensorFiniteAdjunction l E X n)).ofNatIsoRight
            (Functor.isoWhiskerRight (eqToIso (PurCompactSupport.finiteDirectImage_eq l E n f)).symm
          (pbcRestrict
            ((PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)).map Y)) ≪≫
        proEtaleRingRestrictionDirectImage f
          ((PurCompactSupport.completed l E).ring Y)
          ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring Y)
          ((PurCompactSupport.completed l E).ring X)
          ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring X)
          ((PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)).map Y)
          ((PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)).map X)
          ((PurCompactSupport.completed l E).pull f)
          ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).pull f)
          ((PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)).square f)
        ).symm).leftAdjointUniq
              ((pullbackTensorFiniteAdjunction l E Y n).comp
                (coefficientProEtaleModuleAdjunction.{u, u} f
                  (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1)))))) := by
  unfold ordinaryFiniteScalarPull finiteScalarRestrictionDirect
  rfl

/-- The ordinary comparison has the composite-adjunction transpose prescribed by
its restriction/direct-image square.
Source: Stacks Tag 06YY
(blueprint: lem-sf-integral-finite-scalar-pull-ordinary).
Proof: the unit equation for leftAdjointUniq after ofNatIsoRight gives the
transpose followed by the inverse right comparison. Cancel that inverse. -/
theorem ordinaryFiniteScalarPull_transpose {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : integralTowerModules l E Y) :
    let ar := proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f)
    let ax := pullbackTensorFiniteAdjunction l E X n
    let ay := pullbackTensorFiniteAdjunction l E Y n
    let e := coefficientProEtaleModuleAdjunction.{u, u} f
      (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))
    (ar.comp ax).homEquiv M _ ((ordinaryFiniteScalarPull l E f n).hom.app M) =
      (ay.comp e).unit.app M ≫ (finiteScalarRestrictionDirect l E f n).hom.app
        ((integralOperationsLevelPullback l E f n).obj
          ((scalarReductionExtension l E Y n).obj M)) := by
  let ar := proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f)
  let ax := pullbackTensorFiniteAdjunction l E X n
  let ay := pullbackTensorFiniteAdjunction l E Y n
  let e := coefficientProEtaleModuleAdjunction.{u, u} f
    (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))
  unfold ordinaryFiniteScalarPull
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((ar.comp ax).ofNatIsoRight (finiteScalarRestrictionDirect l E f n).symm)
    (ay.comp e) M
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  apply (cancel_mono ((finiteScalarRestrictionDirect l E f n).inv.app _)).1
  dsimp only [Functor.comp_obj] at h ⊢
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  exact h

/-- Degreewise form of the ordinary scalar square.
Source: Stacks 07A6
(blueprint: lem-sf-integral-finite-scalar-pull-ordinary). -/
def ordinaryFiniteScalarPullComplex {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj
        (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      ((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj
        (((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P) where
  f i := (ordinaryFiniteScalarPull l E f n).hom.app (P.X i)
  comm' i j _ := ((ordinaryFiniteScalarPull l E f n).hom.naturality (P.d i j)).symm

end WeilConjectures.IntegralSystemRealization

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralScalarOperations.IntegralOperationsScalarExtension
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison

import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.ChangeOfRingsComplex
import Mathlib.Algebra.Homology.HomologicalComplex
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellation
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorLevelReduction
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackLevelReduction
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarFiniteReductionMaps
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackLevelConstruction
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorLevelConstruction

/-! # Finite-level models for normalized integral scalar comparisons

Source: blueprint sec-smooth-purity/sk-def-sf-operations, integral/common-stage paragraph;
Stacks Tags 07A4, 08J9, 099N
(blueprint: lem-pur-integral-scalar-finite-comparison-models).

The representative maps below fix the comparisons before any common-stage descent.
They use arbitrary finite extensions between the small coefficient models, independently
of the universe containing the algebraic closure.
-/

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

/-- The prescribed representative normalization, retained as a named predicate.
Source: Stacks 07A4, 08J9, 08TC
(blueprint: lem-pur-integral-scalar-finite-comparison-models). -/
def scalarPullbackLevelNormalization {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
    (α : integralOperationsPullbackLevel l E f n ⋙
        (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        integralOperationsPullbackLevel l L f n) : Prop :=
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
            (integralOrdinaryTensorSection l E L ι Y (P.X i) (op V) 1 x))

/-- Scalar extension of a finite pullback level, before taking the Roos complex.
Source: Stacks 07A4, 099N (blueprint: lem-pur-integral-scalar-finite-comparison-models).
Proof: on the displayed generators send 1 tensor f-star(1 tensor x) to
f-star(1 tensor (1 tensor x)). Extend by the target completed-ring action. The
canonical constant-section ring map makes this balanced. Kan extension and
sheafification give a unique sheaf map. It commutes with the differential and is
natural in P since the generator formula commutes with every chain map. -/
theorem scalarPullbackLevel_existsUnique {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    ∃! α : integralOperationsPullbackLevel l E f n ⋙
        (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        integralOperationsPullbackLevel l L f n,
      scalarPullbackLevelNormalization l E L ι f n α := by
  obtain ⟨α, hα⟩ := integralScalarPullbackLevel_exists l E L ι f n
  refine ⟨α, hα, ?_⟩
  intro β hβ
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro i
  with_unfolding_all
    refine scalar_pullback_hom_ext l E L ι f n n (scalarFiniteRingMap l E L ι X n)
      (scalarProjectionRingSquare l E L ι X n) (P.X i)
      ((integralOperationsLevelPullback l L f n).obj
        ((unrestrictedIntegralReductionFunctor l L Y n).obj
          ((integralOrdinaryScalar l E L ι Y).obj (P.X i))))
      ((β.app P).f i) ((α.app P).f i) ?_
    intro V x
    exact (hβ P i V x).trans (hα P i V x).symm

/-- The generator-normalized finite-level scalar pullback map.
Source: Stacks 07A4 (blueprint: lem-pur-integral-scalar-finite-comparison-models). -/
def scalarPullbackLevel {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    integralOperationsPullbackLevel l E f n ⋙
        (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        integralOperationsPullbackLevel l L f n :=
  (scalarPullbackLevel_existsUnique l E L ι f n).exists.choose

/-- The prescribed representative normalization, retained as a named predicate.
Source: Stacks 07A4, 08J9, 08TC
(blueprint: lem-pur-integral-scalar-finite-comparison-models). -/
def scalarPullbackTowerNormalization {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y)
    (α : integralOperationsPullbackTowerFunctor l E f ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        integralOperationsPullbackTowerFunctor l L f) : Prop :=
  ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ),
        (α.app P).app (op n) = (scalarPullbackLevel l E L ι f n).app P

/-- The level maps form the strict tower map; the component equations retain all
reduction maps, rather than choosing a map between unrelated limits.
Source: Stacks 07A4, 08TC (blueprint: lem-pur-integral-scalar-finite-comparison-models).
Proof: the two composites with each consecutive reduction have the same generator
formula. Uniqueness of the level maps proves the consecutive squares, and induction
proves all tower squares. Naturality in P is componentwise. This constructs the tower
transformation, and the component equations give uniqueness. -/
theorem scalarPullbackTower_existsUnique {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) :
    ∃! α : integralOperationsPullbackTowerFunctor l E f ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        integralOperationsPullbackTowerFunctor l L f,
      scalarPullbackTowerNormalization l E L ι f α := by
  exact scalarTowerAssembly
    (fun n ↦ integralOperationsPullbackLevel l E f n)
    (fun n ↦ integralOperationsPullbackLevel l L f n)
    (integralOperationsPullbackTransition l E f) (integralOperationsPullbackTransition l L f)
    ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ))
    ((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ))
    (scalarPullbackLevel l E L ι f)
    (integralScalarPullbackLevelReduction l E L ι f (scalarPullbackLevel l E L ι f)
      (fun n ↦ (scalarPullbackLevel_existsUnique l E L ι f n).exists.choose_spec))

/-- The strict scalar pullback tower map.
Source: Stacks 08TC (blueprint: lem-pur-integral-scalar-finite-comparison-models). -/
def scalarPullbackTower {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    integralOperationsPullbackTowerFunctor l E f ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        integralOperationsPullbackTowerFunctor l L f :=
  (scalarPullbackTower_existsUnique l E L ι f).exists.choose

/-- The chain comparison is the diagonal Roos map of the prescribed tower map.
Source: Stacks 07A4, 08TC (blueprint: lem-pur-integral-scalar-finite-comparison-models). -/
def scalarPullbackChain {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((integralOperationsPullbackComplexFunctor l E f).obj P) ⟶
      (integralOperationsPullbackComplexFunctor l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  scalarRoosMap (integralOrdinaryScalar l E L ι X)
      ((integralOperationsPullbackTowerFunctor l E f).obj P) ≫
    integralOperationsRoosMap ((scalarPullbackTower l E L ι f).app P)

/-- The prescribed representative normalization, retained as a named predicate.
Source: Stacks 07A4, 08J9, 08TC
(blueprint: lem-pur-integral-scalar-finite-comparison-models). -/
def scalarTensorLevelNormalization (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (α : integralOperationsTensorLevel l E W n ⋙
        (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          integralOperationsTensorLevel l L W n) : Prop :=
  ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ)
        (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((α.app (P, Q)).f (p + q)).val.app U
          (integralOrdinaryTensorSection l E L ι W
            (((integralOperationsTensorLevel l E W n).obj (P, Q)).X (p + q)) U 1
            (integralOperationsTotalTensorSection l E W n P Q p q U
              (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
              (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y))) =
        integralOperationsTotalTensorSection l L W n
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q) p q U
          (unrestrictedIntegralTensorSection l L W n
            ((integralOrdinaryScalar l E L ι W).obj (P.X p)) U 1
            (integralOrdinaryTensorSection l E L ι W (P.X p) U 1 x))
          (unrestrictedIntegralTensorSection l L W n
            ((integralOrdinaryScalar l E L ι W).obj (Q.X q)) U 1
            (integralOrdinaryTensorSection l E L ι W (Q.X q) U 1 y))

/-- Scalar extension of each finite tensor level is fixed on total tensor generators.
Source: Stacks 07A4 (blueprint: lem-pur-integral-scalar-finite-comparison-models).
Proof: send 1 tensor ((1 tensor x) tensor (1 tensor y)) to
(1 tensor (1 tensor x)) tensor (1 tensor (1 tensor y)), and extend by the target
completed scalar action. Balance follows from the coefficient quotient map. This
commutes with restrictions and both signed differentials, so extends uniquely
through sheafification and the direct-sum totalization. -/
theorem scalarTensorLevel_existsUnique (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    ∃! α : integralOperationsTensorLevel l E W n ⋙
        (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          integralOperationsTensorLevel l L W n,
      scalarTensorLevelNormalization l E L ι W n α := by
  obtain ⟨α, hα⟩ := integralScalarTensorLevel_exists l E L ι W n
  refine ⟨α, hα, ?_⟩
  intro β hβ
  apply NatTrans.ext
  funext Z
  rcases Z with ⟨P, Q⟩
  apply HomologicalComplex.hom_ext
  intro k
  apply ((scalarAdjunction l E L ι W).homEquiv _ _).injective
  apply finite_tensor_ext l E W n P Q k
  intro p q hpq U x y
  subst k
  change ((β.app (P, Q)).f (p + q)).val.app U
      (((scalarAdjunction l E L ι W).unit.app _).val.app U
        (integralOperationsTotalTensorSection l E W n P Q p q U
          (unrestrictedIntegralTensorSection l E W n _ U 1 x)
          (unrestrictedIntegralTensorSection l E W n _ U 1 y))) =
    ((α.app (P, Q)).f (p + q)).val.app U
      (((scalarAdjunction l E L ι W).unit.app _).val.app U
        (integralOperationsTotalTensorSection l E W n P Q p q U
          (unrestrictedIntegralTensorSection l E W n _ U 1 x)
          (unrestrictedIntegralTensorSection l E W n _ U 1 y)))
  have hs := scalarAdjunction_unit l E L ι W
    (((integralOperationsTensorLevel l E W n).obj (P, Q)).X (p + q)) U
    (integralOperationsTotalTensorSection l E W n P Q p q U
      (unrestrictedIntegralTensorSection l E W n _ U 1 x)
      (unrestrictedIntegralTensorSection l E W n _ U 1 y))
  exact (congrArg (((β.app (P, Q)).f (p + q)).val.app U) hs).trans
    (((hβ P Q p q U x y).trans
      (hα P Q p q U x y).symm).trans
        (congrArg (((α.app (P, Q)).f (p + q)).val.app U) hs.symm))

/-- The normalized finite tensor level map.
Source: Stacks 07A4 (blueprint: lem-pur-integral-scalar-finite-comparison-models). -/
def scalarTensorLevel (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    integralOperationsTensorLevel l E W n ⋙
        (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          integralOperationsTensorLevel l L W n :=
  (scalarTensorLevel_existsUnique l E L ι W n).exists.choose

/-- The prescribed representative normalization, retained as a named predicate.
Source: Stacks 07A4, 08J9, 08TC
(blueprint: lem-pur-integral-scalar-finite-comparison-models). -/
def scalarTensorTowerNormalization (W : AlgebraicGeometry.Scheme.{u})
    (α : integralOperationsTensorTowerFunctor l E W ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          integralOperationsTensorTowerFunctor l L W) : Prop :=
  ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ),
        (α.app (P, Q)).app (op n) = (scalarTensorLevel l E L ι W n).app (P, Q)

/-- The tensor level maps respect the specified strict reductions.
Source: Stacks 08TC (blueprint: lem-pur-integral-scalar-finite-comparison-models).
Proof: both consecutive composites send a total tensor generator to the reduction
of its two entries. The uniqueness of scalarTensorLevel identifies those composites.
Iterate consecutive squares for every tower arrow; naturality is componentwise.
The component equations determine the transformation uniquely. -/
theorem scalarTensorTower_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! α : integralOperationsTensorTowerFunctor l E W ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          integralOperationsTensorTowerFunctor l L W,
      scalarTensorTowerNormalization l E L ι W α := by
  simpa only [integralOperationsTensorTowerFunctor, scalarTensorTowerNormalization,
    Prod.forall] using scalarTowerAssembly
    (fun n ↦ integralOperationsTensorLevel l E W n)
    (fun n ↦ integralOperationsTensorLevel l L W n)
    (integralOperationsTensorTransition l E W) (integralOperationsTensorTransition l L W)
    ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ))
    (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)))
    (scalarTensorLevel l E L ι W)
    (integralScalarTensorLevelReduction l E L ι W (scalarTensorLevel l E L ι W)
      (fun n ↦ (scalarTensorLevel_existsUnique l E L ι W n).exists.choose_spec))

/-- The strict scalar tensor tower map.
Source: Stacks 08TC (blueprint: lem-pur-integral-scalar-finite-comparison-models). -/
def scalarTensorTower (W : AlgebraicGeometry.Scheme.{u}) :
    integralOperationsTensorTowerFunctor l E W ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          integralOperationsTensorTowerFunctor l L W :=
  (scalarTensorTower_existsUnique l E L ι W).exists.choose

/-- The tensor chain map is the diagonal Roos map of that strict tower map.
Source: Stacks 07A4, 08TC (blueprint: lem-pur-integral-scalar-finite-comparison-models). -/
def scalarTensorChain (W : AlgebraicGeometry.Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((integralOperationsTensorComplexFunctor l E W).obj (P, Q)) ⟶
      (integralOperationsTensorComplexFunctor l L W).obj
        ((((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P),
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q)) :=
  scalarRoosMap (integralOrdinaryScalar l E L ι W)
      ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)) ≫
    integralOperationsRoosMap ((scalarTensorTower l E L ι W).app (P, Q))

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor scalarPullbackChain scalarTensorChain

/-- Finite free ordinary coefficient extension preserves the good representatives.
Source: Stacks 06YU, 07A4 (blueprint: lem-pur-integral-scalar-finite-comparison-models).
Proof: the object and morphism formulas of integralOrdinaryScalarWitness give
an isomorphism with the concrete changeOfRingsComplex. Convert flatness on the site
to exactness of tensorRight and apply changeOfRings_isKFlat_of_flat_terms. Tensoring
the comparison isomorphism transports K-flatness; its degree components transport
flatness. This general change-of-rings argument needs no finite-free basis and
imposes no equality of site object and arrow sizes. -/
theorem scalarGood (W : AlgebraicGeometry.Scheme.{u})
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
    integralOperationsGoodComplex l L W
      (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P.obj) := by
  let : EssentiallySmall.{u+1} W.ProEt := essentiallySmallSelf.{0} _
  let R := completedIntegralCommRingSheafUnrestricted.{u, u} l E W
  let S := completedIntegralCommRingSheafUnrestricted.{u, u} l L W
  let φ := integralCompletedScalarMap l E L ι W
  let F := integralOrdinaryScalar l E L ι W
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u+1, u, u+1} R
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u+1, u, u+1} S
  let : MonoidalCategory (integralTowerModules l E W) :=
    SheafOfModules.monoidalCategory.{u, u+1, u+1} R
  let : MonoidalCategory (integralTowerModules l L W) :=
    SheafOfModules.monoidalCategory.{u, u+1, u+1} S
  have ho := integralOrdinaryScalar_obj l E L ι W
  let e : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P.obj ≅
      SheafOfModules.changeOfRingsComplex.{u + 1, u} φ P.obj :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ eqToIso (ho (P.obj.X i))) (by
      intro i j hij
      symm
      change F.map (P.obj.d i j) ≫ eqToHom (ho (P.obj.X j)) =
        eqToHom (ho (P.obj.X i)) ≫
          SheafOfModules.changeOfRingsHom φ (P.obj.X i) (P.obj.d i j)
      erw [integralOrdinaryScalar_map l E L ι W (P.obj.d i j)]
      simp
      rfl)
  have hflat (i : ℤ) : exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory.{u, u+1, u+1} R) (P.obj.X i)) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso.{u+1, u, u+1} R (P.obj.X i))
      (P.property.2 i)
  have h := SheafOfModules.changeOfRings_isKFlat_of_flat_terms.{u + 1, u}
    φ P.obj P.property.1 hflat
  constructor
  · let : (MonoidalCategory.curriedTensor
        (integralTowerModules l L W)).PreservesZeroMorphisms :=
      SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients S
    let : ∀ M : integralTowerModules l L W,
        ((MonoidalCategory.curriedTensor _).obj M).PreservesZeroMorphisms :=
      SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients S
    intro A hA i
    let T := ((MonoidalCategory.curriedTensor
      (integralTowerModules l L W)).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)).obj A
    exact (h.1 A hA i).of_iso (T.mapIso e).symm
  · intro i
    let ei := (HomologicalComplex.eval _ _ i).mapIso e
    have hi := (exactFunctor _ _).prop_of_iso
      ((MonoidalCategory.curriedTensor (integralTowerModules l L W)).flip.mapIso ei).symm
      (h.2 i)
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso.{u+1, u, u+1} S
        (((F.mapHomologicalComplex (.up ℤ)).obj P.obj).X i)).symm hi

/-- The prescribed representative normalization, retained as a named predicate.
Source: Stacks 07A4, 08J9, 08TC
(blueprint: lem-pur-integral-scalar-finite-comparison-models). -/
def scalarPullbackOrdinaryNormalization {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y)
    (α : integralDerivedPullback l E f ⋙ integralOrdinaryDerivedScalar l E L ι X ≅
      integralOrdinaryDerivedScalar l E L ι Y ⋙ integralDerivedPullback l L f) : Prop :=
  ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        (integralOrdinaryDerivedScalar l E L ι X).map
            ((integralDerivedPullbackComparison l E f).hom.app P) ≫
          (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app
            ((integralOperationsPullbackComplexFunctor l E f).obj P.obj) ≫
          DerivedCategory.Q.map (scalarPullbackChain l E L ι f P.obj) =
        α.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (integralDerivedPullback l L f).map
            ((integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj) ≫
          (integralDerivedPullbackComparison l L f).hom.app
            ⟨_, scalarGood l E L ι Y P⟩

attribute [local irreducible] constantSheaf limit
  integralDerivedPullback integralCompletedTensor integralScalarExtension
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

end WeilConjectures

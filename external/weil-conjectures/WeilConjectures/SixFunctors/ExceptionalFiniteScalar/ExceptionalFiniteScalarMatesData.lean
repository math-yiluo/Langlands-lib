/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedFiniteExceptionalAt
public import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom
public import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactSupportScalarTransport
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleExceptionalConstantTensor
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorAmplitude
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientFlatModel
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.AlgebraicGeometry.CompactSupportComparisonUnit

/-! # Finite scalar mates for the constructible exceptional adjunction

Source: Zheng, Propositions 2.23, 2.29 and 3.16; Construction 2.26;
Stacks Project, Tags 0GL6, 09AL and 07A4
(blueprint: lem-sf-exceptional-finite-scalar-mates).

## Main definitions

* `Operation`, `Scalar`, `EtaleMates`, and `Construction` retain the actual
  functors, canonical realizations, adjunctions, scalar maps, and shift equations.

## Main statements

* `exceptionalFiniteScalarMates` asserts existence for every finite coefficient map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.ExceptionalFiniteScalar

/-- The existing triangulated closure supplies the inherited subcategory shifts.
Source: blueprint finite-Tor subcategory; Stacks 08G2
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
instance finiteTriangulated (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (T : Scheme.{u}) :
    (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) T).IsTriangulated :=
  (finite_ctf_isTriangulated l E (n + 1) (Nat.succ_pos n) T).2.1

/-- The chosen ordinary etale adjunction at the retained compactification.
Source: Zheng, Proposition 2.23; Stacks 0F5Y
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
def etaleAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  Adjunction.ofIsLeftAdjoint
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)

/-- Abbreviation for the right adjoint already selected by the ordinary adjunction.
Source: Zheng, Proposition 2.23
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
abbrev etaleExceptional (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).rightAdjoint

/-- Canonical realization of the specified-compactification exceptional functor.
Source: blueprint exceptional inverse image; Stacks 09AL
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
def exceptional (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory X A :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
    (ULift.{u + 1, u} A) c
  (sfIntrinsicDerivedEquivalence Y A).inverse ⋙
    ProEtale.sfFiniteExceptionalAt (ULift.{u + 1, u} A) c ⋙
    (sfIntrinsicDerivedEquivalence X A).functor

/-- The compact-support realization in inverse fixed-module coordinates.
Source: Stacks 09AL; the canonical proper/open site realization
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
def leftFixedIso (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X A) :
    (sfIntrinsicDerivedEquivalence Y A).inverse.obj ((sfIntrinsicCompactSupport c A).obj K) ≅
      (ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj
          ((sfIntrinsicDerivedEquivalence X A).inverse.obj K) :=
  (sfIntrinsicDerivedEquivalence Y A).inverse.mapIso
    ((sfIntrinsicCompactSupport c A).mapIso
      ((sfIntrinsicDerivedEquivalence X A).counitIso.app K).symm ≪≫
      (FiniteCompactScalar.compactRealizationIso A c).app
        ((sfIntrinsicDerivedEquivalence X A).inverse.obj K)) ≪≫
    ((sfIntrinsicDerivedEquivalence Y A).unitIso.app _).symm

/-- The actual ambient scalar-adjunction mate of the proper/open restriction square.
Source: Stacks 0GL6, 07A4; Zheng, Construction 2.26
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
def leftScalarMap {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (a : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    sfIntrinsicCompactSupport c A ⋙ pbcDerivedExtend (proEtaleConstantRingMap (T := Y) a) ⟶
      pbcDerivedExtend (proEtaleConstantRingMap (T := X) a) ⋙ sfIntrinsicCompactSupport c B :=
  ((mateEquiv (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := X) a))
    (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := Y) a))).symm
      (TwoSquare.mk _ _ _ _ (sfCompactSupportRestriction c a).hom))

/-- Literal full-subcategory restriction of the ambient scalar extension.
Source: Stacks 06YY and 09AL; finite scalar construction, step 2
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
def restrictScalar
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ) (T : Scheme.{u})
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    (h : ∀ K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) T,
      finiteTorConstructible l L (m + 1) (Nat.succ_pos m) T
        ((pbcDerivedExtend (proEtaleConstantRingMap (T := T) a)).obj K.obj)) :
    finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) T ⥤
      finiteTorConstructibleCategory l L (m + 1) (Nat.succ_pos m) T :=
  (finiteTorConstructible l L (m + 1) (Nat.succ_pos m) T).lift
    ((finiteTorConstructible l E (n + 1) (Nat.succ_pos n) T).ι ⋙
      pbcDerivedExtend (proEtaleConstantRingMap (T := T) a)) h

/-- Expose the existing composite shift in the intrinsic compact-support coordinates.
Source: Stacks 03DI and 070K; exact open descent and K-injective proper image
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
instance compactShift (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (sfIntrinsicCompactSupport c A).CommShift ℤ :=
  inferInstanceAs (((sfIntrinsicExtensionByZero c.i A).mapDerivedCategory ⋙
    proEtaleConstantDerivedDirectImage c.g A).CommShift ℤ)

/-- The finite operation with its actual realizations and transported adjunction.
The last field specifies the Hom bijection for every retained etale-origin witness.
Source: Zheng, Proposition 2.23; Stacks 09AL; finite construction, step 6
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
structure Operation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c : Compactification f) where
  F : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) X ⥤
    finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) Y
  G : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) Y ⥤
    finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) X
  left : F ⋙ (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) Y).ι ≅
    (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X).ι ⋙
      sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))
  right : G ⋙ (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X).ι ≅
    (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) Y).ι ⋙
      exceptional (Padic.coefficientExtensionRing l E (n + 1)) c
  adjunction : F ⊣ G
  [leftShift : F.CommShift ℤ]
  [rightShift : G.CommShift ℤ]
  unitShift : adjunction.unit.CommShift ℤ
  counitShift : adjunction.counit.CommShift ℤ
  leftShiftRealization : left.hom.CommShift ℤ
  normalized (hY : CompactSpace Y)
    (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) X)
    (N : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) Y)
    (hK : DerivedCategory.TStructure.t.plus
      ((sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj
        K.obj))
    (hN : DerivedCategory.TStructure.t.plus
      ((sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj
        N.obj))
    (W : X.FixedEtaleOriginWitness (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E (n + 1))) ⟨_, hK⟩)
    (v : F.obj K ⟶ N) :
    (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X).ι.map
        (adjunction.homEquiv K N v) ≫ right.hom.app N =
      ((sfIntrinsicDerivedEquivalence X
        (Padic.coefficientExtensionRing l E (n + 1))).counitIso.app K.obj).inv ≫
        (sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (n + 1))).functor.map
          (@ProEtale.specifiedExceptionalHomEquiv _ _ _ _ _ _ _ hY c
            (Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) c)
            ⟨_, hK⟩ W ⟨_, hN⟩
            ((leftFixedIso (Padic.coefficientExtensionRing l E (n + 1)) c K.obj).inv ≫
              (sfIntrinsicDerivedEquivalence Y
                (Padic.coefficientExtensionRing l E (n + 1))).inverse.map
                  (left.inv.app K ≫
                    (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) Y).ι.map v)))

attribute [instance] Operation.leftShift Operation.rightShift

/-- The canonical restriction comparison for exceptional right adjoints: the
right-adjoint uniqueness isomorphism of the scalar/exceptional Hom chain.
Source: Zheng, Proposition 2.23; Stacks 0GL6; finite scalar proof, step 4
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
def restrictionIso {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (a : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (q : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        Etale.scalarExtension a Y ≅ Etale.scalarExtension a X ⋙
          Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c) :
    (etaleExceptional B c) ⋙ Sheaf.derivedRestrictScalars X.smallEtaleTopology a ≅
      Sheaf.derivedRestrictScalars Y.smallEtaleTopology a ⋙ (etaleExceptional A c) :=
  ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology a)).comp
        (etaleAdjunction B c)).rightAdjointUniq
    (((etaleAdjunction A c).comp (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a))).ofNatIsoLeft q)

/-- The scalar shift adjoint to the exact termwise restriction shift.
Source: Stacks 06YY; adjoint shift normalization
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
instance etaleScalarShift {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) (T : Scheme.{u}) : (Etale.scalarExtension a T).CommShift ℤ :=
  (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology a)).leftAdjointCommShift ℤ

/-- Ambient etale realizations of the two scalar mates and the constant-B tensor
calculation. The projection is the existing ordered projection followed by the
canonical pullback of the constant coefficient complex. Its inverse therefore gives
exactly the constant-coefficient exceptional tensor transpose, even for nonflat B.
Source: Zheng, Construction 2.26 and Proposition 2.29(2); Stacks 0GL6
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
structure EtaleMates {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (a : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) where
  q : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
      Etale.scalarExtension a Y ≅ Etale.scalarExtension a X ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c
  q_normalized : q.hom = Etale.compactScalarMap a c
  properShift : (Etale.scalarMate a c.g).CommShift ℤ
  openShift : (Etale.ExceptionalCoefficients.openIso a c.i).hom.CommShift ℤ
  b : (etaleExceptional A c) ⋙ Etale.scalarExtension a X ≅
    Etale.scalarExtension a Y ⋙ (etaleExceptional B c)
  b_normalized : b.hom =
    (mateEquiv (etaleAdjunction A c) (etaleAdjunction B c)
      (TwoSquare.mk _ _ _ _ q.inv))
  projection :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        Etale.scalarExtension a Y ⋙ Sheaf.derivedRestrictScalars Y.smallEtaleTopology a ≅
      (Etale.scalarExtension a X ⋙ Sheaf.derivedRestrictScalars X.smallEtaleTopology a) ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  projection_normalized (K : Etale.DerivedCategoryModule A X) :
    projection.hom.app K =
      (Etale.scalarTensorIso a Y).hom.app
          ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K) ≫
        ((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app K).app
          (Etale.scalarCoefficient a Y) ≫
        (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj K).map
              (Etale.scalarCoefficientPullbackIso a f).hom ≫
            (Etale.scalarTensorIso a X).inv.app K)
  projectionShift : projection.hom.CommShift ℤ
  restricted_b (N : Etale.DerivedCategoryModule A Y) :
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology a).map (b.hom.app N) ≫
        (restrictionIso a c q).hom.app ((Etale.scalarExtension a Y).obj N) =
      (etaleAdjunction A c).homEquiv _ _
        (projection.inv.app ((etaleExceptional A c).obj N) ≫
          (Etale.scalarExtension a Y ⋙ Sheaf.derivedRestrictScalars
            Y.smallEtaleTopology a).map ((etaleAdjunction A c).counit.app N))

/-- Scalar preservation, its unchanged Tor interval, and the literal restricted
functor with the equality realization. Shift compatibility is imposed on that
realization, so the restricted shift is inherited from the ambient derived tensor.
Source: Stacks 06YY, 09AL and 07A4; finite scalar construction, steps 1--2
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
structure Scalar
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1)) (T : Scheme.{u}) where
  preserves (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) T) :
    finiteTorConstructible l L (m + 1) (Nat.succ_pos m) T
      ((pbcDerivedExtend (proEtaleConstantRingMap (T := T) a)).obj K.obj)
  torInterval (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) T) (r s : ℤ) :
    HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E (n + 1)) K.obj r s →
      HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l L (m + 1))
        ((pbcDerivedExtend (proEtaleConstantRingMap (T := T) a)).obj K.obj) r s
  scalar_eq : restrictScalar l E L n m T a preserves ⋙
      (finiteTorConstructible l L (m + 1) (Nat.succ_pos m) T).ι =
    (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) T).ι ⋙
      pbcDerivedExtend (proEtaleConstantRingMap (T := T) a)
  [commShift : (restrictScalar l E L n m T a preserves).CommShift ℤ]
  realizationShift : (eqToIso scalar_eq).hom.CommShift ℤ

/-- The literal restricted functor, with its scalar package visible for instance search.
Source: Stacks 06YY, 09AL (blueprint: lem-sf-exceptional-finite-scalar-mates). -/
def Scalar.functor
    {l : ℕ} [Fact l.Prime]
    {E L : Type u} [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    {n m : ℕ}
    {a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1)} {T : Scheme.{u}}
    (S : Scalar l E L n m a T) :=
  restrictScalar l E L n m T a S.preserves

/-- The shift structure retained by the scalar package.
Source: Stacks 06YY, 09AL (blueprint: lem-sf-exceptional-finite-scalar-mates). -/
instance Scalar.functorShift
    {l : ℕ} [Fact l.Prime]
    {E L : Type u} [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    {n m : ℕ}
    {a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1)} {T : Scheme.{u}}
    (S : Scalar l E L n m a T) : S.functor.CommShift ℤ := S.commShift

/-- All finite scalar conclusions on the actual full subcategories. Every ring map is
retained, rather than only an inductively generated list of coefficient changes.
Source: Zheng, Propositions 2.23 and 2.29; Stacks 09AL, 0GL6 and 07A4
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
structure Construction
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f) where
  scalarX : Scalar l E L n m a X
  scalarY : Scalar l E L n m a Y
  source : Operation l E n c
  target : Operation l L m c
  q : source.F ⋙ scalarY.functor ≅
    scalarX.functor ⋙ target.F
  b : source.G ⋙ scalarX.functor ≅
    scalarY.functor ⋙ target.G
  q_normalized (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) X) :
    (finiteTorConstructible l L (m + 1) (Nat.succ_pos m) Y).ι.map (q.hom.app K) ≫
        target.left.hom.app ((scalarX.functor).obj K) =
      (pbcDerivedExtend (proEtaleConstantRingMap (T := Y) a)).map (source.left.hom.app K) ≫
        (leftScalarMap a c).app K.obj
  counit (N : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) Y) :
    q.hom.app (source.G.obj N) ≫ target.F.map (b.hom.app N) ≫
        target.adjunction.counit.app
          ((scalarY.functor).obj N) =
      (scalarY.functor).map (source.adjunction.counit.app N)
  qShift : q.hom.CommShift ℤ
  bShift : b.hom.CommShift ℤ
  etale : EtaleMates (RingHom.ulift.{u + 1, u + 1} a) c

/-- The data left after the scalar packages and the two finite operations are chosen.
Source: Zheng, Construction 2.26 and Proposition 2.29; Stacks 0GL6 and 09AL
(blueprint: lem-sf-exceptional-finite-scalar-mates).

The proof is the ambient proper/open scalar-mate construction, transported through
the selected finite-Tor full subcategories.  In particular, it includes the
normalization equations and both adjoint shift equations required by `Construction`.
-/
structure ConstructionMaps
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f)
    (scalarX : Scalar l E L n m a X) (scalarY : Scalar l E L n m a Y)
    (source : Operation l E n c) (target : Operation l L m c) where
  q : source.F ⋙ scalarY.functor ≅ scalarX.functor ⋙ target.F
  b : source.G ⋙ scalarX.functor ≅ scalarY.functor ⋙ target.G
  q_normalized (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) X) :
    ((finiteTorConstructible l L (m + 1) (Nat.succ_pos m) Y).ι).map (q.hom.app K) ≫
        target.left.hom.app ((scalarX.functor).obj K) =
      (pbcDerivedExtend (proEtaleConstantRingMap (T := Y) a)).map (source.left.hom.app K) ≫
        (leftScalarMap a c).app K.obj
  counit (N : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) Y) :
    q.hom.app (source.G.obj N) ≫ target.F.map (b.hom.app N) ≫
        target.adjunction.counit.app ((scalarY.functor).obj N) =
      (scalarY.functor).map (source.adjunction.counit.app N)
  qShift : q.hom.CommShift ℤ
  bShift : b.hom.CommShift ℤ
  etale : EtaleMates (RingHom.ulift.{u + 1, u + 1} a) c

end WeilConjectures.ExceptionalFiniteScalar

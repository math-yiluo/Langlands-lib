/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.SequenceSiteCompletionProjectionSupplement
public import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
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
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.CategoryTheory.K.KInjectiveDerivedMapComputation
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.Algebra.Homology.SequenceProjection.SequenceProjectionDerivedAdjunction
import WeilConjectures.Algebra.Homology.SequenceProjection.SequencePushforwardLimitProjections
import WeilConjectures.CategoryTheory.SixFunctors.ResolvingDerivedAdjunction
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
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
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
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
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic

/-! # Resolution-normalized sequence-site adjoints

Source: blueprint main-20261015, `sec-six-functors/sk-thm-sf-package/`
`fix-prop-coherence.proof.md`, coefficient-comparison sentence; Stacks 0940,
0941, 03D7, 06YY, 07A6 and 0D6E
(blueprint: def-pur-sequence-adjoint-resolution-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u c v d z
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory
namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  coefficientSequenceRestriction
  coefficientSequenceEvaluation coefficientFiniteDerivedExtension scalarReductionExtension

/-- Read a supplied coherent shift structure without file-local instances.
Source: cochain shift convention, Stacks 0A8D
(blueprint: def-pur-sequence-adjoint-resolution-data). -/
def purSequenceShiftIso {C : Type c} {D : Type d} [Category.{v} C] [Category.{z} D]
    [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) (h : F.CommShift ℤ) (r : ℤ) :
    shiftFunctor C r ⋙ F ≅ F ⋙ shiftFunctor D r :=
  letI := h
  F.commShiftIso r

/-- The ordinary unit-shift equation, with explicit functor and shift parameters.
Source: Stacks 06YY and Mathlib's adjunction shift convention
(blueprint: def-pur-sequence-adjoint-resolution-data). -/
def purSequenceUnitShiftCompatibility
    {C : Type c} {D : Type d} [Category.{v} C] [Category.{z} D]
    [HasShift C ℤ] [HasShift D ℤ] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) (hF : F.CommShift ℤ) (hG : G.CommShift ℤ) (r : ℤ) : Prop :=
  Adjunction.CommShift.CompatibilityUnit adj
    (purSequenceShiftIso F hF r) (purSequenceShiftIso G hG r)

/-- The ordinary counit-shift equation, with explicit functor and shift parameters.
Source: Stacks 06YY and Mathlib's adjunction shift convention
(blueprint: def-pur-sequence-adjoint-resolution-data). -/
def purSequenceCounitShiftCompatibility
    {C : Type c} {D : Type d} [Category.{v} C] [Category.{z} D]
    [HasShift C ℤ] [HasShift D ℤ] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) (hF : F.CommShift ℤ) (hG : G.CommShift ℤ) (r : ℤ) : Prop :=
  Adjunction.CommShift.CompatibilityCounit adj
    (purSequenceShiftIso F hF r) (purSequenceShiftIso G hG r)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The completed ring, retaining exactly its recorded module category.
Source: Stacks 0940 (blueprint: def-pur-sequence-adjoint-resolution-data). -/
abbrev purSequenceBaseRing :=
  SheafOfModules.derivedChangeRingIndependentCoefficients
    (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)

/-- The actual quotient ring on the sequence site, with commutativity forgotten.
Source: Stacks 0941 (blueprint: def-pur-sequence-adjoint-resolution-data). -/
abbrev purSequenceQuotientRing :=
  (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (coefficientSequenceCommRingSheaf l E W)

/-- The constant completed ring on the same sequence site.
Source: Stacks 0940 (blueprint: def-pur-sequence-adjoint-resolution-data). -/
abbrev purSequenceConstantRing :=
  (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (SheafOfModules.systemSequenceRing.{t + 1, t, max u (t + 1)}
        (C := W.ProEt) (J := Scheme.ProEt.topology W)
        ((Functor.const ℕᵒᵖ).obj (completedIntegralCommRingSheafUnrestricted l E W)))

/-- The constant-system functor at the underlying presheaf level. A geometric
inverse image below is identified with this functor, on objects and maps.
Source: Stacks 0940 (blueprint: def-pur-sequence-adjoint-resolution-data). -/
abbrev purSequenceConstantPresheaf :=
  sheafToPresheaf (Scheme.ProEt.topology W) (Type (max u (t + 1))) ⋙
    (Functor.whiskeringLeft (ℕ × W.ProEt)ᵒᵖ W.ProEtᵒᵖ
      (Type (max u (t + 1)))).obj (CategoryTheory.Prod.snd ℕ W.ProEt).op

/-- The recorded ordinary scalar adjunction, with its large unit characterization hidden
behind its actual adjunction type. Source: Stacks 03D7
(blueprint: def-pur-sequence-adjoint-resolution-data). -/
def purSequenceFiniteAdjunction (n : ℕ) :
    scalarReductionExtension l E W n ⊣ scalarReductionRestriction l E W n :=
  (scalarReductionExtension_adjunction l E W n).choose

/-- The existing K-injective model of the constant-tower total limit, with
its declared codomain retained explicitly. Source: Stacks 0941
(blueprint: def-pur-sequence-adjoint-resolution-data). -/
def purSequenceTowerLimitModel
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [J.IsKInjective] :
    (coefficientConstantTowerLimit l E W).obj (DerivedCategory.Q.obj J) ≅
      DerivedCategory.Q.obj (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
        scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).obj J) :=
  Functor.rightDerivedFunctorObjQIso
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) J

attribute [local irreducible] coefficientConstantTowerLimit coefficientSequenceLimit

/-- Ordinary tensor/limit adjoints and their geometric ringed projection.
All displayed section maps use the actual quotient and completed-ring projections.
Source: Stacks 0940, 0941 and 03D7
(blueprint: def-pur-sequence-adjoint-resolution-data). -/
structure PurSequenceOrdinaryAdjoints where
  p : RingedToposMorphismOfUniverses (C := ℕ × W.ProEt) (D := W.ProEt)
    (purSequenceQuotientRing l E W) (purSequenceBaseRing l E W)
  constant : p.inverse ⋙ sheafToPresheaf
    (coefficientSequenceTopology (Scheme.ProEt.topology W)) (Type (max u (t + 1))) ≅
      purSequenceConstantPresheaf.{t, u} W
  quotient : ∀ (n : ℕ) (V : W.ProEtᵒᵖ)
    (x : (p.inverse.obj ((sheafCompose (Scheme.ProEt.topology W)
      (forget RingCat)).obj (purSequenceBaseRing l E W))).obj.obj (op (n, V.unop))),
    p.ringMap.hom.app (op (n, V.unop)) x =
      (completedIntegralCommRingProjectionUnrestricted l E W n).hom.app V
        ((constant.hom.app ((sheafCompose (Scheme.ProEt.topology W)
          (forget RingCat)).obj (purSequenceBaseRing l E W))).app (op (n, V.unop)) x)
  pullback : scalarReductionSource l E W ⥤ coefficientSequenceModules l E W
  pullback_additive : pullback.Additive
  adjunction : pullback ⊣ p.modules
  limit : p.modules ≅ coefficientSequenceRestriction l E W ⋙
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
  tensor : ∀ n : ℕ,
    pullback ⋙ coefficientSequenceEvaluation l E W n ≅ scalarReductionExtension l E W n
  tensor_transition : ∀ (M : scalarReductionSource l E W) (m n : ℕ) (h : n ≤ m),
    (coefficientSequenceTransition l E W h).app (pullback.obj M) ≫
      (normalizedDVRModuleRes l E W h).map ((tensor n).hom.app M) =
    (tensor m).hom.app M ≫ (coefficientOrdinaryQuotient l E W h).app M
  projection : ∀ (N : coefficientSequenceModules l E W) (n : ℕ),
    p.modules.obj N ⟶ (scalarReductionRestriction l E W n).obj
      ((coefficientSequenceEvaluation l E W n).obj N)
  projection_limit : ∀ (N : coefficientSequenceModules l E W) (n : ℕ),
    projection N n = limit.hom.app N ≫ CategoryTheory.Limits.limit.π
      ((coefficientSequenceRestriction l E W).obj N) (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app N
  transpose : ∀ (M : scalarReductionSource l E W) (N : coefficientSequenceModules l E W)
    (h : M ⟶ p.modules.obj N) (n : ℕ),
    ((purSequenceFiniteAdjunction l E W n).homEquiv M
      ((coefficientSequenceEvaluation l E W n).obj N))
        ((tensor n).inv.app M ≫ (coefficientSequenceEvaluation l E W n).map
          ((adjunction.homEquiv M N).symm h)) = h ≫ projection N n

attribute [instance] PurSequenceOrdinaryAdjoints.pullback_additive

/-- Universal derived pairs, their specified adjunction and the normalized
comparison with the supplied coefficient calculus. The `model` field is fixed
by its equation, for every simultaneous replacement, rather than freely chosen.
Source: Stacks 06YY, 07A6, 0941 and 0D6E
(blueprint: def-pur-sequence-adjoint-resolution-data). -/
structure PurSequenceDerivedAdjoints
    (S : CoefficientDerivedSystemCalculus l E W)
    (O : PurSequenceOrdinaryAdjoints l E W) where
  L : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W
  R : coefficientSequenceDerived l E W ⥤ DerivedCategory (scalarReductionSource l E W)
  ε : DerivedCategory.Q ⋙ L ⟶
    O.pullback.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  η : O.p.modules.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ R
  left_derived : L.IsLeftDerivedFunctor ε
    (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ))
  right_derived : R.IsRightDerivedFunctor η
    (HomologicalComplex.quasiIso (coefficientSequenceModules l E W) (.up ℤ))
  adjunction : L ⊣ R
  left : L ≅ S.reduction
  right : R ≅ coefficientSequenceLimit l E W
  left_model : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q),
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
        (Q.X i)) →
    ∃ e : S.reduction.obj (DerivedCategory.Q.obj Q) ≅
      DerivedCategory.Q.obj ((O.pullback.mapHomologicalComplex (.up ℤ)).obj Q),
      ε.app Q = left.hom.app (DerivedCategory.Q.obj Q) ≫ e.hom ∧
      CoefficientReductionPresentation l E W S.toCoefficientDerivedSystemReduction Q hQ
        ((O.pullback.mapHomologicalComplex (.up ℤ)).obj Q) e
        (fun n ↦ (NatIso.mapHomologicalComplex (O.tensor n) (.up ℤ)).app Q)
  right_model : ∀ I : CochainComplex (coefficientSequenceModules l E W) ℤ,
    I.IsKInjective → IsIso (η.app I)
  hom_normalization : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (f : (O.pullback.mapHomologicalComplex (.up ℤ)).obj Q ⟶ I),
    adjunction.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
      (ε.app Q ≫ DerivedCategory.Q.map f) =
    DerivedCategory.Q.map ((O.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
      η.app I
  unit : ∀ P : DerivedCategory (scalarReductionSource l E W),
    adjunction.unit.app P ≫ R.map (left.hom.app P) ≫
      right.hom.app (S.reduction.obj P) = S.adjunction.unit.app P
  counit : ∀ N : coefficientSequenceDerived l E W,
    left.hom.app (R.obj N) ≫ S.reduction.map (right.hom.app N) ≫
      S.adjunction.counit.app N = adjunction.counit.app N
  model : ∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj N ⟶ J)
    [J.IsKInjective] [QuasiIso j],
    (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj N) ≅
      DerivedCategory.Q.obj (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
        scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).obj J)
  model_eq : ∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj N ⟶ J)
    [J.IsKInjective] [QuasiIso j],
    HEq (model N J j) ((coefficientConstantTowerLimit l E W).mapIso
      ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.app N ≪≫
        asIso (DerivedCategory.Q.map j)) ≪≫
      purSequenceTowerLimitModel l E W J)
  composition_model : ∀ (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
    [I.IsKInjective] (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    [J.IsKInjective]
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j],
    QuasiIso (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).map j) ∧
    η.app I ≫ right.hom.app (DerivedCategory.Q.obj I) ≫ (model I J j).hom =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex O.limit (.up ℤ)).hom.app I) ≫
      DerivedCategory.Q.map (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
        scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).map j)

/-- The ringed factorization through the constant completed ring. Its tower
comparison is normalized on unchanged underlying sections and horizontal maps.
Source: Stacks 0940 and 0D6E
(blueprint: def-pur-sequence-adjoint-resolution-data). -/
structure PurSequenceRingedFactorization (O : PurSequenceOrdinaryAdjoints l E W) where
  a : RingedToposMorphismOfUniverses (C := ℕ × W.ProEt) (D := ℕ × W.ProEt)
    (purSequenceQuotientRing l E W) (purSequenceConstantRing l E W)
  g : RingedToposMorphismOfUniverses (C := ℕ × W.ProEt) (D := W.ProEt)
    (purSequenceConstantRing l E W) (purSequenceBaseRing l E W)
  a_identity : a.inverse ≅ 𝟭 _
  g_constant : g.inverse ⋙ sheafToPresheaf
    (coefficientSequenceTopology (Scheme.ProEt.topology W)) (Type (max u (t + 1))) ≅
      purSequenceConstantPresheaf.{t, u} W
  a_quotient : ∀ (n : ℕ) (V : W.ProEtᵒᵖ)
    (x : (a.inverse.obj ((sheafCompose
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (forget RingCat)).obj (purSequenceConstantRing l E W))).obj.obj (op (n, V.unop))),
    a.ringMap.hom.app (op (n, V.unop)) x =
      (completedIntegralCommRingProjectionUnrestricted l E W n).hom.app V
        ((a_identity.hom.app ((sheafCompose
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (forget RingCat)).obj (purSequenceConstantRing l E W))).hom.app
            (op (n, V.unop)) x)
  g_ring : ∀ (n : ℕ) (V : W.ProEtᵒᵖ)
    (x : (g.inverse.obj ((sheafCompose (Scheme.ProEt.topology W)
      (forget RingCat)).obj (purSequenceBaseRing l E W))).obj.obj (op (n, V.unop))),
    g.ringMap.hom.app (op (n, V.unop)) x =
      (g_constant.hom.app ((sheafCompose (Scheme.ProEt.topology W)
        (forget RingCat)).obj (purSequenceBaseRing l E W))).app (op (n, V.unop)) x
  inverse_comp : O.p.inverse ≅ g.inverse ⋙ a.inverse
  direct_comp : O.p.direct ≅ a.direct ⋙ g.direct
  ring_comp : O.p.ringMap =
    inverse_comp.hom.app ((sheafCompose (Scheme.ProEt.topology W)
      (forget RingCat)).obj (purSequenceBaseRing l E W)) ≫
      a.inverse.map g.ringMap ≫ a.ringMap
  modules_comp : O.p.modules ≅ a.modules ⋙ g.modules
  towers : ringedSiteModules.{max u (t + 1)} (purSequenceConstantRing l E W) ≌
    (ℕᵒᵖ ⥤ scalarReductionSource l E W)
  evaluation : ∀ n : ℕ,
    towers.functor ⋙ (CategoryTheory.evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj
      (op n) ≅ SheafOfModules.systemSequenceEvaluation
        ((Functor.const ℕᵒᵖ).obj (completedIntegralCommRingSheafUnrestricted l E W)) n
  sections : ∀ (N : ringedSiteModules.{max u (t + 1)} (purSequenceConstantRing l E W))
    (n : ℕ) (V : W.ProEtᵒᵖ),
    HEq (fun x : ((towers.functor.obj N).obj (op n)).val.obj V ↦
      ((evaluation n).hom.app N).val.app V x)
      (fun x : N.val.obj (op (n, V.unop)) ↦ x)
  transitions : ∀ (N : ringedSiteModules.{max u (t + 1)} (purSequenceConstantRing l E W))
    (m n : ℕ) (h : n ≤ m) (V : W.ProEtᵒᵖ),
    HEq (fun x : ((towers.functor.obj N).obj (op m)).val.obj V ↦
      (((towers.functor.obj N).map (homOfLE h).op).val.app V) x)
      (fun x : N.val.obj (op (m, V.unop)) ↦
        N.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x)
  restriction : a.modules ⋙ towers.functor ≅ coefficientSequenceRestriction l E W
  limit : g.modules ≅ towers.functor ⋙
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
  exact_limits : PreservesFiniteLimits a.modules
  exact_colimits : PreservesFiniteColimits a.modules

/-- The geometric, ordinary and derived resolution identifications, before the
shift-coherence assertions. Source: Stacks 0940, 03D7, 06YY and 0D6E
(blueprint: def-pur-sequence-adjoint-resolution-data). -/
structure PurSequenceResolutionData (S : CoefficientDerivedSystemCalculus l E W) where
  ordinary : PurSequenceOrdinaryAdjoints l E W
  factorization : PurSequenceRingedFactorization l E W ordinary
  derived : PurSequenceDerivedAdjoints l E W S ordinary

end WeilConjectures

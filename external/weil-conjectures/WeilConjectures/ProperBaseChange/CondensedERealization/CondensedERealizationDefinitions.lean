/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.CategoryTheory.ScalarLocalization.PbcRationalTransport
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientImmersionRestriction
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedExchangeCoherence
public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import Mathlib.Topology.Connected.TotallyDisconnected
public import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
public import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
public import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
import WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import Mathlib.Algebra.Category.ModuleCat.Basic
import WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Ab
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic
import WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.Analysis.Normed.Field.TransferInstance

/-!
# Realization of rationalized integral coefficients in condensed E-module objects

Source: Bhatt--Scholze, Lemmas 4.2.12--4.2.13, Proposition 6.8.14(2), Remark 6.8.15,
and the archived module-object definitions (blueprint: lem-weil-pbc-condensed-e-realization).
The auxiliary records retain the coefficient maps and every comparison, including the
normalization of the ordered completed exchange. No exchange is asserted to be invertible.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.mathlibStandardSet false
set_option linter.style.setOption false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] _root_.instCategoryDerivedCategory
  AlgebraicGeometry.ProEtale.upperStar CategoryTheory.Functor.mapMod
  DerivedCategory.homologyFunctor CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed

attribute [local irreducible]
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStar
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerStar
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStarLowerStarAdjunction
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStarComp

set_option allowUnsafeReducibility true in
attribute [local reducible] AlgebraicGeometry.Scheme.completedReductionCoefficient
  AlgebraicGeometry.Scheme.reductionCoefficientSystem
  AlgebraicGeometry.Scheme.reductionModulesHasDerivedCategory
  AlgebraicGeometry.Scheme.reductionRingModulesHasDerivedCategory
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory

attribute [local instance 40000] AlgebraicGeometry.Scheme.reductionRingModulesHasDerivedCategory

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.CondensedERealization

/-- Packaging of the geometric hypotheses, without a choice of coefficient object.
Source: Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-condensed-e-realization). -/
structure Base (k : Type u) [Field k] where
  scheme : Scheme.{u}
  [«over» : scheme.Over (Spec (.of k))]
  [finiteType : LocallyOfFiniteType (scheme ↘ Spec (.of k))]
  [quasiCompact : QuasiCompact (scheme ↘ Spec (.of k))]
  [separated : IsSeparated (scheme ↘ Spec (.of k))]

attribute [instance] Base.«over» Base.finiteType Base.quasiCompact Base.separated

/-- The same geometric datum as a bundled scheme over its base field.
Source: BS 6.8.14(2) (blueprint: lem-weil-pbc-condensed-e-realization). -/
abbrev Base.model {k : Type u} [Field k] (T : Base k) : Over (Spec (.of k)) :=
  Over.mk (T.scheme ↘ Spec (.of k))

/-- Finite type of the same bundled structural morphism.
Source: BS 6.8.14(2) (blueprint: lem-weil-pbc-condensed-e-realization). -/
instance Base.modelFinite {k : Type u} [Field k] (T : Base k) :
    LocallyOfFiniteType T.model.hom := T.finiteType

/-- Quasi-compactness of the same bundled structural morphism.
Source: BS 6.8.14(2) (blueprint: lem-weil-pbc-condensed-e-realization). -/
instance Base.modelQuasiCompact {k : Type u} [Field k] (T : Base k) :
    QuasiCompact T.model.hom := T.quasiCompact

/-- Separatedness of the same bundled structural morphism.
Source: BS 6.8.14(2) (blueprint: lem-weil-pbc-condensed-e-realization). -/
instance Base.modelSeparated {k : Type u} [Field k] (T : Base k) :
    IsSeparated T.model.hom := T.separated

/-- The same base-preserving morphism in the bundled over category.
Source: BS 6.8.14(2) (blueprint: lem-weil-pbc-condensed-e-realization). -/
def Base.map {k : Type u} [Field k] (T U : Base k)
    (h : T.scheme ⟶ U.scheme) [h.IsOver (Spec (.of k))] : T.model ⟶ U.model :=
  Over.homMk h (comp_over h (Spec (.of k)))

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]

/-- The recorded integral full subcategory; only notation is shortened here.
Source: Bhatt--Scholze, Definition 6.8.8
(blueprint: lem-weil-pbc-condensed-e-realization). -/
abbrev Integral (T : Scheme.{u}) := PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)

/-- The recorded raw scalar localization, with no idempotent completion.
Source: Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-condensed-e-realization). -/
abbrev Rational (T : Scheme.{u}) :=
  PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)

/-- The original continuous condensed coefficient object in the scheme universe.
Source: archived ModuleObject/Basic.lean
(blueprint: lem-weil-pbc-condensed-e-realization). -/
abbrev Coefficient (T : Scheme.{u}) :=
  condensedRingObj (Profinite.continuousCoefficientRingObj E) T

/-- The archived ambient derived category, before imposing constructibility.
Source: archived ProEtaleModule/DerivedCategory.lean
(blueprint: lem-weil-pbc-condensed-e-realization). -/
abbrev Ambient (T : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (Coefficient E T))

/-- The archived bounded constructible category, retaining its local presentation condition.
Source: archived ProEtaleModule/DerivedCategory.lean
(blueprint: lem-weil-pbc-condensed-e-realization). -/
abbrev Constructible (T : Scheme.{u}) := BoundedConstructible (Coefficient E T)

/-- The reconstructed section ring of the actual internal coefficient object.
Source: Stacks Tag 00YV
(blueprint: lem-weil-pbc-condensed-e-realization). -/
abbrev SectionRing (T : Scheme.{u}) :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology T) (Coefficient E T)

/-- Constant continuous E-valued functions give the canonical scalar sections.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-condensed-e-realization). -/
def fieldScalarSections (T : Scheme.{u}) :
    E →+* RingCat.sectionsSubring
      ((rationalCoefficientSheaf l T E).obj ⋙ forget₂ CommRingCat RingCat) := by
  letI := coefficientExtensionNormedField l E
  exact
    { toFun := fun a ↦ ⟨fun _ ↦ ContinuousMap.const _ (ULift.up a), fun _ ↦ rfl⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

/-- Scalar multiplication on sectionwise continuous E-module sheaves is pointwise.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-condensed-e-realization). -/
instance fieldModuleLinear (T : Scheme.{u}) :
    Linear E (pbcModules T (rationalCoefficientSheaf l T E)) :=
  letI : Linear (RingCat.sectionsSubring
      ((rationalCoefficientSheaf l T E).obj ⋙ forget₂ CommRingCat RingCat))
      (pbcModules T (rationalCoefficientSheaf l T E)) :=
    SheafOfModules.homLinear (rationalCoefficientSheaf l T E).obj
    (((adicLisseForget T).obj (rationalCoefficientSheaf l T E)).property)
  { homModule := fun M N ↦ Module.compHom (M ⟶ N) (fieldScalarSections l E T)
    smul_comp := fun M N P a f g ↦
      Linear.smul_comp M N P (fieldScalarSections l E T a) f g
    comp_smul := fun M N P f a g ↦
      Linear.comp_smul M N P f (fieldScalarSections l E T a) g }

/-- The derived E-action is inherited from pointwise scalar multiplication on sheaves.
Source: Bhatt--Scholze, Section 6.8
(blueprint: lem-weil-pbc-condensed-e-realization). -/
instance fieldDerivedLinear (T : Scheme.{u}) :
    Linear E (DerivedCategory (pbcModules T (rationalCoefficientSheaf l T E))) := inferInstance

/-- Encode the internal module action and transport along the given coefficient isomorphism.
Both functors are the existing explicit sectionwise equivalences.
Source: Stacks Tag 00YV
(blueprint: lem-weil-pbc-condensed-e-realization). -/
def moduleEncoding (T : Scheme.{u})
    (e : SectionRing E T ≅ rationalCoefficientSheaf l T E) :
    Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (Coefficient E T) ≌
      pbcModules T (rationalCoefficientSheaf l T E) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (ProEt.topology T)
    (Coefficient E T)).trans
      (ringModuleEquivalenceOfIso T ((adicLisseForget T).mapIso e).symm)

attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.pbcCompletedModulesLinear
  AlgebraicGeometry.Scheme.pbcCompletedDerivedLinear
  AlgebraicGeometry.Scheme.pbcIntegralLinear
  moduleEncoding fieldScalarSections fieldModuleLinear fieldDerivedLinear

/-- Coefficient and scalar-extension data at one scheme. All auxiliary coefficient maps
are normalized on functions or on the generating constant sections of finite quotients;
the equivalence is required to be induced by the actual derived scalar extension.
Source: Bhatt--Scholze, Lemmas 4.2.12--4.2.13 and Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-condensed-e-realization). -/
structure At (T : Scheme.{u}) where
  coefficientIso : Mon.mk (Coefficient E T) ≅
    Mon.mk ((sheafCompose (ProEt.topology T) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (AlgebraicGeometry.ProEtale.continuousCoefficientRingSheaf T E))
  coefficient_normalization : ∀ (S : Profinite.{u}) (f : C(S, E)),
    (((pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ T))).homEquiv
        _ _ coefficientIso.hom.hom).hom.app (op S)) (ULift.up f) =
      ULift.up (f.comp (profiniteTestProjection T S))
  sectionIso : SectionRing E T ≅ rationalCoefficientSheaf l T E
  section_normalization : ∀ (U : T.ProEtᵒᵖ) (s : (SectionRing E T).obj.obj U)
      (x : U.unop.left),
    rationalCoefficientValue l E T U (sectionIso.hom.hom.app U s) x =
      (((coefficientIso.hom.hom).hom.app U) s).down x
  integralIso : pbcAdicCompletion T (pbcIntegralDatum l E) ≅
    AlgebraicGeometry.Scheme.integralCoefficientSheaf l T E
  finiteIso : ∀ n : ℕ,
    (pbcAdicRings T (pbcIntegralDatum l E)).obj (op n) ≅
      finiteContinuousCoefficientSheaf l T E n
  finite_normalization : ∀ (n : ℕ) (U : T.ProEtᵒᵖ)
      (a : PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1)) (x : U.unop.left),
    finiteContinuousCoefficientValue l E T n U
      ((finiteIso n).hom.hom.app U
        (pbcFunctionScalars T (pbcIntegralDatum l E) n |>.app U |>.hom <| a)) x =
      integralCoefficientULift l E n a
  integral_normalization : ∀ (n : ℕ) (U : T.ProEtᵒᵖ)
      (s : (AlgebraicGeometry.Scheme.integralCoefficientSheaf l T E).obj.obj U) (x : U.unop.left),
    (finiteContinuousCoefficientValue l E T n U
      ((integralIso.inv ≫ pbcAdicProjection T (pbcIntegralDatum l E) n ≫
        (finiteIso n).hom).hom.app U s) x).down =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
        (integralCoefficientValue l E T U s x)
  inclusion : AlgebraicGeometry.Scheme.integralCoefficientSheaf l T E ⟶ rationalCoefficientSheaf
    l T E
  inclusion_normalization : integralRationalCoefficientNormalized l E T inclusion
  [encodingAdditive : (moduleEncoding l E T sectionIso).functor.Additive]
  [encodingInverseAdditive : (moduleEncoding l E T sectionIso).inverse.Additive]
  realization : Rational l E T ≌ Constructible E T
  scalarExtension :
    pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
        realization.functor ⋙ (boundedConstructible (Coefficient E T)).ι ⋙
          (moduleEncoding l E T sectionIso).mapDerivedCategory.functor ≅
      ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) ⋙
        pbcDerivedExtend (integralIso.hom ≫ inclusion)
  linearity : ∀ (K L : Rational l E T) (f : K ⟶ L)
      (a : Localization.Away (pbcUniformizer l E)),
    ((moduleEncoding l E T sectionIso).mapDerivedCategory.functor).map
        (realization.functor.map (a • f)).hom =
      pbcRationalCoefficientEquiv l E a •
        ((moduleEncoding l E T sectionIso).mapDerivedCategory.functor).map
          (realization.functor.map f).hom
  integral_model : ∀ K : Constructible E T, ∃ M : Integral l E T,
    Nonempty (realization.functor.obj (ScalarLocalization.mk M) ≅ K)
  lisse_criterion : ∀ K : Ambient E T,
    boundedConstructible (Coefficient E T) K ↔
      (∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) ∧
      ∀ q : ℤ, ∃ S : Scheme.Stratification T, ∀ a : Fin S.n,
        ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a),
        ∀ i : C.I₀,
          Mod.IsFree
            ((upperStar Ab.{u + 1} (C.f i)).obj
              ((upperStar Ab.{u + 1} (S.immersion a)).obj (Coefficient E T)))
            (((upperStar Ab.{u + 1} (C.f i)).mapMod _).obj
              (((upperStar Ab.{u + 1} (S.immersion a)).mapMod _).obj
                ((DerivedCategory.homologyFunctor _ q).obj K)))

end WeilConjectures.CondensedERealization

namespace WeilConjectures.CondensedERealization

attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]
variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma bounded_comap {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) Ab.{u + 1}} [MonObj R] [MonObj S]
    [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] [IsIso a]
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) S))
    (hK : boundedConstructible S K) :
    boundedConstructible R ((Mod.comap a).mapDerivedCategory.obj K) := by
  refine ⟨(Mod.comap a).bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩
  exact constructible_of_iso
    (((Mod.comap a).mapDerivedCategoryHomologyFunctorIso n).app K)
    (constructible_comap a (hK.2 n))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma bounded_iso {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)}
    (e : K ≅ L) (hK : boundedConstructible R K) : boundedConstructible R L := by
  exact ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e hK.1,
    fun n ↦ constructible_of_iso ((DerivedCategory.homologyFunctor _ n).mapIso e) (hK.2 n)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma bounded_comap_iff {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) Ab.{u + 1}} [MonObj R] [MonObj S]
    [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] [IsIso a]
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) S)) :
    boundedConstructible R ((Mod.comap a).mapDerivedCategory.obj K) ↔
      boundedConstructible S K := by
  refine ⟨fun h ↦ ?_, bounded_comap a K⟩
  let i : 𝟭 (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) S) ≅
      Mod.comap a ⋙ Mod.comap (asIso a).inv :=
    (Mod.comapId S).symm ≪≫ Mod.comapCongr (by simp) ≪≫
      Mod.comapComp (asIso a).inv a
  let e := (Functor.mapDerivedCategoryIdIso _).symm ≪≫
    Functor.mapDerivedCategoryNatIso i ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm
  exact bounded_iso (e.app K).symm (bounded_comap (asIso a).inv _ h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma leftAdjoint_of_coefficientIso (F : PadicAlgCl.FiniteIntermediateField l)
    {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ'] [IsCommMonObj Λ']
    (a : Profinite.continuousMapRingObj.{u} F.1 ⟶ Λ') [IsMonHom a] [IsIso a]
    (T U : Base k) (h : T.scheme ⟶ U.scheme) [h.IsOver (Spec (.of k))] :
    (boundedConstructibleUpperStar Λ' l (Base.map T U h)).IsLeftAdjoint := by
  have hflat (X : Scheme.{u}) :
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv (coefficientMap a X)).symm
  have hp (K : DerivedCategory (Mod (Sheaf (ProEt.topology T.scheme) Ab.{u + 1})
      (condensedRingObj Λ' T.scheme))) (hK : boundedConstructible _ K) :
      boundedConstructible (condensedRingObj Λ' U.scheme)
        ((CondensedRing.lowerStar Λ' h).rightDerivedFunctor.obj K) := by
    apply (bounded_comap_iff (coefficientMap a U.scheme) _).mp
    exact bounded_iso ((derivedComapLowerStarIso a h).app K).symm
      (ContinuousMapRingObj.boundedConstructible_rightDerivedLowerStar_obj l F
        (Base.map T U h) ⟨_, bounded_comap (coefficientMap a T.scheme) K hK⟩)
  let G := (boundedConstructible (condensedRingObj Λ' U.scheme)).lift
    ((boundedConstructible (condensedRingObj Λ' T.scheme)).ι ⋙
      (CondensedRing.lowerStar Λ' h).rightDerivedFunctor) (fun K ↦ hp K.obj K.property)
  exact (Adjunction.restrictFullyFaithful (derivedUpperStarLowerStarAdjunction Λ' h)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ' l (Base.map T U h)).symm
    (show G ⋙ (boundedConstructible _).ι ≅ _ from
      ObjectProperty.liftCompιIso _ _ _).symm).isLeftAdjoint

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual bounded continuous-E inverse image has a constructible right adjoint,
including finite extensions represented in the scheme universe.
Source: BS 6.8.14(2), 6.8.15 (blueprint: lem-weil-pbc-condensed-e-realization).
Proof: choose a small normed-field representative of the finite-dimensional extension
E/Q_l. The coefficient-ring isomorphism gives equivalences of module categories and
their derived categories, preserving the local finite presentation condition. For the
small representative, the continuous coefficient constructor supplies the finiteness
class, and derived direct image preserves constructibility for separated finite-type
schemes over k. Transport its inverse-image/direct-image adjunction back through these
coefficient equivalences. Inverse image commutes with coefficient transport, so its
left adjoint is exactly the displayed existing inverse image. The transported counit
is the ordinary ambient counit; thus its right adjoint is uniquely determined. -/
theorem fieldUpperStar_isLeftAdjoint (T U : Base k) (h : T.scheme ⟶ U.scheme)
    [h.IsOver (Spec (.of k))] :
    (boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
      (X := T.model) (Y := U.model)
      (Base.map T U h)).IsLeftAdjoint := by
  classical
  have : Small.{0} E := small_of_injective (Module.finBasis ℚ_[l] E).equivFun.injective
  let e : Shrink.{0} E ≃ E := (equivShrink E).symm
  let : NormedField (Shrink.{0} E) := e.normedField
  let : NormedAlgebra ℚ_[l] (Shrink.{0} E) :=
    { toAlgebra := e.algebra ℚ_[l]
      norm_smul_le := fun a x ↦ by
        change ‖e (a • x)‖ ≤ ‖a‖ * ‖e x‖
        rw [show e (a • x) = a • e x from
          (e.algEquiv ℚ_[l]).toLinearEquiv.map_smul a x]
        exact norm_smul_le a (e x) }
  let es : Shrink.{0} E ≃ₐ[ℚ_[l]] E := e.algEquiv ℚ_[l]
  have : FiniteDimensional ℚ_[l] (Shrink.{0} E) :=
    FiniteDimensional.of_injective es.toLinearMap es.injective
  have he : Isometry e := by
    intro x y
    rfl
  have hei : Isometry e.symm := fun x y ↦ by
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  -- Realize the small representative as a finite subextension `F ⊆ ℚ̄_ℓ`.
  let i : Shrink.{0} E →ₐ[ℚ_[l]] PadicAlgCl l := IsAlgClosed.lift
  let σ := i.equivFieldRange
  have : FiniteDimensional ℚ_[l] i.fieldRange := σ.toLinearEquiv.finiteDimensional
  let F : PadicAlgCl.FiniteIntermediateField l := ⟨i.fieldRange, inferInstance⟩
  let ea : F.1 ≃ₐ[ℚ_[l]] E := σ.symm.trans es
  have hc : Continuous ea :=
    he.continuous.comp (LinearMap.continuous_of_finiteDimensional σ.symm.toLinearMap)
  have hci : Continuous ea.symm :=
    (LinearMap.continuous_of_finiteDimensional σ.toLinearMap).comp hei.continuous
  let q : Profinite.continuousMapRingSheaf.{u} F.1 ≅
      Profinite.continuousCoefficientRingSheaf E :=
    { hom := ⟨
        { app := fun _ ↦ RingCat.ofHom
            (ULift.ringEquiv.symm.toRingHom.comp
              ((ea.toRingHom.compLeftContinuous _ hc).comp
                ULift.ringEquiv.toRingHom))
          naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨
        { app := fun _ ↦ RingCat.ofHom
            (ULift.ringEquiv.symm.toRingHom.comp
              ((ea.symm.toRingHom.compLeftContinuous _ hci).comp
                ULift.ringEquiv.toRingHom))
          naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ea.symm_apply_apply (f.down x)
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ea.apply_symm_apply (f.down x) }
  let a := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map q.hom
  have : IsMonHom a := Sheaf.isMonHom_sheafCompose_map _ q.hom
  have : IsIso a := by
    change IsIso ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso q).hom
    infer_instance
  exact leftAdjoint_of_coefficientIso l k F a T U h

/-- Continuous-E direct image, specified up to unique adjunction-compatible iso.
Source: BS 6.8.14(2) (blueprint: lem-weil-pbc-condensed-e-realization). -/
@[irreducible]
def fieldLowerStar (T U : Base k) (h : T.scheme ⟶ U.scheme)
    [h.IsOver (Spec (.of k))] : Constructible E T.scheme ⥤ Constructible E U.scheme :=
  @Functor.rightAdjoint (Constructible E T.scheme) _ (Constructible E U.scheme) _
    (boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
      (X := T.model) (Y := U.model)
      (Base.map T U h)) (fieldUpperStar_isLeftAdjoint l E k T U h)

/-- The canonical adjunction determining continuous-E direct image.
Source: BS 6.8.14(2) (blueprint: lem-weil-pbc-condensed-e-realization). -/
@[irreducible]
def fieldAdjunction (T U : Base k) (h : T.scheme ⟶ U.scheme)
    [h.IsOver (Spec (.of k))] :
    boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
      (X := T.model) (Y := U.model)
      (Base.map T U h) ⊣ fieldLowerStar l E k T U h := by
  unfold fieldLowerStar
  exact @Adjunction.ofIsLeftAdjoint (Constructible E U.scheme) _ (Constructible E T.scheme) _
    (boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
      (X := T.model) (Y := U.model)
      (Base.map T U h)) (fieldUpperStar_isLeftAdjoint l E k T U h)

-- The unit and counit equations compare several nested coefficient equivalences.
/-- Comparison data for one morphism. The integral operations are actual restrictions
of the specified completed pullback and ordinary direct image. Their adjunction is
normalized by the ambient tensor unit and counit. Rational operations are their tensor
extensions, and both adjunctions retain their actual units and counits.
Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15
(blueprint: lem-weil-pbc-condensed-e-realization). -/
structure Along (T U : Base k) (h : T.scheme ⟶ U.scheme)
    [h.IsOver (Spec (.of k))] (rT : At l E T.scheme) (rU : At l E U.scheme) where
  pull : Integral l E U.scheme ⥤ Integral l E T.scheme
  [pullAdditive : pull.Additive]
  [pullLinear : pull.Linear (PbcIntegralRing l E)]
  push : Integral l E T.scheme ⥤ Integral l E U.scheme
  [pushAdditive : push.Additive]
  [pushLinear : push.Linear (PbcIntegralRing l E)]
  pullAmbient : pull ⋙ ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme
    (pbcIntegralDatum l E)) ≅
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E)) ⋙
      (pbcIntegralDatum l E).completedPull h
  pushAmbient : push ⋙ ObjectProperty.ι (PbcIsBoundedConstructibleComplete U.scheme
    (pbcIntegralDatum l E)) ≅
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)) ⋙
      (pbcIntegralDatum l E).push h
  integralAdjunction : pull ⊣ push
  integral_unit : ∀ K : Integral l E U.scheme,
    (integralAdjunction.unit.app K).hom ≫ pushAmbient.hom.app (pull.obj K) ≫
        ((pbcIntegralDatum l E).push h).map (pullAmbient.hom.app K) =
      (proEtaleRingDerivedAdjunction h _ _ ((pbcIntegralDatum l E).integralRingIso h)).unit.app
          K.obj ≫
        ((pbcIntegralDatum l E).push h).map
          ((pbcIntegralDatum l E).ordinaryToCompleted h K.obj)
  integral_counit : ∀ K : Integral l E T.scheme,
    (pbcIntegralDatum l E).ordinaryToCompleted h (push.obj K).obj ≫
        pullAmbient.inv.app (push.obj K) ≫ (integralAdjunction.counit.app K).hom =
      ((pbcIntegralDatum l E).pull h).map (pushAmbient.hom.app K) ≫
        (proEtaleRingDerivedAdjunction h _ _
          ((pbcIntegralDatum l E).integralRingIso h)).counit.app K.obj
  rationalAdjunction :
    ScalarLocalization.transport (PbcIntegralRing l E) (pbcUniformizer l E) pull ⊣
      ScalarLocalization.transport (PbcIntegralRing l E) (pbcUniformizer l E) push
  rational_unit : ∀ K : Integral l E U.scheme,
    HEq (rationalAdjunction.unit.app (ScalarLocalization.mk K))
      ((1 : Localization.Away (pbcUniformizer l E)) ⊗ₜ[PbcIntegralRing l E]
        integralAdjunction.unit.app K)
  rational_counit : ∀ K : Integral l E T.scheme,
    HEq (rationalAdjunction.counit.app (ScalarLocalization.mk K))
      ((1 : Localization.Away (pbcUniformizer l E)) ⊗ₜ[PbcIntegralRing l E]
        integralAdjunction.counit.app K)
  pullComparison :
    ScalarLocalization.transport (PbcIntegralRing l E) (pbcUniformizer l E) pull ⋙
        rT.realization.functor ≅
      rU.realization.functor ⋙
        boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
          (X := T.model) (Y := U.model)
      (Base.map T U h)
  pushComparison :
    ScalarLocalization.transport (PbcIntegralRing l E) (pbcUniformizer l E) push ⋙
        rU.realization.functor ≅
      rT.realization.functor ⋙
        fieldLowerStar l E k T U h
  unit : ∀ K : Rational l E U.scheme,
    rU.realization.functor.map (rationalAdjunction.unit.app K) ≫
        pushComparison.hom.app
          ((ScalarLocalization.transport (PbcIntegralRing l E) (pbcUniformizer l E) pull).obj
            K) ≫
        (fieldLowerStar l E k T U h).map
          (pullComparison.hom.app K) =
      (fieldAdjunction l E k T U h).unit.app (rU.realization.functor.obj K)
  counit : ∀ K : Rational l E T.scheme,
    rT.realization.functor.map (rationalAdjunction.counit.app K) =
      pullComparison.hom.app
          ((ScalarLocalization.transport (PbcIntegralRing l E) (pbcUniformizer l E) push).obj
            K) ≫
        (boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
          (X := T.model) (Y := U.model)
      (Base.map T U h)).map
          (pushComparison.hom.app K) ≫
        (fieldAdjunction l E k T U h).counit.app
            (rT.realization.functor.obj K)

attribute [instance] Along.pullAdditive Along.pullLinear Along.pushAdditive Along.pushLinear

/-- The canonical rational pullback is the dependency's tensor extension of integral pullback.
Source: blueprint rational transport
(blueprint: lem-weil-pbc-condensed-e-realization). -/
abbrev Along.rationalPull {T U : Base k} {h : T.scheme ⟶ U.scheme}
    [h.IsOver (Spec (.of k))] {rT : At l E T.scheme} {rU : At l E U.scheme}
    (a : Along l E k T U h rT rU) : Rational l E U.scheme ⥤ Rational l E T.scheme :=
  ScalarLocalization.transport (PbcIntegralRing l E) (pbcUniformizer l E) a.pull

/-- The canonical rational direct image is the dependency's tensor extension of integral image.
Source: blueprint rational transport
(blueprint: lem-weil-pbc-condensed-e-realization). -/
abbrev Along.rationalPush {T U : Base k} {h : T.scheme ⟶ U.scheme}
    [h.IsOver (Spec (.of k))] {rT : At l E T.scheme} {rU : At l E U.scheme}
    (a : Along l E k T U h rT rU) : Rational l E T.scheme ⥤ Rational l E U.scheme :=
  ScalarLocalization.transport (PbcIntegralRing l E) (pbcUniformizer l E) a.push

end WeilConjectures.CondensedERealization

namespace WeilConjectures.CondensedERealization
variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]
variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
set_option allowUnsafeReducibility true in
attribute [local irreducible] AdicCoefficientDatum.completedPull
  AdicCoefficientDatum.pull AdicCoefficientDatum.ordinaryToCompleted
  AdicCoefficientDatum.completedPullComp AdicCoefficientDatum.pullId
  AlgebraicGeometry.Scheme.pbcIntegralDatum CategoryTheory.ScalarLocalization.transport

/-- A simultaneous realization over all separated finite-type schemes and all morphisms.
The composition and identity isomorphisms are normalized by the specified completed
comparisons and tensor formulas, and the completed exchange is compared as an arrow.
Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15, and the blueprint's
unit--square--counit comparison obligation
(blueprint: lem-weil-pbc-condensed-e-realization). -/
structure Data where
  atObject : ∀ T : Base k, At l E T.scheme
  along : ∀ (T U : Base k) (h : T.scheme ⟶ U.scheme) [h.IsOver (Spec (.of k))],
    Along l E k T U h (atObject T) (atObject U)
  integralComp : ∀ (T U V : Base k) (h : T.scheme ⟶ U.scheme)
      [h.IsOver (Spec (.of k))] (j : U.scheme ⟶ V.scheme) [j.IsOver (Spec (.of k))],
    (along T V (h ≫ j)).pull ≅ (along U V j).pull ⋙ (along T U h).pull
  integralComp_normalization : ∀ (T U V : Base k) (h : T.scheme ⟶ U.scheme)
      [h.IsOver (Spec (.of k))] (j : U.scheme ⟶ V.scheme) [j.IsOver (Spec (.of k))]
      (K : Integral l E V.scheme),
    ((integralComp T U V h j).hom.app K).hom ≫
        (along T U h).pullAmbient.hom.app ((along U V j).pull.obj K) ≫
        ((pbcIntegralDatum l E).completedPull h).map
          (X := ((along U V j).pull.obj K).obj)
          (Y := ((pbcIntegralDatum l E).completedPull j).obj K.obj)
          ((along U V j).pullAmbient.hom.app K) =
      (along T V (h ≫ j)).pullAmbient.hom.app K ≫
        ((pbcIntegralDatum l E).completedPullComp h j).hom.app K.obj
  rationalComp : ∀ (T U V : Base k) (h : T.scheme ⟶ U.scheme)
      [h.IsOver (Spec (.of k))] (j : U.scheme ⟶ V.scheme) [j.IsOver (Spec (.of k))],
    (along T V (h ≫ j)).rationalPull ≅
      (along U V j).rationalPull ⋙ (along T U h).rationalPull
  rationalComp_normalization : ∀ (T U V : Base k) (h : T.scheme ⟶ U.scheme)
      [h.IsOver (Spec (.of k))] (j : U.scheme ⟶ V.scheme) [j.IsOver (Spec (.of k))]
      (K : Integral l E V.scheme),
    HEq ((rationalComp T U V h j).hom.app (ScalarLocalization.mk K))
      ((1 : Localization.Away (pbcUniformizer l E)) ⊗ₜ[PbcIntegralRing l E]
        (integralComp T U V h j).hom.app K)
  composition : ∀ (T U V : Base k) (h : T.scheme ⟶ U.scheme)
      [h.IsOver (Spec (.of k))] (j : U.scheme ⟶ V.scheme) [j.IsOver (Spec (.of k))]
      (K : Rational l E V.scheme),
    (atObject T).realization.functor.map
        (X := (along T V (h ≫ j)).rationalPull.obj K)
        (Y := (along T U h).rationalPull.obj ((along U V j).rationalPull.obj K))
        ((rationalComp T U V h j).hom.app K) ≫
        (along T U h).pullComparison.hom.app ((along U V j).rationalPull.obj K) ≫
        (boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
          (X := T.model) (Y := U.model)
      (Base.map T U h)).map
          (X := (atObject U).realization.functor.obj ((along U V j).rationalPull.obj K))
          (Y := (boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
            (Base.map U V j)).obj ((atObject V).realization.functor.obj K))
          ((along U V j).pullComparison.hom.app K) =
      (along T V (h ≫ j)).pullComparison.hom.app K ≫
        (boundedConstructibleUpperStarComp (Profinite.continuousCoefficientRingObj E)
          l (X := T.model) (Y := U.model) (Z := V.model)
            (Base.map T U h) (Base.map U V j)).hom.app ((atObject V).realization.functor.obj K)
  integralId : ∀ T : Base k, (along T T (𝟙 T.scheme)).pull ≅ 𝟭 (Integral l E T.scheme)
  integralId_normalization : ∀ (T : Base k) (K : Integral l E T.scheme),
    (pbcIntegralDatum l E).ordinaryToCompleted (𝟙 T.scheme) K.obj ≫
        (along T T (𝟙 T.scheme)).pullAmbient.inv.app K ≫
        ((integralId T).hom.app K).hom =
      ((pbcIntegralDatum l E).pullId T.scheme).hom.app K.obj
  rationalId : ∀ T : Base k,
    (along T T (𝟙 T.scheme)).rationalPull ≅ 𝟭 (Rational l E T.scheme)
  rationalId_normalization : ∀ (T : Base k) (K : Integral l E T.scheme),
    HEq ((rationalId T).hom.app (ScalarLocalization.mk K))
      ((1 : Localization.Away (pbcUniformizer l E)) ⊗ₜ[PbcIntegralRing l E]
        (integralId T).hom.app K)
  condensedId : ∀ T : Base k,
    boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l (𝟙 T.model) ≅
      𝟭 (Constructible E T.scheme)
  condensedId_normalization : ∀ (T : Base k) (K : Constructible E T.scheme),
    (boundedConstructibleUpperStarComp (Profinite.continuousCoefficientRingObj E) l
        (𝟙 T.model) (𝟙 T.model)).hom.app K ≫
      (condensedId T).hom.app
        ((boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
          (𝟙 T.model)).obj K) =
      𝟙 ((boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
        (𝟙 T.model)).obj K)
  identity : ∀ (T : Base k) (K : Rational l E T.scheme),
    (atObject T).realization.functor.map ((rationalId T).hom.app K) =
      (along T T (𝟙 T.scheme)).pullComparison.hom.app K ≫
        (condensedId T).hom.app ((atObject T).realization.functor.obj K)

end WeilConjectures.CondensedERealization

namespace WeilConjectures.CondensedERealization

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]
variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

variable (D : Data l E k)
variable {X' X Y' Y : Base k}
variable {g' : X'.scheme ⟶ X.scheme} {f' : X'.scheme ⟶ Y'.scheme}
  {f : X.scheme ⟶ Y.scheme} {g : Y'.scheme ⟶ Y.scheme}
variable [g'.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))]
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]

/-- Regard a rational pullback as a function of a bundled morphism over k, so that
proof irrelevance supplies the canonical transport along an equality of morphisms.
Source: blueprint, comparison of the pullback square
(blueprint: lem-weil-pbc-condensed-e-realization). -/
def Data.pullOnOverHom (T U : Base k)
    (h : { h : T.scheme ⟶ U.scheme // h.IsOver (Spec (.of k)) }) :
    Rational l E U.scheme ⥤ Rational l E T.scheme :=
  letI : h.val.IsOver (Spec (.of k)) := h.property
  (D.along T U h.val).rationalPull

/-- The rational pullback square uses only the specified composition isomorphisms
and the equality of the two scheme composites, with no Cartesian hypothesis.
Source: blueprint, comparison of the pullback square
(blueprint: lem-weil-pbc-condensed-e-realization). -/
def Data.square (sq : CommSq g' f' f g) :
    (D.along Y' Y g).rationalPull ⋙ (D.along X' Y' f').rationalPull ≅
      (D.along X Y f).rationalPull ⋙ (D.along X' X g').rationalPull :=
  (D.rationalComp X' Y' Y f' g).symm ≪≫
    eqToIso (congrArg (Data.pullOnOverHom l E k D X' Y) (Subtype.ext
      (a1 := (⟨f' ≫ g, inferInstance⟩ :
        { h : X'.scheme ⟶ Y.scheme // h.IsOver (Spec (.of k)) }))
      (a2 := (⟨g' ≫ f, inferInstance⟩ :
        { h : X'.scheme ⟶ Y.scheme // h.IsOver (Spec (.of k)) })) sq.w.symm)) ≪≫
      D.rationalComp X' X Y g' f

/-- The actual rational unit--square--counit mate, before any invertibility assertion.
Source: blueprint, last paragraph
(blueprint: lem-weil-pbc-condensed-e-realization). -/
def Data.mate (sq : CommSq g' f' f g) :
    (D.along X Y f).rationalPush ⋙ (D.along Y' Y g).rationalPull ⟶
      (D.along X' X g').rationalPull ⋙ (D.along X' Y' f').rationalPush :=
  (mateEquiv (D.along X Y f).rationalAdjunction (D.along X' Y' f').rationalAdjunction
    (TwoSquare.mk _ _ _ _ (Data.square l E k D sq).hom))

/-- The continuous-E pullback square uses the existing normalized composition iso.
Source: Stacks 0D6G (blueprint: lem-weil-pbc-condensed-e-realization). -/
def fieldSquare (sq : CommSq g' f' f g) :
    boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
      (X := Y'.model) (Y := Y.model)
      (Base.map Y' Y g) ⋙
      boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
        (X := X'.model) (Y := Y'.model)
      (Base.map X' Y' f') ≅
    boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
      (X := X.model) (Y := Y.model)
      (Base.map X Y f) ⋙
      boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
        (X := X'.model) (Y := X.model)
      (Base.map X' X g') :=
  (boundedConstructibleUpperStarComp (Profinite.continuousCoefficientRingObj E) l
    (Base.map X' Y' f') (Base.map Y' Y g)).symm ≪≫
    eqToIso (congrArg (fun h : X'.model ⟶ Y.model ↦
      boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l h)
        (Over.OverMorphism.ext (show (Base.map X' Y' f' ≫ Base.map Y' Y g).left =
          (Base.map X' X g' ≫ Base.map X Y f).left from sq.w.symm))) ≪≫
      boundedConstructibleUpperStarComp (Profinite.continuousCoefficientRingObj E) l
        (Base.map X' X g') (Base.map X Y f)

/-- The continuous-E exchange is the actual unit-square-counit mate.
Source: Stacks 0D6G (blueprint: lem-weil-pbc-condensed-e-realization). -/
def fieldBaseChange (sq : CommSq g' f' f g) :
    fieldLowerStar l E k X Y f ⋙
      boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
        (X := Y'.model) (Y := Y.model)
      (Base.map Y' Y g) ⟶
    boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
      (X := X'.model) (Y := X.model)
      (Base.map X' X g') ⋙ fieldLowerStar l E k X' Y' f' :=
  (mateEquiv (fieldAdjunction l E k X Y f) (fieldAdjunction l E k X' Y' f')
    (TwoSquare.mk _ _ _ _ (fieldSquare l E k sq).hom))

/-- Equality of the specified integral, rational, and condensed exchange maps.
`completedExchange` is definitionally the ordered `completedBaseChangeMap` on every
complete input with any permitted choice of finite-origin witnesses. The rational
exchange is fixed as a mate, and its integral tensor formula is an equality of arrows.
Source: blueprint, ordered completed exchange and its comparison obligation;
Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-condensed-e-realization). -/
structure Exchange where
  integral : ∀ (X' X Y' Y : Base k)
      (g' : X'.scheme ⟶ X.scheme) (f' : X'.scheme ⟶ Y'.scheme)
      (f : X.scheme ⟶ Y.scheme) (g : Y'.scheme ⟶ Y.scheme)
      [g'.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))]
      [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))] [IsProper f]
      (_sq : ChosenCartesianSquare g' f' f g),
    (D.along X Y f).push ⋙ (D.along Y' Y g).pull ⟶
      (D.along X' X g').pull ⋙ (D.along X' Y' f').push
  integral_normalization : ∀ (X' X Y' Y : Base k)
      (g' : X'.scheme ⟶ X.scheme) (f' : X'.scheme ⟶ Y'.scheme)
      (f : X.scheme ⟶ Y.scheme) (g : Y'.scheme ⟶ Y.scheme)
      [g'.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))]
      [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))] [IsProper f]
      (sq : ChosenCartesianSquare g' f' f g) (K : Integral l E X.scheme),
    ((integral X' X Y' Y g' f' f g sq).app K).hom ≫
        (D.along X' Y' f').pushAmbient.hom.app ((D.along X' X g').pull.obj K) ≫
        ((pbcIntegralDatum l E).push f').map
          ((D.along X' X g').pullAmbient.hom.app K) =
      (D.along Y' Y g).pullAmbient.hom.app ((D.along X Y f).push.obj K) ≫
        ((pbcIntegralDatum l E).completedPull g).map
          ((D.along X Y f).pushAmbient.hom.app K) ≫
        (pbcIntegralDatum l E).completedExchange sq K.obj
  rational_normalization : ∀ (X' X Y' Y : Base k)
      (g' : X'.scheme ⟶ X.scheme) (f' : X'.scheme ⟶ Y'.scheme)
      (f : X.scheme ⟶ Y.scheme) (g : Y'.scheme ⟶ Y.scheme)
      [g'.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))]
      [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))] [IsProper f]
      (sq : ChosenCartesianSquare g' f' f g) (K : Integral l E X.scheme),
    HEq ((Data.mate l E k D sq.toCommSq).app (ScalarLocalization.mk K))
      ((1 : Localization.Away (pbcUniformizer l E)) ⊗ₜ[PbcIntegralRing l E]
        (integral X' X Y' Y g' f' f g sq).app K)
  condensed_normalization : ∀ (X' X Y' Y : Base k)
      (g' : X'.scheme ⟶ X.scheme) (f' : X'.scheme ⟶ Y'.scheme)
      (f : X.scheme ⟶ Y.scheme) (g : Y'.scheme ⟶ Y.scheme)
      [g'.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))]
      [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))] [IsProper f]
      (sq : ChosenCartesianSquare g' f' f g) (K : Integral l E X.scheme),
    (D.atObject Y').realization.functor.map
        ((Data.mate l E k D sq.toCommSq).app (ScalarLocalization.mk K)) ≫
        (D.along X' Y' f').pushComparison.hom.app
          ((D.along X' X g').rationalPull.obj (ScalarLocalization.mk K)) ≫
        (fieldLowerStar l E k X' Y' f').map
          ((D.along X' X g').pullComparison.hom.app (ScalarLocalization.mk K)) =
      (D.along Y' Y g).pullComparison.hom.app
          ((D.along X Y f).rationalPush.obj (ScalarLocalization.mk K)) ≫
        (boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
          (X := Y'.model) (Y := Y.model)
      (Base.map Y' Y g)).map
          ((D.along X Y f).pushComparison.hom.app (ScalarLocalization.mk K)) ≫
        (fieldBaseChange l E k sq.toCommSq).app
          ((D.atObject X).realization.functor.obj (ScalarLocalization.mk K))

end WeilConjectures.CondensedERealization

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi

import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
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
import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackTensorCoherence
import all WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackSiteData
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPushforwardCompositionSections
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPushforwardIdentitySections
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.SixFunctors.SequenceComparisonConstruction.KFlatUnaryWhiskering
import WeilConjectures.SixFunctors.SequenceComparisonConstruction.NormalizedDerivedComparisonDescent
import WeilConjectures.SixFunctors.SequenceScalarConstruction.SystemScalarTensorSection
import WeilConjectures.SixFunctors.SequenceScalarConstruction.FixedScalarUnitUnique
import WeilConjectures.SixFunctors.SequenceScalarConstruction.SystemScalarCompositionUnique
import WeilConjectures.SixFunctors.SequenceScalarConstruction.SystemScalarUnitUnique
import WeilConjectures.SixFunctors.SequenceScalarConstruction.FixedScalarCompositionUnique
import WeilConjectures.SixFunctors.SequenceScalarConstruction.SystemScalarPackageExists
import WeilConjectures.SixFunctors.SequenceScalarConstruction.SystemScalarOrdinaryAdjunction
/-!
# Realization of integral pullback comparisons

Source: Stacks Project, Tags 099N(2),(5), 0D6D, 06YY and 0941; blueprint
`sec-trace-formula/sk-thm-trace-transport/prop-trf-karoubi-independence.proof.md`,
final common-stage transport paragraph
(blueprint: def-trf-integral-comparison-sequence-systems).

The sequence site retains the whole quotient diagram. Its pullback is the left
adjoint of the actual sectionwise direct image. Scalar change is the universal
derived change of rings for the actual map of quotient coefficient sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe sa sb sw
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SequenceScalarProof
variable {C : Type sa} [Category.{sb} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{sw} RingCat.{sw})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{sw}] [HasSheafify J AddCommGrpCat.{sw}]
  [EssentiallySmall.{sw} C]

private theorem scalarPackageExists
    {R S : Sheaf J CommRingCat.{sw}} (φ : R ⟶ S)
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel φ) :
    ∃ A : SheafOfModules.SystemScalarModel φ, A.model = D := by
  exact SequenceScalarConstruction.scalarPackageExists φ D

end SequenceScalarProof

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
open scoped ChangeOfRings

/-- Base change on the actual sequence site. Source: Stacks 0941, 09A5
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceBaseChange {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (ℕ × Y.ProEt) ⥤ (ℕ × X.ProEt) :=
  (𝟭 ℕ).prod (proEtaleBaseChange f)

/-- Base change is continuous on the sequence site. Source: Stacks 0941, 09A5
(blueprint: def-trf-integral-comparison-sequence-systems).
Proof: a covering is a vertical covering at its index. Base change preserves the
vertical covering, by continuity on the small pro-etale site. Thus the restriction
of a sheaf is a sheaf, which is exactly the asserted continuity. -/
theorem integralComparisonSequenceBaseChange_continuous {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (integralComparisonSequenceBaseChange f).IsContinuous
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceTopology (ProEt.topology X)) := by
  exact AmbientPullbackTensor.baseContinuous f none

/-- Continuity of the actual sequence-site base change. Source: Stacks 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
instance integralComparisonSequenceBaseChangeContinuous {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (integralComparisonSequenceBaseChange f).IsContinuous
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceTopology (ProEt.topology X)) :=
  integralComparisonSequenceBaseChange_continuous f

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The component of the constant-section map on the product site.
Source: Stacks 03D2, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceRingComponent {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : (ℕ × Y.ProEt)ᵒᵖ) :
    (coefficientSequenceCommRingPresheaf l E Y).obj A ⟶
      (coefficientSequenceCommRingPresheaf l E X).obj
        ((integralComparisonSequenceBaseChange f).op.obj A) :=
  (coefficientProEtaleDirectRingMap.{t, u} f
    (CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionRing l E (A.unop.1 + 1))))).hom.app (op A.unop.2)

private theorem sequenceConstantMap_naturality {X Y : Scheme.{t}} (f : X ⟶ Y)
    {A B : CommRingCat.{max u (t + 1)}} (a : A ⟶ B) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map a ≫
      coefficientProEtaleDirectRingMap.{t, u} f B =
    coefficientProEtaleDirectRingMap.{t, u} f A ≫
      ((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
        (ProEt.topology Y) (ProEt.topology X)).map
          ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map a) := by
  exact AmbientPullbackTensor.constantMap_naturality f a

/-- The constant-section coefficient maps commute with horizontal quotients and
vertical restrictions. Source: Stacks 03D2, 0941
(blueprint: def-trf-integral-comparison-sequence-systems).
Proof: on constant sections both composites send a residue class to the same
constant section at the smaller exponent. Sheafification gives horizontal
naturality. Naturality of each coefficient map gives vertical naturality. Every
arrow in the product site factors into a horizontal and a vertical arrow. -/
theorem integralComparisonSequenceRing_naturality {X Y : Scheme.{t}} (f : X ⟶ Y)
    {A B : (ℕ × Y.ProEt)ᵒᵖ} (g : A ⟶ B) :
    (coefficientSequenceCommRingPresheaf l E Y).map g ≫
        integralComparisonSequenceRingComponent l E f B =
      integralComparisonSequenceRingComponent l E f A ≫
        (coefficientSequenceCommRingPresheaf l E X).map
          ((integralComparisonSequenceBaseChange f).op.map g) := by
  exact AmbientPullbackTensor.ringComponent_naturality l E f none g

/-- Actual constant coefficients on the sequence site, with their quotient transitions.
Source: Stacks 03D2, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceRingMap {X Y : Scheme.{t}} (f : X ⟶ Y) :
    coefficientSequenceCommRingSheaf l E Y ⟶
      ((integralComparisonSequenceBaseChange f).sheafPushforwardContinuous
        CommRingCat.{max u (t + 1)}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).obj
          (coefficientSequenceCommRingSheaf l E X) where
  hom :=
    { app := integralComparisonSequenceRingComponent l E f
      naturality := fun {_ _} g ↦ integralComparisonSequenceRing_naturality l E f g }

/-- Sectionwise direct image with the prescribed quotient coefficient action.
Source: Stacks 03D2, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceDirectImage {X Y : Scheme.{t}} (f : X ⟶ Y) :
    coefficientSequenceModules l E X ⥤ coefficientSequenceModules l E Y :=
  SheafOfModules.pushforward.{max u (t + 1)}
    (F := integralComparisonSequenceBaseChange f)
    (J := coefficientSequenceTopology (ProEt.topology Y))
    (K := coefficientSequenceTopology (ProEt.topology X))
    (S := (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
      RingCat.{max u (t + 1)})).obj (coefficientSequenceCommRingSheaf l E Y))
    (R := (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
      RingCat.{max u (t + 1)})).obj (coefficientSequenceCommRingSheaf l E X))
    ⟨Functor.whiskerRight (integralComparisonSequenceRingMap l E f).hom
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩

/-- The ordinary system inverse image exists. Source: Stacks 03D2, 0941
(blueprint: def-trf-integral-comparison-sequence-systems).
Proof: module sheaves on the sequence site form a Grothendieck abelian category,
so they have a small coseparating family and are complete and well-powered.
Direct image preserves limits: after evaluation it is evaluation on the source
followed by restriction of scalars, both of which preserve limits. Evaluation
jointly reflects limits. The special adjoint functor theorem supplies the left
adjoint, with the original independent scheme and coefficient universes. -/
theorem integralComparisonSequenceDirectImage_isRightAdjoint
    {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (integralComparisonSequenceDirectImage l E f).IsRightAdjoint := by
  exact AmbientPullbackTensor.pushRightAdjoint l E f none

/-- The adjunction structure whose right side is the actual sectionwise direct image.
Source: Stacks 03D2 (blueprint: def-trf-integral-comparison-sequence-systems). -/
instance integralComparisonSequenceRightAdjoint {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (integralComparisonSequenceDirectImage l E f).IsRightAdjoint :=
  integralComparisonSequenceDirectImage_isRightAdjoint l E f

/-- The canonical ordinary inverse image of strict quotient systems.
Source: Stacks 03D2, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequencePullback {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (integralComparisonSequenceDirectImage l E f).leftAdjoint

/-- Exactness of constant-coefficient system inverse image. Source: Stacks 03D2, 0941
(blueprint: def-trf-integral-comparison-sequence-systems).
Proof: evaluate at each positive exponent. The unit-normalized inverse-image
adjunction is the finite constant-coefficient adjunction, which is exact.
Kernels, cokernels and addition in the system category are levelwise. -/
theorem integralComparisonSequencePullback_exact {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (integralComparisonSequencePullback l E f).Additive ∧
      PreservesFiniteLimits (integralComparisonSequencePullback l E f) ∧
      PreservesFiniteColimits (integralComparisonSequencePullback l E f) := by
  exact AmbientPullbackTensor.pullExact l E f none

/-- Additivity of system inverse image. Source: Stacks 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
instance integralComparisonSequencePullbackAdditive {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (integralComparisonSequencePullback l E f).Additive :=
  (integralComparisonSequencePullback_exact l E f).1

/-- Finite limits are computed levelwise. Source: Stacks 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
instance integralComparisonSequencePullbackLimits {X Y : Scheme.{t}} (f : X ⟶ Y) :
    PreservesFiniteLimits (integralComparisonSequencePullback l E f) :=
  (integralComparisonSequencePullback_exact l E f).2.1

/-- Finite colimits are computed levelwise. Source: Stacks 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
instance integralComparisonSequencePullbackColimits {X Y : Scheme.{t}} (f : X ⟶ Y) :
    PreservesFiniteColimits (integralComparisonSequencePullback l E f) :=
  (integralComparisonSequencePullback_exact l E f).2.2

/-- Exact inverse image on the derived category of entire strict quotient systems.
Source: Stacks 0941, 0D6D
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonDerivedSequencePullback {X Y : Scheme.{t}} (f : X ⟶ Y) :
    coefficientSequenceDerived l E Y ⥤ coefficientSequenceDerived l E X :=
  (integralComparisonSequencePullback l E f).mapDerivedCategory

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Inclusion of the actual quotient rings on the sequence site.
Source: Stacks 06YY, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceScalarComponent (X : Scheme.{t}) (A : (ℕ × X.ProEt)ᵒᵖ) :
    (coefficientSequenceCommRingPresheaf l E X).obj A ⟶
      (coefficientSequenceCommRingPresheaf l L X).obj A :=
  (integralScalarQuotientSheafMap l E L ι X A.unop.1).hom.app (op A.unop.2)

/-- Quotient coefficient inclusions are natural on the entire sequence site.
Source: Stacks 06YY, 0941
(blueprint: def-trf-integral-comparison-sequence-systems).
Proof: the horizontal square is integralScalarQuotientMap_transition. The vertical
square is naturality of constant sheafification. Factor a product-site arrow into
these two arrows and paste the squares. -/
theorem integralComparisonSequenceScalar_naturality (X : Scheme.{t})
    {A B : (ℕ × X.ProEt)ᵒᵖ} (g : A ⟶ B) :
    (coefficientSequenceCommRingPresheaf l E X).map g ≫
        integralComparisonSequenceScalarComponent l E L ι X B =
      integralComparisonSequenceScalarComponent l E L ι X A ≫
        (coefficientSequenceCommRingPresheaf l L X).map g := by
  let τ : coefficientSequenceCommRingSystem l E X ⟶
      coefficientSequenceCommRingSystem l L X :=
    NatTrans.ofOpSequence (integralScalarQuotientSheafMap l E L ι X) (fun n ↦ by
      simp only [coefficientSequenceCommRingSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      change (constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map
          (CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift) ≫
          integralScalarQuotientSheafMap l E L ι X n =
        integralScalarQuotientSheafMap l E L ι X (n + 1) ≫
          (constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map
            (CommRingCat.ofHom (Padic.coefficientExtensionTransition l L (n + 1)).ulift)
      unfold integralScalarQuotientSheafMap
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      ext x
      exact congrArg (fun q ↦ q x.down)
        (integralScalarQuotientMap_transition l E L ι n).symm)
  exact (Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := X.ProEt)).functor
    (Functor.uncurry.map (Functor.whiskerRight τ
      (sheafToPresheaf (ProEt.topology X) CommRingCat)))).naturality g

/-- The specified morphism of quotient coefficient sheaves, before deriving.
Source: Stacks 06YY, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceScalarMap (X : Scheme.{t}) :
    coefficientSequenceCommRingSheaf l E X ⟶ coefficientSequenceCommRingSheaf l L X where
  hom :=
    { app := integralComparisonSequenceScalarComponent l E L ι X
      naturality := fun {_ _} g ↦ integralComparisonSequenceScalar_naturality l E L ι X g }

/-- The universal, cochain-normalized derived coefficient change on the sequence site.
The universal counit determines the pair up to the unique compatible isomorphism.
Source: Stacks 06YY, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceScalarModel (X : Scheme.{t}) :=
  Classical.choice (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel
    (integralComparisonSequenceScalarMap l E L ι X))

attribute [local irreducible] integralComparisonSequenceScalarModel

/-- Derived scalar extension of whole strict coefficient systems, retaining homotopies.
Source: Stacks 06YY, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonDerivedSequenceScalar (X : Scheme.{t}) :
    coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l L X :=
  (integralComparisonSequenceScalarModel l E L ι X).T

private theorem sequenceScalarAdjunction (X : Scheme.{t}) :
    ∃ adj : (integralComparisonSequenceScalarModel l E L ι X).E ⊣
      SheafOfModules.restrictScalars ((sheafCompose
        (coefficientSequenceTopology (ProEt.topology X)) (forget₂ CommRingCat RingCat)).map
          (integralComparisonSequenceScalarMap l E L ι X)),
      ∀ (N : coefficientSequenceModules l E X) (U : (ℕ × X.ProEt)ᵒᵖ)
        (x : N.val.obj U),
        (adj.unit.app N).val.app U x =
          (eqToHom ((integralComparisonSequenceScalarModel l E L ι X).obj_eq N).symm).val.app U
            ((toSheafify (coefficientSequenceTopology (ProEt.topology X))
              (SheafOfModules.changeOfRingsPresheaf
                (integralComparisonSequenceScalarMap l E L ι X) N).presheaf).app U
                  ((1 : (coefficientSequenceCommRingSheaf l L X).obj.obj U)
                    ⊗ₜ[(coefficientSequenceCommRingSheaf l E X).obj.obj U,
                      ((integralComparisonSequenceScalarMap l E L ι X).hom.app U).hom] x)) := by
  exact SequenceScalarConstruction.scalarOrdinaryAdjunction
    (integralComparisonSequenceScalarMap l E L ι X)
    (integralComparisonSequenceScalarModel l E L ι X)

/-- The system pullback generator is the actual adjunction unit on sections.
Source: Stacks 03D2, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceGenerator {Y Z : Scheme.{t}} (f : Z ⟶ Y)
    (M : coefficientSequenceModules l E Y) (n : ℕ) (U : Y.ProEt)
    (x : M.val.obj (op (n, U))) :=
  (((Adjunction.ofIsRightAdjoint
    (integralComparisonSequenceDirectImage l E f)).unit.app M).val.app (op (n, U))) x

private noncomputable def sequenceDirectComp {V W Z : Scheme.{t}}
    (h : Z ⟶ W) (k : W ⟶ V) :
    integralComparisonSequenceDirectImage l E h ⋙
      integralComparisonSequenceDirectImage l E k ≅
        integralComparisonSequenceDirectImage l E (h ≫ k) :=
  (AmbientPullbackTensor.pushComp_existsUnique l E h k none).exists.choose.symm

private theorem sequenceDirectComp_apply {V W Z : Scheme.{t}}
    (h : Z ⟶ W) (k : W ⟶ V) (M : coefficientSequenceModules l E Z)
    (U : (ℕ × V.ProEt)ᵒᵖ)
    (x : ((integralComparisonSequenceDirectImage l E h ⋙
      integralComparisonSequenceDirectImage l E k).obj M).val.obj U) :
    ((sequenceDirectComp l E h k).hom.app M).val.app U x =
      M.val.map (Prod.mkHom (𝟙 U.unop.1)
        ((MorphismProperty.Over.pullbackComp h k).hom.app U.unop.2)).op x := by
  exact AmbientPullbackTensor.pushComp_inverse_sections l E h k none M U.unop x

attribute [local irreducible] sequenceDirectComp

/-- The ordinary compositor is determined by fibre-product pasting and mates.
Source: Stacks 0D6D, 03D3
(blueprint: def-trf-integral-comparison-sequence-systems).
Proof: direct images compose by the displayed sectionwise fibre-product map.
The coefficient actions agree because both send constant sections to themselves.
This gives the unique d. Take its mate under the actual adjunctions; mates
preserve isomorphisms and their bijection proves uniqueness of a. -/
theorem integralComparisonSequenceComposition_existsUnique
    {V W Z : Scheme.{t}} (h : Z ⟶ W) (k : W ⟶ V) :
    ∃! a : integralComparisonSequencePullback l E (h ≫ k) ≅
      integralComparisonSequencePullback l E k ⋙ integralComparisonSequencePullback l E h,
      ∃ d : integralComparisonSequenceDirectImage l E h ⋙
          integralComparisonSequenceDirectImage l E k ≅
            integralComparisonSequenceDirectImage l E (h ≫ k),
        conjugateIsoEquiv
          ((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E k)).comp
            (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h)))
          (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E (h ≫ k))) a = d ∧
        ∀ (M : coefficientSequenceModules l E Z) (n : ℕ) (U : V.ProEt)
          (x : ((integralComparisonSequenceDirectImage l E h ⋙
            integralComparisonSequenceDirectImage l E k).obj M).val.obj (op (n, U))),
          (d.hom.app M).val.app (op (n, U)) x =
            M.val.map (CategoryTheory.Prod.mkHom (𝟙 n)
              ((MorphismProperty.Over.pullbackComp h k).hom.app U)).op x := by
  let adj := (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E k)).comp
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h))
  let adj' := Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E (h ≫ k))
  let d := sequenceDirectComp l E h k
  refine ⟨(conjugateIsoEquiv adj adj').symm d, ⟨d, ?_, ?_⟩, ?_⟩
  · exact (conjugateIsoEquiv adj adj').apply_symm_apply d
  · intro M n U x
    exact sequenceDirectComp_apply l E h k M (op (n, U)) x
  · rintro a ⟨d', ha, hd'⟩
    apply (conjugateIsoEquiv adj adj').injective
    rw [ha, Equiv.apply_symm_apply]
    apply Iso.ext
    ext M U x
    exact (hd' M U.unop.1 U.unop.2 x).trans
      (sequenceDirectComp_apply l E h k M U x).symm

/-- The canonical ordinary composition map, retaining every quotient transition.
Source: Stacks 0D6D (blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceComposition {V W Z : Scheme.{t}}
    (h : Z ⟶ W) (k : W ⟶ V) :=
  (integralComparisonSequenceComposition_existsUnique l E h k).exists.choose

/-- Derived composition is the localization of that one strict system map.
Source: Stacks 0D6D, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSystemComposition {V W Z : Scheme.{t}}
    (h : Z ⟶ W) (k : W ⟶ V) :
    integralComparisonDerivedSequencePullback l E (h ≫ k) ≅
      integralComparisonDerivedSequencePullback l E k ⋙
        integralComparisonDerivedSequencePullback l E h :=
  Functor.mapDerivedCategoryNatIso (integralComparisonSequenceComposition l E h k) ≪≫
    (Functor.mapDerivedCategoryCompIso (integralComparisonSequencePullback l E k)
      (integralComparisonSequencePullback l E h)).symm

/-- An actual scalar-unit section in sequence-site change of rings.
Source: Stacks 06YY (blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceTensorSection (Y : Scheme.{t})
    (M : coefficientSequenceModules l E Y) (U : (ℕ × Y.ProEt)ᵒᵖ)
    (s : (coefficientSequenceCommRingSheaf l L Y).obj.obj U) (x : M.val.obj U) :
    ((integralComparisonSequenceScalarModel l E L ι Y).E.obj M).val.obj U :=
  (eqToHom ((integralComparisonSequenceScalarModel l E L ι Y).obj_eq M).symm).val.app U
    ((toSheafify (coefficientSequenceTopology (ProEt.topology Y))
      (SheafOfModules.changeOfRingsPresheaf
        (integralComparisonSequenceScalarMap l E L ι Y) M).presheaf).app U
          (s ⊗ₜ[(coefficientSequenceCommRingSheaf l E Y).obj.obj U,
            ((integralComparisonSequenceScalarMap l E L ι Y).hom.app U).hom] x))

private theorem sequenceTensorSection_eq (Y : Scheme.{t})
    (N : coefficientSequenceModules l E Y) (U : (ℕ × Y.ProEt)ᵒᵖ)
    (s : (coefficientSequenceCommRingSheaf l L Y).obj.obj U) (x : N.val.obj U) :
    integralComparisonSequenceTensorSection l E L ι Y N U s x =
      SheafOfModules.systemModelTmul (integralComparisonSequenceScalarModel l E L ι Y)
        N U s x :=
  SequenceScalarConstruction.modelTmul_eq (integralComparisonSequenceScalarMap l E L ι Y)
    (integralComparisonSequenceScalarModel l E L ι Y) N U s x

private theorem sequenceScalarPullbackRing {Y Z : Scheme.{t}} (f : Z ⟶ Y) :
    integralComparisonSequenceRingMap l E f ≫
        ((integralComparisonSequenceBaseChange f).sheafPushforwardContinuous _
          (coefficientSequenceTopology (ProEt.topology Y))
          (coefficientSequenceTopology (ProEt.topology Z))).map
            (integralComparisonSequenceScalarMap l E L ι Z) =
      integralComparisonSequenceScalarMap l E L ι Y ≫
        integralComparisonSequenceRingMap l L f := by
  ext U : 3
  exact congrArg (fun α ↦ α.hom.app (op U.unop.2))
    (sequenceConstantMap_naturality f (CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((integralScalarQuotientMap l E L ι U.unop.1).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom)))).symm

private theorem sequenceScalarAdjunction_unit (X : Scheme.{t})
    (N : coefficientSequenceModules l E X) (U : (ℕ × X.ProEt)ᵒᵖ) (x : N.val.obj U) :
    (((sequenceScalarAdjunction l E L ι X).choose.unit.app N).val.app U x) =
      integralComparisonSequenceTensorSection l E L ι X N U 1 x :=
  (sequenceScalarAdjunction l E L ι X).choose_spec N U x

attribute [local irreducible] integralComparisonSequenceTensorSection

private noncomputable def sequenceScalarPullbackRight {Y Z : Scheme.{t}} (f : Z ⟶ Y) :
    SheafOfModules.restrictScalars ((sheafCompose
      (coefficientSequenceTopology (ProEt.topology Z)) (forget₂ CommRingCat RingCat)).map
        (integralComparisonSequenceScalarMap l E L ι Z)) ⋙
          integralComparisonSequenceDirectImage l E f ≅
      integralComparisonSequenceDirectImage l L f ⋙
        SheafOfModules.restrictScalars ((sheafCompose
          (coefficientSequenceTopology (ProEt.topology Y)) (forget₂ CommRingCat RingCat)).map
            (integralComparisonSequenceScalarMap l E L ι Y)) := by
  refine NatIso.ofComponents (fun N ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_)) ?_
  · intro r
    ext x
    have hr := congrArg (fun α ↦ α.hom.app U r)
      (sequenceScalarPullbackRing l E L ι f)
    change _ = _
    exact congrArg (fun s : (coefficientSequenceCommRingSheaf l L Z).obj.obj
      ((integralComparisonSequenceBaseChange f).op.obj U) ↦
        s • (show N.val.obj ((integralComparisonSequenceBaseChange f).op.obj U) from x)) hr.symm
  · intros
    ext x
    rfl
  · intros
    ext U x
    rfl

private theorem normalizedAdjointComparison
    {A B : Type*} [Category A] [Category B]
    (F G : A ⥤ B) (R T : B ⥤ A)
    (adj₁ : F ⊣ R) (adj₂ : G ⊣ T) (e : R ≅ T) :
    ∃! a : F ≅ G, ∀ X,
      adj₂.unit.app X ≫ e.inv.app (G.obj X) =
        adj₁.unit.app X ≫ R.map (a.hom.app X) := by
  let a := (conjugateIsoEquiv adj₂ adj₁).symm e.symm
  refine ⟨a, fun X ↦ unit_conjugateEquiv_symm adj₂ adj₁ e.inv X, ?_⟩
  intro b hb
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (adj₁.homEquiv X _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact (hb X).symm.trans (unit_conjugateEquiv_symm adj₂ adj₁ e.inv X)

private theorem sequenceScalarPullbackRight_inv_app {Y Z : Scheme.{t}} (f : Z ⟶ Y)
    (N : coefficientSequenceModules l L Z) (U : (ℕ × Y.ProEt)ᵒᵖ)
    (x : N.val.obj ((integralComparisonSequenceBaseChange f).op.obj U)) :
    ((sequenceScalarPullbackRight l E L ι f).inv.app N).val.app U x = x := by
  rfl

attribute [local irreducible] sequenceScalarPullbackRight

/-- The ordinary scalar/pullback associator of whole quotient diagrams is fixed
on adjunction-unit tensor generators. Source: Stacks 06YY, 03D3
(blueprint: def-trf-integral-comparison-sequence-systems).
Proof: both functors sheafify the same scalar-balanced generators. Send the
specified unit tensor to the specified pullback of the unit tensor; multiply
scalars for the inverse. These formulas commute with vertical restrictions and
horizontal quotients, and local tensor generators prove uniqueness. -/
theorem integralComparisonSequenceScalarPullback_existsUnique
    {Y Z : Scheme.{t}} (f : Z ⟶ Y) :
    ∃! a : integralComparisonSequencePullback l E f ⋙
        (integralComparisonSequenceScalarModel l E L ι Z).E ≅
      (integralComparisonSequenceScalarModel l E L ι Y).E ⋙
        integralComparisonSequencePullback l L f,
      ∀ (M : coefficientSequenceModules l E Y) (n : ℕ) (U : Y.ProEt)
        (x : M.val.obj (op (n, U))),
      (a.hom.app M).val.app (op (n, (proEtaleBaseChange f).obj U))
        (integralComparisonSequenceTensorSection l E L ι Z
          ((integralComparisonSequencePullback l E f).obj M)
          (op (n, (proEtaleBaseChange f).obj U)) 1
          (integralComparisonSequenceGenerator l E f M n U x)) =
        integralComparisonSequenceGenerator l L f
          ((integralComparisonSequenceScalarModel l E L ι Y).E.obj M) n U
          (integralComparisonSequenceTensorSection l E L ι Y M (op (n, U)) 1 x) := by
  let adjY := (sequenceScalarAdjunction l E L ι Y).choose
  have hY := sequenceScalarAdjunction_unit l E L ι Y
  let adjZ := (sequenceScalarAdjunction l E L ι Z).choose
  have hZ := sequenceScalarAdjunction_unit l E L ι Z
  let pE := Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)
  let pL := Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l L f)
  let adj₁ := pE.comp adjZ
  let adj₂ := adjY.comp pL
  let e := sequenceScalarPullbackRight l E L ι f
  let h := normalizedAdjointComparison _ _ _ _ adj₁ adj₂ e
  let a := h.choose
  have hunit := h.choose_spec.1
  have huniq := h.choose_spec.2
  have ha (N : coefficientSequenceModules l E Y) (n : ℕ) (U : Y.ProEt)
      (x : N.val.obj (op (n, U))) :
      (a.hom.app N).val.app (op (n, (proEtaleBaseChange f).obj U))
        (integralComparisonSequenceTensorSection l E L ι Z
          ((integralComparisonSequencePullback l E f).obj N)
          (op (n, (proEtaleBaseChange f).obj U)) 1
          (integralComparisonSequenceGenerator l E f N n U x)) =
        integralComparisonSequenceGenerator l L f
          ((integralComparisonSequenceScalarModel l E L ι Y).E.obj N) n U
          (integralComparisonSequenceTensorSection l E L ι Y N (op (n, U)) 1 x) := by
    have hh := hunit N
    have hv := congrArg (fun q ↦ q.val.app (op (n, U)) x) hh
    dsimp only [Adjunction.comp_unit_app, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply] at hv
    change (e.inv.app _).val.app (op (n, U))
        ((pL.unit.app _).val.app (op (n, U))
          ((adjY.unit.app N).val.app (op (n, U)) x)) =
      (a.hom.app N).val.app (op (n, (proEtaleBaseChange f).obj U))
        ((adjZ.unit.app _).val.app (op (n, (proEtaleBaseChange f).obj U))
          ((pE.unit.app N).val.app (op (n, U)) x)) at hv
    rw [sequenceScalarPullbackRight_inv_app, hY, hZ] at hv
    exact hv.symm
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply huniq b
  intro N
  ext U x
  change (e.inv.app _).val.app U
      ((pL.unit.app _).val.app U ((adjY.unit.app N).val.app U x)) =
    (b.hom.app N).val.app ((integralComparisonSequenceBaseChange f).op.obj U)
      ((adjZ.unit.app _).val.app ((integralComparisonSequenceBaseChange f).op.obj U)
        ((pE.unit.app N).val.app U x))
  rw [sequenceScalarPullbackRight_inv_app, hY, hZ]
  exact (hb N U.unop.1 U.unop.2 x).symm

/-- The generator-normalized ordinary scalar comparison.
Source: Stacks 06YY (blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceScalarPullback {Y Z : Scheme.{t}} (f : Z ⟶ Y) :=
  (integralComparisonSequenceScalarPullback_existsUnique l E L ι f).exists.choose

namespace SequenceDerivedProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe a b c d e f
open CategoryTheory.Functor

private theorem normalizedComparisonDescent
    {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
    {E : Type e} [Category.{f} E]
    (L : C ⥤ D) (P : ObjectProperty C)
    (ff : ((whiskeringLeft P.FullSubcategory D E).obj (P.ι ⋙ L)).FullyFaithful)
    (F G : D ⥤ E) (H : C ⥤ E) (α : L ⋙ F ⟶ H) (β : L ⋙ G ⟶ H)
    (hα : ∀ X, P X → IsIso (α.app X)) (hβ : ∀ X, P X → IsIso (β.app X)) :
    ∃! a : F ≅ G, ∀ X, P X → α.app X = a.hom.app (L.obj X) ≫ β.app X := by
  let eα : (P.ι ⋙ L) ⋙ F ≅ P.ι ⋙ H := NatIso.ofComponents
    (fun X ↦ @asIso _ _ _ _ (α.app X.obj) (hα X.obj X.property))
    (fun g ↦ α.naturality g.hom)
  let eβ : (P.ι ⋙ L) ⋙ G ≅ P.ι ⋙ H := NatIso.ofComponents
    (fun X ↦ @asIso _ _ _ _ (β.app X.obj) (hβ X.obj X.property))
    (fun g ↦ β.naturality g.hom)
  let a : F ≅ G := ff.preimageIso (eα ≪≫ eβ.symm)
  have ha (X : C) (hX : P X) :
      α.app X = a.hom.app (L.obj X) ≫ β.app X := by
    have := hβ X hX
    have hh := congrArg (fun t ↦ t.app ⟨X, hX⟩) (ff.map_preimage (eα ≪≫ eβ.symm).hom)
    change a.hom.app (L.obj X) = α.app X ≫ CategoryTheory.inv (β.app X) at hh
    rw [hh, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  refine ⟨a, ha, ?_⟩
  intro a' ha'
  apply Iso.ext
  apply ff.map_injective
  ext X
  have := hβ X.obj X.property
  apply (cancel_mono (β.app X.obj)).1
  exact (ha' X.obj X.property).symm.trans (ha X.obj X.property)

private theorem kflatWhiskering
    {D : Type e} [Category.{f} D]
    {C : Type a} [Category.{b} C] [EssentiallySmall.{c} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{c} RingCat.{c})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{c}]
    [HasSheafify J AddCommGrpCat.{c}]
    (R : Sheaf J CommRingCat.{c})
    [HasDerivedCategory.{d} (SheafOfModules.{c}
      ((sheafCompose J (forget₂ CommRingCat.{c} RingCat.{c})).obj R))] :
    let A := SheafOfModules.{c}
      ((sheafCompose J (forget₂ CommRingCat.{c} RingCat.{c})).obj R)
    let P : ObjectProperty (CochainComplex A ℤ) :=
      CochainComplex.IsKFlatIndependentCoefficients (R := R)
    Nonempty (((whiskeringLeft P.FullSubcategory (DerivedCategory A) D).obj
      (P.ι ⋙ DerivedCategory.Q)).FullyFaithful) := by
  exact SequenceComparisonConstruction.kflatWhiskering R

universe g h wA wB wC wD

private theorem derivedComparison
    {A : Type a} [Category.{b} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type c} [Category.{d} B] [Abelian B] [HasDerivedCategory.{wB} B]
    {C : Type e} [Category.{f} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {D : Type g} [Category.{h} D] [Abelian D] [HasDerivedCategory.{wD} D]
    (p : A ⥤ B) [p.Additive] [PreservesFiniteLimits p] [PreservesFiniteColimits p]
    (q : C ⥤ D) [q.Additive] [PreservesFiniteLimits q] [PreservesFiniteColimits q]
    (s : A ⥤ C) [s.Additive] (t : B ⥤ D) [t.Additive]
    (LS : DerivedCategory A ⥤ DerivedCategory C)
    (LT : DerivedCategory B ⥤ DerivedCategory D)
    (εS : DerivedCategory.Q ⋙ LS ⟶ s.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (εT : DerivedCategory.Q ⋙ LT ⟶ t.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (c : p ⋙ t ≅ s ⋙ q) (R good : ObjectProperty (CochainComplex A ℤ))
    (ff : ((whiskeringLeft R.FullSubcategory (DerivedCategory A) (DerivedCategory D)).obj
      (R.ι ⋙ DerivedCategory.Q)).FullyFaithful)
    (hgood : ∀ X, good X → R X)
    (hres : ∀ X, R X → ∃ (Y : CochainComplex A ℤ) (r : Y ⟶ X), good Y ∧ QuasiIso r)
    (hS : ∀ X, R X → IsIso (εS.app X))
    (hT : ∀ X, good X → IsIso (εT.app ((p.mapHomologicalComplex (.up ℤ)).obj X))) :
    ∃! a : p.mapDerivedCategory ⋙ LT ≅ LS ⋙ q.mapDerivedCategory,
      ∀ X, R X →
        LT.map (p.mapDerivedCategoryFactors.hom.app X) ≫
          εT.app ((p.mapHomologicalComplex (.up ℤ)).obj X) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app X) =
        a.hom.app (DerivedCategory.Q.obj X) ≫ q.mapDerivedCategory.map (εS.app X) ≫
          q.mapDerivedCategoryFactors.hom.app ((s.mapHomologicalComplex (.up ℤ)).obj X) := by
  exact SequenceComparisonConstruction.derivedComparison p q s t LS LT εS εT c R good
    ff hgood hres hS hT

end SequenceDerivedProof
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem sequencePullback_kflatgood {Y Z : Scheme.{t}} (f : Z ⟶ Y)
    (P : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)}
      (R := coefficientSequenceCommRingSheaf l E Y) P)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)}
      (R := coefficientSequenceCommRingSheaf l E Z)
      (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨A, TA, _⟩ := ringedDerived_closed_symmetric_monoidal.{t + 1, t, u,
    (max u (t + 1)) + 1} (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y)
  obtain ⟨B, TB, _⟩ := ringedDerived_closed_symmetric_monoidal.{t + 1, t, u,
    (max u (t + 1)) + 1} (coefficientSequenceTopology (ProEt.topology Z))
      (coefficientSequenceCommRingSheaf l E Z)
  obtain ⟨K, hK, _⟩ := AmbientPullbackTensor.tensorData_existsUnique l E f none A B TA TB
  exact (hK.2.2.2 P ⟨hP, hf⟩).1

/-- The derived scalar comparison is the localization of that same entire-diagram
map; the equation uses the universal scalar counits, not only finite evaluations.
Source: Stacks 06YY, 0D6D
(blueprint: def-trf-integral-comparison-sequence-systems).
Proof: exact constant-coefficient inverse image preserves flat-term K-flat
complexes. Localize the ordinary tensor associator on K-flat resolutions using
the two universal scalar counits. Roofs give naturality and independence of
resolutions; their localization universal property gives uniqueness. -/
theorem integralComparisonSystemScalarPullback_existsUnique
    {Y Z : Scheme.{t}} (f : Z ⟶ Y) :
    ∃! a : integralComparisonDerivedSequencePullback l E f ⋙
        integralComparisonDerivedSequenceScalar l E L ι Z ≅
      integralComparisonDerivedSequenceScalar l E L ι Y ⋙
        integralComparisonDerivedSequencePullback l L f,
      ∀ (P : CochainComplex (coefficientSequenceModules l E Y) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients
          (R := coefficientSequenceCommRingSheaf l E Y) P →
        (integralComparisonDerivedSequenceScalar l E L ι Z).map
          ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app P) ≫
          (integralComparisonSequenceScalarModel l E L ι Z).ε.app
            (((integralComparisonSequencePullback l E f).mapHomologicalComplex
              (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              (integralComparisonSequenceScalarPullback l E L ι f) (.up ℤ)).hom.app P) =
        a.hom.app (DerivedCategory.Q.obj P) ≫
          (integralComparisonDerivedSequencePullback l L f).map
            ((integralComparisonSequenceScalarModel l E L ι Y).ε.app P) ≫
          (integralComparisonSequencePullback l L f).mapDerivedCategoryFactors.hom.app
            (((integralComparisonSequenceScalarModel l E L ι Y).E.mapHomologicalComplex
              (.up ℤ)).obj P) := by
  let A := coefficientSequenceModules l E Y
  let B := coefficientSequenceModules l L Z
  let R : ObjectProperty (CochainComplex A ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E Y)
  let good : ObjectProperty (CochainComplex A ℤ) := fun X ↦ R X ∧
    ∀ n : ℤ, SheafOfModules.IsFlatOnSite
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) (X.X n)
  have hres : ∀ X, R X → ∃ (K : CochainComplex A ℤ) (r : K ⟶ X), good K ∧ QuasiIso r := by
    intro X _
    obtain ⟨K, r, hK, hf, hr, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X
    have hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite
        (J := coefficientSequenceTopology (ProEt.topology Y))
        (R := coefficientSequenceCommRingSheaf l E Y) (K.X n) := by
      intro n
      exact (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso
          (coefficientSequenceCommRingSheaf l E Y) (K.X n)).symm (hf n)
    have hgood : good K := ⟨hK, hflat⟩
    exact ⟨K, r, hgood, hr⟩
  obtain ⟨ff⟩ := SequenceDerivedProof.kflatWhiskering (D := DerivedCategory B)
    (coefficientSequenceCommRingSheaf l E Y)
  exact SequenceDerivedProof.derivedComparison
    (integralComparisonSequencePullback l E f) (integralComparisonSequencePullback l L f)
    (integralComparisonSequenceScalarModel l E L ι Y).E
    (integralComparisonSequenceScalarModel l E L ι Z).E
    (integralComparisonSequenceScalarModel l E L ι Y).T
    (integralComparisonSequenceScalarModel l E L ι Z).T
    (integralComparisonSequenceScalarModel l E L ι Y).ε
    (integralComparisonSequenceScalarModel l E L ι Z).ε
    (integralComparisonSequenceScalarPullback l E L ι f) R good ff
    (fun _ h ↦ h.1) hres
    (integralComparisonSequenceScalarModel l E L ι Y).computes
    (fun X h ↦ (integralComparisonSequenceScalarModel l E L ι Z).computes _
      (sequencePullback_kflatgood l E f X h.1 h.2))

/-- The localized entire-diagram scalar associator.
Source: Stacks 06YY (blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSystemScalarPullback {Y Z : Scheme.{t}} (f : Z ⟶ Y) :=
  (integralComparisonSystemScalarPullback_existsUnique l E L ι f).exists.choose

private noncomputable def sequenceDirectId (Y : Scheme.{t}) :
    𝟭 (coefficientSequenceModules l E Y) ≅ integralComparisonSequenceDirectImage l E (𝟙 Y) :=
  (AmbientPullbackTensor.pushId_existsUnique l E Y none).exists.choose.symm

private theorem sequenceDirectId_apply (Y : Scheme.{t})
    (M : coefficientSequenceModules l E Y) (U : Y.ProEt) (n : ℕ)
    (x : M.val.obj (op (n, U))) :
    ((sequenceDirectId l E Y).hom.app M).val.app (op (n, U)) x =
      M.val.map (Prod.mkHom (𝟙 n)
        ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Y).hom.app U)).op x := by
  exact AmbientPullbackTensor.pushId_inverse_sections l E Y none M (n, U) x

attribute [local irreducible] sequenceDirectId

/-- The ordinary identity pullback is fixed by its adjunction-unit formula.
Source: Stacks 03D3, 0D6D
(blueprint: def-trf-integral-comparison-sequence-systems).
Proof: the pullback of the identity scheme map is naturally the identity by
the universal property of fibre products. The unit formula defines the mate
between the ordinary module inverse images. The adjunction bijection gives
uniqueness, and the inverse fibre-product map gives its inverse. -/
theorem integralComparisonSequenceUnit_existsUnique (Y : Scheme.{t}) :
    ∃! a : integralComparisonSequencePullback l E (𝟙 Y) ≅ 𝟭 _,
      ∀ (M : coefficientSequenceModules l E Y) (n : ℕ) (U : Y.ProEt)
        (x : M.val.obj (op (n, U))),
        (a.hom.app M).val.app (op (n, (proEtaleBaseChange (𝟙 Y)).obj U))
          (integralComparisonSequenceGenerator l E (𝟙 Y) M n U x) =
        M.val.map (CategoryTheory.Prod.mkHom (𝟙 n)
          ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Y).hom.app U)).op x := by
  let adj := Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E (𝟙 Y))
  let d := sequenceDirectId l E Y
  let a := (conjugateIsoEquiv Adjunction.id adj).symm d
  have ha (M : coefficientSequenceModules l E Y) (n : ℕ) (U : Y.ProEt)
      (x : M.val.obj (op (n, U))) :
      (a.hom.app M).val.app (op (n, (proEtaleBaseChange (𝟙 Y)).obj U))
        (integralComparisonSequenceGenerator l E (𝟙 Y) M n U x) =
      M.val.map (Prod.mkHom (𝟙 n)
        ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Y).hom.app U)).op x := by
    have hh := unit_conjugateEquiv_symm Adjunction.id adj d.hom M
    have hu := congrArg (fun q ↦ q.val.app (op (n, U)) x) hh.symm
    exact hu.trans (sequenceDirectId_apply l E Y M U n x)
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (adj.homEquiv M M).injective
  ext U x
  exact (hb M U.unop.1 U.unop.2 x).trans (ha M U.unop.1 U.unop.2 x).symm

/-- The specified identity inverse-image comparison on whole derived diagrams.
Source: Stacks 0D6D (blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSystemUnit (Y : Scheme.{t}) :
    integralComparisonDerivedSequencePullback l E (𝟙 Y) ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso
    ((integralComparisonSequenceUnit_existsUnique l E Y).exists.choose) ≪≫
      Functor.mapDerivedCategoryIdIso _

variable (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (j : L →ₐ[ℚ_[l]] M)

private theorem sequenceScalarMapComp (Y : Scheme.{t}) :
    integralComparisonSequenceScalarMap l E L ι Y ≫
      integralComparisonSequenceScalarMap l L M j Y =
        integralComparisonSequenceScalarMap l E M (j.comp ι) Y := by
  have hq (n : ℕ) : (integralScalarQuotientMap l L M j n).comp
      (integralScalarQuotientMap l E L ι n) =
        integralScalarQuotientMap l E M (j.comp ι) n := by
    apply RingHom.ext
    intro x
    induction x using Quotient.inductionOn' with
    | h x => rfl
  have hs (n : ℕ) : integralScalarQuotientSheafMap l E L ι Y n ≫
      integralScalarQuotientSheafMap l L M j Y n =
        integralScalarQuotientSheafMap l E M (j.comp ι) Y n := by
    unfold integralScalarQuotientSheafMap
    rw [← Functor.map_comp]
    congr 1
    ext x
    exact congrArg (fun f ↦ f x.down) (hq n)
  ext U : 3
  exact congrArg (fun α ↦ α.hom.app (op U.unop.2)) (hs U.unop.1)

/-- The ordinary scalar associator is fixed on sheafified tensor generators
on the whole sequence site. Source: Stacks 06YY, 0941
(blueprint: def-trf-integral-comparison-sequence-systems).
Proof: send c tensor (b tensor x) to c*j(b) tensor x, with inverse c tensor x
to c tensor (1 tensor x). Balanced relations and sheafification extend these
formulas uniquely. The quotient maps are ring maps, so all horizontal squares
commute, and vertical restrictions commute by tensor functoriality. -/
theorem integralComparisonSequenceScalarComposition_existsUnique (Y : Scheme.{t}) :
    ∃! a : (integralComparisonSequenceScalarModel l E L ι Y).E ⋙
        (integralComparisonSequenceScalarModel l L M j Y).E ≅
      (integralComparisonSequenceScalarModel l E M (j.comp ι) Y).E,
      ∀ (N : coefficientSequenceModules l E Y) (U : (ℕ × Y.ProEt)ᵒᵖ)
        (c : (coefficientSequenceCommRingSheaf l M Y).obj.obj U)
        (b : (coefficientSequenceCommRingSheaf l L Y).obj.obj U) (x : N.val.obj U),
        (a.hom.app N).val.app U
          (integralComparisonSequenceTensorSection l L M j Y
            ((integralComparisonSequenceScalarModel l E L ι Y).E.obj N) U c
            (integralComparisonSequenceTensorSection l E L ι Y N U b x)) =
          integralComparisonSequenceTensorSection l E M (j.comp ι) Y N U
            (c * (integralComparisonSequenceScalarMap l L M j Y).hom.app U b) x := by
  simp only [sequenceTensorSection_eq]
  exact SequenceScalarConstruction.fixedScalarCompositionUnique
    (sequenceScalarMapComp l E L ι M j Y).symm
    (integralComparisonSequenceScalarModel l E L ι Y)
    (integralComparisonSequenceScalarModel l L M j Y)
    (integralComparisonSequenceScalarModel l E M (j.comp ι) Y)

/-- The strict scalar associator used before realization.
Source: Stacks 06YY (blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceScalarComposition (Y : Scheme.{t}) :=
  (integralComparisonSequenceScalarComposition_existsUnique l E L ι M j Y).exists.choose

end WeilConjectures

namespace WeilConjectures
open scoped ChangeOfRings

/-- The chosen ordinary identity inverse-image map, prior to localization.
Source: Stacks 0D6D, 03D3 (blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceUnit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{t}) :=
  (integralComparisonSequenceUnit_existsUnique l E X).exists.choose

private theorem sequenceScalarMapId (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{t}) :
    integralComparisonSequenceScalarMap l E E (AlgHom.id ℚ_[l] E) X = 𝟙 _ := by
  have hq (n : ℕ) : integralScalarQuotientMap l E E (AlgHom.id ℚ_[l] E) n =
      RingHom.id _ := by
    apply RingHom.ext
    intro x
    induction x using Quotient.inductionOn' with
    | h x => rfl
  have hs (n : ℕ) : integralScalarQuotientSheafMap l E E (AlgHom.id ℚ_[l] E) X n =
      𝟙 _ := by
    unfold integralScalarQuotientSheafMap
    rw [hq]
    have hid : CommRingCat.ofHom
        ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
          ((RingHom.id _).comp (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom)) =
        𝟙 (CommRingCat.of (ULift.{t + 1}
          (Padic.coefficientExtensionRing l E (n + 1)))) := by
      ext x
      rfl
    rw [hid]
    exact (constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map_id _
  ext U : 3
  exact congrArg (fun α ↦ α.hom.app (op U.unop.2)) (hs U.unop.1)

/-- Multiplication determines the identity scalar extension on whole quotient systems.
Source: Stacks 06YY (blueprint: def-trf-integral-comparison-sequence-systems).
Proof: multiplication of a scalar and a module section is balanced and commutes with
all quotient transitions and restrictions. Sheafification extends it to scalar change.
The inverse inserts the scalar one. The tensor relations give both inverse equations,
and local generation by tensors gives uniqueness. -/
theorem integralComparisonSequenceScalarUnit_existsUnique (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{t}) :
    ∃! a : (integralComparisonSequenceScalarModel l E E (AlgHom.id ℚ_[l] E) X).E ≅ 𝟭 _,
      ∀ (N : coefficientSequenceModules l E X) (U : (ℕ × X.ProEt)ᵒᵖ)
        (s : (coefficientSequenceCommRingSheaf l E X).obj.obj U) (x : N.val.obj U),
        (a.hom.app N).val.app U
          (integralComparisonSequenceTensorSection l E E (AlgHom.id ℚ_[l] E) X N U s x) =
            s • x := by
  simp only [sequenceTensorSection_eq]
  exact SequenceScalarConstruction.fixedScalarUnitUnique
    (sequenceScalarMapId l E X)
    (integralComparisonSequenceScalarModel l E E (AlgHom.id ℚ_[l] E) X)

/-- Multiplication on the actual quotient systems is the scalar unit.
Source: Stacks 06YY (blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceScalarUnit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{t}) :=
  (integralComparisonSequenceScalarUnit_existsUnique l E X).exists.choose

end WeilConjectures

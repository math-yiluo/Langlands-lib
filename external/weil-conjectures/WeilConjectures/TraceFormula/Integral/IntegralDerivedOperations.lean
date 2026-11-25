/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.AlgebraicGeometry.RestrictionOfScalarsExact
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.SixFunctors.Integral.IntegralDerivedReductionSupplement
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlat
public import WeilConjectures.Algebra.Homology.ChangeOfRingsComplex
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellation
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
public import Mathlib.CategoryTheory.Sites.CompatibleSheafification
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.Algebra.Homology.Functor

/-! # Integral derived operations

Source: Bhatt--Scholze, Definition 3.4.10 and Lemmas 3.4.11, 3.4.12(4), 6.5.9(4);
Stacks Project, Tag 099N(5) (blueprint: def-pur-integral-derived-operations).

The coefficient completion, positive finite reductions, K-flat representatives,
canonical transition maps and Roos complexes are those of the dependency modules.
The first two functors are their normalized descents, chosen together with their
representative comparisons, which determine them up to unique compatible isomorphism.
Internal Hom is the ambient derived internal Hom over the completed coefficient sheaf.
No derived-completeness or constructibility hypothesis is imposed.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory Opposite

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section PullbackDescent

attribute [local instance 3000] integralTowerHasDerivedCategory

/-- A completed pullback descent, its representative comparison, and its universal property.
The record keeps the existing choices together so consumers need not unfold nested existentials.
Source: Bhatt--Scholze, Lemma 6.5.9(4); Stacks Project, Tag 099N(5)
(blueprint: def-trf-integral-pullback-descent-model). -/
structure IntegralPullbackDescent {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) where
  functor : DerivedCategory (integralTowerModules l E Y) ⥤
    DerivedCategory (integralTowerModules l E X)
  comparison : integralOperationsGoodLocalization l E Y ⋙ functor ≅
    integralOperationsPullbackOnGood l E f
  universal : ∀ (G : DerivedCategory (integralTowerModules l E Y) ⥤
      DerivedCategory (integralTowerModules l E X))
    (e : integralOperationsGoodLocalization l E Y ⋙ G ≅
      integralOperationsPullbackOnGood l E f),
    ∃! i : functor ≅ G,
      Functor.isoWhiskerLeft (integralOperationsGoodLocalization l E Y) i ≪≫ e = comparison

/-- The existing normalized pullback descent, packaged without making a new choice.
Its universal property determines the data up to unique compatible isomorphism.
Source: Bhatt--Scholze, Lemma 6.5.9(4); Stacks Project, Tag 099N(5)
(blueprint: def-trf-integral-pullback-descent-model). -/
noncomputable def integralPullbackDescent {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) : IntegralPullbackDescent l E f where
  functor := (integralOperationsWellDefined l E f X).2.2.choose
  comparison := (integralOperationsWellDefined l E f X).2.2.choose_spec.choose
  universal :=
    (integralOperationsWellDefined l E f X).2.2.choose_spec.choose_spec
      |>.choose_spec.choose_spec.1

end PullbackDescent

/-- Completed integral derived pullback: the normalized descent of
P ↦ Cone(1-s)[-1] on the strict tower Res_n f*(P_n), with n denoting exponent n+1.
Source: Bhatt--Scholze, Lemma 6.5.9(4); Stacks Project, Tag 099N(5)
(blueprint: def-pur-integral-derived-operations). -/
noncomputable def integralDerivedPullback {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) :
    DerivedCategory (integralTowerModules.{t, u} l E Y) ⥤
      DerivedCategory (integralTowerModules.{t, u} l E X) :=
  (integralPullbackDescent l E f).functor

/-- The defining natural comparison on all K-flat representatives with flat terms.
Together with this comparison, the descent is unique up to unique isomorphism.
Source: Bhatt--Scholze, Lemma 6.5.9(4); Stacks Project, Tag 099N(5)
(blueprint: def-pur-integral-derived-operations). -/
noncomputable def integralDerivedPullbackComparison {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) :
    integralOperationsGoodLocalization l E Y ⋙ integralDerivedPullback l E f ≅
      integralOperationsPullbackOnGood l E f :=
  (integralPullbackDescent l E f).comparison

/-- A completed tensor descent, its model comparison, and its universal property.
The record keeps the data together so consumers do not unfold nested existence proofs.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4)
(blueprint: def-pur-integral-derived-operations). -/
structure IntegralCompletedTensorDescent (W : AlgebraicGeometry.Scheme.{t}) where
  functor : (DerivedCategory (integralTowerModules l E W)) ×
    (DerivedCategory (integralTowerModules l E W)) ⥤
      DerivedCategory (integralTowerModules l E W)
  comparison : ((integralOperationsGoodLocalization l E W).prod
    (integralOperationsGoodLocalization l E W)) ⋙ functor ≅
      integralOperationsTensorOnGood l E W
  universal : ∀ (G' : (DerivedCategory (integralTowerModules l E W)) ×
      (DerivedCategory (integralTowerModules l E W)) ⥤
        DerivedCategory (integralTowerModules l E W))
    (d' : ((integralOperationsGoodLocalization l E W).prod
      (integralOperationsGoodLocalization l E W)) ⋙ G' ≅
        integralOperationsTensorOnGood l E W),
    ∃! ι : functor ≅ G', Functor.isoWhiskerLeft
      ((integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W)) ι ≪≫ d' = comparison

/-- The existing normalized descent, packaged without making a new choice.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4)
(blueprint: def-pur-integral-derived-operations). -/
noncomputable def integralCompletedTensorDescent (W : AlgebraicGeometry.Scheme.{t}) :
    IntegralCompletedTensorDescent l E W where
  functor :=
    (integralOperationsWellDefined l E (𝟙 W) W).2.2.choose_spec.choose_spec.choose
  comparison :=
    (integralOperationsWellDefined l E (𝟙 W) W).2.2.choose_spec.choose_spec.choose_spec.choose
  universal :=
    (integralOperationsWellDefined l E (𝟙 W) W).2.2.choose_spec.choose_spec
      |>.choose_spec.choose_spec.2.1

/-- The completed tensor product is the normalized descent of the Roos complex
of Res_n(P_n ⊗ Q_n), with the direct-sum total tensor differential and the
pure-tensor reduction transitions specified in IntegralOperationsWellDefined.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4)
(blueprint: def-pur-integral-derived-operations). -/
noncomputable def integralCompletedTensor (W : AlgebraicGeometry.Scheme.{t}) :
    (DerivedCategory (integralTowerModules.{t, u} l E W)) ×
      (DerivedCategory (integralTowerModules.{t, u} l E W)) ⥤
        DerivedCategory (integralTowerModules.{t, u} l E W) :=
  (integralCompletedTensorDescent l E W).functor

/-- The defining natural comparison with the finite-tensor Roos construction on
pairs of K-flat complexes with flat terms. The descent with this comparison
is unique up to unique compatible isomorphism.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4)
(blueprint: def-pur-integral-derived-operations). -/
noncomputable def integralCompletedTensorComparison (W : AlgebraicGeometry.Scheme.{t}) :
    ((integralOperationsGoodLocalization l E W).prod
      (integralOperationsGoodLocalization l E W)) ⋙ integralCompletedTensor l E W ≅
        integralOperationsTensorOnGood l E W :=
  (integralCompletedTensorDescent l E W).comparison

/-- Integral internal Hom is the ambient derived sheaf Hom over the actual
completed ring sheaf, computed by a K-injective resolution of its second argument
among all modules over that sheaf. It is contravariant in its first argument.
Source: Bhatt--Scholze, Lemma 3.4.11; Stacks Project, Section 08J7
(blueprint: def-pur-integral-derived-operations). -/
noncomputable def integralDerivedInternalHom (W : AlgebraicGeometry.Scheme.{t}) :
    (DerivedCategory (integralTowerModules.{t, u} l E W))ᵒᵖ ×
      DerivedCategory (integralTowerModules.{t, u} l E W) ⥤
        DerivedCategory (integralTowerModules.{t, u} l E W) :=
  CategoryTheory.derivedInternalHomOfUniverses.{t + 1, t, u}
    (AlgebraicGeometry.Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)

end WeilConjectures

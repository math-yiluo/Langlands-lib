/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenTensorQuotientAugmentation
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerCanonical
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SixFunctors.Constructible.ConstructibleTensorCompletion
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
public import WeilConjectures.CategoryTheory.StrictRoosComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.StrictRoosDerivation
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.RoosComplex
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.StrictRoosNormalization
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.Basic.Denumerable
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosDescent
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains

/-! # The augmented open projection formula after Roos completion

Source: Stacks Project, proetale.tex, Tag 09BP, lemma-j-shriek-limits;
Bhatt--Scholze, Lemmas 6.5.5 and 6.5.8, pp.49--50; the augmentation-normalized
construction in the DAG (blueprint: lem-sf-open-projection-roos-completion).

The coefficient index n denotes the positive exponent n+1. The ambient categories
are the ordinary unbounded derived categories over the completed coefficient sheaf.
All comparison data below are conclusions, with their representative equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u a b c d wA wB
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenProjectionRoos

section Roos
variable {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]

/-- The boundary of the recorded strict Roos model, without changing its signs.
Source: Stacks 0941 (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev boundary (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) :=
  towerTransitionEndomorphism (K := fun n ↦ T.obj (op n)) (integralOperationsTowerStep T)

/-- Postcomposition of strict towers by the actual termwise functor.
Source: Stacks 0941 (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev onTowers (F : A ⥤ B) [F.Additive] :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (F.mapHomologicalComplex (.up ℤ))

/-- The normalized exact-product comparison. The first and shifted projection
identities specify its action on both summands of the signed mapping fiber.
The augmentation clause supplies the maps with coordinates (a,0) and states their
actual equality, before localization; it does not infer equality from limit projections.
Source: Stacks 09BP and lem-cbc-exact-product-functor-strict-limit
(blueprint: lem-sf-open-projection-roos-completion). -/
structure RoosComparison (F : A ⥤ B) [F.Additive] where
  products : ∀ T : ℕᵒᵖ ⥤ CochainComplex A ℤ,
    (F.mapHomologicalComplex (.up ℤ)).obj (∏ᶜ fun n ↦ T.obj (op n)) ≅
      ∏ᶜ fun n ↦ ((onTowers F).obj T).obj (op n)
  projections : ∀ (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) (n : ℕ),
    (products T).hom ≫ Pi.π (fun k ↦ ((onTowers F).obj T).obj (op k)) n =
      (F.mapHomologicalComplex (.up ℤ)).map (Pi.π (fun k ↦ T.obj (op k)) n)
  iso : integralOperationsRoosFunctor ⋙ F.mapHomologicalComplex (.up ℤ) ≅
    onTowers F ⋙ integralOperationsRoosFunctor
  first : ∀ (T : ℕᵒᵖ ⥤ CochainComplex A ℤ),
    (iso.hom.app T) ≫ CochainComplex.mappingCocone.fst (boundary ((onTowers F).obj T)) =
      (F.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCocone.fst (boundary T)) ≫ (products T).hom
  shifted : ∀ (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) (i k : ℤ) (h : i + -1 = k),
    (iso.hom.app T).f i ≫
        (CochainComplex.mappingCocone.snd (boundary ((onTowers F).obj T))).v i k h =
      F.map ((CochainComplex.mappingCocone.snd (boundary T)).v i k h) ≫
        ((products T).hom.f k)
  augmentations : ∀ (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) (P : CochainComplex A ℤ)
    (a : (Functor.const ℕᵒᵖ).obj P ⟶ T),
    ∃ (b : P ⟶ integralOperationsRoos T)
      (b' : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶
        integralOperationsRoos ((onTowers F).obj T)),
      b ≫ CochainComplex.mappingCocone.fst (boundary T) =
          Pi.lift (fun n ↦ a.app (op n)) ∧
      (∀ (i k : ℤ) (h : i + -1 = k),
        b.f i ≫ (CochainComplex.mappingCocone.snd (boundary T)).v i k h = 0) ∧
      b' ≫ CochainComplex.mappingCocone.fst (boundary ((onTowers F).obj T)) =
          Pi.lift (fun n ↦ (F.mapHomologicalComplex (.up ℤ)).map (a.app (op n))) ∧
      (∀ (i k : ℤ) (h : i + -1 = k), b'.f i ≫
        (CochainComplex.mappingCocone.snd (boundary ((onTowers F).obj T))).v i k h = 0) ∧
      (F.mapHomologicalComplex (.up ℤ)).map b ≫ iso.hom.app T = b'

variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]

/-- The same lambda in the derived category, through the canonical exact-functor
comparison. Roos computes the total right derived limit by the recorded strict-Roos
comparison, including its augmentation. No new derived-limit object is chosen.
Source: Stacks 0941 (blueprint: lem-sf-open-projection-roos-completion). -/
def RoosComparison.derived (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (r : RoosComparison F) (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    F.mapDerivedCategory.obj (DerivedCategory.Q.obj (integralOperationsRoos T)) ≅
      DerivedCategory.Q.obj (integralOperationsRoos ((onTowers F).obj T)) :=
  F.mapDerivedCategoryFactors.app (integralOperationsRoos T) ≪≫
    DerivedCategory.Q.mapIso (r.iso.app T)
end Roos

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : IntegralOpenReduction.Operations l E j)

/-- The source pair insertion for the open projection formula.
Source: blueprint open factor (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev leftInputs := (IntegralOpenReduction.shriek l E j o).prod
  (𝟭 (DerivedCategory (scalarReductionSource l E X)))

/-- The target pair insertion, with actual exact restriction.
Source: blueprint open factor (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev rightInputs := (𝟭 (DerivedCategory (scalarReductionSource l E U))).prod
  (IntegralOpenReduction.star l E j o)

/-- Inclusion of precisely the two bounded constructible integral domains.
Source: Bhatt--Scholze 6.5.8 (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev pairs := (sfIntegralConstructible l E U).ι.prod (sfIntegralConstructible l E X).ι

/-- The actual completed source functor on the stated constructible domain.
Source: Bhatt--Scholze 3.4.10 (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev completedLeft := pairs l E (U := U) (X := X) ⋙ leftInputs l E j o ⋙
  integralCompletedTensor l E X

/-- The actual completed tensor on U, before its extension.
Source: Bhatt--Scholze 3.4.10 (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev completedInside := pairs l E (U := U) (X := X) ⋙ rightInputs l E j o ⋙
  integralCompletedTensor l E U

/-- The actual completed target functor on the stated constructible domain.
Source: Bhatt--Scholze 3.4.10 (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev completedRight := completedInside l E j o ⋙ IntegralOpenReduction.shriek l E j o

attribute [local irreducible] integralOperationsTensorTowerFunctor
  coefficientTotalTensor integralOperationsTensorLevel
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  unrestrictedIntegralComplexFunctor scalarReductionExistence unrestrictedIntegralReductionExistence

variable
  (SX : CoefficientDerivedSystemCalculus l E X)
  (SU : CoefficientDerivedSystemCalculus l E U)
  (AX : OpenSemilinearTensor.OrdinaryReduction l E X)
  (AU : OpenSemilinearTensor.OrdinaryReduction l E U)
  (st : IntegralOpenReduction.TensorComparison l E j o)
  (m : OpenSemilinearTensor.Comparison l E j o SX SU AX AU st)
  (c : IntegralOpenReduction.Comparison l E j o SX SU st)
  (q : OpenTensorQuotient.Comparison l E j o SX SU AX AU st m c)

/-- The exact ordinary representative equation, kept as a shared proposition.
Source: Stacks 09BP and 0941; the original completion specification
(blueprint: def-sf-open-projection-roos-completion-data). -/
def OrdinaryRepresentative
    [restrictionLimits : PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o)]
    [restrictionColimits : PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o)]
    (flat : ∀ (W : Scheme.{u}) (P : CochainComplex (scalarReductionSource l E W) ℤ),
    integralOperationsGoodComplex l E W P →
      proEtaleFlatRepresentatives W (completedIntegralCommRingSheafUnrestricted l E W) P)
    (extendGood : ∀ (P : CochainComplex (scalarReductionSource l E U) ℤ),
    integralOperationsGoodComplex l E U P → integralOperationsGoodComplex l E X
      ((OpenSemilinearTensor.extensionComplex l E j o).obj P))
    (restrictGood : ∀ (P : CochainComplex (scalarReductionSource l E X) ℤ),
    integralOperationsGoodComplex l E X P → integralOperationsGoodComplex l E U
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj P))
    (ordinary : leftInputs l E j o ⋙ q.tensorX.ordinary.tensor ≅
    rightInputs l E j o ⋙ q.tensorU.ordinary.tensor ⋙ IntegralOpenReduction.shriek l E j o)
    : Prop :=
    ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ)
      (F : CochainComplex (scalarReductionSource l E X) ℤ)
      (hQ : integralOperationsGoodComplex l E U Q)
      (hF : integralOperationsGoodComplex l E X F),
    HEq (q.tensorX.ordinary.representative.hom.app
        (⟨(OpenSemilinearTensor.extensionComplex l E j o).obj Q,
          flat X _ (extendGood Q hQ)⟩, ⟨F, flat X F hF⟩) ≫
      q.tensorX.ordinary.tensor.map (Prod.mkHom
        ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.inv.app Q) (𝟙 _)) ≫
      ordinary.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj F) ≫
      (IntegralOpenReduction.shriek l E j o).map
        (q.tensorU.ordinary.tensor.map (Prod.mkHom (𝟙 _)
          ((IntegralOpenReduction.restriction l E j o).mapDerivedCategoryFactors.hom.app F))) ≫
      (IntegralOpenReduction.shriek l E j o).map
        (q.tensorU.ordinary.representative.inv.app
          (⟨Q, flat U Q hQ⟩, ⟨(OpenSemilinearTensor.restrictionComplex l E j o).obj F,
            flat U _ (restrictGood F hF)⟩)) ≫
      (IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.hom.app
        ((constructibleTensorTotal l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)))
      (DerivedCategory.Q.map (m.totalComparison.chain Q F).hom)

/-- The exact completed representative equation for every normalized strict square.
Source: Stacks 09BP and 0941; the original completion specification
(blueprint: def-sf-open-projection-roos-completion-data). -/
def CompletedRepresentative
    [restrictionLimits : PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o)]
    [restrictionColimits : PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o)]
    (extension : RoosComparison (IntegralOpenReduction.extension l E j o))
    (extendGood : ∀ (P : CochainComplex (scalarReductionSource l E U) ℤ),
    integralOperationsGoodComplex l E U P → integralOperationsGoodComplex l E X
      ((OpenSemilinearTensor.extensionComplex l E j o).obj P))
    (restrictGood : ∀ (P : CochainComplex (scalarReductionSource l E X) ℤ),
    integralOperationsGoodComplex l E X P → integralOperationsGoodComplex l E U
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj P))
    (gamma : completedLeft l E j o ≅ completedRight l E j o)
    : Prop :=
    ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ)
      (F : CochainComplex (scalarReductionSource l E X) ℤ)
      (hQ : integralOperationsGoodComplex l E U Q)
      (hF : integralOperationsGoodComplex l E X F)
      (hK : sfIntegralConstructible l E U (DerivedCategory.Q.obj Q))
      (hP : sfIntegralConstructible l E X (DerivedCategory.Q.obj F))
      (z : OpenTensorQuotient.StrictSquare l E j o m.totalComparison q.scalar st
        q.strictScalar Q F),
    OpenTensorQuotient.RoosNormalization l E X q.tensorX
      ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) F z.upper →
    OpenTensorQuotient.RoosNormalization l E U q.tensorU Q
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj F) z.lower →
    gamma.hom.app (⟨DerivedCategory.Q.obj Q, hK⟩, ⟨DerivedCategory.Q.obj F, hP⟩) ≫
      (IntegralOpenReduction.shriek l E j o).map
        ((integralCompletedTensor l E U).map (Prod.mkHom (𝟙 _)
          ((IntegralOpenReduction.restriction l E j o).mapDerivedCategoryFactors.hom.app F))) ≫
      (IntegralOpenReduction.shriek l E j o).map
        ((integralCompletedTensorComparison l E U).hom.app
          (⟨Q, hQ⟩, ⟨(OpenSemilinearTensor.restrictionComplex l E j o).obj F,
            restrictGood F hF⟩)) ≫
      (extension.derived (IntegralOpenReduction.extension l E j o)
        ((integralOperationsTensorTowerFunctor l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))).hom =
      (integralCompletedTensor l E X).map (Prod.mkHom
        ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.hom.app Q) (𝟙 _)) ≫
      (integralCompletedTensorComparison l E X).hom.app
        (⟨(OpenSemilinearTensor.extensionComplex l E j o).obj Q, extendGood Q hQ⟩, ⟨F, hF⟩) ≫
      DerivedCategory.Q.map (integralOperationsRoosMap z.gamma.hom)

/-- The strict finite restriction equation, with its prescribed termwise tower map.
Source: Stacks 09BP and 0941; the original completion specification
(blueprint: def-sf-open-projection-roos-completion-data). -/
def RestrictionRepresentative
    [restrictionLimits : PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o)]
    [restrictionColimits : PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o)]
    (restriction : RoosComparison (IntegralOpenReduction.restriction l E j o))
    (moduleUnit : 𝟭 (scalarReductionSource l E U) ≅
    IntegralOpenReduction.extension l E j o ⋙ IntegralOpenReduction.restriction l E j o)
    (extendGood : ∀ (P : CochainComplex (scalarReductionSource l E U) ℤ),
    integralOperationsGoodComplex l E U P → integralOperationsGoodComplex l E X
      ((OpenSemilinearTensor.extensionComplex l E j o).obj P))
    (restrictGood : ∀ (P : CochainComplex (scalarReductionSource l E X) ℤ),
    integralOperationsGoodComplex l E X P → integralOperationsGoodComplex l E U
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj P))
    (tensorRestriction : completedLeft l E j o ⋙ IntegralOpenReduction.star l E j o ≅
    completedInside l E j o)
    : Prop :=
    ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ)
      (F : CochainComplex (scalarReductionSource l E X) ℤ)
      (hQ : integralOperationsGoodComplex l E U Q)
      (hF : integralOperationsGoodComplex l E X F)
      (hK : sfIntegralConstructible l E U (DerivedCategory.Q.obj Q))
      (hP : sfIntegralConstructible l E X (DerivedCategory.Q.obj F))
      (z : OpenTensorQuotient.StrictSquare l E j o m.totalComparison q.scalar st
        q.strictScalar Q F),
    OpenTensorQuotient.RoosNormalization l E X q.tensorX
      ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) F z.upper →
    OpenTensorQuotient.RoosNormalization l E U q.tensorU Q
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj F) z.lower →
    ∃ delta : (onTowers (IntegralOpenReduction.restriction l E j o)).obj
        ((integralOperationsTensorTowerFunctor l E X).obj
          ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F)) ≅
      (integralOperationsTensorTowerFunctor l E U).obj
        (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F),
    (∀ (n : ℕ) (i : ℤ),
      ((delta.hom.app (op n)).f i) =
        (IntegralOpenReduction.restriction l E j o).map ((z.gamma.hom.app (op n)).f i) ≫
          moduleUnit.inv.app
            ((((integralOperationsTensorTowerFunctor l E U).obj
              (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)).obj (op n)).X i)) ∧
    tensorRestriction.hom.app
        (⟨DerivedCategory.Q.obj Q, hK⟩, ⟨DerivedCategory.Q.obj F, hP⟩) ≫
      (integralCompletedTensor l E U).map (Prod.mkHom (𝟙 _)
        ((IntegralOpenReduction.restriction l E j o).mapDerivedCategoryFactors.hom.app F)) ≫
      (integralCompletedTensorComparison l E U).hom.app
        (⟨Q, hQ⟩, ⟨(OpenSemilinearTensor.restrictionComplex l E j o).obj F,
          restrictGood F hF⟩) =
      (IntegralOpenReduction.star l E j o).map
        ((integralCompletedTensor l E X).map (Prod.mkHom
          ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.hom.app Q)
          (𝟙 _)) ≫
          (integralCompletedTensorComparison l E X).hom.app
            (⟨(OpenSemilinearTensor.extensionComplex l E j o).obj Q, extendGood Q hQ⟩,
              ⟨F, hF⟩)) ≫
      (restriction.derived (IntegralOpenReduction.restriction l E j o)
        ((integralOperationsTensorTowerFunctor l E X).obj
          ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F))).hom ≫
      DerivedCategory.Q.map (integralOperationsRoosMap delta.hom)

-- The predicate retains simultaneous natural transformations and all representative equations.
/-- The completion of the specified augmented square. Every isomorphism is pinned
by chain or unit equations, including restriction and every strict finite reduction.
`ordinary` is gamma^B, `gamma` is Gamma, `extension` is lambda_j.
Source: Stacks 09BP; Bhatt--Scholze 6.5.5, 6.5.8
(blueprint: lem-sf-open-projection-roos-completion). -/
def CompletionData
    [restrictionLimits : PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o)]
    [restrictionColimits : PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o)] :
    Prop :=
    ∃ (extension : RoosComparison (IntegralOpenReduction.extension l E j o)),
    ∃ (restriction : RoosComparison (IntegralOpenReduction.restriction l E j o)),
    ∃ (moduleUnit : 𝟭 (scalarReductionSource l E U) ≅
    IntegralOpenReduction.extension l E j o ⋙ IntegralOpenReduction.restriction l E j o),
    ∃ (_moduleUnit_hom : moduleUnit.hom = (IntegralOpenReduction.ordinaryAdjunction l E j o).unit),
    ∃ (unit : 𝟭 (DerivedCategory (scalarReductionSource l E U)) ≅
    IntegralOpenReduction.shriek l E j o ⋙ IntegralOpenReduction.star l E j o),
    ∃ (_unit_hom : unit.hom = (IntegralOpenReduction.openAdjunction l E j o).unit),
    ∃ (flat : ∀ (W : Scheme.{u}) (P : CochainComplex (scalarReductionSource l E W) ℤ),
    integralOperationsGoodComplex l E W P →
      proEtaleFlatRepresentatives W (completedIntegralCommRingSheafUnrestricted l E W) P),
    ∃ (extendGood : ∀ (P : CochainComplex (scalarReductionSource l E U) ℤ),
    integralOperationsGoodComplex l E U P → integralOperationsGoodComplex l E X
      ((OpenSemilinearTensor.extensionComplex l E j o).obj P)),
    ∃ (restrictGood : ∀ (P : CochainComplex (scalarReductionSource l E X) ℤ),
    integralOperationsGoodComplex l E X P → integralOperationsGoodComplex l E U
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj P)),
    ∃ (ordinary : leftInputs l E j o ⋙ q.tensorX.ordinary.tensor ≅
    rightInputs l E j o ⋙ q.tensorU.ordinary.tensor ⋙ IntegralOpenReduction.shriek l E j o),
    ∃ (_ordinary_representative : OrdinaryRepresentative l E j o SX SU AX AU st m c q
      flat extendGood restrictGood ordinary),
    ∃ (gamma : completedLeft l E j o ≅ completedRight l E j o),
    ∃ (_units : ∀ K : sfIntegralConstructibleCategory l E U × sfIntegralConstructibleCategory l E X,
    (q.tensorX.chi l E).app ((leftInputs l E j o).obj (K.1.obj, K.2.obj)) ≫
        gamma.hom.app K =
      ordinary.hom.app (K.1.obj, K.2.obj) ≫
        (IntegralOpenReduction.shriek l E j o).map
          ((q.tensorU.chi l E).app ((rightInputs l E j o).obj (K.1.obj, K.2.obj)))),
    ∃ (_invertibleUnits : ∀ K :
      sfIntegralConstructibleCategory l E U × sfIntegralConstructibleCategory l E X,
    IsIso ((q.tensorX.chi l E).app ((leftInputs l E j o).obj (K.1.obj, K.2.obj))) ∧
      IsIso ((q.tensorU.chi l E).app ((rightInputs l E j o).obj (K.1.obj, K.2.obj)))),
    ∃ (_representative : CompletedRepresentative l E j o SX SU AX AU st m c q
      extension extendGood restrictGood gamma),
    ∃ (tensorRestriction : completedLeft l E j o ⋙ IntegralOpenReduction.star l E j o ≅
    completedInside l E j o),
    ∃ (_restriction_identity : ∀ K :
      sfIntegralConstructibleCategory l E U × sfIntegralConstructibleCategory l E X,
    (IntegralOpenReduction.star l E j o).map (gamma.hom.app K) ≫
        unit.inv.app ((completedInside l E j o).obj K) = tensorRestriction.hom.app K),
    RestrictionRepresentative l E j o SX SU AX AU st m c q
      restriction moduleUnit extendGood restrictGood
      tensorRestriction

/-- Exactness together with the specified comparison predicate. The exactness
witnesses are supplied by the conclusion, not imposed as additional hypotheses.
Source: Stacks 09BP (blueprint: lem-sf-open-projection-roos-completion). -/
def Completion : Prop :=
  ∃ (hL : PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o))
    (hC : PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o)),
  CompletionData l E j o SX SU AX AU st m c q
    (restrictionLimits := hL) (restrictionColimits := hC)

attribute [local irreducible] CompletionData Completion

end WeilConjectures.OpenProjectionRoos

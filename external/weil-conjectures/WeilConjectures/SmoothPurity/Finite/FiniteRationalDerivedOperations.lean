/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
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
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
import WeilConjectures.SmoothPurity.Integral.IntegralDerivedPullbackLinear
import WeilConjectures.CategoryTheory.ScalarLocalization.BilinearScalarLocalization

import WeilConjectures.SmoothPurity.Integral.IntegralCompletedTensorBilinear
import WeilConjectures.SmoothPurity.Integral.IntegralDerivedHomBilinear
import WeilConjectures.SmoothPurity.OperationsScalarLocalization.DerivedScalarLocalizationFunctor
import WeilConjectures.SmoothPurity.OperationsScalarLocalization.DerivedScalarLocalizationIso
import WeilConjectures.SmoothPurity.OperationsScalarLocalization.DerivedScalarLocalizationBilinearComparison
import WeilConjectures.SmoothPurity.OperationsScalarLocalization.DerivedScalarLocalizationRestrictedHom

/-! # Finite, integral, and rational derived operations

Source: blueprint sec-smooth-purity/sk-def-sf-operations, order 1467;
Stacks Project, Tags 06YL, 06YV, 08J7 and 099N
(blueprint: def-sf-finite-rational-derived-operations).

This is the finite, integral, and rational part of
`prose-03-02`, extracted with its declaration names,
signatures, and definitions preserved. The common-stage module re-exports it.

## Main definitions

- `finiteDerivedPullback`: exact intrinsic constant-coefficient inverse image.
- `finiteIntrinsicDerivedTensor`, `finiteIntrinsicDerivedInternalHom`: ambient operations.
- `finiteIntrinsicTensorModels`: K-flat tensor and ordinary evaluation normalization.
- `finiteIntrinsicReductionHom`: reduced evaluation's canonical closed transpose.
- `constructibleIntegralPullback`, `constructibleIntegralTensor`: actual restrictions.
- `constructibleIntegralHom`: ambient Hom restricted to permitted constructible pairs.
- `rationalDerivedPullback`, `rationalDerivedTensor`, `rationalDerivedInternalHom`:
  the uniquely specified linear and bilinear extensions with unchanged integral objects.

The scalar comparisons rationalize the prescribed integral comparisons.
No idempotent completion, arbitrary isomorphism, or extra coefficient flatness is used.
-/

-- The module has public declarations; avoid the costly final private-only style scan.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
-- The generated common-stage types make the section-variable linter expensive.
-- Every retained section parameter is present in the operation's public type.
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v r s u₁ v₁ u₂ v₂

open Opposite TensorProduct

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

-- Keep the chosen derived localization model abstract during elaboration.
attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear

private theorem conjugation_naturality {C : Type u₁} [Category.{v₁} C]
    {A B A' B' D E D' E' : C}
    (c : A ≅ A') (c' : B ≅ B') (d : D ≅ D') (d' : E ≅ E')
    (p : A ⟶ B) (p' : A' ⟶ B') (q : D ⟶ E) (q' : D' ⟶ E')
    (e : A ≅ D) (e' : B ≅ E)
    (hc : p ≫ c'.hom = c.hom ≫ p')
    (hd : q ≫ d'.hom = d.hom ≫ q')
    (he : p ≫ e'.hom = e.hom ≫ q) :
    p' ≫ (c'.inv ≫ e'.hom ≫ d'.hom) =
      (c.inv ≫ e.hom ≫ d.hom) ≫ q' := by
  apply (cancel_epi c.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← hc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, he, Category.assoc, hd]

private theorem map_heq {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hx
  cases hy
  cases h
  rfl

private theorem map_naturality_iso_components
    {B : Type*} [Category* B] {C : Type*} [Category* C]
    {D : Type*} [Category* D] (F : C ⥤ D) {G H : B ⥤ C} (η : G ⟶ H)
    {K M : B} (a : K ⟶ M) (eK : G.obj K ≅ H.obj K) (eM : G.obj M ≅ H.obj M)
    (hK : eK.hom = η.app K) (hM : eM.hom = η.app M) :
    F.map (G.map a) ≫ (F.mapIso eM).hom =
      (F.mapIso eK).hom ≫ F.map (H.map a) := by
  simp only [Functor.mapIso_hom, hK, hM, ← Functor.map_comp, η.naturality]

attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionAbsoluteValue

attribute [local irreducible] integralDerivedPullback integralCompletedTensor
  integralDerivedInternalHom sfRationalScalarExtension
  completedIntegralCoefficientSheafUnrestricted integralScalarExtension integralOrdinaryScalar

/-- The recorded quotient coefficient ring; every operation below uses exponent n+1.
Source: blueprint `prose-03-02`
(blueprint: prose-03-02).
-/
noncomputable abbrev finiteCoefficientRing (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) := Padic.coefficientExtensionRing l E n

/-- Finite-level derived pullback on the intrinsic constant-ring category.
Source: blueprint `prose-03-02`; uses the exact
pro-etale inverse image of `prose-03-02`.
(blueprint: prose-03-02).
-/
noncomputable abbrev finiteDerivedPullback {X Y : Scheme.{u}}
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (f : X ⟶ Y) :
    proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1)) ⥤
      proEtaleDerivedCategory X (finiteCoefficientRing l E (n + 1)) :=
  letI : Finite (finiteCoefficientRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))
  sfIntrinsicDerivedPullback (finiteCoefficientRing l E (n + 1)) f

/-- Intrinsic finite closed structure for the recorded K-injective internal Hom.
The closed universal property and its K-flat evaluation normalization determine
this structure up to the unique compatible isomorphism used downstream.
Source: Stacks 07A4, 08J9; coefficient evaluation calculus
(blueprint: prose-03-02). -/
noncomputable def finiteIntrinsicClosed (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (n : ℕ) :
    CoefficientClosedStructure (coefficientFiniteInternalHom l E W n) :=
  (coefficientDerivedSystemEvaluationCalculus l E W).choose.finiteClosed n

/-- Tensor on the actual intrinsic positive-level coefficient category.
Source: Stacks 07A4 (blueprint: prose-03-02). -/
noncomputable def finiteIntrinsicDerivedTensor (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (n : ℕ) :
    proEtaleDerivedCategory W (finiteCoefficientRing l E (n + 1)) ×
      proEtaleDerivedCategory W (finiteCoefficientRing l E (n + 1)) ⥤
        proEtaleDerivedCategory W (finiteCoefficientRing l E (n + 1)) :=
  (finiteIntrinsicClosed l E W n).tensor

/-- The recorded intrinsic ambient Hom, with its first input contravariant.
Source: Stacks 08J7 (blueprint: prose-03-02). -/
noncomputable abbrev finiteIntrinsicDerivedInternalHom (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (n : ℕ) := coefficientFiniteInternalHom l E W n

/-- The actual K-flat representative comparison, including the ordinary evaluation
formula on pure tensors. The site object and morphism universes remain u+1 and u.
Source: Stacks 07A4, 08J9 (blueprint: prose-03-02). -/
noncomputable def finiteIntrinsicTensorModels (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (n : ℕ) :
    CoefficientTensorModels.{u, u+1, u} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n) (finiteIntrinsicClosed l E W n) :=
  (coefficientDerivedSystemEvaluationCalculus l E W).choose.finiteTensorModel n

/-- Intrinsic finite evaluation: the counit for the recorded internal Hom.
Source: Stacks 08J9 (blueprint: prose-03-02). -/
noncomputable abbrev finiteIntrinsicEvaluation (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (n : ℕ) := (finiteIntrinsicClosed l E W n).evaluation

/-- Intrinsic finite currying: the canonical closed Hom equivalence, whose
representative normalization is finiteIntrinsicTensorModels.uncurry_model.
Source: Stacks 08J9 (blueprint: prose-03-02). -/
noncomputable abbrev finiteIntrinsicTranspose (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (n : ℕ) := (finiteIntrinsicClosed l E W n).transpose

/-- The canonical quotient change-of-rings Hom comparison at n+1 ≤ m+1.
Its definition is the unique closed transpose of reduced evaluation, conjugated
by the comparison fixed on K-flat tensor generators. This supplies the requested
consumer on the existing intrinsic Hom with no flatness assumption on the quotient.
Source: Stacks 06YS, 0A95; coefficient calculus steps 10--11
(blueprint: prose-03-02). -/
noncomputable abbrev finiteIntrinsicReductionHom (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :=
  coefficientFiniteQuotientHomComparison l E W
    (coefficientDerivedSystemEvaluationCalculus l E W).choose.toCoefficientDerivedSystemTensors
    (coefficientDerivedSystemEvaluationCalculus l E W).choose.quotientCalculus h

/-- Restriction of the canonical integral pullback to the recorded constructible
subcategory. Its underlying object and arrow maps are the ambient ones.
Source: blueprint integral paragraph; Stacks Tag 099N(5)
(blueprint: prose-03-02). -/
noncomputable def constructibleIntegralPullback (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X :=
  (sfIntegralConstructible l E X).lift
    ((sfIntegralConstructible l E Y).ι ⋙ integralDerivedPullback l E f)
    (fun K ↦ ((integralOperations_preserve_constructible l E f).1 K.obj K.property).1)

/-- Constructible restriction of the completed integral tensor, for either scheme.
Source: blueprint integral paragraph; Bhatt--Scholze, Lemma 6.5.5
(blueprint: prose-03-02). -/
noncomputable def constructibleIntegralTensor (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :
    sfIntegralConstructibleCategory l E W × sfIntegralConstructibleCategory l E W ⥤
      sfIntegralConstructibleCategory l E W :=
  (sfIntegralConstructible l E W).lift
    (((sfIntegralConstructible l E W).ι.prod (sfIntegralConstructible l E W).ι) ⋙
      integralCompletedTensor l E W)
    (fun MN ↦ ((integralOperations_preserve_constructible l E (𝟙 W)).2 W
      (Or.inl rfl) MN.1.obj MN.2.obj MN.1.property MN.2.property).1)

/-- The full subcategory of integral pairs for which the ambient derived internal
Hom is constructible. No closure assertion for all pairs is made.
Source: blueprint integral internal-Hom qualification; Stacks Tag 08J7
(blueprint: prose-03-02). -/
noncomputable def constructibleIntegralHomPairs (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) :
    ObjectProperty ((sfIntegralConstructibleCategory l E W)ᵒᵖ ×
      sfIntegralConstructibleCategory l E W) :=
  fun MN ↦ sfIntegralConstructible l E W
    ((integralDerivedInternalHom l E W).obj (op MN.1.unop.obj, MN.2.obj))

/-- Restrict ambient internal Hom exactly on the permitted pairs.
Source: blueprint integral paragraph; Stacks Tag 08J7
(blueprint: prose-03-02). -/
noncomputable def constructibleIntegralHom (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) :
    (constructibleIntegralHomPairs l E W).FullSubcategory ⥤
      sfIntegralConstructibleCategory l E W :=
  (sfIntegralConstructible l E W).lift
    ((constructibleIntegralHomPairs l E W).ι ⋙
      ((sfIntegralConstructible l E W).ι.op.prod (sfIntegralConstructible l E W).ι) ⋙
      integralDerivedInternalHom l E W)
    (fun MN ↦ MN.property)

/-- Rational Hom has exactly the same integral-pair restriction on its objects.
Source: blueprint rational paragraph
(blueprint: prose-03-02). -/
noncomputable def constructibleRationalHomPairs (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) :
    ObjectProperty ((sfRationalConstructibleCategory l E W)ᵒᵖ ×
      sfRationalConstructibleCategory l E W) :=
  fun MN ↦ constructibleIntegralHomPairs l E W (op MN.1.unop.obj, MN.2.obj)

/-- The rational pullback is uniquely prescribed on unchanged objects and every
pure tensor in the raw localized Hom groups. Additivity extends the displayed
formula to sums. Scalar-first coordinates are those of the recorded localization.
Source: blueprint rational paragraph
(blueprint: prose-03-02).
Proof: integral pullback is linear for the constant O_E action, since the strict
finite inverse images and their Roos construction commute with that action.
Base change its linear Hom maps. The tensor balancing relation gives well-defined
maps. On pure tensors the identity and composition equations follow from the
integral functor laws and multiplication of coefficients. Additivity gives them
on all morphisms. Objects and pure tensors determine the functor uniquely. -/
theorem rationalDerivedPullback_existsUnique (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃! F : sfRationalConstructibleCategory l E Y ⥤
        sfRationalConstructibleCategory l E X,
      F.Additive ∧
      (∀ K, F.obj K = ⟨(constructibleIntegralPullback l E f).obj K.obj⟩) ∧
      (∀ (K L : sfIntegralConstructibleCategory l E Y) (a : K ⟶ L)
        (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
        HEq (F.map (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] a :
          (sfRationalConstructibleLocalization l E Y).obj K ⟶
            (sfRationalConstructibleLocalization l E Y).obj L))
          (c ⊗ₜ[Padic.coefficientExtensionIntegers l E]
            (constructibleIntegralPullback l E f).map a)) := by
  let R := Padic.coefficientExtensionIntegers l E
  let t := Padic.coefficientExtensionUniformizer l E
  let U := constructibleIntegralPullback l E f
  have hU := integralDerivedPullback_linear l E f
  have : U.Additive := ⟨fun {K M a b} ↦ by
    apply ObjectProperty.hom_ext
    exact hU.1.map_add⟩
  have hlin : U.Linear R := ⟨fun {K M} a c ↦ by
    apply ObjectProperty.hom_ext
    exact hU.2.map_smul a.hom c⟩
  exact OperationsScalarLocalization.functor_existsUnique t U

/-- The unique rational pullback with the prescribed integral object and tensor
Hom action. Source: blueprint rational paragraph
(blueprint: prose-03-02). -/
noncomputable def rationalDerivedPullback (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :=
  (rationalDerivedPullback_existsUnique l E f).exists.choose

attribute [local irreducible] rationalDerivedPullback

private theorem constructibleIntegralTensor_bilinear (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :
    ∃ β : ∀ M M' N N' : sfIntegralConstructibleCategory l E W,
        (M ⟶ M') →ₗ[Padic.coefficientExtensionIntegers l E]
          (N ⟶ N') →ₗ[Padic.coefficientExtensionIntegers l E]
            ((constructibleIntegralTensor l E W).obj (M, N) ⟶
              (constructibleIntegralTensor l E W).obj (M', N')),
      ∀ (M M' N N' : sfIntegralConstructibleCategory l E W) (a : M ⟶ M') (b : N ⟶ N'),
        β M M' N N' a b = (constructibleIntegralTensor l E W).map (Prod.mkHom a b) := by
  let R := Padic.coefficientExtensionIntegers l E
  let B := constructibleIntegralTensor l E W
  have hH (M M' N N' : sfIntegralConstructibleCategory l E W) :=
    integralCompletedTensor_bilinear l E W M.obj M'.obj N.obj N'.obj
  let β (M M' N N' : sfIntegralConstructibleCategory l E W) := (hH M M' N N').choose
  let γ (M M' N N' : sfIntegralConstructibleCategory l E W) :
      (M ⟶ M') →ₗ[R] (N ⟶ N') →ₗ[R] (B.obj (M, N) ⟶ B.obj (M', N')) :=
    ((β M M' N N').compl₁₂
      ((sfIntegralConstructible l E W).ι.mapLinearMap R)
      ((sfIntegralConstructible l E W).ι.mapLinearMap R)).compr₂
        (InducedCategory.homLinearEquiv (R := R)
          (F := fun X : sfIntegralConstructibleCategory l E W ↦ X.obj)
          (X := B.obj (M, N)) (Y := B.obj (M', N'))).symm.toLinearMap
  refine ⟨γ, ?_⟩
  intro M M' N N' a b
  apply ObjectProperty.hom_ext
  exact (hH M M' N N').choose_spec a.hom b.hom

section RationalTensorConstruction
attribute [local irreducible] constructibleIntegralTensor sfIntegralConstructibleLinear
  ObjectProperty.FullSubcategory.category Preadditive.fullSubcategory Linear.fullSubcategory

/-- Rational tensor is the unique additive-in-each-variable extension with
coefficient multiplication c*d on pure tensors; no Karoubi envelope occurs.
Source: blueprint rational paragraph
(blueprint: prose-03-02).
Proof: integral tensor is O_E-linear in each variable by its strict finite tensor
formulas, preserved by Roos descent. Extend the bilinear Hom map in both scalar
factors. Balancing is precisely integral bilinearity. Integral functoriality and
commutativity of coefficients prove identities and composition on pure tensors,
then bilinearity proves them on all arrows. These generators prove uniqueness. -/
theorem rationalDerivedTensor_existsUnique (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :
    ∃! F : sfRationalConstructibleCategory l E W ×
        sfRationalConstructibleCategory l E W ⥤ sfRationalConstructibleCategory l E W,
      (∀ MN, F.obj MN = ⟨(constructibleIntegralTensor l E W).obj
        (MN.1.obj, MN.2.obj)⟩) ∧
      (∀ (M M' N N' : sfRationalConstructibleCategory l E W),
        ∃ b : (M ⟶ M') →ₗ[Localization.Away (Padic.coefficientExtensionUniformizer l E)]
          (N ⟶ N') →ₗ[Localization.Away (Padic.coefficientExtensionUniformizer l E)]
          (F.obj (M, N) ⟶ F.obj (M', N')),
        (∀ a b', F.map (Prod.mkHom a b') = b a b') ∧
        ∀ (a : M.obj ⟶ M'.obj) (b' : N.obj ⟶ N'.obj)
          (c d : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
          HEq (b (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] a)
            (d ⊗ₜ[Padic.coefficientExtensionIntegers l E] b'))
            ((c * d) ⊗ₜ[Padic.coefficientExtensionIntegers l E]
              (constructibleIntegralTensor l E W).map (Prod.mkHom a b'))) := by
  obtain ⟨β, hβ⟩ := constructibleIntegralTensor_bilinear l E W
  exact @ScalarLocalization.bilinearFunctor_existsUnique (sfIntegralConstructibleCategory l E W)
    (ObjectProperty.FullSubcategory.category (sfIntegralConstructible l E W))
    (Preadditive.fullSubcategory (sfIntegralConstructible l E W))
    (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionIntegers l E).toCommRing
    (sfIntegralConstructibleLinear l E W) (Padic.coefficientExtensionUniformizer l E)
    (constructibleIntegralTensor l E W) β hβ

end RationalTensorConstruction

/-- Rational tensor with unchanged integral objects and bilinear scalar extension
on morphisms. Source: blueprint rational paragraph
(blueprint: prose-03-02). -/
noncomputable def rationalDerivedTensor (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :=
  (rationalDerivedTensor_existsUnique l E W).exists.choose

private theorem chosenUnique_spec {A : Sort*} {p : A → Prop} (h : ∃! a, p a)
    (a : A) (ha : a = h.exists.choose) : p a :=
  ha.symm ▸ h.exists.choose_spec

private abbrev rationalTensor_spec (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :=
  chosenUnique_spec (rationalDerivedTensor_existsUnique l E W)
    (rationalDerivedTensor l E W) rfl

attribute [local irreducible] rationalDerivedTensor

/-- The underlying permitted integral pair of a permitted rational pair.
Source: blueprint rational internal-Hom paragraph
(blueprint: prose-03-02). -/
noncomputable def integralPairOfRationalHomPair (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (P : (constructibleRationalHomPairs l E W).FullSubcategory) :
    (constructibleIntegralHomPairs l E W).FullSubcategory :=
  ⟨(op P.obj.1.unop.obj, P.obj.2.obj), P.property⟩

/-- Restrict the ambient bilinear arrow action to permitted constructible endpoints. -/
private theorem constructibleIntegralHom_bilinear (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) :
    ∃ β : ∀ P Q : (constructibleIntegralHomPairs l E W).FullSubcategory,
        (Q.obj.1.unop ⟶ P.obj.1.unop) →ₗ[Padic.coefficientExtensionIntegers l E]
          (P.obj.2 ⟶ Q.obj.2) →ₗ[Padic.coefficientExtensionIntegers l E]
            ((constructibleIntegralHom l E W).obj P ⟶
              (constructibleIntegralHom l E W).obj Q),
      ∀ (P Q : (constructibleIntegralHomPairs l E W).FullSubcategory)
        (a : Q.obj.1.unop ⟶ P.obj.1.unop) (b : P.obj.2 ⟶ Q.obj.2),
        β P Q a b = (constructibleIntegralHom l E W).map
          (ObjectProperty.homMk (Prod.mkHom a.op b)) := by
  let R := Padic.coefficientExtensionIntegers l E
  let q := constructibleIntegralHomPairs l E W
  let B := constructibleIntegralHom l E W
  have hH (P Q : q.FullSubcategory) :=
    integralDerivedHom_bilinear l E W P.obj.1.unop.obj Q.obj.1.unop.obj
      P.obj.2.obj Q.obj.2.obj
  let β (P Q : q.FullSubcategory) := (hH P Q).choose
  have hβ (P Q : q.FullSubcategory) := (hH P Q).choose_spec
  let γ (P Q : q.FullSubcategory) :
      (Q.obj.1.unop ⟶ P.obj.1.unop) →ₗ[R] (P.obj.2 ⟶ Q.obj.2) →ₗ[R]
        (B.obj P ⟶ B.obj Q) :=
    ((β P Q).compl₁₂
      ((sfIntegralConstructible l E W).ι.mapLinearMap R)
      ((sfIntegralConstructible l E W).ι.mapLinearMap R)).compr₂
        (InducedCategory.homLinearEquiv (R := R)
          (F := fun X : sfIntegralConstructibleCategory l E W ↦ X.obj)
          (X := B.obj P) (Y := B.obj Q)).symm.toLinearMap
  have hγ (P Q : q.FullSubcategory)
      (a : Q.obj.1.unop ⟶ P.obj.1.unop) (b : P.obj.2 ⟶ Q.obj.2) :
      γ P Q a b = B.map (ObjectProperty.homMk (Prod.mkHom a.op b)) := by
    apply ObjectProperty.hom_ext
    exact hβ P Q a.hom b.hom
  exact ⟨γ, hγ⟩

section RationalHomConstruction
attribute [local irreducible] constructibleIntegralHom sfIntegralConstructibleLinear
  ObjectProperty.FullSubcategory.category Preadditive.fullSubcategory Linear.fullSubcategory

/-- The unique rational internal Hom on the permitted full subcategory of pairs.
The multiplication c*d applies to the contravariant first map and covariant
second map, in exactly the source and target order of the blueprint.
Source: blueprint rational paragraph; Stacks Tag 08J7
(blueprint: prose-03-02).
Proof: the ambient integral Hom functor is O_E-linear separately in both
variables, with precomposition in the first variable and postcomposition in the
second. Restrict its maps to the permitted endpoints, then extend bilinearly
along O_E to E using the tensor universal property. Balancing gives the formula
on pure tensors. Identities and composition follow on pure tensors from the
integral functor laws; extend to sums by bilinearity. Objects and these formulas
uniquely determine the functor. The domain restriction concerns objects only,
so every pair of arrows between permitted endpoints is included. -/
theorem rationalDerivedInternalHom_existsUnique (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) :
    ∃! F : (constructibleRationalHomPairs l E W).FullSubcategory ⥤
        sfRationalConstructibleCategory l E W,
      (∀ P, F.obj P = ⟨(constructibleIntegralHom l E W).obj
        (integralPairOfRationalHomPair l E W P)⟩) ∧
      (∀ (P Q : (constructibleRationalHomPairs l E W).FullSubcategory),
        ∃ b : (Q.obj.1.unop ⟶ P.obj.1.unop)
          →ₗ[Localization.Away (Padic.coefficientExtensionUniformizer l E)]
          (P.obj.2 ⟶ Q.obj.2)
          →ₗ[Localization.Away (Padic.coefficientExtensionUniformizer l E)]
          (F.obj P ⟶ F.obj Q),
        (∀ a b', F.map (ObjectProperty.homMk (Prod.mkHom a.op b')) = b a b') ∧
        ∀ (a : Q.obj.1.unop.obj ⟶ P.obj.1.unop.obj)
          (b' : P.obj.2.obj ⟶ Q.obj.2.obj)
          (c d : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
          HEq (b (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] a)
            (d ⊗ₜ[Padic.coefficientExtensionIntegers l E] b'))
            ((c * d) ⊗ₜ[Padic.coefficientExtensionIntegers l E]
              (constructibleIntegralHom l E W).map
                (X := integralPairOfRationalHomPair l E W P)
                (Y := integralPairOfRationalHomPair l E W Q)
                (ObjectProperty.homMk (Prod.mkHom a.op b')))) := by
  obtain ⟨β, hβ⟩ := constructibleIntegralHom_bilinear l E W
  exact @OperationsScalarLocalization.restrictedHom_existsUnique
    (sfIntegralConstructibleCategory l E W)
    (ObjectProperty.FullSubcategory.category (sfIntegralConstructible l E W))
    (Preadditive.fullSubcategory (sfIntegralConstructible l E W))
    (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionIntegers l E).toCommRing
    (sfIntegralConstructibleLinear l E W) (Padic.coefficientExtensionUniformizer l E)
    (constructibleIntegralHomPairs l E W) (constructibleIntegralHom l E W)
    (constructibleRationalHomPairs l E W) (fun _ h ↦ h) β hβ

end RationalHomConstruction

/-- Rational internal Hom, with its contravariant/covariant pure-tensor action.
Source: blueprint rational paragraph
(blueprint: prose-03-02). -/
noncomputable def rationalDerivedInternalHom (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) :=
  (rationalDerivedInternalHom_existsUnique l E W).exists.choose

section ScalarComparisons
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] rationalDerivedInternalHom

/-- The restricted integral pullback comparison, with its canonical ambient component.
Source: blueprint common-stage paragraph
(blueprint: prose-03-02). -/
def integralPullbackScalarComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y) :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      E L ι X).obj ((constructibleIntegralPullback l E f).obj K) ≅
      (constructibleIntegralPullback l L f).obj
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj K) :=
  ObjectProperty.isoMk _ (scalarPullbackCompleted l E L ι f K.obj K.property.1
    ((constructibleIntegralPullback l E f).obj K).property.1)

/-- The restricted integral tensor comparison, with both input comparisons covariant.
Source: blueprint common-stage paragraph
(blueprint: prose-03-02). -/
def integralTensorScalarComparison (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W) :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      E L ι W).obj ((constructibleIntegralTensor l E W).obj (M, N)) ≅
      (constructibleIntegralTensor l L W).obj
        (((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M),
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj N)) :=
  ObjectProperty.isoMk _ (scalarTensorCompleted l E L ι W M.obj N.obj
    M.property.1 N.property.1 ((constructibleIntegralTensor l E W).obj (M, N)).property.1)

section RationalScalarComparisons
attribute [local irreducible] Linear.homModule Preadditive.homGroup
  ScalarLocalization.linear ScalarLocalization.preadditive sfIntegralConstructibleLinear

/-- Rational pullback comparison: precisely the rationalized normalized integral map.
Source: blueprint common-stage paragraph
(blueprint: prose-03-02).
Proof: apply localization to integralPullbackScalarComparison. The scalar and
pullback object formulas identify the endpoints. Naturality holds on integral
maps by the normalized chain construction, then on pure tensors by linearity,
and hence on every morphism by addition. The inverse localizes too. The displayed
component formula determines the natural isomorphism uniquely. -/
theorem rationalPullbackScalarComparison_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃! α : rationalDerivedPullback l E f ⋙
        sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ≅
      sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙
        rationalDerivedPullback l L f,
      ∀ K : sfRationalConstructibleCategory l E Y,
        HEq (α.hom.app K) ((sfRationalConstructibleLocalization l L X).map
          (integralPullbackScalarComparison l E L ι f K.obj).hom) := by
  let S (W : Scheme.{u}) := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  let U := constructibleIntegralPullback l E f ⋙ S X
  let V := S Y ⋙ constructibleIntegralPullback l L f
  let e : U ≅ V := NatIso.ofComponents (integralPullbackScalarComparison l E L ι f)
    (by
      intro K M a
      apply ObjectProperty.hom_ext
      change (integralScalarExtension l E L ι X).map
          ((integralDerivedPullback l E f).map a.hom) ≫
            (scalarPullbackCompleted l E L ι f M.obj M.property.1
              ((constructibleIntegralPullback l E f).obj M).property.1).hom =
        (scalarPullbackCompleted l E L ι f K.obj K.property.1
          ((constructibleIntegralPullback l E f).obj K).property.1).hom ≫
          (integralDerivedPullback l L f).map
            ((integralScalarExtension l E L ι Y).map a.hom)
      dsimp only [scalarPullbackCompleted, Iso.trans_hom, Functor.mapIso_hom]
      have hnX := (scalarCompletion l E L ι X).naturality
        ((integralDerivedPullback l E f).map a.hom)
      have hnO := (scalarPullbackOrdinary l E L ι f).hom.naturality a.hom
      dsimp only [Functor.comp_map] at hnO
      exact conjugation_naturality
        (scalarCompletionIso l E L ι X _
          ((constructibleIntegralPullback l E f).obj K).property.1)
        (scalarCompletionIso l E L ι X _
          ((constructibleIntegralPullback l E f).obj M).property.1)
        ((integralDerivedPullback l L f).mapIso
          (scalarCompletionIso l E L ι Y K.obj K.property.1))
        ((integralDerivedPullback l L f).mapIso
          (scalarCompletionIso l E L ι Y M.obj M.property.1))
        _ _ _ _
        ((scalarPullbackOrdinary l E L ι f).app K.obj)
        ((scalarPullbackOrdinary l E L ι f).app M.obj)
        hnX
        (map_naturality_iso_components (integralDerivedPullback l L f)
          (scalarCompletion l E L ι Y) a.hom
          (scalarCompletionIso l E L ι Y K.obj K.property.1)
          (scalarCompletionIso l E L ι Y M.obj M.property.1) rfl rfl)
        hnO)
  let A := rationalDerivedPullback l E f
  let B := rationalDerivedPullback l L f
  let TX := sfRationalScalarExtension l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  let TY := sfRationalScalarExtension l E Y 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  let c (z : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :=
    (sfRationalCoefficientEquiv l L).symm (ι (sfRationalCoefficientEquiv l E z))
  have hA : ∀ K, A.obj K = ⟨(constructibleIntegralPullback l E f).obj K.obj⟩ := by
    simpa only [A, rationalDerivedPullback] using
      (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1
  have hB : ∀ K, B.obj K = ⟨(constructibleIntegralPullback l L f).obj K.obj⟩ := by
    simpa only [B, rationalDerivedPullback] using
      (rationalDerivedPullback_existsUnique l L f).exists.choose_spec.2.1
  have hS (W : Scheme.{u}) : ∀ K : sfRationalConstructibleCategory l E W,
      (sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K = ⟨(S W).obj K.obj⟩ := by
    simpa only [sfRationalScalarExtension, S] using
      (sfRationalScalarExtension_existsUnique l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1
  have mA (K M : sfIntegralConstructibleCategory l E Y) (a : K ⟶ M)
      (z : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
      HEq (A.map (z ⊗ₜ[Padic.coefficientExtensionIntegers l E] a))
        (z ⊗ₜ[Padic.coefficientExtensionIntegers l E]
          (constructibleIntegralPullback l E f).map a) := by
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    simpa only [A, rationalDerivedPullback, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.2 K M a z
  have mB (K M : sfIntegralConstructibleCategory l L Y) (a : K ⟶ M)
      (z : Localization.Away (Padic.coefficientExtensionUniformizer l L)) :
      HEq (B.map (z ⊗ₜ[Padic.coefficientExtensionIntegers l L] a))
        (z ⊗ₜ[Padic.coefficientExtensionIntegers l L]
          (constructibleIntegralPullback l L f).map a) := by
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    simpa only [B, rationalDerivedPullback, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (rationalDerivedPullback_existsUnique l L f).exists.choose_spec.2.2 K M a z
  have mS (W : Scheme.{u}) (K M : sfIntegralConstructibleCategory l E W) (a : K ⟶ M)
      (z : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
      HEq ((sfRationalScalarExtension l E W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
        (z ⊗ₜ[Padic.coefficientExtensionIntegers l E] a))
        (c z ⊗ₜ[Padic.coefficientExtensionIntegers l L] (S W).map a) := by
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    simpa only [sfRationalScalarExtension, c, S, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (sfRationalScalarExtension_existsUnique l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.2 K M a z
  have : A.Additive := by
    simpa only [A, rationalDerivedPullback] using
      (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.1
  have : B.Additive := by
    simpa only [B, rationalDerivedPullback] using
      (rationalDerivedPullback_existsUnique l L f).exists.choose_spec.1
  apply OperationsScalarLocalization.iso_existsUnique _ _ c U V e (A ⋙ TX) (TY ⋙ B)
  · intro K
    exact (congrArg TX.obj (hA K)).trans (hS X _)
  · intro K
    exact (hB (TY.obj K)).trans
      (congrArg (fun Z : sfRationalConstructibleCategory l L Y ↦
        ScalarLocalization.mk ((constructibleIntegralPullback l L f).obj Z.obj)) (hS Y K))
  · intro K M a z
    exact (map_heq TX (hA _) (hA _) (mA K M a z)).trans
      (mS X _ _ ((constructibleIntegralPullback l E f).map a) z)
  · intro K M a z
    exact (map_heq B (hS Y _) (hS Y _) (mS Y K M a z)).trans
      (mB _ _ ((S Y).map a) (c z))

/-- The uniquely normalized rational pullback scalar comparison.
Source: blueprint common-stage paragraph
(blueprint: prose-03-02). -/
def rationalPullbackScalarComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :=
  (rationalPullbackScalarComparison_existsUnique l E L ι f).exists.choose

attribute [local irreducible] rationalPullbackScalarComparison

/-- Rational tensor comparison, fixed by rationalizing the specified integral comparison.
Source: blueprint common-stage paragraph
(blueprint: prose-03-02).
Proof: localize integralTensorScalarComparison. Both sides have the prescribed
integral tensor objects. On pairs of pure tensors, integral naturality and the
product of the two coefficients give rational naturality. Bilinearity gives it
on arbitrary maps. The integral inverse localizes to the inverse; the component
formula makes this isomorphism unique. -/
theorem rationalTensorScalarComparison_existsUnique (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    ∃! α : rationalDerivedTensor l E W ⋙
        sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ≅
      (sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).prod
        (sfRationalScalarExtension l E W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι) ⋙ rationalDerivedTensor l L W,
      ∀ M N : sfRationalConstructibleCategory l E W,
        HEq (α.hom.app (M, N)) ((sfRationalConstructibleLocalization l L W).map
          (integralTensorScalarComparison l E L ι W M.obj N.obj).hom) := by
  let S := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  let U := constructibleIntegralTensor l E W ⋙ S
  let V := S.prod S ⋙ constructibleIntegralTensor l L W
  let e : U ≅ V := NatIso.ofComponents
    (fun K ↦ integralTensorScalarComparison l E L ι W K.1 K.2) (by
      intro K M a
      apply ObjectProperty.hom_ext
      change (integralScalarExtension l E L ι W).map
          ((integralCompletedTensor l E W).map (Prod.mkHom a.1.hom a.2.hom)) ≫
            (scalarTensorCompleted l E L ι W M.1.obj M.2.obj
              M.1.property.1 M.2.property.1
              ((constructibleIntegralTensor l E W).obj M).property.1).hom =
        (scalarTensorCompleted l E L ι W K.1.obj K.2.obj
          K.1.property.1 K.2.property.1
          ((constructibleIntegralTensor l E W).obj K).property.1).hom ≫
          (integralCompletedTensor l L W).map (Prod.mkHom
            ((integralScalarExtension l E L ι W).map a.1.hom)
            ((integralScalarExtension l E L ι W).map a.2.hom))
      dsimp only [scalarTensorCompleted, Iso.trans_hom, Functor.mapIso_hom]
      have hnX := (scalarCompletion l E L ι W).naturality
        ((integralCompletedTensor l E W).map (Prod.mkHom a.1.hom a.2.hom))
      have hnO := (scalarTensorOrdinary l E L ι W).hom.naturality
        (Prod.mkHom a.1.hom a.2.hom)
      dsimp only [Functor.comp_map, Functor.prod_map] at hnO
      exact conjugation_naturality
        (scalarCompletionIso l E L ι W _
          ((constructibleIntegralTensor l E W).obj K).property.1)
        (scalarCompletionIso l E L ι W _
          ((constructibleIntegralTensor l E W).obj M).property.1)
        ((integralCompletedTensor l L W).mapIso (Iso.prod
          (scalarCompletionIso l E L ι W K.1.obj K.1.property.1)
          (scalarCompletionIso l E L ι W K.2.obj K.2.property.1)))
        ((integralCompletedTensor l L W).mapIso (Iso.prod
          (scalarCompletionIso l E L ι W M.1.obj M.1.property.1)
          (scalarCompletionIso l E L ι W M.2.obj M.2.property.1)))
        _ _ _ _
        ((scalarTensorOrdinary l E L ι W).app (K.1.obj, K.2.obj))
        ((scalarTensorOrdinary l E L ι W).app (M.1.obj, M.2.obj))
        hnX
        (by
          set_option backward.isDefEq.respectTransparency false in
          set_option backward.isDefEq.respectTransparency.types false in
          have h := congrArg (integralCompletedTensor l L W).map
            (show Prod.mkHom
                ((integralOrdinaryDerivedScalar l E L ι W).map a.1.hom)
                ((integralOrdinaryDerivedScalar l E L ι W).map a.2.hom) ≫
                  Prod.mkHom ((scalarCompletion l E L ι W).app M.1.obj)
                    ((scalarCompletion l E L ι W).app M.2.obj) =
              Prod.mkHom ((scalarCompletion l E L ι W).app K.1.obj)
                  ((scalarCompletion l E L ι W).app K.2.obj) ≫
                Prod.mkHom ((integralScalarExtension l E L ι W).map a.1.hom)
                  ((integralScalarExtension l E L ι W).map a.2.hom) by
              ext
              · exact (scalarCompletion l E L ι W).naturality a.1.hom
              · exact (scalarCompletion l E L ι W).naturality a.2.hom)
          simpa only [Functor.mapIso_hom, scalarCompletionIso, asIso_hom,
            Iso.prod_hom, Functor.map_comp] using h)
        hnO)
  let A := rationalDerivedTensor l E W
  let B := rationalDerivedTensor l L W
  let T := sfRationalScalarExtension l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  let c := (sfRationalCoefficientEquiv l L).symm.toRingHom.comp
    (ι.toRingHom.comp (sfRationalCoefficientEquiv l E).toRingHom)
  have hA : ∀ K, A.obj K = ⟨(constructibleIntegralTensor l E W).obj
      (K.1.obj, K.2.obj)⟩ := by
    exact (rationalTensor_spec l E W).1
  have hB : ∀ K, B.obj K = ⟨(constructibleIntegralTensor l L W).obj
      (K.1.obj, K.2.obj)⟩ := by
    exact (rationalTensor_spec l L W).1
  have hS : ∀ K, T.obj K = ⟨S.obj K.obj⟩ := by
    simpa only [T, S, sfRationalScalarExtension] using
      (sfRationalScalarExtension_existsUnique l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1
  have mS (K M : sfIntegralConstructibleCategory l E W) (a : K ⟶ M)
      (z : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
      HEq (T.map (z ⊗ₜ[Padic.coefficientExtensionIntegers l E] a))
        (c z ⊗ₜ[Padic.coefficientExtensionIntegers l L] S.map a) := by
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    change HEq ((sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
      (z ⊗ₜ[Padic.coefficientExtensionIntegers l E] a))
      ((sfRationalCoefficientEquiv l L).symm (ι (sfRationalCoefficientEquiv l E z))
        ⊗ₜ[Padic.coefficientExtensionIntegers l L] S.map a)
    simpa only [S, sfRationalScalarExtension, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (sfRationalScalarExtension_existsUnique l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.2 K M a z
  have mA := (rationalTensor_spec l E W).2
  have mB := (rationalTensor_spec l L W).2
  change ∃! α : A ⋙ T ≅ T.prod T ⋙ B, _
  suffices H : ∃! α : A ⋙ T ≅ T.prod T ⋙ B,
      ∀ K : sfRationalConstructibleCategory l E W × sfRationalConstructibleCategory l E W,
        HEq (α.hom.app K) ((sfRationalConstructibleLocalization l L W).map
          (integralTensorScalarComparison l E L ι W K.1.obj K.2.obj).hom) by
    obtain ⟨α, hα, huniq⟩ := H
    exact ⟨α, fun M N ↦ hα (M, N), fun α' hα' ↦ huniq α' (fun K ↦ hα' K.1 K.2)⟩
  exact OperationsScalarLocalization.bilinearComparison_existsUnique _ _ c
    (constructibleIntegralTensor l E W) (constructibleIntegralTensor l L W) S
    A B T hA hB hS mS mA mB e

/-- The uniquely normalized rational tensor scalar comparison.
Source: blueprint common-stage paragraph
(blueprint: prose-03-02). -/
def rationalTensorScalarComparison (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :=
  (rationalTensorScalarComparison_existsUnique l E L ι W).exists.choose

end RationalScalarComparisons

attribute [local irreducible] rationalPullbackScalarComparison rationalTensorScalarComparison

/-- Scalar extension preserves the permitted integral-Hom pairs.
Source: blueprint common-stage paragraph
(blueprint: prose-03-02).
Proof: the source Hom is constructible by the permitted-pair predicate. Completed
scalar extension preserves that predicate. scalarHomCompleted identifies its
extension with the target Hom using the evaluation-defined ordinary comparison
and the three normalized completion maps. Constructibility is invariant under
this actual integral isomorphism, proving precisely the target predicate. -/
theorem integralHomScalarPair_permitted (W : Scheme.{u})
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory) :
    sfIntegralConstructible l L W ((integralDerivedInternalHom l L W).obj
      (op ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj P.obj.1.unop).obj,
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj P.obj.2).obj)) := by
  have hIso := (scalarHomCompleted l E L ι W P.obj.1.unop.obj P.obj.2.obj
    P.obj.1.unop.property.1 P.obj.2.property.1 P.property.1)
  have hK := ((sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj
      ((constructibleIntegralHom l E W).obj P)).property
  apply (sfIntegralConstructible l L W).prop_of_iso hIso
  exact hK

/-- The scalar-extended permitted integral pair.
Source: blueprint common-stage paragraph
(blueprint: prose-03-02). -/
def integralHomScalarPair (W : Scheme.{u})
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory) :
    (constructibleIntegralHomPairs l L W).FullSubcategory :=
  ⟨(op ((sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj P.obj.1.unop),
    (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj P.obj.2),
    integralHomScalarPair_permitted l E L ι W P⟩

/-- The restricted integral Hom comparison is the specified completed ambient comparison.
Source: blueprint common-stage paragraph
(blueprint: prose-03-02). -/
def integralHomScalarComparison (W : Scheme.{u})
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory) :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      E L ι W).obj ((constructibleIntegralHom l E W).obj P) ≅
      (constructibleIntegralHom l L W).obj (integralHomScalarPair l E L ι W P) :=
  ObjectProperty.isoMk _ (scalarHomCompleted l E L ι W P.obj.1.unop.obj P.obj.2.obj
    P.obj.1.unop.property.1 P.obj.2.property.1 P.property.1)

/-- Rational scalar extension preserves exactly the permitted Hom-pair domain.
Source: blueprint common-stage paragraph
(blueprint: prose-03-02).
Proof: the rational scalar object formula gives the scalar extension of the
underlying integral objects. Substitute those formulas in the domain predicate;
it becomes integralHomScalarPair_permitted, with only proof-irrelevant subtype
fields to identify. No rational isomorphism is used to infer integral constructibility. -/
theorem rationalHomScalarPair_permitted (W : Scheme.{u})
    (P : (constructibleRationalHomPairs l E W).FullSubcategory) :
    constructibleRationalHomPairs l L W
      (op ((sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.1.unop),
        (sfRationalScalarExtension l E W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.2) := by
  change constructibleIntegralHomPairs l L W
    (op ((sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.1.unop).obj,
      ((sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.2).obj)
  have h := integralHomScalarPair_permitted l E L ι W
    (integralPairOfRationalHomPair l E W P)
  have hs : ∀ K : sfRationalConstructibleCategory l E W,
      (sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K =
      ⟨(sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj K.obj⟩ := by
    simpa only [sfRationalScalarExtension] using
      (sfRationalScalarExtension_existsUnique l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1
  rw [hs P.obj.1.unop, hs P.obj.2]
  exact h

/-- The permitted rational pair after scalar extension.
Source: blueprint common-stage paragraph
(blueprint: prose-03-02). -/
def rationalHomScalarPair (W : Scheme.{u})
    (P : (constructibleRationalHomPairs l E W).FullSubcategory) :
    (constructibleRationalHomPairs l L W).FullSubcategory :=
  ⟨(op ((sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.1.unop),
    (sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.2),
    rationalHomScalarPair_permitted l E L ι W P⟩

/-- Rational Hom scalar comparison is precisely the rationalized canonical integral map.
Source: blueprint common-stage paragraph
(blueprint: prose-03-02).
Proof: use the scalar and Hom object formulas to identify the endpoints with the
localizations of the integral endpoints. Localize integralHomScalarComparison
and its inverse. Its hom is the displayed component, which also proves uniqueness.
Naturality extends from the integral comparison by the separate linearity of Hom,
with precomposition in the first variable. -/
theorem rationalHomScalarComparison_existsUnique (W : Scheme.{u})
    (P : (constructibleRationalHomPairs l E W).FullSubcategory) :
    ∃! α : (sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
          ((rationalDerivedInternalHom l E W).obj P) ≅
      (rationalDerivedInternalHom l L W).obj (rationalHomScalarPair l E L ι W P),
      HEq α.hom ((sfRationalConstructibleLocalization l L W).map
        (integralHomScalarComparison l E L ι W (integralPairOfRationalHomPair l E W P)).hom) := by
  have hs : ∀ K : sfRationalConstructibleCategory l E W,
      (sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K =
      ⟨(sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj K.obj⟩ := by
    simpa only [sfRationalScalarExtension] using
      (sfRationalScalarExtension_existsUnique l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1
  have he : ∀ P : (constructibleRationalHomPairs l E W).FullSubcategory,
      (rationalDerivedInternalHom l E W).obj P =
      ⟨(constructibleIntegralHom l E W).obj (integralPairOfRationalHomPair l E W P)⟩ := by
    simpa only [rationalDerivedInternalHom] using
      (rationalDerivedInternalHom_existsUnique l E W).exists.choose_spec.1
  have hl : ∀ P : (constructibleRationalHomPairs l L W).FullSubcategory,
      (rationalDerivedInternalHom l L W).obj P =
      ⟨(constructibleIntegralHom l L W).obj (integralPairOfRationalHomPair l L W P)⟩ := by
    simpa only [rationalDerivedInternalHom] using
      (rationalDerivedInternalHom_existsUnique l L W).exists.choose_spec.1
  have hp : integralPairOfRationalHomPair l L W (rationalHomScalarPair l E L ι W P) =
      integralHomScalarPair l E L ι W (integralPairOfRationalHomPair l E W P) := by
    apply ObjectProperty.FullSubcategory.ext
    change (op (((sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.1.unop).obj),
      ((sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.2).obj) = _
    rw [hs P.obj.1.unop, hs P.obj.2]
    rfl
  have hx : (sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
        ((rationalDerivedInternalHom l E W).obj P) =
      (sfRationalConstructibleLocalization l L W).obj
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj
            ((constructibleIntegralHom l E W).obj
              (integralPairOfRationalHomPair l E W P))) := by
    rw [hs, he]
    rfl
  have hy : (rationalDerivedInternalHom l L W).obj
      (rationalHomScalarPair l E L ι W P) =
      (sfRationalConstructibleLocalization l L W).obj
        ((constructibleIntegralHom l L W).obj
          (integralHomScalarPair l E L ι W (integralPairOfRationalHomPair l E W P))) := by
    rw [hl, hp]
    rfl
  let e := (sfRationalConstructibleLocalization l L W).mapIso
    (integralHomScalarComparison l E L ι W (integralPairOfRationalHomPair l E W P))
  let a := eqToIso hx ≪≫ e ≪≫ (eqToIso hy).symm
  have ha : HEq a.hom e.hom := by simp [a]
  refine ⟨a, ha, ?_⟩
  intro a' ha'
  apply Iso.ext
  exact eq_of_heq (ha'.trans ha.symm)

/-- The uniquely normalized rational internal-Hom scalar comparison.
Source: blueprint common-stage paragraph
(blueprint: prose-03-02). -/
def rationalHomScalarComparison (W : Scheme.{u})
    (P : (constructibleRationalHomPairs l E W).FullSubcategory) :=
  (rationalHomScalarComparison_existsUnique l E L ι W P).exists.choose

end ScalarComparisons

end WeilConjectures

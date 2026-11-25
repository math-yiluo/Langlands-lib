/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedReflection.PodReindexingCompletedEvaluationReflection
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
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
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexCoefficientTransition
public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
public import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeCoordinates
public import WeilConjectures.PoincareDuality.Pod.PodCommonStageObjectNormalizations
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.PoincareDuality.PodCoefficientDescent.PodCommonStageCompositorNaturality
import WeilConjectures.PoincareDuality.PodCoefficientDescent.PodFiniteScalarCoordinatesRealization
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationPullbackPairIso
import WeilConjectures.SmoothPurity.Integral.IntegralCompletedTensorBilinear
import WeilConjectures.PoincareDuality.PodCoefficientDescent.PodPairNatIsoDescent
import WeilConjectures.SmoothPurity.Common.CommonStagePullbackDescent
import WeilConjectures.ZetaWeil.SpecifiedHomScalarRationalNaturality
import all WeilConjectures.SmoothPurity.CommonStageInternalHom.CommonStageInternalHomCoherenceLemmas
import all WeilConjectures.SmoothPurity.CommonStageInternalHom.CommonStageInternalHomCoherence

/-! # Scalar and localized descent of the reindexed internal Hom

Source: current blueprint, theorem-poincare-duality-frobenius--2, proof Step 5;
Stacks Project, Tags 08J9 and 0GMX
(blueprint: lem-pod-reindexing-hom-coefficient-descent).

The ambient comparison uses the prescribed evaluation transpose. The integral,
rational and common-stage comparisons below retain that same map and its inverse.
The coefficient scalars have degree zero, including in ramified extensions.

## Main statements

* `ambient_scalar`, `ambient_coordinates`, `ambient_scalar_chain`: unrestricted
  finite-free base change, normalized coordinates and representative evaluation.
* `integralComparison`, `rationalComparison`, `commonComparison`: the same
  evaluation-normalized reindexing comparison at the three coefficient stages.
* `rational_scalar`, `rational_signed_shifts`, `rational_composition`: the fixed
  scalar, signed-shift and composition equations before common-stage descent.
-/

@[expose] public noncomputable section
set_option linter.privateModule false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TensorProduct
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodCoefficientDescent

attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
  HasDerivedCategory.standard completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence

private theorem existsUnique_iso_of_eq {C : Type*} [Category* C]
    {A B A' B' : C} (hA : A = A') (hB : B = B') (e : A' ≅ B') :
    ∃! d : A ≅ B, HEq d.hom e.hom := by
  subst A'
  subst B'
  exact ⟨e, HEq.rfl, fun d hd ↦ Iso.ext (eq_of_heq hd)⟩

private theorem localizedLinearEquiv_existsUnique
    {R : Type*} [CommRing R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]
    (p : R) (A B X Y : ScalarLocalization R C p) (A₀ B₀ X₀ Y₀ : C)
    (hA : A = ⟨A₀⟩) (hB : B = ⟨B₀⟩) (hX : X = ⟨X₀⟩) (hY : Y = ⟨Y₀⟩)
    (e₀ : (A₀ ⟶ B₀) ≃ₗ[R] (X₀ ⟶ Y₀)) :
    ∃! e : (A ⟶ B) ≃ₗ[Localization.Away p] (X ⟶ Y),
      ∀ (f : A₀ ⟶ B₀) (a : Localization.Away p) (q : A ⟶ B),
        HEq q (a ⊗ₜ[R] f) → HEq (e q) (a ⊗ₜ[R] e₀ f) := by
  cases hA
  cases hB
  cases hX
  cases hY
  refine ⟨e₀.baseChange R (Localization.Away p), ?_, ?_⟩
  · intro f a q hq
    cases hq
    rfl
  · intro e he
    apply LinearEquiv.ext
    intro q
    induction q using TensorProduct.inductionOn with
    | tmul a f => exact eq_of_heq (he f a _ HEq.rfl)
    | add q q' hq hq' => simp only [map_add, hq, hq']

private theorem copyObj_eq {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (obj : C → D) (h : ∀ X, F.obj X = obj X) :
    F.copyObj obj (fun X ↦ eqToIso (h X)) = F := by
  exact (Functor.ext_of_iso (F.isoCopyObj obj (fun X ↦ eqToIso (h X))) h
    (fun _ ↦ rfl)).symm

private theorem fullSubcategory_shift_obj {C : Type*} [Category* C] [HasShift C ℤ]
    (P : ObjectProperty C) [P.IsStableUnderShift ℤ] (M : P.FullSubcategory) (a : ℤ) :
    (M⟦a⟧).obj = M.obj⟦a⟧ := by
  unfold shiftFunctor ObjectProperty.hasShift
  rfl

private theorem inverse_square {C : Type*} [Category* C] {A B D E : C}
    (i : A ⟶ B) (j : D ⟶ E) [IsIso i] [IsIso j]
    (f : A ⟶ D) (g : B ⟶ E) (h : f ≫ j = i ≫ g) :
    g ≫ inv j = inv i ≫ f := by
  apply (cancel_epi i).1
  simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rw [← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct

attribute [local irreducible] Linear.homModule

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section FiniteScalar
variable (L : Type u) [Field L] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] scalarIntegralClosed scalarClosedTensor scalarHomOrdinary

end FiniteScalar

/-- Completed evaluation in the recorded full constructible category.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
def integralEvaluation (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory) :
    (constructibleIntegralTensor l E W).obj
      (P.obj.1.unop, (constructibleIntegralHom l E W).obj P) ⟶ P.obj.2 :=
  ObjectProperty.homMk (PodCompletedReflection.evaluation l E W
    P.obj.1.unop P.obj.2 P.property)

/-- The recorded completed transposition, restricted by fullness.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
def integralTranspose (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory)
    (K : sfIntegralConstructibleCategory l E W)
    (b : (constructibleIntegralTensor l E W).obj (P.obj.1.unop, K) ⟶ P.obj.2) :
    K ⟶ (constructibleIntegralHom l E W).obj P :=
  ObjectProperty.homMk
    (PodCompletedReflection.transpose l E W P.obj.1.unop K P.obj.2 b.hom)

section IntegralTransposeLinearity

set_option allowUnsafeReducibility true in
attribute [local semireducible] Preadditive.fullSubcategory

private def integralTransposeEquiv (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory)
    (K : sfIntegralConstructibleCategory l E W) :
    ((constructibleIntegralTensor l E W).obj (P.obj.1.unop, K) ⟶ P.obj.2) ≃
      (K ⟶ (constructibleIntegralHom l E W).obj P) :=
  InducedCategory.homEquiv.trans
    ((PodCompletedReflection.transpose l E W P.obj.1.unop K P.obj.2).trans
      (InducedCategory.homEquiv (X := K)
        (Y := (constructibleIntegralHom l E W).obj P)).symm)

private theorem integralTransposeEquiv_symm (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory)
    (K : sfIntegralConstructibleCategory l E W)
    (t : K ⟶ (constructibleIntegralHom l E W).obj P) :
    (integralTransposeEquiv l E W P K).symm t =
      (constructibleIntegralTensor l E W).map (Prod.mkHom (𝟙 _) t) ≫
        integralEvaluation l E W P := by
  apply (integralTransposeEquiv l E W P K).injective
  rw [Equiv.apply_symm_apply]
  apply ObjectProperty.hom_ext
  have hn := (PodCompletedReflection.reflection_laws l E W).2.1
    P.obj.1.unop P.obj.1.unop ((constructibleIntegralHom l E W).obj P) K
    P.obj.2 P.obj.2 (𝟙 _) t (𝟙 _)
    (PodCompletedReflection.evaluation l E W P.obj.1.unop P.obj.2 P.property)
  have he := (PodCompletedReflection.transpose l E W P.obj.1.unop
    ((constructibleIntegralHom l E W).obj P) P.obj.2).apply_symm_apply (𝟙 _)
  change (PodCompletedReflection.transpose l E W P.obj.1.unop
    ((constructibleIntegralHom l E W).obj P) P.obj.2)
      (PodCompletedReflection.evaluation l E W P.obj.1.unop P.obj.2 P.property) = 𝟙 _ at he
  change (PodCompletedReflection.transpose l E W P.obj.1.unop K P.obj.2)
      ((integralCompletedTensor l E W).map (Prod.mkHom (𝟙 _) t.hom) ≫
        PodCompletedReflection.evaluation l E W P.obj.1.unop P.obj.2 P.property ≫ 𝟙 _) =
    t.hom ≫ _ ≫ (podReindexingDerivedHom l E W none).map (𝟙 _) at hn
  change t.hom = (PodCompletedReflection.transpose l E W P.obj.1.unop K P.obj.2)
    ((integralCompletedTensor l E W).map (Prod.mkHom (𝟙 _) t.hom) ≫
      PodCompletedReflection.evaluation l E W P.obj.1.unop P.obj.2 P.property)
  rw [he] at hn
  rw [CategoryTheory.Functor.map_id] at hn
  erw [CategoryTheory.Category.comp_id, CategoryTheory.Category.comp_id,
    CategoryTheory.Category.comp_id] at hn
  exact hn.symm

private def integralTransposeLinear (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory)
    (K : sfIntegralConstructibleCategory l E W) :
    ((constructibleIntegralTensor l E W).obj (P.obj.1.unop, K) ⟶ P.obj.2) ≃ₗ[
      Padic.coefficientExtensionIntegers l E]
      (K ⟶ (constructibleIntegralHom l E W).obj P) := by
  let H := (constructibleIntegralHom l E W).obj P
  let β := (integralCompletedTensor_bilinear l E W
    P.obj.1.unop.obj P.obj.1.unop.obj K.obj H.obj).choose
  have hβ := (integralCompletedTensor_bilinear l E W
    P.obj.1.unop.obj P.obj.1.unop.obj K.obj H.obj).choose_spec
  let R := Padic.coefficientExtensionIntegers l E
  let TK := (constructibleIntegralTensor l E W).obj (P.obj.1.unop, K)
  let f : (K ⟶ H) →ₗ[R] (TK ⟶ P.obj.2) :=
    (InducedCategory.homLinearEquiv (R := R) (X := TK) (Y := P.obj.2)).symm.toLinearMap.comp
      ((Linear.rightComp R TK.obj (integralEvaluation l E W P).hom).comp
        ((β (𝟙 _)).comp ((sfIntegralConstructible l E W).ι.mapLinearMap R)))
  have hf (t : K ⟶ H) : f t = (integralTransposeEquiv l E W P K).symm t := by
    rw [integralTransposeEquiv_symm]
    apply ObjectProperty.hom_ext
    exact congrArg (· ≫ (integralEvaluation l E W P).hom) (hβ (𝟙 _) t.hom)
  have hi (b : TK ⟶ P.obj.2) : f (integralTransposeEquiv l E W P K b) = b :=
    (hf _).trans ((integralTransposeEquiv l E W P K).symm_apply_apply b)
  exact {
    integralTransposeEquiv l E W P K with
    map_add' := by
      intro b b'
      apply (integralTransposeEquiv l E W P K).symm.injective
      simp only [← hf, map_add]
      exact (hi (b + b')).trans (congrArg₂ (· + ·) (hi b) (hi b')).symm
    map_smul' := by
      intro r b
      apply (integralTransposeEquiv l E W P K).symm.injective
      simp only [← hf, map_smul]
      exact (hi (r • b)).trans (congrArg (r • ·) (hi b)).symm }

end IntegralTransposeLinearity

/-- Rational transposition is the unique linear extension of completed transposition.
The HEq premises transport only the already specified, unchanged integral objects.
Source: blueprint Step 5; Stacks 08J9
(blueprint: lem-pod-reindexing-hom-coefficient-descent).
Proof (node Steps 10--11): completed currying is O_E-linear, since evaluation,
the tensor unit and ordinary signed currying commute with constant scalars.
Tensor its linear map and inverse with E. The two inverse equations localize.
The recorded tensor and Hom object formulas identify the endpoints, giving the
specified formula on pure tensors. Pure tensors generate, proving uniqueness. -/
theorem rational_transpose_existsUnique (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (P : (constructibleRationalHomPairs l E W).FullSubcategory)
    (K : sfRationalConstructibleCategory l E W) :
    ∃! e : ((rationalDerivedTensor l E W).obj (P.obj.1.unop, K) ⟶ P.obj.2) ≃ₗ[
        Localization.Away (Padic.coefficientExtensionUniformizer l E)]
      (K ⟶ (rationalDerivedInternalHom l E W).obj P),
      ∀ (b : (constructibleIntegralTensor l E W).obj (P.obj.1.unop.obj, K.obj) ⟶ P.obj.2.obj)
        (a : Localization.Away (Padic.coefficientExtensionUniformizer l E))
        (r : (rationalDerivedTensor l E W).obj (P.obj.1.unop, K) ⟶ P.obj.2),
        HEq r (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] b) →
          HEq (e r) (a ⊗ₜ[Padic.coefficientExtensionIntegers l E]
            integralTranspose l E W (integralPairOfRationalHomPair l E W P) K.obj b) := by
  exact localizedLinearEquiv_existsUnique
    (Padic.coefficientExtensionUniformizer l E)
    ((rationalDerivedTensor l E W).obj (P.obj.1.unop, K)) P.obj.2 K
    ((rationalDerivedInternalHom l E W).obj P)
    ((constructibleIntegralTensor l E W).obj (P.obj.1.unop.obj, K.obj))
    P.obj.2.obj K.obj
    ((constructibleIntegralHom l E W).obj (integralPairOfRationalHomPair l E W P))
    ((rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1 _) rfl rfl
    ((rationalDerivedInternalHom_existsUnique l E W).exists.choose_spec.1 P)
    (integralTransposeLinear l E W (integralPairOfRationalHomPair l E W P) K.obj)

/-- The canonical linear rational transposition, including all localized inputs.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
def rationalTranspose (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (P : (constructibleRationalHomPairs l E W).FullSubcategory)
    (K : sfRationalConstructibleCategory l E W) :=
  (rational_transpose_existsUnique l E W P K).exists.choose

/-- Rational evaluation is the inverse transpose of the identity, with the original sign.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
def rationalEvaluation (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (P : (constructibleRationalHomPairs l E W).FullSubcategory) :=
  (rationalTranspose l E W P ((rationalDerivedInternalHom l E W).obj P)).symm (𝟙 _)

/-- Both integer shifts preserve the specified permitted-pair domain.
Source: blueprint Step 5; Stacks 08JA
(blueprint: lem-pod-reindexing-hom-coefficient-descent).
Proof (node Steps 9--12): signed ambient Hom shift identifies the shifted output
with the old Hom shifted by b - a. Constructibility is stable under every integer
shift and under this isomorphism. Both source and target shifts are retained. -/
theorem shifted_pair_permitted (W : Scheme.{u})
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory) (a b : ℤ) :
    constructibleIntegralHomPairs l E W (op (P.obj.1.unop⟦a⟧), P.obj.2⟦b⟧) := by
  change sfIntegralConstructible l E W
    ((integralDerivedInternalHom l E W).obj
      (op (P.obj.1.unop⟦a⟧).obj, (P.obj.2⟦b⟧).obj))
  rw [fullSubcategory_shift_obj, fullSubcategory_shift_obj]
  exact (sfIntegralConstructible l E W).prop_of_iso
    (PodReindexingCoherence.signedShift l E W none
      P.obj.1.unop.obj P.obj.2.obj a b).symm
    ((sfIntegralConstructible l E W).le_shift (b - a) _ P.property)

/-- The shifted integral pair, with the inherited ambient integer shifts.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
def shiftedPair (W : Scheme.{u})
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory) (a b : ℤ) :
    (constructibleIntegralHomPairs l E W).FullSubcategory :=
  ⟨(op (P.obj.1.unop⟦a⟧), P.obj.2⟦b⟧), shifted_pair_permitted l E W P a b⟩

/-- Fullness restricts the actual signed ambient Hom shift, including its Koszul sign.
Source: blueprint Step 5; Stacks 0A8X, 08JA
(blueprint: lem-pod-reindexing-hom-coefficient-descent).
Proof (node Steps 9--12): use the inherited ambient shifts and the signed Hom
comparison. Its degree-r source-shift factor is (-1)^(a*r). Both endpoints are
constructible by shifted_pair_permitted; fullness restricts the same arrow and
its inverse. The underlying arrow fixes the isomorphism uniquely. -/
theorem integral_signedShift_existsUnique (W : Scheme.{u})
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory) (a b : ℤ) :
    ∃! e : (constructibleIntegralHom l E W).obj (shiftedPair l E W P a b) ≅
      ((constructibleIntegralHom l E W).obj P)⟦b - a⟧,
      HEq e.hom.hom (PodReindexingCoherence.signedShift l E W none
        P.obj.1.unop.obj P.obj.2.obj a b).hom := by
  have hsource :
      ((constructibleIntegralHom l E W).obj (shiftedPair l E W P a b)).obj =
        (podReindexingDerivedHom l E W none).obj
          (op (P.obj.1.unop.obj⟦a⟧), P.obj.2.obj⟦b⟧) := by
    change (integralDerivedInternalHom l E W).obj
      (op (P.obj.1.unop⟦a⟧).obj, (P.obj.2⟦b⟧).obj) = _
    rw [fullSubcategory_shift_obj, fullSubcategory_shift_obj]
    rfl
  have htarget : (((constructibleIntegralHom l E W).obj P)⟦b - a⟧).obj =
      ((podReindexingDerivedHom l E W none).obj
        (op P.obj.1.unop.obj, P.obj.2.obj))⟦b - a⟧ :=
    fullSubcategory_shift_obj _ _ _
  obtain ⟨e, he, _⟩ := existsUnique_iso_of_eq hsource htarget
    (PodReindexingCoherence.signedShift l E W none
      P.obj.1.unop.obj P.obj.2.obj a b)
  refine ⟨(sfIntegralConstructible l E W).isoMk e, he, ?_⟩
  intro f hf
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact eq_of_heq (hf.trans he.symm)

/-- The original signed integral Hom shift in its full subcategory.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
def integralSignedShift (W : Scheme.{u})
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory) (a b : ℤ) :=
  (integral_signedShift_existsUnique l E W P a b).exists.choose

section Reindex
variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The specified pullback preserves the permitted integral Hom domain.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent).
Proof (node Steps 8--9): identify ordinary reindexing with the specified pullback
by their identical quotient and zero shifted-product coordinates. The ambient
comparison and completed-evaluation reflection preserve constructibility of Hom.
Conjugate its two inputs by the projection-normalized pullback identifications. -/
theorem integral_pair_permitted
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) :
    constructibleIntegralHomPairs l E X
      (op ((constructibleIntegralPullback l E g).obj P.obj.1.unop),
        (constructibleIntegralPullback l E g).obj P.obj.2) := by
  obtain ⟨A, _, _, _, hA⟩ :=
    PodCompletedReflection.podReindexingCompletedEvaluationReflection l E
  obtain ⟨_, _, _, hκ, c, _⟩ := hA g
  let κ (K : sfIntegralConstructibleCategory l E Y) :
      (podOrdinaryReindex l E g).obj K.obj ≅
        (integralDerivedPullback l E g).obj K.obj := by
    letI := hκ K
    exact asIso ((podOrdinaryToCompleted l E g (A.completion g)).app K.obj)
  have hP : sfIntegralConstructible l E Y
      (PodCompletedReflection.hom l E Y P.obj.1.unop.obj P.obj.2.obj) := P.property
  have hH := PodCompletedReflection.constructible_hom l E g
    (A.completion g) (A.tensor g) c P.obj.1.unop P.obj.2 hP
  let e := (podReindexingDerivedHom l E X none).mapIso
    ((κ P.obj.1.unop).symm.op.prod (κ P.obj.2))
  exact (sfIntegralConstructible l E X).prop_of_iso e hH

/-- Pull back the actual permitted pair, with no change to its morphisms.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
def integralPair : (constructibleIntegralHomPairs l E Y).FullSubcategory ⥤
    (constructibleIntegralHomPairs l E X).FullSubcategory :=
  (constructibleIntegralHomPairs l E X).lift
    ((constructibleIntegralHomPairs l E Y).ι ⋙
      (constructibleIntegralPullback l E g).op.prod (constructibleIntegralPullback l E g))
    (integral_pair_permitted l E g)

/-- Precisely the kappa-conjugate of the ambient c-zero, in specified pullback coordinates.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
def IsIntegralNormalized
    (A : PodCompletionReindex l E g) (c : PodCompletedReflection.Comparison l E g)
    (α : constructibleIntegralHom l E Y ⋙ constructibleIntegralPullback l E g ≅
      integralPair l E g ⋙ constructibleIntegralHom l E X) : Prop :=
  ∀ P : (constructibleIntegralHomPairs l E Y).FullSubcategory,
    (podOrdinaryToCompleted l E g A).app
        ((integralDerivedInternalHom l E Y).obj (op P.obj.1.unop.obj, P.obj.2.obj)) ≫
      (α.hom.app P).hom ≫
      (integralDerivedInternalHom l E X).map (Prod.mkHom
        ((podOrdinaryToCompleted l E g A).app P.obj.1.unop.obj).op (𝟙 _)) =
    (PodCompletedReflection.homComparison l E g c P.obj.1.unop.obj P.obj.2.obj).hom ≫
      (integralDerivedInternalHom l E X).map (Prod.mkHom (𝟙 _)
        ((podOrdinaryToCompleted l E g A).app P.obj.2.obj))

private theorem completionUnit_isIso
    (A : PodCompletionReindex l E g) (hA : PodCompletionReindex.Laws l E g A)
    (K : sfIntegralConstructibleCategory l E Y) :
    IsIso ((podOrdinaryToCompleted l E g A).app K.obj) := by
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  let D : FiniteFieldDatum.{0} := {
    p := p, a := 1, q := p, prime := hp, exponent_pos := le_refl 1,
    cardinality_eq := (pow_one p).symm, k₀ := ZMod p,
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ZMod p) }
  have hlp : l ≠ D.p := by change l ≠ p; omega
  have hK : IntegralOnSlice.IsComplete l E Y none K.obj :=
    ⟨D, hlp, (sfDerivedComplete_iff_legacy l E Y D hlp K.obj).mp K.property.1⟩
  have : IsIso ((podReindexCalculus l E Y).adjunction.unit.app K.obj) :=
    hA.2.2.2.2.2.1 K.obj hK
  dsimp [podOrdinaryToCompleted]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The uniquely normalized integral comparison in the constructible category.
Source: blueprint Step 5; Stacks 099B, 08J9
(blueprint: lem-pod-reindexing-hom-coefficient-descent).
Proof (node Steps 6--9): finite-free completion exchange preserves the actual unit;
the DVR equation varpi_E=u varpi_L^e and exact products apply also when ramified.
The entire-system scalar realization pins tensor and pullback comparisons on both
Roos coordinates. The specified-Hom evaluation pin identifies the remaining Hom
comparison. Precompose with the ordinary-to-completed unit; reflector injectivity
reduces every completed equation to the ordinary one. The kappa-conjugate is the
specified integral isomorphism. Fullness gives naturality; invertibility of kappa
and the ambient map gives invertibility and uniqueness, without any perfectness. -/
theorem integral_comparison_existsUnique
    (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
    (_hA : PodCompletionReindex.Laws l E g A)
    (_hT : PodCompletedTensorReindex.Laws l E g A T)
    (c : PodCompletedReflection.Comparison l E g) :
    ∃! α : constructibleIntegralHom l E Y ⋙ constructibleIntegralPullback l E g ≅
      integralPair l E g ⋙ constructibleIntegralHom l E X,
      IsIntegralNormalized l E g A c α := by
  let F := podOrdinaryReindex l E g
  let G := integralDerivedPullback l E g
  let H := podReindexingDerivedHom l E X none
  let κ := podOrdinaryToCompleted l E g A
  have hκ (K : sfIntegralConstructibleCategory l E Y) : IsIso (κ.app K.obj) :=
    completionUnit_isIso l E g A _hA K
  let e (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) :
      (constructibleIntegralPullback l E g).obj ((constructibleIntegralHom l E Y).obj P) ≅
        (constructibleIntegralHom l E X).obj ((integralPair l E g).obj P) := by
    have := hκ ((constructibleIntegralHom l E Y).obj P)
    have := hκ P.obj.1.unop
    have := hκ P.obj.2
    exact (sfIntegralConstructible l E X).isoMk
      ((asIso (κ.app ((constructibleIntegralHom l E Y).obj P).obj)).symm ≪≫
        PodCompletedReflection.homComparison l E g c P.obj.1.unop.obj P.obj.2.obj ≪≫
        H.mapIso ((asIso (κ.app P.obj.1.unop.obj)).symm.op.prod
          (asIso (κ.app P.obj.2.obj))))
  have he (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) :
      (e P).hom.hom = inv (κ.app ((constructibleIntegralHom l E Y).obj P).obj) ≫
        (PodCompletedReflection.homComparison l E g c P.obj.1.unop.obj P.obj.2.obj).hom ≫
        H.map (Prod.mkHom (inv (κ.app P.obj.1.unop.obj)).op (κ.app P.obj.2.obj)) := rfl
  have hn (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) :
      κ.app ((constructibleIntegralHom l E Y).obj P).obj ≫ (e P).hom.hom ≫
        H.map (Prod.mkHom (κ.app P.obj.1.unop.obj).op (𝟙 _)) =
      (PodCompletedReflection.homComparison l E g c P.obj.1.unop.obj P.obj.2.obj).hom ≫
        H.map (Prod.mkHom (𝟙 _) (κ.app P.obj.2.obj)) := by
    have := hκ ((constructibleIntegralHom l E Y).obj P)
    have := hκ P.obj.1.unop
    rw [he]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, ← H.map_comp,
      prod_comp, ← op_comp, IsIso.hom_inv_id]
    congr 2
    apply Prod.ext
    · rfl
    · exact Category.comp_id _
  let α : constructibleIntegralHom l E Y ⋙ constructibleIntegralPullback l E g ≅
      integralPair l E g ⋙ constructibleIntegralHom l E X :=
    NatIso.ofComponents e (by
      intro P Q f
      apply ObjectProperty.hom_ext
      change G.map ((integralDerivedInternalHom l E Y).map
        (Prod.mkHom f.hom.1.unop.hom.op f.hom.2.hom)) ≫ (e Q).hom.hom =
        (e P).hom.hom ≫ H.map
          (Prod.mkHom (G.map f.hom.1.unop.hom).op (G.map f.hom.2.hom))
      rw [he, he]
      have hH := κ.naturality ((integralDerivedInternalHom l E Y).map
        (Prod.mkHom f.hom.1.unop.hom.op f.hom.2.hom))
      have hM := κ.naturality f.hom.1.unop.hom
      have hN := κ.naturality f.hom.2.hom
      have hc := (PodCompletedReflection.reindexing_laws l E g A T _hA _hT c).2.2.2.2
        P.obj.1.unop.obj Q.obj.1.unop.obj P.obj.2.obj Q.obj.2.obj
        f.hom.1.unop.hom f.hom.2.hom
      have := hκ ((constructibleIntegralHom l E Y).obj P)
      have := hκ ((constructibleIntegralHom l E Y).obj Q)
      have := hκ P.obj.1.unop
      have := hκ Q.obj.1.unop
      change F.map _ ≫ κ.app ((constructibleIntegralHom l E Y).obj Q).obj =
        κ.app ((constructibleIntegralHom l E Y).obj P).obj ≫ G.map _ at hH
      have hH' := @inverse_square _ _ _ _ _ _
        (κ.app ((constructibleIntegralHom l E Y).obj P).obj)
        (κ.app ((constructibleIntegralHom l E Y).obj Q).obj) (hκ _) (hκ _) _ _ hH
      have hM' := inverse_square _ _ _ _ hM
      simp only [Category.assoc]
      erw [reassoc_of% hH', reassoc_of% hc]
      congr 2
      rw [← H.map_comp, ← H.map_comp]
      congr 1
      ext
      · exact hM'.symm
      · exact hN)
  refine ⟨α, hn, ?_⟩
  intro β hβ
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply ObjectProperty.hom_ext
  change (β.hom.app P).hom = (e P).hom.hom
  have := hκ ((constructibleIntegralHom l E Y).obj P)
  have := hκ P.obj.1.unop
  let d := H.mapIso
    ((asIso (κ.app P.obj.1.unop.obj)).op.prod
      (Iso.refl (G.obj P.obj.2.obj)))
  have hβ' := hβ P
  change κ.app ((constructibleIntegralHom l E Y).obj P).obj ≫
    (β.hom.app P).hom ≫ d.hom = _ at hβ'
  have hn' := hn P
  change κ.app ((constructibleIntegralHom l E Y).obj P).obj ≫
    (e P).hom.hom ≫ d.hom = _ at hn'
  apply (cancel_epi (κ.app ((constructibleIntegralHom l E Y).obj P).obj)).1
  apply (cancel_mono d.hom).1
  simpa only [Category.assoc] using hβ'.trans hn'.symm

/-- Rational pullback preserves exactly the integral permitted-pair domain on objects.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent).
Proof (node Step 10): rational pullback has the same integral object formula, so
integral_pair_permitted gives the result. No restriction is imposed on arrows. -/
theorem rational_pair_permitted
    (P : (constructibleRationalHomPairs l E Y).FullSubcategory) :
    constructibleRationalHomPairs l E X
      (op ((rationalDerivedPullback l E g).obj P.obj.1.unop),
        (rationalDerivedPullback l E g).obj P.obj.2) := by
  have hobj := (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.1
  change constructibleIntegralHomPairs l E X
    (op (((rationalDerivedPullback l E g).obj P.obj.1.unop).obj),
      ((rationalDerivedPullback l E g).obj P.obj.2).obj)
  change constructibleIntegralHomPairs l E X
    (op (((rationalDerivedPullback_existsUnique l E g).exists.choose.obj
      P.obj.1.unop).obj),
      ((rationalDerivedPullback_existsUnique l E g).exists.choose.obj P.obj.2).obj)
  rw [hobj P.obj.1.unop, hobj P.obj.2]
  exact integral_pair_permitted l E g (integralPairOfRationalHomPair l E Y P)

/-- The rational permitted-pair functor acts on all localized arrows.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
def rationalPair : (constructibleRationalHomPairs l E Y).FullSubcategory ⥤
    (constructibleRationalHomPairs l E X).FullSubcategory :=
  (constructibleRationalHomPairs l E X).lift
    ((constructibleRationalHomPairs l E Y).ι ⋙
      (rationalDerivedPullback l E g).op.prod (rationalDerivedPullback l E g))
    (rational_pair_permitted l E g)

/-- The rational component and inverse are exactly the localized integral ones.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
def IsRationalNormalized
    (α : constructibleIntegralHom l E Y ⋙ constructibleIntegralPullback l E g ≅
      integralPair l E g ⋙ constructibleIntegralHom l E X)
    (β : rationalDerivedInternalHom l E Y ⋙ rationalDerivedPullback l E g ≅
      rationalPair l E g ⋙ rationalDerivedInternalHom l E X) : Prop :=
  ∀ P : (constructibleRationalHomPairs l E Y).FullSubcategory,
    HEq (β.hom.app P) ((sfRationalConstructibleLocalization l E X).map
      (α.hom.app (integralPairOfRationalHomPair l E Y P))) ∧
    HEq (β.inv.app P) ((sfRationalConstructibleLocalization l E X).map
      (α.inv.app (integralPairOfRationalHomPair l E Y P)))

section RationalComparisonProof

attribute [local irreducible] rationalDerivedPullback rationalDerivedInternalHom
  constructibleIntegralHom constructibleIntegralPullback

private theorem localized_chosen_spec {T : Sort*} {P : T → Prop} (h : ∃! t, P t)
    (t : T) (ht : t = h.exists.choose) : P t := ht.symm ▸ h.exists.choose_spec

/-- Raw localization gives a unique comparison natural for arbitrary localized arrows.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent).
Proof (node Steps 10--12): tensor the integral component and its inverse with one.
Both operation functors have their recorded object formulas. Naturality is integral
naturality multiplied by lambda*nu on pure tensors; bilinearity extends it to every
finite sum, including arrows with no integral lift. Evaluation is bilinear and
transposition linear, so their equations extend in the same way. Composition,
inverse, identity and both signed shift equations localize with their original
comparisons. No idempotents are introduced. The prescribed components give uniqueness. -/
theorem rational_comparison_existsUnique
    (α : constructibleIntegralHom l E Y ⋙ constructibleIntegralPullback l E g ≅
      integralPair l E g ⋙ constructibleIntegralHom l E X) :
    ∃! β : rationalDerivedInternalHom l E Y ⋙ rationalDerivedPullback l E g ≅
      rationalPair l E g ⋙ rationalDerivedInternalHom l E X,
      IsRationalNormalized l E g α β := by
  let R := Padic.coefficientExtensionIntegers l E
  let t := Padic.coefficientExtensionUniformizer l E
  let F := rationalDerivedPullback l E g
  let F₀ := constructibleIntegralPullback l E g
  let HY := rationalDerivedInternalHom l E Y
  let HX := rationalDerivedInternalHom l E X
  let IY := constructibleIntegralHom l E Y
  let IX := constructibleIntegralHom l E X
  have hF : ∀ K, F.obj K = ⟨F₀.obj K.obj⟩ := by
    unfold F rationalDerivedPullback
    exact (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.1
  have mF (K N : sfIntegralConstructibleCategory l E Y) (f : K ⟶ N)
      (a : Localization.Away t) :
      HEq (F.map (a ⊗ₜ[R] f : ScalarLocalization.mk K ⟶ ScalarLocalization.mk N))
        (a ⊗ₜ[R] F₀.map f) := by
    unfold F rationalDerivedPullback
    exact (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.2 K N f a
  have : F.Additive := by
    unfold F rationalDerivedPullback
    exact (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.1
  have specY := localized_chosen_spec (rationalDerivedInternalHom_existsUnique l E Y)
    HY (by unfold HY rationalDerivedInternalHom; rfl)
  have specX := localized_chosen_spec (rationalDerivedInternalHom_existsUnique l E X)
    HX (by unfold HX rationalDerivedInternalHom; rfl)
  exact ScalarLocalization.pullbackPairIso_existsUnique t
    (constructibleIntegralHomPairs l E Y) (constructibleRationalHomPairs l E Y)
    (constructibleIntegralHomPairs l E X) (constructibleRationalHomPairs l E X)
    (fun _ h ↦ h) (fun _ h ↦ h) (fun A ↦ A.property)
    F₀ F hF mF IY IX HY HX specY.1 specX.1 specY.2 specX.2
    (integral_pair_permitted l E g) (rational_pair_permitted l E g) α
end RationalComparisonProof

private theorem integral_normalized_component
    (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
    (hA : PodCompletionReindex.Laws l E g A)
    (hT : PodCompletedTensorReindex.Laws l E g A T)
    (c : PodCompletedReflection.Comparison l E g)
    (α : constructibleIntegralHom l E Y ⋙ constructibleIntegralPullback l E g ≅
      integralPair l E g ⋙ constructibleIntegralHom l E X)
    (hα : IsIntegralNormalized l E g A c α)
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) :
    α.hom.app P = integralTranspose l E X ((integralPair l E g).obj P)
      ((constructibleIntegralPullback l E g).obj ((constructibleIntegralHom l E Y).obj P))
      ((canonicalIntegralPullbackTensor l E g P.obj.1.unop
        ((constructibleIntegralHom l E Y).obj P)).inv ≫
          (constructibleIntegralPullback l E g).map (integralEvaluation l E Y P)) := by
  let F := podOrdinaryReindex l E g
  let G := integralDerivedPullback l E g
  let H := integralDerivedInternalHom l E X
  let κ := podOrdinaryToCompleted l E g A
  let M := P.obj.1.unop
  let N := P.obj.2
  let L := (constructibleIntegralHom l E Y).obj P
  let e : (integralCompletedTensor l E Y).obj (M.obj, L.obj) ⟶ N.obj :=
    (integralEvaluation l E Y P).hom
  let O (K : sfIntegralConstructibleCategory l E Y) :
      sfIntegralConstructibleCategory l E X := ⟨F.obj K.obj, T.constructible K⟩
  let C := constructibleIntegralPullback l E g
  let k (K : sfIntegralConstructibleCategory l E Y) : O K ⟶ C.obj K :=
    ObjectProperty.homMk (κ.app K.obj)
  let b := (canonicalIntegralPullbackTensor l E g M L).inv ≫
    C.map (integralEvaluation l E Y P)
  let β := integralTranspose l E X ((integralPair l E g).obj P) (C.obj L) b
  have hκ (K : sfIntegralConstructibleCategory l E Y) : IsIso (κ.app K.obj) :=
    completionUnit_isIso l E g A hA K
  have hinv : (integralCompletedTensor l E X).map
        (Prod.mkHom (κ.app M.obj) (κ.app L.obj)) ≫
          (canonicalIntegralPullbackTensor l E g M L).inv.hom =
      (T.tensor M L).inv ≫ κ.app ((integralCompletedTensor l E Y).obj (M.obj, L.obj)) := by
    apply (cancel_epi (T.tensor M L).hom).1
    erw [Iso.hom_inv_id_assoc]
    erw [← Category.assoc, ← hT.2.2.2.2.2 M L]
    have he := congrArg (fun f ↦ f.hom)
      (canonicalIntegralPullbackTensor l E g M L).hom_inv_id
    change (canonicalIntegralPullbackTensor l E g M L).hom.hom ≫
      (canonicalIntegralPullbackTensor l E g M L).inv.hom = 𝟙 _ at he
    exact (Category.assoc _ _ _).trans
      ((congrArg (κ.app ((integralCompletedTensor l E Y).obj (M.obj, L.obj)) ≫ ·)
        he).trans (Category.comp_id _))
  have hb : (integralCompletedTensor l E X).map
        (Prod.mkHom (κ.app M.obj) (κ.app L.obj)) ≫ b.hom =
      (T.tensor M L).inv ≫ F.map e ≫ κ.app N.obj := by
    change _ ≫ ((canonicalIntegralPullbackTensor l E g M L).inv.hom ≫
      G.map e) = _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ G.map e) hinv).trans
        ((Category.assoc _ _ _).trans
          (congrArg ((T.tensor M L).inv ≫ ·)
            (κ.naturality e).symm)))
  have hn := (PodCompletedReflection.reflection_laws l E X).2.1
    (C.obj M) (O M) (C.obj L) (O L) (C.obj N) (C.obj N)
    (k M) (k L) (𝟙 _) b.hom
  have hn' := (PodCompletedReflection.reflection_laws l E X).2.1
    (O M) (O M) (O L) (O L) (O N) (C.obj N)
    (𝟙 _) (𝟙 _) (k N)
    ((T.tensor M L).inv ≫ F.map e)
  have ht := (PodCompletedReflection.reindexing_laws l E g A T hA hT c).2.2.2.1
    M L N e
  have he : PodCompletedReflection.transpose l E Y M L N
      e = 𝟙 _ :=
    (PodCompletedReflection.transpose l E Y M L N).apply_symm_apply (𝟙 _)
  change _ = κ.app L.obj ≫ β.hom ≫
    H.map (Prod.mkHom (κ.app M.obj).op (𝟙 _)) at hn
  dsimp only [ObjectProperty.FullSubcategory.id_hom] at hn
  erw [Category.comp_id, hb] at hn
  simp only [ObjectProperty.FullSubcategory.id_hom, ← CategoryTheory.prod_id,
    Category.id_comp] at hn'
  change PodCompletedReflection.transpose l E X (O M) (O L) (C.obj N)
      ((integralCompletedTensor l E X).map (𝟙 (F.obj M.obj, F.obj L.obj)) ≫
        ((T.tensor M L).inv ≫ F.map e) ≫ κ.app N.obj) =
    PodCompletedReflection.transpose l E X (O M) (O L) (O N)
      ((T.tensor M L).inv ≫ F.map e) ≫ H.map
        (Prod.mkHom (𝟙 (F.obj M.obj)).op (κ.app N.obj)) at hn'
  erw [(integralCompletedTensor l E X).map_id, Category.id_comp] at hn'
  have hn'' := hn'.trans (congrArg
    (· ≫ H.map (Prod.mkHom (𝟙 (F.obj M.obj)).op (κ.app N.obj))) ht)
  erw [he, (podOrdinaryReindex l E g).map_id, Category.id_comp] at hn''
  erw [Category.assoc] at hn''
  have hnfinal := hn''.symm.trans hn
  apply ObjectProperty.hom_ext
  change (α.hom.app P).hom = β.hom
  have := hκ L
  have := hκ M
  let d := H.mapIso ((asIso (κ.app M.obj)).op.prod (Iso.refl (G.obj N.obj)))
  apply (cancel_epi (κ.app L.obj)).1
  apply (cancel_mono d.hom).1
  exact (Category.assoc _ _ _).trans
    (((hα P).trans hnfinal).trans (Category.assoc _ _ _).symm)

/-- The normalized integral comparison is independent of its resolution presentation.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent).
Proof (node Steps 8--9): completion-unit tensor compatibility and transpose
naturality identify every normalized component with the transpose of pulled-back
evaluation. Cancel the invertible kappa maps in IsIntegralNormalized. This formula
is independent of the chosen completion presentation, so componentwise equality
gives uniqueness. Existence is integral_comparison_existsUnique applied to the
coherent family supplied by completed-evaluation reflection. -/
theorem integral_existsUnique :
    ∃! α : constructibleIntegralHom l E Y ⋙ constructibleIntegralPullback l E g ≅
      integralPair l E g ⋙ constructibleIntegralHom l E X,
      ∃ (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
        (c : PodCompletedReflection.Comparison l E g),
        PodCompletionReindex.Laws l E g A ∧
        PodCompletedTensorReindex.Laws l E g A T ∧ IsIntegralNormalized l E g A c α := by
  obtain ⟨A, _, _, _, hA⟩ :=
    PodCompletedReflection.podReindexingCompletedEvaluationReflection l E
  obtain ⟨hD, hT, _, _, c, _⟩ := hA g
  obtain ⟨α, hα, _⟩ := integral_comparison_existsUnique l E g
    (A.completion g) (A.tensor g) hD hT c
  refine ⟨α, ⟨A.completion g, A.tensor g, c, hD, hT, hα⟩, ?_⟩
  intro β hβ
  obtain ⟨B, U, d, hB, hU, hβ⟩ := hβ
  apply Iso.ext
  apply NatTrans.ext
  funext P
  exact (integral_normalized_component l E g B U hB hU d β hβ P).trans
    (integral_normalized_component l E g (A.completion g) (A.tensor g) hD hT c α hα P).symm

/-- The unique comparison fixed by ambient evaluation and the specified kappa maps.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
def integralComparison := (integral_existsUnique l E g).exists.choose

/-- The unique raw rational extension of the specified integral comparison.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
def rationalComparison :=
  (rational_comparison_existsUnique l E g (integralComparison l E g)).exists.choose

/-- Naturality includes every pair of localized arrows, not only integral lifts.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent).
Proof (node Step 11): apply naturality of the hom of rationalComparison to
the permitted-pair arrow (a.op, b). The domain is full, so this includes every
localized arrow without choosing an integral lift or a tensor expression. -/
theorem rational_naturality
    (P Q : (constructibleRationalHomPairs l E Y).FullSubcategory)
    (a : Q.obj.1.unop ⟶ P.obj.1.unop) (b : P.obj.2 ⟶ Q.obj.2) :
    (rationalDerivedPullback l E g).map
        ((rationalDerivedInternalHom l E Y).map
          (ObjectProperty.homMk (X := P) (Y := Q) (Prod.mkHom a.op b))) ≫
      (rationalComparison l E g).hom.app Q =
    (rationalComparison l E g).hom.app P ≫
      (rationalDerivedInternalHom l E X).map
        ((rationalPair l E g).map
          (ObjectProperty.homMk (X := P) (Y := Q) (Prod.mkHom a.op b))) := by
  exact (rationalComparison l E g).hom.naturality
    (ObjectProperty.homMk (X := P) (Y := Q) (Prod.mkHom a.op b))

/-- The specified comparisons commute with the specified completed scalar comparisons.
The two input scalar/pullback comparisons occur with their required variances.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent).
Proof (node Steps 4--9): transpose the ambient scalar square in the S_X category,
then use the specified Hom evaluation pin, the tensor completion-unit square and
the alpha/kappa scalar square. Cancel completion units by reflector injectivity.
Fullness gives the displayed equation in the constructible integral category. -/
theorem integral_scalar
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) :
    HEq
      ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).map
          ((integralComparison l E g).hom.app P) ≫
        (integralHomScalarComparison l E L ι X ((integralPair l E g).obj P)).hom)
      ((integralPullbackScalarComparison l E L ι g
          ((constructibleIntegralHom l E Y).obj P)).hom ≫
        (constructibleIntegralPullback l L g).map
          (integralHomScalarComparison l E L ι Y P).hom ≫
        (integralComparison l L g).hom.app (integralHomScalarPair l E L ι Y P) ≫
        ObjectProperty.homMk
          (X := (constructibleIntegralHom l L X).obj
            ((integralPair l L g).obj (integralHomScalarPair l E L ι Y P)))
          (Y := (constructibleIntegralHom l L X).obj
            (integralHomScalarPair l E L ι X ((integralPair l E g).obj P)))
          ((integralDerivedInternalHom l L X).map (Prod.mkHom
            ((integralPullbackScalarComparison l E L ι g P.obj.1.unop).hom.hom).op
            ((integralPullbackScalarComparison l E L ι g P.obj.2).inv.hom)))) := by
  sorry

section RationalScalarProof
variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private theorem functor_map_heq {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B A' B' : C} (ha : A = A') (hb : B = B') {f : A ⟶ B} {f' : A' ⟶ B'}
    (h : HEq f f') : HEq (F.map f) (F.map f') := by
  cases ha
  cases hb
  cases h
  rfl

private theorem dep_heq {α : Sort*} {β : α → Sort*} (f : ∀ a, β a) {a a' : α}
    (h : a = a') : HEq (f a) (f a') := by
  cases h
  rfl

private theorem iso_inv_heq {C : Type*} [Category* C] {A B A' B' : C}
    (e : A ≅ B) (e' : A' ≅ B') (ha : A = A') (hb : B = B') (h : HEq e.hom e'.hom) :
    HEq e.inv e'.inv := by
  cases ha
  cases hb
  rw [Iso.ext (eq_of_heq h)]

/-- The rational Hom functor on a pair arrow with integral representatives.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
private theorem rationalHom_map_heq (K : Type u) [Field K] [Algebra ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] (W : Scheme.{u})
    (P P' : (constructibleRationalHomPairs l K W).FullSubcategory)
    (P₀ P₀' : (constructibleIntegralHomPairs l K W).FullSubcategory)
    (hP : integralPairOfRationalHomPair l K W P = P₀)
    (hP' : integralPairOfRationalHomPair l K W P' = P₀')
    (a : P'.obj.1.unop ⟶ P.obj.1.unop) (b : P.obj.2 ⟶ P'.obj.2)
    (a₀ : P₀'.obj.1.unop ⟶ P₀.obj.1.unop) (b₀ : P₀.obj.2 ⟶ P₀'.obj.2)
    (ha : HEq a (TensorProduct.tmul (Padic.coefficientExtensionIntegers l K)
      (1 : Localization.Away (Padic.coefficientExtensionUniformizer l K)) a₀))
    (hb : HEq b (TensorProduct.tmul (Padic.coefficientExtensionIntegers l K)
      (1 : Localization.Away (Padic.coefficientExtensionUniformizer l K)) b₀)) :
    HEq ((rationalDerivedInternalHom l K W).map
        (ObjectProperty.homMk (X := P) (Y := P') (Prod.mkHom a.op b)))
      ((sfRationalConstructibleLocalization l K W).map
        ((constructibleIntegralHom l K W).map
          (ObjectProperty.homMk (X := P₀) (Y := P₀') (Prod.mkHom a₀.op b₀)))) := by
  subst hP hP'
  obtain ⟨β, hβ, hβ'⟩ :=
    (rationalDerivedInternalHom_existsUnique l K W).exists.choose_spec.2 P P'
  obtain rfl := eq_of_heq ha
  obtain rfl := eq_of_heq hb
  have e := congrArg (fun c : Localization.Away (Padic.coefficientExtensionUniformizer l K) ↦
    c ⊗ₜ[Padic.coefficientExtensionIntegers l K] ((constructibleIntegralHom l K W).map
      (ObjectProperty.homMk (X := integralPairOfRationalHomPair l K W P)
        (Y := integralPairOfRationalHomPair l K W P') (Prod.mkHom a₀.op b₀)))) (one_mul 1)
  exact ((heq_of_eq (hβ _ _)).trans (hβ' a₀ b₀ 1 1)).trans (heq_of_eq e)

/-- The localized form of integral_scalar: the specified rational comparisons commute
with the specified rational scalar comparisons.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent).
Proof: every arrow is the localization of its integral counterpart; apply the
localization functor to integral_scalar. -/
theorem rational_scalar (P : (constructibleRationalHomPairs l E Y).FullSubcategory) :
    (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
        ((rationalComparison l E g).hom.app P) ≫
      (rationalHomScalarComparison l E L ι X ((rationalPair l E g).obj P)).hom =
    (rationalPullbackScalarComparison l E L ι g).hom.app
        ((rationalDerivedInternalHom l E Y).obj P) ≫
      (rationalDerivedPullback l L g).map (rationalHomScalarComparison l E L ι Y P).hom ≫
      (rationalComparison l L g).hom.app (rationalHomScalarPair l E L ι Y P) ≫
      (rationalDerivedInternalHom l L X).map (ObjectProperty.homMk
        (X := (rationalPair l L g).obj (rationalHomScalarPair l E L ι Y P))
        (Y := rationalHomScalarPair l E L ι X ((rationalPair l E g).obj P))
        (Prod.mkHom ((rationalPullbackScalarComparison l E L ι g).hom.app P.obj.1.unop).op
          ((rationalPullbackScalarComparison l E L ι g).inv.app P.obj.2))) := by
  let IP := integralPairOfRationalHomPair l E Y P
  let QL (W : Scheme.{u}) := sfRationalConstructibleLocalization l L W
  let S (W : Scheme.{u}) := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  have hr (K : Type u) [Field K] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
      (A : sfRationalConstructibleCategory l K Y) :
      (rationalDerivedPullback l K g).obj A =
        ⟨(constructibleIntegralPullback l K g).obj A.obj⟩ :=
    (rationalDerivedPullback_existsUnique l K g).exists.choose_spec.2.1 A
  have hH (K : Type u) [Field K] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
      (W : Scheme.{u}) (A : (constructibleRationalHomPairs l K W).FullSubcategory) :
      (rationalDerivedInternalHom l K W).obj A =
        ⟨(constructibleIntegralHom l K W).obj (integralPairOfRationalHomPair l K W A)⟩ :=
    (rationalDerivedInternalHom_existsUnique l K W).exists.choose_spec.1 A
  have hs (W : Scheme.{u}) (A : sfRationalConstructibleCategory l E W) :
      (sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj A =
        ⟨(S W).obj A.obj⟩ :=
    sfRationalScalarExtension_obj l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι A
  have mr {A B : sfIntegralConstructibleCategory l L Y} (a : A ⟶ B) :
      HEq ((rationalDerivedPullback l L g).map
          ((sfRationalConstructibleLocalization l L Y).map a))
        ((QL X).map ((constructibleIntegralPullback l L g).map a)) :=
    (rationalDerivedPullback_existsUnique l L g).exists.choose_spec.2.2 A B a 1
  have ms (W : Scheme.{u}) {A B : sfIntegralConstructibleCategory l E W} (a : A ⟶ B) :
      HEq ((sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
          ((sfRationalConstructibleLocalization l E W).map a))
        ((QL W).map ((S W).map a)) := by
    have h := sfRationalScalarExtension_map_tmul l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι A B a 1
    simp only [map_one] at h
    exact h
  have hβ (K : Type u) [Field K] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
      (A : (constructibleRationalHomPairs l K Y).FullSubcategory) :
      HEq ((rationalComparison l K g).hom.app A)
        ((sfRationalConstructibleLocalization l K X).map
          ((integralComparison l K g).hom.app (integralPairOfRationalHomPair l K Y A))) :=
    ((rational_comparison_existsUnique l K g
      (integralComparison l K g)).exists.choose_spec A).1
  have hρ (A : sfRationalConstructibleCategory l E Y) :
      HEq ((rationalPullbackScalarComparison l E L ι g).hom.app A)
        ((QL X).map (integralPullbackScalarComparison l E L ι g A.obj).hom) :=
    (rationalPullbackScalarComparison_existsUnique l E L ι g).exists.choose_spec A
  have hh (W : Scheme.{u}) (A : (constructibleRationalHomPairs l E W).FullSubcategory) :
      HEq (rationalHomScalarComparison l E L ι W A).hom
        ((QL W).map (integralHomScalarComparison l E L ι W
          (integralPairOfRationalHomPair l E W A)).hom) :=
    (rationalHomScalarComparison_existsUnique l E L ι W A).exists.choose_spec
  -- The integral pairs underlying the four rational pairs.
  have pe1 : integralPairOfRationalHomPair l E X ((rationalPair l E g).obj P) =
      (integralPair l E g).obj IP := by
    apply ObjectProperty.FullSubcategory.ext
    change (op ((rationalDerivedPullback l E g).obj P.obj.1.unop).obj,
      ((rationalDerivedPullback l E g).obj P.obj.2).obj) = _
    rw [hr, hr]
    rfl
  have pe2 : integralPairOfRationalHomPair l L Y (rationalHomScalarPair l E L ι Y P) =
      integralHomScalarPair l E L ι Y IP := by
    apply ObjectProperty.FullSubcategory.ext
    change (op ((sfRationalScalarExtension l E Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.1.unop).obj,
      ((sfRationalScalarExtension l E Y 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.2).obj) = _
    rw [hs, hs]
    rfl
  have pe3 : integralPairOfRationalHomPair l L X
      ((rationalPair l L g).obj (rationalHomScalarPair l E L ι Y P)) =
      (integralPair l L g).obj (integralHomScalarPair l E L ι Y IP) := by
    apply ObjectProperty.FullSubcategory.ext
    change (op ((rationalDerivedPullback l L g).obj
        ((sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.1.unop)).obj,
      ((rationalDerivedPullback l L g).obj ((sfRationalScalarExtension l E Y 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.2)).obj) = _
    rw [hr, hr, hs, hs]
    rfl
  have pe4 : integralPairOfRationalHomPair l L X
      (rationalHomScalarPair l E L ι X ((rationalPair l E g).obj P)) =
      integralHomScalarPair l E L ι X ((integralPair l E g).obj IP) := by
    apply ObjectProperty.FullSubcategory.ext
    change (op ((sfRationalScalarExtension l E X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
          ((rationalDerivedPullback l E g).obj P.obj.1.unop)).obj,
      ((sfRationalScalarExtension l E X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
          ((rationalDerivedPullback l E g).obj P.obj.2)).obj) = _
    rw [hs, hs, hr, hr]
    rfl
  -- The six vertices.
  have o1 : (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
      ((rationalDerivedPullback l E g).obj ((rationalDerivedInternalHom l E Y).obj P)) =
      (QL X).obj ((S X).obj ((constructibleIntegralPullback l E g).obj
        ((constructibleIntegralHom l E Y).obj IP))) := by
    rw [hs, hr, hH]
    rfl
  have o2 : (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
      ((rationalDerivedInternalHom l E X).obj ((rationalPair l E g).obj P)) =
      (QL X).obj ((S X).obj ((constructibleIntegralHom l E X).obj
        ((integralPair l E g).obj IP))) := by
    rw [hs, hH, pe1]
    rfl
  have o3 : (rationalDerivedInternalHom l L X).obj
      (rationalHomScalarPair l E L ι X ((rationalPair l E g).obj P)) =
      (QL X).obj ((constructibleIntegralHom l L X).obj
        (integralHomScalarPair l E L ι X ((integralPair l E g).obj IP))) := by
    rw [hH, pe4]
    rfl
  have o4 : (rationalDerivedPullback l L g).obj
      ((sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
        ((rationalDerivedInternalHom l E Y).obj P)) =
      (QL X).obj ((constructibleIntegralPullback l L g).obj
        ((S Y).obj ((constructibleIntegralHom l E Y).obj IP))) := by
    rw [hr, hs, hH]
    rfl
  have o5 : (rationalDerivedPullback l L g).obj
      ((rationalDerivedInternalHom l L Y).obj (rationalHomScalarPair l E L ι Y P)) =
      (QL X).obj ((constructibleIntegralPullback l L g).obj
        ((constructibleIntegralHom l L Y).obj (integralHomScalarPair l E L ι Y IP))) := by
    rw [hr, hH, pe2]
    rfl
  have o6 : (rationalDerivedInternalHom l L X).obj
      ((rationalPair l L g).obj (rationalHomScalarPair l E L ι Y P)) =
      (QL X).obj ((constructibleIntegralHom l L X).obj
        ((integralPair l L g).obj (integralHomScalarPair l E L ι Y IP))) := by
    rw [hH, pe3]
    rfl
  -- The six arrows are localizations of the integral arrows.
  have oa : (rationalDerivedPullback l E g).obj ((rationalDerivedInternalHom l E Y).obj P) =
      (sfRationalConstructibleLocalization l E X).obj ((constructibleIntegralPullback l E g).obj
        ((constructibleIntegralHom l E Y).obj IP)) := by
    rw [hr, hH]
    rfl
  have ob : (rationalDerivedInternalHom l E X).obj ((rationalPair l E g).obj P) =
      (sfRationalConstructibleLocalization l E X).obj ((constructibleIntegralHom l E X).obj
        ((integralPair l E g).obj IP)) := by
    rw [hH, pe1]
    rfl
  have h1 := (functor_map_heq
    (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι)
    oa ob (hβ E P)).trans (ms X ((integralComparison l E g).hom.app IP))
  have h2 := (hh X ((rationalPair l E g).obj P)).trans
    (functor_map_heq (QL X) (by rw [pe1]) (by rw [pe1])
      (dep_heq (fun A ↦ (integralHomScalarComparison l E L ι X A).hom) pe1))
  have hHobj : ((rationalDerivedInternalHom l E Y).obj P).obj =
      (constructibleIntegralHom l E Y).obj IP := by
    rw [hH]
  have h3 := (hρ ((rationalDerivedInternalHom l E Y).obj P)).trans
    (functor_map_heq (QL X) (by rw [hHobj]) (by rw [hHobj])
      (dep_heq (fun A ↦ (integralPullbackScalarComparison l E L ι g A).hom) hHobj))
  have oc : (sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
      ((rationalDerivedInternalHom l E Y).obj P) =
      (sfRationalConstructibleLocalization l L Y).obj ((S Y).obj
        ((constructibleIntegralHom l E Y).obj IP)) := by
    rw [hs, hH]
    rfl
  have od : (rationalDerivedInternalHom l L Y).obj (rationalHomScalarPair l E L ι Y P) =
      (sfRationalConstructibleLocalization l L Y).obj ((constructibleIntegralHom l L Y).obj
        (integralHomScalarPair l E L ι Y IP)) := by
    rw [hH, pe2]
    rfl
  have h4 := (functor_map_heq (rationalDerivedPullback l L g) oc od (hh Y P)).trans
    (mr (integralHomScalarComparison l E L ι Y IP).hom)
  have h5 := (hβ L (rationalHomScalarPair l E L ι Y P)).trans
    (functor_map_heq (QL X) (by rw [pe2]) (by rw [pe2])
      (dep_heq (fun A ↦ (integralComparison l L g).hom.app A) pe2))
  have ha := (hρ P.obj.1.unop).trans (HEq.rfl :
    HEq ((QL X).map (integralPullbackScalarComparison l E L ι g P.obj.1.unop.obj).hom)
      (TensorProduct.tmul (Padic.coefficientExtensionIntegers l L)
        (1 : Localization.Away (Padic.coefficientExtensionUniformizer l L))
          (integralPullbackScalarComparison l E L ι g P.obj.1.unop.obj).hom))
  have oe : (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
      ((rationalDerivedPullback l E g).obj P.obj.2) =
      (QL X).obj ((S X).obj ((constructibleIntegralPullback l E g).obj P.obj.2.obj)) := by
    rw [hs, hr]
    rfl
  have of : (rationalDerivedPullback l L g).obj
      ((sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
        P.obj.2) =
      (QL X).obj ((constructibleIntegralPullback l L g).obj ((S Y).obj P.obj.2.obj)) := by
    rw [hr, hs]
    rfl
  have hb := (iso_inv_heq ((rationalPullbackScalarComparison l E L ι g).app P.obj.2)
    ((QL X).mapIso (integralPullbackScalarComparison l E L ι g P.obj.2.obj))
    oe of (hρ P.obj.2)).trans (HEq.rfl :
    HEq ((QL X).map (integralPullbackScalarComparison l E L ι g P.obj.2.obj).inv)
      (TensorProduct.tmul (Padic.coefficientExtensionIntegers l L)
        (1 : Localization.Away (Padic.coefficientExtensionUniformizer l L))
          (integralPullbackScalarComparison l E L ι g P.obj.2.obj).inv))
  have h6 := rationalHom_map_heq l L X
    ((rationalPair l L g).obj (rationalHomScalarPair l E L ι Y P))
    (rationalHomScalarPair l E L ι X ((rationalPair l E g).obj P))
    ((integralPair l L g).obj (integralHomScalarPair l E L ι Y IP))
    (integralHomScalarPair l E L ι X ((integralPair l E g).obj IP)) pe3 pe4
    ((rationalPullbackScalarComparison l E L ι g).hom.app P.obj.1.unop)
    ((rationalPullbackScalarComparison l E L ι g).inv.app P.obj.2)
    (integralPullbackScalarComparison l E L ι g P.obj.1.unop.obj).hom
    (integralPullbackScalarComparison l E L ι g P.obj.2.obj).inv ha hb
  have hI := congrArg (QL X).map (eq_of_heq (integral_scalar l E g L ι IP))
  simp only [Functor.map_comp] at hI
  apply eq_of_heq
  refine (heq_comp o1 o2 o3 h1 h2).trans ((heq_of_eq hI).trans ?_)
  exact (heq_comp o1 o4 o3 h3 (heq_comp o4 o5 o3 h4 (heq_comp o5 o6 o3 h5 h6))).symm

end RationalScalarProof

/-- The rational pullback shift is the localization of the termwise reindexing shift,
conjugated only by the specified ordinary-to-completed pullback maps.
Source: blueprint Step 5; Stacks 011G, 099B
(blueprint: lem-pod-reindexing-hom-coefficient-descent).
Proof (node Steps 9--12): exact reindexing shifts termwise with identity degree maps.
The normalized Roos comparison carries the second product coordinate with its
specified sign. The completed reflection comparison intertwines these shifts.
Restrict by fullness, then localize. Every component is prescribed by the
invertible kappa and localization, so the full shift structure is unique. -/
theorem rational_pullbackShift_existsUnique :
    ∃! s : (rationalDerivedPullback l E g).CommShift ℤ,
      ∃ (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
        (d : (constructibleIntegralPullback l E g).CommShift ℤ),
        PodCompletionReindex.Laws l E g A ∧
        PodCompletedTensorReindex.Laws l E g A T ∧
        (∀ (K : sfIntegralConstructibleCategory l E Y) (r : ℤ),
          HEq ((podOrdinaryToCompleted l E g A).app (K⟦r⟧).obj ≫
            (((constructibleIntegralPullback l E g).commShiftIso
              (self := d) r).hom.app K).hom)
            (((podOrdinaryReindex l E g).commShiftIso r).hom.app K.obj ≫
              ((podOrdinaryToCompleted l E g A).app K.obj)⟦r⟧')) ∧
        ∀ (K : sfRationalConstructibleCategory l E Y) (r : ℤ),
          HEq (((rationalDerivedPullback l E g).commShiftIso
              (self := s) r).hom.app K)
            ((sfRationalConstructibleLocalization l E X).map
              (((constructibleIntegralPullback l E g).commShiftIso
                (self := d) r).hom.app K.obj)) := by
  sorry

/-- The uniquely specified rational pullback shift, with its original Roos sign.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
@[instance_reducible]
def rationalPullbackShift := (rational_pullbackShift_existsUnique l E g).exists.choose

end Reindex

attribute [local irreducible] rationalComparison integralComparison rationalTranspose
  rationalEvaluation rationalPullbackShift integralSignedShift

attribute [local irreducible] commonStageDerivedPullback commonStageDerivedTensor
  commonStageDerivedInternalHom

attribute [local irreducible] ObjectProperty.FullSubcategory.category

section CommonStage
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)
variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The recorded common-stage pullback in its literally specified object coordinates.
Only equality transport is used, preserving the prescribed representative maps.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
def commonPullback := (commonStageDerivedPullback l Ω g).copyObj
  (commonStagePullbackObject l Ω g)
  (fun P ↦ eqToIso ((podCommonStageObjectNormalizations l Ω).1 g P))

/-- The recorded common-stage Hom in its literally specified compositum coordinates.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
def commonHom (W : Scheme.{u}) := (commonStageDerivedInternalHom l Ω W).copyObj
  (commonStageHomObject l Ω W)
  (fun P ↦ eqToIso ((podCommonStageObjectNormalizations l Ω).2.2 W P))

/-- The recorded tensor in its literal compositum coordinates, by equality transport.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
def commonTensor (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :=
  (commonStageDerivedTensor l Ω W).copyObj
    (fun P ↦ commonStageTensorObject l Ω W P.1 P.2)
    (fun P ↦ eqToIso ((podCommonStageObjectNormalizations l Ω).2.1 W P.1 P.2))

attribute [local irreducible]
  commonStagePullbackComparison commonStageHomComparison commonStageTensorComparison
  operationStageTransitionIso

private theorem commonPullback_eq : commonPullback l Ω g = commonStageDerivedPullback l Ω g :=
  copyObj_eq _ _
    ((podCommonStageObjectNormalizations l Ω).1 g)

/-- Evaluation at every common field, with the fixed Hom and tensor comparisons.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent).
Proof (node Steps 13--14): at a common coefficient stage evaluate after the two
specified scalar comparisons. rational_scalar and the tensor tower square identify
this representative at any larger field. The common-stage equality criterion gives
a class independent of representatives. Every arrow has a representative, hence
this prescription fixes the evaluation class uniquely. -/
theorem common_evaluation_existsUnique (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (P : (commonStageHomPairs l Ω W).FullSubcategory) :
    ∃! e : (commonTensor l Ω W).obj (P.obj.1.unop, (commonHom l Ω W).obj P) ⟶ P.obj.2,
      ∀ (L : Index l Ω)
        (h : (commonStageTensorObject l Ω W P.obj.1.unop
          (commonStageHomObject l Ω W P)).stage ≤ L)
        (hH : (commonStageHomObject l Ω W P).stage ≤ L)
        (hN : P.obj.2.stage ≤ L),
        HEq e (ofHom
          (commonStageTensorObject l Ω W P.obj.1.unop (commonStageHomObject l Ω W P))
          P.obj.2 L h hN
          ((commonStageTensorComparison l Ω W P.obj.1.unop
              (commonStageHomObject l Ω W P) L h).hom ≫
            (rationalDerivedTensor l (Coefficient.{u} l Ω L) W).map
              (Prod.mkHom (𝟙 _) (commonStageHomComparison l Ω W P L hH).hom) ≫
            rationalEvaluation l (Coefficient.{u} l Ω L) W
              (commonStageHomPairAtStage l Ω W P L hH))) := by
  sorry

/-- The class of the specified rational evaluation at any common coefficient field.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
def commonEvaluation (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (P : (commonStageHomPairs l Ω W).FullSubcategory) :=
  (common_evaluation_existsUnique l Ω W P).exists.choose

section CommonPairProof

private theorem stageIntegralObject (W : Scheme.{u})
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : Index l Ω) (h : P.stage ≤ L) :
    (P.toStage h).obj =
      (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime))
        (Coefficient.{u} l Ω P.stage) (Coefficient.{u} l Ω L)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω P.stage L h) W).obj
          P.obj.obj := by
  change (((stageSystem l Ω W).T h).obj P.obj).obj = _
  have ht : (stageSystem l Ω W).T h = transition l Ω W P.stage L h := by
    simpa only [stageSystem] using
      (stageSystem_existsUnique l Ω W).exists.choose_spec.1 P.stage L h
  have hi := sfRationalScalarExtension_obj l (Coefficient.{u} l Ω P.stage) W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω P.stage L h) P.obj
  exact (congrArg (fun F : Stage l Ω W P.stage ⥤ Stage l Ω W L ↦
    (F.obj P.obj).obj) ht).trans (congrArg ScalarLocalization.obj hi)

private def stagePullbackIntegralIso
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (L : Index l Ω) (h : P.stage ≤ L) :
    ((commonStagePullbackObject l Ω g P).toStage h).obj ≅
      (constructibleIntegralPullback l (Coefficient.{u} l Ω L) g).obj (P.toStage h).obj :=
  eqToIso (stageIntegralObject l Ω X (commonStagePullbackObject l Ω g P) L h) ≪≫
    (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime))
      (Coefficient.{u} l Ω P.stage) (Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω P.stage L h) X).mapIso
        (eqToIso (congrArg ScalarLocalization.obj
          ((rationalDerivedPullback_existsUnique l
            (Coefficient.{u} l Ω P.stage) g).exists.choose_spec.2.1 P.obj))) ≪≫
    integralPullbackScalarComparison l (Coefficient.{u} l Ω P.stage)
      (Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω P.stage L h) g P.obj.obj ≪≫
    (constructibleIntegralPullback l (Coefficient.{u} l Ω L) g).mapIso
      (eqToIso (stageIntegralObject l Ω Y P L h).symm)

/-- The specified common-stage pullback preserves the permitted Hom domain.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent).
Proof (node Steps 13--14): represent the two objects at their compositum and apply
integral_pair_permitted to the underlying integral pair. The rational scalar object
formula and the pullback/scalar comparison identify both pulled-back stage objects
with integral pullbacks. Apply internal Hom with its contravariant first argument,
then transport constructibility through this isomorphism. -/
theorem common_pair_permitted
    (P : (commonStageHomPairs l Ω Y).FullSubcategory) :
    commonStageHomPairs l Ω X
      (op ((commonPullback l Ω g).obj P.obj.1.unop),
        (commonPullback l Ω g).obj P.obj.2) := by
  let M := P.obj.1.unop
  let N := P.obj.2
  let L := Padic.finiteCoefficientCompositum l Ω M.stage N.stage
  have hL := (Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage
  let A := Coefficient.{u} l Ω L
  have hP := integral_pair_permitted l A g
    (integralPairOfRationalHomPair l A Y (commonStageHomRationalPair l Ω Y P))
  let eM := stagePullbackIntegralIso l Ω g M L hL.1
  let eN := stagePullbackIntegralIso l Ω g N L hL.2
  let e := (integralDerivedInternalHom l A X).mapIso
    (((sfIntegralConstructible l A X).ι.mapIso eM).op.prod
      (((sfIntegralConstructible l A X).ι.mapIso eN).symm))
  exact (sfIntegralConstructible l A X).prop_of_iso e hP

end CommonPairProof

/-- The actual common-stage permitted-pair functor, with all quotient-class arrows.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
def commonPair : (commonStageHomPairs l Ω Y).FullSubcategory ⥤
    (commonStageHomPairs l Ω X).FullSubcategory :=
  (commonStageHomPairs l Ω X).lift
    ((commonStageHomPairs l Ω Y).ι ⋙
      (commonPullback l Ω g).op.prod (commonPullback l Ω g))
    (common_pair_permitted l Ω g)

/-- Common-stage components are prescribed at every larger finite coefficient field.
Both input comparisons use the original operation normalizations and variances.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
def IsCommonNormalized
    (α : commonHom l Ω Y ⋙ commonPullback l Ω g ≅
      commonPair l Ω g ⋙ commonHom l Ω X) : Prop :=
  ∀ (P : (commonStageHomPairs l Ω Y).FullSubcategory) (L : Index l Ω)
    (h : (commonStageHomObject l Ω Y P).stage ≤ L)
    (h' : (commonStageHomObject l Ω X ((commonPair l Ω g).obj P)).stage ≤ L)
    (hM : P.obj.1.unop.stage ≤ L) (hN : P.obj.2.stage ≤ L),
    ∃ d : ((commonPullback l Ω g).obj
        ((commonHom l Ω Y).obj P)).toStage h ≅
      ((commonHom l Ω X).obj ((commonPair l Ω g).obj P)).toStage h',
      α.hom.app P = ofHom
        ((commonPullback l Ω g).obj ((commonHom l Ω Y).obj P))
        ((commonHom l Ω X).obj ((commonPair l Ω g).obj P)) L h h' d.hom ∧
      HEq d.hom
        ((commonStagePullbackComparison l Ω g (commonStageHomObject l Ω Y P) L h).hom ≫
          (rationalDerivedPullback l (Coefficient.{u} l Ω L) g).map
            (commonStageHomComparison l Ω Y P L h).hom ≫
          (rationalComparison l (Coefficient.{u} l Ω L) g).hom.app
            (commonStageHomPairAtStage l Ω Y P L h) ≫
          (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) X).map
            (ObjectProperty.homMk
              (X := (rationalPair l (Coefficient.{u} l Ω L) g).obj
                (commonStageHomPairAtStage l Ω Y P L h))
              (Y := commonStageHomPairAtStage l Ω X ((commonPair l Ω g).obj P) L h')
              (Prod.mkHom
                ((commonStagePullbackComparison l Ω g P.obj.1.unop L hM).hom).op
                (commonStagePullbackComparison l Ω g P.obj.2 L hN).inv)) ≫
          (commonStageHomComparison l Ω X ((commonPair l Ω g).obj P) L h').inv)

section CommonComparisonProof
open CommonStageInternalHom
open AlgebraicallyClosedCoefficients (coefficientInclusion)

/-- Transition conjugates by the recorded stage identification.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
private theorem stageT_map (W : Scheme.{u}) {L M : Index l Ω} (k : L ≤ M)
    {A B : Stage l Ω W L} (f : A ⟶ B) :
    ((stageSystem l Ω W).T k).map f =
      (operationStageTransitionIso l Ω W L M k).hom.app A ≫
        (transition l Ω W L M k).map f ≫
          (operationStageTransitionIso l Ω W L M k).inv.app B := by
  rw [← Category.assoc, ← (operationStageTransitionIso l Ω W L M k).hom.naturality f,
    Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- The pullback comparison at a larger stage, through the scalar pullback comparison.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
private theorem pullbackComparison_hom_eq
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (M : Index l Ω) (k : K.stage ≤ M) :
    (commonStagePullbackComparison l Ω g K M k).hom =
      (operationStageTransitionIso l Ω X K.stage M k).hom.app
          ((rationalDerivedPullback l (Coefficient.{u} l Ω K.stage) g).obj K.obj) ≫
        (rationalPullbackScalarComparison l (Coefficient.{u} l Ω K.stage)
          (Coefficient.{u} l Ω M) (coefficientInclusion l Ω K.stage M k) g).hom.app K.obj ≫
        (rationalDerivedPullback l (Coefficient.{u} l Ω M) g).map
          ((operationStageTransitionIso l Ω Y K.stage M k).inv.app K.obj) := by
  unfold commonStagePullbackComparison
  rfl

/-- Cancel the stage identification in the pullback coherence equation.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
private theorem step_algebra {C D : Type*} [Category* C] [Category* D] (R : D ⥤ C)
    {U V W W' Z₀ : C} {x y z : D} (e0 : U ≅ V) (s : V ⟶ W) (e1 : W' ≅ W)
    (ρ : W ⟶ R.obj x) (ey : x ≅ y) (ay : y ≅ z) (aX : U ⟶ Z₀) (cM : Z₀ ⟶ R.obj z)
    (hc : (e0.hom ≫ s ≫ e1.inv) ≫ (e1.hom ≫ ρ ≫ R.map ey.hom) ≫ R.map ay.hom =
      aX ≫ cM) :
    s ≫ ρ ≫ R.map (ey ≪≫ ay).hom = e0.inv ≫ aX ≫ cM := by
  rw [← hc]
  simp

/-- The pullback comparisons are compatible with one further transition.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
private theorem pullback_step (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    {L M : Index l Ω} (h : K.stage ≤ L) (k : L ≤ M) :
    (transition l Ω X L M k).map (commonStagePullbackComparison l Ω g K L h).hom ≫
      (rationalPullbackScalarComparison l (Coefficient.{u} l Ω L) (Coefficient.{u} l Ω M)
        (coefficientInclusion l Ω L M k) g).hom.app (K.toStage h) ≫
      (rationalDerivedPullback l (Coefficient.{u} l Ω M) g).map
        (inputStep l Ω Y K h k).hom =
    (operationStageTransitionIso l Ω X L M k).inv.app (((stageSystem l Ω X).T h).obj
        ((rationalDerivedPullback l (Coefficient.{u} l Ω K.stage) g).obj K.obj)) ≫
      ((stageSystem l Ω X).assoc h k).hom.app
        ((rationalDerivedPullback l (Coefficient.{u} l Ω K.stage) g).obj K.obj) ≫
      (commonStagePullbackComparison l Ω g K M (h.trans k)).hom := by
  have hd := commonStagePullback_comparison_data l Ω g
  let b := @hd.choose
  have hb := @hd.choose_spec.1
  have hcoh := @hd.choose_spec.2
  have h1 : (b h).hom.app K.obj = (commonStagePullbackComparison l Ω g K L h).hom :=
    eq_of_heq (hb h K.obj).1
  have h2 : (b (h.trans k)).hom.app K.obj =
      (commonStagePullbackComparison l Ω g K M (h.trans k)).hom :=
    eq_of_heq (hb (h.trans k) K.obj).1
  have h3 : (b k).hom.app (K.toStage h) =
      (commonStagePullbackComparison l Ω g ⟨L, K.toStage h⟩ M k).hom :=
    eq_of_heq (hb k (K.toStage h)).1
  have h3' := h3.trans (pullbackComparison_hom_eq l Ω g ⟨L, K.toStage h⟩ M k)
  have ht := (stageT_map l Ω X k
    (commonStagePullbackComparison l Ω g K L h).hom).symm.trans
      (congrArg ((stageSystem l Ω X).T k).map h1.symm)
  unfold inputStep
  refine step_algebra (rationalDerivedPullback l (Coefficient.{u} l Ω M) g)
    ((operationStageTransitionIso l Ω X L M k).app _) _
    ((operationStageTransitionIso l Ω X L M k).app _) _
    ((operationStageTransitionIso l Ω Y L M k).app (K.toStage h)).symm
    (((stageSystem l Ω Y).assoc h k).app K.obj) _ _ ?_
  exact (congrArg₂ (fun f c ↦ f ≫ c ≫
    (rationalDerivedPullback l (Coefficient.{u} l Ω M) g).map
      (((stageSystem l Ω Y).assoc h k).hom.app K.obj)) ht h3'.symm).trans
        ((hcoh h k K.obj).trans (congrArg (fun c ↦
          ((stageSystem l Ω X).assoc h k).hom.app
            ((rationalDerivedPullback l (Coefficient.{u} l Ω K.stage) g).obj K.obj) ≫ c) h2))

end CommonComparisonProof

/-- The same evaluation-normalized comparison descends uniquely to actual common-stage classes.
Source: blueprint Step 5; Stacks 08J9
(blueprint: lem-pod-reindexing-hom-coefficient-descent).
Proof (node Steps 13--14): every finite list of objects and arrows is represented
at a common finite coefficient compositum. Conjugate the rational comparison
there by the recorded pullback and Hom scalar comparisons. rational_scalar and
the coefficient tower and unit identities identify these maps at every further
field. The representative equality criterion therefore gives a well-defined
class, independent of representatives. The inverse descends in exactly the same
way. Naturality is rational naturality at a common field. The fixed component
representatives give uniqueness. Evaluate every finite evaluation, transposition,
inverse, signed-shift or scheme-composition diagram at such a field: its integral
equation localizes there, and equality of classes gives its common-stage equation. -/
theorem common_comparison_existsUnique :
    ∃! α : commonHom l Ω Y ⋙ commonPullback l Ω g ≅
      commonPair l Ω g ⋙ commonHom l Ω X,
      IsCommonNormalized l Ω g α := by
  sorry
/-- The normalized natural comparison as an actual common-stage isomorphism.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
def commonComparison := (common_comparison_existsUnique l Ω g).exists.choose

-- Keep the original signature, including the scheme-isomorphism instance.
set_option linter.unusedSectionVars false in
attribute [local irreducible] commonPullback commonTensor commonHom
  commonComparison commonEvaluation

private theorem transportNatIso {C D : Type*} [Category* C] [Category* D]
    {F G F' G' : C ⥤ D} (hF : F = F') (hG : G = G') (e : F ≅ G) :
    ∃ e' : F' ≅ G', ∀ X, HEq (e'.app X).hom (e.app X).hom := by
  subst F' G'
  exact ⟨e, fun _ ↦ HEq.rfl⟩

section CommonCompositorProof

/-- The recorded scheme compositor in literal common-stage coordinates.
Source: blueprint Step 5 (blueprint: lem-pod-reindexing-hom-coefficient-descent).
Proof (node Step 14): tensor-product induction proves rational compositor naturality.
Represent each common-stage arrow over one field; the prescribed component formulas
and cancellation of the operation comparisons give common-stage naturality. Form
the natural isomorphism and transport it through the equality-only functor copies.
Every component is prescribed, so componentwise extensionality proves uniqueness. -/
theorem common_compositor_existsUnique {Z : Scheme.{u}} (h : Z ⟶ X) [IsIso h]
    [∀ z : Z, Invertible (l : Z.residueField z)] :
    ∃! p : commonPullback l Ω (h ≫ g) ≅ commonPullback l Ω g ⋙ commonPullback l Ω h,
      ∀ K, HEq (p.hom.app K) (pullbackTensorCommonComposition l Ω g h K).hom := by
  let e : commonStageDerivedPullback l Ω (h ≫ g) ≅
      commonStageDerivedPullback l Ω g ⋙ commonStageDerivedPullback l Ω h :=
    NatIso.ofComponents (pullbackTensorCommonComposition l Ω g h)
      (fun a ↦ commonStagePullbackComposition_naturality l Ω g h a)
  have hF := commonPullback_eq l Ω (h ≫ g)
  have hG : commonPullback l Ω g ⋙ commonPullback l Ω h =
      commonStageDerivedPullback l Ω g ⋙ commonStageDerivedPullback l Ω h := by
    rw [commonPullback_eq l Ω g, commonPullback_eq l Ω h]
  obtain ⟨p, hp⟩ := transportNatIso hF.symm hG.symm e
  refine ⟨p, hp, ?_⟩
  intro q hq
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((hq K).trans (hp K).symm)

end CommonCompositorProof

attribute [local irreducible] rationalDerivedPullback rationalDerivedInternalHom

end CommonStage

end WeilConjectures.PodCoefficientDescent

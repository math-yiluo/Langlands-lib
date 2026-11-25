/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
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
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationBase
public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationContinuationABase

import all WeilConjectures.SmoothPurity.Supporting.IsomorphismReductionTower
import WeilConjectures.PoincareDuality.PodCoefficientDescent.PodReindexingHomCoefficientDescent
import WeilConjectures.PoincareDuality.Pod.Integral.PodIntegralHomComparisonIsIso
import WeilConjectures.PoincareDuality.Pod.Integral.PodIntegralHomComparisonNaturality
import WeilConjectures.PoincareDuality.Pod.Integral.PodIntegralHomComparisonEvaluation
import WeilConjectures.PoincareDuality.Pod.Integral.PodIntegralHomComparisonTranspose
import all WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonIsomorphism
import WeilConjectures.PoincareDuality.Pod.PodRationalClosedExistence
import WeilConjectures.PoincareDuality.Pod.PodRationalClosedUniqueness
import WeilConjectures.PoincareDuality.Pod.PodSystemClosedCompatibility
import WeilConjectures.PoincareDuality.Pod.PodRestrictionReindexingTransition

/-! # Internal Hom and evaluation under coefficient-site isomorphisms

Source: Stacks Project, Modules on Sites, Tag 0GMX; the derived and completed
normalization is the enhancement in the node's sixteen proof steps, supplying
main-20261015 theorem-poincare-duality-frobenius--2 Steps 1, 2, 4 and 5.
(blueprint: lem-pod-derived-automorphism-hom-evaluation).

Finite inputs are unbounded. Integral inputs have exactly the recorded
Hom-constructibility condition. Completed inverse image is constructed from
all coefficient projections; its comparison with tower pullback uses the
actual completion unit and a resolution-normalized total-limit comparison.
System maps and their identities are stated before evaluation or realization.
Rational maps are localized; algebraically closed maps use every common stage.

## Main definitions

* `podFiniteHomComparison`: transpose of pullback of finite evaluation.
* `podPartialHomComparison`: the same construction on permitted Hom pairs.
* `podCompletedRingMap`: completed coefficient transport from all projections.
* `podCompletedToTower`: the completion-unit comparison with tower pullback.

## Main statements

* `derivedAutomorphismHomEvaluation`: the four evaluation-defined natural isomorphisms.
* The `*_laws`, `*_shift`, `*_comp` declarations give all coherent identities.
* `podHomReductionSquare`: the actual system-level reduction square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v a b c d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
  HasDerivedCategory.standard
attribute [-instance] isoReductionAbSheafify isoReductionAbBijective isoReductionSiteSmall

section IntegralTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Integral invertibility, naturality, evaluation and every transpose, using
completed tensor and exactly the stated Hom-constructible domain.
Source: node proof steps 8--11.
Proof: the four fields are `podIntegralHomComparison_isIso`,
`podIntegralHomComparison_naturality`, `podIntegralHomComparison_evaluation` and
`podIntegralHomComparison_transpose`.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralHomComparison_laws :
    PodPartialHomCompatibility (podIntegralClosed l E Y) (podIntegralClosed l E X)
      (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
        (canonicalIntegralPullbackTensor l E g) := by
  refine { isIso := ?_, naturality := ?_, evaluation := ?_, transpose := ?_ }
  · exact podIntegralHomComparison_isIso l E g
  · exact podIntegralHomComparison_naturality l E g
  · exact podIntegralHomComparison_evaluation l E g
  · exact podIntegralHomComparison_transpose l E g
end IntegralTransport

section RationalClosed
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

/-- The rational transpose is the unique additive localization of the integral
transpose. The equation fixes inverse transposition on every pure tensor in the
actual localized Hom groups, including its scalar.
Source: node proof step 14.
Proof: integral transposition is O_E-linear, so tensor it with E. Its inverse
localizes too. The unchanged integral objects and the prescribed rational
operation formulas identify the endpoints. Pure tensors generate each Hom
module, so the normalization determines both maps uniquely; balancing and
naturality descend from their integral versions.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podRationalClosed_existsUnique :
    ∃! S : PodPartialClosed (rationalDerivedTensor l E W)
        (constructibleRationalHomPairs l E W) (rationalDerivedInternalHom l E W),
      ∀ (L : sfRationalConstructibleCategory l E W)
        (P : (constructibleRationalHomPairs l E W).FullSubcategory)
        (f : L.obj ⟶ (constructibleIntegralHom l E W).obj
          (integralPairOfRationalHomPair l E W P))
        (a : Localization.Away (Padic.coefficientExtensionUniformizer l E))
        (q : L ⟶ (rationalDerivedInternalHom l E W).obj P),
        HEq q (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f) →
        HEq ((S.transpose L P).symm q)
          (a ⊗ₜ[Padic.coefficientExtensionIntegers l E]
            ((podIntegralClosed l E W).transpose L.obj
              (integralPairOfRationalHomPair l E W P)).symm f) := by
  obtain ⟨S, hS⟩ := podRationalClosed_exists l E W
  refine ⟨S, hS, ?_⟩
  intro S' hS'
  exact podRationalClosed_unique l E W S' S hS' hS

/-- The uniquely localized completed closed data.
Source: node proof step 14 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podRationalClosed := (podRationalClosed_existsUnique l E W).exists.choose
end RationalClosed

section PartialCalculus
variable {C : Type a} {D : Type c}
  [Category.{b} C] [Category.{d} D] [Preadditive C] [Preadditive D]
  {TC : C × C ⥤ C} {TD : D × D ⥤ D}
  {J : ObjectProperty (Cᵒᵖ × C)} {K : ObjectProperty (Dᵒᵖ × D)}
  {HC : J.FullSubcategory ⥤ C} {HD : K.FullSubcategory ⥤ D}
  (SC : PodPartialClosed TC J HC) (SD : PodPartialClosed TD K HD)
  (F : C ⥤ D) (h : ∀ P : J.FullSubcategory, K ((F.op.prod F).obj P.obj))
  (μ : ∀ L M : C, F.obj (TC.obj (L, M)) ≅ TD.obj (F.obj L, F.obj M))

-- Parameter naturality identifies inverse transposition with evaluation.
private theorem partial_evaluation (P : J.FullSubcategory) :
    (μ (HC.obj P) P.obj.1.unop).hom ≫
      TD.map (Prod.mkHom (podPartialHomComparison SC SD F h μ P) (𝟙 _)) ≫
        SD.evaluation ((podPairPullback F J K h).obj P) = F.map (SC.evaluation P) := by
  have key (L : D) (Q : K.FullSubcategory) (f : L ⟶ HD.obj Q) :
      TD.map (Prod.mkHom f (𝟙 _)) ≫ SD.evaluation Q = (SD.transpose L Q).symm f := by
    apply (SD.transpose L Q).injective
    rw [SD.parameter_naturality, PodPartialClosed.evaluation,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, Category.comp_id]
  erw [key]
  rw [podPartialHomComparison, AddEquiv.symm_apply_apply, Iso.hom_inv_id_assoc]

-- A natural tensor comparison preserves all transposes by the evaluation formula.
private theorem partial_transpose
    (hμ : ∀ (L L' M : C) (t : L' ⟶ L),
      TD.map (Prod.mkHom (F.map t) (𝟙 _)) ≫ (μ L M).inv =
        (μ L' M).inv ≫ F.map (TC.map (Prod.mkHom t (𝟙 _))))
    (L : C) (P : J.FullSubcategory) (f : TC.obj (L, P.obj.1.unop) ⟶ P.obj.2) :
    SD.transpose _ _ ((μ L P.obj.1.unop).inv ≫ F.map f) =
      F.map (SC.transpose L P f) ≫ podPartialHomComparison SC SD F h μ P := by
  set t := SC.transpose L P f
  have hev : TC.map (Prod.mkHom t (𝟙 _)) ≫ SC.evaluation P = f := by
    apply (SC.transpose L P).injective
    rw [SC.parameter_naturality, PodPartialClosed.evaluation,
      AddEquiv.apply_symm_apply, Category.comp_id]
  rw [podPartialHomComparison]
  erw [← SD.parameter_naturality]
  congr 1
  symm
  erw [reassoc_of% (hμ _ _ _ t)]
  erw [← F.map_comp, hev]
  rfl
end PartialCalculus

section LocalizationHelpers
open TensorProduct
variable {R : Type*} [CommRing R] {A : Type*} [Category* A]
  [Preadditive A] [Linear R A]

private theorem localized_forward (p : R)
    (L X M N : ScalarLocalization R A p) (X₀ M₀ : A)
    (hX : X = ⟨X₀⟩) (hM : M = ⟨M₀⟩)
    (e : (M ⟶ N) ≃+ (L ⟶ X))
    (e₀ : (M₀ ⟶ N.obj) ≃+ (L.obj ⟶ X₀))
    (hn : ∀ (a : Localization.Away p) (f : L.obj ⟶ X₀) (q : L ⟶ X),
      HEq q (a ⊗ₜ[R] f) → HEq (e.symm q) (a ⊗ₜ[R] e₀.symm f))
    (a : Localization.Away p) (f : M₀ ⟶ N.obj) (q : M ⟶ N)
    (hq : HEq q (a ⊗ₜ[R] f)) : HEq (e q) (a ⊗ₜ[R] e₀ f) := by
  cases hX
  cases hM
  cases hq
  apply heq_of_eq
  apply e.symm.injective
  rw [AddEquiv.symm_apply_apply]
  exact ((eq_of_heq (hn a (e₀ f) _ HEq.rfl)).trans
    (congrArg (fun z ↦ a ⊗ₜ[R] z) (e₀.symm_apply_apply f))).symm

private theorem iso_inv_heq {C : Type*} [Category* C] {X Y X' Y' : C}
    (hX : X = X') (hY : Y = Y') (e : X ≅ Y) (e' : X' ≅ Y')
    (h : HEq e.hom e'.hom) : HEq e.inv e'.inv := by
  subst X' Y'
  have : e = e' := Iso.ext (eq_of_heq h)
  cases this
  rfl

private theorem localized_map_heq (p : R) {B : Type*} [Category* B]
    [Preadditive B] [Linear R B] (F₀ : A ⥤ B)
    (F : ScalarLocalization R A p ⥤ ScalarLocalization R B p)
    (hm : ∀ (K L : A) (f : K ⟶ L) (a : Localization.Away p),
      HEq (F.map (a ⊗ₜ[R] f : ScalarLocalization.mk K ⟶ ScalarLocalization.mk L))
        (a ⊗ₜ[R] F₀.map f))
    {K L : ScalarLocalization R A p} {K₀ L₀ : A}
    (hK : K = ⟨K₀⟩) (hL : L = ⟨L₀⟩)
    (f : K ⟶ L) (f₀ : K₀ ⟶ L₀)
    (hf : HEq f ((ScalarLocalization.localization R A p).map f₀)) :
    HEq (F.map f) ((ScalarLocalization.localization R B p).map (F₀.map f₀)) := by
  subst K L
  cases hf
  exact hm K₀ L₀ f₀ 1

private theorem localized_inverse_identity (p : R)
    (M N H : ScalarLocalization R A p) (H₀ : A) (hH : H = ⟨H₀⟩)
    (T : ScalarLocalization R A p × ScalarLocalization R A p ⥤ ScalarLocalization R A p)
    (T₀ : A × A ⥤ A)
    (e : ∀ L, (T.obj (L, M) ⟶ N) ≃+ (L ⟶ H))
    (e₀ : ∀ L, (T₀.obj (L, M.obj) ⟶ N.obj) ≃+ (L ⟶ H₀))
    (hn : ∀ L (f : L.obj ⟶ H₀) (a : Localization.Away p) (q : L ⟶ H),
      HEq q (a ⊗ₜ[R] f) → HEq ((e L).symm q) (a ⊗ₜ[R] (e₀ L.obj).symm f)) :
    HEq ((e H).symm (𝟙 H))
      ((ScalarLocalization.localization R A p).map ((e₀ H₀).symm (𝟙 H₀))) := by
  cases hH
  exact hn _ (𝟙 _) 1 _ HEq.rfl

end LocalizationHelpers

section RationalNormalization
open TensorProduct
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

private theorem rationalEvaluation_localization
    (P : (constructibleRationalHomPairs l E W).FullSubcategory) :
    HEq ((podRationalClosed l E W).evaluation P)
      ((sfRationalConstructibleLocalization l E W).map
        ((podIntegralClosed l E W).evaluation (integralPairOfRationalHomPair l E W P))) := by
  exact localized_inverse_identity (Padic.coefficientExtensionUniformizer l E)
    P.obj.1.unop P.obj.2 ((rationalDerivedInternalHom l E W).obj P)
    ((constructibleIntegralHom l E W).obj (integralPairOfRationalHomPair l E W P))
    ((rationalDerivedInternalHom_existsUnique l E W).exists.choose_spec.1 P)
    (rationalDerivedTensor l E W) (constructibleIntegralTensor l E W)
    (fun L ↦ (podRationalClosed l E W).transpose L P)
    (fun L ↦ (podIntegralClosed l E W).transpose L (integralPairOfRationalHomPair l E W P))
    (fun L f a q hq ↦
      (podRationalClosed_existsUnique l E W).exists.choose_spec L P f a q hq)

private theorem rationalTranspose_localization
    (L : sfRationalConstructibleCategory l E W)
    (P : (constructibleRationalHomPairs l E W).FullSubcategory)
    (f : (constructibleIntegralTensor l E W).obj (L.obj, P.obj.1.unop.obj) ⟶ P.obj.2.obj)
    (a : Localization.Away (Padic.coefficientExtensionUniformizer l E))
    (q : (rationalDerivedTensor l E W).obj (L, P.obj.1.unop) ⟶ P.obj.2)
    (hq : HEq q (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f)) :
    HEq ((podRationalClosed l E W).transpose L P q)
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l E]
        (podIntegralClosed l E W).transpose L.obj (integralPairOfRationalHomPair l E W P) f) := by
  exact localized_forward (Padic.coefficientExtensionUniformizer l E)
    L ((rationalDerivedInternalHom l E W).obj P)
    ((rationalDerivedTensor l E W).obj (L, P.obj.1.unop)) P.obj.2 _ _
    ((rationalDerivedInternalHom_existsUnique l E W).exists.choose_spec.1 P)
    ((rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1 (L, P.obj.1.unop))
    ((podRationalClosed l E W).transpose L P)
    ((podIntegralClosed l E W).transpose L.obj (integralPairOfRationalHomPair l E W P))
    (fun a f q hq ↦ (podRationalClosed_existsUnique l E W).exists.choose_spec L P f a q hq)
    a f q hq

private theorem rationalTranspose_localized
    (L : sfRationalConstructibleCategory l E W)
    (P : (constructibleRationalHomPairs l E W).FullSubcategory)
    (L₀ : sfIntegralConstructibleCategory l E W)
    (P₀ : (constructibleIntegralHomPairs l E W).FullSubcategory)
    (hL : L.obj = L₀) (hP : integralPairOfRationalHomPair l E W P = P₀)
    (f : (constructibleIntegralTensor l E W).obj (L₀, P₀.obj.1.unop) ⟶ P₀.obj.2)
    (q : (rationalDerivedTensor l E W).obj (L, P.obj.1.unop) ⟶ P.obj.2)
    (hq : HEq q ((sfRationalConstructibleLocalization l E W).map f)) :
    HEq ((podRationalClosed l E W).transpose L P q)
      ((sfRationalConstructibleLocalization l E W).map
        ((podIntegralClosed l E W).transpose L₀ P₀ f)) := by
  subst L₀ P₀
  exact rationalTranspose_localization l E W L P f 1 q hq
end RationalNormalization

section RationalTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Rational pullback preserves the same integral Hom-pair condition.
Source: node proof step 14.
Proof: the rational operations keep integral objects. Their object formulas
identify this condition with podIntegralPairs_pullback.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podRationalPairs_pullback
    (P : (constructibleRationalHomPairs l E Y).FullSubcategory) :
    constructibleRationalHomPairs l E X
      (((rationalDerivedPullback l E g).op.prod (rationalDerivedPullback l E g)).obj P.obj) := by
  exact PodCoefficientDescent.rational_pair_permitted l E g P

/-- The rational comparison uses precisely localized tensor and evaluation.
Source: node proof step 14 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podRationalHomComparison :=
  podPartialHomComparison (podRationalClosed l E Y) (podRationalClosed l E X)
    (rationalDerivedPullback l E g) (podRationalPairs_pullback l E g)
      (canonicalRationalPullbackTensor l E g)

-- Compare the actual transposes after normalizing the recorded operation objects.
private theorem rationalComparison_localization
    (P : (constructibleRationalHomPairs l E Y).FullSubcategory) :
    HEq (podRationalHomComparison l E g P)
      ((sfRationalConstructibleLocalization l E X).map
        (podIntegralHomComparison l E g (integralPairOfRationalHomPair l E Y P))) := by
  let F := rationalDerivedPullback l E g
  let F₀ := constructibleIntegralPullback l E g
  let QX := sfRationalConstructibleLocalization l E X
  let P₀ := integralPairOfRationalHomPair l E Y P
  let PX := (podPairPullback F _ _ (podRationalPairs_pullback l E g)).obj P
  let PX₀ := (podPairPullback F₀ _ _ (podIntegralPairs_pullback l E g)).obj P₀
  let H := (rationalDerivedInternalHom l E Y).obj P
  let H₀ := (constructibleIntegralHom l E Y).obj P₀
  have hF (K : sfRationalConstructibleCategory l E Y) :
      F.obj K = QX.obj (F₀.obj K.obj) :=
    (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.1 K
  have hT (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
      (A B : sfRationalConstructibleCategory l E W) :
      (rationalDerivedTensor l E W).obj (A, B) =
        (sfRationalConstructibleLocalization l E W).obj
          ((constructibleIntegralTensor l E W).obj (A.obj, B.obj)) :=
    (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1 (A, B)
  have hH : H = (sfRationalConstructibleLocalization l E Y).obj H₀ :=
    (rationalDerivedInternalHom_existsUnique l E Y).exists.choose_spec.1 P
  have hH₀ : H.obj = H₀ := by rw [hH]; rfl
  have hp : integralPairOfRationalHomPair l E X PX = PX₀ := by
    apply ObjectProperty.FullSubcategory.ext
    change (op (F.obj P.obj.1.unop).obj, (F.obj P.obj.2).obj) = _
    rw [hF, hF]
    rfl
  have hL : (F.obj H).obj = F₀.obj H₀ := by rw [hF, hH]; rfl
  have hs : F.obj ((rationalDerivedTensor l E Y).obj (H, P.obj.1.unop)) =
      QX.obj (F₀.obj ((constructibleIntegralTensor l E Y).obj (H₀, P₀.obj.1.unop))) := by
    rw [hF, hT, hH]
    rfl
  have ht : (rationalDerivedTensor l E X).obj (F.obj H, F.obj P.obj.1.unop) =
      QX.obj ((constructibleIntegralTensor l E X).obj
        (F₀.obj H₀, F₀.obj P₀.obj.1.unop)) := by
    rw [hT, hF, hF, hH]
    rfl
  have hn : F.obj P.obj.2 = QX.obj (F₀.obj P₀.obj.2) := hF _
  let μ₀ := canonicalIntegralPullbackTensor l E g H₀ P₀.obj.1.unop
  have hμ : HEq (canonicalRationalPullbackTensor l E g H P.obj.1.unop).hom
      (QX.map μ₀.hom) := by
    have hc : HEq (canonicalRationalPullbackTensor l E g H P.obj.1.unop).hom
        (QX.map (canonicalIntegralPullbackTensor l E g H.obj P.obj.1.unop.obj).hom) :=
      (canonicalRationalPullbackTensor_existsUnique l E g H P.obj.1.unop).exists.choose_spec
    apply hc.trans
    dsimp only [μ₀, P₀]
    rw [hH₀]
    rfl
  have hμi := iso_inv_heq hs ht (canonicalRationalPullbackTensor l E g H P.obj.1.unop)
    (QX.mapIso μ₀) hμ
  have hev := rationalEvaluation_localization l E Y P
  have hevm := localized_map_heq (Padic.coefficientExtensionUniformizer l E) F₀ F
    (fun K L f a ↦
      (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.2 K L f a)
    (by
      rw [hT]
      change (sfRationalConstructibleLocalization l E Y).obj
        ((constructibleIntegralTensor l E Y).obj (H.obj, P.obj.1.unop.obj)) = _
      rw [hH₀]
      rfl) rfl _ _ hev
  have harg := heq_comp ht hs hn hμi hevm
  exact rationalTranspose_localized l E X (F.obj H) PX (F₀.obj H₀) PX₀ hL hp
    (μ₀.inv ≫ F₀.map ((podIntegralClosed l E Y).evaluation P₀)) _
    (harg.trans (heq_of_eq (QX.map_comp _ _).symm))

attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor
  rationalDerivedInternalHom constructibleIntegralPullback constructibleIntegralHom

/-- Rational maps are the localized integral maps, and naturality holds for
arbitrary localized Hom arrows, including sums of pure tensors.
Source: node proof step 14.
Proof: localize the integral comparison and its inverse. On pure tensors the
closed normalization gives the displayed map; additivity and balancing extend
this to all arrows. Expand each naturality and evaluation equation bilinearly
and apply the integral equation to each summand. Transposition is linear too.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podRationalHomComparison_laws :
    PodPartialHomCompatibility (podRationalClosed l E Y) (podRationalClosed l E X)
      (rationalDerivedPullback l E g) (podRationalPairs_pullback l E g)
        (canonicalRationalPullbackTensor l E g) ∧
    ∀ P : (constructibleRationalHomPairs l E Y).FullSubcategory,
      HEq (podRationalHomComparison l E g P)
        ((sfRationalConstructibleLocalization l E X).map
          (podIntegralHomComparison l E g (integralPairOfRationalHomPair l E Y P))) := by
  have hI := podIntegralHomComparison_laws l E g
  let a (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) :
      (constructibleIntegralPullback l E g).obj ((constructibleIntegralHom l E Y).obj P) ≅
        (constructibleIntegralHom l E X).obj
          ((PodCoefficientDescent.integralPair l E g).obj P) := by
    have : IsIso (podIntegralHomComparison l E g P) := hI.isIso P
    exact asIso (podIntegralHomComparison l E g P)
  let α : constructibleIntegralHom l E Y ⋙ constructibleIntegralPullback l E g ≅
      PodCoefficientDescent.integralPair l E g ⋙ constructibleIntegralHom l E X :=
    NatIso.ofComponents a (by
      intro P Q f
      exact hI.naturality P Q f)
  let β := (PodCoefficientDescent.rational_comparison_existsUnique l E g α).exists.choose
  have hβ := (PodCoefficientDescent.rational_comparison_existsUnique l E g α).exists.choose_spec
  have hα (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) :
      α.hom.app P = podIntegralHomComparison l E g P := rfl
  have he (P : (constructibleRationalHomPairs l E Y).FullSubcategory) :
      podRationalHomComparison l E g P = β.hom.app P := by
    have hb := (hβ P).1
    rw [hα] at hb
    exact eq_of_heq ((rationalComparison_localization l E g P).trans hb.symm)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, rationalComparison_localization l E g⟩
  · intro P
    change IsIso (podRationalHomComparison l E g P)
    rw [he]
    infer_instance
  · intro P Q f
    change _ ≫ podRationalHomComparison l E g Q = podRationalHomComparison l E g P ≫ _
    rw [he, he]
    exact β.hom.naturality f
  · exact partial_evaluation _ _ _ _ _
  · apply partial_transpose
    obtain ⟨eR, heR⟩ :=
      (derivedPullbackTensorIso l E g 0 (AlgebraicClosure ℚ_[l])).2.2.2.2.2.2.1
    intro L L' M t
    rw [← heR, ← heR, Iso.app_inv, Iso.app_inv]
    have hn := eR.inv.naturality (Prod.mkHom t (𝟙 M))
    simpa only [Functor.comp_map, Functor.prod_map,
      (rationalDerivedPullback l E g).map_id] using hn
end RationalTransport

section CommonClosed
open GeneralAlgebraicallyClosedCoefficients AlgebraicallyClosedCoefficients
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

/-- Exact common-stage normalization of inverse transposition, at every finite
stage containing the entries. The implications only reconcile the recorded
operation objects with their literal pair representatives, whose equality is
part of the owning operation definitions; they impose no condition on arrows.
Source: node proof steps 15--16
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def PodCommonTransposeNormalization
    (S : PodPartialClosed (commonStageDerivedTensor l Ω W)
      (commonStageHomPairs l Ω W) (commonStageDerivedInternalHom l Ω W)) : Prop :=
  ∀ (L : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (P : (commonStageHomPairs l Ω W).FullSubcategory)
    (F : AlgebraicallyClosedCoefficients.Index l Ω)
    (hL : L.stage ≤ F) (hP : (commonStageHomObject l Ω W P).stage ≤ F)
    (hT : (commonStageTensorObject l Ω W L P.obj.1.unop).stage ≤ F)
    (hN : P.obj.2.stage ≤ F)
    (φ : L.toStage hL ⟶ (commonStageHomObject l Ω W P).toStage hP)
    (q : L ⟶ (commonStageDerivedInternalHom l Ω W).obj P),
    HEq q (ofHom L (commonStageHomObject l Ω W P) F hL hP φ) →
    HEq ((S.transpose L P).symm q)
      (ofHom (commonStageTensorObject l Ω W L P.obj.1.unop) P.obj.2 F hT hN
        ((commonStageTensorComparison l Ω W L P.obj.1.unop F hT).hom ≫
          ((podRationalClosed l (Coefficient.{u} l Ω F) W).transpose (L.toStage hL)
            (commonStageHomPairAtStage l Ω W P F hP)).symm
              (φ ≫ (commonStageHomComparison l Ω W P F hP).hom)))

/-- Common-stage closed maps are determined by rational transposition at every
larger finite field, and are natural on the actual Hom-colimit category.
Source: node proof steps 15--16.
Proof: put the parameter, pair and arrow over a common finite field. Apply the
rational inverse transpose, conjugating by the recorded tensor and Hom stage
comparisons. Finite free coefficient extension preserves the evaluation formula,
without requiring the first input to be perfect: Hom commutes with the finite
direct sum of its coefficient copies. Transposition therefore commutes with
further scalar extension. This proves independence of enlargement and eventual
equality. The rational inverse maps prove bijectivity; addition and naturality
can be checked at one common stage. Every arrow has such a representative, so
the normalization determines the closed data uniquely.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCommonClosed_existsUnique :
    ∃! S : PodPartialClosed (commonStageDerivedTensor l Ω W)
      (commonStageHomPairs l Ω W) (commonStageDerivedInternalHom l Ω W),
      PodCommonTransposeNormalization l Ω W S := by
  sorry

/-- The closed data normalized on all common finite-field representatives.
Source: node proof step 16 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCommonClosed := (podCommonClosed_existsUnique l Ω W).exists.choose
end CommonClosed

section CommonTransport
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

attribute [local irreducible] commonStageHomPairs

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Isomorphism pullback preserves the permitted common-stage Hom pairs.
Source: node proof steps 15--16.
Proof: at the finite compositum use podRationalPairs_pullback, then the
prescribed pullback/scalar comparison to identify both entries. Hom of the
resulting pair is isomorphic to the pulled back Hom, so is constructible.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCommonPairs_pullback
    (P : (commonStageHomPairs l Ω Y).FullSubcategory) :
    commonStageHomPairs l Ω X
      (((commonStageDerivedPullback l Ω g).op.prod
        (commonStageDerivedPullback l Ω g)).obj P.obj) := by
  have h := PodCoefficientDescent.common_pair_permitted l Ω g P
  have hobj (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
      (commonStageDerivedPullback l Ω g).obj M = commonStagePullbackObject l Ω g M :=
    (commonStageDerivedPullback_existsUnique l Ω g).exists.choose_spec.1 M
  change commonStageHomPairs l Ω X
    (op ((commonStageDerivedPullback l Ω g).obj P.obj.1.unop),
      (commonStageDerivedPullback l Ω g).obj P.obj.2)
  rw [hobj, hobj]
  exact h

/-- The common-stage comparison is the transpose of the prescribed common-stage
tensor/evaluation composite on the actual pair category.
Source: node proof step 16 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCommonHomComparison :=
  podPartialHomComparison (podCommonClosed l Ω Y) (podCommonClosed l Ω X)
    (commonStageDerivedPullback l Ω g) (podCommonPairs_pullback l Ω g)
      (canonicalCommonStagePullbackTensor l Ω g)

/-- Invertibility and all displayed identities on the algebraically closed
coefficient category, naturally for arbitrary common-stage morphisms.
Source: node proof steps 15--16.
Proof: put every arrow in a proposed equation over one common finite field.
The normalized transpose and tensor comparison identify the comparison there
with the rational evaluation-defined comparison. Its inverse, naturality,
evaluation and transposition equations hold by podRationalHomComparison_laws.
Finite free scalar compatibility makes their classes independent of the
chosen stage and arrow representative, including eventual equality.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCommonHomComparison_laws :
    PodPartialHomCompatibility (podCommonClosed l Ω Y) (podCommonClosed l Ω X)
      (commonStageDerivedPullback l Ω g) (podCommonPairs_pullback l Ω g)
        (canonicalCommonStagePullbackTensor l Ω g) := by
  sorry
end CommonTransport

section Systems
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]

/-- The comparison is an actual map on the unbounded derived category of strict
systems, defined before finite evaluation or total-limit realization.
Source: node proof steps 12--13, Stacks 0941 and 0GMX
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podSystemHomComparison :=
  coefficientBaseChangeHom (pullbackTensorCalculus l E Y).systemClosed
    (pullbackTensorCalculus l E X).systemClosed (pullbackTensorSequenceDerived l E g)
      (pullbackTensorSystemComparison l E g)

/-- System reindexing preserves internal Hom and the actual system evaluation,
transposes and internal composition, without inferring equality from evaluations.
Source: node proof step 12.
Proof: identify the ordinary sequence inverse image with the integral-comparison
pullback by their common ring map. Its derived composition and identity
isomorphisms exhibit inverse reindexing as a quasi-inverse. For every test
object in the image, the two closed adjunctions, full faithfulness and the
tensor comparison identify postcomposition with the Hom comparison as a
bijection. Essential surjectivity extends this to all test objects, so Yoneda
proves invertibility. Naturality and transposition are the general closed
adjunction calculations. The recorded tensor associativity and unit identities
construct a strong monoidal structure with exactly the prescribed tensorator;
the general evaluation/composition calculation then gives all remaining laws.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podSystemHomComparison_laws :
    (∀ M N, IsIso (podSystemHomComparison l E g M N)) ∧
    CoefficientEvaluationCompatible (pullbackTensorCalculus l E Y).systemClosed
      (pullbackTensorCalculus l E X).systemClosed (pullbackTensorSequenceDerived l E g)
        (pullbackTensorSystemComparison l E g) := by
  exact podSystemClosedCompatibility l E g
end Systems

attribute [local irreducible] sfIntrinsicPullback

section CompletedReindexing
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]

/-- Pullback of the nth completed-ring projection, followed by the uniquely
constant-section-normalized finite coefficient map.
Source: node proof step 1 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedRingProjection (n : ℕᵒᵖ) :
    (isoSectionwiseInverseImage g RingCat.{u+1}).obj
        (completedIntegralCoefficientSheafUnrestricted l E Y) ⟶
      (integralCoefficientSheafSystem l E X).obj n :=
  (isoSectionwiseInverseImage g RingCat.{u+1}).map
      (limit.π (integralCoefficientSheafSystem l E Y) n) ≫
    isoSectionwiseConstantMap.{u, u} g
      (CommRingCat.of (ULift.{u+1} (finiteCoefficientRing l E (n.unop + 1))))

/-- The projection maps respect every coefficient quotient arrow.
Source: node proof step 1, Stacks 0H7J.
Proof: the limit projections respect every quotient. Constant-section maps
commute with quotient homomorphisms by the sheafification universal property.
Compose these two naturality equations.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCompletedRingProjection_naturality {m n : ℕᵒᵖ} (f : m ⟶ n) :
    podCompletedRingProjection l E g m ≫ (integralCoefficientSheafSystem l E X).map f =
      podCompletedRingProjection l E g n := by
  have hπ := (isoReductionCompletedMap_existsUnique l E g).exists.choose_spec
  dsimp only [podCompletedRingProjection]
  rw [← hπ m.unop, ← hπ n.unop]
  simp only [Category.assoc, limit.w]

/-- The actual completed coefficient transport, constructed by the limit lift
of all finite projections. Source: node proof step 1, Stacks 0038
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedRingMap :
    (isoSectionwiseInverseImage g RingCat.{u+1}).obj
        (completedIntegralCoefficientSheafUnrestricted l E Y) ⟶
      completedIntegralCoefficientSheafUnrestricted l E X :=
  limit.lift (integralCoefficientSheafSystem l E X)
    { pt := _
      π := { app := podCompletedRingProjection l E g
             naturality := fun _ _ f ↦
               (Category.id_comp _).trans (podCompletedRingProjection_naturality l E g f).symm } }

/-- Completed-ring transport is invertible with precisely the prescribed
projections. Source: node proof step 1, Stacks 0038.
Proof: the site equivalence preserves the inverse limit. Each finite coefficient
comparison is invertible. The induced map of limit cones is therefore invertible.
Its composites with the projections are the defining limit-lift equations.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCompletedRingMap_isIso : IsIso (podCompletedRingMap l E g) := by
  have he : podCompletedRingMap l E g = (isoReductionCompletedMap l E g).hom := by
    apply limit.hom_ext
    intro n
    rw [podCompletedRingMap, limit.lift_π]
    exact ((isoReductionCompletedMap_existsUnique l E g).exists.choose_spec n.unop).symm
  rw [he]
  infer_instance

/-- Use the proved invertibility of the actual limit-lift map.
Source: Stacks 0038 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
instance podCompletedRingMapIsIso : IsIso (podCompletedRingMap l E g) :=
  podCompletedRingMap_isIso l E g

attribute [local irreducible] podCompletedRingMap

/-- Exact inverse image on modules over the completed ring sheaf, sectionwise
with the transported coefficient action. Source: node proof step 1
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedModuleInverseImage : integralTowerModules l E Y ⥤ integralTowerModules l E X :=
  isoSectionwiseModuleInverseImage.{u, u} g (podCompletedRingMap l E g)

/-- Additivity inherited from the published exact sectionwise inverse image.
Source: Stacks 03DA (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
instance podCompletedModuleAdditive : (podCompletedModuleInverseImage l E g).Additive :=
  isoSectionwiseModuleInverseImage_additive.{u, u} g (podCompletedRingMap l E g)

/-- Left exactness inherited from the published inverse image.
Source: Stacks 03DA (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
instance podCompletedModuleLimits : PreservesFiniteLimits (podCompletedModuleInverseImage l E g) :=
  isoSectionwiseModuleInverseImage_limits.{u, u} g (podCompletedRingMap l E g)

/-- Right exactness inherited from the published inverse image.
Source: Stacks 03DA (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
instance podCompletedModuleColimits :
    PreservesFiniteColimits (podCompletedModuleInverseImage l E g) :=
  isoSectionwiseModuleInverseImage_colimits.{u, u} g (podCompletedRingMap l E g)

/-- The unbounded derived exact inverse-image equivalence, with the standard
termwise localization and its standard shift comparison.
Source: node proof steps 1--2 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedDerivedInverseImage := (podCompletedModuleInverseImage l E g).mapDerivedCategory

/-- Sectionwise completed inverse image is an equivalence.
Source: node proof steps 1--2.
Proof: reindex with the inverse scheme isomorphism and inverse coefficient map.
Both composites are identity on every coefficient projection, hence on the
completed ring and its actions. The identity-on-sections maps give the natural
unit and counit. Deriving preserves their inverse identities.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCompletedInverseImage_equivalence :
    (podCompletedModuleInverseImage l E g).IsEquivalence ∧
      (podCompletedDerivedInverseImage l E g).IsEquivalence := by
  have h : (podCompletedModuleInverseImage l E g).IsEquivalence :=
    isoReduction_equivalence.{u, u} g (podCompletedRingMap l E g)
  let := h
  refine ⟨h, ?_⟩
  exact Functor.isEquivalence_mapDerivedCategory.{u + 2, u + 2, u + 1, u + 1,
    u + 2, u + 2} (podCompletedModuleInverseImage l E g)

/-- Restriction and reindexing agree by the inverse-image unit on every local
section. This specifies the ordinary comparison before passing to derived maps.
Source: node proof steps 1 and 8.
Proof: after scalar restriction the underlying sheaf of a finite module is
unchanged. The canonical isomorphism from intrinsic inverse image to sectionwise
reindexing sends its adjunction-unit section to restriction along the counit
of postcomposition/base-change. The completed ring map commutes with the finite
projection, so the same section map is linear for the completed action.
The unit determines the comparison uniquely: the finite inverse image is an
equivalence, so its adjunction unit is invertible. Cancel its section maps to
compare transformations on base-changed objects. Base change is itself an
equivalence of sites, so faithful precomposition extends this equality to every
object. The left-adjoint uniqueness comparison supplies the normalized map,
and the scalar-restriction square supplies its completed scalar action.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podFiniteRestrictionOrdinary_existsUnique (n : ℕ) :
    ∃! e : sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) g ⋙
        scalarReductionRestriction l E X n ≅
      scalarReductionRestriction l E Y n ⋙ podCompletedModuleInverseImage l E g,
      ∀ (M : normalizedDVRModules l E Y n) (V : Y.ProEt)
        (x : M.val.obj (op V)),
        HEq (((e.hom.app M).val.app (op ((proEtaleBaseChange g).obj V)))
          ((((sfIntrinsicConstantModuleAdjunction g
            (finiteCoefficientRing l E (n + 1))).unit.app M).val.app (op V)) x))
          ((M.val.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
            (inferInstance : WeaklyEtale g) trivial).counit.app V).op) x) := by
  have he : podCompletedRingMap l E g = (isoReductionCompletedMap l E g).hom := by
    apply limit.hom_ext
    intro k
    rw [podCompletedRingMap, limit.lift_π]
    exact ((isoReductionCompletedMap_existsUnique l E g).exists.choose_spec k.unop).symm
  have hF : podCompletedModuleInverseImage l E g = isoReductionIntegralInverse l E g := by
    exact congrArg (fun c ↦ isoSectionwiseModuleInverseImage.{u, u} g c.hom)
      (show asIso (podCompletedRingMap l E g) = isoReductionCompletedMap l E g from
        Iso.ext he)
  rw [hF]
  let a := sfIntrinsicConstantModuleAdjunction g (finiteCoefficientRing l E (n + 1))
  let b := AlgebraicGeometry.ProEtale.finiteSectionwiseAdjunction.{u, u} l E g n
  let c := a.leftAdjointUniq b
  obtain ⟨s, hs⟩ := isoReduction_restrictionSquare.{u, u} l E g n
  have hsInv (M : normalizedDVRModules l E Y n) (U : X.ProEtᵒᵖ)
      (x : M.val.obj ((proEtaleIsoPostcompose g).op.obj U)) :
      (s.inv.app M).val.app U x = x := by
    have hi := moduleIso_hom_inv_apply (s.app M) U x
    change (s.inv.app M).val.app U ((s.hom.app M).val.app U x) = x at hi
    rw [hs] at hi
    exact hi
  let e := Functor.isoWhiskerRight c (scalarReductionRestriction l E X n) ≪≫ s.symm
  have hn (M : normalizedDVRModules l E Y n) (V : Y.ProEt)
      (x : M.val.obj (op V)) :
      ((e.hom.app M).val.app (op ((proEtaleBaseChange g).obj V)))
          (((a.unit.app M).val.app (op V)) x) =
        (M.val.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
          (inferInstance : WeaklyEtale g) trivial).counit.app V).op) x := by
    change (s.inv.app M).val.app _
      ((c.hom.app M).val.app _ ((a.unit.app M).val.app (op V) x)) = _
    rw [hsInv]
    exact congrArg (fun z ↦ z.val.app (op V) x)
      (Adjunction.unit_leftAdjointUniq_hom_app a b M)
  refine ⟨e, fun M V x ↦ heq_of_eq (hn M V x), ?_⟩
  intro e' he'
  have hpost : (MorphismProperty.Over.map ⊤
      (inferInstance : WeaklyEtale g)).IsEquivalence :=
    (proEtaleIsoPostcompose_equivalence g).1
  let siteAdj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial
  have : (proEtaleBaseChange g).IsEquivalence :=
    siteAdj.isEquivalence_right_of_isEquivalence_left
  have hb : Functor.IsEquivalence
      (AlgebraicGeometry.ProEtale.inverseImageFiniteModules.{u, u} l E g n) :=
    isoReduction_equivalence.{u, u} g _
  have : (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) g).IsEquivalence :=
    Functor.isEquivalence_of_iso c.symm
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.toPresheaf _).map_injective
  have : IsIso (a.unit.app M).val :=
    inferInstanceAs (IsIso ((SheafOfModules.forget _).map (a.unit.app M)))
  have hlevel (V : Y.ProEt) :
      ((PresheafOfModules.toPresheaf _).map (e'.hom.app M).val).app
          (op ((proEtaleBaseChange g).obj V)) =
        ((PresheafOfModules.toPresheaf _).map (e.hom.app M).val).app
          (op ((proEtaleBaseChange g).obj V)) := by
    apply (cancel_epi
      (((PresheafOfModules.toPresheaf _).map (a.unit.app M).val).app (op V))).1
    ext x
    exact (eq_of_heq (he' M V x)).trans (hn M V x).symm
  apply ((Functor.whiskeringLeft _ _ AddCommGrpCat).obj (proEtaleBaseChange g).op).map_injective
  apply NatTrans.ext
  funext V
  exact hlevel V.unop

/-- The uniquely section-normalized ordinary coefficient restriction comparison.
Source: node proof step 8 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podFiniteRestrictionOrdinary (n : ℕ) :=
  (podFiniteRestrictionOrdinary_existsUnique l E g n).exists.choose

/-- Derived finite restriction/reindexing comparison induced from that same
ordinary section map. Source: node proof step 8
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podFiniteRestriction (n : ℕ) :
    finiteDerivedPullback l E n g ⋙ coefficientFiniteDerivedRestriction l E X n ≅
      coefficientFiniteDerivedRestriction l E Y n ⋙ podCompletedDerivedInverseImage l E g :=
  letI := podCompletedModuleAdditive l E g
  letI := podCompletedModuleLimits l E g
  letI := podCompletedModuleColimits l E g
  Functor.mapDerivedCategoryCompIso
    (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) g)
    (scalarReductionRestriction l E X n) ≪≫
    Functor.mapDerivedCategoryNatIso (podFiniteRestrictionOrdinary l E g n) ≪≫
      (Functor.mapDerivedCategoryCompIso (scalarReductionRestriction l E Y n)
        (podCompletedModuleInverseImage l E g)).symm

/-- The actual ordinary limit projection, with the restriction/evaluation identity.
Source: Stacks 0941 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podOrdinaryProjection (W : Scheme.{u}) (n : ℕ) :
    pullbackTensorOrdinaryLimit l E W ⟶
      coefficientSequenceEvaluation l E W n ⋙ scalarReductionRestriction l E W n :=
  Functor.whiskerLeft (coefficientSequenceRestriction l E W) (lim.π (op n)) ≫
    eqToHom (coefficientSequenceRestriction_evaluation l E W n)

/-- The unit-normalized ordinary system/finite pullback comparison.
Source: node proof step 12 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podSystemEvaluationOrdinary (n : ℕ) :
    pullbackTensorSequenceInverse l E g ⋙ coefficientSequenceEvaluation l E X n ≅
      coefficientSequenceEvaluation l E Y n ⋙
        sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) g :=
  (pullbackTensorSequenceInverseEvaluation l E g n).symm ≪≫
    Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E Y n)
      (pullbackTensorLevelIntrinsic l E g n)

attribute [local irreducible] coefficientSequenceRestriction coefficientSequenceEvaluation
  pullbackTensorSequenceInverse isoSectionwiseModuleInverseImage podFiniteRestrictionOrdinary

/-- Ordinary limits commute with the exact equivalence, uniquely on all projections.
Source: node proof step 8, Stacks 0038.
Proof: the two functors take the ordinary limit of the same reindexed diagram.
The finite restriction comparisons identify their cones. The limit universal
property supplies the comparison and its inverse, and jointly monic ordinary
projections prove naturality and uniqueness.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podOrdinaryLimitReindexing_existsUnique :
    ∃! e : pullbackTensorSequenceInverse l E g ⋙ pullbackTensorOrdinaryLimit l E X ≅
        pullbackTensorOrdinaryLimit l E Y ⋙ podCompletedModuleInverseImage l E g,
      ∀ (N : coefficientSequenceModules l E Y) (n : ℕ),
        e.hom.app N ≫ (podCompletedModuleInverseImage l E g).map
          ((podOrdinaryProjection l E Y n).app N) =
        (podOrdinaryProjection l E X n).app ((pullbackTensorSequenceInverse l E g).obj N) ≫
        (scalarReductionRestriction l E X n).map
          ((podSystemEvaluationOrdinary l E g n).hom.app N) ≫
        (podFiniteRestrictionOrdinary l E g n).hom.app
          ((coefficientSequenceEvaluation l E Y n).obj N) := by
  let F := podCompletedModuleInverseImage l E g
  let S := pullbackTensorSequenceInverse l E g
  let RY := coefficientSequenceRestriction l E Y
  let RX := coefficientSequenceRestriction l E X
  let δ (n : ℕ) :
      S ⋙ RX ⋙ (evaluation ℕᵒᵖ (integralTowerModules l E X)).obj (op n) ≅
        RY ⋙ (evaluation ℕᵒᵖ (integralTowerModules l E Y)).obj (op n) ⋙ F :=
    Functor.isoWhiskerLeft S (eqToIso (coefficientSequenceRestriction_evaluation l E X n)) ≪≫
      Functor.isoWhiskerRight (podSystemEvaluationOrdinary l E g n)
        (scalarReductionRestriction l E X n) ≪≫
      Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E Y n)
        (podFiniteRestrictionOrdinary l E g n) ≪≫
      Functor.isoWhiskerRight (eqToIso
        (coefficientSequenceRestriction_evaluation l E Y n)).symm F
  have hδ := podRestrictionReindexingTransition l E g (podCompletedRingMap l E g)
    (podFiniteRestrictionOrdinary l E g)
    (fun n ↦ by
      rw [podCompletedRingMap, limit.lift_π]
      rfl)
    (fun n ↦ by
      simpa only [podFiniteRestrictionOrdinary, podCompletedModuleInverseImage] using
        (podFiniteRestrictionOrdinary_existsUnique l E g n).exists.choose_spec)
  let a : S ⋙ RX ≅ RY ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj F :=
    NatIso.ofComponents
      (fun N ↦ NatIso.ofComponents (fun n ↦ (δ n.unop).app N)
        (fun f ↦ hδ N f))
      (by
        intro N N' f
        apply NatTrans.ext
        funext n
        exact (δ n.unop).hom.naturality f)
  have : F.IsEquivalence := (podCompletedInverseImage_equivalence l E g).1
  let e : S ⋙ pullbackTensorOrdinaryLimit l E X ≅
      pullbackTensorOrdinaryLimit l E Y ⋙ F :=
    Functor.isoWhiskerRight a lim ≪≫
      Functor.isoWhiskerLeft RY (preservesLimitNatIso F).symm
  have he (N : coefficientSequenceModules l E Y) (n : ℕ) :
      e.hom.app N ≫ F.map ((podOrdinaryProjection l E Y n).app N) =
        (podOrdinaryProjection l E X n).app (S.obj N) ≫
        (scalarReductionRestriction l E X n).map
          ((podSystemEvaluationOrdinary l E g n).hom.app N) ≫
        (podFiniteRestrictionOrdinary l E g n).hom.app
          ((coefficientSequenceEvaluation l E Y n).obj N) := by
    dsimp only [e, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      podOrdinaryProjection]
    simp only [F.map_comp, Category.assoc]
    erw [preservesLimitIso_inv_π_assoc, limMap_π_assoc]
    dsimp only [a, NatIso.ofComponents_hom_app, δ, Iso.trans_hom,
      Iso.symm_hom, Iso.app_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    simp only [Category.assoc, ← F.map_comp, eqToIso.hom, eqToIso.inv,
      eqToHom_app, eqToHom_trans, eqToHom_refl, F.map_id]
    simp only [lim.π_app]
    erw [Category.comp_id]
    rfl
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply (isLimitOfPreserves F (limit.isLimit (RY.obj N))).hom_ext
  intro n
  apply (cancel_mono (F.map
    ((eqToIso (coefficientSequenceRestriction_evaluation l E Y n.unop)).hom.app N))).1
  change e'.hom.app N ≫ F.map (limit.π (RY.obj N) n) ≫ F.map _ =
    e.hom.app N ≫ F.map (limit.π (RY.obj N) n) ≫ F.map _
  simpa only [Category.assoc, ← F.map_comp, podOrdinaryProjection,
    NatTrans.comp_app, Functor.whiskerLeft_app, lim.π_app, eqToIso.hom]
    using (he' N n.unop).trans (he N n.unop).symm

/-- The ordinary projection-normalized limit comparison.
Source: Stacks 0038 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podOrdinaryLimitReindexing :=
  (podOrdinaryLimitReindexing_existsUnique l E g).exists.choose

/-- Resolution normalization for total derived-limit reindexing, imposed before
any finite evaluation. This is the right-derived universal-property square.
Source: node proof steps 8 and 13
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def PodLimitResolutionNormalization
    (e : pullbackTensorSequenceDerived l E g ⋙ coefficientSequenceLimit l E X ≅
      coefficientSequenceLimit l E Y ⋙ podCompletedDerivedInverseImage l E g) : Prop :=
  ∀ C : CochainComplex (coefficientSequenceModules l E Y) ℤ,
    pullbackTensorLimitUnit l E X
        (((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)).obj C) ≫
      (coefficientSequenceLimit l E X).map
        ((pullbackTensorSequenceInverse l E g).mapDerivedCategoryFactors.inv.app C) ≫
      e.hom.app (DerivedCategory.Q.obj C) =
    DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex (podOrdinaryLimitReindexing l E g) (.up ℤ)).hom.app C) ≫
      (podCompletedModuleInverseImage l E g).mapDerivedCategoryFactors.inv.app
        (((pullbackTensorOrdinaryLimit l E Y).mapHomologicalComplex (.up ℤ)).obj C) ≫
      (podCompletedDerivedInverseImage l E g).map (pullbackTensorLimitUnit l E Y C)

/-- Exact reindexing commutes with functorial total derived limit, fixed on
resolutions and commuting with every actual finite reduction projection.
Source: node proof steps 8 and 13.
Proof: exact inverse reindexing transports null homotopies, hence K-injective
resolutions in the ordinary system category. Derive the single ordinary limit
comparison using those resolutions. The total derived-functor universal property
fixes the transformation by the displayed unit square, hence uniquely. The
ordinary projection equations give its derived projection equations. Inverse
reindexing gives its inverse. No equality of maps is inferred from finite
projections in a derived category.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podLimitReindexing_existsUnique :
    ∃! e : pullbackTensorSequenceDerived l E g ⋙ coefficientSequenceLimit l E X ≅
        coefficientSequenceLimit l E Y ⋙ podCompletedDerivedInverseImage l E g,
      PodLimitResolutionNormalization l E g e ∧
      ∀ (N : coefficientSequenceDerived l E Y) (n : ℕ),
        e.hom.app N ≫ (podCompletedDerivedInverseImage l E g).map
          ((coefficientSequenceProjection l E Y n).app N) =
        (coefficientSequenceProjection l E X n).app
          ((pullbackTensorSequenceDerived l E g).obj N) ≫
        (coefficientFiniteDerivedRestriction l E X n).map
          ((pullbackTensorDerivedEvaluation l E g n).hom.app N) ≫
        (podFiniteRestriction l E g n).hom.app
          ((coefficientSequenceDerivedEvaluation l E Y n).obj N) := by
  sorry

/-- The total derived-limit comparison fixed by resolutions and projections.
Source: node proof step 8 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podLimitReindexing := (podLimitReindexing_existsUnique l E g).exists.choose
end CompletedReindexing

end WeilConjectures

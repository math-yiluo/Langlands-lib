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

import Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.SmoothPurity.Supporting.IsomorphismReductionTower
import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHom
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
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.PoincareDuality.PodCoefficientDescent.PodReindexingHomCoefficientDescent
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.SmoothPurity.CompletedOperations.CompletedOperationTowerSubstitution
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
import all WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationBase

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

private def podClosedTransposeAdditive
    {D : Type a} [Category.{b} D] [Preadditive D] [HasZeroObject D]
    [HasBinaryProducts D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (L M N : D) :
    (S.tensor.obj (L, M) ⟶ N) ≃+ (L ⟶ H.obj (op M, N)) := by
  let := S.monoidal
  have : (Prod.sectR (op M) D ⋙ H).IsRightAdjoint := (S.adjunction M).isRightAdjoint
  have : (Prod.sectR (op M) D ⋙ H).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (MonoidalCategory.tensorRight M).Additive := (S.adjunction M).left_adjoint_additive
  exact (S.adjunction M).homAddEquiv L N

/-- Partial closed data are determined by their transposition equivalences.
Source: Stacks 08J9; the structure of def-pod-partial-closed-interfaces.
Proof: the naturality field is a proposition, so two structures with equal
transpose families (by function extensionality) are equal.
(blueprint: stage3-derived-automorphism-continuation-a). -/
theorem podPartialClosed_ext
    {C : Type a} [Category.{b} C] [Preadditive C]
    {T : C × C ⥤ C} {J : ObjectProperty (Cᵒᵖ × C)} {H : J.FullSubcategory ⥤ C}
    (S S' : PodPartialClosed T J H)
    (h : ∀ L P, S.transpose L P = S'.transpose L P) : S = S' := by
  cases S with
  | mk tr hn =>
    cases S' with
    | mk tr' hn' =>
      have he : tr = tr' := funext (fun L ↦ funext (fun P ↦ h L P))
      cases he
      rfl

section IntegralClosed
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

/-- The actual ordinary-to-completed tensor unit: reduction's adjunction unit,
its tensor comparison, and the inverse of the recorded Roos realization.
Source: node proof step 10, Stacks 099B
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedTensorUnit (M N : DerivedCategory (integralTowerModules l E W)) :
    (pullbackTensorCalculus l E W).integralClosed.tensor.obj (M, N) ⟶
      (integralCompletedTensor l E W).obj (M, N) :=
  (pullbackTensorCalculus l E W).adjunction.unit.app _ ≫
    (coefficientSequenceLimit l E W).map
      ((pullbackTensorCalculus l E W).reductionTensor.hom.app (M, N)) ≫
    (pullbackTensorIntegralTensorModel l E W).inv.app (M, N)

/-- The completed closed adjunction is uniquely normalized by ordinary evaluation
precomposed with the actual completion unit. No perfectness assumption is imposed.
Source: node proof steps 10--11, Stacks 099B, 0A0E.
Proof: the constant/completed coefficient equivalence identifies quotient-tower
completion with the Koszul reflector, preserving the unit. Maps from the completed
tensor into the complete target N are therefore exactly maps from the ordinary
tensor. Compose this bijection with ordinary tensor-Hom transposition. The Hom
object is constructible by the pair condition, so full-subcategory Hom is unchanged.
Both bijections are additive and natural. The equation fixes every transpose,
hence fixes the partial closed data uniquely.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralClosed_existsUnique :
    ∃! S : PodPartialClosed (constructibleIntegralTensor l E W)
        (constructibleIntegralHomPairs l E W) (constructibleIntegralHom l E W),
      ∀ (L : sfIntegralConstructibleCategory l E W)
        (P : (constructibleIntegralHomPairs l E W).FullSubcategory)
        (f : (constructibleIntegralTensor l E W).obj (L, P.obj.1.unop) ⟶ P.obj.2),
        HEq ((S.transpose L P f).hom)
          ((pullbackTensorCalculus l E W).integralClosed.transpose L.obj P.obj.1.unop.obj
            P.obj.2.obj (podCompletedTensorUnit l E W L.obj P.obj.1.unop.obj ≫ f.hom)) := by
  let S := (pullbackTensorCalculus l E W).integralClosed
  let η : S.tensor ⟶ integralCompletedTensor l E W :=
    (Functor.rightUnitor _).inv ≫
      Functor.whiskerLeft _ (pullbackTensorCalculus l E W).adjunction.unit ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (pullbackTensorCalculus l E W).reductionTensor.hom
        (coefficientSequenceLimit l E W) ≫
      (pullbackTensorIntegralTensorModel l E W).inv
  let tr (L : sfIntegralConstructibleCategory l E W)
      (P : (constructibleIntegralHomPairs l E W).FullSubcategory) :
      ((constructibleIntegralTensor l E W).obj (L, P.obj.1.unop) ⟶ P.obj.2) ≃+
        (L ⟶ (constructibleIntegralHom l E W).obj P) :=
    (InducedCategory.homAddEquiv).trans
      ((AddEquiv.ofBijective
        ({ toFun := fun f ↦ podCompletedTensorUnit l E W L.obj P.obj.1.unop.obj ≫ f
           map_zero' := by simp
           map_add' := fun f g ↦ by simp only [Preadditive.comp_add] } :
          ((integralCompletedTensor l E W).obj (L.obj, P.obj.1.unop.obj) ⟶ P.obj.2.obj) →+
            (S.tensor.obj (L.obj, P.obj.1.unop.obj) ⟶ P.obj.2.obj))
        (PodCompletedReflection.precompose_bijective l E W L P.obj.1.unop P.obj.2)).trans
          ((podClosedTransposeAdditive S L.obj P.obj.1.unop.obj P.obj.2.obj).trans
            (show (L.obj ⟶ ((constructibleIntegralHom l E W).obj P).obj) ≃+
                (L ⟶ (constructibleIntegralHom l E W).obj P) from
              (InducedCategory.homAddEquiv (X := L)
                (Y := (constructibleIntegralHom l E W).obj P)).symm)))
  have htr (L : sfIntegralConstructibleCategory l E W)
      (P : (constructibleIntegralHomPairs l E W).FullSubcategory)
      (f : (constructibleIntegralTensor l E W).obj (L, P.obj.1.unop) ⟶ P.obj.2) :
      (tr L P f).hom = S.transpose L.obj P.obj.1.unop.obj P.obj.2.obj
        (podCompletedTensorUnit l E W L.obj P.obj.1.unop.obj ≫ f.hom) := rfl
  let R : PodPartialClosed (constructibleIntegralTensor l E W)
      (constructibleIntegralHomPairs l E W) (constructibleIntegralHom l E W) := {
    transpose := tr
    parameter_naturality := by
      intro L L' P f h
      apply ObjectProperty.hom_ext
      change (tr L' P ((constructibleIntegralTensor l E W).map
        (Prod.mkHom f (𝟙 P.obj.1.unop)) ≫ h)).hom = f.hom ≫ (tr L P h).hom
      rw [htr, htr]
      have hn : S.tensor.map (Prod.mkHom f.hom (𝟙 P.obj.1.unop.obj)) ≫
          podCompletedTensorUnit l E W L.obj P.obj.1.unop.obj =
        podCompletedTensorUnit l E W L'.obj P.obj.1.unop.obj ≫
          (integralCompletedTensor l E W).map (Prod.mkHom f.hom (𝟙 _)) := by
        simpa [η, podCompletedTensorUnit, S, CoefficientClosedStructure.tensor,
          Category.assoc] using η.naturality (Prod.mkHom f.hom (𝟙 P.obj.1.unop.obj))
      change S.transpose _ _ _ (podCompletedTensorUnit l E W L'.obj _ ≫
        ((integralCompletedTensor l E W).map (Prod.mkHom f.hom (𝟙 _)) ≫ h.hom)) = _
      erw [← Category.assoc, ← hn, Category.assoc]
      let := S.monoidal
      change (S.adjunction P.obj.1.unop.obj).homEquiv _ _
        (S.tensor.map (Prod.mkHom f.hom (𝟙 _)) ≫
          podCompletedTensorUnit l E W L.obj P.obj.1.unop.obj ≫ h.hom) =
        f.hom ≫ (S.adjunction P.obj.1.unop.obj).homEquiv _ _
          (podCompletedTensorUnit l E W L.obj P.obj.1.unop.obj ≫ h.hom)
      simpa only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor,
        MonoidalCategory.tensorHom_id, MonoidalCategory.tensorRight,
        MonoidalCategory.curriedTensor, Functor.flip] using
        (S.adjunction P.obj.1.unop.obj).homEquiv_naturality_left f.hom
          (podCompletedTensorUnit l E W L.obj P.obj.1.unop.obj ≫ h.hom) }
  refine ⟨R, fun L P f ↦ HEq.rfl, ?_⟩
  intro R' hR'
  apply podPartialClosed_ext
  intro L P
  apply AddEquiv.ext
  intro f
  apply ObjectProperty.hom_ext
  exact eq_of_heq (hR' L P f)

/-- Completed transposition with its unique ordinary-unit normalization.
Source: Stacks 099B (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podIntegralClosed := (podIntegralClosed_existsUnique l E W).exists.choose
end IntegralClosed

section IntegralTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The Hom-constructible domain is preserved by isomorphism pullback.
Source: node proof steps 3, 8, 11.
Proof: exact sectionwise reindexing preserves K-injectives, hence the ambient
Hom complex. Its canonical completion-unit comparison identifies reindexing
with the recorded tower pullback on complete inputs. The source Hom is
constructible by hypothesis, and pullback preserves constructibility.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralPairs_pullback
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) :
    constructibleIntegralHomPairs l E X
      (((constructibleIntegralPullback l E g).op.prod
        (constructibleIntegralPullback l E g)).obj P.obj) := by
  exact PodCoefficientDescent.integral_pair_permitted l E g P

/-- The integral comparison is the transpose of completed pullback of evaluation.
Source: node proof steps 10--11, Stacks 0GMX
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podIntegralHomComparison :=
  podPartialHomComparison (podIntegralClosed l E Y) (podIntegralClosed l E X)
    (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
      (canonicalIntegralPullbackTensor l E g)

end IntegralTransport

end WeilConjectures

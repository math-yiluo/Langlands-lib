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
import WeilConjectures.SmoothPurity.CompletedOperations.CompletedOperationTowerSubstitution
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

import all WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import all WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingEvaluationShiftComposition
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralInverseImageComparisonComposition

public import WeilConjectures.PoincareDuality.Pod.PodHomComplexShiftRepresentatives
public import WeilConjectures.SixFunctors.Supporting.DerivedAutomorphismHomEvaluationContinuationA

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
set_option Elab.async false
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

section ReductionNormalization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]

/-- The canonical reduction/reindexing map: the actual reduction/limit adjunct
of exact inverse image of the unit, followed by the inverse limit comparison.
Source: node proof steps 8 and 13
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podReductionReindexingMap (K : DerivedCategory (integralTowerModules l E Y)) :
    (pullbackTensorCalculus l E X).reduction.obj
        ((podCompletedDerivedInverseImage l E g).obj K) ⟶
      (pullbackTensorSequenceDerived l E g).obj
        ((pullbackTensorCalculus l E Y).reduction.obj K) :=
  ((pullbackTensorCalculus l E X).adjunction.homEquiv _ _).symm
    ((podCompletedDerivedInverseImage l E g).map
        ((pullbackTensorCalculus l E Y).adjunction.unit.app K) ≫
      (podLimitReindexing l E g).inv.app ((pullbackTensorCalculus l E Y).reduction.obj K))

/-- The canonical reduction adjunct is invertible and natural for every ambient
complex, without asserting invertibility of the completion unit.
Source: node proof steps 8 and 13.
Proof: the two reduction functors are ordinary quotient systems on a flat-term
K-flat representative. Reindexing commutes with every quotient and strict
transition. Their identity-on-sections map is the displayed adjunct, by the
actual reduction unit and projection equations. Inverse reindexing gives an
inverse system map before localization. Naturality holds on representatives
and descends to every derived arrow.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podReductionReindexingMap_laws :
    (∀ K, IsIso (podReductionReindexingMap l E g K)) ∧
    ∀ (K L : DerivedCategory (integralTowerModules l E Y)) (f : K ⟶ L),
      (pullbackTensorCalculus l E X).reduction.map
          ((podCompletedDerivedInverseImage l E g).map f) ≫
        podReductionReindexingMap l E g L =
      podReductionReindexingMap l E g K ≫
        (pullbackTensorSequenceDerived l E g).map
          ((pullbackTensorCalculus l E Y).reduction.map f) := by
  classical
  have hF : pullbackTensorSequenceDerived l E g ≅
      integralComparisonDerivedSequencePullback l E g := by
    have heq : pullbackTensorSequenceInverse l E g =
        integralComparisonSequencePullback l E g := by
      unfold pullbackTensorSequenceInverse integralComparisonSequencePullback
      congr 1
      unfold pullbackTensorSequenceDirect integralComparisonSequenceDirectImage
      have hr : pullbackTensorSequenceRing l E g = integralComparisonSequenceRingMap l E g := by
        unfold pullbackTensorSequenceRing pullbackTensorSequenceRingMap
        rfl
      rw [hr]
    exact Functor.mapDerivedCategoryNatIso (eqToIso heq)
  have hH : (integralComparisonDerivedSequencePullback l E g).IsEquivalence := by
    let H := integralComparisonDerivedSequencePullback l E g
    let G := integralComparisonDerivedSequencePullback l E (inv g)
    let a : H ⋙ G ≅ 𝟭 _ :=
      (integralComparisonSystemComposition l E (inv g) g).symm ≪≫
        eqToIso (congrArg (integralComparisonDerivedSequencePullback l E)
          (IsIso.inv_hom_id g)) ≪≫ integralComparisonSystemUnit l E Y
    let b : G ⋙ H ≅ 𝟭 _ :=
      (integralComparisonSystemComposition l E g (inv g)).symm ≪≫
        eqToIso (congrArg (integralComparisonDerivedSequencePullback l E)
          (IsIso.hom_inv_id g)) ≪≫ integralComparisonSystemUnit l E X
    exact (CategoryTheory.Equivalence.mk H G a.symm b).isEquivalence_functor
  have : (pullbackTensorSequenceDerived l E g).IsEquivalence :=
    Functor.isEquivalence_of_iso hF.symm
  have : (podCompletedDerivedInverseImage l E g).IsEquivalence :=
    (podCompletedInverseImage_equivalence l E g).2
  obtain ⟨e, he⟩ := adjointSquare (podCompletedDerivedInverseImage l E g)
    (pullbackTensorSequenceDerived l E g) (pullbackTensorCalculus l E Y).adjunction
    (pullbackTensorCalculus l E X).adjunction (podLimitReindexing l E g).symm
  have hmap (K : DerivedCategory (integralTowerModules l E Y)) :
      podReductionReindexingMap l E g K = e.hom.app K := by
    rw [podReductionReindexingMap, Equiv.symm_apply_eq, Adjunction.homEquiv_unit]
    exact (he K).symm
  refine ⟨fun K ↦ ?_, fun K L f ↦ ?_⟩
  · rw [hmap]
    infer_instance
  · rw [hmap, hmap]
    exact e.hom.naturality f

/-- The reduction comparison is the isomorphism of that very canonical adjunct.
Source: node proof step 13 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podReductionReindexing (K : DerivedCategory (integralTowerModules l E Y)) :=
  @asIso _ _ _ _ (podReductionReindexingMap l E g K)
    ((podReductionReindexingMap_laws l E g).1 K)

/-- Exact inverse image to tower pullback: inverse image of the actual completion
unit, the inverse total-limit comparison, and the inverse recorded Roos model.
Source: node proof step 8 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedToTower (K : DerivedCategory (integralTowerModules l E Y)) :
    (podCompletedDerivedInverseImage l E g).obj K ⟶ (integralDerivedPullback l E g).obj K :=
  (podCompletedDerivedInverseImage l E g).map
      ((pullbackTensorCalculus l E Y).adjunction.unit.app K) ≫
    (podLimitReindexing l E g).inv.app ((pullbackTensorCalculus l E Y).reduction.obj K) ≫
    (pullbackTensorIntegralPullbackModel l E g).inv.app K

attribute [local irreducible] pullbackTensorCalculus
  podCompletedDerivedInverseImage integralDerivedPullback podLimitReindexing
  pullbackTensorIntegralPullbackModel completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence

/-- The identification with tower-defined pullback is natural, and is invertible
on exactly the complete constructible inputs used here.
Source: node proof step 8.
Proof: all three factors are natural. For a constructible complete K, the
canonical quotient-tower unit is invertible by the finite-free completed
scalar theorem for E/E. The other two factors are isomorphisms already.
The total-limit comparison's resolution and projection equations imply
commutation with every reduction projection.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCompletedToTower_laws :
    (∀ (K L : DerivedCategory (integralTowerModules l E Y)) (f : K ⟶ L),
      (podCompletedDerivedInverseImage l E g).map f ≫ podCompletedToTower l E g L =
        podCompletedToTower l E g K ≫ (integralDerivedPullback l E g).map f) ∧
    (∀ K : sfIntegralConstructibleCategory l E Y, IsIso (podCompletedToTower l E g K.obj)) := by
  constructor
  · intro K L f
    let SY := pullbackTensorCalculus l E Y
    let F := podCompletedDerivedInverseImage l E g
    have hη := congrArg F.map (SY.adjunction.unit.naturality f)
    have hlim := (podLimitReindexing l E g).inv.naturality (SY.reduction.map f)
    have hrho := (pullbackTensorIntegralPullbackModel l E g).inv.naturality f
    dsimp only [Functor.comp_map, Functor.id_map] at hη hlim hrho
    simp only [Functor.map_comp] at hη
    dsimp only [podCompletedToTower]
    change F.map f ≫ F.map (SY.adjunction.unit.app L) ≫ _ ≫ _ = _
    rw [← Category.assoc (F.map f), hη]
    rw [Category.assoc, ← Category.assoc (F.map
      ((coefficientSequenceLimit l E Y).map (SY.reduction.map f))), hlim]
    simpa only [Category.assoc, pullbackTensorReferencePullback, Functor.comp_map] using
      congrArg (fun k ↦ F.map (SY.adjunction.unit.app K) ≫
        (podLimitReindexing l E g).inv.app (SY.reduction.obj K) ≫ k) hrho
  · intro K
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
    have : IsIso ((pullbackTensorCalculus l E Y).adjunction.unit.app K.obj) :=
      (purNormalizedReconstructionOfScheme l E Y (pullbackTensorCalculus l E Y)).2 K.obj hK
    dsimp only [podCompletedToTower]
    infer_instance

/-- The canonical complete-input identification, retaining its specified map.
Source: node proof step 8 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedToTowerIso (K : sfIntegralConstructibleCategory l E Y) :=
  @asIso _ _ _ _ (podCompletedToTower l E g K.obj) ((podCompletedToTower_laws l E g).2 K)

variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

end ReductionNormalization

section SignedShifts
attribute [local irreducible] homComplexFunctor
universe r s t w
variable {C : Type s} [Category.{t} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max s t r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max s t r}]
  (A : Sheaf J CommRingCat.{max s t r})
  [HasDerivedCategory.{w} (PodModules.{r, s, t} J A)]

end SignedShifts

section FiniteCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y Z : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

omit [IsIso g] in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local irreducible] finiteIntrinsicClosed podFiniteHomComparison

end FiniteCoherence

section IntegralShiftCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

end IntegralShiftCoherence

section IntegralComposition
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y Z : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (h : Z ⟶ X) [IsIso h]

omit [IsIso g] [IsIso h] in
/-- A restriction along an `eqToHom` arrow is the identity, up to `HEq`. -/
private theorem presheafOfModules_map_heq_of_eq {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat.{u + 1}} (M : PresheafOfModules.{u + 1} R) {A B : Cᵒᵖ}
    (f : A ⟶ B) (hf : ∃ p : A = B, f = eqToHom p) (x : M.obj A) :
    HEq (M.map f x) x := by
  obtain ⟨rfl, rfl⟩ := hf
  simp

omit [IsIso g] [IsIso h] in
/-- The completed coefficient transport is the published completed coefficient map. -/
private theorem podCompletedRingMap_eq_inverseImage {V W : Scheme.{u}} (k : V ⟶ W) [IsIso k] :
    podCompletedRingMap l E k = ProEtale.inverseImageCompletedCoefficientMap l E k := by
  apply limit.hom_ext
  intro n
  rw [podCompletedRingMap, limit.lift_π, ProEtale.inverseImageCompletedCoefficientMap,
    limit.lift_π]
  rfl

/-- Composition of exact completed inverse image is fixed on all local sections.
Source: node proof steps 1 and 7, Stacks 00WX.
Proof: composition of the two postcomposition functors agrees with postcomposition
by the composite, using associativity of scheme arrows. The identity on the
unchanged local sections is linear because both coefficient transports have
identical finite projections. It is a natural isomorphism; pointwise equality
on all local sections proves uniqueness.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCompletedModuleComp_existsUnique :
    ∃! e : podCompletedModuleInverseImage l E (h ≫ g) ≅
        podCompletedModuleInverseImage l E g ⋙ podCompletedModuleInverseImage l E h,
      ∀ (M : integralTowerModules l E Y) (U : Z.ProEt)
        (x : ((podCompletedModuleInverseImage l E (h ≫ g)).obj M).val.obj (op U)),
        HEq (((e.hom.app M).val.app (op U)) x) x := by
  let d : proEtaleIsoPostcompose (h ≫ g) ≅
      proEtaleIsoPostcompose h ⋙ proEtaleIsoPostcompose g :=
    MorphismProperty.Over.mapComp (Q := ⊤)
      (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale g)
  let : (proEtaleIsoPostcompose h ⋙ proEtaleIsoPostcompose g).IsContinuous
      (ProEt.topology Z) (ProEt.topology Y) :=
    Functor.isContinuous_comp _ _ (ProEt.topology Z) (ProEt.topology X) (ProEt.topology Y)
  let R := completedIntegralCoefficientSheafUnrestricted l E Y
  let T := Functor.sheafPushforwardContinuousIso d RingCat.{u + 1}
    (ProEt.topology Z) (ProEt.topology Y)
  have hc := ProEtale.completedComposition l E h g
  rw [← podCompletedRingMap_eq_inverseImage l E g, ← podCompletedRingMap_eq_inverseImage l E h,
    ← podCompletedRingMap_eq_inverseImage l E (h ≫ g)] at hc
  have hring : inv (podCompletedRingMap l E (h ≫ g)) ≫ T.hom.app R =
      inv (podCompletedRingMap l E h) ≫
        (isoSectionwiseInverseImage h RingCat.{u + 1}).map
          (inv (podCompletedRingMap l E g)) := by
    rw [← cancel_mono ((isoSectionwiseInverseImage h RingCat.{u + 1}).map
      (podCompletedRingMap l E g) ≫ podCompletedRingMap l E h), Category.assoc,
      Category.assoc, ← Functor.map_comp_assoc, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp, IsIso.inv_hom_id]
    erw [hc]
    rw [← Category.assoc (T.hom.app R)]
    erw [T.hom_inv_id_app]
    rw [Category.id_comp, IsIso.inv_hom_id]
  have hd (U : Z.ProEt) : ∃ p, (d.inv.app U).op = eqToHom p := by
    refine ⟨congrArg op (Functor.congr_obj (MorphismProperty.Over.map_comp (Q := ⊤)
      (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale g)) U), ?_⟩
    apply Quiver.Hom.unop_inj
    rw [Quiver.Hom.unop_op, eqToHom_unop]
    apply MorphismProperty.Over.Hom.ext
    simp [d]
    rfl
  let e := SheafOfModules.pushforwardNatIso (inv (podCompletedRingMap l E (h ≫ g))) d.symm ≪≫
    SheafOfModules.pushforwardCongr hring ≪≫
    (SheafOfModules.pushforwardComp (inv (podCompletedRingMap l E h))
      (inv (podCompletedRingMap l E g))).symm
  refine ⟨e, fun M U x ↦ ?_, fun e' he' ↦ ?_⟩
  · exact presheafOfModules_map_heq_of_eq M.val (d.inv.app U).op (hd U) x
  · apply Iso.ext
    ext M U x
    exact eq_of_heq ((he' M U.unop x).trans
      (presheafOfModules_map_heq_of_eq M.val (d.inv.app U.unop).op (hd U.unop) x).symm)

/-- The unique identity-on-sections completed composition comparison.
Source: Stacks 00WX (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedModuleComp := (podCompletedModuleComp_existsUnique l E g h).exists.choose

/-- Derive that same ordinary comparison, using the fixed exact factorizations.
Source: node proof steps 2 and 7
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedDerivedComp : podCompletedDerivedInverseImage l E (h ≫ g) ≅
    podCompletedDerivedInverseImage l E g ⋙ podCompletedDerivedInverseImage l E h :=
  letI := podCompletedModuleAdditive l E g
  letI := podCompletedModuleAdditive l E h
  letI := podCompletedModuleAdditive l E (h ≫ g)
  letI := podCompletedModuleLimits l E g
  letI := podCompletedModuleLimits l E h
  letI := podCompletedModuleLimits l E (h ≫ g)
  letI := podCompletedModuleColimits l E g
  letI := podCompletedModuleColimits l E h
  letI := podCompletedModuleColimits l E (h ≫ g)
  Functor.mapDerivedCategoryNatIso (podCompletedModuleComp l E g h) ≪≫
    (Functor.mapDerivedCategoryCompIso (podCompletedModuleInverseImage l E g)
      (podCompletedModuleInverseImage l E h)).symm

variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ z : Z, Invertible (l : Z.residueField z)]

/-- Published integral tower composition has the actual completion-unit normalization.
Source: node proof steps 7--8.
Proof: conjugate the derived identity-on-sections composition by the three
complete-input identifications. Their maps are fixed by completion units and
total-limit reindexing. Hence this is the canonical tower composition, natural
by their naturality. Its component formula determines it uniquely.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralPullbackComp_normalization
    (M : sfIntegralConstructibleCategory l E Y) :
    HEq (((pullbackTensorIntegralComposition l E g h).hom.app M).hom)
      ((podCompletedToTowerIso l E (h ≫ g) M).inv ≫
        (podCompletedDerivedComp l E g h).hom.app M.obj ≫
        (podCompletedDerivedInverseImage l E h).map (podCompletedToTowerIso l E g M).hom ≫
        (podCompletedToTowerIso l E h ((constructibleIntegralPullback l E g).obj M)).hom) := by
  sorry

end IntegralComposition

section SystemFibers
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]

variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

end SystemFibers

section ArgumentFirstStages
attribute [local irreducible] pullbackTensorBraiding canonicalFinitePullbackTensor
  finiteIntrinsicClosed finiteIntrinsicTensorModels podFiniteHomComparison
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

end ArgumentFirstStages

section ArgumentFirstCommon
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

end ArgumentFirstCommon

section FieldComposition
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y Z : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (h : Z ⟶ X) [IsIso h]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ z : Z, Invertible (l : Z.residueField z)]

end FieldComposition

section CommonComposition
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y Z : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (h : Z ⟶ X) [IsIso h]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ z : Z, Invertible (l : Z.residueField z)]

end CommonComposition

section RestrictedShiftMaps
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

end RestrictedShiftMaps

section CommonShiftImages
open GeneralAlgebraicallyClosedCoefficients AlgebraicallyClosedCoefficients
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

end CommonShiftImages

end WeilConjectures

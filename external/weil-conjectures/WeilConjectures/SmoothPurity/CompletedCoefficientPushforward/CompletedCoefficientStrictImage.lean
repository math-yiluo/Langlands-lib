/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardModels
import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientOrdinaryStrictImage
import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientSystemRestrictionAcyclic
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
import WeilConjectures.Algebra.Homology.System.SystemGrothendieck
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import all WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import all WeilConjectures.CategoryTheory.Diagram.DiagramRingRestrictionPushforward

/-! # Direct image of strict semilinear coefficient systems

Source: Stacks Project, Cohomology on Sites, Tag 0D6E, on sequence ringed topoi.
(blueprint: lem-pur-completed-coefficient-strict-image).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a av b bv c cv z zv d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedCoefficientPushforward
-- Keep the categorical normalization abstract: kernel checking need not expand the
-- concrete sheaf categories and coefficient presentations at every cancellation.
private theorem normalizedSquare_exists
    {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{d} A]
    {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{d} B]
    {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{d} C]
    {D : Type z} [Category.{zv} D] [Abelian D] [HasDerivedCategory.{d} D]
    [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) (G : C ⥤ D) (U : A ⥤ C) (V : B ⥤ D)
    [F.Additive] [G.Additive] [U.Additive] [V.Additive]
    (RF : RightImage F) (RG : RightImage G) (DU : ExactImage U) (DV : ExactImage V)
    (ordinary : F ⋙ V ≅ U ⋙ G)
    (hG : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (RG.unit.app ((U.mapHomologicalComplex (.up ℤ)).obj I))) :
    ∃ S : Square F G U V RF RG DU DV, S.ordinary = ordinary := by
  obtain ⟨e, he, -⟩ := CategoryTheory.derivedCoefficientComparison F G U V
    DU.functor DV.functor DU.factors DV.factors RF.functor RG.functor
    RF.unit RG.unit RF.computes hG ordinary
  refine ⟨⟨ordinary, e, ?_⟩, rfl⟩
  intro K
  have h := congrArg (fun a ↦ DV.factors.hom.app
    ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫ a ≫
      RG.functor.map (DU.factors.hom.app K)) (he K)
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app] at h
  erw [RG.functor.map_id, Category.comp_id] at h
  exact h

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private instance systemsGrothendieck (W : Scheme.{t}) :
    IsGrothendieckAbelian.{max u (t + 1)} (Systems l E W) := by
  let : EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf _
  let := integralCoefficientAbSheafify.{t, u} W
  let := integralCoefficientAbLocallyBijective.{t, u} W
  let := SheafOfModules.strictRingSystem_isGrothendieckAbelian
    (SheafOfModules.coefficientRings (J := ProEt.topology W)
      (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E))
  exact IsGrothendieckAbelian.of_equivalence
    (SheafOfModules.coefficientSystemEquivalence (J := ProEt.topology W)
      (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E)).symm

/-- The system part of the comparison, for fixed coefficient and tower images.
It retains all transitions before evaluation and contains no inverse-limit data.
Source: Stacks Project, Cohomology on Sites, Tag 0D6E; Zheng Construction 4.1
(blueprint: def-pur-completed-coefficient-strict-image-data). -/
structure StrictImageData {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientComparisonData l E f)
    (towerImage : RightImage
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f C.structureMap))) where
  systemPush : Systems l E X ⥤ Systems l E Y
  [systemPushAdditive : systemPush.Additive]
  systemPushEvaluation : ∀ n,
    systemPush ⋙
      SheafOfModules.coefficientEvaluation.{t + 1, t, max u (t + 1)} (J := ProEt.topology Y)
      (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E) n ⋙
        model l E Y n (C.target.finiteIso n) ≅
      SheafOfModules.coefficientEvaluation.{t + 1, t, max u (t + 1)} (J := ProEt.topology X)
        (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E) n ⋙
          model l E X n (C.source.finiteIso n) ⋙ push f (finiteStructure l E f n)
  systemPushEvaluation_identity : ∀ n,
    IsSectionwiseIdentity Y (N l E Y n) (systemPushEvaluation n).hom
  systemImage : RightImage systemPush
  diagramSquare : Square systemPush
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f C.structureMap))
    C.source.systemRestriction C.target.systemRestriction systemImage towerImage
    C.source.systemFactors C.target.systemFactors
  diagramOrdinary_identity : ∀ (M : Systems l E X) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : ((C.target.systemRestriction.obj (systemPush.obj M)).obj (op n)).val.obj U),
      HEq ((((diagramSquare.ordinary.hom.app M).app (op n)).val.app U) x) x

/-- Extend the fixed coefficient comparisons to the strict-system square, with its
sectionwise identity and evaluation identifications. The tower right image is supplied;
there is no evaluation or limit comparison for that tower in this conclusion.

Source: Stacks Project, Cohomology on Sites, Tag 0D6E, on diagram sites;
Zheng Construction 4.1
(blueprint: lem-pur-completed-coefficient-strict-image).

Proof: Apply direct image to the sheaf at each coefficient level, using the constant
structural map of that quotient. The naturality of constant structural maps with respect
to quotient maps makes the old semilinear transitions into transitions of the image.
This defines the ordinary system functor and its additive action on morphisms.
Transport each level by the supplied finiteIso. Its generator equation and naturality
of constant sections identify the transported finite ring maps with finiteStructure.
Thus systemPushEvaluation has identity underlying sections. Realize systems as modules
over the quotient-ring diagram on the sequence site. The compatible completed
projections give its ring map from the constant completed-ring diagram. Restriction
along that map is the supplied systemRestriction: systemEvaluation_identity,
systemTransition and systemMap identify both functors on objects, transitions and maps.
The two factorizations of the common diagram direct image therefore have an ordinary
comparison with identity sections. Derive the square on diagram sites using normalized
ringed-topos composition, before evaluating. Identify its exact restrictions and tower
image with the supplied factors and universal unit. This gives diagramSquare and its
normalization. Nothing requires normalized coefficient systems or bounded complexes. -/
theorem strictImage_exists {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientComparisonData l E f)
    (towerImage : RightImage
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f C.structureMap))) :
    Nonempty (StrictImageData l E f C towerImage) := by
  obtain ⟨S⟩ := ordinaryStrictImage_exists l E f C
  let := C.completedAdditive
  obtain ⟨RF, η, hRF, hI, -⟩ := CategoryTheory.totalDerivedData S.systemPush
  let systemImage : RightImage S.systemPush := ⟨RF, η, hRF, hI⟩
  obtain ⟨square, hsquare⟩ := normalizedSquare_exists
    S.systemPush ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f C.structureMap))
    C.source.systemRestriction C.target.systemRestriction
    systemImage towerImage C.source.systemFactors C.target.systemFactors S.diagramOrdinary
    (systemRestriction_push_acyclic l E f C.source.toSystemRestrictionData
      C.structureMap towerImage)
  exact ⟨{
    systemPush := S.systemPush
    systemPushAdditive := S.systemPushAdditive
    systemPushEvaluation := S.systemPushEvaluation
    systemPushEvaluation_identity := S.systemPushEvaluation_identity
    systemImage := systemImage
    diagramSquare := square
    diagramOrdinary_identity := by
      simpa only [hsquare] using S.diagramOrdinary_identity }⟩

end WeilConjectures.CompletedCoefficientPushforward

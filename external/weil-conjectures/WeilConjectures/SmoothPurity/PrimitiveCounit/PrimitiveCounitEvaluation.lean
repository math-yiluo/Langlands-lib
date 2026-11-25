/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerCanonical
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.StrictRoosComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
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
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.StrictRoosNormalization
public import WeilConjectures.AlgebraicGeometry.ProEtale.Coefficient.ProEtaleCoefficientPullbackExact
import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation

/-! # Quotient-limit realization and primitive coherent-counit comparisons

Source: Stacks Project, sites-cohomology.tex, Tag 0941, lemma-derived-limit-is-ok,
with the strict Roos normalization and the coherent coefficient-system adjunction
(blueprint: lem-pur-completed-primitive-counit-comparison).

Natural number n means positive coefficient exponent n+1. All systems are derived
before evaluation, and the site has independent object and morphism universes t+1 and t.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived

universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
private theorem pushforwardComp_eq
    {C D H : Type (t + 1)} [Category.{t} C] [Category.{t} D] [Category.{t} H]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : GrothendieckTopology H} {F : C ⥤ D} {G : D ⥤ H}
    [F.IsContinuous J K] [G.IsContinuous K L]
    {A : Sheaf J RingCat.{u}} {B : Sheaf K RingCat.{u}} {R : Sheaf L RingCat.{u}}
    (φ : A ⟶ (F.sheafPushforwardContinuous RingCat J K).obj B)
    (ψ : B ⟶ (G.sheafPushforwardContinuous RingCat K L).obj R) :
    letI := Functor.isContinuous_comp F G J K L
    SheafOfModules.pushforward.{u} ψ ⋙ SheafOfModules.pushforward.{u} φ =
      SheafOfModules.pushforward.{u} (F := F ⋙ G)
        (φ ≫ (F.sheafPushforwardContinuous RingCat J K).map ψ) := by
  unfold SheafOfModules.pushforward
  rfl

attribute [local irreducible] Padic constantSheaf HasDerivedCategory.standard
  Scheme.coefficientProEtaleDirectRingMap
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
namespace WeilConjectures
attribute [local irreducible] integralCompletedTensor integralCompletedTensorComparison
  integralDerivedPullback integralDerivedPullbackComparison
namespace PrimitiveCounit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual base-change functor of the vertical sequence sites.
Source: Stacks 0941 and 09A5
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def base {X Y : Scheme.{t}} (f : X ⟶ Y) : ℕ × Y.ProEt ⥤ ℕ × X.ProEt :=
  (𝟭 ℕ).prod (Scheme.proEtaleBaseChange f)

/-- Vertical sequence base change is continuous.
Source: Stacks 0941 and 09A5
(blueprint: lem-pur-completed-primitive-counit-comparison).
Proof: restrict a vertical covering sieve to its fixed coefficient level. Its image
is a pro-etale covering by continuity of pro-etale base change. Horizontal arrows
keep the same level, so the slice sheaf conditions assemble on the sequence site. -/
theorem base_continuous {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (base f).IsContinuous (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X)) := by
  exact integralComparisonSequenceBaseChange_continuous f

attribute [instance] base_continuous

/-- The sequence ring's section at (n,U) is the actual finite constant-ring section.
Source: Stacks 0941 (blueprint: lem-pur-completed-primitive-counit-comparison).
Proof: unfold the sequence presheaf, uncurry and ofOpSequence at the object (n,U).
The object is the finite constant sheaf evaluated at U; no transition is involved. -/
theorem section_eq (W : Scheme.{t}) (U : (ℕ × W.ProEt)ᵒᵖ) :
    (coefficientSequenceCommRingSheaf l E W).obj.obj U =
      ((constantSheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1}
          (Padic.coefficientExtensionRing l E (U.unop.1 + 1))))).obj.obj (op U.unop.2) := by
  unfold coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  rfl

/-- The constant-section component, transported through the explicit section identity.
Source: Stacks 0H7J, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def ringComponent {X Y : Scheme.{t}} (f : X ⟶ Y) (U : (ℕ × Y.ProEt)ᵒᵖ) :
    (coefficientSequenceCommRingSheaf l E Y).obj.obj U ⟶
      (coefficientSequenceCommRingSheaf l E X).obj.obj ((base f).op.obj U) :=
  eqToHom (section_eq l E Y U) ≫
    (Scheme.coefficientProEtaleDirectRingMap.{t, u} f
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (U.unop.1 + 1))))).hom.app (op U.unop.2) ≫
    eqToHom (section_eq l E X ((base f).op.obj U)).symm

attribute [local semireducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf

/-- Constant-section components respect vertical and quotient arrows simultaneously.
Source: Stacks 0H7J, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison).
Proof: vertical naturality is that of the constant-section map; horizontal naturality
is its naturality in the coefficient ring, checked under sheafification adjunction.
Both transposes send a coefficient to the same constant section after quotient. -/
theorem ringMap_natural {X Y : Scheme.{t}} (f : X ⟶ Y)
    {U V : (ℕ × Y.ProEt)ᵒᵖ} (a : U ⟶ V) :
    (coefficientSequenceCommRingSheaf l E Y).obj.map a ≫ ringComponent l E f V =
      ringComponent l E f U ≫
        (coefficientSequenceCommRingSheaf l E X).obj.map ((base f).op.map a) := by
  exact integralComparisonSequenceRing_naturality l E f a

/-- The sequence ring map assembled from the actual constant-section components.
Source: Stacks 0H7J, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def ringMap {X Y : Scheme.{t}} (f : X ⟶ Y) :
    coefficientSequenceCommRingSheaf l E Y ⟶
      ((base f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj
          (coefficientSequenceCommRingSheaf l E X) :=
  ⟨{ app := ringComponent l E f
     naturality := fun {_ _} a ↦ ringMap_natural l E f a }⟩

/-- Canonical sectionwise system direct image with restricted coefficient action.
Source: Stacks 03D7, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def direct {X Y : Scheme.{t}} (f : X ⟶ Y) :
    coefficientSequenceModules l E X ⥤ coefficientSequenceModules l E Y :=
  SheafOfModules.pushforward (F := base f)
    ⟨Functor.whiskerRight (ringMap l E f).hom
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩

/-- The system inverse image is the left adjoint to this specified direct image.
Source: Stacks 03D3 and 0941
(blueprint: lem-pur-completed-primitive-counit-comparison).
Proof: transport the vertical sequence sites to coefficient-sized skeletons.
Module left Kan extension followed by module sheafification gives a left adjoint
to the displayed pushforward. Transport back along the site equivalences. This
retains all quotient arrows and the prescribed scalar action. -/
theorem direct_isRightAdjoint {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (direct l E f).IsRightAdjoint := by
  exact integralComparisonSequenceDirectImage_isRightAdjoint l E f

attribute [instance] direct_isRightAdjoint

/-- Geometric inverse image on whole strict systems, defined by its universal property.
Source: Stacks 03D3, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def inverse {X Y : Scheme.{t}} (f : X ⟶ Y) := (direct l E f).leftAdjoint

/-- Constant-coefficient geometric inverse image is exact on whole systems.
Source: Stacks 03D2, 0941; lem-coef-semilinear-derived-sections
(blueprint: lem-pur-completed-primitive-counit-comparison).
Proof: evaluation of the adjunction identifies its left adjoint with the canonical
finite-level module inverse image. Those functors are exact for constant coefficients.
Kernels and cokernels of systems are computed at every level. Their comparisons
are therefore isomorphisms. The additive right adjoint makes the left adjoint additive. -/
theorem inverse_exact {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (inverse l E f).Additive ∧ PreservesFiniteLimits (inverse l E f) ∧
      PreservesFiniteColimits (inverse l E f) := by
  exact integralComparisonSequencePullback_exact l E f

/-- Additivity of geometric system inverse image.
Source: Stacks 03D2, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
instance inverseAdditive {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (inverse l E f).Additive := (inverse_exact l E f).1

/-- Left exactness of geometric system inverse image.
Source: Stacks 03D2, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
instance inverseLimits {X Y : Scheme.{t}} (f : X ⟶ Y) :
    PreservesFiniteLimits (inverse l E f) := (inverse_exact l E f).2.1

/-- Right exactness of geometric system inverse image.
Source: Stacks 03D2, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
instance inverseColimits {X Y : Scheme.{t}} (f : X ⟶ Y) :
    PreservesFiniteColimits (inverse l E f) := (inverse_exact l E f).2.2

/-- The exact geometric inverse image on ordinary unbounded derived whole systems.
Source: Stacks 03D2, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def pull {X Y : Scheme.{t}} (f : X ⟶ Y) :
    coefficientSequenceDerived l E Y ⥤ coefficientSequenceDerived l E X :=
  (inverse l E f).mapDerivedCategory

/-- Additivity of finite geometric inverse image from its existing adjunction theorem.
Source: Stacks 03D2 (blueprint: lem-pur-completed-primitive-counit-comparison). -/
instance levelAdditive {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    (integralOperationsLevelPullback l E f n).Additive :=
  integralOperationsLevelPullback_additive l E f n

/-- Exactness at each finite constant coefficient, for the derived evaluation formula.
Source: Stacks 03D2 (blueprint: lem-pur-completed-primitive-counit-comparison). -/
instance levelLimits {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    PreservesFiniteLimits (integralOperationsLevelPullback l E f n) :=
  (Scheme.coefficientProEtaleModulePullback_exact.{t, u} f
    (CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionRing l E (n + 1))))).1

/-- Right exactness at each finite constant coefficient.
Source: Stacks 03D2 (blueprint: lem-pur-completed-primitive-counit-comparison). -/
instance levelColimits {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    PreservesFiniteColimits (integralOperationsLevelPullback l E f n) :=
  (Scheme.coefficientProEtaleModulePullback_exact.{t, u} f
    (CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionRing l E (n + 1))))).2

attribute [local irreducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf

section DirectEvaluationProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] Functor.leftAdjoint ringMap
  Scheme.coefficientProEtaleModuleDirectImage SheafOfModules.pushforward
attribute [local semireducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf

/-- Sectionwise direct image commutes with finite evaluation, including its scalar action.
Source: Stacks 03D7, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison).
Proof: both functors evaluate sections at (n,baseChange U), with the same module map.
The structural ring homomorphism is ringComponent, whose transports are the explicit
sequence-section identities. Unfold them; equality of ring actions and morphisms
then gives equality of module sheaves and of functors. -/
theorem directEvaluation_eq {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    direct l E f ⋙ coefficientSequenceEvaluation l E Y n =
      coefficientSequenceEvaluation l E X n ⋙
        Scheme.coefficientProEtaleModuleDirectImage.{t, u} f
          (CommRingCat.of (ULift.{t + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))) := by
  let a : integralCoefficientSheaf l E Y n ⟶ _ :=
    eqToHom (coefficientSequenceEvaluationRing_eq l E Y n).symm
  let b : integralCoefficientSheaf l E X n ⟶ _ :=
    eqToHom (coefficientSequenceEvaluationRing_eq l E X n).symm
  let φ : (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (coefficientSequenceCommRingSheaf l E Y) ⟶
      ((base f).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj
          ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
            RingCat.{max u (t + 1)})).obj (coefficientSequenceCommRingSheaf l E X)) :=
    ⟨Functor.whiskerRight (ringMap l E f).hom
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩
  let ψ : integralCoefficientSheaf l E Y n ⟶
      ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj
          (integralCoefficientSheaf l E X n) :=
    ⟨Functor.whiskerRight
    (Scheme.coefficientProEtaleDirectRingMap.{t, u} f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩
  have : (Prod.sectR n Y.ProEt ⋙ base f).IsContinuous
      (Scheme.ProEt.topology Y) (coefficientSequenceTopology (Scheme.ProEt.topology X)) :=
    Functor.isContinuous_comp _ _ _ (coefficientSequenceTopology (Scheme.ProEt.topology Y)) _
  have h : a ≫ ((Prod.sectR n Y.ProEt).sheafPushforwardContinuous RingCat
      (Scheme.ProEt.topology Y) (coefficientSequenceTopology (Scheme.ProEt.topology Y))).map φ =
      ψ ≫ ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous RingCat
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map b := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    have ha : a.hom.app U = 𝟙 _ := by
      dsimp only [a]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    have hb : b.hom.app ((Scheme.proEtaleBaseChange f).op.obj U) = 𝟙 _ := by
      dsimp only [b]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    change a.hom.app U ≫ φ.hom.app (op (n, U.unop)) =
      ψ.hom.app U ≫ b.hom.app ((Scheme.proEtaleBaseChange f).op.obj U)
    rw [ha, hb]
    unfold φ ψ ringMap ringComponent
    rfl
  unfold direct coefficientSequenceEvaluation Scheme.coefficientProEtaleModuleDirectImage
  change SheafOfModules.pushforward φ ⋙ SheafOfModules.pushforward a =
    SheafOfModules.pushforward b ⋙ SheafOfModules.pushforward ψ
  erw [pushforwardComp_eq a φ, pushforwardComp_eq ψ b]
  exact congrArg (fun γ ↦ SheafOfModules.pushforward
    (F := Prod.sectR n Y.ProEt ⋙ base f)
    (J := Scheme.ProEt.topology Y)
    (K := coefficientSequenceTopology (Scheme.ProEt.topology X))
    (S := integralCoefficientSheaf l E Y n)
    (R := (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
      RingCat.{max u (t + 1)})).obj (coefficientSequenceCommRingSheaf l E X)) γ) h

end DirectEvaluationProof

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] Functor.leftAdjoint

/-- Cancel the invertible mate in Mathlib’s unit-mate equation.
Source: Mathlib unit_mateEquiv_symm and inverse cancellation
(blueprint: lem-pur-completed-primitive-counit-evaluation-existence). -/
private theorem inverseMate_exists
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    {F : C ⥤ D} {G : D ⥤ C} {L : A ⥤ B} {R : B ⥤ A}
    {U : C ⥤ A} {V : D ⥤ B} (adj : F ⊣ G) (adjn : L ⊣ R)
    (d : G ⋙ U ≅ V ⋙ R)
    [IsIso ((mateEquiv adj adjn).symm d.hom)] :
    ∃ ξ : F ⋙ V ≅ U ⋙ L, ∀ M : C,
      U.map (adj.unit.app M) ≫ d.hom.app (F.obj M) ≫ R.map (ξ.hom.app M) =
        adjn.unit.app (U.obj M) := by
  let e := asIso ((mateEquiv adj adjn).symm d.hom)
  refine ⟨e.symm, ?_⟩
  intro M
  have h := unit_mateEquiv_symm adj adjn d.hom M
  rw [← Category.assoc, h, Category.assoc, ← R.map_comp]
  change adjn.unit.app _ ≫ R.map (e.hom.app M ≫ e.inv.app M) = _
  rw [e.hom_inv_id_app]
  simp only [Functor.comp_obj, R.map_id, Category.comp_id]

section EvaluationProofs
attribute [local irreducible] Scheme.coefficientProEtaleModuleAdjunction
  Scheme.coefficientProEtaleModulePullback SheafOfModules.pushforward ringMap

/-- Existence half of the unit-normalized ordinary evaluation comparison.
Source: Zheng, Construction 4.1; Mathlib unit_mateEquiv_symm.
Proof: the sequence-site coextension theorem makes the canonical inverse mate
invertible. Invert that mate. Its unit-mate equation and inverse cancellation
give exactly the required normalization.
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
theorem inverseEvaluation_exists {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    ∃ ξ : inverse l E f ⋙ coefficientSequenceEvaluation l E X n ≅
      coefficientSequenceEvaluation l E Y n ⋙ integralOperationsLevelPullback l E f n,
      ∀ M : coefficientSequenceModules l E Y,
        (coefficientSequenceEvaluation l E Y n).map
            ((Adjunction.ofIsRightAdjoint (direct l E f)).unit.app M) ≫
          (eqToIso (directEvaluation_eq l E f n)).hom.app ((inverse l E f).obj M) ≫
          (Scheme.coefficientProEtaleModuleDirectImage.{t, u} f
            (CommRingCat.of (ULift.{t + 1}
              (Padic.coefficientExtensionRing l E (n + 1))))).map (ξ.hom.app M) =
        (Scheme.coefficientProEtaleModuleAdjunction.{t, u} f
          (CommRingCat.of (ULift.{t + 1}
            (Padic.coefficientExtensionRing l E (n + 1))))).unit.app
              ((coefficientSequenceEvaluation l E Y n).obj M) := by
  let adj : inverse l E f ⊣ direct l E f :=
    Adjunction.ofIsRightAdjoint (direct l E f)
  let adjn : integralOperationsLevelPullback l E f n ⊣
      Scheme.coefficientProEtaleModuleDirectImage.{t, u} f
        (CommRingCat.of (ULift.{t + 1}
          (Padic.coefficientExtensionRing l E (n + 1)))) :=
    Scheme.coefficientProEtaleModuleAdjunction.{t, u} f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  let d : direct l E f ⋙ coefficientSequenceEvaluation l E Y n ≅
      coefficientSequenceEvaluation l E X n ⋙
        Scheme.coefficientProEtaleModuleDirectImage.{t, u} f
          (CommRingCat.of (ULift.{t + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))) :=
    eqToIso (directEvaluation_eq l E f n)
  have : ((𝟭 ℕ).prod (Scheme.proEtaleBaseChange f)).IsContinuous
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X)) := base_continuous f
  have : IsIso ((mateEquiv adj adjn).symm d.hom) :=
    SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) (Scheme.proEtaleBaseChange f)
      ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          (coefficientSequenceCommRingSheaf l E Y))
      ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          (coefficientSequenceCommRingSheaf l E X)) n
      ⟨Functor.whiskerRight (ringMap l E f).hom
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩
      (integralCoefficientSheaf l E Y n) (integralCoefficientSheaf l E X n)
      (coefficientSequenceEvaluationRing_eq l E Y n)
      (coefficientSequenceEvaluationRing_eq l E X n)
      ⟨Functor.whiskerRight
        (Scheme.coefficientProEtaleDirectRingMap.{t, u} f
          (CommRingCat.of (ULift.{t + 1}
            (Padic.coefficientExtensionRing l E (n + 1))))).hom
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩
      (inverse l E f) (integralOperationsLevelPullback l E f n) adj adjn
      d
  exact inverseMate_exists
    (F := inverse l E f) (G := direct l E f)
    (L := integralOperationsLevelPullback l E f n)
    (R := Scheme.coefficientProEtaleModuleDirectImage.{t, u} f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
    (U := coefficientSequenceEvaluation l E Y n)
    (V := coefficientSequenceEvaluation l E X n) adj adjn d

/-- A normalized inverse has its prescribed adjoint transpose, which determines it.
Source: Mathlib Adjunction.homEquiv_unit
(blueprint: lem-pur-completed-primitive-counit-evaluation-uniqueness). -/
private theorem unitNormalizedIso_unique
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {A : C} {B : D} (a : A ⟶ G.obj B)
    (e e' : B ≅ F.obj A)
    (he : a ≫ G.map e.hom = adj.unit.app A)
    (he' : a ≫ G.map e'.hom = adj.unit.app A) : e = e' := by
  have hi : e.inv = e'.inv := by
    apply (adj.homEquiv A B).injective
    simp only [Adjunction.homEquiv_unit]
    calc
      adj.unit.app A ≫ G.map e.inv = a := by
        rw [← he, Category.assoc, ← G.map_comp, e.hom_inv_id,
          G.map_id, Category.comp_id]
      _ = adj.unit.app A ≫ G.map e'.inv := by
        rw [← he', Category.assoc, ← G.map_comp, e'.hom_inv_id,
          G.map_id, Category.comp_id]
  have hs : e.symm = e'.symm := Iso.ext hi
  simpa only [Iso.symm_symm_eq] using congrArg Iso.symm hs

/-- Apply the adjunction uniqueness calculation componentwise.
Source: Mathlib Iso.ext and NatTrans.ext
(blueprint: lem-pur-completed-primitive-counit-evaluation-uniqueness). -/
private theorem unitNormalizedNatIso_unique
    {C D I : Type*} [Category C] [Category D] [Category I]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (U : I ⥤ C) (V : I ⥤ D)
    (a : ∀ i, U.obj i ⟶ G.obj (V.obj i)) (e e' : V ≅ U ⋙ F)
    (he : ∀ i, a i ≫ G.map (e.hom.app i) = adj.unit.app (U.obj i))
    (he' : ∀ i, a i ≫ G.map (e'.hom.app i) = adj.unit.app (U.obj i)) : e = e' := by
  apply Iso.ext
  apply NatTrans.ext
  funext i
  exact congrArg Iso.hom (unitNormalizedIso_unique adj (a i)
    (e.app i) (e'.app i) (he i) (he' i))

/-- Uniqueness half for the unit-normalized ordinary evaluation comparison.
Source: Stacks 03D3, 0941; Mathlib Adjunction.homEquiv_unit.
Proof: compose each unit equation with the direct image of the inverse comparison.
Both inverses then have the same adjoint transpose. The adjunction hom-bijection
is injective, so they agree. Invert again and apply natural-transformation extensionality.
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
theorem inverseEvaluation_unique {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    (ξ η : inverse l E f ⋙ coefficientSequenceEvaluation l E X n ≅
      coefficientSequenceEvaluation l E Y n ⋙ integralOperationsLevelPullback l E f n)
    (hξ : ∀ M : coefficientSequenceModules l E Y,
      (coefficientSequenceEvaluation l E Y n).map
          ((Adjunction.ofIsRightAdjoint (direct l E f)).unit.app M) ≫
        (eqToIso (directEvaluation_eq l E f n)).hom.app ((inverse l E f).obj M) ≫
        (Scheme.coefficientProEtaleModuleDirectImage.{t, u} f
          (CommRingCat.of (ULift.{t + 1}
            (Padic.coefficientExtensionRing l E (n + 1))))).map (ξ.hom.app M) =
      (Scheme.coefficientProEtaleModuleAdjunction.{t, u} f
        (CommRingCat.of (ULift.{t + 1}
          (Padic.coefficientExtensionRing l E (n + 1))))).unit.app
            ((coefficientSequenceEvaluation l E Y n).obj M))
    (hη : ∀ M : coefficientSequenceModules l E Y,
      (coefficientSequenceEvaluation l E Y n).map
          ((Adjunction.ofIsRightAdjoint (direct l E f)).unit.app M) ≫
        (eqToIso (directEvaluation_eq l E f n)).hom.app ((inverse l E f).obj M) ≫
        (Scheme.coefficientProEtaleModuleDirectImage.{t, u} f
          (CommRingCat.of (ULift.{t + 1}
            (Padic.coefficientExtensionRing l E (n + 1))))).map (η.hom.app M) =
      (Scheme.coefficientProEtaleModuleAdjunction.{t, u} f
        (CommRingCat.of (ULift.{t + 1}
          (Padic.coefficientExtensionRing l E (n + 1))))).unit.app
            ((coefficientSequenceEvaluation l E Y n).obj M)) :
    ξ = η := by
  exact unitNormalizedNatIso_unique (F := integralOperationsLevelPullback l E f n)
    (Scheme.coefficientProEtaleModuleAdjunction.{t, u} f
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (n + 1)))))
    (coefficientSequenceEvaluation l E Y n)
    (inverse l E f ⋙ coefficientSequenceEvaluation l E X n)
    (fun M ↦ (coefficientSequenceEvaluation l E Y n).map
        ((Adjunction.ofIsRightAdjoint (direct l E f)).unit.app M) ≫
      (eqToIso (directEvaluation_eq l E f n)).hom.app ((inverse l E f).obj M))
    ξ η (fun M ↦ (Category.assoc _ _ _).trans (hξ M))
    (fun M ↦ (Category.assoc _ _ _).trans (hη M))

end EvaluationProofs

/-- The ordinary inverse-image evaluation is uniquely normalized by the actual units.
Source: Stacks 03D3, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison).
Proof: assemble the existence and uniqueness halves above. -/
theorem inverseEvaluation_existsUnique {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    ∃! ξ : inverse l E f ⋙ coefficientSequenceEvaluation l E X n ≅
      coefficientSequenceEvaluation l E Y n ⋙ integralOperationsLevelPullback l E f n,
      ∀ M : coefficientSequenceModules l E Y,
        (coefficientSequenceEvaluation l E Y n).map
            ((Adjunction.ofIsRightAdjoint (direct l E f)).unit.app M) ≫
          (eqToIso (directEvaluation_eq l E f n)).hom.app ((inverse l E f).obj M) ≫
          (Scheme.coefficientProEtaleModuleDirectImage.{t, u} f
            (CommRingCat.of (ULift.{t + 1}
              (Padic.coefficientExtensionRing l E (n + 1))))).map (ξ.hom.app M) =
        (Scheme.coefficientProEtaleModuleAdjunction.{t, u} f
          (CommRingCat.of (ULift.{t + 1}
            (Padic.coefficientExtensionRing l E (n + 1))))).unit.app
              ((coefficientSequenceEvaluation l E Y n).obj M) := by
  obtain ⟨ξ, hξ⟩ := inverseEvaluation_exists l E f n
  refine ⟨ξ, hξ, ?_⟩
  intro η hη
  exact (inverseEvaluation_unique l E f n ξ η hξ hη).symm

/-- The canonical ordinary evaluation comparison, fixed by the universal generator.
Source: Stacks 03D3, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def inverseEvaluation {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    inverse l E f ⋙ coefficientSequenceEvaluation l E X n ≅
      coefficientSequenceEvaluation l E Y n ⋙ integralOperationsLevelPullback l E f n :=
  (inverseEvaluation_existsUnique l E f n).choose

attribute [local irreducible] inverseEvaluation inverse direct

end PrimitiveCounit
end WeilConjectures

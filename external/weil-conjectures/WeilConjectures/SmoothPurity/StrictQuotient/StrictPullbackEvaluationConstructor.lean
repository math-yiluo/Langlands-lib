/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.StrictQuotient.StrictQuotientExpressions
import all WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackSiteData
import WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtale.Coefficient.ProEtaleCoefficientPullbackExact

/-! # Evaluation and exactness of strict sequence inverse image -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures.StrictQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] constantSheaf coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  Scheme.coefficientProEtaleDirectRingMap

private theorem section_naturality.{r, c, v, d, w}
    {C : Type c} [Category.{v} C] {D : Type d} [Category.{w} D]
    {J : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J JD]
    {R : Sheaf J RingCat.{r}} {S : Sheaf JD RingCat.{r}}
    {φ : R ⟶ (F.sheafPushforwardContinuous RingCat J JD).obj S}
    (M : SheafOfModules.{r} R) (N : SheafOfModules.{r} S)
    (η : M ⟶ (SheafOfModules.pushforward φ).obj N)
    {U V : C} (a : U ⟶ V) (x : M.val.obj (op V)) :
    N.val.presheaf.map (F.map a).op (η.val.app (op V) x) =
      η.val.app (op U) (M.val.presheaf.map a.op x) :=
  (PresheafOfModules.naturality_apply η.val a.op x).symm

private theorem pullbackTransitions {V W : Scheme.{t}} (g : V ⟶ W)
    (K : Complex l E W) : PullbackTransitions l E g K := by
  intro m n hmn k U x
  have h := section_naturality.{max u (t + 1), t + 1, t, t + 1, t} (K.X k)
    ((integralComparisonSequencePullback l E g).obj (K.X k))
    ((Adjunction.ofIsRightAdjoint
      (integralComparisonSequenceDirectImage l E g)).unit.app (K.X k))
    (Prod.mkHom (homOfLE hmn) (𝟙 U)) x
  change (((pull l E g K).X k).val.presheaf.map
      (Prod.mkHom (homOfLE hmn) ((Scheme.proEtaleBaseChange g).map (𝟙 U))).op)
        (integralComparisonSequenceGenerator l E g (K.X k) m U x) =
    integralComparisonSequenceGenerator l E g (K.X k) n U
      (horizontal l E (K.X k) hmn U x) at h
  simpa only [horizontal, CategoryTheory.Functor.map_id] using h

private theorem inverse_mate_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (d : R₁ ⋙ G ≅ H ⋙ R₂) (e : L₁ ⋙ H ≅ G ⋙ L₂)
    (he : ((mateEquiv a b).symm d.hom) = e.inv) (M : A) :
    G.map (a.unit.app M) ≫ d.hom.app (L₁.obj M) ≫ R₂.map (e.hom.app M) =
      b.unit.app (G.obj M) := by
  have hu := unit_mateEquiv_symm a b d.hom M
  change G.map (a.unit.app M) ≫ d.hom.app (L₁.obj M) =
    b.unit.app (G.obj M) ≫ R₂.map (((mateEquiv a b).symm d.hom).app M) at hu
  rw [he] at hu
  rw [← Category.assoc, hu, Category.assoc, ← R₂.map_comp, e.inv_hom_id_app]
  exact (congrArg (b.unit.app (G.obj M) ≫ ·) (R₂.map_id _)).trans (Category.comp_id _)

private theorem pullbackComputes {V W : Scheme.{t}} (g : V ⟶ W)
    (K : Complex l E W) (n : ℕ) : PullbackComputes l E g K n := by
  intro LF ε hLF
  let := hLF
  have h := Scheme.coefficientProEtaleModulePullback_exact.{t, u} g
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  let : PreservesFiniteLimits (integralOperationsLevelPullback l E g n) := h.1
  let : PreservesFiniteColimits (integralOperationsLevelPullback l E g n) := h.2
  have := Functor.isIso_of_isLeftDerivedFunctor_of_inverts LF ε
    (by
      rw [← MorphismProperty.IsInvertedBy.iff_of_iso
        (HomologicalComplex.quasiIso (normalizedDVRModules l E W n) (.up ℤ))
        (integralOperationsLevelPullback l E g n).mapDerivedCategoryFactors]
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
      exact MorphismProperty.IsInvertedBy.of_comp _ _
        (Functor.IsLocalization.inverts (L := DerivedCategory.Q)) _)
  infer_instance

private def evaluationFiniteAdjunction {V W : Scheme.{t}} (g : V ⟶ W) (n : ℕ) :
    integralOperationsLevelPullback l E g n ⊣
      Scheme.coefficientProEtaleModuleDirectImage.{t, u} g
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))) :=
  Scheme.coefficientProEtaleModuleAdjunction.{t, u} g _

private def sequenceAdjunction {V W : Scheme.{t}} (g : V ⟶ W) :
    integralComparisonSequencePullback l E g ⊣ integralComparisonSequenceDirectImage l E g :=
  Adjunction.ofIsRightAdjoint _

private def directEvaluation {V W : Scheme.{t}} (g : V ⟶ W) (n : ℕ) :
    integralComparisonSequenceDirectImage l E g ⋙ coefficientSequenceEvaluation l E W n ≅
      coefficientSequenceEvaluation l E V n ⋙
        Scheme.coefficientProEtaleModuleDirectImage.{t, u} g
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))) :=
  AmbientPullbackTensor.sequencePushEvaluation l E g n

private def pullbackEvaluation {V W : Scheme.{t}} (g : V ⟶ W) (n : ℕ) :
    integralComparisonSequencePullback l E g ⋙ coefficientSequenceEvaluation l E V n ≅
      coefficientSequenceEvaluation l E W n ⋙ integralOperationsLevelPullback l E g n := by
  have : ((𝟭 ℕ).prod (Scheme.proEtaleBaseChange g)).IsContinuous
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceTopology (Scheme.ProEt.topology V)) :=
    AmbientPullbackTensor.baseContinuous g none
  have : IsIso ((mateEquiv (sequenceAdjunction l E g) (evaluationFiniteAdjunction l E g n)).symm
      (directEvaluation l E g n).hom) :=
    SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso
      (Scheme.ProEt.topology W) (Scheme.ProEt.topology V) (Scheme.proEtaleBaseChange g)
      _ _ n (AmbientPullbackTensor.moduleRingUnit l E g none) _ _
      (coefficientSequenceEvaluationRing_eq l E W n)
      (coefficientSequenceEvaluationRing_eq l E V n)
      (AmbientPullbackTensor.moduleRingUnit l E g (some n))
      (integralComparisonSequencePullback l E g) (integralOperationsLevelPullback l E g n)
      (sequenceAdjunction l E g) (evaluationFiniteAdjunction l E g n) (directEvaluation l E g n)
  exact (asIso ((mateEquiv (sequenceAdjunction l E g) (evaluationFiniteAdjunction l E g n)).symm
    (directEvaluation l E g n).hom)).symm

private theorem pullbackEvaluation_unit {V W : Scheme.{t}} (g : V ⟶ W) (n : ℕ)
    (M : coefficientSequenceModules l E W) :
    (coefficientSequenceEvaluation l E W n).map ((sequenceAdjunction l E g).unit.app M) ≫
      (directEvaluation l E g n).hom.app ((integralComparisonSequencePullback l E g).obj M) ≫
      (Scheme.coefficientProEtaleModuleDirectImage.{t, u} g
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).map
          ((pullbackEvaluation l E g n).hom.app M) =
      (evaluationFiniteAdjunction l E g n).unit.app
        ((coefficientSequenceEvaluation l E W n).obj M) :=
  inverse_mate_unit (sequenceAdjunction l E g) (evaluationFiniteAdjunction l E g n)
    (directEvaluation l E g n) (pullbackEvaluation l E g n) (by rfl) M

private theorem directEvaluation_apply {V W : Scheme.{t}} (g : V ⟶ W) (n : ℕ)
    (M : coefficientSequenceModules l E V) (U : W.ProEtᵒᵖ)
    (x : M.val.obj (op (n, ((Scheme.proEtaleBaseChange g).obj U.unop)))) :
    ((directEvaluation l E g n).hom.app M).val.app U x = x := rfl

attribute [local irreducible] directEvaluation pullbackEvaluation

private def pullbackComplexEvaluation {V W : Scheme.{t}} (g : V ⟶ W)
    (K : Complex l E W) (n : ℕ) : level l E (pull l E g K) n ≅
      (finitePull l E g n).obj (level l E K n) := by
  let : (integralOperationsLevelPullback l E g n).Additive :=
    integralOperationsLevelPullback_additive l E g n
  exact (NatIso.mapHomologicalComplex (pullbackEvaluation l E g n) (.up ℤ)).app K

private theorem coefficient_unit_equation {V W : Scheme.{t}} (g : V ⟶ W) (n : ℕ)
    (M : coefficientSequenceModules l E W) (N : coefficientSequenceModules l E V)
    (P : normalizedDVRModules l E V n)
    (η : M ⟶ (integralComparisonSequenceDirectImage l E g).obj N)
    (e : (coefficientSequenceEvaluation l E V n).obj N ⟶ P)
    (ε : (coefficientSequenceEvaluation l E W n).obj M ⟶
      (Scheme.coefficientProEtaleModuleDirectImage.{t, u} g
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).obj P)
    (hu : (coefficientSequenceEvaluation l E W n).map η ≫
      (directEvaluation l E g n).hom.app N ≫
      (Scheme.coefficientProEtaleModuleDirectImage.{t, u} g
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).map e = ε)
    (U : W.ProEt) (x : M.val.obj (op (n, U))) :
    e.val.app (op ((Scheme.proEtaleBaseChange g).obj U))
      (η.val.app (op (n, U)) x) = ε.val.app (op U) x := by
  dsimp only [coefficientSequenceEvaluation, integralComparisonSequenceDirectImage,
    Scheme.coefficientProEtaleModuleDirectImage] at η e ε hu
  have hx := congrArg (fun a ↦ a.val.app (op U) x) hu
  change e.val.app (op ((Scheme.proEtaleBaseChange g).obj U))
    (((directEvaluation l E g n).hom.app N).val.app (op U)
      (η.val.app (op (n, U)) x)) = ε.val.app (op U) x at hx
  erw [directEvaluation_apply] at hx
  exact hx

private theorem pullbackEvaluation_generator {V W : Scheme.{t}} (g : V ⟶ W)
    (M : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEt)
    (x : M.val.obj (op (n, U))) :
    ((pullbackEvaluation l E g n).hom.app M).val.app
        (op ((Scheme.proEtaleBaseChange g).obj U))
        (integralComparisonSequenceGenerator l E g M n U x) =
      integralOperationsPullbackGenerator l E g n
        ((coefficientSequenceEvaluation l E W n).obj M) U x := by
  exact coefficient_unit_equation l E g n M _ _
    ((sequenceAdjunction l E g).unit.app M) ((pullbackEvaluation l E g n).hom.app M)
    ((evaluationFiniteAdjunction l E g n).unit.app
      ((coefficientSequenceEvaluation l E W n).obj M))
    (pullbackEvaluation_unit l E g n M) U x

private theorem pullbackModel {V W : Scheme.{t}} (g : V ⟶ W)
    (K : Complex l E W) (n : ℕ) : PullbackModel l E g K n := by
  refine ⟨pullbackComplexEvaluation l E g K n, ?_⟩
  intro k U x
  exact pullbackEvaluation_generator l E g (K.X k) n U x

/-- Evaluation of strict sequence inverse image is the actual finite inverse image,
and finite inverse image computes every universal left-derived pair.
Source: Stacks Project, sites-cohomology.tex, Tags 0G7E and 07A6;
sites-modules.tex, Tag 03EL.
(blueprint: lem-pur-strict-pullback-evaluation-constructor).

Proof: the actual sequence adjunction unit is natural for horizontal site arrows.
The inverse mate of direct-image evaluation is invertible, so it identifies
sequence inverse image evaluated at n with finite inverse image. The inverse-mate
unit identity fixes its generator formula. Apply this natural isomorphism to
cochain complexes. Finite constant-coefficient geometric inverse image is exact;
its functor on complexes therefore inverts quasi-isomorphisms after localization.
The universal property of each left-derived pair makes its comparison invertible
on every complex. All constructions retain independent coefficient and site
universes and impose no flatness or normalization hypothesis on the complex. -/
theorem strictPullbackEvaluationConstructor {V W : Scheme.{t}} (g : V ⟶ W)
    (K : Complex l E W) :
    PullbackTransitions l E g K ∧
      ∀ n : ℕ, PullbackModel l E g K n ∧ PullbackComputes l E g K n := by
  refine ⟨pullbackTransitions l E g K, ?_⟩
  intro n
  exact ⟨pullbackModel l E g K n, pullbackComputes l E g K n⟩

end WeilConjectures.StrictQuotient

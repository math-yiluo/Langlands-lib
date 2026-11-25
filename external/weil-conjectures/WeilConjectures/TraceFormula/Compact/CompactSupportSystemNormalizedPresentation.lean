/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Compact.CompactSupportSystemEvaluationDiagram
import WeilConjectures.SixFunctors.IntegralOpenReduction.NormalizedOpenSections
import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenCoefficientOperationsExistence
import WeilConjectures.AlgebraicGeometry.ProEtale.Coefficient.ProEtaleCoefficientPullbackExact
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.TraceFormula.Compact.CompactSupportFiniteCoefficientPresentation
import WeilConjectures.TraceFormula.Compact.CompactSupportDirectImageEvaluation
import WeilConjectures.TraceFormula.Compact.CompactSupportOpenOrdinaryMate
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Normalized presentations for compact-support system evaluation

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 03DI, 03DJ, 07A4, 0941.
This module specializes the ordinary system calculus to the actual pro-etale functors.
(blueprint: lem-trf-compact-support-normalized-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
attribute [local irreducible] CategoryTheory.constantSheaf

universe t u c₁ c₂ d₁ d₂ v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem compactSupportKInjectives
    {C : Type c₁} [Category.{c₂} C]
    (hsite : EssentiallySmall.{max c₁ c₂ u} C) (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max c₁ c₂ u}) :
    Abelian.HasKInjectiveResolutions
      (SheafOfModules.{max c₁ c₂ u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) := by
  let := hsite
  let : HasSheafify J AddCommGrpCat.{max c₁ c₂ u} :=
    @SheafOfModules.hasSheafify_coefficientUniverse _ _ hsite J
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max c₁ c₂ u} :=
    @SheafOfModules.wEqualsLocallyBijective_coefficientUniverse _ _ hsite J
  have : IsGrothendieckAbelian.{max c₁ c₂ u}
      (SheafOfModules.{max c₁ c₂ u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses J R).1
  infer_instance

private theorem normalizedMateEquations
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (d : R₁ ⋙ G ≅ H ⋙ R₂) (e : L₁ ⋙ H ≅ G ⋙ L₂)
    (hm : ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ d.hom)) = e.inv) :
    (∀ M, G.map (a.unit.app M) ≫ d.hom.app (L₁.obj M) ≫
      R₂.map (e.hom.app M) = b.unit.app (G.obj M)) ∧
    (∀ N, L₂.map (d.hom.app N) ≫ b.counit.app (H.obj N) =
      e.inv.app (R₁.obj N) ≫ H.map (a.counit.app N)) := by
  constructor
  · intro M
    have hu := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ d.hom) M
    change G.map (a.unit.app M) ≫ d.hom.app (L₁.obj M) =
      b.unit.app (G.obj M) ≫ R₂.map
        (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ d.hom)).app M) at hu
    rw [hm] at hu
    rw [reassoc_of% hu]
    rw [← Functor.map_comp, Iso.inv_hom_id_app]
    erw [R₂.map_id, Category.comp_id]
  · intro N
    have hc := mateEquiv_counit_symm a b (TwoSquare.mk _ _ _ _ d.hom) N
    change L₂.map (d.hom.app N) ≫ b.counit.app (H.obj N) =
      ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ d.hom)).app (R₁.obj N) ≫
        H.map (a.counit.app N) at hc
    rw [hm] at hc
    exact hc

private theorem compactSupportOpenDerivedEvaluation
    {X Z : Scheme.{t}} (j : X ⟶ Z) [IsOpenImmersion j]
    (o : IntegralOpenReduction.Operations l E j) :
    ∃ right : ∀ n : ℕ,
        IntegralOpenReduction.P l E j o ⋙ coefficientSequenceDerivedEvaluation l E X n ≅
          coefficientSequenceDerivedEvaluation l E Z n ⋙
            (IntegralOpenReduction.finiteRestriction l E j o n).mapDerivedCategory,
(∀ (n : ℕ) M,
          (coefficientSequenceDerivedEvaluation l E X n).map
            ((IntegralOpenReduction.systemAdjunction l E j
            o).unit.app M) ≫
            (right n).hom.app ((compactSupportCanonicalJSystem l E j
              o).obj M) ≫
            ((IntegralOpenReduction.finiteRestriction l E j
              o n).mapDerivedCategory).map
                ((compactSupportCanonicalJEvaluation l E j o n).hom.app M) =
              (compactSupportCanonicalJLevelAdjunction l E j o
                n).unit.app ((coefficientSequenceDerivedEvaluation l E X n).obj M)) ∧
      (∀ (n : ℕ) N,
          (compactSupportCanonicalJLevel l E j o n).map
            ((right n).hom.app N) ≫
            (compactSupportCanonicalJLevelAdjunction l E j o
              n).counit.app ((coefficientSequenceDerivedEvaluation l E Z n).obj N) =
              (compactSupportCanonicalJEvaluation l E j o n).inv.app ((IntegralOpenReduction.P l E j
                o).obj N) ≫
                (coefficientSequenceDerivedEvaluation l E Z n).map
                  ((IntegralOpenReduction.systemAdjunction l E j
                  o).counit.app N)) := by
  classical
  let (n : ℕ) : (coefficientSequenceEvaluation l E X n).Additive :=
    coefficientSequenceEvaluation_additiveInstance l E X n
  let (n : ℕ) : (coefficientSequenceEvaluation l E Z n).Additive :=
    coefficientSequenceEvaluation_additiveInstance l E Z n
  let (n : ℕ) : PreservesFiniteLimits (coefficientSequenceEvaluation l E X n) :=
    coefficientSequenceEvaluation_limits l E X n
  let (n : ℕ) : PreservesFiniteLimits (coefficientSequenceEvaluation l E Z n) :=
    coefficientSequenceEvaluation_limits l E Z n
  let (n : ℕ) : PreservesFiniteColimits (coefficientSequenceEvaluation l E X n) :=
    coefficientSequenceEvaluation_colimits l E X n
  let (n : ℕ) : PreservesFiniteColimits (coefficientSequenceEvaluation l E Z n) :=
    coefficientSequenceEvaluation_colimits l E Z n
  let (n : ℕ) : (IntegralOpenReduction.finiteRestriction l E j o n).Additive :=
    compactSupportFiniteRestrictionAdditive l E j o n
  let (n : ℕ) : PreservesFiniteLimits (IntegralOpenReduction.finiteRestriction l E j o n) :=
    compactSupportFiniteRestrictionPreservesFiniteLimits l E j o n
  let (n : ℕ) : PreservesFiniteColimits (IntegralOpenReduction.finiteRestriction l E j o n) :=
    compactSupportFiniteRestrictionPreservesFiniteColimits l E j o n
  choose d hd using compactSupportOpenOrdinaryMate l E j o
  let right (n : ℕ) := Functor.mapDerivedCategorySquareIso (d n)
  have hmate (n : ℕ) :
      ((mateEquiv (IntegralOpenReduction.systemAdjunction l E j o)
        (compactSupportCanonicalJLevelAdjunction l E j o n)).symm
        (TwoSquare.mk _ _ _ _ (right n).hom)) =
          (compactSupportCanonicalJEvaluation l E j o n).inv := by
    let a := IntegralOpenReduction.ordinarySystemAdjunction l E j o
    let b := (o.finite n).toAdjunction.comp
      (SheafOfModules.localizedSystemAdjunction.{t+1, t, max u (t+1)}
        (integralCoefficientCommRingSheaf l E Z n) (IntegralOpenReduction.openObject j))
    have hi : IsIso ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ (d n).hom)) := by
      rw [hd n]
      infer_instance
    have he := (exact_localization_inverse_mate a b (d n)).2.1
    have hiso : asIso ((mateEquiv a b).symm
        (TwoSquare.mk _ _ _ _ (d n).hom)) =
          (IntegralOpenReduction.extensionEvaluation l E j o n).symm :=
      Iso.ext (hd n)
    rw [hiso] at he
    change _ = _ at he
    refine he.trans ?_
    simp only [Functor.mapDerivedCategorySquareIso, compactSupportCanonicalJEvaluation,
      Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.symm_hom,
      Iso.trans_inv, Iso.symm_inv, Category.assoc]
  refine ⟨right, ?_, ?_⟩
  · intro n
    exact (normalizedMateEquations (IntegralOpenReduction.systemAdjunction l E j o)
      (compactSupportCanonicalJLevelAdjunction l E j o n) (right n)
      (compactSupportCanonicalJEvaluation l E j o n) (hmate n)).1
  · intro n
    exact (normalizedMateEquations (IntegralOpenReduction.systemAdjunction l E j o)
      (compactSupportCanonicalJLevelAdjunction l E j o n) (right n)
      (compactSupportCanonicalJEvaluation l E j o n) (hmate n)).2

/-- Existence of normalized evaluations for the actual ordinary geometric operations.
This assertion constructs the presentation and its adjunction comparisons only; it does
not compare any tower transitions or construct a compact-support tower isomorphism.

Source: the coherence node's proof steps 1--3 and 6; Zheng 4.1, 4.10;
Stacks 03DI--03DJ, 07A4, 0941
(blueprint: lem-trf-compact-support-normalized-presentation).
Proof: choose the existing section-normalized open-slice calculus and transport
it along the actual open coefficient equivalences. Construct the additive and
exact operation instances and the K-injective resolution instances on the actual
ringed module categories. The finite quotient adjunctions come from the existing
coefficient system calculus. The independent finite-coefficient presentation and
direct-image evaluation results give their respective comparison squares and
normalization equations. For the open comparison, paste the ordinary slice
restriction-evaluation mate with the coefficient-equivalence square. Its inverse
mate is extensionEvaluation.inv. Exact localization preserves that inverse mate;
its left square is exactly compactSupportCanonicalJEvaluation.inv. The unit and
counit equations of the mates correspondence therefore give both displayed open
adjunction equations. Assemble these comparisons into D and supply the ten
normalization clauses in order. -/
theorem compactSupportSystemNormalizedPresentation
    {X Z Y : Scheme.{t}} {j : X ⟶ Z} {p : Z ⟶ Y} [IsOpenImmersion j]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]
    [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))] :
    ∃ D : CompactSupportSystemEvaluationData l E X Z Y j p,
      (∀ {m n : ℕ} (h : n ≤ m)
              (N : normalizedDVRModules l E Z n) (V : Y.ProEtᵒᵖ),
              HEq (fun x ↦ ((D.operations.ordinaryCoefficientComparison h).hom.app N).val.app V x)
                (fun x : N.val.obj ((Scheme.proEtaleBaseChange p).op.obj V) ↦ x)) ∧
      (∀ {m n : ℕ} (h : n ≤ m),
        letI := normalizedDVRModuleRes_limits l E Z h
        letI := normalizedDVRModuleRes_colimits l E Z h
        letI := normalizedDVRModuleRes_limits l E Y h
        letI := normalizedDVRModuleRes_colimits l E Y h
        CompactSupportDerivedSquareNormalization
            (compactSupportLevelDirectImage l E p n) (compactSupportLevelDirectImage l E p m)
            (normalizedDVRModuleRes l E Z h) (normalizedDVRModuleRes l E Y h)
            (D.operations.ordinaryCoefficientComparison h)
              (D.operations.derivedCoefficientComparison h)) ∧
      (∀ (n : ℕ) N V x,
            HEq (((D.operations.instances.jOperations.openSystems.restrictionEvaluation n).hom.app
              N).val.app V x) x) ∧
      (∀ n : ℕ, D.jLeftEvaluation n =
          compactSupportCanonicalJEvaluation l E j D.operations.instances.jOperations n) ∧
      (∀ (n : ℕ) (N : coefficientSequenceModules l E Z)
              (V : Y.ProEtᵒᵖ)
              (x : ((integralComparisonSequenceDirectImage l E p ⋙
                coefficientSequenceEvaluation l E Y n).obj N).val.obj V),
              HEq (((D.pOrdinaryEvaluation n).hom.app N).val.app V x) x) ∧
      (∀ n : ℕ,
        letI := coefficientSequenceEvaluation_additiveInstance l E Z n
        letI := coefficientSequenceEvaluation_additiveInstance l E Y n
        letI := coefficientSequenceEvaluation_limits l E Z n
        letI := coefficientSequenceEvaluation_colimits l E Z n
        letI := coefficientSequenceEvaluation_limits l E Y n
        letI := coefficientSequenceEvaluation_colimits l E Y n
        CompactSupportDerivedSquareNormalization
            (integralComparisonSequenceDirectImage l E p) (compactSupportLevelDirectImage l E p n)
            (coefficientSequenceEvaluation l E Z n) (coefficientSequenceEvaluation l E Y n)
            (D.pOrdinaryEvaluation n).symm (D.pRightEvaluation n).symm) ∧
      (∀ (n : ℕ) M,
          (coefficientSequenceDerivedEvaluation l E X n).map
            ((IntegralOpenReduction.systemAdjunction l E j
            D.operations.instances.jOperations).unit.app M) ≫
            (D.jRightEvaluation n).hom.app ((compactSupportCanonicalJSystem l E j
              D.operations.instances.jOperations).obj M) ≫
            ((IntegralOpenReduction.finiteRestriction l E j
              D.operations.instances.jOperations n).mapDerivedCategory).map ((D.jLeftEvaluation
                n).hom.app M) =
              (compactSupportCanonicalJLevelAdjunction l E j D.operations.instances.jOperations
                n).unit.app ((coefficientSequenceDerivedEvaluation l E X n).obj M)) ∧
      (∀ (n : ℕ) N,
          (compactSupportCanonicalJLevel l E j D.operations.instances.jOperations n).map
            ((D.jRightEvaluation n).hom.app N) ≫
            (compactSupportCanonicalJLevelAdjunction l E j D.operations.instances.jOperations
              n).counit.app ((coefficientSequenceDerivedEvaluation l E Z n).obj N) =
              (D.jLeftEvaluation n).inv.app ((IntegralOpenReduction.P l E j
                D.operations.instances.jOperations).obj N) ≫
                (coefficientSequenceDerivedEvaluation l E Z n).map
                  ((IntegralOpenReduction.systemAdjunction l E j
                  D.operations.instances.jOperations).counit.app N)) ∧
      (∀ (n : ℕ) M,
          (coefficientSequenceDerivedEvaluation l E Y n).map ((compactSupportCanonicalPAdjunction l
            E p).unit.app M) ≫
            (D.pRightEvaluation n).hom.app ((integralComparisonDerivedSequencePullback l E p).obj
              M) ≫
            ((compactSupportLevelDirectImage l E p n).rightDerivedFunctor).map ((D.pLeftEvaluation
              n).hom.app M) =
              (compactSupportCanonicalPLevelAdjunction l E p n).unit.app
                ((coefficientSequenceDerivedEvaluation l E Y n).obj M)) ∧
      (∀ (n : ℕ) N,
          ((compactSupportLevelPullback l E p n).mapDerivedCategory).map ((D.pRightEvaluation
            n).hom.app N) ≫
            (compactSupportCanonicalPLevelAdjunction l E p n).counit.app
              ((coefficientSequenceDerivedEvaluation l E Z n).obj N) =
              (D.pLeftEvaluation n).inv.app (((integralComparisonSequenceDirectImage l E
                p).rightDerivedFunctor).obj N) ≫
                (coefficientSequenceDerivedEvaluation l E Z n).map
                  ((compactSupportCanonicalPAdjunction l E p).counit.app N)) := by
  obtain ⟨sections, hsections⟩ := IntegralOpenReduction.normalizedOpenSections l E j
  obtain ⟨o, ho, _⟩ := OpenSemilinearTensor.openCoefficientOperationsExistence l E j sections
  have hopen : ∀ (n : ℕ) N V x,
      HEq (((o.openSystems.restrictionEvaluation n).hom.app N).val.app V x) x := by
    simpa only [ho] using hsections
  have pAdditive : (integralComparisonSequenceDirectImage l E p).Additive := by
    constructor
    intro M N f g
    ext V x
    rfl
  have levelAdditive (n : ℕ) : (compactSupportLevelDirectImage l E p n).Additive := by
    constructor
    intro M N f g
    ext V x
    rfl
  let inst : CompactSupportSystemOperationInstances l E j p :=
    { jOperations := o
      pAdditive := pAdditive
      pKInjective := compactSupportKInjectives (essentiallySmallSelf _)
        (coefficientSequenceTopology (Scheme.ProEt.topology Z))
        (coefficientSequenceCommRingSheaf l E Z)
      levelAdditive := levelAdditive
      levelKInjective := fun n ↦ compactSupportKInjectives (essentiallySmallSelf _)
        (Scheme.ProEt.topology Z) (integralCoefficientCommRingSheaf l E Z n)
      pullAdditive := fun n ↦
        (Adjunction.ofIsRightAdjoint (compactSupportLevelDirectImage l E p n)).left_adjoint_additive
      pullLimits := fun n ↦
        (Scheme.coefficientProEtaleModulePullback_exact.{t, u} p _).1
      pullColimits := fun n ↦
        (Scheme.coefficientProEtaleModulePullback_exact.{t, u} p _).2 }
  obtain ⟨SZ, _⟩ := coefficientDerivedSystemEvaluationCalculus l E Z
  obtain ⟨SY, _⟩ := coefficientDerivedSystemEvaluationCalculus l E Y
  have scalarZ := fun {m n : ℕ} (h : n ≤ m) ↦ SZ.quotientCalculus.adjunction h
  have scalarY := fun {m n : ℕ} (h : n ≤ m) ↦ SY.quotientCalculus.adjunction h
  let : CompactSupportSystemOperationInstances l E j p := inst
  obtain ⟨a, d, ha, hd⟩ := compactSupportFiniteCoefficientPresentation l E p
  let ops : CompactSupportSystemCanonicalOperations l E j p :=
    { instances := inst
      scalarZ := scalarZ
      scalarY := scalarY
      ordinaryCoefficientComparison := a
      derivedCoefficientComparison := d }
  obtain ⟨jRight, hjUnit, hjCounit⟩ := compactSupportOpenDerivedEvaluation l E j o
  obtain ⟨pLeft, pRight, pOrdinary, hpOrdinary, hpDerived, hpUnit, hpCounit⟩ :=
    compactSupportDirectImageEvaluation l E p
  let D : CompactSupportSystemEvaluationData l E X Z Y j p :=
    { operations := ops
      jLeftEvaluation := compactSupportCanonicalJEvaluation l E j o
      jRightEvaluation := jRight
      pLeftEvaluation := pLeft
      pRightEvaluation := pRight
      pOrdinaryEvaluation := pOrdinary }
  exact ⟨D, ha, hd, hopen, fun _ ↦ rfl, hpOrdinary, hpDerived,
    hjUnit, hjCounit, hpUnit, hpCounit⟩

end WeilConjectures

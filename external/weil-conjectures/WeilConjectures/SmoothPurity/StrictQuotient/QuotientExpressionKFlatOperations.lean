/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.StrictQuotient.StrictQuotientExpressions
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.SmoothPurity.StrictQuotient.StrictUnitOrdinaryAdjoint
import WeilConjectures.SmoothPurity.StrictQuotient.StrictTensorAdjointConstructor
import WeilConjectures.SmoothPurity.StrictQuotient.StrictPullbackAdjointConstructor
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! Normalization and operation-adjoint laws for strict quotient expressions.

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 07A6
(blueprint: lem-pur-quotient-expression-kflat-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u c v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures.StrictQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  coefficientFiniteQuotientExistence coefficientFiniteQuotientDerivedExistence
  coefficientFiniteQuotientModel coefficientFiniteQuotientUnitSection
  SheafOfModules.monoidalCategory scalarReductionExtension
  coefficientFiniteQuotientExtension coefficientSequenceEvaluation
  coefficientOrdinaryQuotient

private theorem composite_mate_isIso
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ A} (am : F ⊣ G)
    {H : A ⥤ C} {J : C ⥤ A} (an : H ⊣ J)
    {L : B ⥤ C} {R : C ⥤ B} (aq : L ⊣ R)
    (e : R ⋙ G ≅ J) (M : A) :
    IsIso ((aq.homEquiv _ _).symm
      ((am.homEquiv _ _).symm (an.unit.app M ≫ e.inv.app (H.obj M)))) := by
  let ac := am.comp aq
  let an' := an.ofNatIsoRight e.symm
  have he : (aq.homEquiv _ _).symm
      ((am.homEquiv _ _).symm (an.unit.app M ≫ e.inv.app (H.obj M))) =
      (ac.leftAdjointUniq an').hom.app M := by
    apply (ac.homEquiv _ _).injective
    calc
      _ = an.unit.app M ≫ e.inv.app (H.obj M) := by
        dsimp only [ac]
        rw [Adjunction.comp_homEquiv]
        change am.homEquiv _ _ (aq.homEquiv _ _
          ((aq.homEquiv _ _).symm ((am.homEquiv _ _).symm
            (an.unit.app M ≫ e.inv.app (H.obj M))))) = _
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      _ = an'.unit.app M := by
        simp only [an', Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
          Functor.whiskerLeft_app, Iso.symm_hom]
      _ = _ := (Adjunction.homEquiv_leftAdjointUniq_hom_app ac an' M).symm
  rw [he]
  infer_instance

private theorem compatible_adjoint_isIso
    {B C : Type*} [Category B] [Category C]
    {L : B ⥤ C} {R : C ⥤ B} (aq : L ⊣ R)
    {M M' : B} {N N' : C} (em : M ≅ M') (en : N ≅ N')
    (t : M ⟶ R.obj N) (u : M' ⟶ R.obj N')
    (h : t ≫ R.map en.hom = em.hom ≫ u)
    (hu : IsIso ((aq.homEquiv _ _).symm u)) :
    IsIso ((aq.homEquiv _ _).symm t) := by
  have hf : (aq.homEquiv _ _).symm t ≫ en.hom =
      L.map em.hom ≫ (aq.homEquiv _ _).symm u := by
    apply (aq.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact h
  have : IsIso ((aq.homEquiv _ _).symm t ≫ en.hom) := by
    rw [hf]
    infer_instance
  exact IsIso.of_isIso_comp_right _ en.hom

private theorem complex_mate_isIso
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    {F : A ⥤ B} {G : B ⥤ A} (am : F ⊣ G) [F.Additive] [G.Additive]
    {H : A ⥤ C} {J : C ⥤ A} (an : H ⊣ J) [H.Additive] [J.Additive]
    {L : B ⥤ C} {R : C ⥤ B} (aq : L ⊣ R) [L.Additive] [R.Additive]
    (e : R ⋙ G ≅ J) (τ : F ⟶ H ⋙ R)
    (hτ : ∀ M, τ.app M = (am.homEquiv _ _).symm
      (an.unit.app M ≫ e.inv.app (H.obj M))) (P : CochainComplex A ℤ) :
    IsIso (((aq.mapHomologicalComplex (.up ℤ)).homEquiv
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((H.mapHomologicalComplex (.up ℤ)).obj P)).symm
        ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app P)) := by
  let g := ((aq.mapHomologicalComplex (.up ℤ)).homEquiv
    ((F.mapHomologicalComplex (.up ℤ)).obj P)
    ((H.mapHomologicalComplex (.up ℤ)).obj P)).symm
      ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app P)
  have hi (k : ℤ) : IsIso (g.f k) := by
    change IsIso ((aq.homEquiv _ _).symm (τ.app (P.X k)))
    rw [hτ]
    exact composite_mate_isIso am an aq e (P.X k)
  exact HomologicalComplex.Hom.isIso_of_components g

private theorem canonical_quotient_adjoint_isIso {Y : Scheme.{t}}
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (S : CoefficientDerivedSystemTensors l E Y)
    (D : CoefficientFiniteQuotientCalculus l E Y S) {m n : ℕ} (hmn : n ≤ m) :
    IsIso ((((D.ordinaryAdjunction hmn).mapHomologicalComplex (.up ℤ)).homEquiv
      (((scalarReductionExtension l E Y m).mapHomologicalComplex (.up ℤ)).obj P)
      (((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P)).symm
        ((NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E Y hmn)
          (.up ℤ)).app P)) := by
  exact complex_mate_isIso
    (F := scalarReductionExtension l E Y m) (G := scalarReductionRestriction l E Y m)
    (scalarReductionExtension_adjunction l E Y m).choose
    (H := scalarReductionExtension l E Y n) (J := scalarReductionRestriction l E Y n)
    (scalarReductionExtension_adjunction l E Y n).choose
    (L := coefficientFiniteQuotientExtension l E Y hmn)
    (R := normalizedDVRModuleRes l E Y hmn) (D.ordinaryAdjunction hmn)
    (eqToIso (coefficientRestrictionComp l E Y hmn))
    (coefficientOrdinaryQuotient l E Y hmn)
    (by
      intro M
      have ht := (coefficientOrdinaryQuotient_exists l E Y hmn).choose_spec.1 M
      dsimp only [coefficientOrdinaryQuotientComponent, coefficientQuotientNatTrans] at ht
      unfold coefficientOrdinaryQuotient
      exact ht) P

private theorem input_adjoint_isIso {Y : Scheme.{t}} (K : Complex l E Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (κ : ∀ n : ℕ, level l E K n ≅
      ((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P)
    (hκ : ∀ {m n : ℕ} (hmn : n ≤ m),
      transition l E K hmn ≫
          ((normalizedDVRModuleRes l E Y hmn).mapHomologicalComplex (.up ℤ)).map
            (κ n).hom =
        (κ m).hom ≫
          (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E Y hmn)
            (.up ℤ)).app P)
    (S : CoefficientDerivedSystemTensors l E Y)
    (D : CoefficientFiniteQuotientCalculus l E Y S) {m n : ℕ} (hmn : n ≤ m) :
    IsIso (ordinaryAlpha l E K S D hmn) := by
  exact compatible_adjoint_isIso
    ((D.ordinaryAdjunction hmn).mapHomologicalComplex (.up ℤ)) (κ m) (κ n)
    (transition l E K hmn)
    ((NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E Y hmn)
      (.up ℤ)).app P) (hκ hmn)
    (canonical_quotient_adjoint_isIso l E P S D hmn)

-- The adjunction-unit calculation is the same categorical argument as
-- QuotientOperationAdjointFactorizations.transpose_of_unit, with only one ε component.
private theorem transpose_from_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {E : A ⥤ B} {U : B ⥤ A} (am : E ⊣ U)
    (I : A ⥤ C) (J : B ⥤ D) {F : C ⥤ D} {R : D ⥤ C} (ad : F ⊣ R)
    (ρ : J ⋙ R ≅ U ⋙ I) (P : A) (ε : F.obj (I.obj P) ⟶ J.obj (E.obj P))
    (hu : ad.unit.app (I.obj P) ≫ R.map ε ≫ ρ.hom.app (E.obj P) =
      I.map (am.unit.app P)) (H : B) (g : P ⟶ U.obj H) :
    (ad.homEquiv _ _).symm (I.map g ≫ ρ.inv.app H) =
      ε ≫ J.map ((am.homEquiv _ _).symm g) := by
  apply (ad.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, ad.homEquiv_unit, R.map_comp, ← Category.assoc]
  have hu' : ad.unit.app (I.obj P) ≫ R.map ε =
      I.map (am.unit.app P) ≫ ρ.inv.app (E.obj P) := by
    apply (cancel_mono (ρ.hom.app (E.obj P))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact hu.trans (Category.comp_id _).symm
  rw [hu', Category.assoc]
  have hn := ρ.inv.naturality ((am.homEquiv P H).symm g)
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← I.map_comp]
  have hg : am.unit.app P ≫ U.map ((am.homEquiv P H).symm g) = g := by
    exact (am.homEquiv_unit P H ((am.homEquiv P H).symm g)).symm.trans
      ((am.homEquiv P H).apply_symm_apply g)
  rw [hg]

private theorem alpha_eq_model {W : Scheme.{t}} (K : Complex l E W)
    (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m)
    (hK : Good l E K m) :
    alpha l E K S D hmn =
      (coefficientFiniteQuotientModel l E W hmn (level l E K m) hK.1).hom ≫
        DerivedCategory.Q.map (ordinaryAlpha l E K S D hmn) := by
  exact transpose_from_unit
    ((D.ordinaryAdjunction hmn).mapHomologicalComplex (.up ℤ))
    DerivedCategory.Q DerivedCategory.Q (D.adjunction hmn)
    (normalizedDVRModuleRes l E W hmn).mapDerivedCategoryFactors
    (level l E K m)
    (coefficientFiniteQuotientModel l E W hmn (level l E K m) hK.1).hom
    (D.unit_model hmn (level l E K m) hK.1) (level l E K n)
    (transition l E K hmn)

private theorem iso_restriction_sections
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {A B : Sheaf J RingCat.{w}} (φ : A ⟶ B)
    {F : SheafOfModules.{w} A ⥤ SheafOfModules.{w} B}
    (ad : F ⊣ SheafOfModules.restrictScalars φ)
    {M : SheafOfModules.{w} A} {N : SheafOfModules.{w} B}
    (e : F.obj M ≅ N) (t : M ⟶ (SheafOfModules.restrictScalars φ).obj N)
    (he : ad.homEquiv _ _ e.hom = t)
    (j : ∀ U : Cᵒᵖ, M.val.obj U → (F.obj M).val.obj U)
    (hj : ∀ U x, coefficientRestrictionSection φ (F.obj M) U
      (((ad.unit.app M).val.app U) x) = j U x)
    (U : Cᵒᵖ) (x : M.val.obj U) (b : B.obj.obj U) :
    e.hom.val.app U (b • j U x) =
        b • coefficientRestrictionSection φ N U (t.val.app U x) ∧
      e.inv.val.app U (b • coefficientRestrictionSection φ N U (t.val.app U x)) =
        b • j U x := by
  rw [Adjunction.homEquiv_unit] at he
  have hx := congrArg (fun z ↦ z.val.app U x) he
  change e.hom.val.app U (((ad.unit.app M).val.app U) x) =
    coefficientRestrictionSection φ N U (t.val.app U x) at hx
  have hunit := hj U x
  change ((ad.unit.app M).val.app U) x = j U x at hunit
  rw [hunit] at hx
  constructor
  · simpa only [map_smul] using congrArg (fun z ↦ b • z) hx
  · rw [← hx, map_smul]
    have hi := congrArg (fun z ↦ z.val.app U (j U x)) e.hom_inv_id
    change e.inv.val.app U (e.hom.val.app U (j U x)) = j U x at hi
    exact congrArg (fun z ↦ b • z) hi

private theorem adjointModel_of_isIso {W : Scheme.{t}} (K : Complex l E W)
    (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m)
    (hK : Good l E K m) (ha : IsIso (ordinaryAlpha l E K S D hmn)) :
    AdjointModel l E K S D hmn hK.1 := by
  let a := asIso (ordinaryAlpha l E K S D hmn)
  refine ⟨a, ?_, alpha_eq_model l E K S D hmn hK, ?_⟩
  · exact ((D.ordinaryAdjunction hmn).mapHomologicalComplex (.up ℤ)).homEquiv
      _ _ |>.apply_symm_apply (transition l E K hmn)
  · intro k U x b
    let ak := (HomologicalComplex.eval _ (.up ℤ) k).mapIso a
    have ht : (D.ordinaryAdjunction hmn).homEquiv _ _ ak.hom =
        (transition l E K hmn).f k :=
      (D.ordinaryAdjunction hmn).homEquiv _ _ |>.apply_symm_apply
        ((transition l E K hmn).f k)
    exact iso_restriction_sections (normalizedDVRQuotient l E W hmn)
      (D.ordinaryAdjunction hmn) ak ((transition l E K hmn).f k) ht
      (coefficientFiniteQuotientUnitSection l E W hmn ((level l E K m).X k))
      (D.ordinary_unit hmn ((level l E K m).X k)) U x b

private theorem comparison_cancel
    {C : Type*} [Category C] {A B D F : C}
    (a : A ⟶ B) (b : B ⟶ D) (e : F ≅ D) :
    (a ≫ b ≫ e.inv) ≫ e.hom = a ≫ b := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem sequence_transition_fac {W : Scheme.{t}} (K : Complex l E W)
    {m n : ℕ} (hmn : n ≤ m) :
    (coefficientSequenceDerivedTransition l E W hmn).app (DerivedCategory.Q.obj K) ≫
        (normalizedDVRRes l E W hmn).map
          ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app K) ≫
        (normalizedDVRModuleRes l E W hmn).mapDerivedCategoryFactors.hom.app
          (level l E K n) =
      (coefficientSequenceEvaluation l E W m).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map (transition l E K hmn) := by
  unfold coefficientSequenceDerivedTransition
  dsimp only [NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors]
  rw [Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso]
  exact comparison_cancel
    ((coefficientSequenceEvaluation l E W m).mapDerivedCategoryFactors.hom.app K)
    (DerivedCategory.Q.map (transition l E K hmn))
    ((coefficientSequenceEvaluation l E W n ⋙
      normalizedDVRModuleRes l E W hmn).mapDerivedCategoryFactors.app K)

private theorem conjugate_adjoint
    {B C : Type*} [Category B] [Category C]
    {L : B ⥤ C} {R : C ⥤ B} (aq : L ⊣ R)
    {M M' : B} {N N' : C} (em : M ≅ M') (en : N ≅ N')
    (t : M ⟶ R.obj N) (u : M' ⟶ R.obj N')
    (h : t ≫ R.map en.hom = em.hom ≫ u) :
    (aq.homEquiv _ _).symm t =
      L.map em.hom ≫ (aq.homEquiv _ _).symm u ≫ en.inv := by
  apply (cancel_mono en.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (aq.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h

private theorem normalized_of_adjoint_isIso {W : Scheme.{t}} (K : Complex l E W)
    (hK : ∀ n, Good l E K n)
    (ha : ∀ (S : CoefficientDerivedSystemTensors l E W)
      (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m),
      IsIso (ordinaryAlpha l E K S D hmn)) :
    IsNormalizedCoefficientSequence l E W (DerivedCategory.Q.obj K) := by
  obtain ⟨S, _⟩ := coefficientDerivedSystemEvaluationCalculus l E W
  let D := S.quotientCalculus
  intro m n hmn P
  let em := (coefficientSequenceEvaluation l E W m).mapDerivedCategoryFactors.app K
  let en := (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.app K
  let a := ((D.adjunction hmn).homEquiv _ _).symm
    ((coefficientSequenceDerivedTransition l E W hmn).app (DerivedCategory.Q.obj K))
  have ht := sequence_transition_fac l E K hmn
  have hα : a = (coefficientFiniteQuotientDerived l E W hmn).map em.hom ≫
      alpha l E K S.toCoefficientDerivedSystemTensors D hmn ≫ en.inv := by
    have hh :
        (coefficientSequenceDerivedTransition l E W hmn).app (DerivedCategory.Q.obj K) ≫
            (normalizedDVRRes l E W hmn).map en.hom =
          em.hom ≫ (DerivedCategory.Q.map (transition l E K hmn) ≫
            (normalizedDVRModuleRes l E W hmn).mapDerivedCategoryFactors.inv.app
              (level l E K n)) := by
      exact (((normalizedDVRModuleRes l E W hmn).mapDerivedCategoryFactors.app
        (level l E K n)).eq_comp_inv.mpr
          ((Category.assoc _ _ _).trans ht)).trans (Category.assoc _ _ _)
    exact conjugate_adjoint (D.adjunction hmn) em en
      ((coefficientSequenceDerivedTransition l E W hmn).app (DerivedCategory.Q.obj K))
      (DerivedCategory.Q.map (transition l E K hmn) ≫
        (normalizedDVRModuleRes l E W hmn).mapDerivedCategoryFactors.inv.app
          (level l E K n)) hh
  have : IsIso (ordinaryAlpha l E K S.toCoefficientDerivedSystemTensors D hmn) :=
    ha _ D hmn
  have : IsIso (alpha l E K S.toCoefficientDerivedSystemTensors D hmn) := by
    rw [alpha_eq_model l E K S.toCoefficientDerivedSystemTensors D hmn (hK m)]
    infer_instance
  have : IsIso a := by rw [hα]; infer_instance
  have hb := ((D.adjunction hmn).homEquiv _ P).bijective.comp
    (Iso.homCongr (asIso a).symm (Iso.refl P)).bijective
  simpa only [Function.comp_def, Iso.homCongr_apply, Iso.symm_inv, asIso_hom,
    Iso.refl_hom, Category.comp_id, Adjunction.homEquiv_naturality_right,
    a, Equiv.apply_symm_apply] using hb

private theorem pull_adjoint_isIso {V W : Scheme.{t}} (g : V ⟶ W)
    (K : Complex l E W)
    (ha : ∀ (S : CoefficientDerivedSystemTensors l E W)
      (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m),
      IsIso (ordinaryAlpha l E K S D hmn))
    (SV : CoefficientDerivedSystemTensors l E V)
    (DV : CoefficientFiniteQuotientCalculus l E V SV) {m n : ℕ} (hmn : n ≤ m) :
    IsIso (ordinaryAlpha l E (pull l E g K) SV DV hmn) := by
  obtain ⟨S, _⟩ := coefficientDerivedSystemEvaluationCalculus l E W
  let DW := S.quotientCalculus
  obtain ⟨em, en, χ, _, _, _, he⟩ :=
    (strictPullbackAdjointConstructor l E g K).2.2
      S.toCoefficientDerivedSystemTensors DW SV DV hmn
  let a := @asIso _ _ _ _ (ordinaryAlpha l E K S.toCoefficientDerivedSystemTensors DW hmn)
    (ha _ DW hmn)
  let L := (coefficientFiniteQuotientExtension l E V hmn).mapHomologicalComplex (.up ℤ)
  let e := L.mapIso em ≪≫ (χ ≪≫ (finitePull l E g n).mapIso a)
  have he' : e.hom = ordinaryAlpha l E (pull l E g K) SV DV hmn ≫ en.hom := he
  have hh : ordinaryAlpha l E (pull l E g K) SV DV hmn = (e ≪≫ en.symm).hom :=
    en.eq_comp_inv.mpr he'.symm
  rw [hh]
  exact (e ≪≫ en.symm).isIso_hom

/-- Given the strict K-flat models and their actual quotient maps, the derived
normalization and the tensor/pullback adjoint equations follow by induction on
`Generated`. This is the operation part of the simultaneous normalization argument.

STATEMENT-DISPUTED: the earlier signature omitted actual quotient-transition
compatibility. Levelwise Goodness permits zero horizontal maps and does not imply normalization.
The data P, κ and hκ restore the actual-quotient hypothesis supplied by the caller.

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 07A6;
(blueprint: lem-pur-quotient-expression-kflat-operations).
-/
theorem quotientExpressionKFlatOperations
    {Z X Y : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (r : ℕ) (N : Fin r → Complex l E Y)
    (P : Fin r → CochainComplex (scalarReductionSource l E Y) ℤ)
    (κ : ∀ (i : Fin r) (n : ℕ), level l E (N i) n ≅
      ((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj (P i))
    (hκ : ∀ (i : Fin r) {m n : ℕ} (hmn : n ≤ m),
      transition l E (N i) hmn ≫
          ((normalizedDVRModuleRes l E Y hmn).mapHomologicalComplex (.up ℤ)).map
            (κ i n).hom =
        (κ i m).hom ≫
          (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E Y hmn)
            (.up ℤ)).app (P i))
    (hgood : ∀ (W : Scheme.{t}) (K : Complex l E W), Generated l E h f N W K →
      ∀ n : ℕ, Good l E K n) :
    (∀ (W : Scheme.{t}) (K : Complex l E W), Generated l E h f N W K →
      IsNormalizedCoefficientSequence l E W (DerivedCategory.Q.obj K) ∧
      (∀ (S : CoefficientDerivedSystemTensors l E W)
        (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m),
        ∃ hK : CochainComplex.IsKFlatIndependentCoefficients
          (R := integralCoefficientCommRingSheaf l E W m) (level l E K m),
          AdjointModel l E K S D hmn hK)) ∧
    (∀ (W : Scheme.{t}) (U V : Complex l E W),
      Generated l E h f N W U → Generated l E h f N W V →
      TensorTransitions l E U V ∧
      (∀ (n : ℕ) (S : CoefficientDerivedSystemTensors l E W),
        ∃ (hU : Good l E U n) (hV : Good l E V n)
          (e : DerivedCategory.Q.obj (level l E (total l E U V) n) ≅
            (S.finiteClosed n).tensor.obj
              (DerivedCategory.Q.obj (level l E U n), DerivedCategory.Q.obj (level l E V n))),
          e.hom = DerivedCategory.Q.map (coefficientEvaluationTensorIso l E W n U V).hom ≫
            ((S.finiteTensorModel n).iso (Scheme.ProEt.topology W)
              (integralCoefficientCommRingSheaf l E W n) (S.finiteClosed n)
              (level l E U n) (level l E V n) hU.1 hV.1).hom) ∧
      (∀ (S : CoefficientDerivedSystemTensors l E W)
        (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m)
        (hUm : Good l E U m) (hVm : Good l E V m)
        (hUn : Good l E U n) (hVn : Good l E V n),
        TensorAdjointEquation l E U V S D hmn hUm hVm hUn hVn)) ∧
    (∀ {V W : Scheme.{t}} (g : V ⟶ W), AllowedArrow h f g →
      ∀ K : Complex l E W, Generated l E h f N W K →
        PullbackTransitions l E g K ∧
        (∀ n : ℕ, PullbackModel l E g K n ∧ PullbackComputes l E g K n) ∧
        (∀ (SW : CoefficientDerivedSystemTensors l E W)
          (DW : CoefficientFiniteQuotientCalculus l E W SW)
          (SV : CoefficientDerivedSystemTensors l E V)
          (DV : CoefficientFiniteQuotientCalculus l E V SV) {m n : ℕ} (hmn : n ≤ m),
          PullbackAdjointEquation l E g K SW DW SV DV hmn)) := by
  have ha : ∀ (W : Scheme.{t}) (K : Complex l E W), Generated l E h f N W K →
      ∀ (S : CoefficientDerivedSystemTensors l E W)
        (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m),
        IsIso (ordinaryAlpha l E K S D hmn) := by
    intro W K hK
    induction hK with
    | input i => exact input_adjoint_isIso l E (N i) (P i) (κ i) (hκ i)
    | unitY => exact strictUnitOrdinaryAdjoint l E Y
    | unitX => exact strictUnitOrdinaryAdjoint l E X
    | unitZ => exact strictUnitOrdinaryAdjoint l E Z
    | @tensor W U V hU hV ihU ihV =>
        intro S D m n hmn
        exact ((strictTensorAdjointConstructor l E U V).2 S D hmn
          (hgood W U hU m) (hgood W V hV m) (hgood W U hU n) (hgood W V hV n)).1
            (ihU S D hmn) (ihV S D hmn)
    | @pullF U hU ihU => exact pull_adjoint_isIso l E f U ihU
    | @pullH U hU ihU => exact pull_adjoint_isIso l E h U ihU
    | @pullHF U hU ihU => exact pull_adjoint_isIso l E (h ≫ f) U ihU
  refine ⟨?_, ?_, ?_⟩
  · intro W K hK
    refine ⟨normalized_of_adjoint_isIso l E K (hgood W K hK) (ha W K hK), ?_⟩
    intro S D m n hmn
    exact ⟨(hgood W K hK m).1,
      adjointModel_of_isIso l E K S D hmn (hgood W K hK m) (ha W K hK S D hmn)⟩
  · intro W U V hU hV
    refine ⟨(strictTensorAdjointConstructor l E U V).1, ?_, ?_⟩
    · intro n S
      exact ⟨hgood W U hU n, hgood W V hV n,
        tensorComparison l E U V n S (hgood W U hU n) (hgood W V hV n), rfl⟩
    · intro S D m n hmn hUm hVm hUn hVn
      exact ((strictTensorAdjointConstructor l E U V).2 S D hmn hUm hVm hUn hVn).2
  · intro V W g _ K _
    exact strictPullbackAdjointConstructor l E g K

end WeilConjectures.StrictQuotient

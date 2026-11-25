/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Compact.CompactSupportSystemEvaluationDiagram
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import all WeilConjectures.SmoothPurity.Supporting.NativeConstantRestrictionAcyclicity
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientRestrictionSectionEvaluationAcyclic
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
import WeilConjectures.AlgebraicGeometry.Sites.KInjectiveComparisonPrinciple
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Acyclicity of evaluated K-injective coefficient systems

Source: Zheng, Construction 4.1 and Lemma 4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective
  WeilConjectures.SemilinearSections.moduleAbelian WeilConjectures.SemilinearSections.hasDerived
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor

universe t u c d cv dv r m

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

attribute [local irreducible] constantSheaf presheafToSheaf Functor.leftAdjoint limit

namespace WeilConjectures

open SheafOfModules (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem quasiIso_of_homotopy
    {A : Type*} [Category A] [Abelian A] {M N : CochainComplex A ℤ}
    {f g : M ⟶ N} (h : Homotopy f g) [QuasiIso g] : QuasiIso f := by
  constructor
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap, h.homologyMap_eq i]
  infer_instance

private theorem comparison_sections
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D] [HasDerivedCategory B]
    (R : A ⥤ B) [R.Additive] [R.PreservesHomology]
    (F : B ⥤ D) [F.Additive]
    {M I : CochainComplex A ℤ} (r : M ⟶ I) [QuasiIso r] [I.IsKInjective]
    (T : CochainComplex B ℤ) [T.IsKInjective]
    (s : (R.mapHomologicalComplex (.up ℤ)).obj M ⟶ T) [QuasiIso s]
    (hs : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map s))
    (hacyc : ∀ (h : (R.mapHomologicalComplex (.up ℤ)).obj I ⟶ T) [QuasiIso h],
      QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map h)) :
    QuasiIso (((R ⋙ F).mapHomologicalComplex (.up ℤ)).map r) := by
  let rr := (R.mapHomologicalComplex (.up ℤ)).map r
  have : QuasiIso rr := inferInstance
  let q := HomotopyCategory.quotient B (.up ℤ)
  obtain ⟨h, hh⟩ := (CochainComplex.IsKInjective.precomp_bijective_of_quasiIso rr T).surjective
    (q.map s)
  obtain ⟨h, rfl⟩ := q.map_surjective h
  have ho : Homotopy (rr ≫ h) s := HomotopyCategory.homotopyOfEq _ _
    (by simpa only [q, Functor.map_comp] using hh)
  have : QuasiIso (rr ≫ h) := quasiIso_of_homotopy ho
  have : QuasiIso h := quasiIso_of_comp_left rr h
  have := hs
  have : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map (rr ≫ h)) :=
    quasiIso_of_homotopy (F.mapHomotopy ho)
  have := hacyc h
  have : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map rr ≫
      (F.mapHomologicalComplex (.up ℤ)).map h) := by
    rw [← Functor.map_comp]
    infer_instance
  have hrr : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map rr) :=
    quasiIso_of_comp_right ((F.mapHomologicalComplex (.up ℤ)).map rr)
      ((F.mapHomologicalComplex (.up ℤ)).map h)
  exact hrr

private theorem scalar_comparison_sections
    {C : Type c} [Category.{cv} C] (K : GrothendieckTopology C)
    [K.HasSheafCompose (forget₂ CommRingCat.{max c cv r} RingCat.{max c cv r})]
    [HasSheafify K AddCommGrpCat.{max c cv r}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max c cv r}]
    (B D : Sheaf K RingCat.{max c cv r})
    (hB : ∀ (U : Cᵒᵖ) (x y : B.obj.obj U), x * y = y * x)
    (hD : ∀ (U : Cᵒᵖ) (x y : D.obj.obj U), x * y = y * x)
    (a : B ⟶ D)
    {M I : CochainComplex (SheafOfModules.{max c cv r} D) ℤ}
    [I.IsKInjective] (f : M ⟶ I) [QuasiIso f]
    (T : CochainComplex (SheafOfModules.{max c cv r} B) ℤ) [T.IsKInjective]
    (s : ((SheafOfModules.restrictScalars.{max c cv r} a).mapHomologicalComplex
      (.up ℤ)).obj M ⟶ T) [QuasiIso s] (U : C)
    (hs : QuasiIso (((SheafOfModules.toSheaf.{max c cv r} B ⋙
      sheafToPresheaf K AddCommGrpCat.{max c cv r} ⋙
      (evaluation _ _).obj (op U)).mapHomologicalComplex (.up ℤ)).map s)) :
    QuasiIso (((SheafOfModules.toSheaf.{max c cv r} D ⋙
      sheafToPresheaf K AddCommGrpCat.{max c cv r} ⋙
      (evaluation _ _).obj (op U)).mapHomologicalComplex (.up ℤ)).map f) := by
  let R := SheafOfModules.restrictScalars.{max c cv r} a
  let F := SheafOfModules.toSheaf.{max c cv r} B ⋙
    sheafToPresheaf K AddCommGrpCat.{max c cv r} ⋙ (evaluation _ _).obj (op U)
  have : PreservesFiniteLimits R := by
    have : PreservesFiniteLimits (R ⋙ SheafOfModules.toSheaf.{max c cv r} B) :=
      inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{max c cv r} D))
    exact preservesFiniteLimits_of_reflects_of_preserves R
      (SheafOfModules.toSheaf.{max c cv r} B)
  have : PreservesFiniteColimits R := by
    have : PreservesFiniteColimits (SheafOfModules.toSheaf.{max c cv r} B) :=
      (CategoryTheory.moduleSheaves_colimits_forgetful B).2.2.1
    have : PreservesFiniteColimits (SheafOfModules.toSheaf.{max c cv r} D) :=
      (CategoryTheory.moduleSheaves_colimits_forgetful D).2.2.1
    have : PreservesFiniteColimits (R ⋙ SheafOfModules.toSheaf.{max c cv r} B) :=
      inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{max c cv r} D))
    have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{max c cv r} B) := inferInstance
    exact preservesFiniteColimits_of_reflects_of_preserves R
      (SheafOfModules.toSheaf.{max c cv r} B)
  let := HasDerivedCategory.standard (SheafOfModules.{max c cv r} B)
  exact comparison_sections R F f T s hs (fun h _ ↦
    SheafOfModules.coefficientRestrictionSectionsEvaluation_quasiIso.{c, cv, r}
      B D hB hD a I T h U)

private instance pushforward_additive
    {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous K L]
    {R : Sheaf L RingCat.{r}} {S : Sheaf K RingCat.{r}}
    (a : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} K L).obj R) :
    (SheafOfModules.pushforward.{m} a).Additive := by
  constructor
  intro M N f g
  ext U x
  rfl

private theorem pushforward_quasiIso_of_sections
    {C D : Type c} [Category.{cv} C] [Category.{cv} D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D}
    [HasSheafify K AddCommGrpCat.{max c cv r}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max c cv r}]
    (F : C ⥤ D) [F.IsContinuous K L]
    {R : Sheaf L RingCat.{max c cv r}} {S : Sheaf K RingCat.{max c cv r}}
    (a : S ⟶ (F.sheafPushforwardContinuous RingCat.{max c cv r} K L).obj R)
    {M N : CochainComplex (SheafOfModules.{max c cv r} R) ℤ} (f : M ⟶ N)
    (hf : ∀ U : D, QuasiIso (((SheafOfModules.toSheaf.{max c cv r} R ⋙
      sheafToPresheaf L AddCommGrpCat.{max c cv r} ⋙
      (evaluation _ _).obj (op U)).mapHomologicalComplex (.up ℤ)).map f)) :
    QuasiIso (((SheafOfModules.pushforward.{max c cv r} a).mapHomologicalComplex
      (.up ℤ)).map f) := by
  apply CategoryTheory.quasiIso_of_sectionsOfUniverses.{c, cv, r}
  intro U
  exact hf (F.obj U)

private theorem derivedUnit_of_resolution
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive]
    {M I : CochainComplex A ℤ} [I.IsKInjective] (r : M ⟶ I) [QuasiIso r]
    [QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map r)] :
    IsIso (F.rightDerivedFunctorUnitQ M) := by
  have hn := F.rightDerivedFunctorUnitQ_naturality r
  have : IsIso (F.rightDerivedFunctorUnitQ M ≫
      F.rightDerivedFunctor.map (DerivedCategory.Q.map r)) := by
    rw [← hn, Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.rightDerivedFunctor.map (DerivedCategory.Q.map r))

private def restriction_pushforward_square
    {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {RX SX : Sheaf K RingCat.{r}} {RY SY : Sheaf J RingCat.{r}}
    (aX : RX ⟶ SX) (aY : RY ⟶ SY)
    (bA : RY ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj RX)
    (bB : SY ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj SX)
    (h : bA ≫ (F.sheafPushforwardContinuous RingCat.{r} J K).map aX = aY ≫ bB) :
    SheafOfModules.restrictScalars.{m} aX ⋙ SheafOfModules.pushforward.{m} bA ≅
      SheafOfModules.pushforward.{m} bB ⋙ SheafOfModules.restrictScalars.{m} aY :=
  SheafOfModules.pushforwardComp.{m} (F := F) (G := 𝟭 D) bA aX ≪≫
    SheafOfModules.pushforwardCongr.{m} h ≪≫
      (SheafOfModules.pushforwardComp.{m} (F := 𝟭 C) (G := F) aY bB).symm

private theorem constantEvaluation_kinjective_generic
    {C : Type c} [Category.{cv} C] (K : GrothendieckTopology C)
    [HasSheafify K AddCommGrpCat.{m}] [K.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasSheafify (coefficientSequenceTopology K) AddCommGrpCat.{m}]
    [(coefficientSequenceTopology K).WEqualsLocallyBijective AddCommGrpCat.{m}]
    (O : Sheaf K RingCat.{m}) (n : ℕ)
    [(Prod.sectR n C).IsContinuous K (coefficientSequenceTopology K)]
    (T : CochainComplex (SheafOfModules.{m} (NativeConstantModel.sequenceRing K O)) ℤ)
    [T.IsKInjective] :
    CochainComplex.IsKInjective (((SheafOfModules.pushforward.{m}
      (F := Prod.sectR n C) (J := K) (K := coefficientSequenceTopology K)
      (R := NativeConstantModel.sequenceRing K O) (S := O) (𝟙 O)).mapHomologicalComplex
        (.up ℤ)).obj T) := by
  let e := NativeConstantModel.sequenceEquivalence K O
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : CochainComplex.IsKInjective
      ((e.functor.mapHomologicalComplex (.up ℤ)).obj T) := inferInstance
  exact CategoryTheory.tower_evaluation_isKInjective _
    ((e.functor.mapHomologicalComplex (.up ℤ)).obj T) (op n)

private abbrev integralRing (W : Scheme.{t}) :=
  integralConstantRingOfUniverses l E W

private abbrev sequenceIntegralRing (W : Scheme.{t}) :=
  NativeConstantModel.sequenceRing (Scheme.ProEt.topology W) (integralRing l E W)

private abbrev integralCommRing (W : Scheme.{t}) :
    Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)} :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).obj
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))

private def constantQuotient (W : Scheme.{t}) (n : ℕ) :
    integralCommRing l E W ⟶ integralCoefficientCommRingSheaf l E W n :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map
    (CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom)))

private def constantQuotientCone (W : Scheme.{t}) :
    (Functor.const ℕᵒᵖ).obj (integralCommRing l E W) ⟶
      coefficientSequenceCommRingSystem l E W :=
  NatTrans.ofOpSequence (constantQuotient l E W) (by
    intro n
    apply (sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map_injective
    simp only [Functor.map_comp, Functor.const_obj_map,
      coefficientSequenceCommRingSystem, Functor.ofOpSequence_map_homOfLE_succ]
    change integralConstantQuotientOfUniverses l E W n =
      integralConstantQuotientOfUniverses l E W (n + 1) ≫
        integralCoefficientSheafTransition l E W n
    have h := integralConstantQuotientOfUniverses_compatibility l E W n
    simp only [Functor.const_obj_map, integralCoefficientSheafSystem,
      Functor.ofOpSequence_map_homOfLE_succ] at h
    exact (Category.id_comp _).symm.trans h)

private def sequenceIntegralCommRingMap (W : Scheme.{t}) :
    NativeConstantModel.sequenceCommRing (Scheme.ProEt.topology W) (integralCommRing l E W) ⟶
      coefficientSequenceCommRingSheaf l E W where
  hom :=
    { app U := ((constantQuotientCone l E W).app (op U.unop.1)).hom.app (op U.unop.2)
      naturality := by
        intro U V f
        have hn := congrArg (fun k ↦ k.hom.app (op U.unop.2))
          ((constantQuotientCone l E W).naturality f.unop.1.op)
        change ((constantQuotientCone l E W).app (op V.unop.1)).hom.app (op U.unop.2) =
          ((constantQuotientCone l E W).app (op U.unop.1)).hom.app (op U.unop.2) ≫
            ((coefficientSequenceCommRingSystem l E W).map f.unop.1.op).hom.app
              (op U.unop.2) at hn
        change (integralCommRing l E W).obj.map f.unop.2.op ≫
            ((constantQuotientCone l E W).app (op V.unop.1)).hom.app (op V.unop.2) =
          ((constantQuotientCone l E W).app (op U.unop.1)).hom.app (op U.unop.2) ≫
            (((coefficientSequenceCommRingSystem l E W).map f.unop.1.op).hom.app
              (op U.unop.2) ≫
                ((coefficientSequenceCommRingSystem l E W).obj (op V.unop.1)).obj.map
                  f.unop.2.op)
        rw [← Category.assoc, ← hn]
        exact ((constantQuotientCone l E W).app (op V.unop.1)).hom.naturality f.unop.2.op }

private def sequenceIntegralMap (W : Scheme.{t}) :
    sequenceIntegralRing l E W ⟶
      (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          (coefficientSequenceCommRingSheaf l E W) :=
  (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (sequenceIntegralCommRingMap l E W)

private abbrev sequenceIntegralRestriction (W : Scheme.{t}) :=
  SheafOfModules.restrictScalars.{max u (t + 1)} (sequenceIntegralMap l E W)

private abbrev integralEvaluation (W : Scheme.{t}) (n : ℕ) :=
  SheafOfModules.pushforward.{max u (t + 1)} (F := Prod.sectR n W.ProEt)
    (J := Scheme.ProEt.topology W) (K := coefficientSequenceTopology (Scheme.ProEt.topology W))
    (R := sequenceIntegralRing l E W) (S := integralRing l E W) (𝟙 (integralRing l E W))

attribute [local irreducible] sequenceIntegralMap sequenceIntegralCommRingMap
  constantQuotientCone constantQuotient

private def integralEvaluationSquare (W : Scheme.{t}) (n : ℕ) :
    sequenceIntegralRestriction l E W ⋙ integralEvaluation l E W n ≅
      coefficientSequenceEvaluation l E W n ⋙
        SheafOfModules.restrictScalars.{max u (t + 1)}
          (integralConstantQuotientOfUniverses l E W n) := by
  let ι := Prod.sectR n W.ProEt
  let O := integralRing l E W
  let a := sequenceIntegralMap l E W
  let q := integralConstantQuotientOfUniverses l E W n
  let φ := eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm
  have he : (𝟙 O) ≫ (ι.sheafPushforwardContinuous RingCat.{max u (t + 1)}
      (Scheme.ProEt.topology W) (coefficientSequenceTopology (Scheme.ProEt.topology W))).map a =
      q ≫ φ := by
    ext U x
    change _ = ((eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm).hom.app U)
      ((q.hom.app U) x)
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
    unfold a sequenceIntegralMap sequenceIntegralCommRingMap constantQuotientCone
      constantQuotient
    rfl
  change SheafOfModules.restrictScalars.{max u (t + 1)} a ⋙
      SheafOfModules.pushforward.{max u (t + 1)} (F := ι) (𝟙 O) ≅
    SheafOfModules.pushforward.{max u (t + 1)} (F := ι) φ ⋙
      SheafOfModules.restrictScalars.{max u (t + 1)} q
  exact restriction_pushforward_square ι a q (𝟙 O) φ he

private instance integralEvaluation_additive (W : Scheme.{t}) (n : ℕ) :
    (integralEvaluation l E W n).Additive := by
  constructor
  intro M N f g
  ext U x
  rfl

private instance (priority := 10000) baseSheafify (W : Scheme.{t}) :
    HasSheafify (Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbSheafify.{t, u} W

private instance (priority := 10000) baseLocallyBijective (W : Scheme.{t}) :
    (Scheme.ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbLocallyBijective.{t, u} W

private instance sequenceSheafify (W : Scheme.{t}) :
    HasSheafify (coefficientSequenceTopology (Scheme.ProEt.topology W))
      AddCommGrpCat.{max u (t + 1)} := hasSheafifyEssentiallySmallSite _ _

private instance sequenceLocallyBijective (W : Scheme.{t}) :
    (coefficientSequenceTopology (Scheme.ProEt.topology W)).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

private theorem constantEvaluation_kinjective (W : Scheme.{t}) (n : ℕ)
    (T : CochainComplex (SheafOfModules.{max u (t + 1)}
      (sequenceIntegralRing l E W)) ℤ) [T.IsKInjective] :
    CochainComplex.IsKInjective
      (((integralEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj T) := by
  exact constantEvaluation_kinjective_generic (Scheme.ProEt.topology W)
    (integralRing l E W) n T

attribute [local irreducible] integralEvaluationSquare integralConstantQuotientOfUniverses
  Functor.mapHomologicalComplexCompIso

private theorem evaluation_resolution_sections (W : Scheme.{t}) (n : ℕ)
    (J : CochainComplex (coefficientSequenceModules l E W) ℤ) [J.IsKInjective]
    (I : CochainComplex (normalizedDVRModules l E W n) ℤ) [I.IsKInjective]
    (r : ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
    [QuasiIso r] (U : W.ProEt) :
    QuasiIso (((SheafOfModules.toSheaf.{max u (t + 1)} (integralCoefficientSheaf l E W n) ⋙
      sheafToPresheaf (Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)} ⋙
        (evaluation _ _).obj (op U)).mapHomologicalComplex (.up ℤ)).map r) := by
  let S := sequenceIntegralRestriction l E W
  let V := integralEvaluation l E W n
  let R := SheafOfModules.restrictScalars.{max u (t + 1)}
    (integralConstantQuotientOfUniverses l E W n)
  let F := SheafOfModules.toSheaf.{max u (t + 1)} (integralRing l E W) ⋙
    sheafToPresheaf (Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)} ⋙
      (evaluation _ _).obj (op U)
  let Tseq := coefficientSequenceTopology (Scheme.ProEt.topology W)
  let Oc := integralCommRing l E W
  let Oseq := NativeConstantModel.sequenceCommRing (Scheme.ProEt.topology W) Oc
  have : IsGrothendieckAbelian.{max u (t + 1)}
      (SheafOfModules.{max u (t + 1)} (sequenceIntegralRing l E W)) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u}
      Tseq Oseq).1
  have : Abelian.HasKInjectiveResolutions
      (SheafOfModules.{max u (t + 1)} (sequenceIntegralRing l E W)) := inferInstance
  have hv := sequenceEvaluation_exact.{u, t + 1, t} (Scheme.ProEt.topology W) n
    (R := sequenceIntegralRing l E W) (𝟙 (integralRing l E W))
  have : PreservesFiniteLimits V := hv.1
  have : PreservesFiniteColimits V := hv.2
  have : V.PreservesHomology := inferInstance
  obtain ⟨T, hT, s, _, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
    ((S.mapHomologicalComplex (.up ℤ)).obj J)
  have := hT
  have := hq
  have ht := constantEvaluation_kinjective l E W n T
  let Tn : CochainComplex (SheafOfModules.{max u (t + 1)} (integralRing l E W)) ℤ :=
    (V.mapHomologicalComplex (.up ℤ)).obj T
  have : CochainComplex.IsKInjective Tn := ht
  let c := Functor.mapHomologicalComplexCompIso
    (F := S) (G := V) (integralEvaluationSquare l E W n) (.up ℤ)
  let s' : (R.mapHomologicalComplex (.up ℤ)).obj
      (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj J) ⟶ Tn :=
    c.inv.app J ≫ (V.mapHomologicalComplex (.up ℤ)).map s
  have : QuasiIso s' := by dsimp only [s']; infer_instance
  have hs : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map
      ((V.mapHomologicalComplex (.up ℤ)).map s)) := by
    exact SheafOfModules.coefficientRestrictionSectionsEvaluation_quasiIso.{t + 1, t, u}
      (sequenceIntegralRing l E W)
      ((sheafCompose Tseq (forget₂ CommRingCat.{max u (t + 1)}
        RingCat.{max u (t + 1)})).obj (coefficientSequenceCommRingSheaf l E W))
      (fun V x y ↦ @mul_comm (Oseq.obj.obj V) inferInstance x y)
      (fun V x y ↦ @mul_comm ((coefficientSequenceCommRingSheaf l E W).obj.obj V)
        inferInstance x y) (sequenceIntegralMap l E W) J T s (n, U)
  have hs' : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map s') := by
    dsimp only [s']
    rw [Functor.map_comp]
    infer_instance
  exact scalar_comparison_sections (Scheme.ProEt.topology W)
    (integralRing l E W) (integralCoefficientSheaf l E W n)
    (fun V x y ↦ @mul_comm (Oc.obj.obj V) inferInstance x y)
    (fun V x y ↦ @mul_comm ((integralCoefficientCommRingSheaf l E W n).obj.obj V)
      inferInstance x y) (integralConstantQuotientOfUniverses l E W n) r Tn s' U hs'

attribute [local irreducible] Scheme.coefficientProEtaleDirectRingMap

/-- Evaluation of a K-injective system is acyclic for finite geometric direct image.

Source: Zheng, Construction 4.1 and Lemma 4.10, derived direct-image evaluation;
Stacks, Tags 0D6E, 03DI, 03DJ and 070M.
Restrict the system scalars to the constant integral coefficient ring and resolve
there by a K-injective constant-coefficient system T. The scalar-restriction
section theorem makes this resolution sectionwise a quasi-isomorphism. Constant
systems are diagrams of modules over one ring sheaf, whose evaluations preserve
K-injectives: their left adjoints are exact coproduct functors. Thus T_n is
K-injective. For a K-injective resolution r of J_n, exact scalar restriction
preserves its quasi-isomorphism. The K-injective comparison principle factors
the evaluated resolution through the restricted target of r up to homotopy.
The comparison is a quasi-isomorphism between a restricted K-injective and a
K-injective, so the same scalar-restriction section theorem applies. Homotopy
invariance and two-out-of-three show that r is sectionwise a quasi-isomorphism.
Geometric direct image evaluates these same maps on base-changed site objects,
so it sends r to a quasi-isomorphism. Naturality of the derived unit, and its
invertibility on the K-injective target of r, now give the desired isomorphism.
This applies to all n, including zero, zero complexes, and empty schemes.
(blueprint: lem-trf-compact-support-evaluation-direct-image-acyclic).
-/
theorem compactSupportEvaluationDirectImage_acyclic
    {Z Y : Scheme.{t}} (p : Z ⟶ Y) (n : ℕ)
    [(compactSupportLevelDirectImage l E p n).Additive]
    [Abelian.HasKInjectiveResolutions (normalizedDVRModules l E Z n)]
    (J : CochainComplex (coefficientSequenceModules l E Z) ℤ) [J.IsKInjective] :
    IsIso ((compactSupportLevelDirectImage l E p n).rightDerivedFunctorUnitQ
      (((coefficientSequenceEvaluation l E Z n).mapHomologicalComplex (.up ℤ)).obj J)) := by
  classical
  let M := ((coefficientSequenceEvaluation l E Z n).mapHomologicalComplex (.up ℤ)).obj J
  obtain ⟨I, hI, r, _, hr⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective M
  have := hI
  have := hr
  have hpush : QuasiIso
      (((compactSupportLevelDirectImage l E p n).mapHomologicalComplex (.up ℤ)).map r) := by
    dsimp only [compactSupportLevelDirectImage, Scheme.coefficientProEtaleModuleDirectImage]
    apply pushforward_quasiIso_of_sections.{t + 1, t, u}
      (Scheme.proEtaleBaseChange p) _ r
    intro U
    exact evaluation_resolution_sections l E Z n J I r U
  exact derivedUnit_of_resolution (compactSupportLevelDirectImage l E p n) r

end WeilConjectures

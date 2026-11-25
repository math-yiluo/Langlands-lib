/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.PurStrictScalar.ConstantScalarTowerMates
public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
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
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import all WeilConjectures.CategoryTheory.ExactDerivedSquare.DerivedExactSquareCoherence
import WeilConjectures.SmoothPurity.Supporting.NativeConstantRestrictionAcyclicity
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import WeilConjectures.SmoothPurity.PurStrictScalar.NativeConstantSectionRestriction
import WeilConjectures.SmoothPurity.PurStrictScalar.NativeSequenceRestrictionProperties
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarAdjunctions
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows

/-! # The native compact-support tower with discrete constant coefficients

Source: Stacks 03DA, 0D6E, 0E8I and 0940.
(blueprint: def-pur-native-constant-support-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective
  WeilConjectures.SemilinearSections.moduleAbelian WeilConjectures.SemilinearSections.hasDerived
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
  WeilConjectures.PurStrictScalar.unitCompatible
  WeilConjectures.PurStrictScalar.derivedUnit
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

private theorem derivedUnit_eq_unitQ
    {A B : Type (v + 1)} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions A]
    (H : A ⥤ B) [H.Additive] (K : CochainComplex A ℤ) :
    derivedUnit H K = H.rightDerivedFunctorUnitQ K := by
  unfold derivedUnit Functor.rightDerivedFunctorUnitQ
  rfl

private theorem derivedUnit_isIso_of_resolution
    {C D : Type (v + 1)} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    [Abelian.HasKInjectiveResolutions C]
    (G : C ⥤ D) [G.Additive] (K : CochainComplex C ℤ)
    (h : ∀ (T : CochainComplex C ℤ) [T.IsKInjective] (j : K ⟶ T) [QuasiIso j],
      QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j)) :
    IsIso (G.rightDerivedFunctorUnitQ K) := by
  obtain ⟨T, _, j, _, _⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
  have := h T j
  have : IsIso (G.rightDerivedFunctorUnitQ T) := by
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance
  have hn := G.rightDerivedFunctorUnitQ_naturality j
  have : IsIso (G.rightDerivedFunctorUnitQ K ≫
      G.rightDerivedFunctor.map (DerivedCategory.Q.map j)) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right (G.rightDerivedFunctorUnitQ K)
    (G.rightDerivedFunctor.map (DerivedCategory.Q.map j))

private theorem unitCompatible_of_acyclic
    {A B C D : Type (v + 1)}
    [Category.{v} A] [Category.{v} B] [Category.{v} C] [Category.{v} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
    (H : A ⥤ B) (G : C ⥤ D) (V : A ⥤ C) (W : B ⥤ D)
    [H.Additive] [G.Additive] [V.Additive] [W.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (α : H ⋙ W ≅ V ⋙ G)
    (hacyc : ∀ (I : CochainComplex A ℤ) [I.IsKInjective]
      (T : CochainComplex C ℤ) [T.IsKInjective]
      (j : (V.mapHomologicalComplex (.up ℤ)).obj I ⟶ T) [QuasiIso j],
      QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j)) :
    ∃! d : H.rightDerivedFunctor ⋙ W.mapDerivedCategory ≅
        V.mapDerivedCategory ⋙ G.rightDerivedFunctor,
      unitCompatible H G V W α d := by
  obtain ⟨d, hd⟩ := CategoryTheory.ExactDerivedSquare.square_exists H G V W α (by
    intro I hI
    have := hI
    exact derivedUnit_isIso_of_resolution G ((V.mapHomologicalComplex (.up ℤ)).obj I)
      (fun T _ j _ ↦ hacyc I T j))
  refine ⟨d, ?_, ?_⟩
  · simpa only [unitCompatible, derivedUnit, Functor.rightDerivedFunctorUnitQ,
      NatIso.mapHomologicalComplex] using hd
  · intro d' hd'
    apply CategoryTheory.ExactDerivedSquare.square_unique H G V W α d' d ?_ hd
    simpa only [unitCompatible, derivedUnit, Functor.rightDerivedFunctorUnitQ,
      NatIso.mapHomologicalComplex] using hd'

private theorem derivedComposite_existsUnique
    {A B C : Type (v + 1)}
    [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} C]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (U : A ⥤ B) (H : B ⥤ C) [U.Additive] [H.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (hcompute : ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      IsIso (H.rightDerivedFunctorUnitQ ((U.mapHomologicalComplex (.up ℤ)).obj I))) :
    ∃! d : (U ⋙ H).rightDerivedFunctor ≅ U.mapDerivedCategory ⋙ H.rightDerivedFunctor,
      ∀ K : CochainComplex A ℤ,
        derivedUnit (U ⋙ H) K ≫ d.hom.app (DerivedCategory.Q.obj K) =
          derivedUnit H ((U.mapHomologicalComplex (.up ℤ)).obj K) ≫
            H.rightDerivedFunctor.map (U.mapDerivedCategoryFactors.inv.app K) := by
  let F := U ⋙ H
  let c := Functor.rightDerivedPullback U (𝟙 F)
  have hc : IsIso c := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
    have hi : IsIso (c.app (DerivedCategory.Q.obj I)) := by
      have h := Functor.rightDerivedFunctorUnitQ_rightDerivedPullback_app' U (𝟙 F) I
      have : IsIso (F.rightDerivedFunctorUnitQ I) := by
        rw [Functor.rightDerivedFunctorUnitQ_eq]
        infer_instance
      have := hcompute I
      have : IsIso (F.rightDerivedFunctorUnitQ I ≫ c.app (DerivedCategory.Q.obj I)) := by
        dsimp only [c]
        rw [h]
        simp only [NatTrans.mapHomologicalComplex_id, NatTrans.id_app]
        have hq := DerivedCategory.Q.map_id ((F.mapHomologicalComplex (.up ℤ)).obj I)
        rw [hq, Category.id_comp]
        convert (inferInstance : IsIso
          (H.rightDerivedFunctorUnitQ ((U.mapHomologicalComplex (.up ℤ)).obj I) ≫
            H.rightDerivedFunctor.map (U.mapDerivedCategoryFactors.inv.app I))) using 0
      exact IsIso.of_isIso_comp_left (F.rightDerivedFunctorUnitQ I)
        (c.app (DerivedCategory.Q.obj I))
    have hn := c.naturality e.hom
    have : IsIso (c.app M ≫ (U.mapDerivedCategory ⋙ H.rightDerivedFunctor).map e.hom) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right (c.app M)
      ((U.mapDerivedCategory ⋙ H.rightDerivedFunctor).map e.hom)
  have hnorm : ∀ K : CochainComplex A ℤ,
      derivedUnit F K ≫ (asIso c).hom.app (DerivedCategory.Q.obj K) =
        derivedUnit H ((U.mapHomologicalComplex (.up ℤ)).obj K) ≫
          H.rightDerivedFunctor.map (U.mapDerivedCategoryFactors.inv.app K) := by
    intro K
    have h := Functor.rightDerivedFunctorUnitQ_rightDerivedPullback_app' U (𝟙 F) K
    simp only [NatTrans.mapHomologicalComplex_id, NatTrans.id_app] at h
    have hq := DerivedCategory.Q.map_id ((F.mapHomologicalComplex (.up ℤ)).obj K)
    rw [hq, Category.id_comp] at h
    simp only [derivedUnit_eq_unitQ, c, F, asIso_hom]
    convert h using 0
  refine ⟨asIso c, hnorm, ?_⟩
  intro d hd
  apply Iso.ext
  apply F.rightDerivedFunctor_hom_ext
  intro K
  simpa only [derivedUnit_eq_unitQ, F] using (hd K).trans (hnorm K).symm

private theorem scalarRestrictionTower_exact
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    {A B : Sheaf J RingCat.{v}} (α : A ⟶ B) :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (SheafOfModules.restrictScalars.{v} α)) ∧
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (SheafOfModules.restrictScalars.{v} α)) := by
  let U := SheafOfModules.restrictScalars.{v} α
  have : PreservesFiniteLimits (U ⋙ SheafOfModules.toSheaf A) :=
    SheafOfModules.instPreservesFiniteLimitsSheafAddCommGrpCatToSheaf B
  have : PreservesFiniteColimits (U ⋙ SheafOfModules.toSheaf A) :=
    SheafOfModules.preservesFiniteColimits_toSheaf B
  have : PreservesFiniteLimits U :=
    preservesFiniteLimits_of_reflects_of_preserves U (SheafOfModules.toSheaf A)
  have : PreservesFiniteColimits U :=
    preservesFiniteColimits_of_reflects_of_preserves U (SheafOfModules.toSheaf A)
  constructor
  · constructor
    intro K _ _
    change PreservesLimitsOfShape K ((Functor.whiskeringRight ℕᵒᵖ _ _).obj U)
    infer_instance
  · constructor
    intro K _ _
    change PreservesColimitsOfShape K ((Functor.whiskeringRight ℕᵒᵖ _ _).obj U)
    infer_instance

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Restriction from the completed coefficient sheaf to its actual constant scalars.
Source: Stacks 03DA, 099M (blueprint: def-pur-native-constant-support-model). -/
abbrev constantRestriction (W : Scheme.{u}) :=
  SheafOfModules.restrictScalars.{u + 1} (integralConstantToCompletionOfUniverses l E W)

/-- The same exact restriction on whole strict towers.
Source: Stacks 0940 (blueprint: def-pur-native-constant-support-model). -/
abbrev towerConstantRestriction (W : Scheme.{u}) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (constantRestriction l E W)

/-- Restriction remains exact on the diagram category.
Source: Stacks 03DA, 0940 (blueprint: def-pur-native-constant-support-model).
Proof: restriction leaves underlying abelian sheaves unchanged and is exact.
Limits and colimits of strict towers are computed pointwise. -/
theorem towerConstantRestriction_exact (W : Scheme.{u}) :
    PreservesFiniteLimits (towerConstantRestriction l E W) ∧
      PreservesFiniteColimits (towerConstantRestriction l E W) := by
  exact scalarRestrictionTower_exact (ProEt.topology W)
    (integralConstantToCompletionOfUniverses l E W)

/-- Restriction of the native varying-ring system to discrete integral towers.
Source: Stacks 0940 (blueprint: def-pur-native-constant-support-model). -/
def systemRestriction (W : Scheme.{u}) :
    ProEtale.VaryingRing.Modules (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) W ⥤
        Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W :=
  coefficientSequenceRestriction.{u, u} l E W ⋙ towerConstantRestriction l E W

/-- Exactness of restriction of the native quotient diagram.
Source: Stacks 03DA, 0940 (blueprint: def-pur-native-constant-support-model).
Proof: both restrictions are exact and their composite is exact. -/
theorem systemRestriction_exact (W : Scheme.{u}) :
    (systemRestriction l E W).Additive ∧
      PreservesFiniteLimits (systemRestriction l E W) ∧
        PreservesFiniteColimits (systemRestriction l E W) := by
  have := (coefficientSequenceRestriction_exact.{u, u} l E W).1
  have := (coefficientSequenceRestriction_exact.{u, u} l E W).2.1
  have := (coefficientSequenceRestriction_exact.{u, u} l E W).2.2
  have := (towerConstantRestriction_exact l E W).1
  have := (towerConstantRestriction_exact l E W).2
  have : (towerConstantRestriction l E W).Additive := inferInstance
  dsimp only [systemRestriction]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Exact limits for the native restriction. Source: Stacks 03DA
(blueprint: def-pur-native-constant-support-model). -/
instance systemRestriction_limits (W : Scheme.{u}) :
    PreservesFiniteLimits (systemRestriction l E W) := (systemRestriction_exact l E W).2.1

/-- Exact colimits for the native restriction. Source: Stacks 03DA
(blueprint: def-pur-native-constant-support-model). -/
instance systemRestriction_colimits (W : Scheme.{u}) :
    PreservesFiniteColimits (systemRestriction l E W) := (systemRestriction_exact l E W).2.2

/-- Additivity is inherited from the two coefficient restrictions.
Source: Stacks 03DA (blueprint: def-pur-native-constant-support-model). -/
instance systemRestriction_additive (W : Scheme.{u}) :
    (systemRestriction l E W).Additive :=
  (systemRestriction_exact l E W).1

/-- Its exact localization, with the standard derived categories at both ends.
Source: Stacks 0940 (blueprint: def-pur-native-constant-support-model). -/
def systemU (W : Scheme.{u}) :
    ProEtale.VaryingRing.Derived (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) W ⥤
      Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W :=
  haveI := (systemRestriction_exact l E W).2.1
  haveI := (systemRestriction_exact l E W).2.2
  (systemRestriction l E W).mapDerivedCategory

private theorem constantProjection (W : Scheme.{u}) (n : ℕ) :
    integralConstantToCompletionOfUniverses l E W ≫
      (sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (completedIntegralCommRingProjectionUnrestricted l E W n) =
      integralConstantQuotientOfUniverses l E W n := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply RingCat.hom_ext
  apply RingHom.ext
  intro x
  exact congrArg (fun q ↦ (q.hom.app U).hom x)
    (limit.lift_π (integralConstantConeOfUniverses l E W) (op n))

private def constantLevelMap (W : Scheme.{u}) (n : ℕ) :=
  integralConstantQuotientOfUniverses l E W n ≫
    eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm

private theorem restrict_restrict_pushforward_obj
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K]
    {A B T : Sheaf J RingCat.{v}} {R : Sheaf K RingCat.{v}}
    (α : A ⟶ B) (β : B ⟶ T)
    (γ : T ⟶ (F.sheafPushforwardContinuous RingCat.{v} J K).obj R)
    (N : SheafOfModules.{v} R) :
    (SheafOfModules.restrictScalars α).obj
        ((SheafOfModules.restrictScalars β).obj ((SheafOfModules.pushforward γ).obj N)) =
      (SheafOfModules.pushforward ((α ≫ β) ≫ γ)).obj N := by
  rfl

private theorem restrictionLevel_eq (W : Scheme.{u})
    (N : coefficientSequenceModules.{u, u} l E W) (n : ℕ) :
    ((systemRestriction l E W).obj N).obj (op n) =
      (SheafOfModules.pushforward (F := Prod.sectR n W.ProEt)
        (constantLevelMap l E W n)).obj N := by
  have h := congrArg (constantRestriction l E W).obj
    ((coefficientSequenceRestriction_exists l E W).exists.choose_spec.1 N n)
  refine h.trans ?_
  exact (restrict_restrict_pushforward_obj
    (integralConstantToCompletionOfUniverses l E W)
    ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedIntegralCommRingProjectionUnrestricted l E W n))
    (eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm) N).trans
    (congrArg (fun q ↦ (SheafOfModules.pushforward (F := Prod.sectR n W.ProEt)
      (q ≫ eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm)).obj N)
      (constantProjection l E W n))

private theorem section_ext {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{v}}
    {M N : SheafOfModules.{v} R} (f g : M ⟶ N)
    (h : ∀ U x, f.val.app U x = g.val.app U x) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  exact LinearMap.ext (h U)

private abbrev sectionTowerFunctor := @nativeSectionTowerFunctor

private abbrev constantTowerFunctor (W : Scheme.{u}) := nativeConstantSectionTower l E W

private theorem systemRestriction_eq (W : Scheme.{u}) :
    systemRestriction l E W = constantTowerFunctor l E W := by
  have hU := (coefficientSequenceRestriction_exists l E W).exists.choose_spec
  have hobj := restrictionLevel_eq l E W
  have hN (N : coefficientSequenceModules.{u, u} l E W) :
      (systemRestriction l E W).obj N = (constantTowerFunctor l E W).obj N := by
    refine CategoryTheory.Functor.ext (fun ⟨n⟩ ↦ hobj N n) ?_
    rintro ⟨m⟩ ⟨n⟩ f
    apply moduleSheaf_hom_eq_of_heq (hobj N m) (hobj N n)
    intro V
    exact hU.2.1 N m n (leOfHom f.unop) V
  refine CategoryTheory.Functor.ext hN ?_
  intro M N f
  apply NatTrans.ext
  funext n
  rcases n with ⟨n⟩
  simp only [NatTrans.comp_app, eqToHom_app]
  apply moduleSheaf_hom_eq_of_heq (hobj M n) (hobj N n)
  intro V
  exact hU.2.2 f n V

private theorem constantLevelMap_app (W : Scheme.{u}) (n : ℕ) (U : W.ProEtᵒᵖ) :
    (constantLevelMap l E W n).hom.app U =
      (integralConstantQuotientOfUniverses l E W n).hom.app U := by
  rcases U with ⟨U⟩
  dsimp only [constantLevelMap, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

private def sectionPushSquare
    {C D : Type*} [Category C] [Category D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (J' : GrothendieckTopology (ℕ × C)) (K' : GrothendieckTopology (ℕ × D))
    (F : C ⥤ D) (n : ℕ) [F.IsContinuous J K]
    [((𝟭 ℕ).prod F).IsContinuous J' K']
    [(Prod.sectR n C).IsContinuous J J'] [(Prod.sectR n D).IsContinuous K K']
    {R : Sheaf K' RingCat.{v}} {S : Sheaf J' RingCat.{v}}
    {A : Sheaf J RingCat.{v}} {B : Sheaf K RingCat.{v}}
    (φ : S ⟶ (((𝟭 ℕ).prod F).sheafPushforwardContinuous RingCat.{v} J' K').obj R)
    (ρ : A ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{v} J J').obj S)
    (σ : B ⟶ ((Prod.sectR n D).sheafPushforwardContinuous RingCat.{v} K K').obj R)
    (η : A ⟶ (F.sheafPushforwardContinuous RingCat.{v} J K).obj B)
    (h : ρ ≫ ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{v} J J').map φ =
      η ≫ (F.sheafPushforwardContinuous RingCat.{v} J K).map σ) :
    SheafOfModules.pushforward.{v} φ ⋙ SheafOfModules.pushforward.{v} ρ ≅
      SheafOfModules.pushforward.{v} σ ⋙ SheafOfModules.pushforward.{v} η := by
  letI : (Prod.sectR n C ⋙ (𝟭 ℕ).prod F).IsContinuous J K' :=
    Functor.isContinuous_comp _ _ _ J' _
  letI : (F ⋙ Prod.sectR n D).IsContinuous J K' :=
    Functor.isContinuous_comp _ _ _ K _
  exact SheafOfModules.pushforwardComp.{v} ρ φ ≪≫
    SheafOfModules.pushforwardCongr.{v} h ≪≫
      (SheafOfModules.pushforwardComp.{v} η σ).symm

private def sectionPushTowerSquare
    {C D : Type*} [Category C] [Category D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    [((𝟭 ℕ).prod F).IsContinuous (coefficientSequenceTopology J)
      (coefficientSequenceTopology K)]
    [∀ n : ℕ, (Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J)]
    [∀ n : ℕ, (Prod.sectR n D).IsContinuous K (coefficientSequenceTopology K)]
    (R : Sheaf (coefficientSequenceTopology K) RingCat.{v})
    (S : Sheaf (coefficientSequenceTopology J) RingCat.{v})
    (A : Sheaf J RingCat.{v}) (B : Sheaf K RingCat.{v})
    (φ : S ⟶ (((𝟭 ℕ).prod F).sheafPushforwardContinuous RingCat.{v}
      (coefficientSequenceTopology J) (coefficientSequenceTopology K)).obj R)
    (ρ : ∀ n : ℕ, A ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{v}
      J (coefficientSequenceTopology J)).obj S)
    (σ : ∀ n : ℕ, B ⟶ ((Prod.sectR n D).sheafPushforwardContinuous RingCat.{v}
      K (coefficientSequenceTopology K)).obj R)
    (hρ : ∀ {m n : ℕ} (h : n ≤ m), ρ m ≫
      (Functor.sheafPushforwardContinuousNatTrans (verticalNat h) RingCat.{v}
        J (coefficientSequenceTopology J)).app S = ρ n)
    (hσ : ∀ {m n : ℕ} (h : n ≤ m), σ m ≫
      (Functor.sheafPushforwardContinuousNatTrans (verticalNat h) RingCat.{v}
        K (coefficientSequenceTopology K)).app R = σ n)
    (η : A ⟶ (F.sheafPushforwardContinuous RingCat.{v} J K).obj B)
    (h : ∀ n : ℕ, ρ n ≫ ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{v}
      J (coefficientSequenceTopology J)).map φ =
        η ≫ (F.sheafPushforwardContinuous RingCat.{v} J K).map (σ n)) :
    { d : SheafOfModules.pushforward.{v} φ ⋙ sectionTowerFunctor J S A ρ hρ ≅
        sectionTowerFunctor K R B σ hσ ⋙
          (Functor.whiskeringRight ℕᵒᵖ _ _).obj (SheafOfModules.pushforward.{v} η) //
      ∀ (N : SheafOfModules.{v} R) (n : ℕ) (V : Cᵒᵖ),
        HEq (fun x ↦ (((d.hom.app N).app (op n)).val.app V) x)
          (id : N.val.obj (op (n, F.obj V.unop)) → N.val.obj (op (n, F.obj V.unop))) } := by
  let e (n : ℕ) := sectionPushSquare J K (coefficientSequenceTopology J)
    (coefficientSequenceTopology K) F n φ (ρ n) (σ n) η (h n)
  let d : SheafOfModules.pushforward.{v} φ ⋙ sectionTowerFunctor J S A ρ hρ ≅
      sectionTowerFunctor K R B σ hσ ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj (SheafOfModules.pushforward.{v} η) :=
    NatIso.ofComponents (fun N ↦ NatIso.ofComponents (fun n ↦ (e n.unop).app N) (by
      intro m n f
      apply section_ext
      intro V x
      change N.val.presheaf.map
        (((𝟭 ℕ).prod F).map ((verticalNat (leOfHom f.unop)).app V.unop)).op x =
          N.val.presheaf.map ((verticalNat (leOfHom f.unop)).app (F.obj V.unop)).op x
      have he : ((𝟭 ℕ).prod F).map ((verticalNat (leOfHom f.unop)).app V.unop) =
          (verticalNat (leOfHom f.unop)).app (F.obj V.unop) := by
        apply Prod.hom_ext
        · rfl
        · exact F.map_id V.unop
      exact congrArg (fun a ↦ N.val.presheaf.map a.op x) he)) (by
        intro M N f
        apply NatTrans.ext
        funext n
        exact (e n.unop).hom.naturality f)
  exact ⟨d, fun _ _ _ ↦ HEq.rfl⟩

private abbrev constantBaseRingMap {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (proEtaleRingDirectImageMap g
      (coefficients (CommRingCat.of (ULift.{u + 1}
        (Padic.coefficientExtensionIntegers l E))) Y)
      (coefficients (CommRingCat.of (ULift.{u + 1}
        (Padic.coefficientExtensionIntegers l E))) X)
      (constantRingIso (CommRingCat.of (ULift.{u + 1}
        (Padic.coefficientExtensionIntegers l E))) g))

private theorem constantLevelRingSquare {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ) :
    constantLevelMap l E Y n ≫
      ((Prod.sectR n Y.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (coefficientSequenceTopology (ProEt.topology Y))).map
          (ProEtale.VaryingRing.ringMap (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) g) =
      constantBaseRingMap l E g ≫
        ((proEtaleBaseChange g).sheafPushforwardContinuous RingCat.{u + 1}
          (ProEt.topology Y) (ProEt.topology X)).map (constantLevelMap l E X n) := by
  let A := CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
  let a : A ⟶ compactSupportSystemLevel l E n := CommRingCat.ofHom
    ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
      ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
        (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom))
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  have h := ProEtale.VaryingRing.constantMap_naturality g a
  have hc : proEtaleRingDirectImageMap g (coefficients A Y) (coefficients A X)
      (constantRingIso A g) = proEtaleConstantDirectImageMap g CommRingCat.{u + 1} A :=
    ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  have hU := congrArg (fun t ↦
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map (t.hom.app U)) h
  change (constantLevelMap l E Y n).hom.app U ≫ _ =
    (constantBaseRingMap l E g).hom.app U ≫ (constantLevelMap l E X n).hom.app
      ((proEtaleBaseChange g).op.obj U)
  rw [constantLevelMap_app, constantLevelMap_app]
  dsimp only [constantBaseRingMap]
  rw [hc]
  exact hU

private theorem towerIso_ext
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {A : Sheaf J RingCat.{v}}
    {F G : D ⥤ (ℕᵒᵖ ⥤ SheafOfModules.{v} A)} (a b : F ≅ G)
    (h : ∀ (N : D) (n : ℕᵒᵖ) (V : Cᵒᵖ),
      HEq (fun x ↦ (((a.hom.app N).app n).val.app V) x)
        (fun x ↦ (((b.hom.app N).app n).val.app V) x)) : a = b := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply NatTrans.ext
  funext n
  apply section_ext
  intro V x
  exact congrFun (eq_of_heq (h N n V)) x

/-- The section-normalized ordinary diagram direct-image comparison is unique.
Source: Stacks 03DA, 0D6E (blueprint: def-pur-native-constant-support-model).
Proof: after restriction, both objects have the sections of N at the same
base-change object (n,V). The coefficient square identifies their scalar actions.
Identity on these sections is a module map, is natural in V,n,N, and is invertible.
Sectionwise extensionality gives uniqueness. This includes empty objects. -/
theorem systemProperOrdinary_existsUnique {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ∃! d : ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) g ⋙ systemRestriction l E Y ≅
      systemRestriction l E X ⋙
        towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g,
      ∀ (N : coefficientSequenceModules.{u, u} l E X) (n : ℕ) (V : Y.ProEtᵒᵖ),
        HEq (fun x ↦
            (((d.hom.app N).app (op n)).val.app V) x)
          (id : N.val.obj (op (n, (proEtaleBaseChange g).obj V.unop)) →
            N.val.obj (op (n, (proEtaleBaseChange g).obj V.unop))) := by
  apply existsUnique_of_exists_of_unique
  · rw [systemRestriction_eq l E X, systemRestriction_eq l E Y]
    have : ((𝟭 ℕ).prod (proEtaleBaseChange g)).IsContinuous
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X)) :=
      ProEtale.VaryingRing.baseChange_continuous g
    let d := sectionPushTowerSquare (ProEt.topology Y) (ProEt.topology X)
      (proEtaleBaseChange g)
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf l E X))
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf l E Y))
      (integralConstantRingOfUniverses l E Y) (integralConstantRingOfUniverses l E X)
      (ProEtale.VaryingRing.ringMap (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) g)
      (constantLevelMap l E Y) (constantLevelMap l E X)
      (fun h ↦ nativeConstantLevelMap_horizontal l E Y h)
      (fun h ↦ nativeConstantLevelMap_horizontal l E X h)
      (constantBaseRingMap l E g) (constantLevelRingSquare l E g)
    exact ⟨d.val, d.property⟩
  · intro a b ha hb
    refine towerIso_ext (C := Y.ProEt) (D := coefficientSequenceModules.{u, u} l E X)
      (J := ProEt.topology Y) (A := integralConstantRingOfUniverses l E Y)
      (F := ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) g ⋙ systemRestriction l E Y)
      (G := systemRestriction l E X ⋙
        towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
      a b ?_
    intro N n V
    rcases n with ⟨n⟩
    exact (ha N n V).trans (hb N n V).symm

/-- The ordinary comparison is selected by identity on sections, not by existence
of an unspecified isomorphism.
Source: Stacks 0D6E (blueprint: def-pur-native-constant-support-model). -/
def systemProperOrdinary {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) g ⋙ systemRestriction l E Y ≅
      systemRestriction l E X ⋙
        towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g :=
  (systemProperOrdinary_existsUnique l E g).choose

/-- The recorded additive native pushforward at the fixed coefficient universes.
Source: Stacks 03DA (blueprint: def-pur-native-constant-support-model). -/
instance nativePush_additive {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) g).Additive :=
  ProEtale.VaryingRing.push_additive _ _ g

/-- K-injective resolutions from the recorded native ringed sequence site.
Source: Stacks 079P, 0941 (blueprint: def-pur-native-constant-support-model). -/
instance nativeSequence_kInjective (W : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (coefficientSequenceModules.{u, u} l E W) :=
  ProEtale.VaryingRing.modules_kInjective (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) W

/-- The whole-system derived direct-image comparison is characterized by the two
actual derived units, before evaluating any level.
Source: Stacks 0D6E (blueprint: def-pur-native-constant-support-model).
Proof: view restriction as the direct image of the identity ringed diagram topos.
The two composites are the same ringed-topos morphism. Derived composition gives
an isomorphism commuting with both resolution units. The universal property of
the derived composite gives uniqueness. Restriction need not preserve K-injectives. -/
theorem systemProper_existsUnique {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ∃! d : ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) g ⋙ systemU l E Y ≅
      systemU l E X ⋙ R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g,
      unitCompatible
        (hAdd := nativePush_additive l E g)
        (vAdd := systemRestriction_additive l E X)
        (wAdd := systemRestriction_additive l E Y)
        (A := ProEtale.VaryingRing.Modules (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) X)
        (B := ProEtale.VaryingRing.Modules (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) Y)
        (C := Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X)
        (D := Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Y)
        (ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) g)
        (towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
        (systemRestriction l E X) (systemRestriction l E Y)
        (systemProperOrdinary l E g) d := by
  refine unitCompatible_of_acyclic
    (ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) g)
    (towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
    (systemRestriction l E X) (systemRestriction l E Y)
    (systemProperOrdinary l E g) ?_
  intro I _ T _ j _
  exact nativeConstantRestriction_push_quasiIso l E g I T j

/-- The normalized derived comparison, retaining its whole-diagram universal unit.
Source: Stacks 0D6E (blueprint: def-pur-native-constant-support-model). -/
def systemProper {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) g ⋙ systemU l E Y ≅
      systemU l E X ⋙ R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g :=
  (systemProper_existsUnique l E g).choose

/-- The inverse-image restriction square is the mate of identity on sections.
Source: Stacks 07A6 (blueprint: def-pur-native-constant-support-model). -/
def systemPullMap {X Y : Scheme.{u}} (g : X ⟶ Y) :
    systemRestriction l E Y ⋙
        towerPullback (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g ⟶
      ProEtale.VaryingRing.pull (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) g ⋙ systemRestriction l E X :=
  ((mateEquiv (ProEtale.VaryingRing.moduleAdj (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) g)
    ((proEtaleRingModuleAdjunction g ((constants l E).ring Y)
      ((constants l E).ring X) ((constants l E).pull g)).whiskerRight ℕᵒᵖ)).symm
    (TwoSquare.mk _ _ _ _ (systemProperOrdinary l E g).hom))

attribute [local irreducible] Functor.leftAdjoint
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private abbrev constantScalarMap := nativeConstantScalarMap l E

private theorem constantScalarMap_compatibility (n : ℕ) :
    constantScalarMap l E (n + 1) ≫ compactSupportSystemQuotient l E n =
      constantScalarMap l E n := nativeConstantScalarMap_compatibility l E n

private def constantScalarRestriction := nativeConstantScalarRestriction l E
  (fun W ↦ by
    change (constantTowerFunctor l E W).Additive
    rw [← systemRestriction_eq l E W]
    exact systemRestriction_additive l E W)
  (fun W ↦ by
    change PreservesFiniteLimits (constantTowerFunctor l E W)
    rw [← systemRestriction_eq l E W]
    exact systemRestriction_limits l E W)
  (fun W ↦ by
    change PreservesFiniteColimits (constantTowerFunctor l E W)
    rw [← systemRestriction_eq l E W]
    exact systemRestriction_colimits l E W)

private theorem maps_eq_of_normalized_sections {A B T : Type v}
    (hA : A = T) (hB : B = T) (f g : A → B)
    (hf : HEq f (id : T → T)) (hg : ∀ x, HEq (g x) x) : f = g := by
  subst A B
  funext x
  exact (congrFun (eq_of_heq hf) x).trans (eq_of_heq (hg x)).symm

private theorem explicitConstantPullMate_isIso {X Y : Scheme.{u}} (g : X ⟶ Y)
    (d : ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) g ⋙ constantTowerFunctor l E Y ≅
      constantTowerFunctor l E X ⋙
        towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
    (hd : ∀ (N : coefficientSequenceModules.{u, u} l E X) (n : ℕ) (V : Y.ProEtᵒᵖ),
      HEq (fun x ↦ (((d.hom.app N).app (op n)).val.app V) x)
        (id : N.val.obj (op (n, (proEtaleBaseChange g).obj V.unop)) →
          N.val.obj (op (n, (proEtaleBaseChange g).obj V.unop)))) :
    IsIso ((mateEquiv (ProEtale.VaryingRing.moduleAdj (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) g)
      ((proEtaleRingModuleAdjunction g ((constants l E).ring Y)
        ((constants l E).ring X) ((constants l E).pull g)).whiskerRight ℕᵒᵖ)).symm
      (TwoSquare.mk _ _ _ _ d.hom)) := by
  let R := compactSupportSystemLevel l E
  let φ := compactSupportSystemQuotient l E
  let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let ψ := constantScalarMap l E
  let C := constantScalarRestriction l E
  obtain ⟨G⟩ := ProEtale.VaryingRing.ordinaryScalarAdjunctions R φ B ψ
    (constantScalarMap_compatibility l E) C
  have hdG : d = G.d g := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply NatTrans.ext
    funext n
    apply section_ext
    intro U
    have he := maps_eq_of_normalized_sections
      (T := (N.val.obj (op (n.unop, (proEtaleBaseChange g).obj U.unop)) : Type (u + 1)))
      rfl rfl
      (fun x ↦ (((d.hom.app N).app n).val.app U) x)
      (fun x ↦ ((((G.d g).hom.app N).app n).val.app U) x)
      (hd N n.unop U) (G.d_sections g N n.unop U)
    exact congrFun he
  rw [hdG]
  exact ProEtale.VaryingRing.inverseMateIsoOfUnit
    (ProEtale.VaryingRing.moduleAdj R φ g) (ProEtale.VaryingRing.scalarTowerAdj B g)
    (C.rho Y) (C.rho X) (G.d g).hom (G.b g)
    (ProEtale.VaryingRing.OrdinaryScalarAdjunctions.unit R φ B ψ C G g)

/-- This coefficient inverse-image square is cartesian and its mate is invertible.
Source: Stacks 03D2, 07A6 (blueprint: def-pur-native-constant-support-model).
Proof: base change pulls back the same constant quotient ring and constant-to-completed
map. Tensor balancing identifies both module inverse images with the same sheafified
module presheaf. The mate sends 1 tensor x to the inverse-image unit, so is this iso. -/
theorem systemPullMap_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    IsIso (systemPullMap l E g) := by
  let P (V : coefficientSequenceModules.{u, u} l E X ⥤
      Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X)
      (W : coefficientSequenceModules.{u, u} l E Y ⥤
        Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Y) : Prop :=
    ∀ d : ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) g ⋙ W ≅ V ⋙
          towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g,
      (∀ (N : coefficientSequenceModules.{u, u} l E X) (n : ℕ) (U : Y.ProEtᵒᵖ),
        HEq (fun x ↦ (((d.hom.app N).app (op n)).val.app U) x)
          (id : N.val.obj (op (n, (proEtaleBaseChange g).obj U.unop)) →
            N.val.obj (op (n, (proEtaleBaseChange g).obj U.unop)))) →
      IsIso ((mateEquiv (ProEtale.VaryingRing.moduleAdj (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) g)
        ((proEtaleRingModuleAdjunction g ((constants l E).ring Y)
          ((constants l E).ring X) ((constants l E).pull g)).whiskerRight ℕᵒᵖ)).symm
        (TwoSquare.mk _ _ _ _ d.hom))
  have hP : P (constantTowerFunctor l E X) (constantTowerFunctor l E Y) :=
    explicitConstantPullMate_isIso l E g
  rw [← systemRestriction_eq l E X, ← systemRestriction_eq l E Y] at hP
  exact hP (systemProperOrdinary l E g)
    (systemProperOrdinary_existsUnique l E g).choose_spec.1

/-- The ordinary open restriction square is the geometric open-adjunction mate.
Source: Stacks 03DI, 0E8I (blueprint: def-pur-native-constant-support-model). -/
def systemOpenMap {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    systemRestriction l E X ⋙
        towerJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j ⟶
      ProEtale.VaryingRing.extension (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j ⋙ systemRestriction l E Y :=
  haveI := systemPullMap_isIso l E j
  ((mateEquiv (ProEtale.VaryingRing.moduleJAdj (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    ((moduleJAdj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j).whiskerRight ℕᵒᵖ)).symm
    (TwoSquare.mk _ _ _ _ (inv (systemPullMap l E j))))

private theorem constantOpen_counit_isIso {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : coefficientSequenceModules.{u, u} l E X) :
    IsIso (((moduleJAdj
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j).whiskerRight ℕᵒᵖ).counit.app
        ((constantTowerFunctor l E Y).obj
          ((ProEtale.VaryingRing.extension (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) j).obj M))) := by
  let R := compactSupportSystemLevel l E
  let φ := compactSupportSystemQuotient l E
  let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let ψ := constantScalarMap l E
  let C := constantScalarRestriction l E
  obtain ⟨G⟩ := ProEtale.VaryingRing.ordinaryScalarAdjunctions R φ B ψ
    (constantScalarMap_compatibility l E) C
  let b := ProEtale.VaryingRing.scalarTowerOpenAdj B j
  have := ProEtale.VaryingRing.moduleJAdj_unit_isIso R φ j
  have : IsIso (b.unit.app ((C.rho X).obj M)) := by
    rw [← G.open_unit j M]
    let eη := (@asIso _ _ _ _ (ProEtale.VaryingRing.moduleJAdj R φ j).unit
      (ProEtale.VaryingRing.moduleJAdj_unit_isIso R φ j)).app M
    exact ((C.rho X).mapIso eη ≪≫ (G.b j).app
      ((ProEtale.VaryingRing.extension R φ j).obj M) ≪≫
        (towerPullback B j).mapIso ((G.a j).app M)).isIso_hom
  have hc : IsIso (b.counit.app ((towerJ B j).obj ((C.rho X).obj M))) :=
    IsIso.of_isIso_fac_left (b.left_triangle_components ((C.rho X).obj M))
  exact (NatTrans.isIso_app_iff_of_iso b.counit ((G.a j).app M)).mpr hc

private theorem inverseOpenMate_isIso_of_support
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {R : B ⥤ A} {l : D ⥤ E} {r : E ⥤ D}
    (a : L ⊣ R) (b : l ⊣ r) (F : A ⥤ D) (G : B ⥤ E)
    (e : R ⋙ F ≅ G ⋙ r) [IsIso a.unit]
    (hc : ∀ M, IsIso (b.counit.app (G.obj (L.obj M)))) :
    IsIso ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ e.hom)) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro M
  have := hc M
  change IsIso (𝟙 _ ≫ l.map (F.map (a.unit.app M)) ≫
    𝟙 _ ≫ l.map (𝟙 _) ≫ l.map (e.hom.app (L.obj M)) ≫
    l.map (𝟙 _) ≫ 𝟙 _ ≫ b.counit.app (G.obj (L.obj M)) ≫ 𝟙 _)
  infer_instance

/-- Open restriction is invertible with ordinary tensor/unit normalization.
Source: Stacks 03DI, 0E8I (blueprint: def-pur-native-constant-support-model).
Proof: transpose using the open unit. On the open the map is identity on the
restricted module, and off the open both sides are zero. These local formulas
identify the inverse and commute with every horizontal quotient transition. -/
theorem systemOpenMap_isIso {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    IsIso (systemOpenMap l E j) := by
  have := systemPullMap_isIso l E j
  have := ProEtale.VaryingRing.moduleJAdj_unit_isIso (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j
  have hc := constantOpen_counit_isIso l E j
  rw [← systemRestriction_eq l E Y] at hc
  exact inverseOpenMate_isIso_of_support
    (ProEtale.VaryingRing.moduleJAdj (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    ((moduleJAdj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j).whiskerRight ℕᵒᵖ)
    (systemRestriction l E X) (systemRestriction l E Y) (asIso (inv (systemPullMap l E j))) hc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Exact descent of that specified ordinary open map.
Source: Stacks 0E8I (blueprint: def-pur-native-constant-support-model). -/
def systemOpen {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    systemU l E X ⋙ J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j ≅
      ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j ⋙ systemU l E Y :=
  haveI := systemOpenMap_isIso l E j
  haveI := systemRestriction_additive l E X
  haveI := systemRestriction_additive l E Y
  haveI := (systemRestriction_exact l E X).2.1
  haveI := (systemRestriction_exact l E X).2.2
  haveI := (systemRestriction_exact l E Y).2.1
  haveI := (systemRestriction_exact l E Y).2.2
  haveI := ProEtale.VaryingRing.extensionAdditive (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j
  haveI := ProEtale.VaryingRing.extensionLimits (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j
  haveI := ProEtale.VaryingRing.extensionColimits (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j
  Functor.mapDerivedCategorySquareIso (asIso (systemOpenMap l E j))

/-- The native reduction lift restricted to the discrete constant integral sheaf.
Source: Stacks 0940; recorded reduction-tower construction
(blueprint: def-pur-native-constant-support-model). -/
def reduction (W : Scheme.{u}) (S : CoefficientDerivedSystemCalculus.{u, u} l E W) :=
  S.reduction ⋙ systemU l E W

/-- The actual ordinary limit of the quotient system after completed coefficient
restriction. Source: Stacks 0940 (blueprint: def-pur-native-constant-support-model). -/
def ordinaryLimit (W : Scheme.{u}) :
    coefficientSequenceModules.{u, u} l E W ⥤ scalarReductionSource l E W :=
  coefficientSequenceRestriction.{u, u} l E W ⋙
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The ordinary quotient system is left adjoint to its ordinary inverse limit.
Source: Stacks 03EK, 0940 (blueprint: def-pur-native-constant-support-model).
Proof: module extension to the quotient sequence ring is left adjoint to restriction.
Compose this adjunction with the diagonal/limit adjunction on completed modules.
This constructs the required left adjoint and its unit on the entire diagram. -/
theorem ordinaryLimit_rightAdjoint (W : Scheme.{u}) :
    (ordinaryLimit l E W).IsRightAdjoint := by
  have := (nativeSequenceRestriction_properties l E W).1
  dsimp only [ordinaryLimit]
  infer_instance

/-- The right adjoint structure of the ordinary limit.
Source: Stacks 0940 (blueprint: def-pur-native-constant-support-model). -/
instance ordinaryLimit_isRightAdjoint (W : Scheme.{u}) :
    (ordinaryLimit l E W).IsRightAdjoint := ordinaryLimit_rightAdjoint l E W

/-- The actual ordinary quotient-system extension, specified by its universal property.
Source: Stacks 03EK, 0940 (blueprint: def-pur-native-constant-support-model). -/
def ordinaryReduction (W : Scheme.{u}) :
    scalarReductionSource l E W ⥤ coefficientSequenceModules.{u, u} l E W :=
  (ordinaryLimit l E W).leftAdjoint

/-- Its canonical adjunction. Source: Stacks 0940
(blueprint: def-pur-native-constant-support-model). -/
def ordinaryReductionAdj (W : Scheme.{u}) :
    ordinaryReduction l E W ⊣ ordinaryLimit l E W :=
  Adjunction.ofIsRightAdjoint (ordinaryLimit l E W)

/-- Additivity of the ordinary adjunction functors.
Source: Stacks 03DA, 03EK (blueprint: def-pur-native-constant-support-model).
Proof: the ordinary limit is additive since restriction and limits are additive.
Its left adjoint is additive by the additive-adjunction criterion. -/
theorem ordinaryReduction_additive_data (W : Scheme.{u}) :
    (ordinaryLimit l E W).Additive ∧ (ordinaryReduction l E W).Additive := by
  have h : (ordinaryLimit l E W).Additive := by
    dsimp only [ordinaryLimit]
    infer_instance
  exact ⟨h, (ordinaryReductionAdj l E W).left_adjoint_additive⟩

/-- Additivity of the actual ordinary limit. Source: Stacks 03DA
(blueprint: def-pur-native-constant-support-model). -/
instance ordinaryLimit_additive (W : Scheme.{u}) :
    (ordinaryLimit l E W).Additive := (ordinaryReduction_additive_data l E W).1

/-- Additivity of the actual quotient extension. Source: Stacks 03EK
(blueprint: def-pur-native-constant-support-model). -/
instance ordinaryReduction_additive (W : Scheme.{u}) :
    (ordinaryReduction l E W).Additive := (ordinaryReduction_additive_data l E W).2

/-- The two ways of deriving the actual system limit agree, with the canonical
resolution unit on every whole-system complex.
Source: Stacks 0940, 0941 (blueprint: def-pur-native-constant-support-model).
Proof: use injective resolutions in the ringed sequence site. Their restrictions
are inverse-limit acyclic by the level/coextension adjunction. The derived-composite
comparison is invertible. Its universal derived unit gives the displayed equation
and determines it uniquely; no equality is inferred from finite evaluation. -/
theorem reductionRightComparison_existsUnique (W : Scheme.{u}) :
    ∃! d : (ordinaryLimit l E W).rightDerivedFunctor ≅ coefficientSequenceLimit l E W,
      ∀ K : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ,
        derivedUnit (ordinaryLimit l E W) K ≫ d.hom.app (DerivedCategory.Q.obj K) =
          derivedUnit
              (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
              (((coefficientSequenceRestriction.{u, u} l E W).mapHomologicalComplex
                (.up ℤ)).obj K) ≫
            (coefficientConstantTowerLimit l E W).map
              ((coefficientSequenceRestriction.{u, u} l E W).mapDerivedCategoryFactors.inv.app
                K) := by
  let U := coefficientSequenceRestriction.{u, u} l E W
  let H : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W := lim
  apply derivedComposite_existsUnique U H
  intro I hI
  have := hI
  exact derivedUnit_isIso_of_resolution H ((U.mapHomologicalComplex (.up ℤ)).obj I)
    (fun T _ j _ ↦ (nativeSequenceRestriction_properties l E W).2 I T j)

/-- The unit-normalized derived-limit comparison. Source: Stacks 0941
(blueprint: def-pur-native-constant-support-model). -/
def reductionRightComparison (W : Scheme.{u}) :=
  (reductionRightComparison_existsUnique l E W).choose

/-- The whole-diagram reduction counit is the mate of the actual right-derived
unit, under the ordinary quotient/limit adjunction and the recorded reduction
adjunction. Thus it is fixed before evaluating any quotient.
Source: Stacks 06YY, 0941 (blueprint: def-pur-native-constant-support-model). -/
def systemReductionCounit (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W) :
    DerivedCategory.Qh ⋙ S.reduction ⟶
      (ordinaryReduction l E W).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  haveI : (ordinaryLimit l E W).leftAdjoint.Additive := ordinaryReduction_additive l E W
  ((mateEquiv ((ordinaryReductionAdj l E W).mapHomotopyCategory (.up ℤ))
    (S.adjunction.ofNatIsoRight (reductionRightComparison l E W).symm)).symm
      (TwoSquare.mk _ _ _ _ (ordinaryLimit l E W).rightDerivedFunctorUnit))

/-- The recorded separately derived proper/open lift, then coefficient restriction.
Source: Stacks 0940; recorded reduction-tower construction
(blueprint: def-pur-native-constant-support-model). -/
def support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X) :=
  S.reduction ⋙ ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.i ⋙
    ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g ⋙ systemU l E Y

/-- The canonical identification with proper/open operations on constant towers.
Both factors are fixed by their derived units or ordinary open-adjunction units.
Source: Stacks 0D6E, 0E8I (blueprint: def-pur-native-constant-support-model). -/
def supportModel {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X) :
    support l E c S ≅ reduction l E X S ⋙ image l E c :=
  Functor.isoWhiskerLeft S.reduction
    (Functor.isoWhiskerLeft
      (ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.i) (systemProper l E c.g)) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft S.reduction
      (systemOpen l E c.i).symm)
      (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c.g)

end WeilConjectures.PurStrictScalar

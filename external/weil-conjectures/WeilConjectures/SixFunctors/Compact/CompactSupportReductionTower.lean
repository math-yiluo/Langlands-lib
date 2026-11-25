/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.Compact.CompactSupportReductionTowerData
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Compact.CompactSupportReductionTowerFunctorSpec
import all WeilConjectures.SmoothPurity.Compact.CompactSupportNativeTowerPresentation
import WeilConjectures.SmoothPurity.Compact.CompactSupportSequenceRestrictionLinearity
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemTransition
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# Coherent compact-support reduction towers

Source: Weil blueprint, `sk-def-sf-operations`, proof of
`lem-weil-compact-support-representative-independence`, first sentence;
Stacks Project, Tags 0940, 0941 and 06YY; Bhatt--Scholze, Definition 6.7.6
(blueprint: lem-weil-compact-support-reduction-tower-functor).

The target is the derived category of strict towers of modules over the completed
coefficient sheaf. Evaluation comparisons are natural isomorphisms of functors.
Every pair of positive levels is constrained by the actual quotient map; index n
means exponent n+1. The proper image is derived separately after open extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
attribute [local irreducible] HasDerivedCategory.standard
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective
  WeilConjectures.SemilinearSections.moduleAbelian WeilConjectures.SemilinearSections.hasDerived
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private def compactSupportConstantScalarHom (W : Scheme.{u}) (U : W.ProEtᵒᵖ) :
    Padic.coefficientExtensionIntegers l E →+*
      (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U :=
  ((integralConstantToCompletion l E W).hom.app U).hom.comp
    (((forget₂ CommRingCat RingCat).map
      ((toSheafify (ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u}
            (Padic.coefficientExtensionIntegers l E))))).app U)).hom.comp
        ULift.ringEquiv.symm.toRingHom)

private theorem compactSupportConstantScalar_naturality (W : Scheme.{u})
    {U V : W.ProEtᵒᵖ} (f : U ⟶ V) (a : Padic.coefficientExtensionIntegers l E) :
    (completedIntegralCoefficientSheafUnrestricted l E W).obj.map f
      (compactSupportConstantScalar l E W U a) =
        compactSupportConstantScalar l E W V a := by
  let η := Functor.whiskerRight
    (toSheafify (ProEt.topology W)
      ((Functor.const W.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)))))
    (forget₂ CommRingCat RingCat) ≫ (integralConstantToCompletion l E W).hom
  exact (ConcreteCategory.congr_hom (η.naturality f) (ULift.up a)).symm

private def compactSupportScalarSections (W : Scheme.{u}) :
    Padic.coefficientExtensionIntegers l E →+*
      RingCat.sectionsSubring (completedIntegralCoefficientSheafUnrestricted l E W).obj :=
  (RingHom.pi (compactSupportConstantScalarHom l E W)).codRestrict _ (fun a ↦ by
    intro U V f
    exact compactSupportConstantScalar_naturality l E W f a)

@[instance_reducible]
private def compactSupportScalarLinear (W : Scheme.{u}) :
    Linear (Padic.coefficientExtensionIntegers l E) (scalarReductionSource l E W) := by
  letI : Linear
      (RingCat.sectionsSubring (completedIntegralCoefficientSheafUnrestricted l E W).obj)
      (scalarReductionSource l E W) :=
    SheafOfModules.homLinear (completedIntegralCommRingSheafUnrestricted l E W).obj
      (completedIntegralCoefficientSheafUnrestricted l E W).property
  exact
    { homModule := fun M N ↦ Module.compHom (M ⟶ N) (compactSupportScalarSections l E W)
      smul_comp := fun M N P a f g ↦
        Linear.smul_comp M N P (compactSupportScalarSections l E W a) f g
      comp_smul := fun M N P f a g ↦
        Linear.comp_smul M N P f (compactSupportScalarSections l E W a) g }

private theorem compactSupportScalarLinear_normalized (W : Scheme.{u}) :
    @IsCompactSupportScalarAction l _ E _ _ _ W (compactSupportScalarLinear l E W) := by
  intro M N f a U x
  rfl

private def compactSupportCompletionCone (W : Scheme.{u}) :
    Cone (coefficientSequenceCommRingSystem.{u, u} l E W) where
  pt := completedIntegralCommRingSheafUnrestricted l E W
  π := NatTrans.ofOpSequence (completedIntegralCommRingProjectionUnrestricted l E W)
    (fun n ↦ by
      apply (sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_injective
      simp only [Functor.map_comp, Functor.const_obj_map,
        coefficientSequenceCommRingSystem, Functor.ofOpSequence_map_homOfLE_succ]
      change limit.π (integralCoefficientSheafSystem l E W) (op n) =
        limit.π (integralCoefficientSheafSystem l E W) (op (n + 1)) ≫ _
      have hw := (limit.w (integralCoefficientSheafSystem l E W)
        (homOfLE (Nat.le_succ n)).op).symm
      simp only [integralCoefficientSheafSystem,
        Functor.ofOpSequence_map_homOfLE_succ] at hw
      convert hw using 1
      · congr 1
      · apply Sheaf.hom_ext
        apply NatTrans.ext
        funext V
        ext x
        rfl)

private def compactSupportSequenceProjection (W : Scheme.{u}) :
    (CategoryTheory.Prod.snd ℕ W.ProEt).op ⋙
        (completedIntegralCoefficientSheafUnrestricted l E W).obj ⟶
      (coefficientSequenceCommRingSheaf.{u, u} l E W).obj ⋙
        forget₂ CommRingCat RingCat := by
  let π := Functor.whiskerRight (compactSupportCompletionCone l E W).π
    (sheafToPresheaf (ProEt.topology W) CommRingCat.{u + 1})
  exact Functor.whiskerRight
    (Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := W.ProEt)).functor
      (Functor.uncurry.map π)) (forget₂ CommRingCat RingCat)

private def compactSupportSequenceScalars (W : Scheme.{u}) :
    Padic.coefficientExtensionIntegers l E →+*
      RingCat.sectionsSubring
        ((coefficientSequenceCommRingSheaf.{u, u} l E W).obj ⋙
          forget₂ CommRingCat RingCat) :=
  (RingHom.pi (fun V ↦ ((compactSupportSequenceProjection l E W).app V).hom.comp
    (compactSupportConstantScalarHom l E W (op V.unop.2)))).codRestrict _ (fun a ↦ by
      intro V V' f
      have hn := ConcreteCategory.congr_hom
        ((compactSupportSequenceProjection l E W).naturality f)
        (compactSupportConstantScalar l E W (op V.unop.2) a)
      change (compactSupportSequenceProjection l E W).app V'
          ((completedIntegralCoefficientSheafUnrestricted l E W).obj.map
            ((CategoryTheory.Prod.snd ℕ W.ProEt).op.map f)
            (compactSupportConstantScalar l E W (op V.unop.2) a)) =
        (((coefficientSequenceCommRingSheaf.{u, u} l E W).obj ⋙
          forget₂ CommRingCat RingCat).map f)
          ((compactSupportSequenceProjection l E W).app V
            (compactSupportConstantScalar l E W (op V.unop.2) a)) at hn
      change _ = _
      exact hn.symm.trans (congrArg
        (fun x ↦ (compactSupportSequenceProjection l E W).app V' x)
        (compactSupportConstantScalar_naturality l E W
          ((CategoryTheory.Prod.snd ℕ W.ProEt).op.map f) a)))

@[instance_reducible]
private def compactSupportSequenceLinear (W : Scheme.{u}) :
    Linear (Padic.coefficientExtensionIntegers l E) (coefficientSequenceModules.{u, u} l E W) := by
  letI : Linear (RingCat.sectionsSubring
      ((coefficientSequenceCommRingSheaf.{u, u} l E W).obj ⋙ forget₂ CommRingCat RingCat))
      (coefficientSequenceModules.{u, u} l E W) :=
    SheafOfModules.homLinear (coefficientSequenceCommRingSheaf.{u, u} l E W).obj
      ((sheafCompose (coefficientSequenceTopology (ProEt.topology W))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf.{u, u} l E W)).property
  exact
    { homModule := fun M N ↦ Module.compHom (M ⟶ N) (compactSupportSequenceScalars l E W)
      smul_comp := fun M N P a f g ↦
        Linear.smul_comp M N P (compactSupportSequenceScalars l E W a) f g
      comp_smul := fun M N P f a g ↦
        Linear.comp_smul M N P f (compactSupportSequenceScalars l E W a) g }

private theorem compactSupportSequenceProjection_app (W : Scheme.{u}) (n : ℕ)
    (V : W.ProEtᵒᵖ) :
    (compactSupportSequenceProjection l E W).app (op (n, V.unop)) =
      (forget₂ CommRingCat RingCat).map
        ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app V) := rfl

private theorem compactSupportEvaluationRingCast (W : Scheme.{u}) (n : ℕ)
    (V : W.ProEtᵒᵖ) :
    (eqToHom (coefficientSequenceEvaluationRing_eq.{u, u} l E W n).symm).hom.app V =
      𝟙 ((integralCoefficientSheaf l E W n).obj.obj V) := by
  change ((sheafToPresheaf (ProEt.topology W) RingCat).map
    (eqToHom (coefficientSequenceEvaluationRing_eq.{u, u} l E W n).symm)).app V = _
  rw [eqToHom_map, eqToHom_app]
  rfl

-- Transport across normalized coefficient carriers requires additional elaboration steps.
private theorem compactSupportSequenceRestrictionLinear (W : Scheme.{u}) :
    letI := compactSupportSequenceLinear l E W
    letI := compactSupportScalarLinear l E W
    (coefficientSequenceRestriction.{u, u} l E W).Linear
      (Padic.coefficientExtensionIntegers l E) := by
  refine compactSupportSequenceRestriction_linear_of_sections l E W
    (compactSupportScalarLinear l E W) (compactSupportSequenceLinear l E W)
    (compactSupportScalarLinear_normalized l E W)
    (fun a V ↦ (compactSupportSequenceScalars l E W a).val V) ?_ ?_
  · intro M a n V x
    rfl
  · intro a n V
    simp only [compactSupportSequenceScalars, RingHom.codRestrict_apply,
      RingHom.pi_apply, RingHom.comp_apply, compactSupportSequenceProjection_app]
    rw [compactSupportEvaluationRingCast]
    rfl

private theorem compactSupportRightDerivedLinear
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (R : Type*) [CommRing R] [Linear R C] [Linear R D]
    (F : C ⥤ D) [F.Additive] [F.Linear R] : F.rightDerivedFunctor.Linear R := by
  have : (HomotopyCategory.KInjectives.equivalence C).functor.Linear R := by
    change ((HomotopyCategory.subcategoryAcyclic C).rightOrthogonal.ι ⋙
      DerivedCategory.Qh).Linear R
    infer_instance
  exact Functor.linear_of_iso R F.rightDerivedFunctorIsoKInjectives.symm

private theorem compactSupportAdjointTransition
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (S : B ⥤ A) (e : S ⋙ Rm ≅ Rn)
    {M : C} {P : A} {Q : B} (a : M ⟶ Rm.obj P) (b : M ⟶ Rn.obj Q)
    (v : P ⟶ S.obj Q) (h : a ≫ Rm.map v ≫ e.hom.app Q = b) :
    (am.homEquiv M P).symm a ≫ v =
      (am.homEquiv M (S.obj (Ln.obj M))).symm
          (an.unit.app M ≫ e.inv.app (Ln.obj M)) ≫
        S.map ((an.homEquiv M Q).symm b) := by
  apply (am.homEquiv M (S.obj Q)).injective
  rw [am.homEquiv_naturality_right, Equiv.apply_symm_apply,
    am.homEquiv_naturality_right, Equiv.apply_symm_apply]
  apply (cancel_mono (e.hom.app Q)).1
  simp only [Category.assoc]
  have he := e.hom.naturality ((an.homEquiv M Q).symm b)
  dsimp only [Functor.comp_map] at he
  rw [he, Iso.inv_hom_id_app_assoc, ← an.homEquiv_unit, Equiv.apply_symm_apply]
  exact h

private theorem compactSupportTowerTransition_fac (W : Scheme.{u}) (m n : ℕ)
    (h : n ≤ m) (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    (pbcTowerTransition W (completedIntegralCommRingSheafUnrestricted l E W) m n h).app
        (DerivedCategory.Q.obj I) ≫
      (coefficientConstantTowerEvaluationFactors.{u, u} l E W n).hom.app I =
    (coefficientConstantTowerEvaluationFactors.{u, u} l E W m).hom.app I ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).map (homOfLE h).op)
        (.up ℤ)).app I) := by
  change _ ≫ (((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj
    (op n)).mapDerivedCategoryFactors.hom.app I) = _
  simp only [pbcTowerTransition, Localization.liftNatTrans_app, Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  rfl

private theorem compactSupportTowerProjection_comp (W : Scheme.{u}) (m n : ℕ)
    (h : n ≤ m) (K : coefficientSequenceRestrictedDerived.{u, u} l E W) :
    (coefficientConstantTowerProjection.{u, u} l E W m).app K ≫
      (pbcTowerTransition W (completedIntegralCommRingSheafUnrestricted l E W) m n h).app K =
    (coefficientConstantTowerProjection.{u, u} l E W n).app K := by
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  have := hI
  have hi : (coefficientConstantTowerProjection.{u, u} l E W m).app
      (DerivedCategory.Q.obj I) ≫
      (pbcTowerTransition W (completedIntegralCommRingSheafUnrestricted l E W) m n h).app
        (DerivedCategory.Q.obj I) =
    (coefficientConstantTowerProjection.{u, u} l E W n).app
      (DerivedCategory.Q.obj I) := by
    apply (cancel_mono
      ((coefficientConstantTowerEvaluationFactors.{u, u} l E W n).hom.app I)).1
    erw [Category.assoc, compactSupportTowerTransition_fac, ← Category.assoc]
    dsimp only [coefficientConstantTowerProjection]
    rw [(coefficientConstantTowerProjection_exists.{u, u} l E W m).choose_spec.1 I,
      (coefficientConstantTowerProjection_exists.{u, u} l E W n).choose_spec.1 I]
    rw [Category.assoc, ← Functor.map_comp]
    congr 2
    apply HomologicalComplex.hom_ext
    intro i
    exact limit.w (I.X i) (homOfLE h).op
  apply (cancel_epi ((coefficientConstantTowerLimit.{u, u} l E W).map e.inv)).1
  erw [← Category.assoc, (coefficientConstantTowerProjection.{u, u} l E W m).naturality,
    Category.assoc,
    (pbcTowerTransition W (completedIntegralCommRingSheafUnrestricted l E W) m n h).naturality,
    ← Category.assoc, hi,
    (coefficientConstantTowerProjection.{u, u} l E W n).naturality]
  rfl

private theorem compactSupportSequenceProjection_comp (W : Scheme.{u})
    {m n : ℕ} (h : n ≤ m) (M : coefficientSequenceDerived.{u, u} l E W) :
    (coefficientSequenceProjection l E W m).app M ≫
      (scalarReductionDerivedRestriction l E W m).map
        ((compactSupportCoefficientTransition l E W h).app M) ≫
      (compactSupportRestrictionComp l E W m n h).hom.app
        ((coefficientSequenceDerivedEvaluation l E W n).obj M) =
    (coefficientSequenceProjection l E W n).app M := by
  dsimp only [coefficientSequenceProjection, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [Category.assoc, ← compactSupportCoefficientTransition_restricted l E W h M,
    ← Category.assoc, compactSupportTowerProjection_comp]

private theorem compactSupportReductionTransition
    (W : Scheme.{u}) (S : CoefficientDerivedSystemReduction.{u, u} l E W)
    {m n : ℕ} (h : n ≤ m) (K : DerivedCategory (scalarReductionSource l E W)) :
    (compactSupportCoefficientTransition l E W h).app (S.reduction.obj K) ≫
      (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory.map
          ((S.reductionEvaluation n).hom.app K) =
    (S.reductionEvaluation m).hom.app K ≫ compactSupportReductionMap l E W m n h K := by
  let A (n : ℕ) := (derivedScalarExtensionRestrictionAdjunction l E W n).choose
  let a (n : ℕ) := S.adjunction.unit.app K ≫
    (coefficientSequenceProjection l E W n).app (S.reduction.obj K)
  have ha (n : ℕ) : ((A n).homEquiv K _).symm (a n) =
      (S.reductionEvaluation n).inv.app K := by
    apply ((A n).homEquiv K _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    exact S.unit_projection K n
  have hc : a m ≫ (scalarReductionDerivedRestriction l E W m).map
      ((compactSupportCoefficientTransition l E W h).app (S.reduction.obj K)) ≫
      (compactSupportRestrictionComp l E W m n h).hom.app
        ((coefficientSequenceDerivedEvaluation l E W n).obj (S.reduction.obj K)) = a n := by
    dsimp only [a]
    rw [Category.assoc, compactSupportSequenceProjection_comp]
  have ht := compactSupportAdjointTransition (A m) (A n)
    (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E m n h)).mapDerivedCategory
    (compactSupportRestrictionComp l E W m n h) (a m) (a n)
    ((compactSupportCoefficientTransition l E W h).app (S.reduction.obj K)) hc
  dsimp only [Functor.id_obj] at ht
  rw [ha m, ha n] at ht
  apply (cancel_epi ((S.reductionEvaluation m).inv.app K)).1
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rw [ht]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [(proEtaleCoefficientRestrictScalars W
    (compactSupportLevelQuotient l E m n h)).mapDerivedCategory.map_id, Category.comp_id]
  rfl

private theorem compactSupportLimitLinear (W : Scheme.{u}) :
    letI := compactSupportScalarLinear l E W
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W).Linear
      (Padic.coefficientExtensionIntegers l E) := by
  letI := compactSupportScalarLinear l E W
  constructor
  intro M N f a
  apply limit.hom_ext
  intro n
  simp only [lim_map, limMap_π, Linear.smul_comp]
  rfl

private theorem compactSupportFiniteScalar (W : Scheme.{u}) (n : ℕ)
    (V : W.ProEtᵒᵖ) (a : Padic.coefficientExtensionIntegers l E) :
    ((compactSupportSequenceProjection l E W).app (op (n, V.unop)))
        (compactSupportConstantScalar l E W V a) =
      ((toSheafify (ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj (compactSupportSystemLevel l E n))).app V)
        (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a)) := by
  have hp := congrArg (fun v ↦ (v.hom.app V).hom
      (((toSheafify (ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u}
            (Padic.coefficientExtensionIntegers l E))))).app V) (ULift.up a)))
    (limit.lift_π (integralConstantCoefficientCone l E W) (op n))
  change ((compactSupportSequenceProjection l E W).app (op (n, V.unop)))
      (compactSupportConstantScalar l E W V a) = _ at hp
  rw [hp]
  let q : CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) ⟶
      compactSupportSystemLevel l E n := CommRingCat.ofHom
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).ulift
  have hq := toSheafify_naturality (ProEt.topology W)
    ((Functor.const W.ProEtᵒᵖ).map q)
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app hq V) (ULift.up a)).symm

private theorem compactSupportSystemScalarMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : (ℕ × Y.ProEt)ᵒᵖ) (a : Padic.coefficientExtensionIntegers l E) :
    (compactSupportSequenceScalars l E X a).val
        ((ProEtale.VaryingRing.baseChange f).op.obj V) =
      (ProEtale.VaryingRing.ringMapApp (compactSupportSystemLevel l E) f V)
        ((compactSupportSequenceScalars l E Y a).val V) := by
  simp only [compactSupportSequenceScalars, RingHom.codRestrict_apply,
    RingHom.pi_apply, RingHom.comp_apply]
  have hc (W : Scheme.{u}) (V : W.ProEtᵒᵖ) :
      compactSupportConstantScalarHom l E W V a =
        compactSupportConstantScalar l E W V a := rfl
  have hx := compactSupportFiniteScalar l E X V.unop.1
    (op ((proEtaleBaseChange f).obj V.unop.2)) a
  have hy := compactSupportFiniteScalar l E Y V.unop.1 (op V.unop.2) a
  change ((compactSupportSequenceProjection l E X).app _).hom
      (compactSupportConstantScalarHom l E X _ a) = _ at hx
  change ((compactSupportSequenceProjection l E Y).app _).hom
      (compactSupportConstantScalarHom l E Y _ a) = _ at hy
  erw [hx, hy]
  have h := ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj (compactSupportSystemLevel l E V.unop.1))
    ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
        (compactSupportSystemLevel l E V.unop.1)))).apply_symm_apply
    (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (compactSupportSystemLevel l E V.unop.1))))
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app h (op V.unop.2))
    (ULift.up (Ideal.Quotient.mk
      (Padic.coefficientExtensionIdeal l E (V.unop.1 + 1)) a))).symm

-- Transport across normalized coefficient carriers requires additional elaboration steps.
-- The native module pushforward changes only the scalar action on sections.
private theorem compactSupportSystemPushLinear {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI := compactSupportSequenceLinear l E X
    letI := compactSupportSequenceLinear l E Y
    @Functor.Linear (Padic.coefficientExtensionIntegers l E) _
      (coefficientSequenceModules.{u, u} l E X) (coefficientSequenceModules.{u, u} l E Y)
      _ _ _ _ _ _
      (ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f) := by
  letI := compactSupportSequenceLinear l E X
  letI := compactSupportSequenceLinear l E Y
  rw [Functor.linear_iff]
  intro M a
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  let y : M.val.obj ((ProEtale.VaryingRing.baseChange f).op.obj V) := x
  change (compactSupportSequenceScalars l E X a).val
      ((ProEtale.VaryingRing.baseChange f).op.obj V) • y =
    (ProEtale.VaryingRing.ringMapApp (compactSupportSystemLevel l E) f V)
      ((compactSupportSequenceScalars l E Y a).val V) • y
  exact congrArg (fun b : (((coefficientSequenceCommRingSheaf.{u, u} l E X).obj ⋙
      forget₂ CommRingCat RingCat).obj ((ProEtale.VaryingRing.baseChange f).op.obj V)) ↦ b • y)
      (compactSupportSystemScalarMap l E f V a)

private theorem compactSupportFiniteSquare
    {C₀ C₁ D₀ D₁ : Type*} [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) (p : C₁ ⥤ C₀) (q : D₁ ⥤ D₀)
    (χ : p ⋙ F₀ ⟶ F₁ ⋙ q)
    {x k : C₀} {y z : C₁} {a : D₀} {b : D₁}
    (d : x ⟶ p.obj y) (ρ₀ : x ⟶ k) (ρ₁ : y ⟶ z) (t : k ⟶ p.obj z)
    (τ : a ⟶ q.obj b) (ε₀ : a ⟶ F₀.obj x) (ε₁ : b ⟶ F₁.obj y)
    (hg : τ ≫ q.map ε₁ = ε₀ ≫ F₀.map d ≫ χ.app y)
    (hd : d ≫ p.map ρ₁ = ρ₀ ≫ t) :
    τ ≫ q.map ε₁ ≫ q.map (F₁.map ρ₁) =
      ε₀ ≫ F₀.map ρ₀ ≫ F₀.map t ≫ χ.app z := by
  have hn := χ.naturality ρ₁
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hg, ← hn, ← F₀.map_comp_assoc, hd]
  simp only [Functor.map_comp, Category.assoc]

private theorem compactSupportCompletedSquare
    {D₀ D₁ B : Type*} [Category D₀] [Category D₁] [Category B]
    (q : D₁ ⥤ D₀) (R₀ : D₀ ⥤ B) (R₁ : D₁ ⥤ B) (ω : q ⋙ R₀ ⟶ R₁)
    {a x k j : D₀} {b y z : D₁} {v w : B}
    (τ : a ⟶ q.obj b) (ε₀ : a ⟶ x) (ε₁ : b ⟶ y)
    (ρ₀ : x ⟶ k) (ρ₁ : y ⟶ z) (t₀ : k ⟶ j) (t₁ : j ⟶ q.obj z)
    (σ : v ⟶ w) (ι₀ : v ⟶ R₀.obj a) (ι₁ : w ⟶ R₁.obj b)
    (ht : σ ≫ ι₁ = ι₀ ≫ R₀.map τ ≫ ω.app b)
    (H : τ ≫ q.map ε₁ ≫ q.map ρ₁ = ε₀ ≫ ρ₀ ≫ t₀ ≫ t₁) :
    σ ≫ ι₁ ≫ R₁.map ε₁ ≫ R₁.map ρ₁ =
      ι₀ ≫ R₀.map ε₀ ≫ R₀.map ρ₀ ≫ R₀.map t₀ ≫ R₀.map t₁ ≫ ω.app z := by
  have hε := ω.naturality ε₁
  have hρ := ω.naturality ρ₁
  dsimp only [Functor.comp_map] at hε hρ
  rw [reassoc_of% ht, ← reassoc_of% hε, ← hρ]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun f ↦ ι₀ ≫ R₀.map f ≫ ω.app z) H

-- Derived functors are used through their comparison lemmas, without unfolding resolutions.
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor

-- Preserve the original instance-binder names in the unchanged theorem signature.
set_option linter.unusedVariables false in
/-- There is a coherent exact integral-linear compact-support reduction tower functor.
Its natural evaluation comparisons identify every transition with the canonical
quotient/direct-image comparison, including adjacent and equal levels.
Source: blueprint `lem-weil-compact-support-representative-independence`, first
proof sentence; Stacks Tags 0940, 0941 and 06YY; Bhatt--Scholze, Definition 6.7.6
(blueprint: lem-weil-compact-support-reduction-tower-functor).
Proof:
1. Form the ringed sequence site with quotient restriction maps. Its module sheaves
are semilinear coefficient systems, and it admits simultaneous K-injective resolutions
by lem-coef-semilinear-derived-sections, lem-weil-pbc-diagram-site-realization and
prop-pur-kinjective-resolutions-exist.
2. Derived pullback along the completed-to-system coefficient morphism gives exact
simultaneous reduction, computed by P tensor A_n on a flat-term K-flat resolution
(lem-weil-pbc-ringed-topoi-derived-pullback and lem-pc-kflat-resolution).
The strict chain maps id tensor q compose for all pairs of coefficient levels.
3. Apply exact open extension at every level, then the separately right-derived
proper direct image of the entire system. The geometric clauses of
lem-coef-semilinear-derived-sections identify its evaluations with Rp_* j_!,
including on all derived morphisms. They apply to arbitrary semilinear sections.
4. Restrict every level along B_Y to A_n. The projection compatibility makes the
transitions B_Y-linear. Exact restriction descends to the derived strict-tower
category by situation-conventions.
5. Each factor is triangulated; use lem-pc-right-derived-functor-triangulated and
lem-weil-pbc-triangulated-functor-composite to obtain the composite shift structure.
6. Evaluation of the coherent system gives precisely the displayed transition:
apply compact support to the quotient-induced map and then its canonical scalar
comparison. The proper comparison is normalized on K-injective replacements by
lem-weil-proetale-direct-image-restriction-of-scalars, without assuming that
restriction preserves K-injectives; the open comparison is identity on underlying
abelian sheaves (lem-sf-compact-support-restriction-of-scalars).
7. Quotient composition holds on K-flat complexes before localization; the
coefficient comparison cocycle carries it to every pair m>=n and is natural in K.
8. Compatible constant sections define the two normalized linear structures.
All four factors preserve these scalars on complexes and their resolution roofs,
so their composite is R-linear. The derived tower action is induced levelwise,
not a scalar action chosen after evaluation. -/
theorem exists_compactSupportReductionTower
    (K₀ : Type u) [Field K₀] (X Y : Scheme.{u})
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hl : IsUnit (l : K₀)) (c : Compactification f) :
    ∃ (sX : Linear (Padic.coefficientExtensionIntegers l E) (scalarReductionSource l E X))
      (sY : Linear (Padic.coefficientExtensionIntegers l E) (scalarReductionSource l E Y)),
      (fun [linearX : Linear (Padic.coefficientExtensionIntegers l E) (scalarReductionSource l E X)]
        [linearY : Linear (Padic.coefficientExtensionIntegers l E) (scalarReductionSource l E Y)] ↦
        IsCompactSupportScalarAction l E X ∧ IsCompactSupportScalarAction l E Y ∧
        ∃ T : DerivedCategory (scalarReductionSource l E X) ⥤
            DerivedCategory (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y)),
          CompactSupportReductionTowerFunctorSpec l E c T)
        (linearX := sX) (linearY := sY) := by
  classical
  let sX := compactSupportScalarLinear l E X
  let sY := compactSupportScalarLinear l E Y
  refine ⟨sX, sY, compactSupportScalarLinear_normalized l E X,
    compactSupportScalarLinear_normalized l E Y, ?_⟩
  let := sX
  let := sY
  obtain ⟨S, hS⟩ := coefficientDerivedSystemEvaluationCalculus.{u, u} l E X
  let A := compactSupportSystemLevel l E
  let q := compactSupportSystemQuotient l E
  let J : coefficientSequenceDerived.{u, u} l E X ⥤
      coefficientSequenceDerived.{u, u} l E c.Z := ProEtale.VaryingRing.J.{u} A q c.i
  let G : coefficientSequenceDerived.{u, u} l E c.Z ⥤
      coefficientSequenceDerived.{u, u} l E Y := ProEtale.VaryingRing.P.{u} A q c.g
  let U := coefficientSequenceDerivedRestriction.{u, u} l E Y
  let T : DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y)) :=
    S.reduction ⋙ J ⋙ G ⋙ U
  letI : (coefficientSequenceLimit.{u, u} l E X).CommShift ℤ := by
    unfold coefficientSequenceLimit coefficientConstantTowerLimit
      coefficientSequenceDerivedRestriction
    infer_instance
  letI : (coefficientSequenceLimit.{u, u} l E X).IsTriangulated := by
    unfold coefficientSequenceLimit coefficientConstantTowerLimit
      coefficientSequenceDerivedRestriction
    infer_instance
  letI : S.reduction.CommShift ℤ := S.adjunction.leftAdjointCommShift ℤ
  letI : S.adjunction.CommShift ℤ := S.adjunction.commShift_of_rightAdjoint ℤ
  letI : S.reduction.IsTriangulated := S.adjunction.isTriangulated_leftAdjoint
  letI : U.CommShift ℤ := by dsimp [U, coefficientSequenceDerivedRestriction]; infer_instance
  letI : U.IsTriangulated := by dsimp [U, coefficientSequenceDerivedRestriction]; infer_instance
  letI : J.CommShift ℤ := by dsimp only [J]; infer_instance
  letI : G.CommShift ℤ := by dsimp only [G]; infer_instance
  letI : J.IsTriangulated := by dsimp only [J]; infer_instance
  letI : G.IsTriangulated := by dsimp only [G]; infer_instance
  letI : T.CommShift ℤ := by dsimp only [T]; infer_instance
  have : T.IsTriangulated := by dsimp only [T]; infer_instance
  refine ⟨T, ?_, inferInstance, this, ?_⟩
  · letI := compactSupportSequenceLinear l E X
    letI := compactSupportSequenceLinear l E c.Z
    letI := compactSupportSequenceLinear l E Y
    have := compactSupportSequenceRestrictionLinear l E X
    have := compactSupportSequenceRestrictionLinear l E Y
    have := compactSupportLimitLinear l E X
    have := compactSupportSystemPushLinear l E c.i
    have := compactSupportSystemPushLinear l E c.g
    letI : Linear (Padic.coefficientExtensionIntegers l E)
        (ProEtale.VaryingRing.Modules A q X) := compactSupportSequenceLinear l E X
    letI : Linear (Padic.coefficientExtensionIntegers l E)
        (ProEtale.VaryingRing.Modules A q c.Z) := compactSupportSequenceLinear l E c.Z
    letI : Linear (Padic.coefficientExtensionIntegers l E)
        (ProEtale.VaryingRing.Modules A q Y) := compactSupportSequenceLinear l E Y
    have : (ProEtale.VaryingRing.pull A q c.i).Linear
        (Padic.coefficientExtensionIntegers l E) :=
      (ProEtale.VaryingRing.moduleAdj A q c.i).left_adjoint_linear
    have : (ProEtale.VaryingRing.extension A q c.i).Linear
        (Padic.coefficientExtensionIntegers l E) :=
      (ProEtale.VaryingRing.moduleJAdj A q c.i).left_adjoint_linear
    have : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤
        scalarReductionSource l E X).rightDerivedFunctor.Linear
          (Padic.coefficientExtensionIntegers l E) :=
      compactSupportRightDerivedLinear _ _
    have : (coefficientSequenceLimit.{u, u} l E X).Linear
        (Padic.coefficientExtensionIntegers l E) := by
      unfold coefficientSequenceLimit coefficientConstantTowerLimit
        coefficientSequenceDerivedRestriction
      infer_instance
    have : S.reduction.Linear (Padic.coefficientExtensionIntegers l E) :=
      S.adjunction.left_adjoint_linear
    have : J.Linear (Padic.coefficientExtensionIntegers l E) := by
      dsimp only [J, ProEtale.VaryingRing.J]
      infer_instance
    have : G.Linear (Padic.coefficientExtensionIntegers l E) :=
      compactSupportRightDerivedLinear _ _
    have : U.Linear (Padic.coefficientExtensionIntegers l E) := by
      dsimp only [U, coefficientSequenceDerivedRestriction]
      infer_instance
    dsimp only [T]
    infer_instance
  · let e (n : ℕ) : T ⋙ pbcTowerEvaluation Y
        (completedIntegralCommRingSheafUnrestricted l E Y) n ≅
          compactSupportRestrictedLevel l E c n :=
      Functor.isoWhiskerLeft (S.reduction ⋙ J ⋙ G)
          (coefficientRestrictedEvaluationIso.{u, u} l E Y n) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft S.reduction (compactSupportSystemEvaluation l E c n) ≪≫
            (Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight (S.reductionEvaluation n) _) _
    refine ⟨e, ?_, ?_⟩
    swap
    · unfold IsNativeCompactSupportTowerPresentation
      exact ⟨S, rfl, HEq.rfl⟩
    intro m n h K
    let F (n : ℕ) := sfIntrinsicCompactSupport c
      (Padic.coefficientExtensionRing l E (n + 1))
    let R (W : Scheme.{u}) (n : ℕ) := scalarReductionDerivedRestriction l E W n
    let r (W : Scheme.{u}) := (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E m n h)).mapDerivedCategory
    let M := S.reduction.obj K
    let N := (J ⋙ G).obj M
    let d := (compactSupportCoefficientTransition l E X h).app M
    let dn := (compactSupportCoefficientTransition l E Y h).app N
    let ε (n : ℕ) := (compactSupportSystemEvaluation l E c n).hom.app M
    let ρ (n : ℕ) := (S.reductionEvaluation n).hom.app K
    have hg := compactSupportNativeSystemTransition l E c h M
    have hd := compactSupportReductionTransition l E X S.toCoefficientDerivedSystemReduction h K
    change dn ≫ (r Y).map (ε n) = ε m ≫ (F m).map d ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
        ((coefficientSequenceDerivedEvaluation l E X n).obj M) at hg
    change d ≫ (r X).map (ρ n) = ρ m ≫ compactSupportReductionMap l E X m n h K at hd
    have H := compactSupportFiniteSquare (F m) (F n) (r X) (r Y)
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom
      d (ρ m) (ρ n) (compactSupportReductionMap l E X m n h K) dn (ε m) (ε n) hg hd
    simp only [e, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      compactSupportRestrictedTransition, Functor.map_comp,
      Category.id_comp, Category.assoc]
    change (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y) m n h).app
        (U.obj N) ≫
      (coefficientRestrictedEvaluationIso l E Y n).hom.app N ≫
      (R Y n).map (ε n) ≫ (R Y n).map ((F n).map (ρ n)) =
      (coefficientRestrictedEvaluationIso l E Y m).hom.app N ≫
      (R Y m).map (ε m) ≫ (R Y m).map ((F m).map (ρ m)) ≫
      (R Y m).map ((F m).map (compactSupportReductionMap l E X m n h K)) ≫
      (R Y m).map ((sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
          ((scalarReductionDerivedExtension l E X n).obj K)) ≫
      (compactSupportRestrictionComp l E Y m n h).hom.app
        ((F n).obj ((scalarReductionDerivedExtension l E X n).obj K))
    exact compactSupportCompletedSquare (r Y) (R Y m) (R Y n)
      (compactSupportRestrictionComp l E Y m n h).hom dn (ε m) (ε n)
      ((F m).map (ρ m)) ((F n).map (ρ n))
      ((F m).map (compactSupportReductionMap l E X m n h K))
      ((sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
        ((scalarReductionDerivedExtension l E X n).obj K))
      ((pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y) m n h).app
        (U.obj N))
      ((coefficientRestrictedEvaluationIso l E Y m).hom.app N)
      ((coefficientRestrictedEvaluationIso l E Y n).hom.app N)
      (compactSupportCoefficientTransition_restricted l E Y h N) H

end WeilConjectures

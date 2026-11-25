/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefOpenTensorEvaluationData
import all WeilConjectures.AlgebraicGeometry.Geometric.GeometricTensorEvaluation
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorEvaluation
import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefEvaluationTensorComparisonModel
import all WeilConjectures.AlgebraicGeometry.System.SystemOrdinaryTensorReduction

/-! # Evaluation of the normalized restriction tensor comparison

Source: Stacks 07A4 and 0941; support-open-tensor steps 5--6.
(blueprint: lem-coef-native-restriction-tensor-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open WeilConjectures.SemilinearSections
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive Functor.ofSequence Functor.ofOpSequence
  constantSheaf presheafToSheaf MorphismProperty.Over.pullback
  DerivedCategory DerivedCategory.Q DerivedCategory.Qh _root_.instCategoryDerivedCategory
namespace WeilConjectures.CoefSupportOpenTensor

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance 2000] coefficientSequenceEvaluation_additiveInstance
  coefficientSequenceEvaluation_limits coefficientSequenceEvaluation_colimits
attribute [local irreducible] coefficientTensorGenerator coefficientTotalTensor
  SheafOfModules.monoidalCategory CoefficientClosedStructure.tensor
  coefficientSystemTensorModelIso coefficientFiniteTensorModelIso
  ordinaryEvaluationTensor ordinaryTensorHom tensorSection

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSystem coefficientSequenceCommRingTransition
  coefficientSequenceEvaluation coefficientSequenceHasDerived
  integralCoefficientSheafTransition compactSupportSystemLevel compactSupportSystemQuotient
  ProEtale.VaryingRing.coefficientTransition RingHom.ulift
  SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  SemilinearSections.evaluation
  SheafOfModules.pushforward SheafOfModules.restrictScalars
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'
  ProEtale.StrictTower.moduleDirectImage proEtaleRingModuleDirectImage
  ProEtale.VaryingRing.push ProEtale.VaryingRing.baseChange ProEtale.StrictTower.modulePullback
  coefficientEvaluationSection SemilinearSections.evalSection pullSection finitePullSection
attribute [local instance 2000] ProEtale.VaryingRing.extensionAdditive
  ProEtale.VaryingRing.extensionLimits ProEtale.VaryingRing.extensionColimits
  ProEtale.VaryingRing.pullAdditive ProEtale.VaryingRing.pullLimits
  ProEtale.VaryingRing.pullColimits ProEtale.StrictTower.moduleJ_additive
  ProEtale.StrictTower.moduleJ_finiteLimits ProEtale.StrictTower.moduleJ_finiteColimits
  ProEtale.StrictTower.modulePullback_additive ProEtale.StrictTower.modulePullback_finiteLimits
  ProEtale.StrictTower.modulePullback_finiteColimits

private theorem square_of_unit
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {P : D ⥤ C} (a : F ⊣ P)
    {A B : C} {X Y : D} (χ : X ≅ F.obj A) (μ : A ≅ B)
    (f : X ⟶ Y) (g : F.obj B ⟶ Y) (h : A ⟶ P.obj X)
    (hn : h ≫ P.map χ.hom = a.unit.app A)
    (hs : μ.inv ≫ h ≫ P.map f = a.unit.app B ≫ P.map g) :
    f = χ.hom ≫ F.map μ.hom ≫ g := by
  have hu : a.unit.app A ≫ P.map χ.inv = h := by
    rw [← hn]
    simp only [Category.assoc, ← P.map_comp, Iso.hom_inv_id,
      P.map_id, Category.comp_id]
  apply (cancel_epi χ.inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply (a.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, P.map_comp]
  rw [reassoc_of% hu]
  apply (cancel_epi μ.inv).1
  have hr := a.unit.naturality μ.hom
  change μ.hom ≫ a.unit.app B = a.unit.app A ≫ P.map (F.map μ.hom) at hr
  rw [← reassoc_of% hr, Iso.inv_hom_id_assoc]
  exact hs

private theorem raw_eval_pullSection
    (R : ℕ → CommRingCat.{u + 1}) (q : ∀ n, R (n + 1) ⟶ R n)
    {X Z : Scheme.{u}} (j : X ⟶ Z) (n : ℕ)
    (M : ProEtale.VaryingRing.Modules R q Z) (V : Z.ProEtᵒᵖ)
    (x : M.val.obj (op (n, V.unop))) :
    ((ProEtale.VaryingRing.moduleEvalG R q j n).hom.app M).val.app
      ((proEtaleBaseChange j).op.obj V)
      (((ProEtale.VaryingRing.moduleAdj R q j).unit.app M).val.app
        (op (n, V.unop)) x) =
    ((proEtaleRingModuleAdjunction j (ProEtale.VaryingRing.coefficients R Z n)
      (ProEtale.VaryingRing.coefficients R X n)
      (ProEtale.StrictTower.constantRingIso (R n) j)).unit.app
        ((ProEtale.VaryingRing.eval R q Z n).obj M)).val.app V x := by
  have h := (ProEtale.VaryingRing.moduleEvalG_existsUnique R q j n).choose_spec.1 M
  have hh := congrArg (fun f ↦ f.val.app V x) h
  change ((ProEtale.VaryingRing.moduleEvalG R q j n).hom.app M).val.app
    ((proEtaleBaseChange j).op.obj V)
    (((ProEtale.VaryingRing.moduleEvalP R q j n).hom.app _).val.app V
      (((ProEtale.VaryingRing.moduleAdj R q j).unit.app M).val.app
        (op (n, V.unop)) x)) = _ at hh
  have hp := (ProEtale.VaryingRing.moduleEvalP_existsUnique R q j n).choose_spec.1
    ((ProEtale.VaryingRing.pull R q j).obj M)
    V.unop (((ProEtale.VaryingRing.moduleAdj R q j).unit.app M).val.app
      (op (n, V.unop)) x)
  have hpp := congrArg (fun z ↦
    ((ProEtale.VaryingRing.moduleEvalG R q j n).hom.app M).val.app
      ((proEtaleBaseChange j).op.obj V) z) hp
  exact hpp.symm.trans hh

-- Reuse the instances stored in a model instead of asking elaboration to rebuild
-- its large coefficient-site specialization. The resulting applications are
-- ordinary terms and are checked by Lean's kernel.
local elab "modelField% " f:ident m:term:max : term => do
  let e ← Lean.Elab.Term.elabTerm m none
  let t ← Lean.Meta.whnf (← Lean.Meta.inferType e)
  let .const head levels := t.getAppFn | Lean.throwError "model structure expected"
  return Lean.mkAppN (Lean.mkConst (head ++ f.getId) levels) (t.getAppArgs.push e)

local elab "kernel_exact " t:term : tactic => Lean.Elab.Tactic.withMainContext do
  let e ← Lean.Elab.Term.elabTerm t none
  (← Lean.Elab.Tactic.getMainGoal).assign e
  Lean.Elab.Tactic.replaceMainGoal []

private theorem eval_pullSection {X Z : Scheme.{u}} (j : X ⟶ Z) (n : ℕ)
    (M : coefficientSequenceModules l E Z) (V : Z.ProEtᵒᵖ) (x : M.val.obj (op (n, V.unop))) :
    ((ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j n).hom.app M).val.app
        ((proEtaleBaseChange j).op.obj V)
      (coefficientEvaluationSection l E X _ n ((proEtaleBaseChange j).op.obj V)
        (pullSection l E j M (op (n, V.unop)) x)) =
    finitePullSection l E j n ((coefficientSequenceEvaluation l E Z n).obj M) V
      (coefficientEvaluationSection l E Z M n V x) := by
  exact raw_eval_pullSection (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j n M V x

-- Compare the two native coefficient-ring presentations in the section calculations.
private theorem ordinary_restriction_square {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j]
    (SX : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SZ : CoefficientDerivedSystemCalculus.{u, u} l E Z)
    (O : SystemOpenModel l E j SX.toCoefficientDerivedSystemTensors
      SZ.toCoefficientDerivedSystemTensors)
    (n : ℕ)
    (On : FiniteOpenModel l E j SX.toCoefficientDerivedSystemTensors
      SZ.toCoefficientDerivedSystemTensors n)
    (M N : coefficientSequenceModules l E Z) :
    (coefficientSequenceEvaluation l E X n).map
        ((modelField% ordinary (modelField% restrictionModel O)) M N).hom ≫
      ((ordinaryEvaluationTensor.{u+1, u, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X)
        (coefficientSequenceCommRingTransition l E X) n) _ _).hom ≫
      ordinaryTensorHom.{u+1, u, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)
        ((ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j n).hom.app M)
        ((ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j n).hom.app N) =
    (ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j n).hom.app
        (ordinaryTensor.{u+1, u, u} (coefficientSequenceTopology (ProEt.topology Z))
          (coefficientSequenceCommRingSheaf l E Z) M N) ≫
      (ProEtale.StrictTower.modulePullback (compactSupportSystemLevel l E n) j).map
        ((ordinaryEvaluationTensor.{u+1, u, u} (ProEt.topology Z)
        (integralCoefficientCommRingSheaf l E Z)
        (coefficientSequenceCommRingTransition l E Z) n) M N).hom ≫
      ((modelField% ordinary (modelField% restrictionModel On))
        ((coefficientSequenceEvaluation l E Z n).obj M)
        ((coefficientSequenceEvaluation l E Z n).obj N)).hom := by
  let eX := coefficientSequenceEvaluation l E X n
  let eZ := coefficientSequenceEvaluation l E Z n
  let P := ProEtale.StrictTower.moduleDirectImage (compactSupportSystemLevel l E n) j
  let a := proEtaleRingModuleAdjunction j
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
  let χ := ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j n
  let T := ordinaryTensor.{u+1, u, u} (coefficientSequenceTopology (ProEt.topology Z))
    (coefficientSequenceCommRingSheaf l E Z) M N
  let μ := ((ordinaryEvaluationTensor.{u+1, u, u} (ProEt.topology Z)
        (integralCoefficientCommRingSheaf l E Z)
        (coefficientSequenceCommRingTransition l E Z) n) M N)
  let f := eX.map ((modelField% ordinary (modelField% restrictionModel O)) M N).hom ≫
    ((ordinaryEvaluationTensor.{u+1, u, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X)
        (coefficientSequenceCommRingTransition l E X) n) _ _).hom ≫
      ordinaryTensorHom.{u+1, u, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n) (χ.hom.app M) (χ.hom.app N)
  let g := ((modelField% ordinary (modelField% restrictionModel On))
    (eZ.obj M) (eZ.obj N)).hom
  let h := eZ.map ((ProEtale.VaryingRing.moduleAdj (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j).unit.app T) ≫
    (ProEtale.VaryingRing.moduleEvalP (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j n).hom.app _
  have hn : h ≫ P.map (χ.hom.app T) = a.unit.app (eZ.obj T) := by
    kernel_exact (ProEtale.VaryingRing.moduleEvalG_existsUnique (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j n).choose_spec.1 T
  apply square_of_unit a (χ.app T) μ f g h hn
  apply tensor_hom_ext.{u+1, u, u} (ProEt.topology Z)
  intro V x y
  obtain ⟨x, rfl⟩ := evalSection_surjective.{u+1, u, u} (ProEt.topology Z)
    (integralCoefficientCommRingSheaf l E Z)
    (coefficientSequenceCommRingTransition l E Z) n M V x
  obtain ⟨y, rfl⟩ := evalSection_surjective.{u+1, u, u} (ProEt.topology Z)
    (integralCoefficientCommRingSheaf l E Z)
    (coefficientSequenceCommRingTransition l E Z) n N V y
  let V' := (proEtaleBaseChange j).op.obj V
  let σ := (modelField% ordinary (modelField% restrictionModel O)) M N
  let μX := (ordinaryEvaluationTensor.{u+1, u, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X)
        (coefficientSequenceCommRingTransition l E X) n)
    ((ProEtale.VaryingRing.pull (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j).obj M)
    ((ProEtale.VaryingRing.pull (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j).obj N)
  let z := tensorSection.{u+1, u, u} (coefficientSequenceTopology (ProEt.topology Z))
    (coefficientSequenceCommRingSheaf l E Z) M N (op (n, V.unop)) x y
  let η := (ProEtale.VaryingRing.moduleAdj (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j).unit.app T
  let pull := ProEtale.VaryingRing.pull (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j
  let ρ := ((ProEtale.VaryingRing.moduleEvalP (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j n).hom.app (pull.obj T)).val.app V
  let out := fun t ↦
    (ordinaryTensorHom.{u+1, u, u} (ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X n) (χ.hom.app M) (χ.hom.app N)).val.app V'
      (μX.hom.val.app V' ((eX.map σ.hom).val.app V' t))
  let out' := fun t ↦
    (ordinaryTensorHom.{u+1, u, u} (ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X n) (χ.hom.app M) (χ.hom.app N)).val.app V'
      (μX.hom.val.app V' t)
  let out'' := (ordinaryTensorHom.{u+1, u, u} (ProEt.topology X)
    (integralCoefficientCommRingSheaf l E X n) (χ.hom.app M) (χ.hom.app N)).val.app V'
  have h₀ := evaluation_inv_pure_cast.{u+1, u, u} (ProEt.topology Z)
    (integralCoefficientCommRingSheaf l E Z)
    (coefficientSequenceCommRingTransition l E Z) n M N V x y
  have h₁ := evaluation_map_section.{u+1, u, u} (ProEt.topology Z)
    (integralCoefficientCommRingSheaf l E Z)
    (coefficientSequenceCommRingTransition l E Z) n η V z
  have h₂ := (ProEtale.VaryingRing.moduleEvalP_existsUnique (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j n).choose_spec.1 (pull.obj T) V.unop
      (η.val.app (op (n, V.unop)) z)
  have h₃ := evaluation_map_section.{u+1, u, u} (ProEt.topology X)
    (integralCoefficientCommRingSheaf l E X)
    (coefficientSequenceCommRingTransition l E X) n σ.hom V'
      (η.val.app (op (n, V.unop)) z)
  have h₄ := (modelField% restrictionPure O) M N (op (n, V.unop)) x y
  have h₅ := evaluation_pure_cast.{u+1, u, u} (ProEt.topology X)
    (integralCoefficientCommRingSheaf l E X)
    (coefficientSequenceCommRingTransition l E X) n _ _ V'
      (pullSection l E j M (op (n, V.unop)) x)
      (pullSection l E j N (op (n, V.unop)) y)
  have h₆ := tensorSection_map.{u+1, u, u} (ProEt.topology X)
    (χ.hom.app M) (χ.hom.app N) V'
    (evalSection.{u+1, u, u} (ProEt.topology X) (integralCoefficientCommRingSheaf l E X)
      (coefficientSequenceCommRingTransition l E X) n _ V'
      (pullSection l E j M (op (n, V.unop)) x))
    (evalSection.{u+1, u, u} (ProEt.topology X) (integralCoefficientCommRingSheaf l E X)
      (coefficientSequenceCommRingTransition l E X) n _ V'
      (pullSection l E j N (op (n, V.unop)) y))
  have h₇ := eval_pullSection l E j n M V x
  have h₈ := eval_pullSection l E j n N V y
  have h₉ := ((modelField% restrictionPure On) (eZ.obj M) (eZ.obj N) V
    (evalSection.{u+1, u, u} (ProEt.topology Z) (integralCoefficientCommRingSheaf l E Z)
      (coefficientSequenceCommRingTransition l E Z) n M V x)
    (evalSection.{u+1, u, u} (ProEt.topology Z) (integralCoefficientCommRingSheaf l E Z)
      (coefficientSequenceCommRingTransition l E Z) n N V y)).symm
  have H₀ := congrArg (fun t ↦ out (ρ ((eZ.map η).val.app V t))) h₀
  have H₁ := congrArg (fun t ↦ out (ρ t)) h₁
  have H₂ := congrArg out h₂
  have H₃ := congrArg out' h₃
  have H₄ := congrArg (fun t ↦ out' (evalSection.{u+1, u, u} (ProEt.topology X)
    (integralCoefficientCommRingSheaf l E X) (coefficientSequenceCommRingTransition l E X)
    n _ V' t)) h₄
  have H₅ := congrArg out'' h₅
  have H₆ := congrArg₂ (tensorSection.{u+1, u, u} (ProEt.topology X)
    (integralCoefficientCommRingSheaf l E X n) _ _ V') h₇ h₈
  kernel_exact H₀.trans (H₁.trans (H₂.trans (H₃.trans
    (H₄.trans (H₅.trans (h₆.trans (H₆.trans h₉)))))))

/-- Evaluation commutes with the tensor comparison for open inverse image.
This concerns only restriction and tensor, before taking an open-extension mate.
Source: Stacks 07A4, sites-cohomology-lemma-pullback-tensor-product;
Stacks 03EK, sites-modules-section-tensor-product;
support-open-tensor steps 5--6 and the recorded evaluation tensor normalization.
(blueprint: lem-coef-native-restriction-tensor-evaluation).

Proof: choose flat-term K-flat representatives of M and N. On ordinary module
sheaves, precompose the two maps with inverse image of the pure-tensor section
and the inverse-image adjunction unit. The restrictionPure equations for O and
On, the unit normalization of moduleEvalG, and the pure-tensor normalization of
coefficientEvaluationTensorIso identify both outputs with the tensor of the two
pulled, evaluated sections. The inverse-image adjunction and tensor
sheafification show equality of these ordinary maps. On each total summand of
bidegree (a,b), use the same ordinary equality; evaluation preserves direct sums
and the signed differential, so the cochain maps agree. The restrictionModel
fields and evaluationTensor_normalization identify their localizations with the
two displayed composites. Cancel the tensor-model and exact-functor
factorization isomorphisms. Finally naturality along the resolving
quasi-isomorphisms gives the square for M and N. This uses neither an open
tensor projection nor its evaluation equation. Identity and empty opens, zero
objects, and degree n = 0 obey the same unit and generator equations. -/
theorem nativeRestrictionTensorEvaluation {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j]
    (SX : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SZ : CoefficientDerivedSystemCalculus.{u, u} l E Z)
    (O : SystemOpenModel l E j SX.toCoefficientDerivedSystemTensors
      SZ.toCoefficientDerivedSystemTensors)
    (n : ℕ)
    (On : FiniteOpenModel l E j SX.toCoefficientDerivedSystemTensors
      SZ.toCoefficientDerivedSystemTensors n)
    (M N : coefficientSequenceDerived.{u, u} l E Z) :
    let θ := @OpenTensorModel.restriction.{u+1, u, u} (ℕ × Z.ProEt) _
      (ProEtale.VaryingRing.sequenceSiteSmall Z)
      (coefficientSequenceTopology (ProEt.topology Z))
      (coefficientSequenceCommRingSheaf.{u, u} l E Z)
      SZ.systemClosed SZ.systemTensorModel
      (ℕ × X.ProEt) _ (ProEtale.VaryingRing.sequenceSiteSmall X)
      (coefficientSequenceTopology (ProEt.topology X))
      (coefficientSequenceCommRingSheaf.{u, u} l E X)
      SX.systemClosed SX.systemTensorModel
      (ProEtale.VaryingRing.extension (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.pull (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.extensionAdditive
        (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.extensionLimits
        (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.extensionColimits
        (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.pullAdditive
        (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.pullLimits
        (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.pullColimits
        (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.moduleJAdj (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.baseChange j) (pullSection l E j) O
    let ψ := @OpenTensorModel.restriction.{u+1, u, u} Z.ProEt _
      (WeilConjectures.instEssentiallySmallProEt_weilConjectures Z) (ProEt.topology Z)
      (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
      (SZ.finiteClosed n) (SZ.finiteTensorModel n)
      X.ProEt _ (WeilConjectures.instEssentiallySmallProEt_weilConjectures X) (ProEt.topology X)
      (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
      (SX.finiteClosed n) (SX.finiteTensorModel n)
      (ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) j)
      (ProEtale.StrictTower.modulePullback (compactSupportSystemLevel l E n) j)
      (ProEtale.StrictTower.moduleJ_additive (compactSupportSystemLevel l E n) j)
      (ProEtale.StrictTower.moduleJ_finiteLimits (compactSupportSystemLevel l E n) j)
      (ProEtale.StrictTower.moduleJ_finiteColimits (compactSupportSystemLevel l E n) j)
      (proEtaleRingModulePullback_additive j
        (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
        (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
        (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j))
      (proEtaleRingModulePullback_preservesFiniteLimits j
        (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
        (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
        (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j))
      (proEtaleRingModulePullback_preservesFiniteColimits j
        (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
        (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
        (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j))
      (ProEtale.StrictTower.moduleJAdj (compactSupportSystemLevel l E n) j)
      (proEtaleBaseChange j) (finitePullSection l E j n) On
    (coefficientSequenceDerivedEvaluation.{u, u} l E X n).map
        (θ.hom.app (M, N)) ≫
      (SX.evaluationTensor n).hom.app
        ((ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j).obj M,
         (ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j).obj N) ≫
      (SX.finiteClosed n).tensor.map (Prod.mkHom
        ((ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j n).hom.app M)
        ((ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j n).hom.app N)) =
    (ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j n).hom.app
          (SZ.systemClosed.tensor.obj (M, N)) ≫
      (ProEtale.StrictTower.modulePullback (compactSupportSystemLevel l E n)
        j).mapDerivedCategory.map ((SZ.evaluationTensor n).hom.app (M, N)) ≫
      ψ.hom.app
        ((coefficientSequenceDerivedEvaluation.{u, u} l E Z n).obj M,
         (coefficientSequenceDerivedEvaluation.{u, u} l E Z n).obj N) := by
  let tF := modelField% restrictionModel O
  obtain ⟨tG, hG⟩ := coefficientEvaluationTensorModel_exists l E X SX n
  obtain ⟨tH, hH⟩ := coefficientEvaluationTensorModel_exists l E Z SZ n
  let tI := modelField% restrictionModel On
  let χ := ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j n
  have ho := ordinary_restriction_square l E j SX SZ O n On
  simp_rw [← hG, ← hH] at ho
  run_tac Lean.Elab.Tactic.withMainContext do
    let get (name : Lean.Name) : Lean.Elab.Tactic.TacticM Lean.Expr := do
      return (← Lean.Meta.getLocalDeclFromUserName name).toExpr
    let tF ← get `tF
    let tG ← get `tG
    let tH ← get `tH
    let tI ← get `tI
    let tf ← Lean.Meta.whnf (← Lean.Meta.inferType tF)
    let tg ← Lean.Meta.whnf (← Lean.Meta.inferType tG)
    let th ← Lean.Meta.whnf (← Lean.Meta.inferType tH)
    let ti ← Lean.Meta.whnf (← Lean.Meta.inferType tI)
    let .const _ levels := tf.getAppFn | Lean.throwError "tensor model expected"
    let f := tf.getAppArgs
    let g := tg.getAppArgs
    let h := th.getAppArgs
    let i := ti.getAppArgs
    unless f.size == 19 && g.size == 19 && h.size == 19 && i.size == 19 do
      Lean.throwError "unexpected tensor model parameters"
    let args := #[f[0]!, f[4]!, h[4]!, g[4]!, f[1]!, f[5]!, h[5]!, g[5]!,
      f[3]!, f[6]!, h[6]!, g[6]!, f[2]!, f[7]!, h[7]!, g[7]!,
      f[8]!, f[9]!, h[9]!, g[9]!, f[10]!, g[10]!, h[10]!, i[10]!,
      f[11]!, g[11]!, h[11]!, i[11]!,
      f[12]!, f[13]!, g[12]!, g[13]!, h[12]!, h[13]!, i[12]!, i[13]!,
      f[14]!, f[15]!, h[15]!, g[15]!, f[16]!, f[17]!, h[17]!, g[17]!,
      f[18]!, g[18]!, h[18]!, i[18]!, tF, tG, tH, tI,
      ← get `χ, ← get `ho, ← get `M, ← get `N]
    (← Lean.Elab.Tactic.getMainGoal).assign
      (Lean.mkAppN (Lean.mkConst ``fourModels_square levels) args)
    Lean.Elab.Tactic.replaceMainGoal []

end WeilConjectures.CoefSupportOpenTensor

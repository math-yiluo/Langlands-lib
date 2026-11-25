/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts
import all WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts
import all WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus
import all WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingSignedRoosShift
import all WeilConjectures.PoincareDuality.Pod.PodNativeRoosFunctorComparison
import all WeilConjectures.PoincareDuality.Pod.PodNormalizedRoosComparisonShift

/-! # Signed shifts of the normalized limit-to-Roos comparison -/

@[expose] public noncomputable section
set_option autoImplicit false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 10000] WeilConjectures.podLimitCommShift

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry

-- Congruence keeps implicit additive-instance arguments explicit. In particular,
-- it uses uniqueness of preadditive structures instead of unfolding their operations.
-- Every generated term is checked by the kernel; no expression is accepted by evaluation.
open Lean Meta Elab Tactic in
private def podTransportInstances : TacticM Unit := withMainContext do
  let rec prove (x y : Expr) : Nat → MetaM Expr
    | 0 => throwError "transport recursion limit: {x} / {y}"
    | fuel + 1 => do
      if x == y then return ← mkAppM ``HEq.refl #[x]
      if (← isProof x) && (← isProof y) then
        return ← mkAppM ``proof_irrel_heq #[x, y]
      let tx ← inferType x
      if tx.getAppFn.isConstOf ``CategoryTheory.Preadditive then
        return ← mkAppM ``heq_of_eq #[← mkAppM ``Subsingleton.elim #[x, y]]
      let sameFn ← if x.getAppFn == y.getAppFn then pure true else
        if x.getAppFn.isConst && y.getAppFn.isConst &&
            x.getAppFn.constName! == y.getAppFn.constName! then
          withTransparency .reducible (isDefEq x.getAppFn y.getAppFn)
        else pure false
      if sameFn && x.getAppNumArgs == y.getAppNumArgs && x.isApp then
        let thm ← mkHCongrWithArity x.getAppFn x.getAppNumArgs
        let ax := x.getAppArgs
        let ay := y.getAppArgs
        let mut ps := #[]
        for kind in thm.argKinds, a in ax, b in ay do
          let h ← prove a b fuel
          match kind with
          | .eq => ps := ps ++ #[a, b, ← mkAppM ``eq_of_heq #[h]]
          | .heq => ps := ps ++ #[a, b, h]
          | _ => throwError "unexpected congr kind"
        return mkAppN thm.proof ps
      let xx ← withTransparency .reducible (whnf x)
      let yy ← withTransparency .reducible (whnf y)
      if xx != x || yy != y then return ← prove xx yy fuel
      if let .proj n i obj := x.getAppFn then
        if let some obj' ← withTransparency .all (unfoldDefinition? obj) then
          return ← prove (mkAppN (.proj n i obj') x.getAppArgs) y fuel
      if let .proj n i obj := y.getAppFn then
        if let some obj' ← withTransparency .all (unfoldDefinition? obj) then
          return ← prove x (mkAppN (.proj n i obj') y.getAppArgs) fuel
      if let some xx ← withTransparency .all (unfoldDefinition? x) then
        return ← prove xx y fuel
      if let some yy ← withTransparency .all (unfoldDefinition? y) then
        return ← prove x yy fuel
      let xx ← withTransparency .all (whnf x)
      let yy ← withTransparency .all (whnf y)
      if xx != x || yy != y then return ← prove xx yy fuel
      throwError "transport stuck: {x} / {y}"
  let target ← whnf (← getMainTarget)
  let some (_, x, _, y) := target.heq? | throwError "expected HEq"
  let p ← prove x y 100
  (← getMainGoal).assign p
  replaceMainGoal []

namespace WeilConjectures

-- Keep the coefficient universe explicit during sheafification synthesis.
private instance (priority := 20000) fixedAbSheafify (Z : Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} Z

private instance (priority := 20000) fixedAbBijective (Z : Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology Z).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} Z

attribute [local irreducible] CategoryTheory.RoosConeCalculus.roosCommShift

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})

/-- The localization functor of strict coefficient-system complexes. -/
private abbrev coefficientQ :
    CochainComplex (coefficientSequenceModules l E W) ℤ ⥤ coefficientSequenceDerived l E W :=
  DerivedCategory.Q

/-- The natural limit-to-Roos comparison, assembled from the exact restriction
comparison and the normalized Roos comparison composed with the native Roos functor. -/
private def nativeLimitIso (ρ : IntegralComparisonRoosModel l E W) :
    coefficientQ l E W ⋙ coefficientSequenceLimit l E W ≅
      (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ) ⋙
        roosF ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors
      (coefficientConstantTowerLimit l E W) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ρ.comparison ≪≫
      Functor.isoWhiskerRight podNativeRoosIso DerivedCategory.Q)

/-- The native Roos comparison has identity components. -/
private theorem podNativeRoosIso_hom_app
    (X : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    (podNativeRoosIso (A := scalarReductionSource l E W)).hom.app X = 𝟙 _ :=
  rfl

private theorem nativeLimitIso_hom_app (ρ : IntegralComparisonRoosModel l E W)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    (nativeLimitIso l E W ρ).hom.app C = (podLimitRoos l E ρ C).hom := by
  dsimp only [nativeLimitIso, podLimitRoos]
  erw [Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
    NatTrans.comp_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.id_comp, Category.id_comp,
    podNativeRoosIso_hom_app, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

attribute [local instance] CategoryTheory.RoosConeCalculus.roosCommShift

private instance nativeLimitIso_commShift (ρ : IntegralComparisonRoosModel l E W) :
    NatTrans.CommShift (nativeLimitIso l E W ρ).hom ℤ := by
  have := podNormalizedRoosComparisonCommShift l E W ρ _
    CategoryTheory.RoosConeCalculus.shift_augmentation
  have h1 : NatTrans.CommShift (Functor.associator (coefficientQ l E W)
      (coefficientSequenceDerivedRestriction l E W) (coefficientConstantTowerLimit l E W)).inv ℤ :=
    inferInstance
  have h2 : NatTrans.CommShift (Functor.whiskerRight
      (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.hom
      (coefficientConstantTowerLimit l E W)) ℤ := inferInstance
  have h3 : NatTrans.CommShift (Functor.associator
      ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q (coefficientConstantTowerLimit l E W)).hom ℤ := inferInstance
  have h4 : NatTrans.CommShift (Functor.whiskerLeft
      ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ))
      (ρ.comparison ≪≫ Functor.isoWhiskerRight podNativeRoosIso DerivedCategory.Q).hom) ℤ :=
    inferInstance
  have h34 := @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ h3 h4
  have h234 := @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ h2 h34
  exact @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ h1 h234

private theorem normalization_native_square
    (ρ : IntegralComparisonRoosModel l E W)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) (r : ℤ) :
    let := CategoryTheory.RoosConeCalculus.roosCommShift
      (A := scalarReductionSource l E W)
    (coefficientSequenceLimit l E W).map
        (((coefficientQ l E W).commShiftIso r).inv.app C) ≫
      (podLimitRoos l E ρ (C⟦r⟧)).hom ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map
        (podRestrictionShift l E W C r).hom) ≫
      DerivedCategory.Q.map
        ((Functor.commShiftIso roosF r).hom.app
          (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)) ≫
      (DerivedCategory.Q.commShiftIso r).hom.app
        (integralOperationsRoos (podRestrictedTower l E C)) =
    ((coefficientSequenceLimit l E W).commShiftIso r).hom.app ((coefficientQ l E W).obj C) ≫
      (podLimitRoos l E ρ C).hom⟦r⟧' := by
  let := CategoryTheory.RoosConeCalculus.roosCommShift
    (A := scalarReductionSource l E W)
  have : NatTrans.CommShift (nativeLimitIso l E W ρ).hom ℤ :=
    nativeLimitIso_commShift l E W ρ
  let R := (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)
  have h := NatTrans.shift_app_comm (nativeLimitIso l E W ρ).hom r C
  simp only [Functor.commShiftIso_comp_hom_app] at h
  erw [nativeLimitIso_hom_app, nativeLimitIso_hom_app] at h
  have h' := congrArg
    ((coefficientSequenceLimit l E W).map
      (((coefficientQ l E W).commShiftIso r).inv.app C) ≫ ·) h.symm
  simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp] at h'
  have hm := podNativeRoosMap_eq ((R.commShiftIso r).hom.app C)
  rw [Category.assoc] at h'
  intro _
  dsimp only [podRestrictionShift, Functor.mapIso_hom, Iso.app_hom]
  erw [hm]
  exact h'

/-- The K-injective-normalized Roos comparison has the prescribed signed shift.
Source: Stacks 0941, the shifted K-injective calculation, and 011G, signed shifts
(blueprint: lem-pod-limit-signed-shift-normalization-s8).

Proof: the two coordinate equations uniquely determine the signed Roos map.
On a K-injective tower, the comparison is the inverse derived-unit comparison
followed by the limit tuple with zero in the second coordinate. The tuple
inclusion commutes with the signed shift because that second coordinate is zero.
The canonical derived unit commutes with shifts. Cancel it on K-injectives,
then use naturality along a K-injective replacement to obtain the equation on
every complex. Compose with exact restriction and its canonical shift comparison.
No boundedness, completeness or constructibility is used. -/
theorem podLimitSignedShiftNormalization
    (ρ : IntegralComparisonRoosModel l E W)
    (S : PodSignedRoosShift (scalarReductionSource l E W)) (hS : S.Laws) :
    PodLimitSignedShift l E W ρ S := by
  let := CategoryTheory.RoosConeCalculus.roosCommShift
    (A := scalarReductionSource l E W)
  intro C r
  let R := (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)
  have hS' : S = podNativeRoosShift := roosShift_eq S podNativeRoosShift hS nativeRoos_laws
  subst S
  have hN := normalization_native_square l E W ρ C r
  have hn := native_shift_Q (A := scalarReductionSource l E W) (R.obj C) r
  dsimp only at hN
  erw [hn] at hN
  refine HEq.trans ?_ (HEq.trans (heq_of_eq hN) ?_)
  all_goals run_tac podTransportInstances

end WeilConjectures

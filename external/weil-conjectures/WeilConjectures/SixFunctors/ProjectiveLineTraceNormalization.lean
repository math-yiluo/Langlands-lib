/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransportData
public import WeilConjectures.SixFunctors.ProjectiveLineTraceModel
import WeilConjectures.SixFunctors.ProjectiveLineTraceRawAdjustment

/-! # Comparison of the two explicit projective-line trace presentations

A coefficient automorphism relates geometric transport to the prescribed ordinary trace.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private meta def unfoldInstanceBoundary (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
  if let .fvar id := e then
    if let some v := (← id.getDecl).value? then return some v
  if let .letE _ _ v b _ := e then return some (b.instantiate1 v)
  let names : List Lean.Name := [``DerivedCategoryModule, ``presentedFiniteP1Trace,
    `AlgebraicGeometry.Etale.SfP1Transport.trace,
    ``SfP1Transport.traceComposite, ``ordinaryFiniteTwistedPullback,
    ``derivedTensorRight, ``ordinaryFiniteP1SplittingTarget, ``derivedTensorUnit,
    ``ordinaryFinitePushforward, ``ordinaryFinitePullback, ``ordinaryFiniteTensor,
    ``ordinaryFiniteUnit, ``ordinaryFiniteDegreeZero, ``ordinaryFiniteConstant,
    ``ordinaryFiniteSingleFunctor]
  if let some n := e.getAppFn.constName? then
    if names.contains n then
      return ← Lean.Meta.withTransparency .all (Lean.Meta.unfoldDefinition? e)
  if e.getAppFn.isConstOf ``Functor.obj then
    let args := e.getAppArgs
    if args.size ≥ 2 && (args[args.size - 2]!).getAppFn.isConstOf ``Functor.id then
      return some (← Lean.Meta.withTransparency .all (Lean.Meta.whnf e))
  return none

/-- Construct a kernel-checked heterogeneous congruence, handling cached proof arguments
by proof irrelevance instead of unfolding the derived-functor constructions. -/
private meta def traceProofCongruence : Nat → Lean.Expr → Lean.Expr → Lean.MetaM Lean.Expr
  | 0, _, _ => throwError "trace congruence exhausted its structural depth"
  | fuel + 1, lhs, rhs => do
    let lhs := (← Lean.instantiateMVars lhs).consumeMData.headBeta
    let rhs := (← Lean.instantiateMVars rhs).consumeMData.headBeta
    if lhs == rhs then
      return ← Lean.Meta.mkAppM ``HEq.refl #[lhs]
    if let (.const n _, .const m _) := (lhs, rhs) then
      if n == m then return ← Lean.Meta.mkAppM ``HEq.refl #[lhs]
    if lhs.isSort && rhs.isSort && (← Lean.Meta.isDefEq lhs rhs) then
      return ← Lean.Meta.mkAppM ``HEq.refl #[lhs]
    if ← Lean.Meta.isProp (← Lean.Meta.inferType lhs) then
      return ← Lean.Meta.mkAppM ``proof_irrel_heq #[lhs, rhs]
    let aa := lhs.getAppArgs
    let bb := rhs.getAppArgs
    let sameHead := lhs.getAppFn == rhs.getAppFn ||
      (lhs.getAppFn.constName?.isSome && lhs.getAppFn.constName? == rhs.getAppFn.constName?)
    unless sameHead && aa.size == bb.size && aa.size > 0 do
      if let some a ← unfoldInstanceBoundary lhs then
        return ← traceProofCongruence fuel a rhs
      if let some b ← unfoldInstanceBoundary rhs then
        return ← traceProofCongruence fuel lhs b
      if lhs.isProj || rhs.isProj ||
          lhs.getAppFn.isConstOf ``MonoidalCategoryStruct.tensorUnit ||
          rhs.getAppFn.isConstOf ``MonoidalCategoryStruct.tensorUnit then
        if ← Lean.Meta.withTransparency .all (Lean.Meta.isDefEq lhs rhs) then
          return ← Lean.Meta.mkAppM ``HEq.refl #[lhs]
      throwError "non-proof disagreement: {lhs} versus {rhs}\nDETAIL {repr lhs}\n{repr rhs}"
    let ct ← Lean.Meta.mkHCongrWithArity lhs.getAppFn aa.size
    let mut pf := ct.proof
    for i in [:aa.size] do
      let ih ← traceProofCongruence fuel aa[i]! bb[i]!
      let arg ← match ct.argKinds[i]! with
        | .eq => Lean.Meta.mkAppM ``eq_of_heq #[ih]
        | .heq => pure ih
        | _ => throwError "unexpected congruence argument"
      pf := Lean.mkAppN pf #[aa[i]!, bb[i]!, arg]
    if (← Lean.Meta.inferType pf).isEq then
      return ← Lean.Meta.mkAppM ``heq_of_eq #[pf]
    return pf

section ConstantUnitComparison

attribute [local instance] Sheaf.monoidalCategory
private theorem constantSheaf_unit
    {C D : Type*} [Category C] [Category D] [MonoidalCategory D]
    (J : GrothendieckTopology C) [(J.W (A := D)).IsMonoidal] [HasWeakSheafify J D] :
    Functor.Monoidal.εIso (constantSheaf J D) = Iso.refl _ := by
  apply Iso.ext
  change 𝟙 _ ≫ (presheafToSheaf J D).map (𝟙 _) = 𝟙 _
  rw [Category.id_comp]
  exact (presheafToSheaf J D).map_id _

private theorem map_refl_iso
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {U : C} {V : D} (e : U ≅ U) (i : F.obj U ≅ V) (he : e = Iso.refl U) :
    F.mapIso e ≪≫ i = i := by
  rw [he, Functor.mapIso_refl, Iso.refl_trans]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem constantUnit_eq (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u}) :
    SfP1Transport.constantUnit A Y = singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y := by
  unfold SfP1Transport.constantUnit
  apply map_refl_iso
  exact congrArg Iso.symm (constantSheaf_unit Y.smallEtaleTopology (D := ModuleCat A))

end ConstantUnitComparison

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace

attribute [local irreducible] derivedTensor singleFunctorObjUnitIso

set_option linter.auxLemma false in
attribute [local instance 100000]
  presentedFiniteP1Trace._proof_1
  presentedFiniteP1Trace._proof_2
  presentedFiniteP1Trace._proof_4
  presentedFiniteP1Trace._proof_5
  presentedFiniteP1Trace._proof_6
  presentedFiniteP1Trace._proof_7
  presentedFiniteP1Trace._proof_8
  presentedFiniteP1Trace._proof_9
  presentedFiniteP1Trace._proof_10
  presentedFiniteP1Trace._proof_11
  presentedFiniteP1Trace._proof_12
  presentedFiniteP1Trace._proof_13
  presentedFiniteP1Trace._proof_14
  presentedFiniteP1Trace._proof_15
  presentedFiniteP1Trace._proof_16
  presentedFiniteP1Trace._proof_17
  presentedFiniteP1Trace._proof_18
  presentedFiniteP1Trace._proof_19
  presentedFiniteP1Trace._proof_20
  presentedFiniteP1Trace._proof_21
  presentedFiniteP1Trace._proof_22
  presentedFiniteP1Trace._proof_23
  presentedFiniteP1Trace._proof_24
  presentedFiniteP1Trace._proof_25
  presentedFiniteP1Trace._proof_26

set_option allowUnsafeReducibility true in
attribute [local irreducible] rightDerivedLowerShriekOfCompactification

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- A coefficient automorphism identifies the transported kernel trace with the
prescribed presentation trace.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, transport through a presentation.
(auxiliary; not a blueprint node)

Proof: direct image along e is an equivalence. Lift the discrepancy between the
adjunction-unit coefficient identification and the geometric inverse-image comparison
to an automorphism of the shifted line. Naturality of derived direct-image composition
moves this automorphism to the coefficient slot and cancels that discrepancy. The
constant-sheaf unit comparison is the identity before applying the single-complex
functor, so its composite is the canonical single-complex unit comparison. -/
theorem exists_presentedFiniteP1TraceNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    (e : X ≅ ProjectiveLine Y) (w : e.hom ≫ (ProjectiveLine Y ↘ Y) = q)
    (hY : IsUnit (N : Γ(Y, ⊤))) (d : ArbitraryBaseFiniteP1Splitting A N hA t Y hY) :
    ∃ a : (ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧ ≅
        (ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧,
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).map a.hom ≫
          SfP1Transport.trace A N hA t q e w hY d.trace =
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app
          ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) ≫
          presentedFiniteP1Trace A N hA t q e w hY d ≫
          (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom := by
  obtain ⟨a, ha⟩ := exists_presentedFiniteP1RawAdjustment A N hA t q e w hY d
  rw [← SfP1Transport.presentationTrace_assoc A q e w
    ((ordinaryFiniteLine A N hA (ProjectiveLine Y))⟦(2 : ℤ)⟧)
    (d.trace ≫ (SfP1Transport.constantUnit A Y).hom)] at ha
  refine ⟨a, ?_⟩
  conv_rhs =>
    arg 2
    arg 2
    rewrite [← constantUnit_eq]
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let h := (← Lean.Meta.getLocalDeclFromUserName `ha).toExpr
      let lhs ← Lean.Meta.inferType h
      let rhs ← g.getType
      let heq ← traceProofCongruence 150 lhs rhs
      let eq ← Lean.Meta.mkAppM ``eq_of_heq #[heq]
      g.assign (← Lean.Meta.mkAppM ``Eq.mp #[eq, h])
    Lean.Elab.Tactic.replaceMainGoal []

end AlgebraicGeometry.Etale

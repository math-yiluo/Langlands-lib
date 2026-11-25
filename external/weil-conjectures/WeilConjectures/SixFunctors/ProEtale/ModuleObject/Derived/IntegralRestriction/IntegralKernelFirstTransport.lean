/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelUnitCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralNormalizedFamily
/-! # Transport from restricted to ambient first contraction -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
open DiagonalCoefficients
open RationalP1
-- Identify the named and inherited braidings while checking the fixed Tate casts.
attribute [local implicit_reducible] sheafSymmetricCategory sheafBraidedCategory
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  Sheaf.symmetricCategory CategoryTheory.Mod.derivedMonoidalCategory
/-- A comparison cast preserves its underlying isomorphism heterogeneously. -/
private theorem cast_heq_base {α β : Sort u} (h : α = β) (x : α) : HEq (h.mp x) x := by
  cases h
  rfl

/-- The transport calculation over arbitrary coefficients and an ambient object.
Keeping the object ambient avoids comparing restricted-category predicates inside the
normalization witnesses after specialization. -/
private theorem generic_transport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (e e' : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
        (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
          (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (he : e = e')
    (T : IntegralCompactSupport.Ambient Λ Y ⥤
      IntegralCompactSupport.Ambient Λ (ProjectiveLine Y))
    (comparison : T ≅ moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
      RationalP1.twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y)))
    (M : IntegralCompactSupport.Ambient Λ (ProjectiveLine Y))
    (η : M ⟶ T.obj ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M))
    (ε : (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj
      (T.obj ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)) ⟶
        (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)
    (hu : ∃ hb hp,
      HEq (η ≫ comparison.hom.app
          ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M))
        (unitComponent Λ Y L d e M hb hp))
    (hv : ∃ hc, HEq ε
      ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        (comparison.hom.app
          ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)) ≫
      counitComponent Λ Y L d
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M) hc)) :
    ∃ (u : M ⟶
        (RationalP1.twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj
          ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
            ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)))
      (v : (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj
        ((RationalP1.twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj
          ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
            ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M))) ⟶
        (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M),
      UnitComponentNormalized Λ Y L d e' M u ∧
      CounitComponentNormalized Λ Y L d
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M) v ∧
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map η ≫ ε =
        (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map u ≫ v := by
  subst e'
  obtain ⟨hb, hp, hu⟩ := hu
  obtain ⟨hc, hv⟩ := hv
  refine ⟨unitComponent Λ Y L d e M hb hp,
    counitComponent Λ Y L d
      ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M) hc, ?_, ?_, ?_⟩
  · exact ⟨hb, hp, HEq.refl _⟩
  · exact ⟨hc, HEq.refl _⟩
  · let F := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
    have hu' : η ≫ comparison.hom.app (F.obj M) =
        unitComponent Λ Y L d e M hb hp := eq_of_heq hu
    have hv' : ε = F.map (comparison.hom.app (F.obj M)) ≫
        counitComponent Λ Y L d (F.obj M) hc := eq_of_heq hv
    change F.map η ≫ ε = _
    rw [hv', ← Category.assoc, ← Functor.map_comp, hu']

open Lean Meta Elab Tactic
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
-- Kernel conversion checks the fixed integral Tate casts and derived-category aliases.
/--
The normalized restricted components factor through ambient normalized components.
For each restricted object, the unit followed by the canonical ambient comparison and
the counit comparison give ambient maps `u` and `v`; their ambient composite is
exactly the original restricted composite after applying the pushforward.  This is
the formal transport part of the first contraction and is strictly smaller than the
geometric ambient trace/base-change calculation.
Source: `sk-thm-int-restriction-line.proof.md`, paragraph (1), normalization transport.
(blueprint: lem-integral-kernel-first-transport).
-/
theorem integralKernel_first_transport
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [∀ x : ProjectiveLine Y, Invertible (ℓ : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (ℓ : (diagonalSurface Y).residueField x)]
    (hq : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y)
        ((pullTwistShift ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) 1).obj K))
    (hr : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y) K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val)
          (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y)).obj K))
    (family : Family ℓ Y) (_href : IntegralFamilyReference ℓ Y family)
    (a : IntegralUnitCounitType ℓ E Y hq hr)
    (_hnorm : IntegralUnitCounitNormalized ℓ E Y hq hr family a) :
    ∀ M, ∃ (u : M.obj ⟶
        (RationalP1.twist (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y)
          (spIntegralTwist (ProjectiveLine Y) ℓ E)).obj
          ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.val)
            (ProjectiveLine Y ↘ Y)).obj
            ((moduleObjectDerivedPushforward
              (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj M.obj)))
      (v : (moduleObjectDerivedPushforward
          (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj
        ((RationalP1.twist (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y)
          (spIntegralTwist (ProjectiveLine Y) ℓ E)).obj
            ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.val)
              (ProjectiveLine Y ↘ Y)).obj
              ((moduleObjectDerivedPushforward
                (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj M.obj))) ⟶
        (moduleObjectDerivedPushforward
          (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj M.obj),
      RationalP1.UnitComponentNormalized
        (Profinite.padicIntegersRingObj ℓ E.val) Y (fun X ↦ spIntegralTwist X ℓ E)
        (family.integral E)
        (by simpa only [traceTate] using
          (integralShiftedLinePullIso ℓ E (RationalP1.secondProjection Y))) M.obj u ∧
      RationalP1.CounitComponentNormalized
        (Profinite.padicIntegersRingObj ℓ E.val) Y (fun X ↦ spIntegralTwist X ℓ E)
        (family.integral E)
        ((moduleObjectDerivedPushforward
          (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj M.obj) v ∧
      (((restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr).map (a.1.app M)) ≫
        a.2.app ((restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr).obj M)).hom =
      (moduleObjectDerivedPushforward
        (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).map u ≫ v := by
  intro M
  -- Preserve the literal coefficient instances, comparisons and ambient object occurring
  -- in the supplied normalization. This forward application is checked by the kernel.
  run_tac withMainContext do
    let hnorm ← getLocalDeclFromUserName `_hnorm
    let m ← getLocalDeclFromUserName `M
    let hr ← getLocalDeclFromUserName `hr
    let unit ← mkAppM ``And.left #[hnorm.toExpr]
    let unitType ← whnf (← inferType (mkApp unit m.toExpr))
    let .lam _ _ inner _ := unitType.getAppArgs[1]!
      | throwError "expected the base-change witness"
    let .lam _ _ heq _ := inner.getAppArgs[1]!
      | throwError "expected the projection witness"
    let unitFormula := heq.getAppArgs.back!
    let unitArgs := unitFormula.getAppArgs
    let source := unitArgs[6]!
    let goalType ← getMainTarget
    let .lam _ _ vExists _ := goalType.getAppArgs[1]!
      | throwError "expected the ambient unit quantifier"
    let .lam _ _ conjunction _ := vExists.getAppArgs[1]!
      | throwError "expected the ambient counit quantifier"
    let destination := conjunction.getAppArgs[0]!.getAppArgs[6]!
    unless source.isAppOfArity ``Eq.mp 4 && destination.isAppOfArity ``Eq.mp 4 do
      throwError "expected the explicit Tate comparison casts"
    let srcArgs := source.getAppArgs
    let dstArgs := destination.getAppArgs
    -- The two simp-generated casts have the same underlying shifted-line isomorphism.
    let hs ← mkAppM ``cast_heq_base #[srcArgs[2]!, srcArgs[3]!]
    let ht ← mkAppM ``cast_heq_base #[dstArgs[2]!, dstArgs[3]!]
    let ht ← mkAppM ``HEq.symm #[ht]
    let he ← mkAppM ``HEq.trans #[hs, ht]
    let he ← mkAppM ``eq_of_heq #[he]
    let comparisonApp := heq.getAppArgs[1]!.getAppArgs.back!
    let mut comparison := comparisonApp
    for _ in [:5] do
      if comparison.isAppOfArity ``integralAmbientTwistIso 6 then break
      let comparisonArgs := comparison.getAppArgs
      match comparison.getAppFn with
      | .proj _ _ parent => comparison := parent
      | .const name _ =>
        if name == ``NatTrans.app then
          comparison := comparisonArgs[comparisonArgs.size - 2]!
        else if name == ``Iso.hom then
          comparison := comparisonArgs.back!
        else
          throwError "unexpected comparison head: {name}"
      | _ => throwError "expected a comparison projection"
    unless comparison.isAppOfArity ``integralAmbientTwistIso 6 do
      throwError "expected the canonical comparison isomorphism"
    let comparisonType ← inferType comparison
    let comparisonArgs := comparisonType.getAppArgs
    let t := comparisonArgs[comparisonArgs.size - 2]!
    let comparisonInputs := comparison.getAppArgs
    let push ← mkAppM ``restrictedPush
      #[comparisonInputs[0]!, comparisonInputs[2]!, comparisonInputs[5]!, hr.toExpr]
    let image ← mkAppM ``Functor.obj #[push, m.toExpr]
    let counit ← mkAppM ``And.right #[hnorm.toExpr]
    let counitProof := mkApp counit image
    let counitType ← whnf (← inferType counitProof)
    let .lam _ _ counitHEq _ := counitType.getAppArgs[1]!
      | throwError "expected the counit inversion witness"
    let ε := counitHEq.getAppArgs[1]!
    let lhs := heq.getAppArgs[1]!
    let η := lhs.getAppArgs[lhs.getAppArgs.size - 2]!
    let .const _ levels := unitFormula.getAppFn
      | throwError "expected the named ambient unit formula"
    -- Apply the proved ambient calculation to the actual normalized components.
    let proof := mkAppN (mkConst ``generic_transport levels)
      #[unitArgs[0]!, unitArgs[1]!, unitArgs[2]!, unitArgs[3]!, unitArgs[4]!,
        unitArgs[5]!, source, destination, he, t, comparison, unitArgs[7]!, η, ε,
        mkApp unit m.toExpr, counitProof]
    (← getMainGoal).assign proof
    replaceMainGoal []

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction

run_cmd do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env "generic_transport"
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env "integralKernel_first_transport"

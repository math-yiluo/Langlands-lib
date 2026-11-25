/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalDerivedScalarComparisons
import Mathlib.Logic.Function.Basic
import Mathlib.Lean.Meta.CongrTheorems
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperBaseChange
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperExchange
import all WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientExchangeComparison
import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientProjectionComparison
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
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
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Finite proper formulas and comparison tools

The finite proper theorem is expressed for unbundled internal module objects.
Private comparison lemmas retain the canonical exchange and projection maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u u₁ u₂

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CategoryTheory.Limits
open AlgebraicGeometry.ProEtale.QuotientChange

set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  upperStar lowerStar derivedUpperStarLowerStarAdjunction
  leftDerivedUpperStarComp leftDerivedUpperStarTensor derivedTensor
  CategoryTheory.mateEquiv CategoryTheory.Adjunction.rightAdjointProjectionMap

private theorem coefficientPiEq {α β : Sort u₁} {P : α → Sort u₂}
    {Q : β → Sort u₂} (h : α = β) (hPQ : HEq P Q) :
    (∀ x, P x) = (∀ x, Q x) := by
  cases h
  cases hPQ
  rfl

open Lean Meta Elab Tactic in
private meta structure CoefficientCongrState where
  proofs : Array (Expr × Expr × Expr) := #[]
  congrs : Array (Expr × Nat × CongrTheorem) := #[]

open Lean Meta Elab Tactic in
private meta partial def coefficientHEq (lhs rhs : Expr) (fuel : Nat := 160) :
    StateRefT CoefficientCongrState MetaM Expr := do
  if lhs == rhs then return ← mkHEqRefl lhs
  for (a, b, h) in (← get).proofs do
    if a == lhs && b == rhs then return h
  if fuel == 0 then throwError "coefficient congruence exhausted: {lhs}
{rhs}"
  let next := fuel - 1
  let prove : StateRefT CoefficientCongrState MetaM Expr := do
    if (← isProof lhs) && (← isProof rhs) then
      return ← mkAppM ``proof_irrel_heq #[lhs, rhs]
    match lhs, rhs with
    | .lam n α body _, .lam _ β body' _ =>
      let hα ← mkEqOfHEq (← coefficientHEq α β next)
      let init ← get
      let hfun ← withLocalDeclD n α fun x =>
        withLocalDeclD (n.appendAfter "'") β fun y => do
        withLocalDeclD `hxy (← mkHEq x y) fun hxy => do
          modify fun st => {st with proofs := st.proofs.push (x, y, hxy)}
          let h ← coefficientHEq (body.instantiate1 x) (body'.instantiate1 y) next
          mkLambdaFVars #[x, y, hxy] h
      let congrs := (← get).congrs
      set { init with congrs := congrs }
      let ty ← whnf (← inferType lhs)
      let ty' ← whnf (← inferType rhs)
      let P := mkLambda n .default α ty.bindingBody!
      let Q := mkLambda n .default β ty'.bindingBody!
      return ← mkAppOptM ``Function.hfunext #[some α, some β, some P, some Q,
        some lhs, some rhs, some hα, some hfun]
    | .forallE n α body _, .forallE _ β body' _ =>
      let hα ← mkEqOfHEq (← coefficientHEq α β next)
      let P := mkLambda n .default α body
      let Q := mkLambda n .default β body'
      let hPQ ← coefficientHEq P Q next
      let h ← mkAppOptM ``coefficientPiEq #[some α, some β, some P, some Q,
        some hα, some hPQ]
      return ← mkHEqOfEq h
    | _, _ => pure ()
    let expandProjection (e : Expr) : MetaM Expr := do
      let .proj typeName index major := e.getAppFn | return e
      let info := Lean.getStructureInfo (← getEnv) typeName
      let p ← mkProjection major info.fieldNames[index]!
      return mkAppN p e.getAppArgs
    let lhs' ← expandProjection lhs
    let rhs' ← expandProjection rhs
    if lhs' != lhs || rhs' != rhs then
      return ← coefficientHEq lhs' rhs' next
    let f := lhs.getAppFn
    let g := rhs.getAppFn
    let xs := lhs.getAppArgs
    let ys := rhs.getAppArgs
    if f == g && xs.size == ys.size && !xs.isEmpty then
      let mut found := none
      for (ff, arity, thm) in (← get).congrs do
        if ff == f && arity == xs.size then found := some thm
      let thm? ← match found with
        | some thm => pure (some thm)
        | none => do
          let thm? ← if let .const name levels := f then
            mkHCongrWithArityForConst? name levels xs.size
          else
            try pure (some (← mkHCongrWithArity f xs.size))
            catch _ => pure none
          if let some thm := thm? then
            modify fun st => {st with congrs := st.congrs.push (f, xs.size, thm)}
          pure thm?
      if let some thm := thm? then
        let mut args := #[]
        for i in [:xs.size] do
          let h ← coefficientHEq xs[i]! ys[i]! next
          let h ← if thm.argKinds[i]! == .eq then mkEqOfHEq h else pure h
          args := args ++ #[xs[i]!, ys[i]!, h]
        let h := mkAppN thm.proof args
        let ty ← inferType h
        if ty.isHEq then return h else return ← mkHEqOfEq h
      else
        let ty ← whnf (← inferType lhs)
        let ty' ← whnf (← inferType rhs)
        if ty.isForall && ty'.isForall then
          let lhs' := mkLambda ty.bindingName! .default ty.bindingDomain!
            (mkApp (lhs.liftLooseBVars 0 1) (.bvar 0))
          let rhs' := mkLambda ty'.bindingName! .default ty'.bindingDomain!
            (mkApp (rhs.liftLooseBVars 0 1) (.bvar 0))
          return ← coefficientHEq lhs' rhs' next
    let lhs' ← whnf lhs
    let rhs' ← whnf rhs
    if lhs' != lhs || rhs' != rhs then
      return ← coefficientHEq lhs' rhs' next
    let lhs' := (← unfoldDefinition? lhs).getD lhs
    let rhs' := (← unfoldDefinition? rhs).getD rhs
    if lhs' != lhs || rhs' != rhs then
      return ← coefficientHEq lhs' rhs' next
    throwError "coefficient congruence stuck:
{lhs}
{rhs}"
  let h ← prove
  modify fun st => {st with proofs := st.proofs.push (lhs, rhs, h)}
  return h

open Lean Meta Elab Tactic in
private meta def coefficientCongrGoal : TacticM Unit := do
  liftMetaTactic fun goal => goal.withContext do
    let ty ← goal.getType
    let some (_, lhs, rhs) := ty.eq? | throwError "expected equality"
    let (h, _) ← (coefficientHEq lhs rhs).run {}
    goal.assign (← mkEqOfHEq h)
    return []

section Helpers

attribute [local semireducible] L F adj IntegralQuotient.actualProjection
  IntegralQuotient.actualTensorPull

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

attribute [local instance] finiteProperCache1 finiteProperCache2 finiteProperCache3
  finiteProperCache4 finiteProperCache5 finiteProperCache6 finiteProperCache7
  finiteProperCache8 finiteProperCache9 finiteProperCache10 finiteProperCache11
  finiteProperCache12

private instance sectionDerived
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T) :=
  @HasDerivedCategory.ofIsGrothendieckAbelian _ _ _
    (SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
      (Scheme.ProEt.topology T) _)

private noncomputable instance modulesClosed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :
    MonoidalClosed (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T)) := by
  have h : IsCommMonObj (condensedRingObj Λ T) := isCommMonObj_condensedRingObj Λ T
  exact @Mod.monoidalClosed _ _ _ _ _ _ _ _ _ h

private noncomputable instance modulesSymmetric
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :
    SymmetricCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T)) := by
  have h : IsCommMonObj (condensedRingObj Λ T) := isCommMonObj_condensedRingObj Λ T
  exact @Mod.symmetricCategory _ _ _ _ _ _ _ _ _ h

private instance modulesFlat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) := by
  have h : IsCommMonObj (condensedRingObj Λ T) := isCommMonObj_condensedRingObj Λ T
  exact @Mod.hasFunctorialFlatResolution _ _ _ _ _ _ _ _ _ h inferInstance

private theorem finite_ambient_iso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' p' p g)
    (K : DerivedCategory (Modules R X)) :
    IsIso ((finiteProperExchange R sq.toCommSq).app K) ↔
      IsIso ((condensedAmbientExchange R sq).app K) := by
  have hs : finitePullbackSquare R sq.toCommSq =
      condensedAmbientPullbackComparison R sq :=
    congrArg (fun i ↦ (leftDerivedUpperStarComp R p' g).symm ≪≫ i ≪≫
      leftDerivedUpperStarComp R g' p)
      (finitePullbackCongr_eqToIso R sq.toCommSq.w.symm)
  have he : finiteProperExchange R sq.toCommSq = condensedAmbientExchange R sq :=
    congrArg (fun (i : (upperStar R g).leftDerivedFunctor ⋙
        (upperStar R p').leftDerivedFunctor ≅ (upperStar R p).leftDerivedFunctor ⋙
        (upperStar R g').leftDerivedFunctor) ↦ (mateEquiv
      (G := (upperStar R g).leftDerivedFunctor)
      (H := (upperStar R g').leftDerivedFunctor)
      (derivedUpperStarLowerStarAdjunction R p)
      (derivedUpperStarLowerStarAdjunction R p')
      (TwoSquare.mk _ _ _ _ i.hom))) hs
  exact iff_of_eq (congrArg IsIso (congrArg (fun t ↦ t.app K) he))

-- Bundle the inputs for the proved finite coefficient theorem.
private theorem finite_formulas
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    (e : Mon.mk R ≅ Mon.mk (FiniteDiscreteOrdinary.coefficient A))
    (l : ℕ) [Fact l.Prime] (hA : ∃ r : ℕ, (l ^ r : ℕ) • (1 : A) = 0)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] :
    (∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (p' : X' ⟶ Y') (g' : X' ⟶ X)
      (sq : ChosenCartesianSquare g' p' p g) (K : DerivedCategory (Modules R X)),
      (constantModelBoundedConstructible R X ⊓ _root_.DerivedCategory.finiteTorAmplitude _) K →
      IsIso ((condensedAmbientExchange R sq).app K)) ∧
    (∀ (K : DerivedCategory (Modules R X)) (M : DerivedCategory (Modules R Y)),
      (constantModelBoundedConstructible R X ⊓ _root_.DerivedCategory.finiteTorAmplitude _) K →
      (constantModelBoundedConstructible R Y ⊓ _root_.DerivedCategory.finiteTorAmplitude _) M →
      IsIso (moduleObjectProjectionMap R p K M)) := by
  classical
  let Xo := Over.mk (X ↘ Spec (.of k))
  let Yo := Over.mk (Y ↘ Spec (.of k))
  let pp : Xo ⟶ Yo := Over.homMk p ((Scheme.Hom.isOver_iff (Spec (.of k))).mp inferInstance)
  let : LocallyOfFiniteType Xo.hom := ‹LocallyOfFiniteType (X ↘ Spec (.of k))›
  let : QuasiCompact Xo.hom := ‹QuasiCompact (X ↘ Spec (.of k))›
  let : IsSeparated Xo.hom := ‹IsSeparated (X ↘ Spec (.of k))›
  let : LocallyOfFiniteType Yo.hom := ‹LocallyOfFiniteType (Y ↘ Spec (.of k))›
  let : QuasiCompact Yo.hom := ‹QuasiCompact (Y ↘ Spec (.of k))›
  let : IsSeparated Yo.hom := ‹IsSeparated (Y ↘ Spec (.of k))›
  let : IsProper pp.left := ‹IsProper p›
  let enc := fun T : Scheme.{u} ↦ (FiniteDiscreteOrdinary.encoding_exists A T).some
  have h := finiteProperBaseChange_of_coefficientIso R A e enc l hA k Xo Yo pp
  constructor
  · intro X' Y' g p' g' sq K hK
    have hf := h.2.1 X' Y' g p' g' sq ⟨K, hK⟩
    have hs : IsIso ((finiteProperExchange R sq.toCommSq).app K) := by
      refine Eq.mp ?_ hf
      run_tac coefficientCongrGoal
    exact (finite_ambient_iso R sq K).1 hs
  · intro K M hK hM
    have hf := h.2.2 ⟨K, hK⟩ ⟨M, hM⟩
    refine Eq.mp ?_ hf
    run_tac coefficientCongrGoal

private theorem quotient_ambient_eq
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' p' p g)
    : IntegralQuotient.ambient R sq = condensedAmbientExchange R sq := by
  have hc {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W) :
      scalarPullbackComposition R a b = leftDerivedUpperStarComp R a b := by
    unfold scalarPullbackComposition L moduleObjectDerivedPullback
    rfl
  have hs : scalarPullbackSquare R sq = condensedAmbientPullbackComparison R sq := by
    unfold scalarPullbackSquare condensedAmbientPullbackComparison
    exact congrArg₂ (fun i j ↦ i.symm ≪≫
      eqToIso (congrArg (fun h : X' ⟶ Y ↦ L R h) sq.toCommSq.w.symm) ≪≫ j)
      (hc p' g) (hc g' p)
  have ha {U V : Scheme.{u}} (a : U ⟶ V) :
      adj R a = derivedUpperStarLowerStarAdjunction R a := by
    unfold adj
    rfl
  have he : IntegralQuotient.ambient R sq = condensedAmbientExchange R sq := by
    unfold IntegralQuotient.ambient condensedAmbientExchange
    exact congrArg₂ (fun a b ↦ (mateEquiv a b
      (TwoSquare.mk _ _ _ _ (scalarPullbackSquare R sq).hom)))
      (ha p) (ha p') |>.trans
        (congrArg (fun (i : (upperStar R g).leftDerivedFunctor ⋙
            (upperStar R p').leftDerivedFunctor ≅ (upperStar R p).leftDerivedFunctor ⋙
            (upperStar R g').leftDerivedFunctor) ↦ (mateEquiv
          (derivedUpperStarLowerStarAdjunction R p)
          (derivedUpperStarLowerStarAdjunction R p')
          (TwoSquare.mk _ _ _ _ i.hom))) hs)
  exact he

private theorem quotient_projection_eq
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : DerivedCategory (Modules R X)) (M : DerivedCategory (Modules R Y)) :
    ((IntegralQuotient.actualProjection R p).app K).app M =
      moduleObjectProjectionMap R p K M := by
  unfold IntegralQuotient.actualProjection IntegralQuotient.actualTensorPull
  unfold adj L F moduleObjectDerivedPullback moduleObjectDerivedPushforward
  unfold moduleObjectProjectionMap moduleObjectProjectionData
  rfl

private theorem generic_projection_iso
    (R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (c : D a Y ⋙ L S p ≅ L R p ⋙ D a X)
    (bX : (Functor.postcompose₂.obj (D a X)).obj (derivedTensor R X) ≅
      (((Functor.whiskeringLeft₂ _).obj (D a X)).obj (D a X)).obj (derivedTensor S X))
    (bY : (Functor.postcompose₂.obj (D a Y)).obj (derivedTensor R Y) ≅
      (((Functor.whiskeringLeft₂ _).obj (D a Y)).obj (D a Y)).obj (derivedTensor S Y))
    (K : DerivedCategory (Modules R X)) (M : DerivedCategory (Modules R Y))
    (hEq : IntegralQuotient.ProjectionComparisonEquation a p c bX bY K M)
    [IsIso (rho a p c)]
    (hFinite : IsIso (((IntegralQuotient.actualProjection S p).app ((D a X).obj K)).app
      ((D a Y).obj M))) :
    IsIso ((D a Y).map (((IntegralQuotient.actualProjection R p).app K).app M)) := by
  let := hFinite
  unfold IntegralQuotient.ProjectionComparisonEquation at hEq
  let out := (F S p).map
    ((bX.hom.app K).app ((L R p).obj M) ≫
      ((derivedTensor S X).obj ((D a X).obj K)).map (c.inv.app M))
  have hiso : IsIso ((D a Y).map
      (((IntegralQuotient.actualProjection R p).app K).app M) ≫
      (rho a p c).app (((derivedTensor R X).obj K).obj ((L R p).obj M)) ≫ out) :=
    (congrArg IsIso hEq).mp (by infer_instance)
  have : IsIso out := by dsimp only [out]; infer_instance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _
    ((D a Y).map (((IntegralQuotient.actualProjection R p).app K).app M))
    ((rho a p c).app (((derivedTensor R X).obj K).obj ((L R p).obj M)) ≫ out)
    (by infer_instance) hiso

private theorem generic_exchange_iso
    (R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    (b : ∀ {U V : Scheme.{u}} (u : U ⟶ V), D a V ⋙ L S u ≅ L R u ⋙ D a U)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' p' p g)
    (K : DerivedCategory (Modules R X))
    (hEq : Functor.whiskerRight (rho a p (b p)) (L S g) ≫
        Functor.whiskerLeft (D a X) (IntegralQuotient.ambient S sq) ≫
        Functor.whiskerRight (b g').hom (F S p') =
      Functor.whiskerLeft (F R p) (b g).hom ≫
        Functor.whiskerRight (IntegralQuotient.ambient R sq) (D a Y') ≫
        Functor.whiskerLeft (L R g') (rho a p' (b p')))
    (hIso : IsIso (rho a p (b p))) (hIso' : IsIso (rho a p' (b p')))
    (hFinite : IsIso ((IntegralQuotient.ambient S sq).app ((D a X).obj K))) :
    IsIso ((D a Y').map ((IntegralQuotient.ambient R sq).app K)) := by
  let := hIso
  let := hIso'
  let := hFinite
  have eq := congrArg (fun t ↦ t.app K) hEq
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at eq
  have hiso : IsIso ((b g).hom.app ((F R p).obj K) ≫
      (D a Y').map ((IntegralQuotient.ambient R sq).app K) ≫
      (rho a p' (b p')).app ((L R g').obj K)) :=
    (congrArg IsIso eq).mp (by infer_instance)
  have := IsIso.of_isIso_comp_left ((b g).hom.app ((F R p).obj K))
    ((D a Y').map ((IntegralQuotient.ambient R sq).app K) ≫
      (rho a p' (b p')).app ((L R g').obj K))
  exact IsIso.of_isIso_comp_right
    ((D a Y').map ((IntegralQuotient.ambient R sq).app K))
    ((rho a p' (b p')).app ((L R g').obj K))

private theorem generic_condensed_exchange_iso
    (R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    (b : ∀ {U V : Scheme.{u}} (u : U ⟶ V), D a V ⋙ L S u ≅ L R u ⋙ D a U)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' p' p g)
    (K : DerivedCategory (Modules R X))
    (hEq : Functor.whiskerRight (rho a p (b p)) (L S g) ≫
        Functor.whiskerLeft (D a X) (IntegralQuotient.ambient S sq) ≫
        Functor.whiskerRight (b g').hom (F S p') =
      Functor.whiskerLeft (F R p) (b g).hom ≫
        Functor.whiskerRight (IntegralQuotient.ambient R sq) (D a Y') ≫
        Functor.whiskerLeft (L R g') (rho a p' (b p')))
    (hIso : IsIso (rho a p (b p))) (hIso' : IsIso (rho a p' (b p')))
    (hFinite : IsIso ((condensedAmbientExchange S sq).app ((D a X).obj K))) :
    IsIso ((D a Y').map ((condensedAmbientExchange R sq).app K)) := by
  have hfi : IsIso ((IntegralQuotient.ambient S sq).app ((D a X).obj K)) :=
    (congrArg IsIso (congrArg (fun t ↦ t.app ((D a X).obj K))
      (quotient_ambient_eq S sq))).mpr hFinite
  have hint := generic_exchange_iso R S a b sq K hEq hIso hIso' hfi
  exact (congrArg IsIso (congrArg (fun t ↦ (D a Y').map (t.app K))
    (quotient_ambient_eq R sq))).mp hint

end Helpers

/-- The finite proper exchange and projection formulas for unbundled complexes,
with a specified finite continuous coefficient presentation.
Source: the finite proper theorem, blueprint proper-base-change proof, paragraph (3).
(blueprint: lem-sfb-finite-coefficient-proper-formulas).

Proof: bundle the two schemes and their morphism over Spec k, use the normalized
finite encoding, and apply the finite coefficient-isomorphism theorem. Bundle each
Dctf input without changing its object. Identify the canonical finite pullback square
with the specified ambient pullback square and retain the canonical projection map. -/
theorem finiteCoefficientProperFormulas
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    (e : Mon.mk R ≅ Mon.mk (FiniteDiscreteOrdinary.coefficient A))
    (l : ℕ) [Fact l.Prime] (hA : ∃ r : ℕ, (l ^ r : ℕ) • (1 : A) = 0)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] :
    (∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (p' : X' ⟶ Y') (g' : X' ⟶ X)
      (sq : ChosenCartesianSquare g' p' p g) (K : DerivedCategory (Modules R X)),
      (constantModelBoundedConstructible R X ⊓ _root_.DerivedCategory.finiteTorAmplitude _) K →
      IsIso ((condensedAmbientExchange R sq).app K)) ∧
    (∀ (K : DerivedCategory (Modules R X)) (M : DerivedCategory (Modules R Y)),
      (constantModelBoundedConstructible R X ⊓ _root_.DerivedCategory.finiteTorAmplitude _) K →
      (constantModelBoundedConstructible R Y ⊓ _root_.DerivedCategory.finiteTorAmplitude _) M →
      IsIso (moduleObjectProjectionMap R p K M)) := by
  have hf := finite_formulas R A e l hA k p
  refine Eq.mp ?_ hf
  run_tac coefficientCongrGoal

end AlgebraicGeometry.ProEtale.CondensedRing

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.PointExchangeOnSeparatedBdc

/-!

# The ambient identity of the exchange `ν_X` of a separated `X` on pushforwards

For `ν_X = pointCompactSupportExchangeOfSeparated` the ambient hypothesis `hC` of
`pointCompactSupportExchangeOfSeparated_app_lowerStar` (`PointExchangeOnSeparatedBdc`) is proved
(`pointCompactSupportExchangeOfSeparated_app_lowerStar_ambient`), which gives the identities
without hypothesis `pointCompactSupportExchangeOfSeparated_app_lowerStar_eq` and
`pointCompactSupportExchangeOfSeparated_app_lowerStar_component_eq`.

## Implementation notes

`hC` is an instance of `NearbyCyclesModel.Hom.pointExchange_comp_app_of_eq`. The kernel compares
two terms by unfolding as soon as a projection (`Quiver.Hom`, `Prefunctor.obj`,
`CategoryStruct.comp`, …, reducibility hint `abbrev`) is applied to arguments which are not
syntactically equal, and then runs out of memory on the derived categories. So the instance of the
lemma has to agree *syntactically* with the type of `hC`:

* the type of `hC` contains several terms of `MonObj (Profinite.padicAlgClRingObj ℓ)`
  (`Sheaf.monObj_sheafCompose_obj`), differing only in their `Precoherent Profinite` proofs
  (`ProEtale.pointLowerStar._proof_1`, `Profinite.padicIntegersRingObj._proof_1` and the
  synthesized instance), while a lemma generic in `[MonObj Λ]` produces a single one. The proof of
  `pointCompactSupportExchangeOfSeparated_app_lowerStar_ambient` first replaces, inside these
  instance terms, every such proof by a single one, by `Eq.mp` along a motive abstracting the
  proof (the kernel checks the motive by proof irrelevance and its instance at the original proof
  is syntactically the goal);
* `pointModelHom` is stated with `pointSpecialMap`, so that the morphism of special fibres has the
  same form everywhere (and not also `deformationSpecialFibreMap …`);
* `NearbyCyclesModel.Hom.pointExchange_comp_app_of_eq` takes the composite morphism of models
  (`pointCompModelHom`) and the second copy of the adjunction of `h'` (`openImmersionAdjunction`)
  as arguments, equal to the expected ones by hypotheses closed by `rfl` in isolation, and writes
  the source of the component of `closedExtension` at `𝟙 Y` as `R(gu)_*` (not `R(gu)_* ⋙ 𝟭`).

The statements of this chain of identities are large, and writing the `.olean` of a module runs
Lean's library-suggestion extensions (`symbolFrequency`, `sineQuaNon`) over the statement of every
theorem, which takes tens of seconds per statement here. This is why the chain is split into
`PointExchangeOnComponentBdcOfEq`, `PointExchangeOnSeparatedBdc` and this file.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Separated

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

variable (x : RationalPoint X) (k' : Type u) [Field k'] [Algebra k k'] {ℓ : ℕ} [Fact ℓ.Prime]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] {B : Over (Spec (.of k))} [LocallyOfFiniteType B.hom]
  [QuasiCompact B.hom] [IsSeparated B.hom]

/-- The hypothesis `α` of a proof of `∀ a : α, β a`. -/
abbrev HypothesisOf {α : Prop} {β : α → Prop} (_ : ∀ a, β a) : Prop := α

/-- **The ambient identity `hC` of `pointCompactSupportExchangeOfSeparated_app_lowerStar`**: an
instance of `NearbyCyclesModel.Hom.pointExchange_comp_app_of_eq`, once the `Precoherent Profinite`
proofs in the `MonObj` instances of `ℚ̄_ℓ` are identified (see the implementation notes). -/
theorem pointCompactSupportExchangeOfSeparated_app_lowerStar_ambient {B' : Scheme.{u}}
    {MB : NearbyCyclesModel B.left B'} {g : B ⟶ X}
    {g' : B' ⟶ (deformationSpecialFibre X x.left.ker k').left}
    (φg : MB.Hom (deformationModel X x.left.ker k') g.left g')
    (N : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    HypothesisOf (pointCompactSupportExchangeOfSeparated_app_lowerStar x k' φg N) := by
  -- Replace, inside the `MonObj` instances `Sheaf.monObj_sheafCompose_obj`, every `Precoherent`
  -- proof by the one of the coherent topology of the first instance, by casts along motives.
  run_tac do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let target ← Lean.Meta.whnfR (← Lean.instantiateMVars (← goal.getType))
    let isInst (e : Lean.Expr) : Bool := e.isAppOf ``Sheaf.monObj_sheafCompose_obj
    let isProof (e : Lean.Expr) : Lean.MetaM Bool := do
      let some c := e.getAppFn.constName? | return false
      unless (← Lean.getConstInfo c).type.getForallBody.isAppOf ``Precoherent do return false
      return (← Lean.Meta.inferType e).isAppOf ``Precoherent
    let proofs ← IO.mkRef (#[] : Array Lean.Expr)
    Lean.Meta.forEachExpr target fun e ↦ do
      if isInst e then
        Lean.Meta.forEachExpr e fun e' ↦ do
          if ← isProof e' then
            unless (← proofs.get).contains e' do proofs.modify (·.push e')
    let some J := target.find? fun e ↦ isInst e | throwError "no `MonObj` instance found"
    let some hStd := (J.find? (·.isAppOfArity ``coherentTopology 3)).map (·.appArg!)
      | throwError "no coherent topology found"
    let hType ← Lean.Meta.inferType hStd
    let mut goal ← goal.replaceTargetDefEq target
    let mut target := target
    for p in ← proofs.get do
      if p != hStd then
        let motive ← Lean.Meta.withLocalDeclD `h hType fun h ↦ do
          Lean.Meta.mkLambdaFVars #[h] <| target.replace fun e ↦ if isInst e then
            some (e.replace fun e' ↦ if e' == p then some h else none) else none
        let eq ← Lean.Meta.mkAppM ``Subsingleton.elim #[hStd, p]
        let propEq ← Lean.Meta.mkAppM ``congrArg #[motive, eq]
        target := motive.beta #[hStd]
        let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar target
        goal.assign (Lean.mkAppN (Lean.mkConst ``Eq.mp [.zero])
          #[Lean.mkApp motive hStd, Lean.mkApp motive p, propEq, next])
        goal := next.mvarId!
    Lean.Elab.Tactic.replaceMainGoal [goal]
  apply NearbyCyclesModel.Hom.pointExchange_comp_app_of_eq
  all_goals rfl

/-- **The exchange `ν_X` of a separated `X` on pushforwards from `B`**, without hypothesis:
`pointCompactSupportExchangeOfSeparated_app_lowerStar` for its ambient identity
`pointCompactSupportExchangeOfSeparated_app_lowerStar_ambient`. -/
theorem pointCompactSupportExchangeOfSeparated_app_lowerStar_eq {B' : Scheme.{u}}
    {MB : NearbyCyclesModel B.left B'} {g : B ⟶ X}
    {g' : B' ⟶ (deformationSpecialFibre X x.left.ker k').left}
    (φg : MB.Hom (deformationModel X x.left.ker k') g.left g')
    (N : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    type_of% (pointCompactSupportExchangeOfSeparated_app_lowerStar x k' φg N
      (pointCompactSupportExchangeOfSeparated_app_lowerStar_ambient x k' φg N)) :=
  pointCompactSupportExchangeOfSeparated_app_lowerStar x k' φg N
    (pointCompactSupportExchangeOfSeparated_app_lowerStar_ambient x k' φg N)

/-- **The exchange `ν_X` of a separated `X` on pushforwards from a thickened point `B`**
(`b ≫ g = x`), without hypothesis: `pointCompactSupportExchangeOfSeparated_app_lowerStar_eq` for
`pointComponentModelHom`. -/
theorem pointCompactSupportExchangeOfSeparated_app_lowerStar_component_eq {b : RationalPoint B}
    (g : B ⟶ X) (hbg : b ≫ g = x) (N : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    type_of% (pointCompactSupportExchangeOfSeparated_app_lowerStar_component x k' g hbg N
      (pointCompactSupportExchangeOfSeparated_app_lowerStar_ambient x k' _ N)) :=
  pointCompactSupportExchangeOfSeparated_app_lowerStar_eq x k' _ N

end Separated

end AlgebraicGeometry.ProEtale.CondensedRing

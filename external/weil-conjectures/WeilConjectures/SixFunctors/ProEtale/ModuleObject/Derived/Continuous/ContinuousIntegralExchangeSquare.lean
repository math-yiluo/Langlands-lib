/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralComparisons
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteDiscreteRingObj.FiniteDiscreteCoefficientBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralExchangeEquality
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralPushComparison

/-! # Scalar localization comparison for the specified proper exchange -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

/-- Close the main goal by the local hypothesis `name`, whose type is definitionally equal to the
goal. Here the hypotheses come from the general-`E` lemmas, whose coefficient ring
`C(-, ↥E)` carries the metric topology of the normed field `↥E`, while the goal is stated
through the per-ring operations, with the subspace topology of `↥E ⊆ ℚ̄_ℓ`. The two agree
definitionally, but elaborator unification reaches them only after unfolding the derived
functors (over 100 s). The proof term is `id (α := goal) h`; Lean's kernel checks it. -/
private meta def exactLocalByKernel (name : Lean.Name) : Lean.Elab.Tactic.TacticM Unit := do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    let h := (← Lean.Meta.getLocalDeclFromUserName name).toExpr
    goal.assign (← Lean.Meta.mkExpectedTypeHint h (← goal.getType))
  Lean.Elab.Tactic.replaceMainGoal []

/-- The proposition of `continuousIntegral_exchange_square`, named so that the theorem's
elaborated type stays small (the inline statement is very large once elaborated, and the
export-time walk over public theorem types made the module far too slow). -/
abbrev continuousIntegralExchangeSquareStatement
    (sq : IsPullback g' f' f g) (M : integralConstructible ℓ E X)
    (hM : ProEtale.boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) X)
        ((integralScalarExtension ℓ E X).obj M.obj)) : Prop :=
    let N : ProEtale.BoundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) X) :=
      ⟨(integralScalarExtension ℓ E X).obj M.obj, hM⟩
    ∃ (s : (integralScalarExtension ℓ E Y').obj
          (((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
              (f.asOver (Spec (.of k))) ⋙
            boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ
              (g.asOver (Spec (.of k)))).obj M).obj) ≅
        ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E (f.asOver (Spec (.of k))) ⋙
          boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
            (g.asOver (Spec (.of k)))).obj N).obj)
      (t : (integralScalarExtension ℓ E Y').obj
          (((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g'.asOver (Spec (.of k))) ⋙
            UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
              (f'.asOver (Spec (.of k)))).obj M).obj) ≅
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
            (g'.asOver (Spec (.of k))) ⋙
          ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E
            (f'.asOver (Spec (.of k)))).obj N).obj),
      s.hom ≫ ((ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E
          (sq.toCommSq.asOver (Spec (.of k)))).app N).hom =
        (integralScalarExtension ℓ E Y').map
          ((UnitBallRingObj.boundedConstructibleBaseChange ℓ (continuousIntegers ℓ E)
            (sq.toCommSq.asOver (Spec (.of k)))).app M).hom ≫
            t.hom

/-- Source and target comparisons identify the specified integral and E exchange maps.
Source: Bhatt--Scholze, Lemma 6.8.2 and Remark 6.8.15; scalar localization and
unit-square-counit compatibility in the condensed realization argument.
(blueprint: lem-weil-pbc-continuous-integral-exchange-square).

Proof in words. On compact profinite tests, continuousIntegralFunctions_isLocalization
identifies the coefficient map with inversion of ℓ. Exact inverse image from the point
preserves this localization. Thus scalar extension is exact and commutes with pullback.
For proper f and its base change f', ordinary derived pushforward commutes with the
localization telescope on bounded-below objects: apply qcqs pushforward continuity to
uniformly bounded-below representatives, all with the same lower bound. Compose the
pullback comparison with the pullback of the pushforward comparison to obtain s.
Compose the pushforward comparison with the pushforward of the pullback comparison
to obtain t. Both are invertible by the same continuity result. These comparisons are
mates of restriction-of-scalars comparisons. Hence they preserve units and counits,
and their pullback comparisons preserve coherent composition. Expanding the specified
exchange as unit insertion, square transport and counit contraction gives exactly the
displayed commuting square. Restriction along fully faithful constructible inclusions
preserves these identities. No invertibility of exchange itself enters this argument. -/
theorem continuousIntegral_exchange_square [IsProper f]
    (sq : IsPullback g' f' f g) (M : integralConstructible ℓ E X)
    (hM : ProEtale.boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) X)
        ((integralScalarExtension ℓ E X).obj M.obj)) :
    continuousIntegralExchangeSquareStatement ℓ E k sq M hM := by
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) sq inferInstance
  have hf : IsIso (integralConstructiblePushHom ℓ E k f M) := by
    have h := integralScalarPushHom_isIso ℓ E f M
    refine (ObjectProperty.isIso_hom_iff _).1 ?_
    run_tac exactLocalByKernel `h
  have hf' : IsIso (integralConstructiblePushHom ℓ E k f'
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ
        (g'.asOver (Spec (.of k)))).obj M)) := by
    have h := integralScalarPushHom_isIso ℓ E f'
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g'.asOver (Spec (.of k)))).obj M)
    refine (ObjectProperty.isIso_hom_iff _).1 ?_
    run_tac exactLocalByKernel `h
  have : IsIso (integralConstructibleSourceHom ℓ E k f g M) :=
    IsIso.comp_isIso' (Iso.isIso_hom _) (Functor.map_isIso _ _)
  have : IsIso (integralConstructibleTargetHom ℓ E k f' g' M) :=
    IsIso.comp_isIso' hf' (Functor.map_isIso _ (integralConstructiblePullIso ℓ E k g' M).hom)
  let ι := (ProEtale.boundedConstructible
    (condensedRingObj (Profinite.continuousMapRingObj E) Y')).ι
  refine ⟨ι.mapIso (asIso (integralConstructibleSourceHom ℓ E k f g M)),
    ι.mapIso (asIso (integralConstructibleTargetHom ℓ E k f' g' M)), ?_⟩
  have h := congrArg (fun a ↦ a.hom)
    (integralConstructible_exchange_equality ℓ E k f g f' g' sq.toCommSq M)
  run_tac exactLocalByKernel `h

end AlgebraicGeometry.ProEtale.CondensedRing

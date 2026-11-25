/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteRealizationPredicate

/-! # Existence for the existing compact-support realization predicate

Project the integral-functor conjunct of the existing representative comparison.
(blueprint: lem-weil-compact-support-finite-realization-exists).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

section FiniteAction
variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- The integral realization package with its exact recorded predicate.
Source: blueprint order 1494, proof steps 1--4
(blueprint: lem-weil-compact-support-finite-realization-exists).
Proof: project the integral-functor conjunct after the specified tower, evaluation,
right-derived limit, unit and Roos projections in
exists_compactSupportRepresentativeComparison. Unfold the named predicate; it is
exactly the predicate in that conjunct, with no added choice or normalization. -/
theorem sfCompactSupportFiniteRealization (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    ∃ F, SfCompactSupportFiniteRealizationSpec l K₀ hl c E F := by
    run_tac Lean.Elab.Tactic.withMainContext do
      let l ← Lean.Elab.Term.elabTerm (Lean.mkIdent `l) none
      let E ← Lean.Elab.Term.elabTerm (Lean.mkIdent `E) none
      let K₀ ← Lean.Elab.Term.elabTerm (Lean.mkIdent `K₀) none
      let hl ← Lean.Elab.Term.elabTerm (Lean.mkIdent `hl) none
      let X ← Lean.Elab.Term.elabTerm (Lean.mkIdent `X) none
      let Y ← Lean.Elab.Term.elabTerm (Lean.mkIdent `Y) none
      let f ← Lean.Elab.Term.elabTerm (Lean.mkIdent `f) none
      let c ← Lean.Elab.Term.elabTerm (Lean.mkIdent `c) none
      let h ← Lean.Meta.mkAppM ``exists_compactSupportRepresentativeComparison
        #[l, E, K₀, hl, X, Y, f, c]
      let mut h := h
      let mut ty ← Lean.Meta.inferType h
      for kind in [true, true, false, false, true, true, false, false, true, false] do
        ty ← Lean.Meta.whnf ty
        let args := ty.getAppArgs
        if kind then
          unless ty.isAppOfArity ``Exists 2 do
            throwError "expected existential"
          let levels := [← Lean.Meta.getLevel args[0]!]
          let witness := Lean.mkAppN (Lean.mkConst ``Exists.choose levels) #[args[0]!, args[1]!, h]
          h := Lean.mkAppN (Lean.mkConst ``Exists.choose_spec levels) #[args[0]!, args[1]!, h]
          ty := args[1]!.beta #[witness]
        else
          unless ty.isAppOfArity ``And 2 do
            throwError "expected conjunction"
          h := Lean.mkAppN (Lean.mkConst ``And.right) #[args[0]!, args[1]!, h]
          ty := args[1]!
      ty ← Lean.Meta.whnf ty
      unless ty.isAppOfArity ``Exists 2 do
        throwError "expected existential, got {ty}"
      (← Lean.Elab.Tactic.getMainGoal).assign h

end FiniteAction
end WeilConjectures

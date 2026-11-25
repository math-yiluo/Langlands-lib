/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralSystemScalarCoreData
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralSystemSelectedLeftComparison
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralSystemSelectedLeftCompat

/-! # Whole-system scalar transport before selected finite-level compatibility
Source: Zheng, Construction 4.1, Lemma 5.22 and Proposition 5.26.
(blueprint: lem-sf-exceptional-integral-system-selected-left)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme Opposite SheafOfModules
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private theorem selectedSquareAux
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (e : ℕ+) (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hexp : m = e * n)
    (a : PurCompactSupport.Change (PurCompactSupport.finite l E.carrier n hn)
      (PurCompactSupport.finite l L.carrier m hm))
    (ha : ∀ T : Scheme.{u}, HEq (a.map T)
      ((PurCompactSupport.finiteChange l E.carrier L.carrier i e he e.pos n hn).map T))
    (T : Scheme.{u}) :
    (PurCompactSupport.completedChange l E.carrier L.carrier i).map T ≫
      (PurCompactSupport.reduction l L.carrier m hm).map T =
    (PurCompactSupport.reduction l E.carrier n hn).map T ≫ a.map T := by
  subst m
  rw [eq_of_heq (ha T)]
  exact PurCompactSupport.ramified_reduction_square l E.carrier L.carrier i e he e.pos n hn T

/-- Selected ramified evaluations of the normalized whole-system left scalar mate.
Source: Zheng, Construction 4.1 and Proposition 5.26; the selected-level coefficient
projection square of the exceptional coefficient construction.
Proof: use the cofinal restriction/left-extension unit and counit to evaluate at the
actual exponent e(n+1). The balanced derived tensor square compares extension then
reduction with reduction then the ramified finite extension. Apply it to the
reconstruction unit and the representative-normalized scalar reduction counit; its
transition naturality supplies a whole-system comparison. The defining realization
of core.reduction identifies this map with the specified completed comparison.
The finite scalar equality realizations and the normalized red evaluations give
selected_balanced. For q_selected, substitute the proper coefficient projection
and open balancing definitions into d.comparison_normalized; the system proper/open
realization and transport.evaluation_support identify both paths with the same
projection. No equality is inferred from finite evaluations being faithful. All
exponents are transported along z.exponent and all ring maps along z.actual.
(blueprint: lem-sf-exceptional-integral-system-selected-left). -/
theorem exceptionalIntegralSystemSelectedLeft
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (transport : Transported l Ω D hl c operation left)
    (d : Mates l Ω c operation left)
    (red : ∀ (E : FieldStage.{u} l) (n : ℕ),
      ReductionMates l Ω D hl c operation left transport d E n)
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (core : SystemScalarCore l Ω D hl c operation left transport d E L i) :
    Nonempty (SystemSelectedLeft l Ω D hl c operation left transport d red E L i core) := by
  have selected_square : ∀ (e : ℕ+)
      (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (T : Scheme.{u}),
    (PurCompactSupport.completedChange l E.carrier L.carrier i).map T ≫
        (PurCompactSupport.reduction l L.carrier (z.m + 1) (Nat.succ_pos z.m)).map T =
      (PurCompactSupport.reduction l E.carrier (z.n + 1) (Nat.succ_pos z.n)).map T ≫
        z.change.map T := by
    intro e he z T
    exact selectedSquareAux l E L i e he (z.n + 1) (z.m + 1) (Nat.succ_pos _)
      (Nat.succ_pos _) z.exponent z.change z.actual T
  obtain ⟨selected, selected_balanced⟩ := exceptionalIntegralSystemSelected l Ω D hl c
    operation left transport d red E L i core selected_square
  refine ⟨{ selected := selected
            selected_square := selected_square
            selected_balanced := selected_balanced
            q_selected := ?_ }⟩
  exact exceptionalIntegralSystemSelectedLeftCompat l Ω D hl c operation left transport d red
    E L i core selected_square selected selected_balanced

end WeilConjectures.ExceptionalIntegralScalar

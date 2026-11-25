/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Compactification.StoneCech

/-!
# Disjoint clopen subsets of the Stone–Čech compactification of a discrete space

For a discrete space `α`, extending the characteristic function of a point `a` to
`StoneCech α ⟶ Bool` gives a clopen subset `stoneCechClopen a` of `StoneCech α` containing
`stoneCechUnit a`; these clopen sets are pairwise disjoint (`pairwise_disjoint_stoneCechClopen`).
-/

@[expose] public section

open Function

variable {α : Type*} [TopologicalSpace α] [DiscreteTopology α]

open Classical in
/-- The continuous extension `StoneCech α ⟶ Bool` of the characteristic function of `a`. -/
noncomputable def stoneCechIndicator (a : α) : StoneCech α → Bool :=
  stoneCechExtend (g := fun b ↦ decide (b = a)) continuous_of_discreteTopology

lemma continuous_stoneCechIndicator (a : α) : Continuous (stoneCechIndicator a) :=
  continuous_stoneCechExtend _

lemma stoneCechIndicator_stoneCechUnit_eq_true_iff (a b : α) :
    stoneCechIndicator a (stoneCechUnit b) = true ↔ b = a := by
  classical
  rw [stoneCechIndicator, stoneCechExtend_stoneCechUnit]
  simp

/-- The clopen subset of `StoneCech α` cut out by the extended characteristic function of `a`. -/
def stoneCechClopen (a : α) : Set (StoneCech α) := stoneCechIndicator a ⁻¹' {true}

lemma isClopen_stoneCechClopen (a : α) : IsClopen (stoneCechClopen a) :=
  (isClopen_discrete _).preimage (continuous_stoneCechIndicator a)

lemma stoneCechUnit_mem_stoneCechClopen (a : α) : stoneCechUnit a ∈ stoneCechClopen a :=
  (stoneCechIndicator_stoneCechUnit_eq_true_iff a a).2 rfl

/-- The clopen sets `stoneCechClopen a` are pairwise disjoint: the conjunction of two extended
characteristic functions is continuous and vanishes on the dense image of `α`. -/
lemma pairwise_disjoint_stoneCechClopen :
    Pairwise (Disjoint on (stoneCechClopen : α → Set (StoneCech α))) := by
  intro a b hab
  have h : (fun x ↦ stoneCechIndicator a x && stoneCechIndicator b x) = fun _ ↦ false := by
    refine denseRange_stoneCechUnit.equalizer ?_ continuous_const (funext fun c ↦ ?_)
    · exact (continuous_of_discreteTopology (f := fun p : Bool × Bool ↦ p.1 && p.2)).comp
        ((continuous_stoneCechIndicator a).prodMk (continuous_stoneCechIndicator b))
    · simp only [comp_apply, ← Bool.not_eq_true, Bool.and_eq_true,
        stoneCechIndicator_stoneCechUnit_eq_true_iff]
      rintro ⟨rfl, rfl⟩
      exact hab rfl
  refine Set.disjoint_left.2 fun x hxa hxb ↦ ?_
  have := congrFun h x
  simp_all [stoneCechClopen]

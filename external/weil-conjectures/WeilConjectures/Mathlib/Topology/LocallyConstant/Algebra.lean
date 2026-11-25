/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.LocallyConstant.Algebra
public import WeilConjectures.Mathlib.RingTheory.Idempotents

/-!
# Noetherian rings of locally constant functions

The characteristic functions of pairwise disjoint nonempty clopen subsets of a space `X` are
pairwise orthogonal nonzero idempotents of the ring `LocallyConstant X R`. Hence if that ring is
Noetherian, such a family is finite (`LocallyConstant.finite_of_isNoetherianRing`).
-/

@[expose] public section

open Function

namespace LocallyConstant

variable {X : Type*} [TopologicalSpace X] {R : Type*} [CommRing R]

/-- The characteristic functions of a family of pairwise disjoint clopen subsets are pairwise
orthogonal idempotents. -/
theorem orthogonalIdempotents_charFn {I : Type*} {U : I → Set X} (hU : ∀ i, IsClopen (U i))
    (hdisj : Pairwise (Disjoint on U)) :
    OrthogonalIdempotents fun i ↦ charFn R (hU i) where
  idem i := by
    ext x
    by_cases hx : x ∈ U i <;> simp [coe_charFn, hx]
  ortho i j hij := by
    ext x
    by_cases hx : x ∈ U i
    · have hx' : x ∉ U j := Set.disjoint_left.1 (hdisj hij) hx
      simp [coe_charFn, hx']
    · simp [coe_charFn, hx]

/-- If the ring of `R`-valued locally constant functions on `X` is Noetherian, every family of
pairwise disjoint nonempty clopen subsets of `X` is finite. -/
theorem finite_of_isNoetherianRing [Nontrivial R] [IsNoetherianRing (LocallyConstant X R)]
    {I : Type*} {U : I → Set X} (hU : ∀ i, IsClopen (U i)) (hne : ∀ i, (U i).Nonempty)
    (hdisj : Pairwise (Disjoint on U)) : Finite I :=
  (orthogonalIdempotents_charFn (R := R) hU hdisj).finite_of_isNoetherianRing fun i h ↦ by
    obtain ⟨x, hx⟩ := hne i
    have := congrArg (fun f : LocallyConstant X R ↦ f x) h
    simp [coe_charFn, hx] at this

end LocallyConstant

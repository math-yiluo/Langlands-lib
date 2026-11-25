/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuResolution
import WeilConjectures.RingTheory.PopescuIdealCompEquiv

@[expose] public section

universe u v w

namespace Algebra

/-- When the extended singular ideal escapes the prime, the identity factorization resolves
the problem. The universe lift is an algebra equivalence, preserving the singular ideal.
Source: Stacks Project, Smoothing Ring Maps, definition after Situation 07F7
(blueprint: lem-weil-pbc-popescu-resolution-identity). -/
theorem canBePopescuResolved_of_ideal_not_le
    {R : Type u} {A : Type v} {Λ : Type w}
    [CommRing R] [CommRing A] [CommRing Λ] [Algebra R A] [Algebra R Λ]
    [IsNoetherianRing R] [FinitePresentation R A]
    (α : A →ₐ[R] Λ) (q : PrimeSpectrum Λ) (h : ¬ popescuIdeal α ≤ q.asIdeal) :
    CanBePopescuResolved α q := by
  let e : ULift.{u} A ≃ₐ[R] A := ULift.algEquiv
  have : FinitePresentation R (ULift.{u} A) := FinitePresentation.equiv e.symm
  refine ⟨ULift.{u} A, inferInstance, inferInstance, e.symm.toAlgHom,
    α.comp e.toAlgHom, inferInstance, ?_, ?_, ?_⟩
  · ext x
    exact congrArg α (e.apply_symm_apply x)
  · rw [popescuIdeal_comp_equiv]
  · rwa [popescuIdeal_comp_equiv]

end Algebra

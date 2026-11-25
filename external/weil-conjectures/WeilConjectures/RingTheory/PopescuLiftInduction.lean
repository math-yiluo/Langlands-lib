/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.RingTheory.StrictlyStandardElement

/-!
# The induction claim for lifting Popescu resolutions

Source: Stacks Project, Lemma 07F8 (lemma-lift-solution), induction on the list length.
(blueprint: def-weil-pbc-popescu-lift-induction)
-/

@[expose] public section

universe u v w

namespace Algebra

/-- Resolution data for the total eighth-power quotient, with its maps compatible with the
original map. Source: Stacks Project, Lemma 07F8 (lemma-lift-solution).
(blueprint: def-weil-pbc-popescu-lift-induction) -/
def PopescuEighthPowerQuotientResolved
    {R : Type u} {A : Type v} {Λ : Type w}
    [CommRing R] [CommRing A] [CommRing Λ] [Algebra R A] [Algebra R Λ]
    [IsNoetherianRing R]
    (r : ℕ) (π : Fin r → R) (α : A →ₐ[R] Λ) (q : PrimeSpectrum Λ) : Prop :=
  let J := Ideal.span (Set.range (fun i : Fin r ↦ π i ^ 8))
  let J_A := Ideal.map (algebraMap R A) J
  let J_Λ := Ideal.map (algebraMap R Λ) J
  ∃ (_ : FinitePresentation (R ⧸ J) (A ⧸ J_A))
    (α₀ : (A ⧸ J_A) →ₐ[R ⧸ J] (Λ ⧸ J_Λ)) (q₀ : PrimeSpectrum (Λ ⧸ J_Λ)),
    α₀.toRingHom.comp (Ideal.Quotient.mk J_A) =
      (Ideal.Quotient.mk J_Λ).comp α.toRingHom ∧
    PrimeSpectrum.comap (Ideal.Quotient.mk J_Λ) q₀ = q ∧
    CanBePopescuResolved α₀ q₀

/-- The universally quantified induction assertion for Lemma 07F8.
Source: Stacks Project, Lemma 07F8 (lemma-lift-solution), induction on `r`.
(blueprint: def-weil-pbc-popescu-lift-induction)
-/
def PopescuEighthPowerLifting
    (r : ℕ) : Prop :=
  ∀ (R : Type u) (A : Type v) (Λ : Type w)
    [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ] [IsNoetherianRing R] [FinitePresentation R A]
    (π : Fin r → R) (α : A →ₐ[R] Λ) (q : PrimeSpectrum Λ),
    (∀ i : Fin r, algebraMap R Λ (π i) ∈ q.asIdeal) →
    (∀ (i : Fin r)
      (x : R ⧸ Ideal.span {y | ∃ j : Fin r, j.val < i.val ∧ y = π j ^ 8}),
      π i • x = 0 ↔ π i ^ 2 • x = 0) →
    (∀ (i : Fin r)
      (x : Λ ⧸ Ideal.span
        {y | ∃ j : Fin r, j.val < i.val ∧ y = algebraMap R Λ (π j) ^ 8}),
      π i • x = 0 ↔ π i ^ 2 • x = 0) →
    (∀ i : Fin r, IsStrictlyStandardElement (R := R) (algebraMap R A (π i))) →
    PopescuEighthPowerQuotientResolved r π α q → CanBePopescuResolved α q

end Algebra

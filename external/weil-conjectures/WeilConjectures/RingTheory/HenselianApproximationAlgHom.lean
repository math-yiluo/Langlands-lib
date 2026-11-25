/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.RingTheory.HenselianPairApproximation
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Approximation of a finitely presented algebra map

Source: Stacks Project, proof of Lemma 0GS2, lines 1830–1837; Smoothing Ring Maps,
Lemma 0AH5, case (2) (blueprint: lem-weil-pbc-henselian-approximation-alg-hom).
-/

@[expose] public section

universe u

/-- Approximate a map from a finitely presented algebra into the completion by an
algebra map to the original henselian G-ring, with the same reduction modulo I.
Source: Stacks Project, proof of Lemma 0GS2, lines 1830–1837
(blueprint: lem-weil-pbc-henselian-approximation-alg-hom).

Proof: choose a finite presentation of R by finitely many variables and relations.
The images of its generators under c solve these relations in the I-adic completion.
Apply henselian_pair_approximation with N = 1. The resulting elements of A solve the
relations, so evaluation factors through the presentation to an A-algebra map σ : R → A.
Each generator differs from its completed image by an element of IB. The kernel of the
completion projection to A/I is IB; that projection composed with A → B is the quotient
map. Consequently the two maps to A/I agree on all generators and on A, and hence on R.
This argument also covers zero variables or relations; for R = A it gives the identity.
-/
theorem exists_algHom_approximation_mod_ideal
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I] (hA : IsGRing A)
    {R : Type u} [CommRing R] [Algebra A R] [Algebra.FinitePresentation A R]
    (c : R →ₐ[A] AdicCompletion I A) :
    ∃ σ : R →ₐ[A] A,
      (Ideal.Quotient.mk I).comp σ.toRingHom =
        (AdicCompletion.evalOneₐ I).toRingHom.comp c.toRingHom := by
  classical
  let : IsNoetherianRing A := hA.1
  obtain ⟨n, p, hp, t, ht⟩ := Algebra.FinitePresentation.out (R := A) (A := R)
  let relations : Fin (Fintype.card t) → MvPolynomial (Fin n) A :=
    fun j ↦ ((Fintype.equivFin t).symm j).val
  let ahat : Fin n → AdicCompletion I A := fun i ↦ c (p (MvPolynomial.X i))
  have heval : MvPolynomial.aeval ahat = c.comp p := by
    ext i
    simp [ahat]
  have hzero : ∀ j, MvPolynomial.eval₂ (algebraMap A (AdicCompletion I A))
      ahat (relations j) = 0 := by
    intro j
    change MvPolynomial.aeval ahat (relations j) = 0
    rw [heval]
    have hm : relations j ∈ RingHom.ker p.toRingHom := by
      rw [← ht]
      exact Ideal.subset_span ((Fintype.equivFin t).symm j).property
    simp only [AlgHom.comp_apply, RingHom.mem_ker, AlgHom.toRingHom_eq_coe] at hm ⊢
    change p (relations j) = 0 at hm
    rw [hm, map_zero]
  obtain ⟨a, ha, hcongr⟩ := henselian_pair_approximation I hA relations ahat hzero 1 le_rfl
  have hker : RingHom.ker p.toRingHom ≤
      RingHom.ker (MvPolynomial.aeval a : MvPolynomial (Fin n) A →ₐ[A] A).toRingHom := by
    rw [← ht]
    apply Ideal.span_le.mpr
    intro x hx
    let j := Fintype.equivFin t ⟨x, hx⟩
    have hj : relations j = x := by simp [relations, j]
    have hz := ha j
    rw [hj] at hz
    exact hz
  let σ : R →ₐ[A] A := p.liftOfSurjective hp (MvPolynomial.aeval a) hker
  refine ⟨σ, ?_⟩
  have hgen : ∀ i,
      Ideal.Quotient.mk I (a i) = AdicCompletion.evalOneₐ I (ahat i) := by
    intro i
    have hm := hcongr i
    simp only [pow_one] at hm
    rw [← AdicCompletion.ker_evalOneₐ_eq_map I (IsNoetherian.noetherian I)] at hm
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hm
    change AdicCompletion.evalOneₐ I (ahat i) =
      AdicCompletion.evalOneₐ I (algebraMap A (AdicCompletion I A) (a i)) at hm
    rw [hm]
    exact (DFunLike.congr_fun (AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk I) (a i)).symm
  have heq : (Ideal.Quotient.mkₐ A I).comp (MvPolynomial.aeval a) =
      (AdicCompletion.evalOneₐ I).comp (c.comp p) := by
    ext i
    simpa [ahat] using hgen i
  ext x
  obtain ⟨z, rfl⟩ := hp x
  change Ideal.Quotient.mk I (σ (p z)) = AdicCompletion.evalOneₐ I (c (p z))
  rw [AlgHom.liftOfSurjective_apply]
  exact DFunLike.congr_fun heq z

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.RingTheory.UnitMaximalMinorOfDepthZero

/-!
# A nonzerodivisor in the maximal minors of an injective matrix

Source: Stacks Project, Algebra, Proposition 00N1, proof of (1) => (2).
-/

@[expose] public section

universe u

namespace Matrix

open Module.associatedPrimes

private theorem injective_mulVec_localization
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (T : Submonoid R) [IsLocalization T S]
    {n p : ℕ} (A : Matrix (Fin p) (Fin n) R)
    (hinj : Function.Injective A.mulVec) :
    Function.Injective (A.map (algebraMap R S)).mulVec := by
  let f (k : ℕ) : (Fin k → R) →ₗ[R] (Fin k → S) :=
    LinearMap.pi fun i ↦ (Algebra.linearMap R S).comp (LinearMap.proj i)
  have hf (k : ℕ) : IsLocalizedModule T (f k) := inferInstance
  let g : (Fin n → S) →ₗ[R] (Fin p → S) :=
    (A.map (algebraMap R S)).mulVecLin.restrictScalars R
  apply IsLocalizedModule.injective_of_map_zero T (f n) (g := g)
  intro w hw
  have hAw : f p (A.mulVec w) = 0 := by
    ext i
    change (algebraMap R S) (A.mulVec w i) = 0
    rw [RingHom.map_mulVec]
    exact congrFun hw i
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff T (f p)).mp hAw
  have htw : (t : R) • w = 0 := by
    apply hinj
    simpa only [Submonoid.smul_def, ← Matrix.mulVec_smul, Matrix.mulVec_zero] using ht
  exact (IsLocalizedModule.eq_zero_iff T (f n)).mpr ⟨t, htw⟩

/-- Source: Stacks Project, Algebra, Proposition 00N1, proof of (1) => (2),
restricted to the last injective map; Tags 00MY, 00MW, 00LC, 00LD and 05BZ.
(blueprint: lem-weil-pbc-injective-maximal-minors-nonzerodivisor)

Proof: Localize the injection at each associated prime of R. Localization commutes
with finite free modules and preserves injectivity. The resulting Noetherian local
ring has its maximal ideal as an associated prime, so the depth-zero unit-minor
lemma gives a unit maximal minor. Determinants commute with localization. Thus the
original minor ideal is not contained in that associated prime. The associated
primes are finite, so prime avoidance gives an element of the minor ideal outside
all of them. The zero divisors are their union, so this element is a nonzerodivisor.
If there are zero columns, the empty minor is one and we take one. For the zero
ring, one is still a nonzerodivisor by the injectivity definition. -/
theorem exists_nonZeroDivisor_mem_maximal_minors
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {n p : ℕ} (A : Matrix (Fin p) (Fin n) R)
    (hinj : Function.Injective A.mulVec) :
    ∃ x : R, x ∈ Ideal.span {d : R | ∃ r : Fin n → Fin p,
      StrictMono r ∧ d = (A.submatrix r id).det} ∧ x ∈ nonZeroDivisors R := by
  classical
  let I : Ideal R := Ideal.span {d : R | ∃ r : Fin n → Fin p,
    StrictMono r ∧ d = (A.submatrix r id).det}
  change ∃ x : R, x ∈ I ∧ x ∈ nonZeroDivisors R
  by_contra! h
  have hsub : (I : Set R) ⊆ ⋃ P ∈ associatedPrimes R R, (P : Set R) := by
    rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors]
    exact h
  obtain ⟨P, hP, hIP⟩ :=
    (I.subset_union_prime_finite (associatedPrimes.finite R R) (f := id) 0 0
      (fun _ h _ _ ↦ h.isPrime)).mp hsub
  let : P.IsPrime := hP.isPrime
  let S := Localization.AtPrime P
  let q : R →+* S := algebraMap R S
  have hlocal : IsAssociatedPrime (IsLocalRing.maximalIdeal S) S := by
    apply mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
      P.primeCompl (Algebra.linearMap R S)
    change (IsLocalRing.maximalIdeal (Localization.AtPrime P)).under R ∈ associatedPrimes R R
    rw [Localization.AtPrime.under_maximalIdeal]
    exact hP
  obtain ⟨_, z, hz⟩ := isAssociatedPrime_iff.mp hlocal
  have hdepth : ∃ z : S, ∀ a : S, a * z = 0 ↔ a ∈ IsLocalRing.maximalIdeal S := by
    refine ⟨z, fun a ↦ ?_⟩
    rw [hz]
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul]
  obtain ⟨_, ⟨r, hr, hu⟩, _⟩ :=
    exists_isUnit_maximal_minor_of_annihilator_eq_maximalIdeal (A.map q) hdepth
      (injective_mulVec_localization P.primeCompl A hinj)
  have hd : (A.submatrix r id).det ∈ P :=
    hIP (Ideal.subset_span ⟨r, hr, rfl⟩)
  have hmap : q (A.submatrix r id).det ∈ IsLocalRing.maximalIdeal S :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff S P _).mpr hd
  rw [q.map_det] at hmap
  exact (IsLocalRing.mem_maximalIdeal _).mp hmap hu

end Matrix

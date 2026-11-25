/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.JapaneseDomain
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic

import Mathlib.RingTheory.Localization.AsSubring

@[expose] public section

universe u v

/-- A finite intermediate algebra can normalize all primes over one maximal ideal.
Source: Stacks Project, Algebra, Tag 0333, second paragraph of the reverse implication.
(blueprint: lem-weil-pbc-local-normal-intermediate-algebra)

Proof: Put S = A \ m. Identify the fraction field of A_m with K by the unique
fraction-field isomorphism fixing A_m. N-1 supplies finitely many module generators
of its integral closure. Integral closure commutes with localization (Tag 0307),
so write these generators as x_j/s_j, with x_j integral over A and s_j in S.
Let B = A[x_1,...,x_n] inside K. It is contained in the integral closure of A, and
is finite over A since it has finitely many integral algebra generators.
The ring S^{-1}B contains every chosen generator and is contained in the integral
closure of A_m; therefore it is exactly that integral closure, hence is a normal
domain. For any prime q of B contracting to m, every element of S avoids q.
Consequently B_q is a further localization of S^{-1}B, and is integrally closed.
This proves only the local approximation step, without asserting finiteness of
A's normalization or requiring any normal principal open. -/
theorem exists_local_normal_intermediate_algebra (A : Type u) (K : Type v)
    [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    (m : Ideal A) [m.IsMaximal]
    (hm : IsN1 (Localization.AtPrime m) (FractionRing (Localization.AtPrime m))) :
    ∃ B : Subalgebra A K, B ≤ integralClosure A K ∧ Module.Finite A B ∧
      ∀ (q : Ideal B) [q.IsPrime], Ideal.comap (algebraMap A B) q = m →
        IsIntegrallyClosed (Localization.AtPrime q) := by
  classical
  let Rm := Localization.AtPrime m
  let f := Localization.mapToFractionRing K m.primeCompl Rm
    m.primeCompl_le_nonZeroDivisors
  let : Algebra Rm K := f.toRingHom.toAlgebra
  have : IsScalarTower A Rm K := IsScalarTower.of_algebraMap_eq fun a ↦ (f.commutes a).symm
  have : IsFractionRing Rm K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m.primeCompl Rm K
  let e := IsLocalization.algEquiv (nonZeroDivisors Rm) (FractionRing Rm) K
  have : Module.Finite Rm (integralClosure Rm (FractionRing Rm)) := hm
  have : Module.Finite Rm (integralClosure Rm K) :=
    Module.Finite.of_surjective e.mapIntegralClosure.toLinearMap
      e.mapIntegralClosure.surjective
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := Rm) (M := integralClosure Rm K)
  have ht : ∀ i, ∃ t : m.primeCompl, IsIntegral A (t • (g i : K)) :=
    fun i ↦ IsIntegral.exists_multiple_integral_of_isLocalization m.primeCompl
      (g i : K) (g i).property
  choose t ht using ht
  let B := Algebra.adjoin A (Set.range fun i ↦ t i • (g i : K))
  have hB : B ≤ integralClosure A K := Algebra.adjoin_le fun x hx ↦ by
    obtain ⟨i, rfl⟩ := hx
    exact ht i
  have hfin : Module.Finite A B :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range _) fun x hx ↦ by
      obtain ⟨i, rfl⟩ := hx
      exact ht i
  -- Every element of the local normalization has an outside-m multiple in B.
  have hden : ∀ x : integralClosure Rm K, ∃ s : m.primeCompl, s • (x : K) ∈ B := by
    intro x
    have hx : x ∈ Submodule.span Rm (Set.range g) := by rw [hg]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ⟨t i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
    | zero => exact ⟨1, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨t, ht⟩ := hy
      refine ⟨s * t, ?_⟩
      simpa only [Submonoid.smul_def, Submonoid.coe_mul, Subalgebra.coe_add,
        smul_add, mul_smul, smul_comm (s : A) (t : A)] using
        B.add_mem (B.smul_mem hs (t : A)) (B.smul_mem ht (s : A))
    | smul a x _ hx =>
      obtain ⟨t, ht⟩ := hx
      obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj m.primeCompl a
      refine ⟨s * t, ?_⟩
      have hsK : algebraMap Rm K a * algebraMap A K (s : A) = algebraMap A K b := by
        simpa only [map_mul, ← IsScalarTower.algebraMap_apply, Prod.fst, Prod.snd]
          using congrArg (algebraMap Rm K) hs
      simp only [Submonoid.smul_def, Submonoid.coe_mul, Algebra.smul_def]
      change algebraMap A K ((s : A) * (t : A)) *
        (algebraMap Rm K a * (x : K)) ∈ B
      rw [map_mul]
      have he : algebraMap A K (s : A) * algebraMap A K (t : A) *
          (algebraMap Rm K a * (x : K)) = algebraMap A K b * (t • (x : K)) := by
        simp only [Submonoid.smul_def, Algebra.smul_def]
        rw [← hsK]
        ring
      rw [he]
      simpa only [Algebra.smul_def] using B.smul_mem ht b
  refine ⟨B, hB, hfin, ?_⟩
  intro q _ hq
  let fq := Localization.mapToFractionRing K q.primeCompl (Localization.AtPrime q)
    q.primeCompl_le_nonZeroDivisors
  let : Algebra (Localization.AtPrime q) K := fq.toRingHom.toAlgebra
  have : IsScalarTower B (Localization.AtPrime q) K :=
    IsScalarTower.of_algebraMap_eq fun b ↦ (fq.commutes b).symm
  have : IsFractionRing (Localization.AtPrime q) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl
      (Localization.AtPrime q) K
  -- Clear a q-denominator first, then an m-denominator; both avoid q.
  apply (isIntegrallyClosed_iff K).mpr
  intro x hx
  obtain ⟨t, ht⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization q.primeCompl x hx
  have : Algebra.IsIntegral A B := le_integralClosure_iff_isIntegral.mp hB
  have hxA : IsIntegral A (t • x) := isIntegral_trans (t • x) ht
  have hxRm : IsIntegral Rm (t • x) := hxA.tower_top
  obtain ⟨s, hs⟩ := hden ⟨t • x, hxRm⟩
  have hsQ : algebraMap A B (s : A) ∈ q.primeCompl := by
    change algebraMap A B (s : A) ∉ q
    intro h
    apply s.property
    have hm' : (s : A) ∈ Ideal.comap (algebraMap A B) q := h
    have hm : (s : A) ∈ m := by simpa only [hq] using hm'
    exact hm
  let d : q.primeCompl := ⟨algebraMap A B (s : A), hsQ⟩ * t
  refine ⟨IsLocalization.mk' (Localization.AtPrime q) ⟨_, hs⟩ d, ?_⟩
  apply (IsLocalization.lift_mk'_spec _ _ _ _).mpr
  change s • (t • x) = algebraMap B K (d : B) * x
  simp only [d, Submonoid.smul_def, Algebra.smul_def, Submonoid.coe_mul, map_mul,
    ← IsScalarTower.algebraMap_apply]
  ring

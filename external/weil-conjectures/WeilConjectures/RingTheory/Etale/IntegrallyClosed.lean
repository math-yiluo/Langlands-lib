/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.WeakDimension
public import Mathlib.RingTheory.Etale.Field

/-!
# Étale algebras over a normal domain are normal

Let `R` be an integrally closed domain and `B` an étale `R`-algebra. Every localization of `B` at
a prime ideal is an integrally closed domain (the étale case of Stacks 033C).

The proof uses that `B` is integrally closed in `B ⊗[R] K`, `K` the fraction field of `R`
(Stacks 092W, `Algebra.WeaklyEtale.isIntegrallyClosedIn_tensorProduct`), and that `B ⊗[R] K` is a
finite product of fields `Aᵢ`. The idempotents of this product come from `B`, so a prime `q` of
`B` determines a factor `Aᵢ` into which `B_q` embeds, and `B_q` is integrally closed in `Aᵢ`.
-/

@[expose] public section

universe u

open TensorProduct

/-- **Étale algebras over a normal domain are normal** (the étale case of Stacks 033C). Let `B` be
an étale algebra over an integrally closed domain `R`, and `q` a prime of `B`. Then the
localization `B_q` is an integrally closed domain. -/
theorem Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization {R B : Type u}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing B] [Algebra R B]
    [Algebra.Etale R B] (q : Ideal B) [q.IsPrime] (Bq : Type*) [CommRing Bq] [Algebra B Bq]
    [IsLocalization.AtPrime Bq q] : IsDomain Bq ∧ IsIntegrallyClosed Bq := by
  classical
  have : Nontrivial B := nontrivial_of_ne 0 1 fun h ↦
    ‹q.IsPrime›.ne_top ((Ideal.eq_top_iff_one q).2 (h ▸ q.zero_mem))
  let K := FractionRing R
  have : IsIntegrallyClosedIn R K := (isIntegrallyClosed_iff_isIntegrallyClosedIn K).1 inferInstance
  have : Algebra.IsAlgebraic R K := IsLocalization.isAlgebraic K (nonZeroDivisors R)
  have hic := Algebra.WeaklyEtale.isIntegrallyClosedIn_tensorProduct R B K
  obtain ⟨I, _, Ai, _, _, e, -⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K (K ⊗[R] B)).1 inferInstance
  have := Fintype.ofFinite I
  -- the ring map `B ⟶ ∏ Aᵢ`, injective since `B` is flat over `R`
  let Ψ : B ⊗[R] K ≃+* (∀ i, Ai i) :=
    (Algebra.TensorProduct.comm R B K).toRingEquiv.trans e.toRingEquiv
  let ι : B →+* (∀ i, Ai i) := Ψ.toRingHom.comp (algebraMap B (B ⊗[R] K))
  have hι : Function.Injective ι :=
    Ψ.injective.comp (Algebra.TensorProduct.includeLeft_injective (S := R)
      (IsFractionRing.injective R K))
  -- elements of `∏ Aᵢ` integral over `B` come from `B`
  have hint (w : ∀ i, Ai i) (p : Polynomial B) (hp : p.Monic) (hpw : p.eval₂ ι w = 0) :
      ∃ b, ι b = w := by
    have hw : _root_.IsIntegral B (Ψ.symm w) := ⟨p, hp, Ψ.injective (by
      rw [map_zero, ← hpw]
      exact (Polynomial.hom_eval₂ p _ Ψ.toRingHom _).trans (by simp [ι]))⟩
    obtain ⟨b, hb⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 hw
    exact ⟨b, by simp [ι, hb]⟩
  -- the idempotents of `∏ Aᵢ` come from `B`
  have hb (i : I) : ∃ b : B, ι b = Pi.single i 1 :=
    hint _ (Polynomial.X ^ 2 - Polynomial.X)
      (Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num))
      (by simp [sq, ← Pi.single_mul])
  choose b hb using hb
  have hsum : ∑ i, b i = 1 := hι (by
    rw [map_sum, map_one]
    simp only [hb]
    exact Finset.univ_sum_single (fun _ ↦ 1))
  obtain ⟨i, hi⟩ : ∃ i, b i ∉ q := by
    by_contra! h
    exact ‹q.IsPrime›.ne_top ((Ideal.eq_top_iff_one q).2 (hsum ▸ q.sum_mem fun i _ ↦ h i))
  let π : B →+* Ai i := (Pi.evalRingHom Ai i).comp ι
  have hπ (x : B) (hx : π x = 0) : x * b i = 0 := hι (by
    rw [map_mul, hb, map_zero]
    ext j
    by_cases h : j = i
    · subst h
      simpa [π] using hx
    · simp [h])
  have hunit (s : q.primeCompl) : IsUnit (π s) := by
    refine isUnit_iff_ne_zero.2 fun hs ↦ s.2 ?_
    exact (‹q.IsPrime›.mem_or_mem (hπ s hs ▸ q.zero_mem)).resolve_right hi
  let φ : Bq →+* Ai i := IsLocalization.lift (M := q.primeCompl) hunit
  have hφ : Function.Injective φ := (injective_iff_map_eq_zero φ).2 fun z hz ↦ by
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
    rw [IsLocalization.lift_mk'_spec, mul_zero] at hz
    refine (IsLocalization.mk'_eq_zero_iff _ _).2 ⟨⟨b i, hi⟩, ?_⟩
    rw [mul_comm]
    exact hπ x hz
  have : IsDomain Bq := hφ.isDomain φ
  refine ⟨this, ?_⟩
  let := φ.toAlgebra
  let := π.toAlgebra
  have : IsScalarTower B Bq (Ai i) :=
    .of_algebraMap_eq fun x ↦ (IsLocalization.lift_eq (M := q.primeCompl) hunit x).symm
  have : FaithfulSMul Bq (Ai i) := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : IsIntegrallyClosedIn Bq (Ai i) := by
    refine isIntegrallyClosedIn_iff.2 ⟨hφ, fun {z} hz ↦ ?_⟩
    obtain ⟨⟨m, hm⟩, p, hp, hpz⟩ :=
      IsIntegral.exists_multiple_integral_of_isLocalization q.primeCompl z hz
    rw [Submonoid.smul_def, Algebra.smul_def] at hpz
    obtain ⟨c, hc⟩ := hint (Pi.single i (π m * z)) (Polynomial.X * p)
      (Polynomial.monic_X.mul hp) (by
        ext j
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_X, Pi.mul_apply]
        by_cases h : j = i
        · subst h
          have h := Polynomial.hom_eval₂ p ι (Pi.evalRingHom Ai j) (Pi.single j (π m * z))
          rw [Pi.evalRingHom_apply, Pi.evalRingHom_apply] at h
          rw [h, Pi.single_eq_same]
          exact mul_eq_zero_of_right _ hpz
        · simp [h])
    refine ⟨IsLocalization.mk' Bq c ⟨m, hm⟩, (IsLocalization.lift_mk'_spec _ _ _ _).2 ?_⟩
    simpa [π] using congrFun hc i
  exact .of_isIntegrallyClosedIn Bq (Ai i)

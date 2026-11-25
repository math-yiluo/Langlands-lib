/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Local denominators of integral total fractions

Source: Stacks Project, Algebra, Tag 031S, reverse implication, denominator clearing.
(blueprint: lem-weil-pbc-integral-total-fraction-local-denominator).
-/

@[expose] public section

universe u

/-- Integral total fractions belong locally to any normal prime localization.
Source: Stacks Project, Algebra, Tag 031S, reverse implication, denominator clearing
(blueprint: lem-weil-pbc-integral-total-fraction-local-denominator).

Proof: Write x = a/b with b a nonzerodivisor. Put A = R_p and K = Frac(A).
The image of every nonzerodivisor s of R is nonzero in A: otherwise a multiplier
outside p kills s, forcing that multiplier to be zero, a contradiction. Thus the
map R → K extends to Q(R) → K. The image of x is integral over A by mapping a monic
integral equation, so integral closedness writes it as c/t with c in R and t outside p.
Write tx-c = d/e in Q(R). Its image in K is zero. Hence d maps to zero in A,
and there is u outside p with ud = 0. Multiplying gives (ut)x = uc in Q(R).
Take s = ut and a = uc. Neither factor lies in p, so s does not lie in p.
This also handles the zero ring vacuously, since it has no prime ideal. -/
theorem IsIntegral.exists_local_denominator_of_normal
    {R : Type u} [CommRing R] {x : FractionRing R} (hx : IsIntegral R x)
    (p : Ideal R) [p.IsPrime] [IsDomain (Localization.AtPrime p)]
    [IsIntegrallyClosed (Localization.AtPrime p)] :
    ∃ s : R, s ∉ p ∧ ∃ a : R,
      algebraMap R (FractionRing R) s * x = algebraMap R (FractionRing R) a := by
  let A := Localization.AtPrime p
  let K := FractionRing A
  have hnz (b : nonZeroDivisors R) : algebraMap R A b ≠ 0 := by
    intro hb
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl A b).mp hb
    have hsz : (s : R) = 0 := (mul_right_mem_nonZeroDivisors_eq_zero_iff b.prop).mp hs
    exact s.prop (hsz ▸ p.zero_mem)
  have hunits (b : nonZeroDivisors R) : IsUnit (algebraMap R K b) := by
    apply isUnit_iff_ne_zero.mpr
    rw [IsScalarTower.algebraMap_apply R A K]
    exact (map_ne_zero_iff (algebraMap A K) (IsFractionRing.injective A K)).mpr (hnz b)
  let f : FractionRing R →ₐ[R] K :=
    IsLocalization.liftAlgHom (M := nonZeroDivisors R) (f := Algebra.ofId R K) hunits
  have hint : IsIntegral A (f x) := (hx.map f).tower_top
  obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff K).mp inferInstance hint
  obtain ⟨c, t, ht⟩ := IsLocalization.exists_mk'_eq p.primeCompl z
  have hzt : z * algebraMap R A t = algebraMap R A c := by
    rw [← ht]
    exact IsLocalization.mk'_spec A c t
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) x
  have heq : algebraMap R A ((t : R) * a) = algebraMap R A ((b : R) * c) := by
    apply IsFractionRing.injective A K
    simp only [map_mul, ← IsScalarTower.algebraMap_apply R A K]
    have hab' := congrArg f hab
    simp only [map_mul, AlgHom.commutes] at hab'
    have hzt' := congrArg (algebraMap A K) hzt
    simp only [map_mul, ← IsScalarTower.algebraMap_apply R A K, hz] at hzt'
    calc
      algebraMap R K t * algebraMap R K a =
          algebraMap R K t * (f x * algebraMap R K b) := by rw [hab']
      _ = algebraMap R K b * (f x * algebraMap R K t) := by ring
      _ = algebraMap R K b * algebraMap R K c := by rw [hzt']
  obtain ⟨u, hu⟩ := IsLocalization.exists_of_eq (M := p.primeCompl) heq
  refine ⟨(u : R) * t, p.primeCompl.mul_mem u.prop t.prop, (u : R) * c, ?_⟩
  apply (IsLocalization.map_units (FractionRing R) b).mul_left_cancel
  simp only [map_mul]
  calc
    algebraMap R (FractionRing R) b *
        (algebraMap R (FractionRing R) u * algebraMap R (FractionRing R) t * x) =
        algebraMap R (FractionRing R) u * algebraMap R (FractionRing R) t *
          (x * algebraMap R (FractionRing R) b) := by ring
    _ = algebraMap R (FractionRing R) u * algebraMap R (FractionRing R) t *
        algebraMap R (FractionRing R) a := by rw [hab]
    _ = algebraMap R (FractionRing R) (u * (t * a)) := by simp [map_mul, mul_assoc]
    _ = algebraMap R (FractionRing R) (u * (b * c)) := by rw [hu]
    _ = algebraMap R (FractionRing R) b *
        (algebraMap R (FractionRing R) u * algebraMap R (FractionRing R) c) := by
          simp only [map_mul]
          ring


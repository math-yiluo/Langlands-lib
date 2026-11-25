/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuLiftPresentation
import WeilConjectures.RingTheory.PopescuConormalTransitionCoefficients
import Mathlib.Tactic.Ring

/-! # Redundancy of the full equations in the single zero-base chart

Source: Stacks Project, Tag 07CP, comparison of the conormal expressions on two charts.
(blueprint: lem-weil-pbc-popescu-zero-base-chart-relations).
-/

@[expose] public section

universe a c b

open scoped TensorProduct

namespace Algebra.PopescuLiftPresentation

/-- Every chart relation vanishes in the localized single-chart quotient over B.

Source: Stacks Project, Tag 07CP, final comparison calculation modulo pi.
(blueprint: lem-weil-pbc-popescu-zero-base-chart-relations).

Proof: In the single-chart quotient modulo pi all f_l vanish and the
k-th linear equations hold. For another chart k' put
b_j=a_k'*h_klj-sum h_k'lj'*h_kj'j. Compare the two cleared expressions for
a_k*a_k'*f_l in the reduced conormal module. Its specified basis on E_k implies
b_j=0 in reducedQuotient localized at a_k. Clear its localization denominator:
a power of a_k times b_j belongs to the reduced ideal. Lift this membership
to R[x]; the error is a multiple of pi squared. These terms vanish after tensoring
with B, since every f_l vanishes and pi maps to zero. Therefore b_j vanishes in
the localized single-chart quotient. Expand
 a_k*p_k'l-a_k'*p_kl+sum h_k'lj'*p_kj'.
Modulo pi this is sum b_j*z_j. All terms except a_k*p_k'l vanish, so invertibility
of a_k kills p_k'l as well. The original u_l already vanish by the quotient's
definition. This proves the assertion for every generator of the full defining
ideal without flatness, primes or equality of annihilators. The coefficient
calculation is performed before scalar extension, so it applies to arbitrary B,
including the zero ring and nonflat scalar extensions. -/
theorem zero_base_chart_relations (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (B : Type b) [CommRing B] [Algebra R B]
    (hπ : algebraMap R B π = 0) (k : Fin d.r)
    (k' : Fin d.r) (l : Fin d.m) :
    let J : Ideal d.polynomial := Ideal.span (Set.range (fun i : Fin d.m ⊕ Fin d.m ↦
      match i with
      | .inl j => d.equation (.inl j)
      | .inr l => d.equation (.inr (k, l))))
    let Dk := ULift.{c} (d.polynomial ⧸ J)
    let t := Algebra.TensorProduct.includeRight (R := R) (A := B)
      (ULift.up (Ideal.Quotient.mk J (d.includeX (d.a k))))
    algebraMap (B ⊗[R] Dk) (Localization.Away t)
      (Algebra.TensorProduct.includeRight (R := R) (A := B)
        (ULift.up (Ideal.Quotient.mk J (d.equation (.inr (k', l)))))) = 0 := by
  classical
  dsimp only
  let J : Ideal d.polynomial := Ideal.span (Set.range (fun i : Fin d.m ⊕ Fin d.m ↦
    match i with
    | .inl j => d.equation (.inl j)
    | .inr l => d.equation (.inr (k, l))))
  let Dk := ULift.{c} (d.polynomial ⧸ J)
  let A := B ⊗[R] Dk
  let inc := Algebra.TensorProduct.includeRight (R := R) (A := B) (B := Dk)
  let t : A := inc (ULift.up (Ideal.Quotient.mk J (d.includeX (d.a k))))
  let T := Localization.Away t
  let q : d.polynomial →ₐ[R] Dk :=
    (ULift.algEquiv (R := R)).symm.toAlgHom.comp (Ideal.Quotient.mkₐ R J)
  let ev : d.polynomial →+* T := (algebraMap A T).comp (inc.toRingHom.comp q.toRingHom)
  let ex : MvPolynomial (Fin d.n) R →+* T := ev.comp d.includeX.toRingHom
  change ev (d.equation (.inr (k', l))) = 0
  have hπev : ev (MvPolynomial.C π) = 0 := by
    change algebraMap A T (inc (q (algebraMap R d.polynomial π))) = 0
    rw [q.commutes, inc.commutes, IsScalarTower.algebraMap_apply R B A, hπ,
      map_zero, map_zero]
  have hzero (i : Fin d.m ⊕ Fin d.m) :
      ev (match i with
        | .inl j => d.equation (.inl j)
        | .inr l => d.equation (.inr (k, l))) = 0 := by
    have hi : Ideal.Quotient.mk J (match i with
        | .inl j => d.equation (.inl j)
        | .inr l => d.equation (.inr (k, l))) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    change algebraMap A T (inc (ULift.up (Ideal.Quotient.mk J _))) = 0
    rw [hi]
    change algebraMap A T (inc (0 : Dk)) = 0
    rw [map_zero, map_zero]
  have hf (i : Fin d.m) : ex (d.f i) = 0 := by
    change ev (d.includeX (d.f i)) = 0
    have hi := hzero (.inl i)
    simpa only [equation, map_sub, map_mul, hπev, zero_mul, sub_zero] using hi
  have hker : Ideal.span (Set.range d.f) ⊔
      Ideal.span ({MvPolynomial.C (π ^ 2)} : Set (MvPolynomial (Fin d.n) R)) ≤
        RingHom.ker ex := by
    refine sup_le (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
    · rintro _ ⟨i, rfl⟩
      exact hf i
    · intro p hp
      obtain rfl := Set.mem_singleton_iff.mp hp
      change ev (d.includeX (MvPolynomial.C (π ^ 2))) = 0
      simp only [includeX, MvPolynomial.rename_C, map_pow,
        hπev, zero_pow (by decide : 2 ≠ 0)]
  have ha : IsUnit (ex (d.a k)) :=
    IsLocalization.Away.algebraMap_isUnit (S := T) t
  have hb (j : Fin d.m) (hj : j ∈ d.E k) :
      ex (d.a k') * ex (d.h k l j) -
        ∑ j' ∈ d.E k', ex (d.h k' l j') * ex (d.h k j' j) = 0 := by
    obtain ⟨N, hN⟩ := d.conormal_transition_coefficients hd k k' l j hj
    have hz := hker hN
    rw [RingHom.mem_ker, map_mul, map_pow] at hz
    have hz' := (ha.pow N).mul_right_eq_zero.mp hz
    simpa only [map_sub, map_mul, map_sum] using hz'
  have hp (i : Fin d.m) : ex (d.a k) * ev (MvPolynomial.X (.inr i)) =
      ∑ j ∈ d.E k, ex (d.h k i j) * ev (MvPolynomial.X (.inr j)) := by
    change ev (d.includeX (d.a k)) * ev (MvPolynomial.X (.inr i)) =
      ∑ j ∈ d.E k, ev (d.includeX (d.h k i j)) * ev (MvPolynomial.X (.inr j))
    have hi := hzero (.inr i)
    simpa only [equation, map_sub, map_mul, map_sum, hπev, zero_mul, sub_zero,
      sub_eq_zero] using hi
  have heq : ev (d.equation (.inr (k', l))) =
      ex (d.a k') * ev (MvPolynomial.X (.inr l)) -
        ∑ j' ∈ d.E k', ex (d.h k' l j') * ev (MvPolynomial.X (.inr j')) := by
    simp only [equation, map_sub, map_mul, map_sum, hπev, zero_mul, sub_zero]
    rfl
  apply ha.mul_right_eq_zero.mp
  rw [heq, mul_sub, Finset.mul_sum]
  have hsum : (∑ j' ∈ d.E k', ex (d.a k) *
        (ex (d.h k' l j') * ev (MvPolynomial.X (.inr j')))) =
      ∑ j ∈ d.E k, ex (d.a k') *
        (ex (d.h k l j) * ev (MvPolynomial.X (.inr j))) := by
    calc
      _ = ∑ j' ∈ d.E k', ex (d.h k' l j') *
          (∑ j ∈ d.E k, ex (d.h k j' j) * ev (MvPolynomial.X (.inr j))) := by
        apply Finset.sum_congr rfl
        intro j' _
        rw [← hp j']
        ring
      _ = ∑ j' ∈ d.E k', ∑ j ∈ d.E k, ex (d.h k' l j') *
          (ex (d.h k j' j) * ev (MvPolynomial.X (.inr j))) := by
        apply Finset.sum_congr rfl
        intro j' _
        exact Finset.mul_sum _ _ _
      _ = ∑ j ∈ d.E k, ∑ j' ∈ d.E k', ex (d.h k' l j') *
          (ex (d.h k j' j) * ev (MvPolynomial.X (.inr j))) := Finset.sum_comm
      _ = ∑ j ∈ d.E k, (∑ j' ∈ d.E k', ex (d.h k' l j') *
          ex (d.h k j' j)) * ev (MvPolynomial.X (.inr j)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j' _
        ring
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← sub_eq_zero.mp (hb j hj)]
        ring
  rw [hsum, ← Finset.mul_sum]
  calc
    ex (d.a k) * (ex (d.a k') * ev (MvPolynomial.X (.inr l))) -
        ex (d.a k') * ∑ j ∈ d.E k, ex (d.h k l j) *
          ev (MvPolynomial.X (.inr j)) =
      ex (d.a k') * (ex (d.a k) * ev (MvPolynomial.X (.inr l)) -
        ∑ j ∈ d.E k, ex (d.h k l j) * ev (MvPolynomial.X (.inr j))) := by ring
    _ = 0 := by rw [hp l, sub_self, mul_zero]

end Algebra.PopescuLiftPresentation

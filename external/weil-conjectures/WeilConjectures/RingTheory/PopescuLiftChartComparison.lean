/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuLiftPartialChart
import Mathlib.Tactic.Ring

/-! # Comparing the partial chart with the full Popescu lifting algebra

Source: Stacks Project, Tag 07CP, the final local kernel calculation.
(blueprint: lem-weil-pbc-popescu-lift-chart-relations).
-/

@[expose] public section

universe a c

namespace Algebra.PopescuLiftPresentation


/-- The coefficients comparing two cleared relations vanish after localization
of the reduced coefficient quotient.

Source: Stacks Project, Tag 07CP, the paragraph beginning “The relations (4) imply”.
(blueprint: lem-weil-pbc-popescu-lift-chart-relations).

Proof: Reduce the cleared relations modulo pi squared and apply the quotient map
I -> I/I squared, then localize at a_k. Multiplying the k-th expression for f_l
by a_kprime and substituting the k-th expressions into the kprime-th expression
produces a zero combination of the specified conormal basis. Its coordinate at j
is the displayed coefficient, hence this coefficient is zero in the localized
quotient. The localization equality criterion gives a power of a_k annihilating
its quotient class. Thus the reduced polynomial belongs to the ideal of the
reduced f_l. Lift a finite ideal expression to R[x] using surjectivity of reduction.
The residual polynomial reduces to zero, so C(pi squared) divides it. This gives
membership in the sum of the original relation ideal and (C(pi squared)). Empty
E has no j to check; zero rings and nilpotent a_k are handled by the same
localization equality criterion, and no cancellation of pi is used. -/
private theorem chart_coefficient_clearing {R : Type a} {Cbar : Type c}
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (k k' : Fin d.r) (l : Fin d.m) (j : d.E k) :
    ∃ N : ℕ, d.a k ^ N *
        (d.a k' * d.h k l j - ∑ j' ∈ d.E k', d.h k' l j' * d.h k j' j) ∈
      Ideal.span (Set.range d.f) ⊔ Ideal.span ({MvPolynomial.C (π ^ 2)} :
        Set (MvPolynomial (Fin d.n) R)) := by
  classical
  let P := MvPolynomial (Fin d.n) (R ⧸ Ideal.span ({π ^ 2} : Set R))
  let I : Ideal P := d.reducedIdeal
  let Q := P ⧸ I
  let S := Localization.Away (d.reducedElement k)
  let F := LocalizedModule.mkLinearMap (Submonoid.powers (d.reducedElement k)) I.Cotangent
  let v (l : Fin d.m) : I := ⟨d.reduced (d.f l), Ideal.subset_span ⟨l, rfl⟩⟩
  let t (l : Fin d.m) := F (I.toCotangent (v l))
  let s (p : MvPolynomial (Fin d.n) R) : S :=
    algebraMap Q S (Ideal.Quotient.mk I (d.reduced p))
  have hred (i : Fin d.r) (l : Fin d.m) :
      d.reduced (d.a i) * d.reduced (d.f l) =
        ∑ j ∈ d.E i, d.reduced (d.h i l j) * d.reduced (d.f j) := by
    have h := congrArg (MvPolynomial.map (Ideal.Quotient.mk
      (Ideal.span ({π ^ 2} : Set R))) (σ := Fin d.n)) (hd.relation i l)
    simpa only [map_mul, map_add, map_sum, MvPolynomial.map_C,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (π ^ 2)),
      map_zero, zero_mul, add_zero] using h
  have hrel (i : Fin d.r) (l : Fin d.m) :
      s (d.a i) • t l = ∑ j ∈ d.E i, s (d.h i l j) • t j := by
    have hi : d.reduced (d.a i) • v l =
        ∑ j ∈ d.E i, d.reduced (d.h i l j) • v j := by
      apply Subtype.ext
      simpa only [Submodule.coe_smul, Submodule.coe_sum, smul_eq_mul] using hred i l
    have hc := congrArg I.toCotangent hi
    simp only [map_smul, map_sum] at hc
    have hc' : algebraMap P Q (d.reduced (d.a i)) • I.toCotangent (v l) =
        ∑ j ∈ d.E i,
          algebraMap P Q (d.reduced (d.h i l j)) • I.toCotangent (v j) := by
      simpa only [algebraMap_smul] using hc
    change algebraMap Q S (algebraMap P Q (d.reduced (d.a i))) •
      F (I.toCotangent (v l)) = ∑ j ∈ d.E i,
        algebraMap Q S (algebraMap P Q (d.reduced (d.h i l j))) •
          F (I.toCotangent (v j))
    simp only [algebraMap_smul, ← F.map_smul, ← map_sum]
    exact congrArg F hc'
  obtain ⟨b, hb⟩ := hd.conormal k
  have ht (j : d.E k) : t j = b j := (hb j).symm
  have hsum : ∑ j : d.E k,
      (s (d.a k') * s (d.h k l j) -
        ∑ j' ∈ d.E k', s (d.h k' l j') * s (d.h k j' j)) • b j = 0 := by
    simp_rw [← ht]
    rw [Finset.sum_coe_sort (d.E k) (fun j : Fin d.m ↦
      (s (d.a k') * s (d.h k l j) -
        ∑ j' ∈ d.E k', s (d.h k' l j') * s (d.h k j' j)) • t j)]
    simp only [sub_smul, Finset.sum_sub_distrib,
      Finset.sum_smul (R := S), mul_smul]
    rw [← Finset.smul_sum, ← hrel k l]
    rw [Finset.sum_comm]
    simp_rw [← Finset.smul_sum, ← hrel k]
    simp_rw [smul_comm (s (d.h k' l _)) (s (d.a k))]
    rw [← Finset.smul_sum, ← hrel k' l, smul_smul, smul_smul, mul_comm]
    exact sub_self _
  have hcoeff : s (d.a k') * s (d.h k l j) -
      ∑ j' ∈ d.E k', s (d.h k' l j') * s (d.h k j' j) = 0 := by
    exact Fintype.linearIndependent_iff.mp b.linearIndependent _ hsum j
  have hs : s (d.a k' * d.h k l j -
      ∑ j' ∈ d.E k', d.h k' l j' * d.h k j' j) = 0 := by
    simpa only [s, map_sub, map_mul, map_sum] using hcoeff
  let B := d.a k' * d.h k l j -
    ∑ j' ∈ d.E k', d.h k' l j' * d.h k j' j
  have hs' : algebraMap Q S (Ideal.Quotient.mk I (d.reduced B)) =
      algebraMap Q S 0 := by simpa only [map_zero] using hs
  obtain ⟨N, hN⟩ := IsLocalization.Away.exists_of_eq (d.reducedElement k) hs'
  have hmem : d.reduced (d.a k ^ N * B) ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul, map_pow, mul_zero] using hN
  let red := MvPolynomial.map (Ideal.Quotient.mk
    (Ideal.span ({π ^ 2} : Set R))) (σ := Fin d.n)
  let I₀ : Ideal (MvPolynomial (Fin d.n) R) := Ideal.span (Set.range d.f)
  have hmap : I₀.map red = I := by
    rw [Ideal.map_span]
    change Ideal.span (red '' Set.range d.f) = Ideal.span (Set.range (fun j ↦ red (d.f j)))
    rw [← Set.range_comp']
  have hsurj : Function.Surjective red :=
    MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨p, hp, heq⟩ := (Ideal.mem_map_iff_of_surjective red hsurj).mp (hmap.symm ▸ hmem)
  have hz : red (d.a k ^ N * B - p) = 0 := by rw [map_sub, heq, sub_self]
  have hdiv : MvPolynomial.C (π ^ 2) ∣ d.a k ^ N * B - p := by
    apply (MvPolynomial.C_dvd_iff_map_hom_eq_zero
      (Ideal.Quotient.mk (Ideal.span ({π ^ 2} : Set R))) (π ^ 2)
      (fun r ↦ (Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton)) _).mpr
    exact hz
  refine ⟨N, ?_⟩
  have hdiff : d.a k ^ N * B - p ∈
      Ideal.span ({MvPolynomial.C (π ^ 2)} : Set (MvPolynomial (Fin d.n) R)) :=
    Ideal.mem_span_singleton.mpr hdiv
  have hadd := (I₀ ⊔ Ideal.span ({MvPolynomial.C (π ^ 2)} :
    Set (MvPolynomial (Fin d.n) R))).add_mem
    (Ideal.mem_sup_left hp) (Ideal.mem_sup_right hdiff)
  simpa only [add_sub_cancel] using hadd


/-- Other charts' equations are pi-divisible in the partial chart local ring.

Source: Stacks Project, Tag 07CP (lemma-lifting), final three paragraphs.
(blueprint: lem-weil-pbc-popescu-lift-chart-relations).

Proof: Write u_l=f_l-pi*z_l and p_kl for the chart relations. The identity
pi*p_kl=-a_k*u_l+sum(h_klj*u_j) and invertibility of a_k show that every u_l
vanishes in the chart local ring (chart_original_equation_eq_zero). Compare the
conormal expressions for charts k and k': independence of the prepared conormal
basis makes b_j=a_k'*h_klj-sum(h_k'lj'*h_kj'j) vanish in Cbar localized at a_k.
Clear finitely many denominators to obtain a_k^N*b_j in I+pi^2*P. Multiplying
once more by a_k and using the cleared f-relations puts it in I_Ek+pi^2*P.
The exact expansion is
 a_k*p_k'l-a_k'*p_kl+sum(h_k'lj'*p_kj')=sum(b_j*z_j)+pi*delta,
where delta=-a_k*g_k'l+a_k'*g_kl-sum(h_k'lj'*g_kj'). Multiply by a_k^N.
The b_j terms now belong to I_Ek+pi^2*P, hence their multiples by z_j belong
to pi*D_k, since f_j=pi*z_j for j in E_k. The p_kl and p_kj' terms vanish
in D_k (normalization handles indices in E_k). Thus a_k^(N+1)*p_k'l is
in pi*D_k. Invert the unit a_k^(N+1) in the local ring and use membership
in the principal ideal (pi) to obtain p_k'l=pi*y. This gives the asserted divisibility, without
any flatness or equality-of-annihilators hypothesis. The separate, proved key
identity gives pi-torsion (chart_other_equation_pi_mul_eq_zero), which is not
part of this remaining statement. -/
theorem chart_relations_pi_divisible {R : Type a} {Cbar : Type c}
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (k : Fin d.r) (q : PrimeSpectrum d.liftingAlgebra)
    (hk : ULift.up (Ideal.Quotient.mk d.definingIdeal (d.includeX (d.a k))) ∉ q.asIdeal)
    : ∀ (k' : Fin d.r) (l : Fin d.m),
      ∃ y : d.chartLocal k q,
        algebraMap (d.chartAlgebra k) (d.chartLocal k q)
          (ULift.up (Ideal.Quotient.mk (d.chartIdeal k) (d.equation (.inr (k', l))))) =
            algebraMap R (d.chartLocal k q) π * y := by
  classical
  let T := d.chartLocal k q
  let J : Ideal T := Ideal.span ({algebraMap R T π} : Set T)
  let S := T ⧸ J
  let evT : d.polynomial →+* T :=
    (algebraMap (d.chartAlgebra k) T).comp
      ((ULift.algEquiv (R := R)).symm.toRingHom.comp (Ideal.Quotient.mk (d.chartIdeal k)))
  let ev : d.polynomial →+* S := (Ideal.Quotient.mk J).comp evT
  let s : MvPolynomial (Fin d.n) R →+* S := ev.comp d.includeX.toRingHom
  have hs (p : MvPolynomial (Fin d.n) R) : s p = ev (d.includeX p) := rfl
  have hπ : ev (MvPolynomial.C π) = 0 := by
    change Ideal.Quotient.mk J (algebraMap R T π) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hunitT : IsUnit (evT (d.includeX (d.a k))) :=
    IsLocalization.map_units T
      (⟨ULift.up (Ideal.Quotient.mk (d.chartIdeal k) (d.includeX (d.a k))), by
        change (d.chartMap k) _ ∉ q.asIdeal
        exact hk⟩ : (d.chartPrime k q).asIdeal.primeCompl)
  have hunit : IsUnit (s (d.a k)) := hunitT.map (Ideal.Quotient.mk J)
  have hf (j : Fin d.m) : s (d.f j) = 0 := by
    have hu := congrArg (Ideal.Quotient.mk J)
      (d.chart_original_equation_eq_zero hd k q hk j)
    change ev (d.equation (.inl j)) = 0 at hu
    simpa only [hs, equation,
      map_sub, map_mul, hπ, zero_mul, sub_zero] using hu
  have hI : Ideal.span (Set.range d.f) ⊔
      Ideal.span ({MvPolynomial.C (π ^ 2)} : Set (MvPolynomial (Fin d.n) R)) ≤
        RingHom.ker s := by
    apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact hf j
    · apply Ideal.span_le.mpr
      rintro _ ⟨rfl⟩
      change s (MvPolynomial.C (π ^ 2)) = 0
      change ev (d.includeX (MvPolynomial.C (π ^ 2))) = 0
      rw [show d.includeX (MvPolynomial.C (π ^ 2)) = (MvPolynomial.C π) ^ 2 by
        change MvPolynomial.rename Sum.inl (MvPolynomial.C (π ^ 2)) = _
        rw [MvPolynomial.rename_C, MvPolynomial.C_pow], map_pow, hπ, zero_pow (by decide)]
  have hb (k' : Fin d.r) (l : Fin d.m) (j : Fin d.m) (hj : j ∈ d.E k) :
      s (d.a k') * s (d.h k l j) -
        ∑ j' ∈ d.E k', s (d.h k' l j') * s (d.h k j' j) = 0 := by
    obtain ⟨N, hN⟩ := chart_coefficient_clearing π d hd k k' l ⟨j, hj⟩
    have hz : s (d.a k ^ N *
        (d.a k' * d.h k l j - ∑ j' ∈ d.E k', d.h k' l j' * d.h k j' j)) = 0 :=
      hI hN
    rw [map_mul, map_pow] at hz
    have hz' := (hunit.pow N).mul_right_eq_zero.mp hz
    simpa only [map_sub, map_mul, map_sum] using hz'
  have hp (l : Fin d.m) : ev (d.equation (.inr (k, l))) = 0 := by
    by_cases hl : l ∈ d.E k
    · have heq : d.equation (.inr (k, l)) = 0 := by
        simp only [equation, hd.normalized_g k l hl, map_zero, mul_zero, sub_zero]
        have hsum : (∑ j ∈ d.E k, d.includeX (d.h k l j) *
            MvPolynomial.X (.inr j)) =
            d.includeX (d.a k) * MvPolynomial.X (.inr l) := by
          rw [Finset.sum_eq_single l]
          · rw [hd.normalized_h k l hl l, ite_eq_left rfl]
          · intro j hj hjl
            rw [hd.normalized_h k l hl j, ite_eq_right (Ne.symm hjl), map_zero, zero_mul]
          · exact fun h ↦ (h hl).elim
        rw [hsum, sub_self]
      rw [heq, map_zero]
    · have heq : Ideal.Quotient.mk (d.chartIdeal k) (d.equation (.inr (k, l))) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span ⟨l, by simp [chartEquation, hl]⟩)
      change Ideal.Quotient.mk J
        (algebraMap (d.chartAlgebra k) T
          ((ULift.algEquiv (R := R)).symm (Ideal.Quotient.mk _ _))) = 0
      rw [heq, map_zero, map_zero, map_zero]
  have hrel (l : Fin d.m) :
      s (d.a k) * ev (MvPolynomial.X (.inr l)) =
        ∑ j ∈ d.E k, s (d.h k l j) * ev (MvPolynomial.X (.inr j)) := by
    have h := hp l
    simpa only [hs, equation, map_sub,
      map_mul, map_sum, hπ, zero_mul, sub_zero, sub_eq_zero] using h
  intro k' l
  have hswap :
      (∑ j' ∈ d.E k', s (d.h k' l j') *
        ∑ j ∈ d.E k, s (d.h k j' j) * ev (MvPolynomial.X (.inr j))) =
      ∑ j ∈ d.E k, (∑ j' ∈ d.E k', s (d.h k' l j') * s (d.h k j' j)) *
        ev (MvPolynomial.X (.inr j)) := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  have hmul : s (d.a k) * ev (d.equation (.inr (k', l))) = 0 := by
    calc
      s (d.a k) * ev (d.equation (.inr (k', l))) =
          s (d.a k') * (s (d.a k) * ev (MvPolynomial.X (.inr l))) -
            ∑ j' ∈ d.E k', s (d.h k' l j') *
              (s (d.a k) * ev (MvPolynomial.X (.inr j'))) := by
        simp only [hs, equation, map_sub,
          map_mul, map_sum, hπ, zero_mul, sub_zero, mul_sub, Finset.mul_sum]
        congr 1
        · ring
        · apply Finset.sum_congr rfl
          intro j hj
          ring
      _ = ∑ j ∈ d.E k,
          (s (d.a k') * s (d.h k l j) -
            ∑ j' ∈ d.E k', s (d.h k' l j') * s (d.h k j' j)) *
              ev (MvPolynomial.X (.inr j)) := by
        simp_rw [hrel]
        rw [hswap]
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [hb k' l j hj, zero_mul]
  have hz : ev (d.equation (.inr (k', l))) = 0 := hunit.mul_right_eq_zero.mp hmul
  have hmem : evT (d.equation (.inr (k', l))) ∈ J :=
    Ideal.Quotient.eq_zero_iff_mem.mp hz
  exact Ideal.mem_span_singleton.mp hmem


private theorem localRingHom_bijective_of_kernel_vanishes
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Surjective f) (q : PrimeSpectrum B)
    (hker : ∀ x : A, f x = 0 →
      algebraMap A (Localization.AtPrime (PrimeSpectrum.comap f q).asIdeal) x = 0) :
    Function.Bijective (Localization.localRingHom (PrimeSpectrum.comap f q).asIdeal
      q.asIdeal f rfl) := by
  let p := PrimeSpectrum.comap f q
  let F := Localization.localRingHom p.asIdeal q.asIdeal f rfl
  constructor
  · apply (injective_iff_map_eq_zero F).mpr
    intro x hx
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl x
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨u, hu⟩ := hx
    obtain ⟨b, hb⟩ := hf u
    have hbunit : IsUnit (algebraMap A (Localization.AtPrime p.asIdeal) b) :=
      IsLocalization.map_units _ (⟨b, by
        change f b ∉ q.asIdeal
        simpa only [hb] using (Ideal.mem_primeCompl_iff.mp u.property)⟩ : p.asIdeal.primeCompl)
    have hba : algebraMap A (Localization.AtPrime p.asIdeal) (b * a) = 0 :=
      hker _ (by simpa only [map_mul, hb] using hu)
    rw [map_mul] at hba
    have ha : algebraMap A (Localization.AtPrime p.asIdeal) a = 0 :=
      hbunit.mul_right_eq_zero.mp hba
    rw [IsLocalization.mk'_eq_mul_mk'_one, ha, zero_mul]
  · intro z
    obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq q.asIdeal.primeCompl z
    obtain ⟨a, ha⟩ := hf b
    obtain ⟨s, hs⟩ := hf t
    let s' : p.asIdeal.primeCompl := ⟨s, by
      change f s ∉ q.asIdeal
      simpa only [hs] using (Ideal.mem_primeCompl_iff.mp t.property)⟩
    refine ⟨IsLocalization.mk' (Localization.AtPrime p.asIdeal) a s', ?_⟩
    change F (IsLocalization.mk' (Localization.AtPrime p.asIdeal) a s') = _
    dsimp only [F]
    rw [Localization.localRingHom_mk', ha]
    congr 1
    exact Subtype.ext hs

/-- Kill the extra equations using the chart's annihilator equality, then localize.

Source: Stacks Project, Tag 07CP, the final annihilator argument.
(blueprint: lem-weil-pbc-popescu-lift-chart-relations). -/
theorem chart_comparison_bijective {R : Type a} {Cbar : Type c}
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (k : Fin d.r) (q : PrimeSpectrum d.liftingAlgebra)
    (hk : ULift.up (Ideal.Quotient.mk d.definingIdeal (d.includeX (d.a k))) ∉ q.asIdeal)
    (hAnn : Module.annihilator (d.chartLocal k q)
        (Ideal.span ({algebraMap R (d.chartLocal k q) π} : Set (d.chartLocal k q))) =
      Module.annihilator (d.chartLocal k q)
        (Ideal.span ({(algebraMap R (d.chartLocal k q) π) ^ 2} :
          Set (d.chartLocal k q)))) :
    Function.Bijective (Localization.localRingHom (d.chartPrime k q).asIdeal q.asIdeal
      (d.chartMap k).toRingHom rfl) := by
  classical
  let T := d.chartLocal k q
  let πT := algebraMap R T π
  let ev : d.polynomial →+* T :=
    (algebraMap (d.chartAlgebra k) T).comp
      ((ULift.algEquiv (R := R)).symm.toRingHom.comp (Ideal.Quotient.mk (d.chartIdeal k)))
  have hzero (t : Fin d.m ⊕ (Fin d.r × Fin d.m)) : ev (d.equation t) = 0 := by
    cases t with
    | inl l => exact d.chart_original_equation_eq_zero hd k q hk l
    | inr kl =>
      rcases kl with ⟨k', l⟩
      obtain ⟨y, hy⟩ := d.chart_relations_pi_divisible π hd k q hk k' l
      have hkill := d.chart_other_equation_pi_mul_eq_zero hd k q hk k' l
      change ev (d.equation (.inr (k', l))) = πT * y at hy
      change πT * ev (d.equation (.inr (k', l))) = 0 at hkill
      rw [hy] at hkill
      have hy2 : y ∈ Module.annihilator T (Ideal.span ({πT ^ 2} : Set T)) := by
        change y ∈ (Submodule.span T ({πT ^ 2} : Set T)).annihilator
        rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
        calc
          y * πT ^ 2 = (πT * y) * πT := by
            rw [pow_two, ← mul_assoc, mul_comm y πT]
          _ = πT * (πT * y) := mul_comm _ _
          _ = 0 := hkill
      have hy1 : y ∈ Module.annihilator T (Ideal.span ({πT} : Set T)) := hAnn.symm ▸ hy2
      have hyπ : y * πT = 0 := by
        change y ∈ (Submodule.span T ({πT} : Set T)).annihilator at hy1
        rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul] at hy1
        exact hy1
      rw [hy, mul_comm, hyπ]
  have hI : d.definingIdeal ≤ RingHom.ker ev := by
    apply Ideal.span_le.mpr
    rintro _ ⟨t, rfl⟩
    exact hzero t
  have hsurj : Function.Surjective (d.chartMap k) := by
    rintro ⟨b⟩
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨ULift.up (Ideal.Quotient.mk (d.chartIdeal k) p), rfl⟩
  apply localRingHom_bijective_of_kernel_vanishes (d.chartMap k).toRingHom hsurj q
  rintro ⟨b⟩ hb
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hp : p ∈ d.definingIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact congrArg ULift.down hb
  exact hI hp

end Algebra.PopescuLiftPresentation

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuLiftPresentation
import all WeilConjectures.RingTheory.PopescuLiftChartComparison

@[expose] public section

universe a c

namespace Algebra

/-! # Descent of the special-chart substitution -/

/-- The polynomial elimination substitution descends to the unlocalized special
lifting quotient, as a homomorphism over the special coefficient ring.
Source: Stacks Project, Tag 07CP, polynomial elimination modulo pi and comparison
of chart coefficients.
(blueprint: lem-weil-pbc-popescu-special-chart-substitution).

Proof: Write A=(Cbar/pi)[1/a_k]. Substitute x_i by its coefficient class in A,
z_j for j in E_k by X_j, and z_l otherwise by a_k inverse times the sum of
h_klj X_j. The f_l vanish since the kernel of the prepared presentation is their
span. The k-th relations vanish by normalized_h. For a chart kprime, compare
its expansion of a_k a_kprime f_l with that on chart k in the localized reduced
conormal module. The prepared basis makes every coefficient
 a_kprime h_klj - sum h_kprime,ljprime h_k,jprimej
zero in the reduced coefficient chart. The surjective presentation and its
specified kernel identify that chart with Cbar[1/a_k]; passing to A preserves
these equalities. Thus all other chart relations vanish as well. Descend through
the defining quotient, ULift, and the quotient by pi. This gives the claimed
map and its values on the free variables. To check coefficient compatibility,
use hc for the x_i, algebra compatibility for constants, polynomial induction
and hd.surjective for Cbar, and hcmod for Cbar/pi. No nontriviality assumption
is needed: localization at zero and empty sets of free variables are allowed. -/
theorem popescu_special_chart_substitution (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (c : Cbar →ₐ[R] (d.liftingAlgebra ⧸
      Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (cmod : (Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)) →+*
      (d.liftingAlgebra ⧸
        Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (hc : ∀ i : Fin d.n, c (d.ε (MvPolynomial.X i)) = Ideal.Quotient.mk _ (d.x i))
    (hcmod : cmod.comp (Ideal.Quotient.mk _) = c.toRingHom) (k : Fin d.r) :
    let C₀ := Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)
    let D₀ := d.liftingAlgebra ⧸
      Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)
    letI := cmod.toAlgebra
    let A := Localization.Away (Ideal.Quotient.mk
      (Ideal.span ({algebraMap R Cbar π} : Set Cbar)) (d.ε (d.reduced (d.a k))))
    ∃ g : D₀ →ₐ[C₀] MvPolynomial (d.E k) A,
      ∀ j : d.E k, g (Ideal.Quotient.mk _
        (ULift.up (Ideal.Quotient.mk d.definingIdeal (MvPolynomial.X (.inr j.1))))) =
          MvPolynomial.X j := by
  classical
  let C₀ := Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)
  let J := Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)
  let D₀ := d.liftingAlgebra ⧸ J
  let := cmod.toAlgebra
  let q : Cbar →+* C₀ := Ideal.Quotient.mk _
  let a₀ : C₀ := q (d.ε (d.reduced (d.a k)))
  let A := Localization.Away a₀
  let P := MvPolynomial (d.E k) A
  let coeff : Cbar →+* P :=
    MvPolynomial.C.comp ((algebraMap C₀ A).comp q)
  let red : MvPolynomial (Fin d.n) R →+*
      MvPolynomial (Fin d.n) (R ⧸ Ideal.span ({π ^ 2} : Set R)) :=
    MvPolynomial.map (Ideal.Quotient.mk _)
  let s : MvPolynomial (Fin d.n) R →+* P :=
    coeff.comp (d.ε.toRingHom.comp red)
  have hf (l : Fin d.m) : s (d.f l) = 0 := by
    have hmem : d.reduced (d.f l) ∈ RingHom.ker d.ε.toRingHom := by
      rw [hd.kernel]
      exact Ideal.subset_span ⟨l, rfl⟩
    change coeff (d.ε (d.reduced (d.f l))) = 0
    rw [show d.ε (d.reduced (d.f l)) = 0 from hmem, map_zero]
  have hcoeffR (r : R) : coeff (algebraMap R Cbar r) = s (MvPolynomial.C r) := by
    dsimp only [s, RingHom.comp_apply, red]
    rw [MvPolynomial.map_C]
    change coeff (algebraMap R Cbar r) =
      coeff (d.ε (algebraMap (R ⧸ Ideal.span ({π ^ 2} : Set R)) _
        (algebraMap R (R ⧸ Ideal.span ({π ^ 2} : Set R)) r)))
    rw [d.ε.commutes, ← IsScalarTower.algebraMap_apply]
  have hπ : s (MvPolynomial.C π) = 0 := by
    rw [← hcoeffR]
    change MvPolynomial.C (algebraMap C₀ A (q (algebraMap R Cbar π))) = 0
    rw [show q (algebraMap R Cbar π) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _),
      map_zero, map_zero]
  have hunit : IsUnit (s (d.a k)) :=
    (IsLocalization.Away.algebraMap_isUnit a₀).map MvPolynomial.C
  let u : Pˣ := hunit.unit
  have hu : (u : P) = s (d.a k) := hunit.unit_spec
  let z (l : Fin d.m) : P := if hl : l ∈ d.E k then MvPolynomial.X ⟨l, hl⟩
    else (↑u⁻¹ : P) * ∑ j : d.E k, s (d.h k l j) * MvPolynomial.X j
  have hz (j : d.E k) : z j = MvPolynomial.X j := by
    simp only [z, dite_eq_left j.property]
  have hrel (l : Fin d.m) :
      s (d.a k) * z l = ∑ j ∈ d.E k, s (d.h k l j) * z j := by
    rw [← Finset.sum_coe_sort (d.E k) (fun j ↦ s (d.h k l j) * z j)]
    simp_rw [hz]
    by_cases hl : l ∈ d.E k
    · rw [show z l = MvPolynomial.X ⟨l, hl⟩ from hz ⟨l, hl⟩]
      simp only [hd.normalized_h k l hl, apply_ite, map_zero]
      rw [Fintype.sum_eq_single ⟨l, hl⟩]
      · simp
      · intro j hj
        have hne : l ≠ j.1 := by
          intro heq
          apply hj
          exact Subtype.ext heq.symm
        simp [hne]
    · rw [show z l = (↑u⁻¹ : P) * ∑ j : d.E k,
          s (d.h k l j) * MvPolynomial.X j from dite_eq_right hl, ← hu,
        ← mul_assoc]
      simp
  let ev : d.polynomial →+* P := MvPolynomial.eval₂Hom
    (s.comp MvPolynomial.C) (Sum.elim (fun i ↦ s (MvPolynomial.X i)) z)
  have hex : ev.comp d.includeX.toRingHom = s := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ev, PopescuLiftPresentation.includeX]
    · intro i
      simp [ev, PopescuLiftPresentation.includeX]
  have hs (p : MvPolynomial (Fin d.n) R) : ev (d.includeX p) = s p :=
    DFunLike.congr_fun hex p
  have hevX (l : Fin d.m) : ev (MvPolynomial.X (.inr l)) = z l := by
    simp [ev]
  have hevπ : ev (MvPolynomial.C π) = 0 := by
    simpa only [ev, MvPolynomial.eval₂Hom_C, RingHom.comp_apply] using hπ
  have hI₀ : Ideal.span (Set.range d.f) ⊔
      Ideal.span ({MvPolynomial.C (π ^ 2)} : Set (MvPolynomial (Fin d.n) R)) ≤
        RingHom.ker s := by
    apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨l, rfl⟩
      exact hf l
    · apply Ideal.span_le.mpr
      rintro _ ⟨rfl⟩
      change s (MvPolynomial.C (π ^ 2)) = 0
      rw [MvPolynomial.C_pow, map_pow, hπ, zero_pow (by decide)]
  have hb (k' : Fin d.r) (l j : Fin d.m) (hj : j ∈ d.E k) :
      s (d.a k') * s (d.h k l j) -
        ∑ j' ∈ d.E k', s (d.h k' l j') * s (d.h k j' j) = 0 := by
    obtain ⟨N, hN⟩ := PopescuLiftPresentation.chart_coefficient_clearing π d hd k k' l ⟨j, hj⟩
    have hh : s (d.a k ^ N *
        (d.a k' * d.h k l j - ∑ j' ∈ d.E k', d.h k' l j' * d.h k j' j)) = 0 :=
      hI₀ hN
    rw [map_mul, map_pow] at hh
    have hh' := (hunit.pow N).mul_right_eq_zero.mp hh
    simpa only [map_sub, map_mul, map_sum] using hh'
  have hmulSum (t : Finset (Fin d.m)) (f : Fin d.m → P) (a : P) :
      a * ∑ j ∈ t, f j = ∑ j ∈ t, a * f j := Finset.mul_sum t f a
  have hsumMul (t : Finset (Fin d.m)) (f : Fin d.m → P) (a : P) :
      (∑ j ∈ t, f j) * a = ∑ j ∈ t, f j * a := Finset.sum_mul t f a
  have hzero (t : Fin d.m ⊕ (Fin d.r × Fin d.m)) : ev (d.equation t) = 0 := by
    cases t with
    | inl l =>
      simp only [PopescuLiftPresentation.equation, map_sub, map_mul, hs,
        hf, hevπ, zero_mul, sub_zero]
    | inr kl =>
      rcases kl with ⟨k', l⟩
      have hswap :
          (∑ j' ∈ d.E k', s (d.h k' l j') *
            ∑ j ∈ d.E k, s (d.h k j' j) * z j) =
          ∑ j ∈ d.E k, (∑ j' ∈ d.E k', s (d.h k' l j') * s (d.h k j' j)) * z j := by
        simp only [hmulSum, hsumMul, mul_assoc]
        rw [Finset.sum_comm]
      apply hunit.mul_right_eq_zero.mp
      calc
        s (d.a k) * ev (d.equation (.inr (k', l))) =
            s (d.a k') * (s (d.a k) * z l) -
              ∑ j' ∈ d.E k', s (d.h k' l j') * (s (d.a k) * z j') := by
          simp only [PopescuLiftPresentation.equation, map_sub, map_mul, map_sum,
            hs, hevX, hevπ, zero_mul, sub_zero, mul_sub, hmulSum]
          congr 1
          · ring
          · apply Finset.sum_congr rfl
            intro j hj
            ring
        _ = ∑ j ∈ d.E k,
            (s (d.a k') * s (d.h k l j) -
              ∑ j' ∈ d.E k', s (d.h k' l j') * s (d.h k j' j)) * z j := by
          simp_rw [hrel]
          rw [hswap, Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          rw [hb k' l j hj, zero_mul]
  have hI : d.definingIdeal ≤ RingHom.ker ev := by
    apply Ideal.span_le.mpr
    rintro _ ⟨t, rfl⟩
    exact hzero t
  let lift : d.liftingAlgebra →+* P :=
    (Ideal.Quotient.lift d.definingIdeal ev (fun _ hp ↦ hI hp)).comp
      (ULift.ringEquiv.toRingHom)
  have hliftπ : lift (algebraMap R d.liftingAlgebra π) = 0 := by
    change ev (MvPolynomial.C π) = 0
    exact hevπ
  have hJ : J ≤ RingHom.ker lift := by
    apply Ideal.span_le.mpr
    rintro _ ⟨rfl⟩
    exact hliftπ
  let g : D₀ →+* P := Ideal.Quotient.lift J lift (fun _ hp ↦ hJ hp)
  have hgen (p : d.polynomial) :
      g (Ideal.Quotient.mk J (ULift.up (Ideal.Quotient.mk d.definingIdeal p))) = ev p := rfl
  let left : MvPolynomial (Fin d.n) R →ₐ[R] D₀ :=
    c.comp ((d.ε.restrictScalars R).comp
      (MvPolynomial.mapAlgHom (Algebra.ofId R (R ⧸ Ideal.span ({π ^ 2} : Set R)))))
  let right : MvPolynomial (Fin d.n) R →ₐ[R] D₀ :=
    (Ideal.Quotient.mkₐ R J).comp ((ULift.algEquiv (R := R)).symm.toAlgHom.comp
      ((Ideal.Quotient.mkₐ R d.definingIdeal).comp d.includeX))
  have hpoly : left = right := by
    apply MvPolynomial.algHom_ext
    intro i
    change c (d.ε (MvPolynomial.map (algebraMap R
      (R ⧸ Ideal.span ({π ^ 2} : Set R))) (MvPolynomial.X i))) =
      Ideal.Quotient.mk J
        (ULift.up (Ideal.Quotient.mk d.definingIdeal (d.includeX (MvPolynomial.X i))))
    rw [MvPolynomial.map_X]
    simpa only [PopescuLiftPresentation.includeX, MvPolynomial.rename_X,
      PopescuLiftPresentation.x] using hc i
  have hgc (b : Cbar) : g (c b) = coeff b := by
    obtain ⟨pbar, rfl⟩ := hd.surjective b
    obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective
      (Ideal.Quotient.mk (Ideal.span ({π ^ 2} : Set R)))
      Ideal.Quotient.mk_surjective pbar
    have hh := DFunLike.congr_fun hpoly p
    change c (d.ε (d.reduced p)) = Ideal.Quotient.mk J
      (ULift.up (Ideal.Quotient.mk d.definingIdeal (d.includeX p))) at hh
    rw [hh, hgen, hs]
    rfl
  have hcompat : ∀ b : C₀, g (cmod b) = algebraMap C₀ P b := by
    intro b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hh := DFunLike.congr_fun hcmod b
    change cmod (q b) = c b at hh
    rw [hh, hgc]
    rfl
  refine ⟨{ g with commutes' := hcompat }, ?_⟩
  intro j
  change g (Ideal.Quotient.mk J
    (ULift.up (Ideal.Quotient.mk d.definingIdeal (MvPolynomial.X (.inr j.1))))) = _
  rw [hgen, hevX, hz]

end Algebra

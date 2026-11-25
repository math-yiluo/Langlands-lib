/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Data.Fintype.EquivFin
import WeilConjectures.AlgebraicGeometry.Ogoma
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.RegularSequencePowers

/-!
# Generators of a regular prime with controlled annihilators

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FD
(blueprint: lem-weil-pbc-popescu-find-sequence).
-/

@[expose] public section

universe u

namespace Ideal

private theorem span_mul_units {A : Type u} [CommRing A] {ι : Type*}
    (f c : ι → A) (hc : ∀ i, IsUnit (c i)) :
    Ideal.span (Set.range (fun i ↦ c i * f i)) = Ideal.span (Set.range f) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (Ideal.unit_mul_mem_iff_mem _ (hc i)).mp (Ideal.subset_span ⟨i, rfl⟩)

private theorem span_mul_primeCompl {R : Type u} [CommRing R]
    (q : Ideal R) [q.IsPrime] {d : ℕ} (π : Fin d → R) (s : Fin d → q.primeCompl) :
    Ideal.span (Set.range (fun i ↦ algebraMap R (Localization.AtPrime q) (s i * π i))) =
      Ideal.span (Set.range (fun i ↦ algebraMap R (Localization.AtPrime q) (π i))) := by
  simp_rw [map_mul]
  exact span_mul_units _ _ (fun i ↦ IsLocalization.map_units _ (s i))

private theorem exists_generators_powers_mem
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I q : Ideal R) [q.IsPrime] (n d : ℕ) (hn : 0 < n)
    (hpow : (q ^ n).map (algebraMap R (Localization.AtPrime q)) ≤
      I.map (algebraMap R (Localization.AtPrime q)))
    [IsRegularLocalRing (Localization.AtPrime q)]
    (hdim : ringKrullDim (Localization.AtPrime q) = (d : WithBot ℕ∞)) :
    ∃ π : Fin d → R,
      Ideal.span (Set.range (fun i ↦ algebraMap R (Localization.AtPrime q) (π i))) =
        q.map (algebraMap R (Localization.AtPrime q)) ∧ ∀ i, π i ^ n ∈ I := by
  classical
  let A := Localization.AtPrime q
  let m := IsLocalRing.maximalIdeal A
  have hmrank : m.spanFinrank = d := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
    rw [hdim] at h
    exact_mod_cast h
  obtain ⟨s, hs, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank m.fg_of_isNoetherianRing
  let v := (Finset.equivFinOfCardEq (hs.trans hmrank)).symm
  let y : Fin d → A := fun i ↦ (v i : A)
  have hrange : Set.range y = (s : Set A) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (v i).property
    · intro hx
      exact ⟨v.symm ⟨x, hx⟩, by simp [y]⟩
  have hyspan : Ideal.span (Set.range y) = q.map (algebraMap R A) := by
    rw [hrange]
    have hspan' : Ideal.span (s : Set A) = m := hspan
    rw [hspan', IsLocalization.AtPrime.map_eq_maximalIdeal]
  choose a t ht using fun i ↦ IsLocalization.exists_mk'_eq q.primeCompl (y i)
  have hat : ∀ i, algebraMap R A (a i) = algebraMap R A (t i) * y i := by
    intro i
    rw [← ht i, mul_comm]
    exact (IsLocalization.mk'_spec A (a i) (t i)).symm
  have haspan : Ideal.span (Set.range (fun i ↦ algebraMap R A (a i))) =
      q.map (algebraMap R A) := by
    simp_rw [hat]
    rw [span_mul_units _ _ (fun i ↦ IsLocalization.map_units _ (t i)), hyspan]
  have hapow : ∀ i, algebraMap R A (a i ^ n) ∈ I.map (algebraMap R A) := by
    intro i
    apply hpow
    rw [Ideal.map_pow, map_pow]
    apply Ideal.pow_mem_pow
    rw [← haspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hex : ∀ i, ∃ s : q.primeCompl, (s : R) * a i ^ n ∈ I := by
    intro i
    obtain ⟨s, hs, hsi⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl A I _).mp (hapow i)
    exact ⟨⟨s, hs⟩, hsi⟩
  choose c hc using hex
  refine ⟨fun i ↦ c i * a i, ?_, ?_⟩
  · exact (span_mul_primeCompl q a c).trans haspan
  · intro i
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    simpa [mul_pow, pow_succ, mul_assoc, mul_left_comm, mul_comm] using
      I.mul_mem_left ((c i : R) ^ k) (hc i)

private theorem localized_previous_annihilators
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (q : Ideal R) [q.IsPrime] [IsRegularLocalRing (Localization.AtPrime q)]
    (e d : ℕ) (he : 0 < e)
    (hdim : ringKrullDim (Localization.AtPrime q) = (d : WithBot ℕ∞))
    (π : Fin d → R)
    (hspan : Ideal.span (Set.range (fun i ↦ algebraMap R (Localization.AtPrime q) (π i))) =
      q.map (algebraMap R (Localization.AtPrime q))) (i : Fin d) :
    {x : LocalizedModule q.primeCompl
      (R ⧸ Ideal.span {x : R | ∃ j : Fin d, j < i ∧ x = π j ^ e}) | π i • x = 0} =
    {x : LocalizedModule q.primeCompl
      (R ⧸ Ideal.span {x : R | ∃ j : Fin d, j < i ∧ x = π j ^ e}) |
      π i • (π i • x) = 0} := by
  classical
  let A := Localization.AtPrime q
  let a : Fin d → A := fun j ↦ algebraMap R A (π j)
  have hrs : IsLocalRing.IsRegularSystemOfParameters (List.ofFn a) := by
    constructor
    · simp only [List.mem_ofFn']
      change Ideal.span (Set.range a) = IsLocalRing.maximalIdeal A
      exact hspan.trans (IsLocalization.AtPrime.map_eq_maximalIdeal (Rₚ := A) q)
    · simpa only [List.length_ofFn] using hdim.symm
  have hreg := (IsRegularLocalRing.isRegular_and_quotients_of_generators
    A d hdim (List.ofFn a) hrs).1
  let exp : Fin d → ℕ := fun j ↦ if j < i then e else 1
  have hexp : ∀ j, 0 < exp j := by intro j; dsimp [exp]; split <;> omega
  have hregpow := (RingTheory.Sequence.isRegular_ofFn_pow_iff A a exp hexp).mp hreg
  have hi : i.val < (List.ofFn (fun j ↦ a j ^ exp j)).length := by simp
  have hnext := hregpow.toIsWeaklyRegular.regular_mod_prev i.val hi
  rw [Ideal.smul_eq_mul, Ideal.mul_top] at hnext
  let J : Ideal R := Ideal.span {x : R | ∃ j : Fin d, j < i ∧ x = π j ^ e}
  have hJ : J.map (algebraMap R A) =
      Ideal.ofList ((List.ofFn (fun j ↦ a j ^ exp j)).take i.val) := by
    rw [Ideal.map_span]
    apply congrArg Ideal.span
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_take_iff_getElem,
      List.length_ofFn, List.getElem_ofFn]
    constructor
    · rintro ⟨y, ⟨j, hj, rfl⟩, rfl⟩
      refine ⟨j.val, by omega, ?_⟩
      simp [a, exp, hj]
    · rintro ⟨j, hj, hx⟩
      have hjd : j < d := by omega
      have hji : (⟨j, hjd⟩ : Fin d) < i := by exact hj.trans_le (Nat.min_le_left _ _)
      refine ⟨π ⟨j, hjd⟩ ^ e, ⟨⟨j, hjd⟩, hji, rfl⟩, ?_⟩
      simpa [a, exp, hji] using hx
  have hentry : (List.ofFn (fun j ↦ a j ^ exp j))[i.val] = algebraMap R A (π i) := by
    simp [a, exp]
  rw [hentry, ← hJ] at hnext
  have hloc : J.localized' A q.primeCompl (Algebra.linearMap R A) =
      J.map (algebraMap R A) := by
    rw [Submodule.localized'_eq_span]
    rfl
  let f := J.toLocalizedQuotient' A q.primeCompl (Algebra.linearMap R A)
  let E := IsLocalizedModule.linearEquiv q.primeCompl f
    (LocalizedModule.mkLinearMap q.primeCompl (R ⧸ J))
  have hnext' : IsSMulRegular
      (A ⧸ J.localized' A q.primeCompl (Algebra.linearMap R A)) (π i) := by
    rw [hloc]
    intro x y hxy
    apply hnext
    simpa only [algebraMap_smul A] using hxy
  have hlocalized : IsSMulRegular (LocalizedModule q.primeCompl (R ⧸ J)) (π i) :=
    (E.toEquiv.isSMulRegular_congr (fun x ↦ E.map_smul (π i) x)).mp hnext'
  ext x
  constructor
  · intro hx
    change π i • (π i • x) = 0
    rw [hx, smul_zero]
  · intro hx
    exact hlocalized.right_eq_zero_of_smul hx

/-- Source: Stacks Project, Lemma 07FD
(blueprint: lem-weil-pbc-popescu-find-sequence).
The exponent `n` is the given exponent, as obtained by the source's proof.

Proof: Set S = R \ q. Lift d generators of the maximal ideal of the regular local ring
R_q to numerators in R. Their n-th powers belong to I after localization; clearing
denominators and multiplying each generator by an element of S puts these powers in I.
Both generation after localization and membership of the n-th powers in I persist under
further multiplication by elements of S. Induct on the length of the initial segment for
which the annihilator equality holds. The localized generators form a regular sequence
by 00NQ (lem-weil-pbc-regular-local-generators-regular-sequence), and their positive powers
are regular by 07DV (lem-weil-pbc-regular-sequence-powers). Thus the next generator and
its square both act injectively on the localized quotient by previous e-th powers.
Localization is exact (lem-weil-pbc-localization-module-exact), identifying this quotient
with the localization of the finitely generated module R modulo the previous powers.
Ogoma's lemma 07FC (lem-weil-pbc-ogoma) then supplies an element of S whose product with
the next generator has equal annihilators for its first and second powers on that module.
This preserves all preceding conditions, completing the induction. -/
theorem exists_generators_with_controlled_annihilators
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I q : Ideal R) [q.IsPrime] (hIq : I ≤ q)
    (n e d : ℕ) (hn : 0 < n) (he : 0 < e)
    (hpow : (q ^ n).map (algebraMap R (Localization.AtPrime q)) ≤
      I.map (algebraMap R (Localization.AtPrime q)))
    [IsRegularLocalRing (Localization.AtPrime q)]
    (hdim : ringKrullDim (Localization.AtPrime q) = (d : WithBot ℕ∞)) :
    ∃ π : Fin d → R,
      Ideal.span (Set.range (fun i ↦ algebraMap R (Localization.AtPrime q) (π i))) =
        q.map (algebraMap R (Localization.AtPrime q)) ∧
      (∀ i : Fin d, π i ^ n ∈ I) ∧
      (∀ i : Fin d,
        {m : R ⧸ Ideal.span {x : R | ∃ j : Fin d, j < i ∧ x = π j ^ e} | π i • m = 0} =
          {m : R ⧸ Ideal.span {x : R | ∃ j : Fin d, j < i ∧ x = π j ^ e} |
            π i ^ 2 • m = 0}) := by
  classical
  have _ := hIq
  let P (k : ℕ) : Prop := ∃ π : Fin d → R,
    Ideal.span (Set.range (fun i ↦ algebraMap R (Localization.AtPrime q) (π i))) =
      q.map (algebraMap R (Localization.AtPrime q)) ∧
    (∀ i : Fin d, π i ^ n ∈ I) ∧
    (∀ i : Fin d, i.val < k →
      {m : R ⧸ Ideal.span {x : R | ∃ j : Fin d, j < i ∧ x = π j ^ e} | π i • m = 0} =
        {m : R ⧸ Ideal.span {x : R | ∃ j : Fin d, j < i ∧ x = π j ^ e} |
          π i ^ 2 • m = 0})
  have hbase : P 0 := by
    obtain ⟨π, hπ, hp⟩ := exists_generators_powers_mem I q n d hn hpow hdim
    exact ⟨π, hπ, hp, by intro i hi; omega⟩
  have hstep : ∀ k, k < d → P k → P (k + 1) := by
    intro k hk hP
    obtain ⟨π, hπ, hp, hann⟩ := hP
    let i : Fin d := ⟨k, hk⟩
    let J : Ideal R := Ideal.span {x : R | ∃ j : Fin d, j < i ∧ x = π j ^ e}
    obtain ⟨s, hs⟩ := ogoma_lemma (M := R ⧸ J) q.primeCompl (π i)
      (localized_previous_annihilators q e d he hdim π hπ i)
    have hs1 := hs 1 (by omega)
    simp only [pow_one] at hs1
    let π' : Fin d → R := Function.update π i ((s : R) * π i)
    have hsame (j : Fin d) (hj : j < i) : π' j = π j := by
      exact Function.update_of_ne (ne_of_lt hj) _ _
    have hprev (j : Fin d) (hj : j ≤ i) :
        Ideal.span {x : R | ∃ l : Fin d, l < j ∧ x = π' l ^ e} =
          Ideal.span {x : R | ∃ l : Fin d, l < j ∧ x = π l ^ e} := by
      apply congrArg Ideal.span
      ext x
      constructor
      · rintro ⟨l, hl, hxl⟩
        exact ⟨l, hl, by simpa only [hsame l (lt_of_lt_of_le hl hj)] using hxl⟩
      · rintro ⟨l, hl, hxl⟩
        exact ⟨l, hl, by simpa only [hsame l (lt_of_lt_of_le hl hj)] using hxl⟩
    refine ⟨π', ?_, ?_, ?_⟩
    · let c : Fin d → q.primeCompl := fun j ↦ if j = i then s else 1
      have hupdate : π' = fun j ↦ (c j : R) * π j := by
        funext j
        by_cases hji : j = i <;> simp [π', c, hji]
      rw [hupdate]
      exact (span_mul_primeCompl q π c).trans hπ
    · intro j
      by_cases hji : j = i
      · subst j
        simp only [π', Function.update_self, mul_pow]
        exact I.mul_mem_left _ (hp i)
      · simpa only [π', Function.update_of_ne hji] using hp j
    · intro j hj
      by_cases hji : j = i
      · subst j
        rw [hprev i le_rfl]
        simpa only [π', Function.update_self] using hs1
      · have hlt : j < i := by
          have hne : j.val ≠ k := fun h ↦ hji (Fin.ext h)
          change j.val < k
          omega
        rw [hprev j hlt.le, hsame j hlt]
        exact hann j hlt
  have hall : ∀ k, k ≤ d → P k := by
    intro k
    induction k with
    | zero => intro _; exact hbase
    | succ k ih =>
      intro hk
      exact hstep k (by omega) (ih (by omega))
  obtain ⟨π, hπ, hp, hann⟩ := hall d le_rfl
  exact ⟨π, hπ, hp, fun i ↦ hann i i.isLt⟩

end Ideal

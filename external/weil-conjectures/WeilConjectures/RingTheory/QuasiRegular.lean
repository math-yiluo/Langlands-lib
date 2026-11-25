/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Regular sequences are quasi-regular

Let `a₁, …, a_c` be a regular sequence in a commutative ring `R`, generating the ideal `I`. If
`F ∈ R[X₁, …, X_c]` is homogeneous of degree `d` and `F(a) ∈ I^{d+1}`, then all coefficients of
`F` lie in `I` (`MvPolynomial.coeff_mem_of_eval_mem_pow_succ`). Equivalently, the canonical
surjection `(R / I)[X₁, …, X_c] ⟶ ⨁_d I^d / I^{d+1}`, `Xᵢ ↦ aᵢ`, is an isomorphism: the sequence is
*quasi-regular* (Matsumura, *Commutative ring theory*, Theorem 16.2; Stacks, Tag 061M).

The regularity hypothesis is phrased by peeling off the first entry: `a` is regular
(`MvPolynomial.IsRevRegular`) if `a₀` is a nonzerodivisor modulo `(a₁, …, a_c)` and
`(a₁, …, a_c)` is regular. For a weakly regular list `r₁, …, r_c` in the sense of Mathlib
(`RingTheory.Sequence.IsWeaklyRegular`), the reversed sequence is regular in this sense.

## Main statements

- `MvPolynomial.coeff_mem_of_eval_mem_pow_succ`: quasi-regularity of regular sequences.
-/

@[expose] public section

open Finsupp

namespace MvPolynomial

variable {R : Type*} [CommRing R]

section Homogeneous

variable {σ : Type*} [Finite σ] {a : σ → R}

/-- The value at `a` of a homogeneous polynomial of degree `d` with coefficients in `K` lies in
`K (a)^d`. -/
lemma IsHomogeneous.eval_mem_mul_pow {K : Ideal R} {G : MvPolynomial σ R} {d : ℕ}
    (hG : G.IsHomogeneous d) (hK : ∀ m, G.coeff m ∈ K) :
    eval a G ∈ K * Ideal.span (Set.range a) ^ d := by
  have := Fintype.ofFinite σ
  rw [eval_eq]
  refine Ideal.sum_mem _ fun m hm ↦ Ideal.mul_mem_mul (hK m) ?_
  have hdeg : ∑ i ∈ m.support, m i = d := (hG.degree_eq_sum_deg_support hm).symm
  rw [← hdeg, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ ↦ Ideal.pow_mem_pow
    (show a i ∈ Ideal.span (Set.range a) from Ideal.subset_span ⟨i, rfl⟩) _

/-- The value at `a` of a homogeneous polynomial of degree `d` lies in `(a)^d`. -/
lemma IsHomogeneous.eval_mem_pow {G : MvPolynomial σ R} {d : ℕ} (hG : G.IsHomogeneous d) :
    eval a G ∈ Ideal.span (Set.range a) ^ d := by
  simpa using hG.eval_mem_mul_pow (a := a) (K := (⊤ : Ideal R)) fun _ ↦ Submodule.mem_top

/-- Every element of `(a)^d` is the value at `a` of a homogeneous polynomial of degree `d`. -/
lemma exists_isHomogeneous_eval_eq {d : ℕ} {x : R} (hx : x ∈ Ideal.span (Set.range a) ^ d) :
    ∃ G : MvPolynomial σ R, G.IsHomogeneous d ∧ eval a G = x := by
  have := Fintype.ofFinite σ
  induction d generalizing x with
  | zero => exact ⟨C x, isHomogeneous_C _ _, eval_C _⟩
  | succ d ih =>
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun y hy z hz ↦ ?_) (fun y z ⟨G, hG, hGy⟩ ⟨H, hH, hHz⟩ ↦
      ⟨G + H, hG.add hH, by rw [map_add, hGy, hHz]⟩)
    obtain ⟨G, hG, rfl⟩ := ih hy
    obtain ⟨c, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hz
    refine ⟨G * ∑ i, C (c i) * X i, hG.mul (IsHomogeneous.sum _ _ _ fun i _ ↦
      isHomogeneous_C_mul_X _ _), ?_⟩
    simp [Finset.mul_sum]

end Homogeneous

/-- A sequence `a₀, a₁, …, a_n` is *regular, read from the end*, if `(a₁, …, a_n)` is and `a₀` is a
nonzerodivisor modulo `(a₁, …, a_n)`; that is, `a_n, a_{n-1}, …, a₀` is a regular sequence. -/
def IsRevRegular : {n : ℕ} → (Fin n → R) → Prop
  | 0, _ => True
  | _ + 1, a => IsRevRegular (Fin.tail a) ∧
      ∀ x : R, a 0 * x ∈ Ideal.span (Set.range (Fin.tail a)) →
        x ∈ Ideal.span (Set.range (Fin.tail a))

section QuasiRegular

/-- The reduction step: if every homogeneous polynomial of degree `d` vanishing at `a` has its
coefficients in `I = (a)`, so does every homogeneous `F` of degree `d` with `F(a) ∈ I^{d+1}`: write
`F(a) = ∑ aᵢ Gᵢ(a)` with `Gᵢ` homogeneous of degree `d`, and pass to `F - ∑ aᵢ Gᵢ`. -/
lemma coeff_mem_of_eval_mem_pow_succ_of_eval_eq_zero {n : ℕ} {a : Fin n → R} {d : ℕ}
    (hZ : ∀ F : MvPolynomial (Fin n) R, F.IsHomogeneous d → eval a F = 0 →
      ∀ m, F.coeff m ∈ Ideal.span (Set.range a))
    {F : MvPolynomial (Fin n) R} (hF : F.IsHomogeneous d)
    (hev : eval a F ∈ Ideal.span (Set.range a) ^ (d + 1)) (m : Fin n →₀ ℕ) :
    F.coeff m ∈ Ideal.span (Set.range a) := by
  set I := Ideal.span (Set.range a)
  have key : ∀ x ∈ I ^ d * I, ∃ G : Fin n → MvPolynomial (Fin n) R,
      (∀ i, (G i).IsHomogeneous d) ∧ x = ∑ i, a i * eval a (G i) := by
    intro x hx
    refine Submodule.mul_induction_on hx (fun y hy z hz ↦ ?_) fun y z ⟨G, hG, hy⟩ ⟨H, hH, hz⟩ ↦
      ⟨G + H, fun i ↦ (hG i).add (hH i), by
        simp [hy, hz, mul_add, Finset.sum_add_distrib]⟩
    obtain ⟨H, hH, rfl⟩ := exists_isHomogeneous_eval_eq hy
    obtain ⟨c, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hz
    exact ⟨fun i ↦ C (c i) * H, fun i ↦ hH.C_mul _, by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by simp only [map_mul, eval_C]; ring⟩
  obtain ⟨G, hG, hFG⟩ := key _ (by rwa [← pow_succ])
  have hF' : (F - ∑ i, C (a i) * G i).IsHomogeneous d :=
    hF.sub (IsHomogeneous.sum _ _ _ fun i _ ↦ (hG i).C_mul _)
  have h0 : eval a (F - ∑ i, C (a i) * G i) = 0 := by simp [hFG]
  have h1 := hZ _ hF' h0 m
  have h2 : (∑ i, C (a i) * G i).coeff m ∈ I := by
    rw [coeff_sum]
    exact Ideal.sum_mem _ fun i _ ↦ by
      rw [coeff_C_mul]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have h3 := I.add_mem h1 h2
  rwa [coeff_sub, sub_add_cancel] at h3

/-- **Regular sequences are quasi-regular.** Let `a₀, …, a_{n-1}` be regular, read from the end
(`MvPolynomial.IsRevRegular`), and `I = (a₀, …, a_{n-1})`. If `F` is homogeneous of degree `d` and
`F(a) ∈ I^{d+1}`, then every coefficient of `F` lies in `I`. (Matsumura, Theorem 16.2.) -/
theorem coeff_mem_of_eval_mem_pow_succ : ∀ {n : ℕ} {a : Fin n → R}, IsRevRegular a →
    ∀ (d : ℕ) {F : MvPolynomial (Fin n) R}, F.IsHomogeneous d →
      eval a F ∈ Ideal.span (Set.range a) ^ (d + 1) →
        ∀ m, F.coeff m ∈ Ideal.span (Set.range a)
  | 0, a, _, d, F, _, hev, m => by
    have hI : Ideal.span (Set.range a) = ⊥ := by simp [Set.range_eq_empty]
    rw [hI] at hev ⊢
    rw [Ideal.bot_pow (Nat.succ_ne_zero d)] at hev
    have hm : m = 0 := Subsingleton.elim _ _
    subst hm
    have : eval a F = F.coeff 0 := by
      conv_lhs => rw [F.eq_C_of_isEmpty]
      exact eval_C _
    rwa [this] at hev
  | n + 1, a, ha, d, F, hF, hev, m => by
    set a' : Fin n → R := Fin.tail a with ha'
    set I := Ideal.span (Set.range a)
    set J := Ideal.span (Set.range a')
    have hrange : Set.range a = insert (a 0) (Set.range a') := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ ⟨j, rfl⟩
      · rintro (rfl | ⟨j, rfl⟩)
        exacts [⟨0, rfl⟩, ⟨j.succ, rfl⟩]
    have hIJ : I = Ideal.span {a 0} ⊔ J := by
      simp only [I, J, hrange, Ideal.span_insert]
    have hJI : J ≤ I := hIJ ▸ le_sup_right
    have ha0I : a 0 ∈ I := Ideal.subset_span ⟨0, rfl⟩
    -- `a₀` is a nonzerodivisor modulo every power of `J`
    have hreg : ∀ d x, a 0 * x ∈ J ^ d → x ∈ J ^ d := by
      intro d
      induction d with
      | zero => intro x _; simp
      | succ d ihd =>
        intro x hx
        have hxd := ihd x (Ideal.pow_le_pow_right (Nat.le_succ d) hx)
        obtain ⟨G, hG, rfl⟩ := exists_isHomogeneous_eval_eq (a := a') hxd
        have hc := coeff_mem_of_eval_mem_pow_succ ha.1 d (hG.C_mul (a 0)) (by simpa using hx)
        have hcoeff : ∀ m, G.coeff m ∈ J := fun m ↦ ha.2 _ (by simpa [coeff_C_mul] using hc m)
        simpa [pow_succ'] using hG.eval_mem_mul_pow (a := a') hcoeff
    -- the vanishing statement in degree `0`
    have hZ0 : ∀ F : MvPolynomial (Fin (n + 1)) R, F.IsHomogeneous 0 → eval a F = 0 →
        ∀ m, F.coeff m ∈ I := by
      intro F hF h0 m
      have hC : F = C (F.coeff 0) :=
        totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hF.totalDegree_le)
      rw [hC, eval_C] at h0
      rw [hC, coeff_C]
      split_ifs <;> simp [h0]
    -- the vanishing statement in degree `d + 1`, from quasi-regularity in degree `d`
    have hZ : ∀ d, (∀ F : MvPolynomial (Fin (n + 1)) R, F.IsHomogeneous d →
        eval a F ∈ I ^ (d + 1) → ∀ m, F.coeff m ∈ I) →
        ∀ F : MvPolynomial (Fin (n + 1)) R, F.IsHomogeneous (d + 1) → eval a F = 0 →
          ∀ m, F.coeff m ∈ I := by
      intro d ihS F hF h0 m
      set P := finSuccEquiv R n F with hP
      set G := (finSuccEquiv R n).symm P.divX
      have hPG : finSuccEquiv R n G = P.divX := AlgEquiv.apply_symm_apply _ _
      have hQ0 : (P.coeff 0).IsHomogeneous (d + 1) :=
        hF.finSuccEquiv_coeff_isHomogeneous 0 (d + 1) (zero_add _)
      have hcoeffG (k : ℕ) (t : Fin n →₀ ℕ) :
          G.coeff (Finsupp.cons k t) = F.coeff (Finsupp.cons (k + 1) t) := by
        rw [← finSuccEquiv_coeff_coeff, hPG, Polynomial.coeff_divX, finSuccEquiv_coeff_coeff]
      have hG : G.IsHomogeneous d := by
        intro m' hm'
        have hm'' := hm'
        rw [← Finsupp.cons_tail m', hcoeffG] at hm''
        have h1 := hF hm''
        have h2 : (Finsupp.weight (1 : Fin (n + 1) → ℕ)) m' =
            (Finsupp.weight (1 : Fin (n + 1) → ℕ)) (Finsupp.cons (m' 0) (Finsupp.tail m')) := by
          rw [Finsupp.cons_tail]
        simp only [weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum_cons] at h1 h2 ⊢
        omega
      have hev : eval a F = a 0 * eval a G + eval a' (P.coeff 0) := by
        have e1 := eval_eq_eval_mv_eval' a' (a 0) F
        have e2 := eval_eq_eval_mv_eval' a' (a 0) G
        rw [ha', Fin.cons_self_tail] at e1 e2
        rw [e1, e2, hPG, ← hP, ← ha']
        calc _ = Polynomial.eval (a 0) (Polynomial.map (eval a')
              (Polynomial.X * P.divX + Polynomial.C (P.coeff 0))) := by
                rw [Polynomial.X_mul_divX_add]
          _ = _ := by
            simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X,
              Polynomial.map_C, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
              Polynomial.eval_C]
      have hQ0J : eval a' (P.coeff 0) ∈ J ^ (d + 1) := hQ0.eval_mem_pow
      have hGJ : eval a G ∈ J ^ (d + 1) := by
        refine hreg (d + 1) _ ?_
        have : a 0 * eval a G = -eval a' (P.coeff 0) := by
          rw [hev] at h0; linear_combination h0
        rw [this]
        exact neg_mem hQ0J
      have hGI : ∀ m, G.coeff m ∈ I := ihS G hG (Ideal.pow_right_mono hJI (d + 1) hGJ)
      obtain ⟨H, hH, hHG⟩ := exists_isHomogeneous_eval_eq (a := a') hGJ
      have hQ : ∀ t, (P.coeff 0 + C (a 0) * H).coeff t ∈ J := by
        refine coeff_mem_of_eval_mem_pow_succ ha.1 (d + 1) (hQ0.add (hH.C_mul _)) ?_
        have : eval a' (P.coeff 0 + C (a 0) * H) = 0 := by
          rw [hev] at h0
          simp only [map_add, map_mul, eval_C, hHG]
          linear_combination h0
        rw [this]
        exact zero_mem _
      have hQ0I (t : Fin n →₀ ℕ) : (P.coeff 0).coeff t ∈ I := by
        have h1 := hJI (hQ t)
        have h2 : a 0 * H.coeff t ∈ I := Ideal.mul_mem_right _ _ ha0I
        simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C_mul] at h1
        simpa using I.sub_mem h1 h2
      rw [← Finsupp.cons_tail m]
      cases h : m 0 with
      | zero => rw [← finSuccEquiv_coeff_coeff]; exact hQ0I _
      | succ k => rw [← hcoeffG]; exact hGI _
    -- quasi-regularity in all degrees
    have hS : ∀ d, ∀ F : MvPolynomial (Fin (n + 1)) R, F.IsHomogeneous d →
        eval a F ∈ I ^ (d + 1) → ∀ m, F.coeff m ∈ I := by
      intro d
      induction d with
      | zero => exact fun F hF hev ↦ coeff_mem_of_eval_mem_pow_succ_of_eval_eq_zero hZ0 hF hev
      | succ d ihS => exact fun F hF hev ↦
          coeff_mem_of_eval_mem_pow_succ_of_eval_eq_zero (hZ d ihS) hF hev
    exact hS d F hF hev m

open RingTheory.Sequence in
/-- A weakly regular list `r₁, …, r_n` gives a sequence `a` regular read from the end
(`MvPolynomial.IsRevRegular`, `a = (r_n, …, r₁)`) generating the same ideal. -/
theorem exists_isRevRegular_of_isWeaklyRegular (r : List R) (hr : IsWeaklyRegular R r) (n : ℕ)
    (hn : r.length = n) :
    ∃ a : Fin n → R, IsRevRegular a ∧ Ideal.span (Set.range a) = Ideal.ofList r := by
  induction r using List.reverseRecOn generalizing n with
  | nil =>
    subst hn
    exact ⟨Fin.elim0, trivial, by simp [Set.range_eq_empty]⟩
  | append_singleton l x ih =>
    simp only [List.length_append, List.length_singleton] at hn
    subst hn
    rw [isWeaklyRegular_append_iff, isWeaklyRegular_singleton_iff] at hr
    obtain ⟨a', ha', hspan⟩ := ih hr.1 _ rfl
    have hrange : Set.range (Fin.cons x a' : Fin (l.length + 1) → R) =
        insert x (Set.range a') := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ ⟨j, by simp⟩
      · rintro (rfl | ⟨j, rfl⟩)
        exacts [⟨0, by simp⟩, ⟨j.succ, by simp⟩]
    refine ⟨Fin.cons x a', ⟨by simpa using ha', fun y hy ↦ ?_⟩, ?_⟩
    · simp only [Fin.tail_cons, Fin.cons_zero, hspan] at hy ⊢
      have hsm : (Ideal.ofList l • ⊤ : Submodule R R) = Ideal.ofList l := by
        rw [Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id]; rfl
      have h1 := hr.2 (a₁ := Submodule.Quotient.mk y) (a₂ := 0) (by
        change x • Submodule.Quotient.mk y = x • 0
        rw [smul_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hsm]
        exact hy)
      rwa [Submodule.Quotient.mk_eq_zero, hsm] at h1
    · rw [hrange, Ideal.span_insert, hspan, Ideal.ofList_append, Ideal.ofList_singleton,
        sup_comm]

end QuasiRegular

end MvPolynomial

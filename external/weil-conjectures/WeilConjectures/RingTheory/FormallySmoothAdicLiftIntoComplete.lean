/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import WeilConjectures.RingTheory.FormallySmoothAdicQuotientGrid

/-!
# Lifting adically formally smooth algebras into complete rings

Source: Stacks Project, More on Algebra, Lemma 15.38.5 (Tag 07NJ), with the base
ring discrete (blueprint: lem-weil-pbc-fs-adic-lift-into-complete).
-/

@[expose] public section

universe u v w

namespace Algebra

/-- An algebra formally smooth for the `n`-adic topology lifts through a closed ideal `J`
of an `I`-adically complete algebra when a positive power `J ^ t` lies in `I`.
The lift satisfies the explicit continuity bound `f(n ^ (r * t)) ⊆ I`.
Source: Stacks Project, More on Algebra, Lemma 15.38.5 (Tag 07NJ).
(blueprint: lem-weil-pbc-fs-adic-lift-into-complete)

Proof (following Tag 07NJ):
1. Apply `exists_quotient_grid` to obtain compatible algebra maps
   `F a b : S → A / (J ^ a + I ^ b)` whose first row is the reduction of `g`.
   This isolates the source's finite quotient calculations and lifting induction.
2. Since `J ^ (b*t) = (J ^ t) ^ b ≤ I ^ b`, factor the diagonal maps through
   `A / I ^ b`. Grid compatibility and composition of quotient factors prove
   compatibility of this family. `IsAdicComplete.liftAlgHom` gives `f : S → A`
   with exactly these reductions.
3. For positive `b`, compatibility with the first row shows that `f` and `g`
   agree modulo `J + I ^ b`. For each `x`, choose a representative `y` of `g x`.
   Then `f x - y` lies in every `J + I ^ b`, and hence in `J` by closedness.
   The quotient equality criterion proves `(Ideal.Quotient.mkₐ R J).comp f = g`.
   Only injectivity of the first-row inverse-limit map is needed here.
4. The lifting equation and `hg` imply `(n ^ r).map f ≤ I + J`. Induct on `k`
   to show `(I + J) ^ k ≤ I + J ^ k`, distributing ideal products and absorbing
   terms with an `I` factor. Taking `t`th powers and using `map_pow` and `pow_mul`
   gives `(n ^ (r*t)).map f ≤ (I + J) ^ t ≤ I + J ^ t ≤ I`.
All quotient algebra structures and maps use `def-weil-pbc-algebra-hom-quotient`. -/
theorem FormallySmoothAdic.exists_lift_into_complete
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    (n : Ideal S) (hS : FormallySmoothAdic R S n)
    (I J : Ideal A) [IsAdicComplete I A]
    (t : ℕ) (ht : 1 ≤ t) (hJI : J ^ t ≤ I)
    (hJ : J = ⨅ (m : ℕ) (_ : 1 ≤ m), J ⊔ I ^ m)
    (g : S →ₐ[R] A ⧸ J) (r : ℕ) (hr : 1 ≤ r)
    (hg : ∀ x ∈ n ^ r, g x ∈ I.map (Ideal.Quotient.mk J)) :
    ∃ f : S →ₐ[R] A, (Ideal.Quotient.mkₐ R J).comp f = g ∧
      ∀ x ∈ n ^ (r * t), f x ∈ I := by
  obtain ⟨F, hF, hrow⟩ := hS.exists_quotient_grid n I J g r hr hg
  have hdiag (b : ℕ) : J ^ (b * t) ⊔ I ^ b ≤ I ^ b := by
    apply sup_le _ le_rfl
    rw [Nat.mul_comm, pow_mul]
    exact pow_le_pow_left' hJI b
  let d (b : ℕ) : S →ₐ[R] A ⧸ I ^ b :=
    (Ideal.Quotient.factorₐ R (hdiag b)).comp (F (b * t) b)
  have hd {b c : ℕ} (hbc : b ≤ c) :
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hbc)).comp (d c) = d b := by
    have h := hF (b * t) b (c * t) c (Nat.mul_le_mul_right t hbc) hbc
    have he := congrArg
      (fun k => (Ideal.Quotient.factorₐ R (hdiag b)).comp k) h
    simpa only [d, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp] using he
  let f : S →ₐ[R] A := IsAdicComplete.liftAlgHom I d hd
  have hfd (b : ℕ) (x : S) : Ideal.Quotient.mk (I ^ b) (f x) = d b x := by
    exact IsAdicComplete.mk_liftAlgHom I d hd b x
  have hagree (b : ℕ) (hb : 1 ≤ b) (x : S) :
      Ideal.Quotient.mk (J ⊔ I ^ b) (f x) =
        Ideal.Quotient.factor (le_sup_left : J ≤ J ⊔ I ^ b) (g x) := by
    have hbt : 1 ≤ b * t := le_trans hb (Nat.le_mul_of_pos_right b ht)
    have h := hF 1 b (b * t) b hbt le_rfl
    have he := congrArg (fun k =>
      (Ideal.Quotient.factorₐ R
        (show J ^ 1 ⊔ I ^ b ≤ J ⊔ I ^ b by simp)).comp k) h
    rw [← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp] at he
    have heval := AlgHom.congr_fun (he.trans (hrow b)) x
    have hred := congrArg
      (Ideal.Quotient.factor (le_sup_right : I ^ b ≤ J ⊔ I ^ b)) (hfd b x)
    have hcomp :
        (Ideal.Quotient.factorₐ R (le_sup_right : I ^ b ≤ J ⊔ I ^ b)).comp
          (Ideal.Quotient.factorₐ R (hdiag b)) =
        Ideal.Quotient.factorₐ R
          (sup_le_sup (by simpa only [pow_one] using
            (Ideal.pow_le_pow_right (I := J) hbt)) le_rfl) := by
      rw [Ideal.Quotient.factorₐ_comp]
    change Ideal.Quotient.mk (J ⊔ I ^ b) (f x) =
      ((Ideal.Quotient.factorₐ R (le_sup_right : I ^ b ≤ J ⊔ I ^ b)).comp
        (Ideal.Quotient.factorₐ R (hdiag b))) (F (b * t) b x) at hred
    rw [hcomp] at hred
    exact hred.trans heval
  have hfg : (Ideal.Quotient.mkₐ R J).comp f = g := by
    ext x
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (g x)
    have hmem : f x - y ∈ J := by
      rw [hJ]
      refine Ideal.mem_iInf.mpr fun b => Ideal.mem_iInf.mpr fun hb => ?_
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      rw [hagree b hb x, ← hy, Ideal.Quotient.factor_mk]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hmem |>.trans hy
  refine ⟨f, hfg, ?_⟩
  have hnr : (n ^ r).map f.toRingHom ≤ I ⊔ J := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    have h := hg x hx
    rw [← AlgHom.congr_fun hfg x] at h
    change f x ∈ (I.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) at h
    change f x ∈ I ⊔ J
    simpa only [Ideal.comap_map_quotientMk, sup_comm] using h
  have hpow (k : ℕ) : (I ⊔ J) ^ k ≤ I ⊔ J ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      calc
        (I ⊔ J) ^ k * (I ⊔ J) ≤ (I ⊔ J ^ k) * (I ⊔ J) :=
          mul_le_mul' ih le_rfl
        _ = (I * I ⊔ I * J) ⊔ (J ^ k * I ⊔ J ^ k * J) := by
          rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
        _ ≤ I ⊔ J ^ (k + 1) := by
          refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
          · exact Ideal.mul_le_left.trans le_sup_left
          · exact Ideal.mul_le_left.trans le_sup_left
          · exact Ideal.mul_le_right.trans le_sup_left
          · exact (pow_succ J k).symm.le.trans le_sup_right
  have hbound : (n ^ (r * t)).map f.toRingHom ≤ I := by
    rw [pow_mul, Ideal.map_pow]
    exact (pow_le_pow_left' hnr t).trans ((hpow t).trans (sup_le le_rfl hJI))
  intro x hx
  exact hbound (Ideal.mem_map_of_mem f.toRingHom hx)

end Algebra

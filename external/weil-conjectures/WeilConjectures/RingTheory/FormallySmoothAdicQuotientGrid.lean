/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.RingTheory.FormallySmoothAdicDiagonalStep

/-!
# Compatible lifts on a finite quotient grid

Source: Stacks Project, More on Algebra, proof of Lemma 15.38.5 (Tag 07NJ),
the quotient grid and induction paragraphs
(blueprint: lem-weil-pbc-fs-adic-compatible-quotient-grid).
-/

@[expose] public section

universe u v w

namespace Algebra

private def diagonalIdeal {A : Type w} [CommRing A] (I J : Ideal A) (k : ℕ) :
    Ideal A := J ^ (k + 1) ⊔ I ^ (k + 1)

private def diagonalStage
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    (n : Ideal S) (I J : Ideal A) (g : S →ₐ[R] A ⧸ J) (k : ℕ) :=
  {f : S →ₐ[R] A ⧸ diagonalIdeal I J k //
    (∃ e : ℕ, 1 ≤ e ∧ ∀ x ∈ n ^ e, f x = 0) ∧
    (Ideal.Quotient.factorₐ R (sup_le_sup
      (Ideal.pow_le_self (show k + 1 ≠ 0 by omega)) le_rfl)).comp f =
      (Ideal.Quotient.factorₐ R (le_sup_left : J ≤ J ⊔ I ^ (k + 1))).comp g}

private theorem exists_dependent_chain {T : ℕ → Type*}
    (rel : (k : ℕ) → T (k + 1) → T k → Prop) (hbase : Nonempty (T 0))
    (hnext : ∀ (k : ℕ) (t : T k), ∃ t' : T (k + 1), rel k t' t) :
    ∃ tower : (k : ℕ) → T k, ∀ k : ℕ, rel k (tower (k + 1)) (tower k) := by
  classical
  choose next hn using hnext
  let tower : (k : ℕ) → T k := fun k ↦
    Nat.rec (Classical.choice hbase) (fun k t ↦ next k t) k
  exact ⟨tower, fun k ↦ hn k (tower k)⟩

private theorem first_row_kills_power
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    (n : Ideal S) (I J : Ideal A) (g : S →ₐ[R] A ⧸ J) (r b : ℕ)
    (hg : ∀ x ∈ n ^ r, g x ∈ I.map (Ideal.Quotient.mk J)) :
    ∀ x ∈ n ^ (r * b),
      ((Ideal.Quotient.factorₐ R (le_sup_left : J ≤ J ⊔ I ^ b)).comp g) x = 0 := by
  let q := Ideal.Quotient.factorₐ R (le_sup_left : J ≤ J ⊔ I ^ b)
  have hmap : (n ^ r).map g ≤ I.map (Ideal.Quotient.mk J) :=
    Ideal.map_le_iff_le_comap.mpr hg
  have hp : (n ^ (r * b)).map g ≤ (I ^ b).map (Ideal.Quotient.mk J) := by
    simpa only [pow_mul, Ideal.map_pow] using pow_le_pow_left' hmap b
  have hzero : ((I ^ b).map (Ideal.Quotient.mk J)).map q = ⊥ := by
    change ((I ^ b).map (Ideal.Quotient.mkₐ R J)).map q = ⊥
    rw [Ideal.map_mapₐ]
    change (I ^ b).map (Ideal.Quotient.mkₐ R (J ⊔ I ^ b)) = ⊥
    apply (Ideal.map_eq_bot_iff_le_ker _).mpr
    intro x hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show I ^ b ≤ J ⊔ I ^ b from le_sup_right) hx)
  intro x hx
  have hm := Ideal.mem_map_of_mem q (hp (Ideal.mem_map_of_mem g hx))
  rw [hzero] at hm
  exact hm

/-- Adic formal smoothness constructs compatible maps to `A / (J ^ a + I ^ b)`
whose first row is the reduction of `g`. No completeness, closedness of `J`, or
comparison between powers of `J` and `I` is needed at this finite-stage step.
Source: Stacks Project, More on Algebra, proof of Lemma 15.38.5 (Tag 07NJ),
the quotient grid and induction paragraphs.
(blueprint: lem-weil-pbc-fs-adic-compatible-quotient-grid)

Proof:
1. The reduction of `g` modulo `J + I ^ b` annihilates `n ^ (r*b)` for positive
   `b`: take powers of the ideal-image inclusion and then apply the quotient map.
2. Use diagonal stages with exponent `k+1`, carrying their annihilation exponent
   and prescribed reduction to the first row. The initial stage is the reduction
   of `g` modulo `J + I`. The one-step theorem `exists_diagonal_successor` extends
   any stage using the next first-row reduction of `g`.
3. A proved dependent recursion lemma constructs a tower with adjacent transition
   compatibility. Induction on an inequality gives every diagonal transition.
4. Define the entry at `(a,b)` by projecting the diagonal stage at index
   `max a b`, whose exponent is `max a b + 1`. Monotonicity of `max` and quotient
   factor composition give all the required transition equations.
5. Project the prescribed first-row identity at that diagonal index to obtain the
   desired reduction of `g` at `(1,b)`. The same construction handles either zero
   index, since its quotient is a quotient of every diagonal stage.
6. The one-step lifting theorem proves the square-zero and continuity conditions
   and the independent-universe reduction through a small generated subalgebra.
   Choice is used only in this theorem-level existence proof; no definition
   selects arbitrary data from an unproved existence statement. -/
theorem FormallySmoothAdic.exists_quotient_grid
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    (n : Ideal S) (hS : FormallySmoothAdic R S n) (I J : Ideal A)
    (g : S →ₐ[R] A ⧸ J) (r : ℕ) (hr : 1 ≤ r)
    (hg : ∀ x ∈ n ^ r, g x ∈ I.map (Ideal.Quotient.mk J)) :
    ∃ F : (a b : ℕ) → S →ₐ[R] A ⧸ (J ^ a ⊔ I ^ b),
      (∀ (a b a' b' : ℕ) (ha : a ≤ a') (hb : b ≤ b'),
        (Ideal.Quotient.factorₐ R (sup_le_sup
          (Ideal.pow_le_pow_right ha) (Ideal.pow_le_pow_right hb))).comp
            (F a' b') = F a b) ∧
      ∀ b : ℕ,
        (Ideal.Quotient.factorₐ R (show J ^ 1 ⊔ I ^ b ≤ J ⊔ I ^ b by simp)).comp
          (F 1 b) = (Ideal.Quotient.factorₐ R (le_sup_left : J ≤ J ⊔ I ^ b)).comp
            g := by
  classical
  let Q := diagonalIdeal I J
  let T := diagonalStage n I J g
  have hrow (b : ℕ) (hb : 1 ≤ b) :
      ∃ e : ℕ, 1 ≤ e ∧ ∀ x ∈ n ^ e,
        ((Ideal.Quotient.factorₐ R (le_sup_left : J ≤ J ⊔ I ^ b)).comp g) x = 0 :=
    ⟨r * b, Nat.mul_pos hr hb, first_row_kills_power n I J g r b hg⟩
  have hbase : Nonempty (T 0) := by
    refine ⟨⟨(Ideal.Quotient.factorₐ R
      (show J ≤ Q 0 by simp [Q, diagonalIdeal])).comp g, ⟨r, hr, ?_⟩, ?_⟩⟩
    · intro x hx
      obtain ⟨y, hy, he⟩ := (Ideal.mem_map_iff_of_surjective
        (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).mp (hg x hx)
      change (Ideal.Quotient.factorₐ R (show J ≤ Q 0 by simp [Q, diagonalIdeal]))
        (g x) = 0
      rw [← he]
      change Ideal.Quotient.mk (Q 0) y = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (by
        simpa only [Q, diagonalIdeal, Nat.zero_add, pow_one] using
          (show I ≤ J ⊔ I from le_sup_right) hy)
    · rw [← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
  have hex : ∀ (k : ℕ) (f : T k), ∃ f' : T (k + 1),
      (Ideal.Quotient.factorₐ R (sup_le_sup
        (Ideal.pow_le_pow_right (Nat.le_succ (k + 1)))
        (Ideal.pow_le_pow_right (Nat.le_succ (k + 1))))).comp f'.val = f.val := by
    intro k f
    have hcompat :
        (Ideal.Quotient.factorₐ R (sup_le_sup
          (Ideal.pow_le_self (show k + 1 ≠ 0 by omega)) le_rfl)).comp f.val =
        (Ideal.Quotient.factorₐ R (sup_le_sup le_rfl
          (Ideal.pow_le_pow_right (Nat.le_succ (k + 1))))).comp
            ((Ideal.Quotient.factorₐ R
              (le_sup_left : J ≤ J ⊔ I ^ (k + 1 + 1))).comp g) := by
      rw [← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
      exact f.property.2
    obtain ⟨f', hf', hfirst, hcont⟩ := hS.exists_diagonal_successor n I J
      (k + 1) (by omega) f.val
      ((Ideal.Quotient.factorₐ R
        (le_sup_left : J ≤ J ⊔ I ^ (k + 1 + 1))).comp g)
      f.property.1 (hrow (k + 1 + 1) (by omega)) hcompat
    exact ⟨⟨f', hcont, hfirst⟩, hf'⟩
  obtain ⟨tower, hadj⟩ := exists_dependent_chain
    (fun k (f' : T (k + 1)) (f : T k) ↦
      (Ideal.Quotient.factorₐ R (sup_le_sup
        (Ideal.pow_le_pow_right (Nat.le_succ (k + 1)))
        (Ideal.pow_le_pow_right (Nat.le_succ (k + 1))))).comp f'.val = f.val)
    hbase hex
  have htower : ∀ (k l : ℕ) (h : k ≤ l),
      (Ideal.Quotient.factorₐ R (sup_le_sup
        (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))
        (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)))).comp
          (tower l).val = (tower k).val := by
    intro k l h
    induction l, h using Nat.le_induction with
    | base => simp
    | succ l h ih =>
      rw [← ih, ← hadj l, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
  let F (a b : ℕ) : S →ₐ[R] A ⧸ (J ^ a ⊔ I ^ b) :=
    (Ideal.Quotient.factorₐ R (sup_le_sup
      (Ideal.pow_le_pow_right ((Nat.le_max_left a b).trans (Nat.le_succ _)))
      (Ideal.pow_le_pow_right ((Nat.le_max_right a b).trans (Nat.le_succ _))))).comp
        (tower (max a b)).val
  refine ⟨F, ?_, ?_⟩
  · intro a b a' b' ha hb
    have hm : max a b ≤ max a' b' := max_le_max ha hb
    have hc := congrArg (fun f : S →ₐ[R] A ⧸ Q (max a b) ↦
      (Ideal.Quotient.factorₐ R (sup_le_sup
        (Ideal.pow_le_pow_right ((Nat.le_max_left a b).trans (Nat.le_succ _)))
        (Ideal.pow_le_pow_right ((Nat.le_max_right a b).trans (Nat.le_succ _))))).comp f)
      (htower (max a b) (max a' b') hm)
    dsimp only [F]
    rw [← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
    rw [← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp] at hc
    exact hc
  · intro b
    have hb : b ≤ max 1 b + 1 :=
      (Nat.le_max_right 1 b).trans (Nat.le_succ _)
    have hc := congrArg (fun f : S →ₐ[R] A ⧸ (J ⊔ I ^ (max 1 b + 1)) ↦
      (Ideal.Quotient.factorₐ R (sup_le_sup le_rfl
        (Ideal.pow_le_pow_right hb))).comp f) (tower (max 1 b)).property.2
    dsimp only [F]
    rw [← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
    rw [← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp,
      ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp] at hc
    exact hc

end Algebra

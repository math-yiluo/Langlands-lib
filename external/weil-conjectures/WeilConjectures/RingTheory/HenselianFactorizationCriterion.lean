/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import WeilConjectures.RingTheory.HenselianIntegralIdempotentLifting
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.LinearCombination
import WeilConjectures.RingTheory.MonicFactorizationOfIdempotent

/-!
# Factorization criterion for henselian pairs

Source: Stacks Project, More on Algebra, Lemma Tag 09XI (lemma-characterize-henselian-pair),
condition (3) iff condition (1), with Definition Tag 09XE
(blueprint: lem-weil-pbc-henselian-factorization-criterion).

The henselian pair `(A, I)` is the recorded notion of `def-weil-pbc-henselian-terminology`,
Mathlib's `HenselianRing A I`.
-/

@[expose] public section

universe u

open Polynomial

/-- The Bezout polynomial `b * h₀` represents the Chinese remainder idempotent `(1, 0)`.
Lift this idempotent in `AdjoinRoot f`, compute its images in the two factor quotients,
and apply `Polynomial.exists_monic_factorization_of_idempotent`.
Source: Stacks Project, Tag 09XI, proof of (3) implies (1). -/
private theorem factorization_of_lifting
    {R : Type u} [CommRing R] (J : Ideal R) (hJ : J ≤ Ideal.jacobson ⊥)
    (f : Polynomial R) (hf : f.Monic)
    (H : ∀ e₀ : AdjoinRoot f ⧸ J.map (algebraMap R (AdjoinRoot f)),
      IsIdempotentElem e₀ → ∃ e : AdjoinRoot f, IsIdempotentElem e ∧
        Ideal.Quotient.mk (J.map (algebraMap R (AdjoinRoot f))) e = e₀)
    (g₀ h₀ : Polynomial (R ⧸ J)) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hc : IsCoprime g₀ h₀) (hfac : f.map (Ideal.Quotient.mk J) = g₀ * h₀) :
    ∃ g h : Polynomial R, g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.map (Ideal.Quotient.mk J) = g₀ ∧ h.map (Ideal.Quotient.mk J) = h₀ := by
  obtain ⟨a, b, hab⟩ := hc
  let p₀ := b * h₀
  obtain ⟨p, hp⟩ := Polynomial.map_surjective (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective p₀
  let I := J.map (algebraMap R (AdjoinRoot f))
  let E := AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot J f
  let e₀ := Ideal.Quotient.mk I (AdjoinRoot.mk f p)
  have he₀ : IsIdempotentElem e₀ := by
    apply E.injective
    rw [map_mul]
    change (AdjoinRoot.mk (f.map (Ideal.Quotient.mk J)) (p.map (Ideal.Quotient.mk J))) *
      (AdjoinRoot.mk (f.map (Ideal.Quotient.mk J)) (p.map (Ideal.Quotient.mk J))) =
        AdjoinRoot.mk (f.map (Ideal.Quotient.mk J)) (p.map (Ideal.Quotient.mk J))
    rw [hp, ← map_mul, ← sub_eq_zero, ← map_sub, AdjoinRoot.mk_eq_zero]
    refine ⟨-(a * b), ?_⟩
    dsimp [p₀]
    rw [hfac]
    linear_combination (b * h₀) * hab
  obtain ⟨e, he, heq⟩ := H e₀ he₀
  have hmaps (q : (R ⧸ J)[X]) (hq : q ∣ f.map (Ideal.Quotient.mk J)) :
      AdjoinRoot.map (Ideal.Quotient.mk J) f q hq e = AdjoinRoot.mk q p₀ := by
    let φ := AdjoinRoot.map (Ideal.Quotient.mk J) f q hq
    have hker : I ≤ RingHom.ker φ := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      change φ (algebraMap R (AdjoinRoot f) r) = 0
      simp only [φ, AdjoinRoot.algebraMap_eq, AdjoinRoot.map_of]
      change AdjoinRoot.of q (Ideal.Quotient.mk J r) = 0
      rw [(Ideal.Quotient.eq_zero_iff_mem).mpr hr, map_zero]
    have h := congrArg (Ideal.Quotient.lift I φ hker) heq
    change φ e = φ (AdjoinRoot.mk f p) at h
    rw [h]
    change AdjoinRoot.lift _ _ _ (AdjoinRoot.mk f p) = _
    rw [AdjoinRoot.lift_mk]
    rw [← Polynomial.eval₂_map]
    rw [← AdjoinRoot.algebraMap_eq, ← Polynomial.aeval_def, AdjoinRoot.aeval_eq, hp]
  have he₁ : AdjoinRoot.map (Ideal.Quotient.mk J) f g₀
      (hfac.symm ▸ dvd_mul_right g₀ h₀) e = 1 := by
    rw [hmaps]
    have h := congrArg (AdjoinRoot.mk g₀) hab
    simpa [p₀, map_add, map_mul, AdjoinRoot.mk_self] using h
  have he₀' : AdjoinRoot.map (Ideal.Quotient.mk J) f h₀
      (hfac.symm ▸ dvd_mul_left h₀ g₀) e = 0 := by
    rw [hmaps]
    simp [p₀, map_mul, AdjoinRoot.mk_self]
  exact Polynomial.exists_monic_factorization_of_idempotent
    J hJ f hf g₀ h₀ hg₀ hh₀ ⟨a, b, hab⟩ hfac e he he₁ he₀'

/-- `(A, I)` is henselian iff (i) `I` lies in the Jacobson radical and (ii) every coprime monic
factorization of the reduction of a monic `f ∈ A[T]` lifts to a monic factorization of `f`;
in particular, when `I` lies in the Jacobson radical, henselian iff (ii).
Source: Stacks Project, More on Algebra, Lemma Tag 09XI, (3) ⇔ (1), and Definition Tag 09XE
(blueprint: lem-weil-pbc-henselian-factorization-criterion).

Proof:
1. The Jacobson condition is the `jac` field of the recorded `HenselianRing` predicate.
2. For a monic `f`, the algebra `AdjoinRoot f` is finite over `A`. Bezout coefficients
   for `g₀, h₀` give the Chinese remainder idempotent `(1, 0)` modulo `I`.
   `Algebra.existsUnique_isIdempotentElem_of_henselianRing` lifts this idempotent, and
   `Polynomial.exists_monic_factorization_of_idempotent` gives the monic factors.
3. Conversely, to lift a simple root `x` of the reduction `f₀`, divide by `X - C x`.
   The quotient `q` is monic and `q(x) = f₀'(x)` is a unit, so the division identity
   for `q` gives Bezout coefficients for `X - C x` and `q`. Lift their factorization.
   In a nonzero ring, the Jacobson condition makes `A/I` nonzero, so the lifted monic
   linear factor has degree one. Its negative constant coefficient is a root of `f`
   congruent to the original root modulo `I`. The zero ring is handled separately.
4. With the Jacobson condition given, the first equivalence yields the particular case. -/
theorem henselianRing_iff_factorization_criterion
    (A : Type u) [CommRing A] (I : Ideal A) :
    (HenselianRing A I ↔
      (I ≤ Ideal.jacobson (⊥ : Ideal A) ∧
        ∀ (f : A[X]), f.Monic → ∀ (g₀ h₀ : (A ⧸ I)[X]), g₀.Monic → h₀.Monic →
          IsCoprime g₀ h₀ → f.map (Ideal.Quotient.mk I) = g₀ * h₀ →
          ∃ g h : A[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
            g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀)) ∧
    (I ≤ Ideal.jacobson (⊥ : Ideal A) →
      (HenselianRing A I ↔
        ∀ (f : A[X]), f.Monic → ∀ (g₀ h₀ : (A ⧸ I)[X]), g₀.Monic → h₀.Monic →
          IsCoprime g₀ h₀ → f.map (Ideal.Quotient.mk I) = g₀ * h₀ →
          ∃ g h : A[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
            g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀)) := by
  classical
  -- The recorded predicate uses simple roots, so lift its linear factor directly.
  have main : HenselianRing A I ↔
      (I ≤ Ideal.jacobson (⊥ : Ideal A) ∧
        ∀ (f : A[X]), f.Monic → ∀ (g₀ h₀ : (A ⧸ I)[X]), g₀.Monic → h₀.Monic →
          IsCoprime g₀ h₀ → f.map (Ideal.Quotient.mk I) = g₀ * h₀ →
          ∃ g h : A[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
            g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀) := by
    constructor
    · intro H
      let := H
      refine ⟨HenselianRing.jac, ?_⟩
      intro f hf g₀ h₀ hg₀ hh₀ hc hfac
      let : Module.Finite A (AdjoinRoot f) := hf.finite_adjoinRoot
      apply factorization_of_lifting I HenselianRing.jac f hf
        (fun e₀ he₀ ↦ ?_) g₀ h₀ hg₀ hh₀ hc hfac
      obtain ⟨e, he, -⟩ := Algebra.existsUnique_isIdempotentElem_of_henselianRing
        A I (AdjoinRoot f) e₀ he₀
      exact ⟨e, he⟩
    · rintro ⟨hI, H⟩
      refine ⟨hI, ?_⟩
      intro f hf a₀ ha₀ hunit
      nontriviality A
      have hItop : I ≠ ⊤ := by
        intro ht
        have hj : Ideal.jacobson (⊥ : Ideal A) = ⊤ := top_le_iff.mp (ht ▸ hI)
        exact bot_ne_top (Ideal.jacobson_eq_top_iff.mp hj)
      let : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
      let f₀ := f.map (Ideal.Quotient.mk I)
      let x := Ideal.Quotient.mk I a₀
      have hroot : f₀.IsRoot x := by
        rw [Polynomial.IsRoot, Polynomial.eval_map_apply]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr ha₀
      have hfac : f₀ = (X - C x) * (f₀ /ₘ (X - C x)) :=
        (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot).symm
      have hmonic : (f₀ /ₘ (X - C x)).Monic :=
        (monic_X_sub_C x).of_mul_monic_left (hfac ▸ hf.map _)
      have hu : IsUnit ((f₀ /ₘ (X - C x)).eval x) := by
        have hd := congrArg (Polynomial.eval x)
          (divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative f₀ x)
        simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self,
          zero_mul, add_zero] at hd
        rw [hd]
        simpa only [f₀, x, derivative_map, eval_map_apply] using hunit
      have hc : IsCoprime (X - C x) (f₀ /ₘ (X - C x)) := by
        let q := f₀ /ₘ (X - C x)
        have hdiv := modByMonic_add_div q (X - C x)
        rw [modByMonic_X_sub_C_eq_C_eval] at hdiv
        refine ⟨-C hu.unit⁻¹.val * (q /ₘ (X - C x)), C hu.unit⁻¹.val, ?_⟩
        have hinv : C hu.unit⁻¹.val * C (q.eval x) = (1 : (A ⧸ I)[X]) := by
          rw [← C_mul, hu.val_inv_mul, C_1]
        dsimp [q] at hdiv hinv ⊢
        linear_combination -C hu.unit⁻¹.val * hdiv + hinv
      obtain ⟨g, h, hg, _, hgh, hgm, _⟩ :=
        H f hf (X - C x) (f₀ /ₘ (X - C x)) (monic_X_sub_C x) hmonic hc hfac
      have hdeg : g.natDegree = 1 := by
        rw [← hg.natDegree_map (Ideal.Quotient.mk I), hgm, natDegree_X_sub_C]
      refine ⟨-g.coeff 0, ?_, ?_⟩
      · rw [Polynomial.IsRoot, hgh, Polynomial.eval_mul, hg.eq_X_add_C hdeg]
        simp
      · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_neg, sub_eq_zero]
        have hc := congrArg (fun p : (A ⧸ I)[X] ↦ p.coeff 0) hgm
        simpa [x] using congrArg Neg.neg hc
  refine ⟨main, ?_⟩
  intro hI
  exact main.trans ⟨fun h ↦ h.2, fun h ↦ ⟨hI, h⟩⟩

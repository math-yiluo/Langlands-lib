/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import WeilConjectures.RingTheory.GRing
import WeilConjectures.AlgebraicGeometry.SmoothSectionEtaleLift
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.EtaleSectionLiftingOfGabberRoots
import WeilConjectures.RingTheory.GRingCompletionRegular
import WeilConjectures.RingTheory.SmoothPolynomialFactorization
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Approximation for henselian pairs with a Noetherian G-ring

Source: Stacks Project, Smoothing Ring Maps, Lemma 0AH5,
proof after reduction to a regular completion map.
(blueprint: lem-weil-pbc-henselian-pair-approximation).
-/

@[expose] public section

universe u

/-- The simple root 1 of the reduced Gabber polynomial lifts by Mathlib Hensel. -/
private theorem gabber_roots_of_henselian
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    (n : ℕ) (_hn : 1 ≤ n) (a : Fin (n + 1) → A) (ha : ∀ j, a j ∈ I)
    (f : Polynomial A) (hf : f.Monic)
    (heq : f = Polynomial.X ^ n * (Polynomial.X - 1) +
      Finset.univ.sum (fun j : Fin (n + 1) ↦
        Polynomial.C (a j) * Polynomial.X ^ (j : ℕ))) :
    ∃ α : A, α - 1 ∈ I ∧ f.IsRoot α := by
  have hmap : f.map (Ideal.Quotient.mk I) = Polynomial.X ^ n * (Polynomial.X - 1) := by
    rw [heq]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_sum]
    simp [Polynomial.map_C, fun j ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (ha j)]
  have hv : f.eval 1 ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have he := Polynomial.eval_map_apply (p := f) (f := Ideal.Quotient.mk I) 1
    simpa [hmap] using he.symm
  have hd : Ideal.Quotient.mk I (f.derivative.eval 1) = 1 := by
    have he := Polynomial.eval_map_apply (p := f.derivative) (f := Ideal.Quotient.mk I) 1
    simpa [← Polynomial.derivative_map, hmap, Polynomial.derivative_mul] using he.symm
  obtain ⟨α, hα, hαI⟩ := HenselianRing.is_henselian f hf 1 hv (hd ▸ isUnit_one)
  exact ⟨α, hαI, hα⟩

/--
For a henselian pair whose ring is a G-ring, every solution of a finite system
of polynomial equations in the adic completion is approximated to every
positive order by a solution in the original ring.
Source: Stacks Project, Smoothing Ring Maps, Lemma 0AH5 (case (2))
(blueprint: lem-weil-pbc-henselian-pair-approximation).

Proof: since `A` is a G-ring, `A → A^` is regular (More on Algebra 0AH2); by Popescu's
theorem (Smoothing 07GC) the solution `ahat`, an `A`-algebra map from
`A[x]/(f)` to `A^`, factors through a smooth `A`-algebra `B`. Composing with
`A^ → A/I^N` gives a section `B → A/I^N`, which lifts to an étale `A`-algebra
(More on Algebra 07M7); the henselian property of the pair gives a retraction to
`A` (More on Algebra 09XI), agreeing with the section modulo `I^N` by uniqueness of
`A`-algebra maps to `A/I^N`; the image of the variables is the solution `a`, and the
congruence holds because the kernel of `A^ → A/I^N` is `I^N A^`.
-/
theorem henselian_pair_approximation
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    (hA : IsGRing A) {m n : ℕ}
    (f : Fin m → MvPolynomial (Fin n) A)
    (ahat : Fin n → AdicCompletion I A)
    (hzero : ∀ j : Fin m,
      MvPolynomial.eval₂ (algebraMap A (AdicCompletion I A)) ahat (f j) = 0) :
    ∀ N : ℕ, 1 ≤ N →
      ∃ a : Fin n → A,
        (∀ j : Fin m,
          MvPolynomial.eval₂ (RingHom.id A) a (f j) = 0) ∧
        (∀ k : Fin n,
          ahat k - algebraMap A (AdicCompletion I A) (a k) ∈
            Ideal.map (algebraMap A (AdicCompletion I A)) (I ^ N)) := by
  classical
  have : IsNoetherianRing A := hA.1
  have : IsNoetherianRing (AdicCompletion I A) := AdicCompletion.isNoetherianRing I
  obtain ⟨B, hB, ψ, b, hb, hψ⟩ := exists_smooth_polynomial_factorization
    (AdicCompletion.isRegular_of_isGRing A I hA) f ahat hzero
  intro N hN
  let σ := (AdicCompletion.evalₐ I N).comp ψ
  obtain ⟨A', hA', α, hα, tildeσ, htilde⟩ :=
    AlgebraicGeometry.exists_etale_lift_of_smooth A B (I ^ N) σ hB
  let e := AlgEquiv.ofBijective α hα
  let q := Ideal.Quotient.mkₐ A ((I ^ N).map (algebraMap A A'))
  let σN := e.symm.toAlgHom.comp q
  let σ1 := (Ideal.Quotient.factorₐ A (Ideal.pow_le_self (Nat.ne_of_gt hN))).comp σN
  have : Algebra.Etale A A' := RingHom.etale_algebraMap.mp
    ((AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mp hA')
  obtain ⟨χ, _⟩ := Algebra.exists_etale_section_lift_of_gabber_roots A I
    (HenselianRing.jac (R := A) (I := I)) (gabber_roots_of_henselian I) A' σ1
  let χN := (Ideal.Quotient.mkₐ A (I ^ N)).comp χ
  have hkill : ∀ x ∈ (I ^ N).map (algebraMap A A'), χN x = 0 := by
    have hle : (I ^ N).map (algebraMap A A') ≤ RingHom.ker χN.toRingHom := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro a ha
      change χN (algebraMap A A' a) = 0
      rw [χN.commutes]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    intro x hx
    exact hle hx
  let χbar := Ideal.Quotient.liftₐ ((I ^ N).map (algebraMap A A')) χN hkill
  have hbar : χbar.comp α = AlgHom.id A (A ⧸ I ^ N) := by
    apply Ideal.Quotient.algHom_ext
    ext
  have hagree : ∀ x : A', χN x = σN x := by
    intro x
    obtain ⟨y, hy⟩ := hα.2 (q x)
    have hh := AlgHom.congr_fun hbar y
    change χbar (α y) = y at hh
    have hey : e.symm (q x) = y := by rw [← hy]; exact e.symm_apply_apply y
    change χN x = e.symm (q x)
    rw [hey]
    rw [hy] at hh
    exact hh
  let τ := χ.comp tildeσ
  refine ⟨fun k ↦ τ (b k), ?_, ?_⟩
  · intro j
    have he := congrArg τ (hb j)
    change τ.toRingHom (MvPolynomial.eval₂ (algebraMap A B) b (f j)) = τ 0 at he
    rw [map_zero, MvPolynomial.eval₂_comp_left] at he
    have hc : τ.toRingHom.comp (algebraMap A B) = RingHom.id A := by
      ext a
      exact τ.commutes a
    rw [hc] at he
    exact he
  · intro k
    have ht : σN (tildeσ (b k)) = σ (b k) := by
      have hh := congrFun htilde (b k)
      change q (tildeσ (b k)) = α (σ (b k)) at hh
      change e.symm (q (tildeσ (b k))) = σ (b k)
      rw [hh]
      exact e.symm_apply_apply _
    have heval : AdicCompletion.evalₐ I N
        (ahat k - algebraMap A (AdicCompletion I A) (τ (b k))) = 0 := by
      rw [map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
      apply sub_eq_zero.mpr
      calc
        AdicCompletion.evalₐ I N (ahat k) = σ (b k) := by
          change AdicCompletion.evalₐ I N (ahat k) = AdicCompletion.evalₐ I N (ψ (b k))
          rw [hψ k]
        _ = χN (tildeσ (b k)) := (hagree _).trans ht |>.symm
        _ = Ideal.Quotient.mk (I ^ N) (τ (b k)) := rfl
    have hev : AdicCompletion.eval I A N
        (ahat k - algebraMap A (AdicCompletion I A) (τ (b k))) = 0 := by
      rw [← AdicCompletion.factor_evalₐ_eq_eval (I := I)
        (ahat k - algebraMap A (AdicCompletion I A) (τ (b k))) (by simp)]
      rw [heval, map_zero]
    have hm := hev
    change _ ∈ (AdicCompletion.eval I A N).ker at hm
    rw [← AdicCompletion.pow_smul_top_eq_ker_eval (M := A) I.fg_of_isNoetherianRing,
      Ideal.smul_top_eq_map] at hm
    exact hm

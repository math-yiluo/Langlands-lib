/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Localization.Basic
import WeilConjectures.RingTheory.Derivation.Localization

/-!
# Extension of derivations to completions and localizations

Source: Stacks Project, More on Algebra, Lemma 07PE, parts (1) and (2)
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

universe u

namespace Derivation

private theorem lowers_powers {R : Type u} [CommRing R] (D : Derivation ℤ R R)
    (I : Ideal R) (n : ℕ) : ∀ x ∈ I ^ (n + 1), D x ∈ I ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [D.leibniz]
      apply Ideal.add_mem
      · exact Ideal.mul_mem_right _ _ ha
      · simpa only [smul_eq_mul, Ideal.IsTwoSided.pow_succ] using
          Ideal.mul_mem_mul hb (ih a ha)
    · intro a b ha hb
      simpa only [map_add] using Ideal.add_mem _ ha hb

private def quotientDerivative {R : Type u} [CommRing R] (D : Derivation ℤ R R)
    (I : Ideal R) (n : ℕ) : (R ⧸ I ^ (n + 1)) →+ (R ⧸ I ^ n) :=
  QuotientAddGroup.lift (I ^ (n + 1)).toAddSubgroup
    ((Ideal.Quotient.mk (I ^ n)).toAddMonoidHom.comp D.toLinearMap.toAddMonoidHom)
    (by
      intro x hx
      change Ideal.Quotient.mk (I ^ n) (D x) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (lowers_powers D I n x hx))

private theorem quotientDerivative_mk {R : Type u} [CommRing R] (D : Derivation ℤ R R)
    (I : Ideal R) (n : ℕ) (a : R) :
    quotientDerivative D I n (Ideal.Quotient.mk (I ^ (n + 1)) a) =
      Ideal.Quotient.mk (I ^ n) (D a) := rfl

-- Mathlib stores completion coordinates modulo `I ^ n • ⊤`.
private def rawQuotientDerivative {R : Type u} [CommRing R] (D : Derivation ℤ R R)
    (I : Ideal R) (n : ℕ) :
    (R ⧸ (I ^ (n + 1) • ⊤ : Ideal R)) →+ (R ⧸ (I ^ n • ⊤ : Ideal R)) :=
  QuotientAddGroup.lift (I ^ (n + 1) • ⊤ : Ideal R).toAddSubgroup
    ((Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R)).toAddMonoidHom.comp
      D.toLinearMap.toAddMonoidHom)
    (by
      intro x hx
      change Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) (D x) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      simpa using lowers_powers D I n x (by simpa using hx))

private theorem rawQuotientDerivative_mk {R : Type u} [CommRing R]
    (D : Derivation ℤ R R) (I : Ideal R) (n : ℕ) (a : R) :
    rawQuotientDerivative D I n
        (Ideal.Quotient.mk (I ^ (n + 1) • ⊤ : Ideal R) a) =
      Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) (D a) := rfl

private theorem rawQuotientDerivative_compatible {R : Type u} [CommRing R]
    (D : Derivation ℤ R R) (I : Ideal R) {m n : ℕ} (hmn : m ≤ n)
    (x : R ⧸ (I ^ (n + 1) • ⊤ : Ideal R)) :
    AdicCompletion.transitionMap I R hmn (rawQuotientDerivative D I n x) =
      rawQuotientDerivative D I m
        (AdicCompletion.transitionMap I R (Nat.succ_le_succ hmn) x) := by
  induction x using Quotient.inductionOn' with
  | _ a =>
    change AdicCompletion.transitionMap I R hmn
      (rawQuotientDerivative D I n (Ideal.Quotient.mk _ a)) = _
    rw [rawQuotientDerivative_mk, AdicCompletion.transitionMap_ideal_mk]
    change _ = rawQuotientDerivative D I m (Ideal.Quotient.mk _ a)
    rw [rawQuotientDerivative_mk]

private def completionMap {R : Type u} [CommRing R] (D : Derivation ℤ R R)
    (I : Ideal R) : AdicCompletion I R →+ AdicCompletion I R where
  toFun x := ⟨fun n ↦ rawQuotientDerivative D I n (x.val (n + 1)), by
    intro m n hmn
    rw [rawQuotientDerivative_compatible, x.property (Nat.succ_le_succ hmn)]⟩
  map_zero' := by
    apply Subtype.ext
    funext n
    exact map_zero _
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact map_add _ _ _

private theorem rawQuotientDerivative_leibniz {R : Type u} [CommRing R]
    (D : Derivation ℤ R R) (I : Ideal R) (n : ℕ)
    (x y : R ⧸ (I ^ (n + 1) • ⊤ : Ideal R)) :
    rawQuotientDerivative D I n (x * y) =
      AdicCompletion.transitionMap I R (Nat.le_succ n) x * rawQuotientDerivative D I n y +
      AdicCompletion.transitionMap I R (Nat.le_succ n) y * rawQuotientDerivative D I n x := by
  induction x using Quotient.inductionOn' with | _ a =>
    induction y using Quotient.inductionOn' with | _ b =>
      change Ideal.Quotient.mk _ (D (a * b)) = _
      rw [D.leibniz]
      simp only [smul_eq_mul]
      rfl

private theorem completionMap_leibniz {R : Type u} [CommRing R]
    (D : Derivation ℤ R R) (I : Ideal R) (x y : AdicCompletion I R) :
    completionMap D I (x * y) = x * completionMap D I y + y * completionMap D I x := by
  apply Subtype.ext
  funext n
  change rawQuotientDerivative D I n (x.val (n + 1) * y.val (n + 1)) = _
  rw [rawQuotientDerivative_leibniz, x.property (Nat.le_succ n),
    y.property (Nat.le_succ n)]
  rfl

private theorem rawQuotientDerivative_factor {R : Type u} [CommRing R]
    (D : Derivation ℤ R R) (I : Ideal R) (n : ℕ)
    (z : R ⧸ (I ^ (n + 1) • ⊤ : Ideal R)) :
    Submodule.factor (show (I ^ n • ⊤ : Ideal R) ≤ I ^ n by simp)
      (rawQuotientDerivative D I n z) =
    quotientDerivative D I n
      (Submodule.factor (show (I ^ (n + 1) • ⊤ : Ideal R) ≤ I ^ (n + 1) by simp) z) := by
  induction z using Quotient.inductionOn' with
  | _ a =>
    change Submodule.factor _
      (rawQuotientDerivative D I n (Ideal.Quotient.mk _ a)) = _
    rw [rawQuotientDerivative_mk]
    simp only [← Ideal.Quotient.mk_eq_mk, ← Submodule.mkQ_apply, Submodule.factor_mk]
    exact (quotientDerivative_mk D I n a).symm

private theorem completionMap_eval {R : Type u} [CommRing R]
    (D : Derivation ℤ R R) (I : Ideal R) (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ I n (completionMap D I x) =
      quotientDerivative D I n (AdicCompletion.evalₐ I (n + 1) x) := by
  rw [← AdicCompletion.factor_eval_eq_evalₐ I (completionMap D I x) (by simp),
    ← AdicCompletion.factor_eval_eq_evalₐ I x (by simp)]
  exact rawQuotientDerivative_factor D I n (x.val (n + 1))

private theorem exists_completion_extension (R : Type u) [CommRing R] (D : Derivation ℤ R R) :
    ∀ I : Ideal R,
      ∃ Dc : Derivation ℤ (AdicCompletion I R) (AdicCompletion I R),
        ∃ d : (n : ℕ) → (R ⧸ I ^ (n + 1)) →+ (R ⧸ I ^ n),
          (∀ a : R, Dc (algebraMap R (AdicCompletion I R) a) =
            algebraMap R (AdicCompletion I R) (D a)) ∧
          (∀ (n : ℕ), 1 ≤ n → ∀ a : R,
            d n (Ideal.Quotient.mk (I ^ (n + 1)) a) = Ideal.Quotient.mk (I ^ n) (D a)) ∧
          (∀ (n : ℕ), 1 ≤ n → ∀ x : AdicCompletion I R,
            AdicCompletion.evalₐ I n (Dc x) = d n (AdicCompletion.evalₐ I (n + 1) x)) := by
  intro I
  let f := completionMap D I
  let Dc : Derivation ℤ (AdicCompletion I R) (AdicCompletion I R) :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro n x
        rw [Algebra.smul_def]
        simpa using f.map_zsmul n x
      map_one_eq_zero' := by
        apply Subtype.ext
        funext n
        change rawQuotientDerivative D I n 1 = 0
        change rawQuotientDerivative D I n (Ideal.Quotient.mk _ 1) = _
        rw [rawQuotientDerivative_mk, D.map_one_eq_zero, map_zero]
      leibniz' := by
        intro x y
        exact completionMap_leibniz D I x y }
  refine ⟨Dc, quotientDerivative D I, ?_, ?_, ?_⟩
  · intro a
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ I n (completionMap D I
      (algebraMap R (AdicCompletion I R) a)) = _
    rw [completionMap_eval]
    simp only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply,
      AdicCompletion.evalₐ_of, quotientDerivative_mk]
  · intro n hn a
    exact quotientDerivative_mk D I n a
  · intro n hn x
    exact completionMap_eval D I n x

private theorem localized_extension {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra ℤ S] (W : Submonoid R) [IsLocalization W S] (D : Derivation ℤ R R) :
    ∃ Dw : Derivation ℤ S S,
      ∀ a, Dw (algebraMap R S a) = algebraMap R S (D a) := by
  let ψ : S →+* S := RingHom.id _
  let δ : R →+ S := (algebraMap R S).toAddMonoidHom.comp
    D.toLinearMap.toAddMonoidHom
  have hδ : ∀ x y, δ (x * y) = ψ (algebraMap R S x) • δ y +
    ψ (algebraMap R S y) • δ x := by
    intro x y
    simp only [δ, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
      RingHom.toAddMonoidHom_eq_coe, ψ, RingHom.id_apply, smul_eq_mul]
    change algebraMap R S (D (x * y)) = _
    rw [D.leibniz]
    simp [smul_eq_mul]
  let d : S →+ S :=
    IsLocalization.extendDerivation W ψ δ hδ
  let Dw : Derivation ℤ S S :=
    { toFun := d
      map_add' := d.map_add
      map_smul' := by
        intro n x
        rw [Algebra.smul_def]
        simpa using d.map_zsmul n x
      map_one_eq_zero' := by
        have h := IsLocalization.extendDerivation_mul W ψ δ hδ 1 1
        simp only [ψ, RingHom.id_apply, one_smul, one_mul] at h
        exact (add_eq_left.mp h.symm)
      leibniz' := by
        intro x y
        simpa [d, ψ, smul_eq_mul] using
          IsLocalization.extendDerivation_mul W ψ δ hδ x y }
  refine ⟨Dw, ?_⟩
  intro a
  change d (algebraMap R S a) = _
  exact IsLocalization.extendDerivation_algebraMap W ψ δ hδ a

/-- Stacks Project, More on Algebra, Lemma 07PE, parts (1) and (2)
(blueprint: theorem-finite-etale-covers-proper-henselian--2). An absolute derivation extends to
every adic completion by the maps between successive quotients, and uniquely to every localization
by the quotient rule. Absolute derivations are represented as derivations over `ℤ`.

Proof, following the node's eleven steps:
1. The Leibniz rule at `1 * 1` gives `D 1 = 0`.
2. Induction and the Leibniz rule on products generating `I ^ (n + 1)` give
   `D (I ^ (n + 1)) ⊆ I ^ n`.
3. Hence `D` induces additive maps `d n : R / I ^ (n + 1) → R / I ^ n`.
   Their Leibniz rule uses the reduction map, and they commute with reductions.
4. On compatible sequences set the n-th component of `Dc x` to `d n (x (n + 1))`.
   The preceding compatibility makes this a compatible sequence
   [def-weil-pbc-adic-completion].
5. Additivity and the Leibniz rule hold componentwise, since the reductions of
   `x (n + 1)` and `y (n + 1)` are `x n` and `y n`.
6. On the canonical image of `a`, each component is `D a mod I ^ n`, so `Dc` extends `D`.
7. Any localization extension is forced by differentiating `w * (1 / w) = 1`:
   its value at `a / w` is `D a / w - a * D w / w ^ 2`.
8. This formula is well defined. If `u * z = 0`, where `z = a * w' - a' * w`,
   differentiating and multiplying by `u` gives `u ^ 2 * D z = 0`.
   The difference of the two quotient-rule numerators is
   `w * w' * D z - z * D (w * w')`, which is killed by `u ^ 2`.
9. Expanding the numerator for `(a * v + b * w) / (w * v)` gives additivity.
10. Expanding the numerator for `a * b / (w * v)` gives the Leibniz rule.
11. At `a / 1` the formula gives `D a / 1`, since `D 1 = 0`, so it extends `D`.
-/
theorem exists_completion_and_unique_localization (R : Type u) [CommRing R]
    (D : Derivation ℤ R R) :
    (∀ I : Ideal R,
      ∃ Dc : Derivation ℤ (AdicCompletion I R) (AdicCompletion I R),
        ∃ d : (n : ℕ) → (R ⧸ I ^ (n + 1)) →+ (R ⧸ I ^ n),
          (∀ a : R, Dc (algebraMap R (AdicCompletion I R) a) =
            algebraMap R (AdicCompletion I R) (D a)) ∧
          (∀ (n : ℕ), 1 ≤ n → ∀ a : R,
            d n (Ideal.Quotient.mk (I ^ (n + 1)) a) = Ideal.Quotient.mk (I ^ n) (D a)) ∧
          (∀ (n : ℕ), 1 ≤ n → ∀ x : AdicCompletion I R,
            AdicCompletion.evalₐ I n (Dc x) = d n (AdicCompletion.evalₐ I (n + 1) x))) ∧
    (∀ W : Submonoid R,
      ∃ Dw : Derivation ℤ (Localization W) (Localization W),
        (∀ a : R, Dw (algebraMap R (Localization W) a) =
          algebraMap R (Localization W) (D a)) ∧
        (∀ (a : R) (w : W), Dw (Localization.mk a w) =
          Localization.mk (D a) w - Localization.mk (a * D (w : R)) (w ^ 2)) ∧
        (∀ Dw' : Derivation ℤ (Localization W) (Localization W),
          (∀ a : R, Dw' (algebraMap R (Localization W) a) =
            algebraMap R (Localization W) (D a)) → Dw' = Dw)) := by
  constructor
  · exact exists_completion_extension R D
  · intro W
    -- Reuse the proved square-zero construction for localization existence.
    obtain ⟨Dw, hext⟩ := localized_extension (S := Localization W) W D
    let ψ : Localization W →+* Localization W := RingHom.id _
    refine ⟨Dw, hext, ?_, ?_⟩
    · intro a w
      simp only [Localization.mk_eq_mk']
      have hinv : IsLocalization.mk' (Localization W) 1 w *
          algebraMap R (Localization W) (w : R) = 1 := by
        simp [IsLocalization.mk'_spec]
      rw [IsLocalization.mk'_eq_mul_mk'_one, Dw.leibniz,
        Dw.leibniz_of_mul_eq_one hinv, hext, hext]
      simp only [smul_eq_mul, neg_mul, mul_neg]
      rw [IsLocalization.mk'_eq_mul_mk'_one (D a) w,
        IsLocalization.mk'_eq_mul_mk'_one (a * D (w : R)) (w ^ 2), map_mul,
        ← IsLocalization.mk'_pow, one_pow]
      ring
    · intro Dw' h
      apply Derivation.coe_injective
      exact IsLocalization.derivation_ext W ψ
        (by intro x y; simp [ψ, smul_eq_mul, Dw'.leibniz])
        (by intro x y; simp [ψ, smul_eq_mul, Dw.leibniz])
        (by intro a; rw [h, hext])

end Derivation

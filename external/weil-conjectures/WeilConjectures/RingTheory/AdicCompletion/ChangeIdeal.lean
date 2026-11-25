/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Changing the ideal of an adic completion

Let `I, J ⊆ A` be ideals with `I ^ c ≤ J` and `J ^ d ≤ I`. Then the `I`-adic and the `J`-adic
completions of an `A`-module `M` are canonically isomorphic, compatibly with the maps from `M`
(Stacks, Lemma 0319).

## Main definitions and results

- `AdicCompletion.changeIdealMap`: the map `M^∧_J → M^∧_I`, `(xₙ)ₙ ↦ (x_{dk} mod I^k M)ₖ`, for
  `J ^ d ≤ I`.
- `AdicCompletion.changeIdealCompletion`: the linear equivalence `M^∧_J ≃ M^∧_I`.
- `AdicCompletion.changeIdealCompletionRingEquiv`: for `M = A`, the ring isomorphism.
- `AdicCompletion.isAdicComplete_iff_of_pow_le`: `M` is `I`-adically complete iff it is
  `J`-adically complete.

## References

- Stacks Project, Lemma 10.96.9, <https://stacks.math.columbia.edu/tag/0319>
-/

@[expose] public section

namespace AdicCompletion

variable {A : Type*} [CommRing A] {I J : Ideal A} {M : Type*} [AddCommGroup M] [Module A M]
  {c d : ℕ}

lemma pow_mul_smul_top_le (h : J ^ d ≤ I) (k : ℕ) :
    (J ^ (d * k) • ⊤ : Submodule A M) ≤ I ^ k • ⊤ :=
  Submodule.smul_mono_left (by rw [pow_mul]; exact Ideal.pow_right_mono h k)

/-- Reducing two coordinates of a compatible family to a common coarser quotient gives the
same element. -/
lemma factor_val_eq_factor_val (x : AdicCompletion J M) {m n : ℕ} (hmn : m ≤ n)
    {N : Submodule A M} (hm : (J ^ m • ⊤ : Submodule A M) ≤ N)
    (hn : (J ^ n • ⊤ : Submodule A M) ≤ N) :
    Submodule.factor hn (x.val n) = Submodule.factor hm (x.val m) := by
  rw [← x.prop hmn, transitionMap, Submodule.factorPow, Submodule.factor_comp_apply]

variable (I J M) in
/-- The map `M^∧_J → M^∧_I`, `(xₙ)ₙ ↦ (x_{dk} mod I^k M)ₖ`, for `J ^ d ≤ I`. -/
noncomputable def changeIdealMap (h : J ^ d ≤ I) : AdicCompletion J M →ₗ[A] AdicCompletion I M :=
  lift I (fun k ↦ Submodule.factor (pow_mul_smul_top_le (M := M) h k) ∘ₗ eval J M (d * k))
    (fun {m n} hle ↦ by
      ext x
      simp only [LinearMap.coe_comp, Function.comp_apply, eval_apply, transitionMap,
        Submodule.factorPow, Submodule.factor_comp_apply]
      exact factor_val_eq_factor_val x (Nat.mul_le_mul_left d hle) _ _)

lemma changeIdealMap_val (h : J ^ d ≤ I) (x : AdicCompletion J M) (k : ℕ) :
    (changeIdealMap I J M h x).val k =
      Submodule.factor (pow_mul_smul_top_le (M := M) h k) (x.val (d * k)) :=
  rfl

lemma changeIdealMap_of (h : J ^ d ≤ I) (x : M) :
    changeIdealMap I J M h (of J M x) = of I M x := by
  ext k
  rw [changeIdealMap_val, of_apply, of_apply]
  rfl

lemma changeIdealMap_comp_changeIdealMap (hc : I ^ c ≤ J) (hd : J ^ d ≤ I) (hcd : 1 ≤ c * d)
    (x : AdicCompletion J M) :
    changeIdealMap J I M hc (changeIdealMap I J M hd x) = x := by
  ext n
  rw [changeIdealMap_val, changeIdealMap_val, Submodule.factor_comp_apply]
  have hle : n ≤ d * (c * n) := by
    calc n = 1 * n := (one_mul n).symm
      _ ≤ (c * d) * n := Nat.mul_le_mul_right n hcd
      _ = d * (c * n) := by ring
  rw [factor_val_eq_factor_val x hle le_rfl]
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
  rw [← hy, ← Submodule.mkQ_apply, Submodule.factor_mk]

/-- **Completions along two ideals each containing a power of the other agree.**
Let `I, J ⊆ A` be ideals and `c, d ≥ 1` with `I ^ c ≤ J` and `J ^ d ≤ I`. Then
`θ : M^∧_J → M^∧_I`, `(xₙ)ₙ ↦ (x_{dk} mod I^k M)ₖ`, is an isomorphism of `A`-modules with
inverse `(yₖ)ₖ ↦ (y_{cn} mod J^n M)ₙ`; it satisfies `θ ∘ ι_J = ι_I` (`changeIdealMap_of`).
(blueprint: `lem-weil-pbc-change-ideal-completion`) -/
noncomputable def changeIdealCompletion (hc : I ^ c ≤ J) (hd : J ^ d ≤ I) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) : AdicCompletion J M ≃ₗ[A] AdicCompletion I M :=
  LinearEquiv.ofLinearMap (changeIdealMap I J M hd) (changeIdealMap J I M hc)
    (LinearMap.ext fun y ↦ changeIdealMap_comp_changeIdealMap hd hc
      (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))) y)
    (LinearMap.ext fun x ↦ changeIdealMap_comp_changeIdealMap hc hd
      (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))) x)

lemma changeIdealCompletion_apply (hc : I ^ c ≤ J) (hd : J ^ d ≤ I) (hc1 : 1 ≤ c) (hd1 : 1 ≤ d)
    (x : AdicCompletion J M) :
    changeIdealCompletion hc hd hc1 hd1 x = changeIdealMap I J M hd x :=
  rfl

lemma changeIdealCompletion_symm_apply (hc : I ^ c ≤ J) (hd : J ^ d ≤ I) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (y : AdicCompletion I M) :
    (changeIdealCompletion hc hd hc1 hd1).symm y = changeIdealMap J I M hc y :=
  rfl

/-- The isomorphism `θ` is compatible with the canonical maps from `M`: `θ ∘ ι_J = ι_I`.
(blueprint: `lem-weil-pbc-change-ideal-completion`) -/
lemma changeIdealCompletion_of (hc : I ^ c ≤ J) (hd : J ^ d ≤ I) (hc1 : 1 ≤ c) (hd1 : 1 ≤ d)
    (x : M) : changeIdealCompletion hc hd hc1 hd1 (of J M x) = of I M x :=
  changeIdealMap_of hd x

/-- If `I ^ c ≤ J` and `J ^ d ≤ I`, then `M` is `I`-adically complete if and only if it is
`J`-adically complete. (blueprint: `lem-weil-pbc-change-ideal-completion`) -/
theorem isAdicComplete_iff_of_pow_le (hc : I ^ c ≤ J) (hd : J ^ d ≤ I) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) : IsAdicComplete I M ↔ IsAdicComplete J M := by
  have heq : (of I M : M → AdicCompletion I M) =
      changeIdealCompletion hc hd hc1 hd1 ∘ of J M :=
    funext fun x ↦ (changeIdealCompletion_of hc hd hc1 hd1 x).symm
  rw [← of_bijective_iff, ← of_bijective_iff, heq]
  exact (changeIdealCompletion hc hd hc1 hd1).bijective.of_comp_iff' _

/-- For `M = A`, the isomorphism `θ : A^∧_J ≃ A^∧_I` of `changeIdealCompletion` is a ring
isomorphism. (blueprint: `lem-weil-pbc-change-ideal-completion`) -/
noncomputable def changeIdealCompletionRingEquiv (hc : I ^ c ≤ J) (hd : J ^ d ≤ I) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) : AdicCompletion J A ≃+* AdicCompletion I A where
  __ := changeIdealCompletion (M := A) hc hd hc1 hd1
  map_mul' x y := by
    ext k
    change (changeIdealMap I J A hd (x * y)).val k =
      (changeIdealMap I J A hd x * changeIdealMap I J A hd y).val k
    rw [val_mul, changeIdealMap_val, changeIdealMap_val, changeIdealMap_val, val_mul]
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x.val (d * k))
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (y.val (d * k))
    rw [← ha, ← hb]
    rfl

lemma changeIdealCompletionRingEquiv_apply (hc : I ^ c ≤ J) (hd : J ^ d ≤ I) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (x : AdicCompletion J A) :
    changeIdealCompletionRingEquiv hc hd hc1 hd1 x = changeIdealCompletion hc hd hc1 hd1 x :=
  rfl

end AdicCompletion

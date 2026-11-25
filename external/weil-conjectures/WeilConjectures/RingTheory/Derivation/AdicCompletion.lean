/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.Basic
public import WeilConjectures.Mathlib.RingTheory.Derivation.Basic
public import WeilConjectures.RingTheory.Derivation.Localization
public import Mathlib.Tactic.LinearCombination

/-!
# Extending derivations to adic completions and localizations

Let `D : R → R` be a derivation of a commutative ring.

* For an ideal `I ⊆ R`, the maps `Dₙ : R / I ^ (n + 1) → R / I ^ n`, `a ↦ D a`, induce a
  derivation `D^∧` of the `I`-adic completion with `D^∧ ∘ c = c ∘ D`.
* For a multiplicative subset `W ⊆ R`, there is a unique derivation `D_W` of `W⁻¹R` extending
  `D`, given by the quotient rule.

## Main definitions and results

- `Derivation.quotPowSucc`: the maps `Dₙ`.
- `Derivation.adicCompletion`: the derivation `D^∧`.
- `Derivation.localization`: the derivation `D_W`.

The packaged statement of Stacks, Lemma 07PE (1), (2) is
`Derivation.exists_completion_and_unique_localization` in
`WeilConjectures.RingTheory.Derivation.CompletionAndLocalization`.

## References

- Stacks Project, Lemma 15.49.1, <https://stacks.math.columbia.edu/tag/07PE>
-/

@[expose] public section

namespace Derivation

variable {R : Type*} [CommRing R] (D : Derivation ℤ R R)

section AdicCompletion

variable (I : Ideal R)

lemma map_sub_mem_pow_smul_top {n : ℕ} {a b : R}
    (h : a - b ∈ (I ^ (n + 1) • ⊤ : Ideal R)) : D a - D b ∈ (I ^ n • ⊤ : Ideal R) := by
  rw [smul_eq_mul, Ideal.mul_top] at h ⊢
  rw [← map_sub]
  exact D.map_mem_pow_of_mem_pow_succ h

/-- The map `Dₙ : R / I ^ (n + 1) → R / I ^ n`, `a mod I ^ (n + 1) ↦ D a mod I ^ n`. -/
noncomputable def quotPowSucc (n : ℕ) :
    R ⧸ (I ^ (n + 1) • ⊤ : Ideal R) →+ R ⧸ (I ^ n • ⊤ : Ideal R) :=
  QuotientAddGroup.lift (I ^ (n + 1) • ⊤ : Ideal R).toAddSubgroup
    ((Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R)).toAddMonoidHom.comp D.toAddMonoidHom)
    (fun a ha ↦ by
      simpa [Ideal.Quotient.eq_zero_iff_mem] using
        D.map_sub_mem_pow_smul_top I (a := a) (b := 0) (by simpa using ha))

lemma quotPowSucc_mk (n : ℕ) (a : R) :
    D.quotPowSucc I n (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (D a) :=
  rfl

lemma quotPowSucc_mul (n : ℕ) (s t : R ⧸ (I ^ (n + 1) • ⊤ : Ideal R)) :
    D.quotPowSucc I n (s * t) =
      AdicCompletion.transitionMap I R (Nat.le_succ n) s * D.quotPowSucc I n t +
        AdicCompletion.transitionMap I R (Nat.le_succ n) t * D.quotPowSucc I n s := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [← map_mul, quotPowSucc_mk, quotPowSucc_mk, quotPowSucc_mk,
    AdicCompletion.transitionMap_ideal_mk, AdicCompletion.transitionMap_ideal_mk, leibniz,
    map_add]
  simp only [smul_eq_mul]
  rfl

lemma transitionMap_quotPowSucc {m n : ℕ} (hmn : m ≤ n)
    (s : R ⧸ (I ^ (n + 1) • ⊤ : Ideal R)) :
    AdicCompletion.transitionMap I R hmn (D.quotPowSucc I n s) =
      D.quotPowSucc I m (AdicCompletion.transitionMap I R (Nat.succ_le_succ hmn) s) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [quotPowSucc_mk, AdicCompletion.transitionMap_ideal_mk,
    AdicCompletion.transitionMap_ideal_mk, quotPowSucc_mk]

/-- The additive map `D^∧ : R^∧ → R^∧`, `(xₙ)ₙ ↦ (Dₙ (x_{n+1}))ₙ`. -/
noncomputable def adicCompletionAddMonoidHom :
    AdicCompletion I R →+ AdicCompletion I R where
  toFun x := ⟨fun n ↦ D.quotPowSucc I n (x.val (n + 1)), fun {m n} hmn ↦ by
    rw [transitionMap_quotPowSucc, x.prop]⟩
  map_zero' := by
    ext n
    exact _root_.map_zero (D.quotPowSucc I n)
  map_add' x y := by
    ext n
    exact _root_.map_add (D.quotPowSucc I n) _ _

/-- **A derivation extends to the adic completion.** The derivation `D^∧` of the `I`-adic
completion induced by the maps `Dₙ : R / I ^ (n + 1) → R / I ^ n`. -/
noncomputable def adicCompletion : Derivation ℤ (AdicCompletion I R) (AdicCompletion I R) :=
  Derivation.mk' (D.adicCompletionAddMonoidHom I).toIntLinearMap fun x y ↦ by
    ext n
    simp only [AddMonoidHom.coe_toIntLinearMap, smul_eq_mul, AdicCompletion.val_add_apply,
      AdicCompletion.val_mul]
    simp only [adicCompletionAddMonoidHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      AdicCompletion.val_mul]
    rw [quotPowSucc_mul, x.prop, y.prop]

lemma adicCompletion_val (x : AdicCompletion I R) (n : ℕ) :
    (D.adicCompletion I x).val n = D.quotPowSucc I n (x.val (n + 1)) :=
  rfl

lemma adicCompletion_algebraMap (a : R) :
    D.adicCompletion I (algebraMap R (AdicCompletion I R) a) =
      algebraMap R (AdicCompletion I R) (D a) := by
  ext n
  rw [adicCompletion_val, AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply,
    AdicCompletion.of_apply, AdicCompletion.of_apply]
  exact quotPowSucc_mk D I n a

end AdicCompletion

section Localization

variable (W : Submonoid R) (L : Type*) [CommRing L] [Algebra R L] [IsLocalization W L]

/-- The composite `R → R → W⁻¹R`, `a ↦ D a / 1`. -/
noncomputable def toLocalization : R →+ L :=
  (algebraMap R L).toAddMonoidHom.comp D.toAddMonoidHom

lemma toLocalization_mul (x y : R) :
    D.toLocalization L (x * y) = RingHom.id L (algebraMap R L x) • D.toLocalization L y +
      RingHom.id L (algebraMap R L y) • D.toLocalization L x := by
  simp [toLocalization, leibniz]

/-- **A derivation extends to a localization.** The derivation `D_W` of `W⁻¹R` with
`D_W (a / 1) = D a / 1`. -/
noncomputable def localization : Derivation ℤ L L :=
  Derivation.mk' (IsLocalization.extendDerivation W (RingHom.id L) (D.toLocalization L)
      (D.toLocalization_mul L)).toIntLinearMap fun x y ↦ by
    simpa [mul_comm] using IsLocalization.extendDerivation_mul W (RingHom.id L)
      (D.toLocalization L) (D.toLocalization_mul L) x y

lemma localization_algebraMap (a : R) :
    D.localization W L (algebraMap R L a) = algebraMap R L (D a) :=
  IsLocalization.extendDerivation_algebraMap W (RingHom.id L) (D.toLocalization L)
    (D.toLocalization_mul L) a

/-- A derivation of `W⁻¹R` extending `D` is equal to `D.localization W L`. -/
lemma eq_localization (δ : Derivation ℤ L L)
    (hδ : ∀ a, δ (algebraMap R L a) = algebraMap R L (D a)) : δ = D.localization W L := by
  have := IsLocalization.derivation_ext (N := L) W (RingHom.id L) (δ₁ := δ)
    (δ₂ := D.localization W L) (fun x y ↦ by simp [leibniz])
    (fun x y ↦ by simp [leibniz]) (fun a ↦ by rw [hδ, localization_algebraMap])
  ext x
  exact congrFun this x

/-- The quotient rule: `D_W (a / w) = D a / w - a D w / w ^ 2`. -/
lemma localization_mk' (a : R) (w : W) :
    D.localization W L (IsLocalization.mk' L a w) =
      IsLocalization.mk' L (D a) w - IsLocalization.mk' L (a * D w) (w ^ 2) := by
  have hu : IsUnit (algebraMap R L w) := IsLocalization.map_units L w
  have h := congrArg (D.localization W L) (IsLocalization.mk'_spec L a w)
  rw [leibniz, localization_algebraMap, localization_algebraMap, smul_eq_mul,
    smul_eq_mul] at h
  have h1 := IsLocalization.mk'_spec L (D a) w
  have h2 := IsLocalization.mk'_spec L (a * D w) (w ^ 2)
  have h3 := IsLocalization.mk'_spec L a w
  rw [SubmonoidClass.coe_pow, map_pow, map_mul] at h2
  refine (hu.pow 2).mul_left_injective ?_
  dsimp only
  linear_combination algebraMap R L w * h - algebraMap R L w * h1 + h2 -
    algebraMap R L (D w) * h3

end Localization

end Derivation

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# A cyclic presentation of an ideal-power torsion module

Source: Stacks Project, More on Algebra, Tag 05E8, proof, first two sentences
(blueprint: lem-weil-pbc-torsion-cyclic-presentation).
-/

@[expose] public section

universe u v

open DirectSum

namespace Ideal

/-- An ideal-power torsion module has a surjection from a direct sum of positive-power
ideal quotients, with ideal-power torsion kernel and the resulting short exact sequence.
Source: Stacks Project, Tag 05E8, proof, first two sentences
(blueprint: lem-weil-pbc-torsion-cyclic-presentation).

Proof: Index the summands by the elements `q` of `Q`. Choose the least positive `n_q`
annihilating `q`. The map `R / I ^ n_q → Q` taking the class of `r` to `r • q` is well
defined and linear, since every element of `I ^ n_q` kills `q`
[def-weil-pbc-quotient-module]. Combine these maps by the direct sum universal property
[def-weil-pbc-direct-sum-modules]; the image of `1` in the `q`-summand is `q`, so the
resulting map is surjective. By direct-sum induction, zero is killed by `I ^ 1`,
a single summand is killed by its defining ideal power, and a sum of elements killed
by `I ^ m` and `I ^ l` is killed by `I ^ max m l`. Indeed, the latter ideal power
is contained in each of the former powers. Thus the direct sum and its kernel are
ideal-power torsion. The kernel inclusion and the surjective presentation map form
a short exact sequence [def-weil-pbc-exact-sequence], by Mathlib's
`LinearMap.shortExact_shortComplexKer`. -/
theorem exists_torsion_cyclic_presentation {R : Type u} [CommRing R] (I : Ideal R)
    (Q : Type (max u v)) [AddCommGroup Q] [Module R Q]
    (hQ : ∀ q : Q, ∃ n : ℕ, 0 < n ∧ ∀ a ∈ I ^ n, a • q = 0) :
    ∃ (J : Type (max u v)) (n : J → ℕ), (∀ j : J, 0 < n j) ∧
      ∃ p : (⨁ j : J, R ⧸ I ^ n j) →ₗ[R] Q,
        Function.Surjective p ∧
        (∀ k : LinearMap.ker p, ∃ m : ℕ, 0 < m ∧ ∀ a ∈ I ^ m, a • k = 0) ∧
        p.shortComplexKer.ShortExact := by
  classical
  let n : Q → ℕ := fun q => Nat.find (hQ q)
  have hn (q : Q) : 0 < n q ∧ ∀ a ∈ I ^ n q, a • q = 0 :=
    Nat.find_spec (hQ q)
  let φ (q : Q) : (R ⧸ I ^ n q) →ₗ[R] Q :=
    (I ^ n q).liftQ (LinearMap.toSpanSingleton R Q q) (by
      intro a ha
      exact (hn q).2 a ha)
  let p : (⨁ q : Q, R ⧸ I ^ n q) →ₗ[R] Q := DirectSum.toModule R Q Q φ
  have hp : Function.Surjective p := by
    intro q
    refine ⟨DirectSum.lof R Q (fun q => R ⧸ I ^ n q) q
      ((I ^ n q).mkQ 1), ?_⟩
    change DirectSum.toModule R Q Q φ
      (DirectSum.lof R Q (fun q => R ⧸ I ^ n q) q ((I ^ n q).mkQ 1)) = q
    rw [DirectSum.toModule_lof]
    exact LinearMap.toSpanSingleton_apply_one R Q q
  have hP (x : ⨁ q : Q, R ⧸ I ^ n q) :
      ∃ m : ℕ, 0 < m ∧ ∀ a ∈ I ^ m, a • x = 0 := by
    induction x using DirectSum.induction_on with
    | zero => exact ⟨1, Nat.zero_lt_one, fun a _ => smul_zero a⟩
    | of q x =>
      refine ⟨n q, (hn q).1, ?_⟩
      intro a ha
      rw [← DirectSum.of_smul]
      have hx : a • x = 0 := by
        obtain ⟨r, rfl⟩ := (I ^ n q).mkQ_surjective x
        rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact (I ^ n q).mul_mem_right r ha
      rw [hx, map_zero]
    | add x y hx hy =>
      obtain ⟨m, hm, hx⟩ := hx
      obtain ⟨l, hl, hy⟩ := hy
      refine ⟨max m l, lt_of_lt_of_le hm (le_max_left _ _), ?_⟩
      intro a ha
      rw [smul_add, hx a (I.pow_le_pow_right (le_max_left _ _) ha),
        hy a (I.pow_le_pow_right (le_max_right _ _) ha), zero_add]
  refine ⟨Q, n, fun q => (hn q).1, p, hp, ?_,
    LinearMap.shortExact_shortComplexKer hp⟩
  intro k
  obtain ⟨m, hm, hk⟩ := hP k.val
  refine ⟨m, hm, fun a ha => ?_⟩
  apply Subtype.ext
  exact hk a ha

end Ideal

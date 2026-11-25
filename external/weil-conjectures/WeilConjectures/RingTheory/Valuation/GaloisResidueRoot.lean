/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.Polynomial.Identities
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Simple roots with a residual approximation in a subfield

Let `Ω` be an algebraically closed field, `𝒪` a valuation subring of `Ω` and `N` a subfield of
`Ω` over which `Ω` is algebraic, such that every automorphism of `Ω/N` maps `𝒪` into itself.

* `ValuationSubring.mem_of_isRoot_of_valuation_sub_lt_one`: if `f` has coefficients in `N ∩ 𝒪`,
  `α` is a root of `f` with `f'(α)` a unit of `𝒪`, and `α` is congruent modulo the maximal ideal
  of `𝒪` to an element of `N ∩ 𝒪`, then `α ∈ N`.
* `ValuationSubring.exists_pow_sub_self_eq`: Artin–Schreier equations with a residual solution
  in `N ∩ 𝒪` have a solution in `N`.
* `ValuationSubring.exists_pow_eq`: `ℓ`-th roots of units of `N ∩ 𝒪` with a residual root in
  `N ∩ 𝒪` exist in `N` when `ℓ` is invertible in the residue field.

Membership in the maximal ideal is expressed as `𝒪.valuation x < 1`, and units of `𝒪` as
`𝒪.valuation x = 1`.
-/

@[expose] public section

open Polynomial

/-- A separable element of a normal extension which is fixed by every automorphism lies in the
base field. -/
theorem mem_range_algebraMap_of_forall_algEquiv_apply_eq {F E : Type*} [Field F] [Field E]
    [Algebra F E] [Normal F E] {x : E} (hx : IsSeparable F x) (h : ∀ σ : Gal(E/F), σ x = x) :
    x ∈ (algebraMap F E).range := by
  classical
  have hint := Algebra.IsIntegral.isIntegral (R := F) x
  rw [← minpoly.natDegree_eq_one_iff, ← card_rootSet_eq_natDegree hx (Normal.splits' x),
    Fintype.card_eq_one_iff]
  refine ⟨⟨x, (mem_rootSet.2 ⟨minpoly.ne_zero hint, minpoly.aeval F x⟩)⟩, ?_⟩
  rintro ⟨y, hy⟩
  rw [mem_rootSet] at hy
  have hxy : minpoly F y = minpoly F x :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hy.2 (minpoly.monic hint)).symm
  obtain ⟨σ, rfl⟩ := (Normal.minpoly_eq_iff_mem_orbit E).1 hxy
  exact Subtype.ext (h σ)

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] (𝒪 : ValuationSubring Ω)

/-- A ring automorphism of `Ω` preserving `𝒪` (in both directions) preserves its maximal ideal. -/
theorem valuation_apply_lt_one (σ : Ω ≃+* Ω) (hσ : ∀ x ∈ 𝒪, σ x ∈ 𝒪)
    (hσ' : ∀ x ∈ 𝒪, σ.symm x ∈ 𝒪) {x : Ω} (hx : 𝒪.valuation x < 1) :
    𝒪.valuation (σ x) < 1 := by
  by_contra h
  rw [not_lt] at h
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at h
    exact zero_lt_one.not_ge h
  have h1 : 𝒪.valuation (σ x) = 1 :=
    le_antisymm ((valuation_le_one_iff _ _).2 (hσ x ((valuation_le_one_iff _ _).1 hx.le))) h
  have hinv : (σ x)⁻¹ ∈ 𝒪 := by
    rw [← valuation_le_one_iff, map_inv₀, h1, inv_one]
  have hxinv := hσ' _ hinv
  rw [map_inv₀, RingEquiv.symm_apply_apply, ← valuation_le_one_iff, map_inv₀,
    inv_le_one₀ ((Valuation.pos_iff _).2 hx0)] at hxinv
  exact hx.not_ge hxinv

/-- **Uniqueness of residually close simple roots.** If `f` has coefficients in `𝒪`, `α, β ∈ 𝒪`
are roots of `f` with `β ≡ α` modulo the maximal ideal and `f'(α)` is a unit of `𝒪`, then
`β = α`. -/
theorem eq_of_isRoot_of_valuation_sub_lt_one {f : Ω[X]} (hf𝒪 : ∀ i, f.coeff i ∈ 𝒪) {α β : Ω}
    (hα : α ∈ 𝒪) (hβ : β ∈ 𝒪) (hfα : f.IsRoot α) (hfβ : f.IsRoot β)
    (hf' : 𝒪.valuation (f.derivative.eval α) = 1) (hαβ : 𝒪.valuation (β - α) < 1) :
    β = α := by
  obtain ⟨g, rfl⟩ : ∃ g : 𝒪[X], g.map (algebraMap 𝒪 Ω) = f :=
    (mem_lifts _).1 ((lifts_iff_coeff_lifts _).2 fun i => ⟨⟨_, hf𝒪 i⟩, rfl⟩)
  have hβα : β - α ∈ 𝒪 := sub_mem hβ hα
  obtain ⟨k, hk⟩ := g.binomExpansion ⟨α, hα⟩ ⟨β - α, hβα⟩
  have hk' := congrArg (algebraMap 𝒪 Ω) hk
  simp only [map_add, map_mul, map_pow] at hk'
  have hev (y : 𝒪) (p : 𝒪[X]) : algebraMap 𝒪 Ω (p.eval y) = (p.map (algebraMap 𝒪 Ω)).eval
      (algebraMap 𝒪 Ω y) := by
    rw [eval_map, eval₂_at_apply]
  rw [hev, hev, hev, ← derivative_map] at hk'
  have hαc : algebraMap 𝒪 Ω ⟨α, hα⟩ = α := rfl
  have hβc : algebraMap 𝒪 Ω (⟨α, hα⟩ + ⟨β - α, hβα⟩) = β := by simp
  have hdc : algebraMap 𝒪 Ω ⟨β - α, hβα⟩ = β - α := rfl
  rw [hβc, hαc, hdc, hfβ.eq_zero, hfα.eq_zero, zero_add] at hk'
  by_contra hne
  have hne' : β - α ≠ 0 := sub_ne_zero.2 hne
  have key : (map (algebraMap 𝒪 Ω) g).derivative.eval α = -(algebraMap 𝒪 Ω k * (β - α)) := by
    have : (β - α) * ((map (algebraMap 𝒪 Ω) g).derivative.eval α +
        algebraMap 𝒪 Ω k * (β - α)) = 0 := by
      rw [hk']
      ring
    rw [eq_neg_iff_add_eq_zero]
    exact (mul_eq_zero.1 this).resolve_left hne'
  rw [key, Valuation.map_neg, Valuation.map_mul] at hf'
  have hk1 : 𝒪.valuation (algebraMap 𝒪 Ω k) ≤ 1 := (valuation_le_one_iff _ _).2 k.2
  exact ((mul_le_of_le_one_left' hk1).trans_lt hαβ).ne hf'

/-- **Galois–residue lemma.** Let `Ω` be algebraically closed and algebraic over a subfield `N`,
such that every automorphism of `Ω/N` maps `𝒪` into itself. Let `f` have coefficients in
`N ∩ 𝒪` and let `α` be a root of `f` with `f'(α)` a unit of `𝒪`, congruent modulo the maximal
ideal of `𝒪` to some `n ∈ N ∩ 𝒪`. Then `α ∈ N`. -/
theorem mem_of_isRoot_of_valuation_sub_lt_one [IsAlgClosed Ω] (N : Subfield Ω)
    [Algebra.IsAlgebraic N Ω] (h𝒪 : ∀ σ : Ω ≃ₐ[N] Ω, ∀ x ∈ 𝒪, σ x ∈ 𝒪)
    {f : Ω[X]} (hfN : ∀ i, f.coeff i ∈ N) (hf𝒪 : ∀ i, f.coeff i ∈ 𝒪)
    {α : Ω} (hα : f.IsRoot α) (hf' : 𝒪.valuation (f.derivative.eval α) = 1)
    {n : Ω} (hnN : n ∈ N) (hn𝒪 : n ∈ 𝒪) (hαn : 𝒪.valuation (α - n) < 1) : α ∈ N := by
  have : IsAlgClosure N Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨fN, rfl⟩ : ∃ fN : N[X], fN.map (algebraMap N Ω) = f :=
    (mem_lifts _).1 ((lifts_iff_coeff_lifts _).2 fun i => ⟨⟨_, hfN i⟩, rfl⟩)
  have hα𝒪 : α ∈ 𝒪 := by
    rw [← sub_add_cancel α n]
    exact 𝒪.add_mem _ _ ((valuation_le_one_iff _ _).1 hαn.le) hn𝒪
  have hfα : aeval α fN = 0 := by rwa [aeval_def, ← eval_map]
  have hint := Algebra.IsIntegral.isIntegral (R := N) α
  have hsep : IsSeparable N α := by
    obtain ⟨q, hq⟩ := minpoly.dvd N α hfα
    rw [IsSeparable, separable_iff_derivative_ne_zero (minpoly.irreducible hint)]
    intro h0
    have hder : (fN.map (algebraMap N Ω)).derivative.eval α = 0 := by
      rw [derivative_map, eval_map, ← aeval_def, hq, derivative_mul, h0, zero_mul, zero_add,
        map_mul, minpoly.aeval, zero_mul]
    rw [hder, map_zero] at hf'
    exact zero_ne_one hf'
  have hfix (σ : Gal(Ω/N)) : σ α = α := by
    have hσn : σ n = n := σ.commutes ⟨n, hnN⟩
    refine eq_of_isRoot_of_valuation_sub_lt_one 𝒪 hf𝒪 hα𝒪 (h𝒪 σ α hα𝒪) hα ?_ hf' ?_
    · rw [IsRoot, eval_map, ← aeval_def, aeval_algEquiv, AlgHom.comp_apply, hfα, map_zero]
    · have hσ : 𝒪.valuation (σ (α - n)) < 1 :=
        valuation_apply_lt_one 𝒪 σ.toRingEquiv (h𝒪 σ) (h𝒪 σ.symm) hαn
      rw [map_sub, hσn] at hσ
      rw [← sub_sub_sub_cancel_right (σ α) α n]
      exact Valuation.map_sub_lt _ hσ hαn
  obtain ⟨a, ha⟩ := mem_range_algebraMap_of_forall_algEquiv_apply_eq hsep hfix
  rw [← ha]
  exact a.2

/-- If a monic polynomial over an algebraically closed field takes a value in the maximal ideal
of `𝒪` at `x`, then it has a root congruent to `x` modulo the maximal ideal. -/
theorem exists_isRoot_valuation_sub_lt_one [IsAlgClosed Ω] {f : Ω[X]} (hf : f.Monic) {x : Ω}
    (hx : 𝒪.valuation (f.eval x) < 1) : ∃ r, f.IsRoot r ∧ 𝒪.valuation (r - x) < 1 := by
  rw [(IsAlgClosed.splits f).eq_prod_roots_of_monic hf, eval_multiset_prod, Multiset.map_map,
    map_multiset_prod, Multiset.map_map] at hx
  by_contra h
  push Not at h
  refine hx.not_ge (Multiset.one_le_prod_of_one_le fun y hy => ?_)
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hy
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
  rw [Valuation.map_sub_swap]
  exact h r ((mem_roots hf.ne_zero).1 hr)

/-- The coefficients of `X ^ n - X - C a` lie in every subring containing `a`. -/
theorem coeff_X_pow_sub_X_sub_C_mem {S : Type*} [SetLike S Ω] [SubringClass S Ω] {s : S}
    (n : ℕ) {a : Ω} (ha : a ∈ s) (i : ℕ) : (X ^ n - X - C a : Ω[X]).coeff i ∈ s := by
  simp only [coeff_sub, coeff_X_pow, coeff_X, coeff_C]
  refine sub_mem (sub_mem ?_ ?_) ?_ <;> split_ifs <;>
    first | exact OneMemClass.one_mem s | exact ZeroMemClass.zero_mem s | exact ha

/-- The coefficients of `X ^ n - C a` lie in every subring containing `a`. -/
theorem coeff_X_pow_sub_C_mem {S : Type*} [SetLike S Ω] [SubringClass S Ω] {s : S}
    (n : ℕ) {a : Ω} (ha : a ∈ s) (i : ℕ) : (X ^ n - C a : Ω[X]).coeff i ∈ s := by
  simp only [coeff_sub, coeff_X_pow, coeff_C]
  refine sub_mem ?_ ?_ <;> split_ifs <;>
    first | exact OneMemClass.one_mem s | exact ZeroMemClass.zero_mem s | exact ha

/-- **Artin–Schreier lifting.** In characteristic `p`, if `a ∈ N ∩ 𝒪` and `X ^ p - X - a` has a
residual root in `N ∩ 𝒪`, then it has a root in `N`. -/
theorem exists_pow_sub_self_eq [IsAlgClosed Ω] (N : Subfield Ω) [Algebra.IsAlgebraic N Ω]
    (h𝒪 : ∀ σ : Ω ≃ₐ[N] Ω, ∀ x ∈ 𝒪, σ x ∈ 𝒪) (p : ℕ) [hp : Fact p.Prime] [CharP Ω p]
    {a : Ω} (haN : a ∈ N) (ha𝒪 : a ∈ 𝒪) {n : Ω} (hnN : n ∈ N) (hn𝒪 : n ∈ 𝒪)
    (hn : 𝒪.valuation (n ^ p - n - a) < 1) : ∃ θ ∈ N, θ ^ p - θ = a := by
  have hmonic : (X ^ p - X - C a : Ω[X]).Monic := by
    rw [sub_sub]
    refine monic_X_pow_sub ((degree_X_add_C a).trans_lt ?_)
    exact_mod_cast hp.out.one_lt
  obtain ⟨θ, hθ, hθn⟩ := exists_isRoot_valuation_sub_lt_one 𝒪 hmonic (x := n) (by simpa using hn)
  refine ⟨θ, mem_of_isRoot_of_valuation_sub_lt_one 𝒪 N h𝒪 (coeff_X_pow_sub_X_sub_C_mem p haN)
    (coeff_X_pow_sub_X_sub_C_mem p ha𝒪) hθ ?_ hnN hn𝒪 hθn, ?_⟩
  · simp [derivative_X_pow]
  · simpa [sub_eq_zero] using hθ.eq_zero

/-- **`ℓ`-th roots.** If `ℓ` is invertible in the residue field of `𝒪`, `u ∈ N ∩ 𝒪` is a unit of
`𝒪` and `u` has a residual `ℓ`-th root in `N ∩ 𝒪`, then `u` has an `ℓ`-th root in `N`. -/
theorem exists_pow_eq [IsAlgClosed Ω] (N : Subfield Ω) [Algebra.IsAlgebraic N Ω]
    (h𝒪 : ∀ σ : Ω ≃ₐ[N] Ω, ∀ x ∈ 𝒪, σ x ∈ 𝒪) {ℓ : ℕ} (hℓ : 𝒪.valuation (ℓ : Ω) = 1)
    {u : Ω} (huN : u ∈ N) (hu : 𝒪.valuation u = 1) {n : Ω} (hnN : n ∈ N) (hn𝒪 : n ∈ 𝒪)
    (hn : 𝒪.valuation (n ^ ℓ - u) < 1) : ∃ y ∈ N, y ^ ℓ = u := by
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    simp at hℓ
  obtain ⟨y, hy, hyn⟩ := exists_isRoot_valuation_sub_lt_one 𝒪 (monic_X_pow_sub_C u hℓ0) (x := n)
    (by simpa using hn)
  have hy' : y ^ ℓ = u := by simpa [sub_eq_zero] using hy.eq_zero
  have hvy : 𝒪.valuation y = 1 := by
    rw [← pow_eq_one_iff_left hℓ0, ← map_pow, hy', hu]
  refine ⟨y, mem_of_isRoot_of_valuation_sub_lt_one 𝒪 N h𝒪 (coeff_X_pow_sub_C_mem ℓ huN)
    (coeff_X_pow_sub_C_mem ℓ ((valuation_le_one_iff _ _).1 hu.le)) hy ?_ hnN hn𝒪 hyn, hy'⟩
  simp [derivative_X_pow, hℓ, hvy]

end ValuationSubring

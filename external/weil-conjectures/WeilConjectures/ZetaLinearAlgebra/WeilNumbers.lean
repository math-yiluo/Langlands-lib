/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.Mathlib.NumberTheory.Padics.Complex
public import WeilConjectures.ZetaLinearAlgebra.Weights

/-!
# Weil numbers

An element `α` of a field of characteristic zero is a *`q`-Weil number of weight `w`*
(blueprint `theorem-weil-conjectures-smooth-proper-schemes--5`) if it is algebraic over `ℚ` and
`|τ α| = q ^ (w / 2)` for every field embedding `τ : ℚ(α) → ℂ`. Equivalently, every complex
conjugate of `α` (every complex root of its minimal polynomial over `ℚ`) has absolute value
`q ^ (w / 2)`.

## Main statements

- `IsWeilNumber`: the predicate of being a `q`-Weil number of weight `w`.
- `isWeilNumber_iff`: characterization through the complex roots of the minimal polynomial.
- `isWeilNumber_algHom_apply_iff`, `isWeilNumber_algEquiv_apply_iff`: the Weil-number condition
  is invariant under `ℚ`-algebra embeddings, in particular under `Gal(ℚ̄/ℚ)`.
- `isUniversallyPureOfWeight_iff_isWeilNumber_inv`: a nonzero complex number is universally pure
  of weight `w` iff its inverse is a Weil number of weight `w`.
- `PadicAlgCl.isWeilNumber_of_forall_ringEquiv`: the intrinsic-weight clause of the blueprint
  lemma `lemma-reciprocal-roots-zeta--6`.
-/

@[expose] public section

open IntermediateField Polynomial

section Defs

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Blueprints `theorem-weil-conjectures-smooth-proper-schemes--5` and `definition-reciprocal-root`:
`α` is a *`q`-Weil number of weight `w`* if it is algebraic
over `ℚ` and every `ℚ`-embedding `τ : ℚ(α) → ℂ` satisfies `‖τ α‖ = q ^ (w / 2)`. -/
def IsWeilNumber (q : ℕ) (w : ℝ) (α : K) : Prop :=
  IsIntegral ℚ α ∧ ∀ τ : ℚ⟮α⟯ →ₐ[ℚ] ℂ, ‖τ (AdjoinSimple.gen ℚ α)‖ = (q : ℝ) ^ (w / 2)

/-- For `α` integral over `ℚ`, a property holds for the images of `α` under all embeddings
`ℚ(α) → ℂ` iff it holds for all complex roots of the minimal polynomial of `α`. -/
theorem forall_algHom_adjoin_iff_forall_mem_roots {α : K} (hα : IsIntegral ℚ α)
    (P : ℂ → Prop) :
    (∀ τ : ℚ⟮α⟯ →ₐ[ℚ] ℂ, P (τ (AdjoinSimple.gen ℚ α))) ↔
      ∀ y ∈ ((minpoly ℚ α).map (algebraMap ℚ ℂ)).roots, P y := by
  refine ⟨fun h y hy ↦ ?_, fun h τ ↦ h _ ?_⟩
  · have := h ((algHomAdjoinIntegralEquiv ℚ hα).symm ⟨y, hy⟩)
    rwa [algHomAdjoinIntegralEquiv_symm_apply_gen] at this
  · refine mem_aroots.2 ⟨minpoly.ne_zero hα, ?_⟩
    rw [Polynomial.aeval_algHom_apply, aeval_gen_minpoly, map_zero]

/-- Blueprint `theorem-weil-conjectures-smooth-proper-schemes--5`: `α` is a `q`-Weil number of
weight `w` iff it is integral over `ℚ` and every complex root of its minimal polynomial has absolute
value `q ^ (w / 2)`. -/
theorem isWeilNumber_iff {q : ℕ} {w : ℝ} {α : K} :
    IsWeilNumber q w α ↔ IsIntegral ℚ α ∧
      ∀ y ∈ ((minpoly ℚ α).map (algebraMap ℚ ℂ)).roots, ‖y‖ = (q : ℝ) ^ (w / 2) :=
  and_congr_right fun hα ↦
    forall_algHom_adjoin_iff_forall_mem_roots hα fun y ↦ ‖y‖ = (q : ℝ) ^ (w / 2)

variable {K' : Type*} [Field K'] [Algebra ℚ K']

/-- Blueprint `theorem-weil-conjectures-smooth-proper-schemes--5`, `lemma-reciprocal-roots-zeta--6`:
the Weil-number condition is invariant under `ℚ`-algebra embeddings, since these preserve minimal
polynomials. -/
theorem isWeilNumber_algHom_apply_iff {q : ℕ} {w : ℝ} (f : K →ₐ[ℚ] K') {α : K} :
    IsWeilNumber q w (f α) ↔ IsWeilNumber q w α := by
  rw [isWeilNumber_iff, isWeilNumber_iff, isIntegral_algHom_iff f f.toRingHom.injective,
    minpoly.algHom_eq f f.toRingHom.injective]

/-- Blueprint `lemma-reciprocal-roots-zeta--6`: the Weil-number condition is stable under
`ℚ`-algebra isomorphisms, in particular under `Gal(ℚ̄/ℚ)`. -/
theorem isWeilNumber_algEquiv_apply_iff {q : ℕ} {w : ℝ} (σ : K ≃ₐ[ℚ] K') {α : K} :
    IsWeilNumber q w (σ α) ↔ IsWeilNumber q w α :=
  isWeilNumber_algHom_apply_iff (σ : K →ₐ[ℚ] K')

/-- If `α β = 1`, a property of the images of `α` under the embeddings of `ℚ(α)` transfers to
the inverses of the images of `β` under the embeddings of `ℚ(β)`. -/
private theorem forall_algHom_adjoin_inv {α β : K} (hαβ : α * β = 1) {P : ℂ → Prop}
    (h : ∀ τ : ℚ⟮α⟯ →ₐ[ℚ] ℂ, P (τ (AdjoinSimple.gen ℚ α))) (τ : ℚ⟮β⟯ →ₐ[ℚ] ℂ) :
    P (τ (AdjoinSimple.gen ℚ β))⁻¹ := by
  have hα : α = β⁻¹ := eq_inv_of_mul_eq_one_left hαβ
  have hmem : α ∈ ℚ⟮β⟯ := hα ▸ ℚ⟮β⟯.inv_mem (mem_adjoin_simple_self ℚ β)
  have hle : ℚ⟮α⟯ ≤ ℚ⟮β⟯ := adjoin_simple_le_iff.2 hmem
  have hgen : (⟨α, hmem⟩ : ℚ⟮β⟯) = (AdjoinSimple.gen ℚ β)⁻¹ :=
    Subtype.ext (hα.trans (by rw [IntermediateField.coe_inv, AdjoinSimple.coe_gen]))
  have := h (τ.comp (inclusion hle))
  rwa [AlgHom.comp_apply, show inclusion hle (AdjoinSimple.gen ℚ α) = ⟨α, hmem⟩ from rfl, hgen,
    map_inv₀] at this


/-- If every complex root of a nonzero `Q ∈ ℤ[X]` has absolute value `q ^ (w / 2)`, then every
root of `Q` in a field `K` of characteristic zero is a `q`-Weil number of weight `w`: its
conjugates are complex roots of `Q`. -/
theorem isWeilNumber_of_mem_roots {q : ℕ} {w : ℝ} {Q : ℤ[X]} (hQ : Q ≠ 0)
    (h : ∀ y ∈ (Q.map (Int.castRingHom ℂ)).roots, ‖y‖ = (q : ℝ) ^ (w / 2)) {α : K}
    (hα : α ∈ (Q.map (Int.castRingHom K)).roots) : IsWeilNumber q w α := by
  have : CharZero K := algebraRat.charZero K
  have hcomp : (algebraMap ℚ K).comp (Int.castRingHom ℚ) = Int.castRingHom K :=
    RingHom.ext_int _ _
  have hcompℂ : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ :=
    RingHom.ext_int _ _
  have hQℚ : Q.map (Int.castRingHom ℚ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hQ
  have hQℂ : Q.map (Int.castRingHom ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hQ
  have hQK : Q.map (Int.castRingHom K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hQ
  have haeval : aeval α (Q.map (Int.castRingHom ℚ)) = 0 := by
    rw [aeval_def, eval₂_map, hcomp, ← eval_map]
    exact (mem_roots hQK).1 hα
  have hint : IsIntegral ℚ α := ⟨_, (monic_normalize hQℚ), by
    rw [← aeval_def, normalize_apply, map_mul, haeval, zero_mul]⟩
  refine isWeilNumber_iff.2 ⟨hint, fun y hy ↦ h y ?_⟩
  have hdvd : (minpoly ℚ α).map (algebraMap ℚ ℂ) ∣ Q.map (Int.castRingHom ℂ) := by
    rw [← hcompℂ, ← Polynomial.map_map]
    exact Polynomial.map_dvd _ (minpoly.dvd ℚ α haeval)
  exact Multiset.mem_of_le (Polynomial.roots.le_of_dvd hQℂ hdvd) hy

/-- The weight of a `q`-Weil number is unique for `q > 1`: the absolute value of a complex
conjugate determines it. -/
theorem IsWeilNumber.weight_eq {q : ℕ} (hq : 1 < q) {w w' : ℝ} {α : K} (h : IsWeilNumber q w α)
    (h' : IsWeilNumber q w' α) : w = w' := by
  rw [isWeilNumber_iff] at h h'
  have hne : (minpoly ℚ α).map (algebraMap ℚ ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).2 (minpoly.ne_zero h.1)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root ((minpoly ℚ α).map (algebraMap ℚ ℂ))
    (by rw [degree_map]; exact (minpoly.degree_pos h.1).ne')
  have hy' : y ∈ ((minpoly ℚ α).map (algebraMap ℚ ℂ)).roots := (mem_roots hne).2 hy
  have e := (h.2 y hy').symm.trans (h'.2 y hy')
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have := le_antisymm ((Real.rpow_le_rpow_left_iff hq').1 e.le)
    ((Real.rpow_le_rpow_left_iff hq').1 e.ge)
  linarith
end Defs

/-- The universal purity of `Weights.lean` versus Weil numbers (blueprint
`theorem-weil-conjectures-smooth-proper-schemes--5`): a nonzero complex number `z` is universally
pure of weight `w` (its conjugates have absolute value `q ^ (-w / 2)`) iff `z⁻¹` is a `q`-Weil
number of weight `w`. -/
theorem isUniversallyPureOfWeight_iff_isWeilNumber_inv {q w : ℕ} {z : ℂ} (hz : z ≠ 0) :
    IsUniversallyPureOfWeight q w z ↔ IsWeilNumber q w z⁻¹ := by
  have hnorm : ∀ y : ℂ, ‖y‖ = (q : ℝ) ^ (-(w : ℝ) / 2) ↔ ‖y⁻¹‖ = (q : ℝ) ^ ((w : ℝ) / 2) := by
    intro y
    rw [neg_div, Real.rpow_neg (Nat.cast_nonneg q), norm_inv, inv_eq_iff_eq_inv]
  unfold _root_.IsUniversallyPureOfWeight IsWeilNumber
  rw [isAlgebraic_iff_isIntegral]
  refine ⟨fun ⟨hint, h⟩ ↦ ⟨hint.inv, ?_⟩, fun ⟨hint, h⟩ ↦ ⟨?_, ?_⟩⟩
  · rw [← forall_algHom_adjoin_iff_forall_mem_roots hint] at h
    intro τ
    have := forall_algHom_adjoin_inv (mul_inv_cancel₀ hz) (P := fun y ↦ ‖y⁻¹‖ = _)
      (fun τ ↦ (hnorm _).1 (h τ)) τ
    rwa [inv_inv] at this
  · simpa using hint.inv
  · have hint' : IsIntegral ℚ z := by simpa using hint.inv
    rw [← forall_algHom_adjoin_iff_forall_mem_roots hint']
    intro τ
    rw [hnorm]
    exact forall_algHom_adjoin_inv (inv_mul_cancel₀ hz) (P := fun y ↦ ‖y‖ = _) h τ

/-- The intrinsic-weight clause of blueprint `lemma-reciprocal-roots-zeta--6`: if `α ∈ ℚ̄_p` is
algebraic over `ℚ` and `‖ι α‖ = q ^ (w / 2)` for every abstract field isomorphism
`ι : ℚ̄_p ≃ ℂ`, then `α` is a `q`-Weil number of weight `w`: every conjugate of `α` is the image
of `α` under such an isomorphism (`PadicAlgCl.exists_ringEquiv_complex_apply_eq`). -/
theorem PadicAlgCl.isWeilNumber_of_forall_ringEquiv (p : ℕ) [Fact p.Prime] {q : ℕ} {w : ℝ}
    {α : PadicAlgCl p} (hα : IsIntegral ℚ α)
    (h : ∀ ι : PadicAlgCl p ≃+* ℂ, ‖ι α‖ = (q : ℝ) ^ (w / 2)) : IsWeilNumber q w α := by
  refine isWeilNumber_iff.2 ⟨hα, fun y hy ↦ ?_⟩
  obtain ⟨ι, rfl⟩ := PadicAlgCl.exists_ringEquiv_complex_apply_eq p hα (mem_aroots.1 hy).2
  exact h ι

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtension
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.FieldTheory.Minpoly.Basic

/-!
# Finite p-adic coefficient extensions under algebra isomorphisms

An isomorphism of finite extensions of `ℚ_[l]` preserves the spectral absolute value, hence
identifies the valuation rings and their uniformizer ideals. Every finite extension has an
isomorphic model in any universe.

Source: Serre, Local Fields, Chapter II, §2 (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

namespace Padic

variable (l : ℕ) [Fact l.Prime]
variable {E : Type v} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {E' : Type w} [Field E'] [Algebra ℚ_[l] E'] [FiniteDimensional ℚ_[l] E']

/-- Algebra isomorphisms preserve the spectral absolute value: it only depends on the
minimal polynomial. Source: Serre, Local Fields, Chapter II, §2
(auxiliary; not a blueprint node). -/
theorem coefficientExtensionAbsoluteValue_algEquiv (σ : E ≃ₐ[ℚ_[l]] E') (x : E) :
    coefficientExtensionAbsoluteValue l E' (σ x) = coefficientExtensionAbsoluteValue l E x := by
  rw [coefficientExtensionAbsoluteValue_apply, coefficientExtensionAbsoluteValue_apply]
  change spectralValue (minpoly ℚ_[l] (σ x)) = spectralValue (minpoly ℚ_[l] x)
  rw [minpoly.algEquiv_eq]

/-- An algebra isomorphism maps the valuation ring onto the valuation ring.
(auxiliary; not a blueprint node). -/
theorem coefficientExtensionIntegers_map_algEquiv (σ : E ≃ₐ[ℚ_[l]] E') :
    (coefficientExtensionIntegers l E).map σ.toRingEquiv.toRingHom =
      coefficientExtensionIntegers l E' := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change coefficientExtensionAbsoluteValue l E' (σ x) ≤ 1
    rw [coefficientExtensionAbsoluteValue_algEquiv]
    exact hx
  · intro hy
    refine ⟨σ.symm y, ?_, σ.apply_symm_apply y⟩
    change coefficientExtensionAbsoluteValue l E (σ.symm y) ≤ 1
    rw [← coefficientExtensionAbsoluteValue_algEquiv l σ, σ.apply_symm_apply]
    exact hy

/-- The ring isomorphism of valuation rings induced by an algebra isomorphism.
(auxiliary; not a blueprint node). -/
def coefficientExtensionIntegersEquiv (σ : E ≃ₐ[ℚ_[l]] E') :
    coefficientExtensionIntegers l E ≃+* coefficientExtensionIntegers l E' :=
  RingEquiv.trans (σ.toRingEquiv.subringMap (s := coefficientExtensionIntegers l E))
    (RingEquiv.subringCongr (coefficientExtensionIntegers_map_algEquiv l σ))

/-- The uniformizer ideal is the maximal ideal of the valuation ring.
(auxiliary; not a blueprint node). -/
theorem span_coefficientExtensionUniformizer_eq_maximalIdeal (E : Type v) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Ideal.span {coefficientExtensionUniformizer l E} =
      coefficientExtensionMaximalIdeal l E :=
  (coefficientExtensionIntegers_dvr l E).choose_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec

/-- The chosen uniformizer is nonzero, since the maximal ideal is nonzero.
(auxiliary; not a blueprint node). -/
theorem coefficientExtensionUniformizer_ne_zero (E : Type v) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    coefficientExtensionUniformizer l E ≠ 0 := by
  intro h
  have hm : coefficientExtensionMaximalIdeal l E ≠ ⊥ :=
    (coefficientExtensionIntegers_dvr l E).choose_spec.2.2.2.2.2.2.2.2.2.1
  apply hm
  rw [← span_coefficientExtensionUniformizer_eq_maximalIdeal, h, Ideal.span_singleton_eq_bot]

/-- Any ring isomorphism of valuation rings identifies the uniformizer ideals, since these
are the unique maximal ideals. (auxiliary; not a blueprint node). -/
theorem map_span_coefficientExtensionUniformizer
    (e : coefficientExtensionIntegers l E ≃+* coefficientExtensionIntegers l E') :
    Ideal.map e (Ideal.span {coefficientExtensionUniformizer l E}) =
      Ideal.span {coefficientExtensionUniformizer l E'} := by
  have h := (coefficientExtensionIntegers_dvr l E).choose_spec
  have h' := (coefficientExtensionIntegers_dvr l E').choose_spec
  rw [span_coefficientExtensionUniformizer_eq_maximalIdeal,
    span_coefficientExtensionUniformizer_eq_maximalIdeal]
  have : (coefficientExtensionMaximalIdeal l E).IsMaximal := h.2.2.2.2.1
  exact h'.2.2.2.2.2.1 _ (Ideal.map_isMaximal_of_equiv e)

/-- Every finite extension of `ℚ_[l]` has an isomorphic copy in any universe.
(auxiliary; not a blueprint node). -/
theorem exists_algEquiv_coefficientExtension (E : Type v) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ (E₀ : Type u) (_ : Field E₀) (_ : Algebra ℚ_[l] E₀) (_ : FiniteDimensional ℚ_[l] E₀),
      Nonempty (E ≃ₐ[ℚ_[l]] E₀) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℚ_[l] E
  have : Small.{u} E := small_of_surjective hf
  refine ⟨Shrink.{u} E, inferInstance, inferInstance, ?_, ⟨(Shrink.algEquiv ℚ_[l] E).symm⟩⟩
  exact LinearEquiv.finiteDimensional (Shrink.algEquiv ℚ_[l] E).symm.toLinearEquiv

end Padic

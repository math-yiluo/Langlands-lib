/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement

/-!
# Inverting a coefficient-field uniformizer

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-def-sf-operations`,
`def-weil-rationalization-karoubi`, the displayed Hom tensor E formula;
Stacks Project, Tags 00CO and 00CX
(blueprint: lem-weil-l-adic-integers-localization-uniformizer).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Padic

/-- Inverting the chosen uniformizer identifies the integers with the coefficient field
and identifies their tensor products as E-modules. The two module structures in the last
clause are specified on pure tensors: the left action is transported using `φ.symm`, and
the right action is multiplication on the field factor. The additive equivalence `F`
intertwines these actions, which states precisely that it is an E-linear isomorphism.

Source: blueprint `def-weil-rationalization-karoubi`, displayed Hom tensor E formula;
Stacks Project, Tags 00CO and 00CX
(blueprint: lem-weil-l-adic-integers-localization-uniformizer).

Proof: Define the fraction map x/π^n ↦ x π^(-n). Cross multiplication and cancellation
in E show that it is well defined, preserves ring operations and is injective. By
`lem-weil-l-adic-extension-integers-dvr`, π is nonzero and every nonzero field element
is a unit times an integer power of π. Nonnegative powers lie in the integer ring;
negative powers give fractions with denominator π^n. Zero is the image of 0/1.
This proves surjectivity and the localization assertion. For every module M, the
bilinear universal property of `def-weil-pbc-module-tensor-product` gives the maps
m ⊗ t ↦ m ⊗ φ(t) and m ⊗ e ↦ m ⊗ φ.symm(e). They respect balancing since φ fixes
the integers, and their composites fix all pure tensors, hence are identities.
Transport multiplication by e to multiplication by φ.symm(e) on the left localization factor.
On pure tensors the forward map intertwines this action with multiplication by e
on the right field factor; generation by pure tensors proves E-linearity. -/
theorem coefficientExtension_localization_uniformizer (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    IsLocalization.Away (coefficientExtensionUniformizer l E) E ∧
    ∃ φ : Localization.Away (coefficientExtensionUniformizer l E) ≃ₐ[
        coefficientExtensionIntegers l E] E,
      (∀ (x : coefficientExtensionIntegers l E) (n : ℕ),
        φ (IsLocalization.mk' (Localization.Away (coefficientExtensionUniformizer l E))
          x (⟨coefficientExtensionUniformizer l E ^ n, ⟨n, rfl⟩⟩ :
            Submonoid.powers (coefficientExtensionUniformizer l E))) =
          (x : E) * (coefficientExtensionUniformizer l E : E)⁻¹ ^ n) ∧
      ∀ (M : Type v) [AddCommGroup M] [Module (coefficientExtensionIntegers l E) M],
        ∃ (s : Module E (M ⊗[coefficientExtensionIntegers l E]
            Localization.Away (coefficientExtensionUniformizer l E)))
          (t : Module E (M ⊗[coefficientExtensionIntegers l E] E))
          (F : (M ⊗[coefficientExtensionIntegers l E]
            Localization.Away (coefficientExtensionUniformizer l E)) ≃+
              (M ⊗[coefficientExtensionIntegers l E] E)),
          (∀ (e : E) (m : M) (a : Localization.Away (coefficientExtensionUniformizer l E)),
            s.toSMul.smul e (m ⊗ₜ a) = m ⊗ₜ (φ.symm e * a)) ∧
          (∀ (e : E) (m : M) (a : E),
            t.toSMul.smul e (m ⊗ₜ a) = m ⊗ₜ (e * a)) ∧
          (∀ (m : M) (a : Localization.Away (coefficientExtensionUniformizer l E)),
            F (m ⊗ₜ a) = m ⊗ₜ φ a) ∧
          (∀ (e : E) (z : M ⊗[coefficientExtensionIntegers l E]
              Localization.Away (coefficientExtensionUniformizer l E)),
            F (s.toSMul.smul e z) = t.toSMul.smul e (F z)) := by
  let H := coefficientExtensionIntegers_dvr l E
  let O := coefficientExtensionIntegers l E
  let HM := H.choose
  let HS := H.choose_spec
  rcases HS with ⟨hO, hm, hu, hlocal, hmax, hmax_unique, hfrac, hdvr,
    hpid, hm0, hprime, hfinite, hr, hgen, hassoc, hexists⟩
  let π : O := hgen.choose
  have hπ : Ideal.span ({π} : Set O) = HM := hgen.choose_spec
  have hπ_ne : (π : E) ≠ 0 := by
    rcases hr with ⟨r, hr1, hr2, hchar⟩
    intro h
    apply (hchar π).mp hπ |>.1
    exact Subtype.ext h
  have hunit : IsUnit (algebraMap O E π) := by
    change IsUnit (π : E)
    exact isUnit_iff_ne_zero.mpr hπ_ne
  have hsurj : ∀ z : E, ∃ n a, z * (algebraMap O E π) ^ n = algebraMap O E a := by
    intro z
    by_cases hz : z = 0
    · refine ⟨0, 0, ?_⟩
      simp [hz]
    · let x : Eˣ := Units.mk0 z hz
      obtain ⟨p, hp, _⟩ := hexists π hπ x
      rcases p with ⟨v, n⟩
      cases n with
      | ofNat k =>
          refine ⟨0, v * π ^ k, ?_⟩
          change z * (π : E) ^ 0 = (((v : O) * π ^ k : O) : E)
          have hp' := hp
          simp only [x, Units.val_mk0] at hp'
          simp [hp']
      | negSucc k =>
          refine ⟨k + 1, v, ?_⟩
          change z * (π : E) ^ (k + 1) = (v : E)
          have hp' := hp
          simp only [x, Units.val_mk0, zpow_negSucc] at hp'
          rw [hp']
          field_simp
  have heq : ∀ (a b : O), (algebraMap O E) a = algebraMap O E b →
      ∃ n, π ^ n * a = π ^ n * b := by
    intro a b hab
    have hab' : a = b := Subtype.ext hab
    exact ⟨0, by simp [hab']⟩
  have hloc : IsLocalization.Away (coefficientExtensionUniformizer l E) E := by
    change IsLocalization.Away π E
    exact IsLocalization.Away.mk π hunit hsurj heq
  let := hloc
  let R := coefficientExtensionIntegers l E
  let L := Localization.Away (coefficientExtensionUniformizer l E)
  let φ : L ≃ₐ[R] E := IsLocalization.algEquiv
    (Submonoid.powers (coefficientExtensionUniformizer l E)) L E
  refine ⟨hloc, φ, ?_, ?_⟩
  · intro x n
    rw [IsLocalization.algEquiv_mk']
    apply IsLocalization.mk'_eq_iff_eq_mul.mpr
    change (x : E) = (x : E) * (π : E)⁻¹ ^ n * ((π ^ n : O) : E)
    simp [hπ_ne]
  · intro M _ _
    let F := (φ.toLinearEquiv.lTensor M).toAddEquiv
    let C := (TensorProduct.comm R M E).toAddEquiv
    let t : Module E (M ⊗[R] E) := C.module E
    let := t
    let s : Module E (M ⊗[R] L) := F.module E
    refine ⟨s, t, F, ?_, ?_, ?_, ?_⟩
    · intro e m a
      change F.symm (e • F (m ⊗ₜ a)) = m ⊗ₜ (φ.symm e * a)
      change F.symm (C.symm (e • C (m ⊗ₜ φ a))) = _
      simp [F, C, TensorProduct.smul_tmul', smul_eq_mul, map_mul]
    · intro e m a
      change C.symm (e • C (m ⊗ₜ a)) = m ⊗ₜ (e * a)
      simp [C, TensorProduct.smul_tmul', smul_eq_mul]
    · intro m a
      rfl
    · intro e z
      exact F.apply_symm_apply (e • F z)

end Padic

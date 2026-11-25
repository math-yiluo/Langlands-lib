/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Core

/-!
# Noetherian approximation of finitely presented algebras with a section

Let `B` be a finitely presented `A`-algebra together with an `A`-algebra section `s : B → A`.
We show that `B` and `s` descend to a finitely generated `ℤ`-subalgebra `A₀` of `A`: there is
a finitely presented `A₀`-algebra `B₀` with `B ≅ A ⊗[A₀] B₀` and an `A₀`-algebra section
`s₀ : B₀ → A₀` inducing `s` (Stacks, Tags 00R0 and 05N9; used for 01ZM and 055P).

## Main results

- `Algebra.FinitePresentation.exists_fg_subalgebra_isPushout`
- `Algebra.FinitePresentation.exists_fg_subalgebra_with_section`
-/

@[expose] public section

universe u

open TensorProduct MvPolynomial

namespace Algebra.FinitePresentation

/-- Noetherian approximation of a finitely presented algebra (Stacks 00R0, 05N9): `B` descends
to a finitely generated `ℤ`-subalgebra `A₀` of `A`. That is, there is a finitely presented
`A₀`-algebra `B₀` with `B ≅ A ⊗[A₀] B₀`. -/
theorem exists_fg_subalgebra_isPushout
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B] :
    ∃ (A₀ : Subalgebra ℤ A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀)
      (_ : Algebra B₀ B) (_ : IsScalarTower A₀ B₀ B),
      A₀.FG ∧ Algebra.FinitePresentation A₀ B₀ ∧ Algebra.IsPushout A₀ A B₀ B := by
  let P := Presentation.ofFinitePresentation A B
  let A₀ : Subalgebra ℤ A := Algebra.adjoin ℤ P.coeffs
  have hA₀ : A₀.FG := Subalgebra.fg_def.mpr ⟨_, P.finite_coeffs, rfl⟩
  have : P.HasCoeffs A₀ := ⟨by
    rw [Subalgebra.setRange_algebraMap]
    exact Algebra.subset_adjoin⟩
  let B₀ := P.ModelOfHasCoeffs A₀
  let f : B₀ →ₐ[A₀] B := Ideal.Quotient.liftₐ _ (aeval P.val) fun a ha ↦
    (Ideal.span_le (I := RingHom.ker (aeval (R := A₀) P.val))).mpr
      (Set.range_subset_iff.mpr fun i ↦ by simp) ha
  let _ : Algebra B₀ B := f.toRingHom.toAlgebra
  have : IsScalarTower A₀ B₀ B := .of_algebraMap_eq fun x ↦ (f.commutes x).symm
  refine ⟨A₀, B₀, inferInstance, inferInstance, inferInstance, inferInstance, hA₀,
    inferInstance, ⟨.of_equiv (P.tensorModelOfHasCoeffsEquiv A₀).toLinearEquiv fun b ↦ ?_⟩⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine (P.tensorModelOfHasCoeffsEquiv_tmul A₀ 1 p).trans ?_
  rw [map_one, one_mul]
  rfl

/-- Noetherian approximation of a finitely presented algebra with a section (Stacks 00R0, 05N9;
used for 055P): `B` and the section `s` descend to a finitely generated `ℤ`-subalgebra `A₀` of
`A`. That is, there is a finitely presented `A₀`-algebra `B₀` with `B ≅ A ⊗[A₀] B₀` and an
`A₀`-algebra section `s₀ : B₀ → A₀` compatible with `s`. -/
theorem exists_fg_subalgebra_with_section
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
    (s : B →ₐ[A] A) :
    ∃ (A₀ : Subalgebra ℤ A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀)
      (_ : Algebra B₀ B) (_ : IsScalarTower A₀ B₀ B),
      A₀.FG ∧ Algebra.FinitePresentation A₀ B₀ ∧ Algebra.IsPushout A₀ A B₀ B ∧
      ∃ s₀ : B₀ →ₐ[A₀] A₀, ∀ b : B₀, (s₀ b : A) = s (algebraMap B₀ B b) := by
  let P := Presentation.ofFinitePresentation A B
  let A₀ : Subalgebra ℤ A := Algebra.adjoin ℤ (P.coeffs ∪ Set.range (s ∘ P.val))
  have hA₀ : A₀.FG :=
    Subalgebra.fg_def.mpr ⟨_, P.finite_coeffs.union (Set.finite_range _), rfl⟩
  have : P.HasCoeffs A₀ := ⟨by
    rw [Subalgebra.setRange_algebraMap]
    exact Set.subset_union_left.trans Algebra.subset_adjoin⟩
  let B₀ := P.ModelOfHasCoeffs A₀
  let f : B₀ →ₐ[A₀] B := Ideal.Quotient.liftₐ _ (aeval P.val) fun a ha ↦
    (Ideal.span_le (I := RingHom.ker (aeval (R := A₀) P.val))).mpr
      (Set.range_subset_iff.mpr fun i ↦ by simp) ha
  let _ : Algebra B₀ B := f.toRingHom.toAlgebra
  have : IsScalarTower A₀ B₀ B := .of_algebraMap_eq fun x ↦ (f.commutes x).symm
  have hval (j) : s (P.val j) ∈ A₀ := Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)
  let t : MvPolynomial _ A₀ →ₐ[A₀] A₀ := aeval fun j ↦ ⟨s (P.val j), hval j⟩
  have ht' : (Algebra.ofId A₀ A).comp t = (s.restrictScalars A₀).comp (aeval P.val) := by
    ext j
    simp [t]
  have ht (p : MvPolynomial _ A₀) : (t p : A) = s (aeval P.val p) := congr($ht' p)
  let s₀ : B₀ →ₐ[A₀] A₀ := Ideal.Quotient.liftₐ _ t fun a ha ↦
    (Ideal.span_le (I := RingHom.ker t)).mpr (Set.range_subset_iff.mpr fun i ↦ by
      simp [← Subtype.val_inj, ht]) ha
  refine ⟨A₀, B₀, inferInstance, inferInstance, inferInstance, inferInstance, hA₀,
    inferInstance, ⟨.of_equiv (P.tensorModelOfHasCoeffsEquiv A₀).toLinearEquiv fun b ↦ ?_⟩,
    s₀, fun b ↦ ?_⟩
  · obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine (P.tensorModelOfHasCoeffsEquiv_tmul A₀ 1 p).trans ?_
    rw [map_one, one_mul]
    rfl
  · obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ht p

end Algebra.FinitePresentation

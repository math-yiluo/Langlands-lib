/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Ideal.Quotient.Defs

import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Algebra.BigOperators.Fin

/-! # Lifts of cycles in a quotient tensor complex
Source: Stacks Project, Algebra, proof of Tag 00M5 and Remark 00M6.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators
namespace ModuleCat

/-- Source: Stacks Project, Algebra, proof of Tag 00M5 and Remark 00M6;
Step 2 of the ideal comparison compatibility argument.
(blueprint: lem-weil-pbc-quotient-cycle-lift).

Proof in words: tensoring a module E with R/I identifies it with E/IE by
TensorProduct.tensorQuotEquivQuotSMul. Surjectivity of the quotient map
therefore lifts iCycles(z) to y ⊗ 1. Since z is a cycle, its differential
vanishes, so (d y) ⊗ 1 = 0. Under the same quotient identification in degree
zero, this says d y belongs to I times the whole degree-zero module.
That submodule consists precisely of finite sums of a • p with a in I:
its generating products are closed under addition and scalar multiplication,
and coefficients can be absorbed in a. Index such a finite sum by Fin k.
This gives the claimed expression. The argument requires no freeness; for
I = 0 the expression is the empty sum, and for I = R all tensors vanish.
-/
theorem exists_quotient_cycle_lift
    {R : Type u} [CommRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    (P : ProjectiveResolution M)
    (z : ((((tensoringRight (ModuleCat.{u} R)).obj
        (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).cycles 1) :
    ∃ (y : P.complex.X 1) (k : ℕ) (a : Fin k → I) (p : Fin k → P.complex.X 0),
      ((((tensoringRight (ModuleCat.{u} R)).obj
        (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).iCycles 1 z = y ⊗ₜ[R] (1 : R ⧸ I) ∧
      P.complex.d 1 0 y = ∑ j, (a j : R) • p j := by
  classical
  let C := (((tensoringRight (ModuleCat.{u} R)).obj
    (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let e := TensorProduct.tensorQuotEquivQuotSMul (P.complex.X 1) I
  obtain ⟨y, hy⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R (P.complex.X 1)))
    (e (C.iCycles 1 z))
  have hlift : C.iCycles 1 z = y ⊗ₜ[R] (1 : R ⧸ I) := by
    apply e.injective
    simpa only [Submodule.mkQ_apply, e, ← RingHom.map_one (Ideal.Quotient.mk I),
      TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul] using hy.symm
  have hzero : (P.complex.d 1 0 y) ⊗ₜ[R] (1 : R ⧸ I) = 0 := by
    have h := ConcreteCategory.congr_hom (C.iCycles_d 1 0) z
    change C.d 1 0 (C.iCycles 1 z) = 0 at h
    rw [hlift] at h
    exact h
  have hmem : P.complex.d 1 0 y ∈ I • (⊤ : Submodule R (P.complex.X 0)) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    have h := congrArg (TensorProduct.tensorQuotEquivQuotSMul (P.complex.X 0) I) hzero
    simpa only [← RingHom.map_one (Ideal.Quotient.mk I),
      TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul, map_zero] using h
  have hfinite : ∀ x ∈ I • (⊤ : Submodule R (P.complex.X 0)),
      ∃ (k : ℕ) (a : Fin k → I) (p : Fin k → P.complex.X 0),
        x = ∑ j, (a j : R) • p j := by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr p _
      exact ⟨1, fun _ ↦ ⟨r, hr⟩, fun _ ↦ p, by simp⟩
    · intro x₁ x₂ h₁ h₂
      obtain ⟨k₁, a₁, p₁, h₁⟩ := h₁
      obtain ⟨k₂, a₂, p₂, h₂⟩ := h₂
      refine ⟨k₁ + k₂, Fin.addCases a₁ a₂, Fin.addCases p₁ p₂, ?_⟩
      rw [Fin.sum_univ_add]
      simpa only [Fin.addCases_left, Fin.addCases_right] using congrArg₂ (· + ·) h₁ h₂
  obtain ⟨k, a, p, hd⟩ := hfinite _ hmem
  exact ⟨y, k, a, p, hlift, hd⟩

end ModuleCat

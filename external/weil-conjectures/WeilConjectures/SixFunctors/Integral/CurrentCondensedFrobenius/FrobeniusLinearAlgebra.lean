/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaLinearAlgebra.Pairing

/-! # Linear algebra of a perfect Frobenius similitude

Source: current blueprint, `sk-thm-frobenius.proof.md`, final paragraph
(blueprint: lem-pod-frobenius-linear-consequences).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v w z
open Module

namespace WeilConjectures.SixFunctors.CurrentCondensedFrobenius

variable {R : Type u} [Field R] {V : Type v} {W : Type w}
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [Module.Finite R V] [Module.Finite R W]
  (p : V →ₗ[R] W →ₗ[R] R) [p.IsPerfPair]
  (A : V →ₗ[R] V) (B : W →ₗ[R] W) (c : R)
  (hc : c ≠ 0) (hsim : ∀ x y, p (A x) (B y) = c * p x y)

include hc hsim
omit [Module.Finite R W] in
/-- The adjoint given by the pairing conjugates the second operator to the
scaled transpose of the first inverse. Source: Frobenius proof, final paragraph
(blueprint: lem-pod-frobenius-linear-consequences).
Proof: the similitude and nonzero scalar imply injectivity; finite dimension
makes the first operator an equivalence. Substitute its inverse in the
similitude identity and evaluate the canonical perfect-pairing adjoint. -/
theorem inverseTranspose :
    ∃ a : V ≃ₗ[R] V, a.toLinearMap = A ∧
      ∃ adj : W ≃ₗ[R] Module.Dual R V,
        (∀ x y, adj y x = p x y) ∧
        ∀ y, adj (B y) = c • a.symm.toLinearMap.dualMap (adj y) := by
  let a : V ≃ₗ[R] V := LinearEquiv.ofBijective A
    ⟨LinearMap.injective_of_similitude hc hsim,
      LinearMap.injective_iff_surjective.mp (LinearMap.injective_of_similitude hc hsim)⟩
  refine ⟨a, rfl, p.flip.toPerfPair, ?_, ?_⟩
  · intro x y
    rfl
  · intro y
    ext x
    change p x (B y) = c * p (a.symm x) y
    have h := hsim (a.symm x) y
    change p (A (a.symm x)) (B y) = c * p (a.symm x) y at h
    simpa only [show A (a.symm x) = x from a.apply_symm_apply x] using h

/-- The inverse-transpose, dimension, determinant and reciprocal-root conclusions
of a perfect similitude. Source: Frobenius proof, final paragraph
(blueprint: lem-pod-frobenius-linear-consequences).
Proof: use the preceding inverse-transpose calculation. Perfectness gives equal
ranks; the determinant product and root multiset identities are the existing
perfect-similitude theorems, including in dimension zero. -/
theorem linearFieldConsequences :
    (∃ a : V ≃ₗ[R] V, a.toLinearMap = A ∧
      ∃ adj : W ≃ₗ[R] Module.Dual R V,
        (∀ x y, adj y x = p x y) ∧
        ∀ y, adj (B y) = c • a.symm.toLinearMap.dualMap (adj y)) ∧
    Module.finrank R V = Module.finrank R W ∧
    LinearMap.det A * LinearMap.det B = c ^ Module.finrank R V ∧
    ∀ (Ω : Type z) [Field Ω] [IsAlgClosed Ω] (j : R →+* Ω),
      (B.charpoly.map j).roots =
        (A.charpoly.map j).roots.map (fun α ↦ j c / α) := by
  exact ⟨inverseTranspose p A B c hc hsim, Module.finrank_of_isPerfPair p,
    LinearMap.det_mul_det_of_similitude hsim,
    fun _ _ _ j ↦ LinearMap.roots_map_charpoly_of_similitude hc hsim j⟩

end WeilConjectures.SixFunctors.CurrentCondensedFrobenius

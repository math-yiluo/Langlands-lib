/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
import WeilConjectures.RingTheory.GradedSubmoduleFinite

/-!
# Finite graded kernels over the two-variable polynomial ring

Source: blueprint `sec-picard-framework/det-thm-picard-duality/lem-sc-p1-graded-resolution.md`,
proof, Noetherianity of successive graded kernels (blueprint: lem-sc-p1-graded-kernel-finite).
-/

@[expose] public section

universe u v w

namespace MvPolynomial

/-- The kernel of a graded map out of a finite graded `k[x₀,x₁]`-module is finite graded.
Source: blueprint `lem-sc-p1-graded-resolution.md`, proof, successive graded kernels
(blueprint: lem-sc-p1-graded-kernel-finite).

The internal integer gradings allow arbitrary shifts, with the polynomial ring carrying its
standard total-degree grading. Finite graded generation is expressed by finite homogeneous
spanning sets. The kernel grading is the grading inherited from `F`, expressed by closure under
homogeneous components; its finite homogeneous generators are elements of `F` spanning `q.ker`.

Proof:
1. Decompose an element of the kernel into its finitely many homogeneous components. Since `q`
   preserves degrees and `M` is an internal direct sum, each image component is zero. Thus every
   homogeneous component belongs to the kernel, making it a graded submodule of `F`.
2. Apply `lem-sc-p1-graded-submodule-finite` to this graded submodule of the finitely generated
   graded module `F`. It supplies the finite homogeneous generating set for the kernel. -/
theorem graded_kernel_finite {k : Type u} [Field k]
    {F : Type v} [AddCommGroup F] [Module (MvPolynomial (Fin 2) k) F]
    {M : Type w} [AddCommGroup M] [Module (MvPolynomial (Fin 2) k) M]
    (ℱ : ℤ → AddSubgroup F) (hF : DirectSum.IsInternal ℱ)
    (ℳ : ℤ → AddSubgroup M) (hM : DirectSum.IsInternal ℳ)
    (hsmulF : ∀ (n : ℕ) (j : ℤ) (f : MvPolynomial (Fin 2) k) (x : F),
      f ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℱ j → f • x ∈ ℱ ((n : ℤ) + j))
    (hfiniteF : ∃ s : Set F, s.Finite ∧ (∀ x ∈ s, SetLike.IsHomogeneousElem ℱ x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = ⊤)
    (q : F →ₗ[MvPolynomial (Fin 2) k] M)
    (hgraded : ∀ (j : ℤ) (x : F), x ∈ ℱ j → q x ∈ ℳ j) :
    @Submodule.IsHomogeneous ℤ (AddSubgroup F) (MvPolynomial (Fin 2) k) F
      _ _ _ q.ker ℱ _ _ _ hF.chooseDecomposition ∧
    ∃ s : Set F, s.Finite ∧ (∀ x ∈ s, SetLike.IsHomogeneousElem ℱ x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = q.ker := by
  classical
  let : DirectSum.Decomposition ℱ := hF.chooseDecomposition
  let : DirectSum.Decomposition ℳ := hM.chooseDecomposition
  let g : ∀ j, ℱ j →+ ℳ j := fun j ↦
    { toFun := fun x ↦ ⟨q x, hgraded j x x.property⟩
      map_zero' := Subtype.ext (q.map_zero)
      map_add' := fun x y ↦ Subtype.ext (q.map_add x y) }
  have hmap (x : F) : DirectSum.decompose ℳ (q x) =
      DirectSum.map g (DirectSum.decompose ℱ x) := by
    rw [← DirectSum.sum_support_decompose ℱ x, map_sum, DirectSum.decompose_sum,
      DirectSum.decompose_sum, map_sum]
    congr 1
    simp [DirectSum.decompose_of_mem ℳ (hgraded _ _ (Subtype.prop _)),
      DirectSum.decompose_of_mem ℱ (Subtype.prop _), DirectSum.map_of, g]
  have hK : q.ker.IsHomogeneous ℱ := by
    intro j x hx
    change q (DirectSum.decompose ℱ x j : F) = 0
    have hj := congrArg (fun z ↦ (z j : M)) (hmap x)
    simpa [LinearMap.mem_ker.mp hx, DirectSum.decompose_zero, g] using hj.symm
  exact ⟨hK, graded_submodule_finite ℱ hF hsmulF hfiniteF q.ker hK⟩

end MvPolynomial

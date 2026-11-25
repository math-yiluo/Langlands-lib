/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Finiteness.Basic
import WeilConjectures.RingTheory.FiniteHomogeneousGenerators
import WeilConjectures.RingTheory.GradedKernelFinite

/-!
# Internal grading on a finite graded kernel

Source: blueprint `theorem-riemann-roch-coherent-serre-duality`, successive graded kernels.
-/

@[expose] public section

universe u v w

open scoped DirectSum

namespace MvPolynomial

private theorem finite_homogeneous_spanning {k : Type u} [Field k]
    {N : Type v} [AddCommGroup N] [Module (MvPolynomial (Fin 2) k) N]
    [Module.Finite (MvPolynomial (Fin 2) k) N]
    (ℳ : ℤ → AddSubgroup N) (hℳ : DirectSum.IsInternal ℳ)
    (hsmul : ∀ (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : N),
      s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℳ j → s • x ∈ ℳ ((n : ℤ) + j)) :
    ∃ s : Set N, s.Finite ∧ (∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = ⊤ := by
  classical
  obtain ⟨r, d, m, hm, f, hf, hfm, _⟩ :=
    exists_finite_homogeneous_generators ℳ hℳ hsmul
  refine ⟨Set.range m, Set.finite_range m, ?_, ?_⟩
  · rintro x ⟨a, rfl⟩
    exact ⟨d a, hm a⟩
  · have heq : f = Finsupp.linearCombination (MvPolynomial (Fin 2) k) m := by
      ext a
      simpa using hfm a
    rw [← Finsupp.range_linearCombination, ← heq]
    exact LinearMap.range_eq_top.mpr hf

/-- The inherited grading on the kernel of a graded surjection is internal and finite.
Source: blueprint `theorem-riemann-roch-coherent-serre-duality`, proof, successive graded kernels
(blueprint: lem-sc-p1-graded-kernel-internal).

Proof: take finite homogeneous generating families for source and target using
`exists_finite_homogeneous_generators`, and turn their ranges into finite homogeneous spanning
sets. Apply `graded_kernel_finite` to obtain closure of the kernel under homogeneous components
and a finite homogeneous spanning set in the source. For a kernel element, its finite source
homogeneous decomposition therefore consists entirely of kernel elements. Viewing these
components as elements of the kernel gives existence of its inherited decomposition, while
uniqueness follows by applying the injective subtype map and source uniqueness. Thus the
comapped additive subgroups form an internal direct sum. The finite spanning set in the source
makes the kernel a finitely generated submodule, hence its carrier has `Module.Finite`.
Apply `exists_finite_homogeneous_generators` to this internal grading and use the standard
finsupp basis to identify the image of its surjection with the span of the generators.
Their finite range is the asserted homogeneous spanning set. Zero kernels and zero-rank
source modules use the empty generating set. -/
theorem graded_kernel_internal_finite {k : Type u} [Field k]
    {F : Type v} [AddCommGroup F] [Module (MvPolynomial (Fin 2) k) F]
    {M : Type w} [AddCommGroup M] [Module (MvPolynomial (Fin 2) k) M]
    [Module.Finite (MvPolynomial (Fin 2) k) F]
    [Module.Finite (MvPolynomial (Fin 2) k) M]
    (ℱ : ℤ → AddSubgroup F) (hF : DirectSum.IsInternal ℱ)
    (ℳ : ℤ → AddSubgroup M) (hM : DirectSum.IsInternal ℳ)
    (hsmulF : ∀ (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : F),
      s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℱ j → s • x ∈ ℱ ((n : ℤ) + j))
    (q : F →ₗ[MvPolynomial (Fin 2) k] M)
    (hgraded : ∀ (j : ℤ) (x : F), x ∈ ℱ j → q x ∈ ℳ j) :
    DirectSum.IsInternal (fun j ↦ (ℱ j).comap q.ker.subtype.toAddMonoidHom) ∧
    Module.Finite (MvPolynomial (Fin 2) k) q.ker ∧
    ∃ s : Set q.ker, s.Finite ∧
      (∀ x ∈ s, SetLike.IsHomogeneousElem
        (fun j ↦ (ℱ j).comap q.ker.subtype.toAddMonoidHom) x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = ⊤ := by
  classical
  let : DirectSum.Decomposition ℱ := hF.chooseDecomposition
  obtain ⟨hhom, t, ht, _, htspan⟩ := graded_kernel_finite ℱ hF ℳ hM hsmulF
    (finite_homogeneous_spanning ℱ hF hsmulF) q hgraded
  let 𝒦 : ℤ → AddSubgroup q.ker :=
    fun j ↦ (ℱ j).comap q.ker.subtype.toAddMonoidHom
  let inc : ∀ j : ℤ, 𝒦 j →+ ℱ j := fun j ↦
    { toFun := fun x ↦ ⟨x.val.val, x.property⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hmap : ∀ x : ⨁ j, 𝒦 j,
      DirectSum.coeAddMonoidHom ℱ (DirectSum.map inc x) =
        (DirectSum.coeAddMonoidHom 𝒦 x).val := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of j x => simp [inc]
    | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  have hK : DirectSum.IsInternal 𝒦 := by
    constructor
    · intro x y hxy
      have hinj : Function.Injective (DirectSum.map inc) :=
        (DirectSum.map_injective inc).mpr (by
          intro j a b hab
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun z : ℱ j ↦ z.val) hab)
      apply hinj
      exact hF.injective (by rw [hmap, hmap, hxy])
    · intro x
      let c : ∀ j : ℤ, 𝒦 j := fun j ↦
        ⟨⟨(DirectSum.decompose ℱ x.val j).val, hhom j x.property⟩,
          (DirectSum.decompose ℱ x.val j).property⟩
      refine ⟨∑ j ∈ (DirectSum.decompose ℱ x.val).support, DirectSum.of _ j (c j), ?_⟩
      apply Subtype.ext
      simp only [map_sum, DirectSum.coeAddMonoidHom_of, Submodule.coe_sum]
      exact DirectSum.sum_support_decompose ℱ x.val
  have : Module.Finite (MvPolynomial (Fin 2) k) q.ker :=
    Module.Finite.of_fg (Submodule.fg_def.mpr ⟨t, ht, htspan⟩)
  have hsK : ∀ (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : q.ker),
      s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ 𝒦 j → s • x ∈ 𝒦 ((n : ℤ) + j) := by
    intro n j s x hs hx
    exact hsmulF n j s x.val hs hx
  exact ⟨hK, inferInstance, finite_homogeneous_spanning 𝒦 hK hsK⟩

end MvPolynomial

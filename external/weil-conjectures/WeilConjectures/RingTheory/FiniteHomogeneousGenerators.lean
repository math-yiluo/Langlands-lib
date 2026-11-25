/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite homogeneous generators of a graded module

Source: Weil conjectures blueprint, `sec-picard-framework/det-thm-picard-duality`,
proof, construction of the initial graded free module from homogeneous generators
(blueprint: lem-sc-p1-finite-homogeneous-generators).
-/

@[expose] public section

universe u v

namespace MvPolynomial

/-- Every finitely generated graded module over `k[x₀,x₁]` has finitely many homogeneous
    generators, and these generators give a surjective graded map from a finite sum of shifts.

Source: blueprint `lem-sc-p1-graded-resolution.md`, proof, construction of the initial graded
free module from homogeneous generators (blueprint: lem-sc-p1-finite-homogeneous-generators).

Proof: direct-sum induction shows that all homogeneous elements span the module. Finite
generation extracts a finite subset of this spanning set. Enumerate it by `Fin r` and choose
a degree for each element. The linear-combination map has range equal to the span of this
family, hence is surjective. Its value on each basis vector is the chosen generator, and
compatibility of scalar multiplication with the grading gives the last clause. No nonzero
assumption is needed, so the zero module and empty generating family are included.
-/
theorem exists_finite_homogeneous_generators {k : Type u} [Field k]
    {M : Type v} [AddCommGroup M] [Module (MvPolynomial (Fin 2) k) M]
    [Module.Finite (MvPolynomial (Fin 2) k) M]
    (ℳ : ℤ → AddSubgroup M) (hℳ : DirectSum.IsInternal ℳ)
    (hsmul : ∀ (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : M),
      s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℳ j →
        s • x ∈ ℳ ((n : ℤ) + j)) :
    ∃ (r : ℕ) (d : Fin r → ℤ) (m : Fin r → M)
      (_ : ∀ i, m i ∈ ℳ (d i))
      (f : (Fin r →₀ MvPolynomial (Fin 2) k) →ₗ[MvPolynomial (Fin 2) k] M),
      Function.Surjective f ∧
      (∀ i, f (Finsupp.single i 1) = m i) ∧
      (∀ (i : Fin r) (n : ℕ) (s : MvPolynomial (Fin 2) k),
        s ∈ homogeneousSubmodule (Fin 2) k n →
          f (s • Finsupp.single i 1) ∈ ℳ ((n : ℤ) + d i)) := by
  classical
  let R := MvPolynomial (Fin 2) k
  let H : Set M := {x | ∃ j, x ∈ ℳ j}
  let : DirectSum.Decomposition ℳ := hℳ.chooseDecomposition
  have hH : Submodule.span R H = ⊤ := by
    apply top_unique
    intro x _
    refine DirectSum.Decomposition.inductionOn ℳ ?_ ?_ ?_ x
    · exact Submodule.zero_mem _
    · intro j y
      exact Submodule.subset_span ⟨j, y.property⟩
    · intro y z hy hz
      exact Submodule.add_mem _ hy hz
  have hfg : (Submodule.span R H).FG := by
    rw [hH]
    exact Module.Finite.fg_top
  obtain ⟨S, hSH, hS⟩ := (Submodule.fg_span_iff_fg_span_finset_subset H).mp hfg
  obtain ⟨r, m, hmS⟩ := S.finite_toSet.fin_embedding
  have hmH : ∀ i, ∃ j, m i ∈ ℳ j := by
    intro i
    exact hSH (hmS ▸ Set.mem_range_self i)
  choose d hd using hmH
  have hmspan : Submodule.span R (Set.range m) = ⊤ := by
    rw [hmS, ← hS, hH]
  refine ⟨r, d, m, hd, Finsupp.linearCombination R m, ?_, ?_, ?_⟩
  · exact (span_range_eq_top_iff_surjective_finsuppLinearCombination R).mp hmspan
  · intro i
    exact (Finsupp.linearCombination_single (R := R) (v := ⇑m) 1 i).trans
      (one_smul R (m i))
  · intro i n s hs
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [Finsupp.linearCombination_single]
    exact hsmul n (d i) s (m i) hs (hd i)

end MvPolynomial

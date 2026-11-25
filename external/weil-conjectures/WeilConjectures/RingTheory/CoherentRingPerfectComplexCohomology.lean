/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.RingTheory.FinitePresentationKerRangeCokernel

/-! # Cohomology of finite projective complexes over coherent rings

Source: Stacks Project, More on Algebra, Lemma 0EWZ and Algebra, Lemma 05CX
(blueprint: lem-sc-coherent-ring-perfect-complex-cohomology).

The complex here is the affine module complex mentioned in
`lemma-coherent-base-change-invertible-sheaves--1`, not its associated complex of sheaves. Coherence
is expressed by the defining ideal condition of Stacks, Algebra, Definition 10.90.1 (section Tag
05CU).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Every cohomology module of a bounded complex of finite projective modules over a
commutative coherent ring is finitely presented.
Source: Stacks Project, More on Algebra, Lemma 0EWZ; Algebra, Lemmas 05CW and 05CX
(blueprint: lem-sc-coherent-ring-perfect-complex-cohomology).

Proof: Each term is finitely presented by
`lem-weil-pbc-finite-projective-finitely-presented`. Apply
`lem-sc-coherent-ring-fp-kernel-cokernel` to the differentials: their kernels (cycles)
and images (boundaries) are finitely presented. The differential squares to zero, so
boundaries include into cycles. Apply the same closure lemma to that inclusion; its
cokernel, the cohomology module, is finitely presented. This is also the strictly
perfect specialization of 0EWZ, using 05CX to identify coherent and finitely presented
modules. -/
theorem finitePresentation_homology_of_coherent
    {R : Type u} [CommRing R]
    (hR : ∀ I : Ideal R, I.FG → Module.FinitePresentation R I)
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hterms : ∀ n : ℤ, Module.Finite R (P.X n) ∧ Module.Projective R (P.X n))
    (q : ℤ) : Module.FinitePresentation R (P.homology q) := by
  -- Finite presentation of homology uses only the three terms adjacent to q.
  have _ := hbounded
  have hfp (n : ℤ) : Module.FinitePresentation R (P.X n) := by
    have := (hterms n).1
    have := (hterms n).2
    exact Module.finitePresentation_of_projective R (P.X n)
  let S := P.sc q
  have : Module.FinitePresentation R S.X₁ := hfp _
  have : Module.FinitePresentation R S.X₂ := hfp _
  have : Module.FinitePresentation R S.X₃ := hfp _
  have : Module.FinitePresentation R (LinearMap.ker S.g.hom) :=
    (Module.finitePresentation_ker_range_cokernel_of_fg_ideals hR S.g.hom).1
  have : Module.FinitePresentation R
      (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
    (Module.finitePresentation_ker_range_cokernel_of_fg_ideals
      hR S.moduleCatToCycles).2.2
  have : Module.FinitePresentation R S.moduleCatLeftHomologyData.H := by
    change Module.FinitePresentation R
      (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  exact Module.FinitePresentation.of_equiv S.moduleCatHomologyIso.toLinearEquiv.symm

end CochainComplex

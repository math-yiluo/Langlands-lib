/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SingularIdeal
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.RingTheory.LinearEquationLocalizationPolynomial
import WeilConjectures.RingTheory.SingularIdealLocalizationSmooth

/-!
# Factoring through a smooth algebra when the extended singular ideal is the unit ideal

Source: Stacks Project, Smoothing Ring Maps, Lemma 16.2.8, Tag 07EU (`lemma-final-solve`)
(blueprint: lem-weil-pbc-popescu-final-solve).
-/

@[expose] public section

universe u v w

namespace Algebra

/-- If the singular ideal of a finitely presented `R`-algebra `A` extends to the unit ideal
in `Λ`, the given map factors through a smooth `R`-algebra.
Source: Stacks Project, Smoothing Ring Maps, Lemma 16.2.8, Tag 07EU
(blueprint: lem-weil-pbc-popescu-final-solve).

Proof: (1) Unit-ideal extension gives finitely many `fᵢ ∈ singularIdeal R A` and `λᵢ ∈ Λ`
with `∑ α(fᵢ) λᵢ = 1` (definition node `def-weil-pbc-singular-ideal`).
(2) Set `B = A[x₁, …, xᵣ]/(∑ fᵢ xᵢ - 1)`. Evaluation `xᵢ ↦ λᵢ` descends to `B → Λ`,
and its composite with `A → B` is `α` by construction.
(3) Each `A_{fᵢ}` is smooth over `R`, by
`lem-weil-pbc-singular-ideal-localization-smooth`.
(4) Each `B_{fᵢ}` is a polynomial algebra in the other variables over `A_{fᵢ}`, by
`lem-weil-pbc-linear-equation-localization-polynomial`; it is smooth over `A_{fᵢ}` by
`lem-weil-pbc-polynomial-ring-smooth` and invariance under algebra isomorphism.
(5) Composition of smooth maps gives smoothness of `B_{fᵢ}` over `R`, by
`lem-weil-pbc-smooth-ring-map-base-change-composition`.
(6) The relation in `B` makes the images of the `fᵢ` generate its unit ideal, so locality
of smoothness gives smoothness of `B` over `R` by
`lem-weil-pbc-smooth-ring-map-local-on-cover`. For an empty family, `Λ` and `B` are zero
rings and the same argument uses the empty cover. The carrier of `B` can be taken in
`Type v`, since this explicit polynomial quotient over `A : Type v` lives there. -/
theorem exists_smooth_factorization_of_singularIdeal_map_eq_top
    {R : Type u} {A : Type v} {Λ : Type w}
    [CommRing R] [CommRing A] [CommRing Λ] [Algebra R A] [Algebra R Λ]
    [FinitePresentation R A] (α : A →ₐ[R] Λ)
    (h : Ideal.map α.toRingHom (singularIdeal R A) = ⊤) :
    ∃ (B : Type v) (_ : CommRing B) (_ : Algebra R B),
      Smooth R B ∧ ∃ (β : A →ₐ[R] B) (γ : B →ₐ[R] Λ), γ.comp β = α := by
  classical
  have hmem : (1 : Λ) ∈ Submodule.span Λ
      (α.toRingHom '' (singularIdeal R A : Set A)) := by
    change (1 : Λ) ∈ Ideal.map α.toRingHom (singularIdeal R A)
    rw [h]
    trivial
  obtain ⟨r, c, g, hg⟩ := Submodule.mem_span_set'.mp hmem
  choose f hf hα using fun i ↦ (g i).property
  have hsum : ∑ i : Fin r, α (f i) * c i = 1 := by
    simp only [smul_eq_mul, ← hα] at hg
    change ∑ i : Fin r, c i * α (f i) = 1 at hg
    simpa only [mul_comm] using hg
  let I : Ideal (MvPolynomial (Fin r) A) :=
    Ideal.span {(∑ j : Fin r, MvPolynomial.C (f j) * MvPolynomial.X j) - 1}
  let B := MvPolynomial (Fin r) A ⧸ I
  let q := Ideal.Quotient.mk I
  let β : A →ₐ[R] B := IsScalarTower.toAlgHom R A B
  let ev : MvPolynomial (Fin r) A →ₐ[R] Λ :=
    { MvPolynomial.eval₂Hom α.toRingHom c with
      commutes' := fun x ↦ by simp [AlgHom.commutes] }
  have hev : ∀ p ∈ I, ev p = 0 := by
    change I ≤ RingHom.ker ev.toRingHom
    apply Ideal.span_le.mpr
    intro p hp
    rcases hp with rfl
    simpa [ev] using sub_eq_zero.mpr hsum
  let γ : B →ₐ[R] Λ := Ideal.Quotient.liftₐ I ev hev
  refine ⟨B, inferInstance, inferInstance, ?_, β, γ, ?_⟩
  · have hcover : Ideal.span (Set.range (algebraMap A B ∘ f)) = ⊤ := by
      apply (Ideal.eq_top_iff_one _).mpr
      have hrel : (∑ j : Fin r, algebraMap A B (f j) * q (MvPolynomial.X j)) = 1 := by
        have hz := Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span (Set.mem_singleton
            ((∑ j : Fin r, MvPolynomial.C (f j) * MvPolynomial.X j) - 1)))
        change q ((∑ j : Fin r, MvPolynomial.C (f j) * MvPolynomial.X j) - 1) = 0 at hz
        change (∑ j : Fin r, q (MvPolynomial.C (f j)) * q (MvPolynomial.X j)) = 1
        simpa only [map_sub, map_sum, map_mul, map_one, sub_eq_zero] using hz
      rw [← hrel]
      exact Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_right _ _
        (Ideal.subset_span ⟨j, rfl⟩)
    have hlocal (i : Fin r) : Smooth R (Localization.Away (algebraMap A B (f i))) := by
      let Af := Localization.Away (f i)
      let Bf := Localization.Away (algebraMap A B (f i))
      let : Algebra Af Bf := (Localization.awayMap (algebraMap A B) (f i)).toAlgebra
      have : Smooth R Af := smooth_localization_of_mem_singularIdeal R A (f i) (hf i)
      obtain ⟨e, _⟩ := MvPolynomial.linearEquationLocalizationPolynomial A r f i
      have : Smooth Af (MvPolynomial {j : Fin r // j ≠ i} Af) :=
        ⟨inferInstance, inferInstance⟩
      have : Smooth Af Bf := Smooth.of_equiv e
      have : IsScalarTower R Af Bf := by
        apply IsScalarTower.of_algebraMap_eq
        intro x
        change algebraMap R Bf x =
          Localization.awayMap (algebraMap A B) (f i) (algebraMap R Af x)
        rw [IsScalarTower.algebraMap_apply R A Af]
        change algebraMap R Bf x =
          IsLocalization.Away.map Af Bf (algebraMap A B) (f i)
            (algebraMap A Af (algebraMap R A x))
        simp only [IsLocalization.Away.map, IsLocalization.map_eq]
        rw [← IsScalarTower.algebraMap_apply A B Bf,
          ← IsScalarTower.algebraMap_apply R A Bf]
      exact Smooth.comp R Af Bf
    have : FinitePresentation R B :=
      FinitePresentation.quotient (R := R) (A := MvPolynomial (Fin r) A)
        (Submodule.fg_span_singleton _)
    refine ⟨?_, inferInstance⟩
    apply smoothLocus_eq_univ_iff.mp
    apply Set.eq_univ_of_univ_subset
    rw [← TopologicalSpace.Opens.coe_top,
      ← PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hcover]
    simp only [TopologicalSpace.Opens.coe_iSup, Set.iUnion_subset_iff]
    intro b hb
    obtain ⟨i, rfl⟩ := hb
    exact basicOpen_subset_smoothLocus_iff_smooth.mpr (hlocal i)
  · ext a
    change ev (MvPolynomial.C a) = α a
    simp [ev]

end Algebra

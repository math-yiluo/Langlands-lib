/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.RingTheory.PopescuLiftOnceCore
import WeilConjectures.RingTheory.NakayamaNilpotent

/-!
# Factoring through a quotient of a smooth algebra over a square-zero base

Source: Stacks Project, Smoothing Ring Maps, Lemma 16.5.1, Tag 07CK
(blueprint: lem-weil-pbc-popescu-lift-once).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace Algebra

/-- A map from a finitely presented algebra factors through `B / J`, with `B` smooth and
`J` finitely generated and contained in the extended square-zero base ideal, provided the
reduction of the target algebra is a filtered colimit of smooth algebras.

Source: Stacks Project, Smoothing Ring Maps, Lemma 16.5.1, Tag 07CK
(blueprint: lem-weil-pbc-popescu-lift-once).

Proof (the twelve steps of the node):
1. Reduce a finite polynomial presentation of `A` modulo `I`. This gives a finite
   presentation of `A / IA` over `R / I` and an induced map to `Λ / IΛ`.
2. Use lem-weil-pbc-colimit-standard-smooth-algebras (07CI) to express `Λ / IΛ` as a
   filtered colimit of standard smooth algebras. Use
   lem-weil-pbc-filtered-colimit-algebras-elementwise and
   lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit (00QO) to factor
   the reduced map through a standard smooth algebra `Bbar`.
3. By lem-weil-pbc-finite-presentation-over-finite-type-algebra (00F4), present `Bbar`
   by finitely many variables `t` and relations `gbar` over `A / IA`.
4. Lift the images of `t` to elements `λ` of `Λ` and lift `gbar` to polynomials `g`
   over `A`. Their evaluations lie in `IΛ`; write each as a finite sum `ε * μ`
   with `ε` in `I`.
5. Adjoin variables `δ` to `A[t]` and impose the relations `g - sum ε * δ`.
   The resulting algebra `A'` maps to `Λ` by `t ↦ λ`, `δ ↦ μ`, extending the original
   map. It is finitely presented over `R` by
   lem-weil-pbc-finite-presentation-base-change-composition.
6. Modulo `I`, the algebra `A'` is `Bbar[δ]`, hence standard smooth. Choose a
   standard smooth presentation with an invertible Jacobian minor determinant.
7. Lift its equations to `R`, and invert the lifted determinant by adjoining one
   variable with relation `x * determinant - 1`. The resulting algebra `B` is
   standard smooth: the enlarged Jacobian minor has determinant the square of the
   original determinant. It is smooth by lem-weil-pbc-standard-smooth-is-smooth.
8. Reduction identifies `B / IB` with `A' / IA'`: the extra variable is the inverse
   of the Jacobian determinant. Check the inverse maps on all generators.
9. By lem-weil-pbc-smooth-ring-map-square-zero-lifting (00TN), lift the map
   `B → A' / IA'` to `θ : B → A'`, since `(IA')² = 0`. Its reduction is the
   isomorphism from step 8.
10. Apply lem-weil-pbc-nakayama-nilpotent (00DV) to conclude that `θ` is surjective.
11. Put `J = ker θ`. Injectivity modulo `I` gives `J ≤ IB`. Finite presentation of
    `A'` and lem-weil-pbc-finite-presentation-surjection-kernel-fg (00R2) show the
    kernel of the polynomial presentation mapping to `A'` is finitely generated.
    Its image under the surjection to `B` is `J`, so `J` is finitely generated.
12. Identify `B / J` with `A'` and compose the maps from `A` and to `Λ`.
    Their composite is the original algebra map by step 5. -/
theorem exists_smooth_quotient_factorization
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) (hI : I ^ 2 = ⊥)
    (hΛ :
      ObjectProperty.ind.{max u v}
        (fun C : CommAlgCat.{max u v} (R ⧸ I) ↦ Smooth (R ⧸ I) C)
        (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))
    (A : Type w) [CommRing A] [Algebra R A] [FinitePresentation R A]
    (φ : A →ₐ[R] Λ) :
    ∃ (B : Type (max u v w)) (_ : CommRing B) (_ : Algebra R B),
      Smooth R B ∧ ∃ (J : Ideal B), J.FG ∧ J ≤ I.map (algebraMap R B) ∧
        ∃ (ψ : A →ₐ[R] B ⧸ J) (χ : B ⧸ J →ₐ[R] Λ), χ.comp ψ = φ := by
  classical
  obtain ⟨A', _, _, hfp, ι, φ', hφ, B, _, _, hB, ⟨e⟩⟩ :=
    exists_smooth_reduction_factorization R Λ I hΛ A φ
  let IA := I.map (algebraMap R A')
  let IB := I.map (algebraMap R B)
  have hIA : IA ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, hI, Ideal.map_bot]
  let γ : B →ₐ[R] A' ⧸ IA := e.toAlgHom.comp (Ideal.Quotient.mkₐ R IB)
  obtain ⟨θ, hθ⟩ := FormallySmooth.comp_surjective R B IA hIA γ
  have hs : Function.Surjective θ := by
    apply RingTheory.surjective_of_surjective_mod_nilpotent R B A' I θ.toLinearMap
      ⟨2, by decide, hI⟩
    intro y
    let E := Submodule.quotEquivOfEq (I • (⊤ : Submodule R A'))
      (IA.restrictScalars R) (Ideal.smul_top_eq_map I)
    obtain ⟨b, hb⟩ := e.surjective (E y)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨(I • (⊤ : Submodule R B)).mkQ x, E.injective ?_⟩
    change E (Submodule.Quotient.mk (θ x)) = E y
    rw [Submodule.quotEquivOfEq_mk]
    exact (DFunLike.congr_fun hθ x).trans hb
  let J := RingHom.ker θ.toRingHom
  have hJfg : J.FG := FinitePresentation.ker_fG_of_surjective θ hs
  have hJI : J ≤ IB := by
    intro b hb
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply e.injective
    have hz : θ b = 0 := hb
    have he := DFunLike.congr_fun hθ b
    change Ideal.Quotient.mk IA (θ b) = e (Ideal.Quotient.mk IB b) at he
    rw [hz, map_zero] at he
    exact he.symm.trans (map_zero e).symm
  let q : (B ⧸ J) ≃ₐ[R] A' := Ideal.quotientKerAlgEquivOfSurjective hs
  refine ⟨B, inferInstance, inferInstance, hB, J, hJfg, hJI, ?_⟩
  let ψ : A →ₐ[R] B ⧸ J := q.symm.toAlgHom.comp ι
  let χ : B ⧸ J →ₐ[R] Λ := φ'.comp q.toAlgHom
  refine ⟨ψ, χ, ?_⟩
  apply AlgHom.ext
  intro x
  change φ' (q (q.symm (ι x))) = φ x
  rw [q.apply_symm_apply]
  exact DFunLike.congr_fun hφ x

end Algebra

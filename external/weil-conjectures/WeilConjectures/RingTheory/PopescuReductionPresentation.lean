/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Smooth.StandardSmooth
import WeilConjectures.RingTheory.PopescuReductionPresentationCore
import WeilConjectures.RingTheory.PopescuReductionPresentationFromFactor

/-! # Polynomial data for a standard smooth stage modulo an ideal -/

@[expose] public section

universe u v w

open CategoryTheory

namespace Algebra

/-- The first four construction steps of Stacks Project, Tag 07CK (lemma-lift-once).
No factor algebra over `R` is constructed in this lemma.

Proof: Base change a finite presentation of `A` to `R/I`. Factor the resulting map
into the given filtered colimit through a standard smooth stage, using finite
presentation (Tags 00QO and 07C3). If necessary use a small finite polynomial
presentation of the source to perform this factorization in the diagram's universe.
The stage is finitely presented over `R/I`; since `A/IA` is finite type over `R/I`,
Tag 00F4 gives a finite polynomial presentation over `A/IA`. Lift its generators'
images to `Λ` and its finitely many equations coefficientwise to `A`. Their evaluations
map to zero in `Λ/IΛ`, because the reduced evaluation factors through the stage.
Thus they belong to `IΛ`. The quotient defined by the reduced equations is isomorphic
to that stage, so is standard smooth. Surjectivity of quotient maps proves the lifting
claims even for empty presentations, the zero ring, and `I = top`.
(blueprint: lem-weil-pbc-popescu-reduction-presentation) -/
theorem exists_popescu_reduction_presentation
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R)
    (hΛ : ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} (R ⧸ I) ↦ IsStandardSmooth (R ⧸ I) C)
      (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))
    (A : Type w) [CommRing A] [Algebra R A] [FinitePresentation R A]
    (φ : A →ₐ[R] Λ) :
    ∃ (n m : ℕ) (g : Fin m → MvPolynomial (Fin n) A) (lifts : Fin n → Λ),
      (∀ i, MvPolynomial.eval₂ φ.toRingHom lifts (g i) ∈ I.map (algebraMap R Λ)) ∧
      IsStandardSmooth (R ⧸ I)
        (MvPolynomial (Fin n) (A ⧸ I.map (algebraMap R A)) ⧸
          Ideal.span (Set.range fun i ↦
            MvPolynomial.map (Ideal.Quotient.mk (I.map (algebraMap R A))) (g i))) := by
  obtain ⟨C, hCring, hCalg, hC, β, δ, hfactor⟩ :=
    exists_popescu_reduction_factor R Λ I hΛ A φ
  let _ := hCring
  let _ := hCalg
  obtain ⟨n, m, g, lifts, h_eval, hstd⟩ :=
    exists_popescu_reduction_presentation_of_factor R Λ I A φ C hC β δ hfactor
  exact ⟨n, m, g, lifts, h_eval, hstd⟩

end Algebra

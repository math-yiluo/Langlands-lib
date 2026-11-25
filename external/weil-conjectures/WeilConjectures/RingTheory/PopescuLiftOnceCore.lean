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
import WeilConjectures.RingTheory.IndStandardSmooth
import WeilConjectures.RingTheory.PopescuStandardReductionFactor
import WeilConjectures.RingTheory.StandardSmoothQuotientLift
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

@[expose] public section

universe u v w

open CategoryTheory

namespace Algebra

/-- The presentation construction preceding square-zero lifting in Popescu's lemma.

Source: Stacks Project, Smoothing Ring Maps, Lemma 16.5.1, Tag 07CK,
proof lines 1255--1296 (blueprint: lem-weil-pbc-popescu-lift-once-core).

Proof: Reduce a finite presentation of `A` modulo `I`. Express the target reduction
as a filtered colimit of standard smooth algebras using Tag 07CI, and factor the
reduced map through one stage by finite presentation (Tag 00QO). This stage is
finitely presented over `A / IA` by Tag 00F4; write it as `(A / IA)[t] / (gbar)`.
Lift its finitely many generators to `Lambda`, and lift the relations to `A[t]`.
Their evaluations lie in `I Lambda`, hence each is a finite sum `epsilon * mu`
with `epsilon` in `I`. Define `A' = A[t, delta] / (g - sum epsilon * delta)`;
evaluation at the chosen lifts and at `mu` gives `phi'`, extending `phi`.
There are finitely many generators and relations, so `A'` is finitely presented
by composition (Tag 00F4). Modulo `I` it is the standard smooth stage with the
variables `delta` adjoined, so it has a standard smooth presentation
`(R / I)[x] / (fbar)` with invertible Jacobian minor `Dbar`.
Lift the equations to `R[x]`, with Jacobian minor `D`, and set
`B = R[x, z] / (f, z * D - 1)`. The enlarged Jacobian minor has determinant
`D^2`, a unit in `B`, so `B` is standard smooth and thus smooth (Tag 00T7).
Reduction identifies `B / IB` with `A' / IA'`: send `x` to the presentation
generators and `z` to the inverse of `Dbar`; the inverse sends the presentation
generators to `x`. Both composites fix every generator, including `z` by uniqueness
of the inverse of `Dbar`. These are `R`-algebra maps. No square-zero hypothesis is
used in this presentation construction, only in the subsequent lifting. -/
theorem exists_smooth_reduction_factorization
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R)
    (hΛ : ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} (R ⧸ I) ↦ Smooth (R ⧸ I) C)
      (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))
    (A : Type w) [CommRing A] [Algebra R A] [FinitePresentation R A]
    (φ : A →ₐ[R] Λ) :
    ∃ (A' : Type (max u v w)) (_ : CommRing A') (_ : Algebra R A'),
      FinitePresentation R A' ∧
      ∃ (ι : A →ₐ[R] A') (φ' : A' →ₐ[R] Λ), φ'.comp ι = φ ∧
      ∃ (B : Type (max u v w)) (_ : CommRing B) (_ : Algebra R B),
        Smooth R B ∧
          Nonempty ((B ⧸ I.map (algebraMap R B)) ≃ₐ[R]
            (A' ⧸ I.map (algebraMap R A'))) := by
  have hstd := ind_isStandardSmooth_of_ind_smooth (R ⧸ I)
    (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))) hΛ
  obtain ⟨A', hring, halg, hfp, ι, φ', hcomp, hred⟩ :=
    exists_standardSmooth_reduction_factorization R Λ I hstd A φ
  let := hring
  let := halg
  let := hred
  obtain ⟨B, hBring, hBalg, hBstd, ⟨e⟩⟩ :=
    exists_standardSmooth_quotient_lift R I (A' ⧸ I.map (algebraMap R A'))
  let := hBring
  let := hBalg
  let := hBstd
  exact ⟨A', hring, halg, hfp, ι, φ', hcomp, B, hBring, hBalg,
    inferInstance, ⟨e.restrictScalars R⟩⟩

end Algebra

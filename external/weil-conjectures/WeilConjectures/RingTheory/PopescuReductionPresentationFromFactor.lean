/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuReductionPresentationCore
import Mathlib.RingTheory.Extension.Presentation.Basic

/-! Lifting a finite polynomial presentation from a reduced standard smooth factor. -/

@[expose] public section

universe u v w

open CategoryTheory

namespace Algebra

/-- Lift a finite presentation of the standard smooth reduced factor.
Source: Stacks Project, Tag 07CK, steps 3--4; Tag 00F4(4).

Regard `C` as an `A/IA`-algebra via `β`. Since `A/IA` is finite type over
`R/I` and `C` is finitely presented over `R/I`, `C` is finitely presented over
`A/IA`. Choose a finite presentation. Lift each relation coefficientwise to `A`
and each generator image under `δ` to `Λ`, using quotient surjectivity. The
factorization identity identifies evaluation modulo `IΛ` with evaluation in `C`
followed by `δ`, so each lifted relation evaluates into `IΛ`. The reduced quotient
is isomorphic to `C` over `R/I`, and standard smoothness transports along this
isomorphism. The finite-presentation hypothesis on `A` is essential (the old
statement failed for the augmentation from infinitely many polynomial variables).
(blueprint: new-lem-popescu-reduction-presentation-from-factor)
-/
theorem exists_popescu_reduction_presentation_of_factor
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) (A : Type w) [CommRing A] [Algebra R A] [FinitePresentation R A]
    (φ : A →ₐ[R] Λ)
    (C : Type (max u v w)) [CommRing C] [Algebra (R ⧸ I) C]
    (hC : IsStandardSmooth (R ⧸ I) C)
    (β : A ⧸ I.map (algebraMap R A) →ₐ[R ⧸ I] C)
    (δ : C →ₐ[R ⧸ I] Λ ⧸ I.map (algebraMap R Λ))
    (hfactor : δ.comp β = reducedAlgHom R Λ I A φ) :
    ∃ (n m : ℕ) (g : Fin m → MvPolynomial (Fin n) A) (lifts : Fin n → Λ),
      (∀ i, MvPolynomial.eval₂ φ.toRingHom lifts (g i) ∈
        I.map (algebraMap R Λ)) ∧
      IsStandardSmooth (R ⧸ I)
        (MvPolynomial (Fin n) (A ⧸ I.map (algebraMap R A)) ⧸
          Ideal.span (Set.range fun i ↦
            MvPolynomial.map (Ideal.Quotient.mk (I.map (algebraMap R A))) (g i))) := by
  classical
  let A₀ := A ⧸ I.map (algebraMap R A)
  let qA := Ideal.Quotient.mk (I.map (algebraMap R A))
  let qΛ := Ideal.Quotient.mk (I.map (algebraMap R Λ))
  let : Algebra A₀ C := β.toRingHom.toAlgebra
  have : IsScalarTower (R ⧸ I) A₀ C := IsScalarTower.of_algHom β
  have : FiniteType (R ⧸ I) A₀ :=
    FiniteType.of_restrictScalars_finiteType R (R ⧸ I) A₀
  have : IsStandardSmooth (R ⧸ I) C := hC
  have : FinitePresentation A₀ C :=
    FinitePresentation.of_restrict_scalars_finitePresentation (R ⧸ I) A₀ C
  obtain ⟨n, m, ⟨P⟩⟩ := Presentation.exists_presentation_fin A₀ C
  have hrel := fun i ↦ MvPolynomial.map_surjective qA
    Ideal.Quotient.mk_surjective (P.relation i)
  choose g hg using hrel
  have hval := fun i ↦ Ideal.Quotient.mk_surjective (δ (P.val i))
  choose lifts hlifts using hval
  refine ⟨n, m, g, lifts, ?_, ?_⟩
  · have hcoeff : qΛ.comp φ.toRingHom = δ.toRingHom.comp (β.toRingHom.comp qA) := by
      ext a
      have h := DFunLike.congr_fun hfactor (qA a)
      simpa [reducedAlgHom, qA, qΛ] using h.symm
    have hev (p : MvPolynomial (Fin n) A) :
        qΛ (MvPolynomial.eval₂ φ.toRingHom lifts p) =
          δ (MvPolynomial.aeval P.val (MvPolynomial.map qA p)) := by
      rw [MvPolynomial.hom_eval₂, hcoeff]
      change _ = δ.toRingHom (MvPolynomial.eval₂ (algebraMap A₀ C) P.val
        (MvPolynomial.map qA p))
      rw [MvPolynomial.hom_eval₂, MvPolynomial.eval₂_map]
      simp only [qΛ, hlifts]
      rfl
    intro i
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [hev, hg, P.aeval_val_relation, map_zero]
  · have hI : Ideal.span (Set.range fun i ↦ MvPolynomial.map qA (g i)) = P.ker := by
      simpa only [hg] using P.span_range_relation_eq_ker
    let e := (Ideal.quotientEquivAlgOfEq (R ⧸ I) hI).trans
      (P.quotientEquiv.restrictScalars (R ⧸ I))
    exact IsStandardSmooth.of_algEquiv e.symm

end Algebra

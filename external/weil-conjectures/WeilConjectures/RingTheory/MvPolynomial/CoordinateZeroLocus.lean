/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!

# Points of affine space with coordinates in finite sets

Let `K` be a field, `ι` a finite type and, for each `i : ι`, `f i` a nonzero polynomial in one
variable. The primes of `K[X_i : i ∈ ι]` containing every `f i (X i)` are finitely many, and all
maximal (`MvPolynomial.finite_zeroLocus_range_aeval_X`,
`MvPolynomial.isMaximal_of_mem_zeroLocus_range_aeval_X`): the quotient by these elements is a
finite-dimensional, hence artinian, `K`-algebra.

Geometrically: the set of points of `𝔸ⁿ_K` all of whose coordinates lie in given finite sets of
closed points of the line is a finite set of closed points. This is the "finite product of finite
sets" in the finite-support step of Gabber's Künneth formula (blueprint
`proposition-external-kunneth-formula-nearby-cycles`).

-/

@[expose] public section

open Polynomial

namespace MvPolynomial

variable {K : Type*} [Field K] {ι : Type*} [Finite ι] (f : ι → K[X])

/-- The quotient of `K[X_i : i ∈ ι]` by the elements `f i (X i)`. -/
abbrev CoordinateQuotient : Type _ :=
  MvPolynomial ι K ⧸ Ideal.span (Set.range fun i ↦ Polynomial.aeval (X (R := K) i) (f i))

variable {f}

omit [Finite ι] in
/-- The quotient of `K[X_i : i ∈ ι]` by nonzero `f i (X i)` is integral over `K`. -/
lemma isIntegral_coordinateQuotient (hf : ∀ i, f i ≠ 0) :
    Algebra.IsIntegral K (CoordinateQuotient f) := by
  set I := Ideal.span (Set.range fun i ↦ Polynomial.aeval (X (R := K) i) (f i))
  constructor
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective K I a
  change p ∈ (integralClosure K (CoordinateQuotient f)).comap (Ideal.Quotient.mkₐ K I)
  induction p using MvPolynomial.induction_on with
  | C a => exact (integralClosure K _).algebraMap_mem a
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp =>
    refine mul_mem hp ?_
    change IsIntegral K (Ideal.Quotient.mkₐ K I (X i))
    refine IsAlgebraic.isIntegral ⟨f i, hf i, ?_⟩
    rw [Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨i, rfl⟩

/-- The quotient of `K[X_i : i ∈ ι]` by nonzero `f i (X i)` is artinian. -/
lemma isArtinianRing_coordinateQuotient (hf : ∀ i, f i ≠ 0) :
    IsArtinianRing (CoordinateQuotient f) := by
  set I := Ideal.span (Set.range fun i ↦ Polynomial.aeval (X (R := K) i) (f i))
  have := isIntegral_coordinateQuotient hf
  have : Algebra.FiniteType K (CoordinateQuotient f) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K I)
      (Ideal.Quotient.mkₐ_surjective K I)
  have : Module.Finite K (CoordinateQuotient f) := Algebra.IsIntegral.finite
  exact IsArtinianRing.of_finite K _

omit [Finite ι] in
/-- The primes containing all the `f i (X i)` are those pulled back from the quotient. -/
lemma zeroLocus_range_aeval_X :
    PrimeSpectrum.zeroLocus (Set.range fun i ↦ Polynomial.aeval (X (R := K) i) (f i)) =
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk
        (Ideal.span (Set.range fun i ↦ Polynomial.aeval (X (R := K) i) (f i))))) := by
  rw [range_comap_of_surjective (hf := Ideal.Quotient.mk_surjective), Ideal.mk_ker,
    PrimeSpectrum.zeroLocus_span]

/-- Finitely many primes of `K[X_i : i ∈ ι]` contain all the `f i (X i)`, for nonzero `f i`. -/
theorem finite_zeroLocus_range_aeval_X (hf : ∀ i, f i ≠ 0) :
    (PrimeSpectrum.zeroLocus
      (Set.range fun i ↦ Polynomial.aeval (X (R := K) i) (f i))).Finite := by
  have := isArtinianRing_coordinateQuotient hf
  rw [zeroLocus_range_aeval_X]
  exact Set.finite_range _

/-- A prime of `K[X_i : i ∈ ι]` containing all the `f i (X i)`, for nonzero `f i`, is maximal. -/
theorem isMaximal_of_mem_zeroLocus_range_aeval_X (hf : ∀ i, f i ≠ 0)
    {P : PrimeSpectrum (MvPolynomial ι K)}
    (hP : P ∈ PrimeSpectrum.zeroLocus
      (Set.range fun i ↦ Polynomial.aeval (X (R := K) i) (f i))) :
    P.asIdeal.IsMaximal := by
  have := isArtinianRing_coordinateQuotient hf
  rw [zeroLocus_range_aeval_X] at hP
  obtain ⟨Q, rfl⟩ := hP
  exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective

end MvPolynomial

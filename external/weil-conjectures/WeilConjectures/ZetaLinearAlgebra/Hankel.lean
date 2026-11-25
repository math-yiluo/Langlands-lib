/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Pi
public import WeilConjectures.Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import WeilConjectures.ZetaLinearAlgebra.ShiftSpan

@[expose] public section

/-!
# Rationality of a power series descends along a field extension

Let `K ⊆ L` be fields. A power series `f ∈ K⟦X⟧` admits a normalized fraction `A / B`, that is
a pair of polynomials with `B.coeff 0 = 1` and `f * B = A`, over `K` if and only if it admits
one over `L`.

The proof is linear algebra: by `WeilConjectures.ZetaLinearAlgebra.ShiftSpan`, rationality of
`f` is equivalent to finite-dimensionality of the span of the shifts of its coefficient
sequence, and such a span cannot shrink when the field of coefficients is enlarged, because
linear independence of finitely many sequences is witnessed by a nonvanishing determinant
(`linearIndependent_algebraMap_comp_iff'`). No Hankel matrix appears: the shift span plays the
role of the Hankel rank throughout.

## Main statements

- `rank_shiftSpan_le_finrank_shiftSpan_algebraMap_comp` and
  `finiteDimensional_shiftSpan_of_algebraMap_comp`: the shift span of a sequence does not
  shrink when the coefficients are pushed to a larger field.
- `PowerSeries.exists_normalized_fraction_map_iff`: a power series over `K` is rational over
  `K` if and only if it is rational over an extension field `L`.
- `PowerSeries.exists_normalized_fraction_of_map_rat`: the case `K = ℚ` of a
  characteristic-zero extension field, which is what the rationality of the zeta function
  needs.
-/

open scoped Polynomial PowerSeries

section ShiftSpan

variable {K : Type*} (L : Type*) [Field K] [Field L] [Algebra K L]

/-- Coefficientwise extension of scalars along a field extension maps the shift span of a
sequence into the shift span of the pushed sequence. -/
lemma shiftSpan_map_le (a : ℕ → K) :
    (shiftSpan K a).map ((Algebra.linearMap K L).compLeft ℕ)
      ≤ (shiftSpan L (algebraMap K L ∘ a)).restrictScalars K := by
  rw [Submodule.map_le_iff_le_comap]
  refine shiftSpan_le fun m => ?_
  have heq : (Algebra.linearMap K L).compLeft ℕ ((⇑(seqShift K))^[m] a)
      = (⇑(seqShift L))^[m] (algebraMap K L ∘ a) := by
    funext n
    simp [LinearMap.compLeft, iterate_seqShift_apply]
  simp only [Submodule.mem_comap, Submodule.restrictScalars_mem, heq]
  exact iterate_seqShift_mem_shiftSpan (algebraMap K L ∘ a) m

/-- An element of the shift span of `a` stays in the shift span after pushing its values
along a field extension. -/
lemma algebraMap_comp_mem_shiftSpan {a x : ℕ → K} (hx : x ∈ shiftSpan K a) :
    algebraMap K L ∘ x ∈ shiftSpan L (algebraMap K L ∘ a) :=
  shiftSpan_map_le L a (Submodule.mem_map_of_mem hx)

/-- The shift span over the base field is at most as large as the shift span of the pushed
sequence over the extension field. -/
theorem rank_shiftSpan_le_finrank_shiftSpan_algebraMap_comp (a : ℕ → K)
    [FiniteDimensional L (shiftSpan L (algebraMap K L ∘ a))] :
    Module.rank K (shiftSpan K a)
      ≤ (Module.finrank L (shiftSpan L (algebraMap K L ∘ a)) : Cardinal) := by
  refine rank_le fun s hs => ?_
  have hu : LinearIndependent K fun i : s => ((i : shiftSpan K a) : ℕ → K) :=
    hs.map' (shiftSpan K a).subtype (Submodule.ker_subtype _)
  have hmem : ∀ i : s, algebraMap K L ∘ ((i : shiftSpan K a) : ℕ → K)
      ∈ shiftSpan L (algebraMap K L ∘ a) := fun i => algebraMap_comp_mem_shiftSpan L i.1.2
  have hw : LinearIndependent L fun i : s =>
      (⟨_, hmem i⟩ : shiftSpan L (algebraMap K L ∘ a)) :=
    LinearIndependent.of_comp (shiftSpan L (algebraMap K L ∘ a)).subtype
      (linearIndependent_algebraMap_comp_iff'.2 hu)
  simpa [Fintype.card_coe] using hw.fintype_card_le_finrank

/-- Hankel descent for shift spans: if the shift span of the pushed sequence is
finite-dimensional over the extension field, then the shift span of the original sequence is
finite-dimensional over the base field. -/
theorem finiteDimensional_shiftSpan_of_algebraMap_comp (a : ℕ → K)
    [FiniteDimensional L (shiftSpan L (algebraMap K L ∘ a))] :
    FiniteDimensional K (shiftSpan K a) :=
  Module.rank_lt_aleph0_iff.mp <| lt_of_le_of_lt
    (rank_shiftSpan_le_finrank_shiftSpan_algebraMap_comp L a) Cardinal.natCast_lt_aleph0

end ShiftSpan

namespace PowerSeries

section

variable {K : Type*} (L : Type*) [Field K] [Field L] [Algebra K L]

/-- Hankel rationality descent: a power series over `K` admits a normalized fraction over `K`
if and only if it admits one over an extension field `L`. -/
theorem exists_normalized_fraction_map_iff (f : K⟦X⟧) :
    (∃ A B : L[X], B.coeff 0 = 1 ∧ map (algebraMap K L) f * (B : L⟦X⟧) = (A : L⟦X⟧)) ↔
      ∃ A B : K[X], B.coeff 0 = 1 ∧ f * (B : K⟦X⟧) = (A : K⟦X⟧) := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [exists_normalized_fraction_iff_finiteDimensional_shiftSpan] at h ⊢
    have hcoeff : (fun n => coeff n (map (algebraMap K L) f))
        = algebraMap K L ∘ fun n => coeff n f := funext fun n => by simp
    rw [hcoeff] at h
    exact finiteDimensional_shiftSpan_of_algebraMap_comp L _
  · rintro ⟨A, B, hB, hAB⟩
    refine ⟨A.map (algebraMap K L), B.map (algebraMap K L), by simp [hB], ?_⟩
    simp only [Polynomial.polynomial_map_coe, ← map_mul, hAB]

end

/-- Hankel rationality descent over the rationals: a power series with rational coefficients
which admits a normalized fraction over a field of characteristic zero admits one over `ℚ`.
This is the form the rationality of the zeta function uses. -/
theorem exists_normalized_fraction_of_map_rat (L : Type*) [Field L] [CharZero L] (f : ℚ⟦X⟧)
    (h : ∃ A B : L[X], B.coeff 0 = 1 ∧
      map (algebraMap ℚ L) f * (B : L⟦X⟧) = (A : L⟦X⟧)) :
    ∃ A B : ℚ[X], B.coeff 0 = 1 ∧ f * (B : ℚ⟦X⟧) = (A : ℚ⟦X⟧) :=
  (exists_normalized_fraction_map_iff L f).1 h

end PowerSeries

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Clearing equations and the inverse Jacobian

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07F9,
`lemma-delocalize-weak`, the denominator-clearing paragraphs.
(blueprint: lem-weil-pbc-popescu-weak-clear-core)
-/

@[expose] public section

universe u v

namespace Algebra

open MvPolynomial

/-- Clear the defining equations and inverse-Jacobian certificate, retaining generation
of the localized kernel. No auxiliary relations are involved.
Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07F9,
`lemma-delocalize-weak`, the denominator-clearing paragraphs.
(blueprint: lem-weil-pbc-popescu-weak-clear-core)

Proof: Identify the polynomial ring over Rₚ with the localization of the polynomial
ring over R at the constant polynomials from R \ p. For each relation of P, multiply
by a common denominator of its finitely many coefficients, obtaining fⱼ over R.
The coefficient extension of fⱼ is a scalar unit times P.relation j. Consequently
these extensions generate exactly the kernel of evaluation, and fⱼ vanishes in D.
Partial differentiation commutes with coefficient extension and the scalar factors
have derivative zero, so the new Jacobian determinant is the old determinant times
the product of these units. Its evaluation in D is therefore a unit. Surjectivity
of the presentation evaluation lifts its inverse to a localized polynomial. The
product of that lift and the determinant differs from 1 by an element of the ideal
of the extended fⱼ. Express this membership as a finite linear combination. Clear
all coefficients in the inverse and in this combination with one denominator
outside p. The resulting polynomial identity holds after localization; multiply
by one further scalar outside p annihilating its error in the localization kernel.
This gives C s - h * det ∈ (f), with s outside p. The empty relation family uses
empty determinant and products equal to 1. -/
theorem exists_cleared_submersive_presentation_core
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {D : Type v} [CommRing D] [Algebra (Localization.AtPrime p) D]
    [Algebra R D] [IsScalarTower R (Localization.AtPrime p) D]
    (n m c : ℕ) (hc : c ≤ n + m)
    (P : SubmersivePresentation (Localization.AtPrime p) D (Fin (n + m)) (Fin c))
    (hmap : P.map = Fin.castLE hc) :
    ∃ (f : Fin c → MvPolynomial (Fin (n + m)) R)
      (s : R) (h : MvPolynomial (Fin (n + m)) R),
      s ∉ p ∧
      (MvPolynomial.C s - h * Matrix.det
        (fun i j : Fin c ↦ pderiv (Fin.castLE hc i) (f j)) ∈
          Ideal.span (Set.range f)) ∧
      (∀ j, aeval P.val (f j) = 0) ∧
      Ideal.map (MvPolynomial.map (algebraMap R (Localization.AtPrime p)))
        (Ideal.span (Set.range f)) = RingHom.ker (aeval P.val) := by
  classical
  let := MvPolynomial.algebraMvPolynomial (σ := Fin (n + m))
    (R := R) (S := Localization.AtPrime p)
  let φ : MvPolynomial (Fin (n + m)) R →+*
      MvPolynomial (Fin (n + m)) (Localization.AtPrime p) :=
    MvPolynomial.map (algebraMap R (Localization.AtPrime p))
  let M := p.primeCompl.map (C (σ := Fin (n + m)))
  have hclear (j : Fin c) : ∃ (f : MvPolynomial (Fin (n + m)) R) (s : p.primeCompl),
      φ f = C (algebraMap R (Localization.AtPrime p) s) * P.relation j := by
    obtain ⟨⟨f, d⟩, hd⟩ := IsLocalization.surj M (P.relation j)
    change P.relation j * φ (d : MvPolynomial (Fin (n + m)) R) = φ f at hd
    obtain ⟨s, hs, hsd⟩ := d.property
    refine ⟨f, ⟨s, hs⟩, ?_⟩
    simpa [φ, ← hsd, MvPolynomial.map_C, mul_comm] using hd.symm
  choose f s hclear using hclear
  have hsunit (j : Fin c) :
      IsUnit (C (algebraMap R (Localization.AtPrime p) (s j)) :
        MvPolynomial (Fin (n + m)) (Localization.AtPrime p)) :=
    (IsLocalization.map_units (Localization.AtPrime p) (s j)).map C
  have hfzero (j : Fin c) : aeval P.val (f j) = 0 := by
    have h := congrArg (aeval P.val) (hclear j)
    simpa [φ, MvPolynomial.algebraMap_def, MvPolynomial.aeval_map_algebraMap] using h
  have hkernel : Ideal.map φ (Ideal.span (Set.range f)) =
      RingHom.ker (aeval P.val) := by
    rw [Ideal.map_span, ← Set.range_comp]
    apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      change aeval P.val (φ (f j)) = 0
      rw [hclear, map_mul, P.aeval_val_relation, mul_zero]
    · rw [← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      apply (Ideal.unit_mul_mem_iff_mem _ (hsunit j)).mp
      rw [← hclear]
      exact Ideal.subset_span ⟨j, rfl⟩
  let Δ : MvPolynomial (Fin (n + m)) R :=
    Matrix.det (fun i j : Fin c ↦ pderiv (Fin.castLE hc i) (f j))
  have hmat : (fun i j : Fin c ↦ φ (pderiv (Fin.castLE hc i) (f j))) =
      (fun i j : Fin c ↦ C (algebraMap R (Localization.AtPrime p) (s j)) *
        P.jacobiMatrix i j) := by
    funext i j
    rw [PreSubmersivePresentation.jacobiMatrix_apply, hmap]
    change MvPolynomial.map _ _ = _
    rw [← pderiv_map]
    change pderiv _ (φ (f j)) = _
    rw [hclear, pderiv_C_mul]
  have hdet : φ Δ = (∏ j, C (algebraMap R (Localization.AtPrime p) (s j))) *
      P.jacobiMatrix.det := by
    change φ (Matrix.det _) = _
    rw [RingHom.map_det]
    change Matrix.det (fun i j : Fin c ↦ φ (pderiv (Fin.castLE hc i) (f j))) = _
    rw [hmat]
    exact Matrix.det_mul_row _ _
  have hΔunit : IsUnit (aeval P.val Δ) := by
    have h := congrArg (aeval P.val) hdet
    have heq : aeval P.val Δ =
        (∏ j, algebraMap (Localization.AtPrime p) D
          (algebraMap R (Localization.AtPrime p) (s j))) * P.jacobian := by
      simpa [φ, MvPolynomial.algebraMap_def, MvPolynomial.aeval_map_algebraMap,
        P.jacobian_eq_jacobiMatrix_det, P.algebraMap_eq] using h
    rw [heq]
    apply IsUnit.mul _ P.jacobian_isUnit
    exact IsUnit.prod_univ_iff.mpr fun j ↦
      (IsLocalization.map_units (Localization.AtPrime p) (s j)).map
        (algebraMap (Localization.AtPrime p) D)
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hΔunit
  obtain ⟨q, hq⟩ := P.aeval_val_surjective v
  obtain ⟨⟨h, d⟩, hd⟩ := IsLocalization.surj M q
  change q * φ (d : MvPolynomial (Fin (n + m)) R) = φ h at hd
  obtain ⟨t, ht, htd⟩ := d.property
  have hmem : φ (C t - h * Δ) ∈ Ideal.map φ (Ideal.span (Set.range f)) := by
    rw [hkernel, RingHom.mem_ker]
    have hqmul : q * C (algebraMap R (Localization.AtPrime p) t) = φ h := by
      simpa [φ, ← htd, MvPolynomial.map_C] using hd
    have heval := congrArg (aeval P.val) hqmul
    simp only [map_mul, aeval_C] at heval
    simp only [map_sub, map_mul]
    change _ - (aeval P.val) (φ h) * (aeval P.val) (φ Δ) = 0
    simp only [φ, MvPolynomial.map_C, MvPolynomial.aeval_C,
      MvPolynomial.aeval_map_algebraMap]
    simp only [φ, MvPolynomial.aeval_map_algebraMap] at heval
    rw [← heval, hq]
    change _ - (v * _) * aeval P.val Δ = 0
    rw [mul_right_comm, mul_comm v, hv, one_mul, sub_self]
  obtain ⟨b, hb, hbmem⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff M
      (MvPolynomial (Fin (n + m)) (Localization.AtPrime p))
      (Ideal.span (Set.range f)) (C t - h * Δ)).mp hmem
  obtain ⟨r, hr, hrb⟩ := hb
  refine ⟨f, r * t, C r * h, p.primeCompl.mul_mem hr ht, ?_, hfzero, ?_⟩
  · change C (r * t) - (C r * h) * Δ ∈ Ideal.span (Set.range f)
    convert hbmem using 1
    rw [← hrb, map_mul]
    ring
  · exact hkernel

end Algebra

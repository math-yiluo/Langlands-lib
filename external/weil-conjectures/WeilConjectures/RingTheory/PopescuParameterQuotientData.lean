/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.EuclideanDomain.Field

@[expose] public section

universe u v w

namespace Algebra

/-- Construct the canonical quotient algebra map and prime, and prove finite presentation.

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FE, first step of the
powered-parameter reduction (blueprint: lem-weil-pbc-popescu-parameter-quotient-data).

Proof: Each variable image belongs to q because its localization belongs to the maximal
ideal. Its positive powers do too, so JΛ is contained in q. The algebra-map compatibility
of γ sends JC into JΛ; the quotient universal property gives γ₀. The image of q in the
quotient is prime and contracts to q. The quotient of C is finite type over R and hence
over R/J by restriction of scalars. R/J is Noetherian, so finite type is finite presentation.
All witnesses are constructed using quotient maps; no arbitrary existence witness is used.
For d=0 the ideals are zero and the same quotient constructions apply. -/
theorem parameter_quotient_data
    {k : Type u} {C : Type v} {Λ : Type w}
    [Field k] [CommRing C] [CommRing Λ] [Algebra k Λ]
    (d c : ℕ) (hc : 1 ≤ c) (φ : MvPolynomial (Fin d) k →ₐ[k] Λ)
    [Algebra (MvPolynomial (Fin d) k) C]
    [FinitePresentation (MvPolynomial (Fin d) k) C]
    (γ : letI := φ.toRingHom.toAlgebra; C →ₐ[MvPolynomial (Fin d) k] Λ)
    (q : PrimeSpectrum Λ)
    (hgen : Ideal.span (Set.range (fun i : Fin d ↦
      algebraMap Λ (Localization.AtPrime q.asIdeal) (φ (MvPolynomial.X i)))) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) :
    letI := φ.toRingHom.toAlgebra
    let J : Ideal (MvPolynomial (Fin d) k) :=
      Ideal.span (Set.range (fun i : Fin d ↦ (MvPolynomial.X i ^ c) ^ 8))
    let J_C := Ideal.map (algebraMap (MvPolynomial (Fin d) k) C) J
    let J_Λ := Ideal.map (algebraMap (MvPolynomial (Fin d) k) Λ) J
    ∃ (_ : FinitePresentation (MvPolynomial (Fin d) k ⧸ J) (C ⧸ J_C))
      (γ₀ : (C ⧸ J_C) →ₐ[MvPolynomial (Fin d) k ⧸ J] (Λ ⧸ J_Λ))
      (q₀ : PrimeSpectrum (Λ ⧸ J_Λ)),
      γ₀.toRingHom.comp (Ideal.Quotient.mk J_C) =
        (Ideal.Quotient.mk J_Λ).comp γ.toRingHom ∧
      PrimeSpectrum.comap (Ideal.Quotient.mk J_Λ) q₀ = q := by
  let := φ.toRingHom.toAlgebra
  dsimp
  let J : Ideal (MvPolynomial (Fin d) k) :=
    Ideal.span (Set.range (fun i : Fin d ↦ (MvPolynomial.X i ^ c) ^ 8))
  let J_C := Ideal.map (algebraMap (MvPolynomial (Fin d) k) C) J
  let J_Λ := Ideal.map (algebraMap (MvPolynomial (Fin d) k) Λ) J
  have hJq : J_Λ ≤ q.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change φ ((MvPolynomial.X i ^ c) ^ 8) ∈ q.asIdeal
    rw [map_pow, map_pow]
    refine q.asIdeal.pow_mem_of_mem ?_ _ (by omega)
    refine q.asIdeal.pow_mem_of_mem ?_ _ (by omega)
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime q.asIdeal) q.asIdeal _).mp
    rw [← hgen]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hmap : J_C ≤ Ideal.comap γ.toRingHom J_Λ := by
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
    have hcomp : γ.toRingHom.comp (algebraMap (MvPolynomial (Fin d) k) C) =
        algebraMap (MvPolynomial (Fin d) k) Λ := γ.comp_algebraMap
    rw [hcomp]
    exact Ideal.le_comap_map
  let f := Ideal.quotientMap J_Λ γ.toRingHom hmap
  let γ₀ : (C ⧸ J_C) →ₐ[MvPolynomial (Fin d) k ⧸ J] (Λ ⧸ J_Λ) :=
    { f with
      commutes' := by
        intro r
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        change f (Ideal.Quotient.mk J_C (algebraMap (MvPolynomial (Fin d) k) C r)) =
          Ideal.Quotient.mk J_Λ (algebraMap (MvPolynomial (Fin d) k) Λ r)
        simp only [f, Ideal.quotientMap_mk]
        exact congrArg (Ideal.Quotient.mk J_Λ) (γ.commutes r) }
  let q₀ : PrimeSpectrum (Λ ⧸ J_Λ) :=
    ⟨Ideal.map (Ideal.Quotient.mk J_Λ) q.asIdeal,
      Ideal.isPrime_map_quotientMk_of_isPrime hJq⟩
  have hft : FiniteType (MvPolynomial (Fin d) k ⧸ J) (C ⧸ J_C) :=
    FiniteType.of_restrictScalars_finiteType (MvPolynomial (Fin d) k)
      (MvPolynomial (Fin d) k ⧸ J) (C ⧸ J_C)
  have hfp : FinitePresentation (MvPolynomial (Fin d) k ⧸ J) (C ⧸ J_C) :=
    FinitePresentation.of_finiteType.mp hft
  refine ⟨hfp, γ₀, q₀, Ideal.quotientMap_comp_mk hmap, ?_⟩
  apply PrimeSpectrum.ext
  exact Ideal.comap_map_mk hJq

end Algebra

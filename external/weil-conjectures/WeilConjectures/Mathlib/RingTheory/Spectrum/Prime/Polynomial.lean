/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.PolynomialAlgebra

/-!
# Primes of a polynomial ring containing a polynomial

Let `g ∈ R[X]` and let `p` be a prime of `R` not containing the leading coefficient of `g`. Then
the fibre of `Spec R[X] ⟶ Spec R` over `p` contains a prime not containing `g`
(`Polynomial.exists_primeSpectrum_notMem_comap_C_eq`), and only finitely many primes containing
`g` (`Polynomial.finite_setOf_mem_comap_C_eq`): these correspond to the primes of `κ(p)[X]`
containing the nonzero image of `g`.

Over a field `K`, a nonzero `g ∈ K[X]` lies in only finitely many primes
(`Polynomial.finite_setOf_mem_asIdeal`), and is coprime to some monic irreducible polynomial
(`Polynomial.exists_monic_irreducible_isCoprime`).
-/

@[expose] public section

open PrimeSpectrum

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- The base change `R[X] ⟶ κ(p) ⊗[R] R[X]` is the composite of `R[X] ⟶ κ(p)[X]` and the
isomorphism `κ(p)[X] ≅ κ(p) ⊗[R] R[X]`. -/
lemma polyEquivTensor'_comp_mapRingHom (p : Ideal R) [p.IsPrime] :
    ((polyEquivTensor' R p.ResidueField : p.ResidueField[X] ≃ₐ[p.ResidueField] _) :
        p.ResidueField[X] →+* p.Fiber R[X]).comp
      (mapRingHom (algebraMap R p.ResidueField)) =
      Algebra.TensorProduct.includeRight.toRingHom := by
  refine ringHom_ext (fun r ↦ ?_) ?_
  · have h := (polyEquivTensor' R p.ResidueField).commutes (algebraMap R p.ResidueField r)
    rw [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h
    change polyEquivTensor' R p.ResidueField (map (algebraMap R p.ResidueField) (C r)) =
      (1 : p.ResidueField) ⊗ₜ[R] C r
    rw [map_C, h, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, Algebra.algebraMap_eq_smul_one r, TensorProduct.smul_tmul,
      ← Algebra.algebraMap_eq_smul_one, algebraMap_eq]
  · simp [polyEquivTensor_apply]

/-- If the prime `p` of `R` does not contain the leading coefficient of `g`, then the prime
`p[X]` of `R[X]` lies over `p` and does not contain `g`. -/
lemma exists_primeSpectrum_notMem_comap_C_eq {g : R[X]} (p : PrimeSpectrum R)
    (hg : g.leadingCoeff ∉ p.asIdeal) :
    ∃ Q : PrimeSpectrum R[X], g ∉ Q.asIdeal ∧ PrimeSpectrum.comap C Q = p := by
  refine ⟨⟨p.asIdeal.map C, Ideal.isPrime_map_C_of_isPrime⟩, fun h ↦ hg ?_, ?_⟩
  · exact Ideal.mem_map_C_iff.1 h _
  · ext x
    simp only [comap_asIdeal, Ideal.mem_comap, Ideal.mem_map_C_iff, coeff_C]
    refine ⟨fun h ↦ by simpa using h 0, fun h n ↦ ?_⟩
    split_ifs
    · exact h
    · exact p.asIdeal.zero_mem

/-- If the prime `p` of `R` does not contain the leading coefficient of `g`, then only finitely
many primes of `R[X]` over `p` contain `g`: they correspond to primes of `κ(p)[X]` containing the
nonzero image of `g`. -/
lemma finite_setOf_mem_comap_C_eq {g : R[X]} (p : PrimeSpectrum R)
    (hg : g.leadingCoeff ∉ p.asIdeal) :
    {Q : PrimeSpectrum R[X] | g ∈ Q.asIdeal ∧ PrimeSpectrum.comap C Q = p}.Finite := by
  set K := p.asIdeal.ResidueField
  set ψ := mapRingHom (algebraMap R K)
  have hg' : ψ g ≠ 0 := by
    intro h
    have := congrArg (fun f ↦ f.coeff g.natDegree) h
    simp only [ψ, coe_mapRingHom, coeff_map, coeff_zero] at this
    exact hg ((Ideal.algebraMap_residueField_eq_zero).1 this)
  -- the primes of `κ(p)[X]` containing `ψ g` are finitely many
  have hfin : (zeroLocus {ψ g}).Finite := by
    have : Module.Finite K (AdjoinRoot (ψ g)) := (AdjoinRoot.powerBasis hg').finite
    have : IsArtinianRing (AdjoinRoot (ψ g)) := IsArtinianRing.of_finite K _
    have : Finite (PrimeSpectrum (AdjoinRoot (ψ g))) := inferInstance
    rw [← zeroLocus_span, ← Ideal.mk_ker (I := Ideal.span {ψ g}),
      ← range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
    exact Set.finite_range (PrimeSpectrum.comap (AdjoinRoot.mk (ψ g)))
  refine (hfin.image (PrimeSpectrum.comap ψ)).subset fun Q ⟨hgQ, hQ⟩ ↦ ?_
  have hQ' : Q ∈ PrimeSpectrum.comap (algebraMap R R[X]) ⁻¹' {p} := by
    simpa [← algebraMap_eq] using hQ
  set P' := preimageEquivFiber R R[X] p ⟨Q, hQ'⟩
  set e := (polyEquivTensor' R K : K[X] ≃ₐ[K] _)
  have hQe : PrimeSpectrum.comap ((e : K[X] →+* p.asIdeal.Fiber R[X]).comp ψ) P' = Q := by
    rw [polyEquivTensor'_comp_mapRingHom]
    exact congrArg Subtype.val ((preimageEquivFiber R R[X] p).symm_apply_apply ⟨Q, hQ'⟩)
  refine ⟨PrimeSpectrum.comap (e : K[X] →+* p.asIdeal.Fiber R[X]) P', ?_, ?_⟩
  · rw [mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe, ← Ideal.mem_comap,
      ← comap_asIdeal, ← comap_comp_apply, hQe]
    exact hgQ
  · rw [← comap_comp_apply, hQe]

/-- Over a field, a nonzero polynomial `g` lies in only finitely many primes of `K[X]`. -/
lemma finite_setOf_mem_asIdeal {K : Type*} [Field K] {g : K[X]} (hg : g ≠ 0) :
    {Q : PrimeSpectrum K[X] | g ∈ Q.asIdeal}.Finite := by
  refine (finite_setOf_mem_comap_C_eq ⟨⊥, Ideal.isPrime_bot⟩ (by simpa using hg)).subset
    fun Q hQ ↦ ⟨hQ, ?_⟩
  ext x
  simp only [comap_asIdeal, Ideal.mem_comap, Submodule.mem_bot]
  refine ⟨fun hx ↦ by_contra fun hx0 ↦ Q.isPrime.ne_top
    (Ideal.eq_top_of_isUnit_mem _ hx (isUnit_C.mpr (Ne.isUnit hx0))), ?_⟩
  rintro rfl
  simp

/-- Over a field, every nonzero polynomial `h` is coprime to some monic irreducible polynomial:
take a monic irreducible factor of `h * X + 1`. -/
lemma exists_monic_irreducible_isCoprime {K : Type*} [Field K] {h : K[X]} (hh : h ≠ 0) :
    ∃ P : K[X], P.Monic ∧ Irreducible P ∧ IsCoprime P h := by
  have hdeg : (h * X + 1).natDegree = h.natDegree + 1 := by
    rw [← C_1, natDegree_add_C, natDegree_mul_X hh]
  have hQ0 : h * X + 1 ≠ 0 := fun h0 ↦ by simp [h0] at hdeg
  have hQ : ¬IsUnit (h * X + 1) := fun hu ↦ by simp [natDegree_eq_zero_of_isUnit hu] at hdeg
  obtain ⟨q, hq, hqd⟩ := WfDvdMonoid.exists_irreducible_factor hQ hQ0
  have hu : IsUnit (C q.leadingCoeff⁻¹) :=
    isUnit_C.mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr hq.ne_zero)).isUnit
  refine ⟨q * C q.leadingCoeff⁻¹, monic_mul_leadingCoeff_inv hq.ne_zero,
    (irreducible_mul_isUnit hu).mpr hq, ?_⟩
  refine (isCoprime_mul_unit_right_left hu _ _).mpr (IsCoprime.of_isCoprime_of_dvd_left ?_ hqd)
  exact ⟨1, -X, by ring⟩

end Polynomial

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.ResidueSubfield
public import WeilConjectures.RingTheory.Valuation.ResidueLinearIndependent
public import Mathlib.RingTheory.Valuation.Integral
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The Gauss valuation on a simple residually transcendental extension

Let `𝒪` be a valuation subring of a field `Ω`, `F ⊆ Ω` a subfield and `x ∈ 𝒪` whose residue `x̄`
is transcendental over a subfield `k` of the residue field containing the residues of `F ∩ 𝒪`.
Then the valuation on `F[x]` is the Gauss valuation: `v (∑ cᵢ xⁱ) = maxᵢ v (cᵢ)`
(`ValuationSubring.valuation_aeval_eq_sup`), and the residues of the integral elements of
`F(x)` lie in `k(x̄)` (`ValuationSubring.residue_mem_adjoin_of_mem_adjoin`).

We also record that the residues of an algebraically closed subfield form an algebraically
closed subfield of the residue field (`ValuationSubring.isAlgClosed_residueSubfield`).
-/

@[expose] public section

open IsLocalRing Polynomial

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] {𝒪 : ValuationSubring Ω}

/-- The residue of an element `x ∈ 𝒪` transcendental over `k` is nonzero, so `x` has value `1`. -/
lemma valuation_eq_one_of_transcendental {k : Subfield (ResidueField 𝒪)} {x : 𝒪}
    (hx : Transcendental k (residue 𝒪 x)) : 𝒪.valuation (x : Ω) = 1 := by
  rw [← valuation_eq_one_iff, ← residue_ne_zero_iff_isUnit]
  rintro h
  exact hx (h ▸ isAlgebraic_zero)

/-- The powers of an element transcendental over a field are linearly independent. -/
lemma linearIndependent_pow_of_transcendental {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    {a : A} (ha : Transcendental K a) : LinearIndependent K fun n : ℕ ↦ a ^ n := by
  have := (Polynomial.basisMonomials K).linearIndependent.map' (aeval a).toLinearMap
    (LinearMap.ker_eq_bot.2 (transcendental_iff_injective.1 ha))
  simpa [Function.comp_def] using this

/-- If the coefficients of `f ∈ F[X]` are integral and the residues of `F ∩ 𝒪` lie in `k`, then
`f(x)` is integral with residue in `k(x̄)`. -/
lemma exists_residue_aeval_mem_adjoin {F : Subfield Ω} {k : Subfield (ResidueField 𝒪)}
    (hFk : 𝒪.residueSubfield F ≤ k) (x : 𝒪) (f : F[X])
    (hf : ∀ i, 𝒪.valuation (f.coeff i : Ω) ≤ 1) :
    ∃ z : 𝒪, (z : Ω) = aeval (x : Ω) f ∧
      residue 𝒪 z ∈ IntermediateField.adjoin k {residue 𝒪 x} := by
  refine ⟨∑ i ∈ f.support, ⟨f.coeff i, (𝒪.valuation_le_one_iff _).1 (hf i)⟩ * x ^ i, ?_, ?_⟩
  · simp [aeval_def, eval₂_eq_sum, Polynomial.sum_def]
    rfl
  · rw [map_sum]
    refine sum_mem fun i _ ↦ ?_
    rw [map_mul, map_pow]
    exact MulMemClass.mul_mem
      (IntermediateField.algebraMap_mem _ (⟨_, hFk ⟨_, (f.coeff i).2, rfl⟩⟩ : k))
      (pow_mem (IntermediateField.mem_adjoin_simple_self k _) i)

/-- **The Gauss valuation.** If the residue of `x ∈ 𝒪` is transcendental over a subfield `k` of
the residue field containing the residues of `F ∩ 𝒪`, then `v (f(x)) = maxᵢ v (cᵢ)` for every
polynomial `f = ∑ cᵢ Xⁱ` over `F`. -/
theorem valuation_aeval_eq_sup {F : Subfield Ω} {k : Subfield (ResidueField 𝒪)}
    (hFk : 𝒪.residueSubfield F ≤ k) {x : 𝒪} (hx : Transcendental k (residue 𝒪 x))
    (f : F[X]) :
    𝒪.valuation (aeval (x : Ω) f) = f.support.sup fun i ↦ 𝒪.valuation (f.coeff i : Ω) := by
  classical
  have hind : 𝒪.valuation.ResiduallyIndependent F fun i : f.support ↦ ((x ^ (i : ℕ) : 𝒪) : Ω) := by
    refine Valuation.ResiduallyIndependent.of_linearIndependent_residue (A := k)
      (fun c hc ↦ ⟨⟨_, hFk ⟨⟨_, hc⟩, c.2, rfl⟩⟩, rfl⟩) _ ?_
    simpa [Function.comp_def] using
      (linearIndependent_pow_of_transcendental hx).comp (fun i : f.support ↦ (i : ℕ))
        Subtype.val_injective
  have h := hind.map_sum_smul (fun i ↦ by simp [valuation_eq_one_of_transcendental hx])
    fun i ↦ f.coeff i
  rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def, ← Finset.sum_coe_sort f.support,
    ← Finset.sup_attach]
  simp only [Algebra.smul_def] at h
  exact h

/-- **Residues of a residually transcendental simple extension.** If the residue of `x ∈ 𝒪` is
transcendental over a subfield `k` of the residue field containing the residues of `F ∩ 𝒪`, then
the residue of every integral element of `F(x)` lies in `k(x̄)`. -/
theorem residue_mem_adjoin_of_mem_adjoin {F : Subfield Ω} {k : Subfield (ResidueField 𝒪)}
    (hFk : 𝒪.residueSubfield F ≤ k) {x : 𝒪} (hx : Transcendental k (residue 𝒪 x)) {y : 𝒪}
    (hy : (y : Ω) ∈ IntermediateField.adjoin F {(x : Ω)}) :
    residue 𝒪 y ∈ IntermediateField.adjoin k {residue 𝒪 x} := by
  classical
  obtain ⟨f, g, hfg⟩ := (IntermediateField.mem_adjoin_simple_iff F _).1 hy
  by_cases hg : aeval (x : Ω) g = 0
  · rw [hg, div_zero] at hfg
    obtain rfl : y = 0 := Subtype.ext hfg
    simp
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp at hg
  obtain ⟨i₀, hi₀, hmax⟩ := g.support.exists_max_image (fun i ↦ 𝒪.valuation (g.coeff i : Ω))
    (support_nonempty.2 hg0)
  have hc : (g.coeff i₀ : Ω) ≠ 0 := by
    simpa using mem_support_iff.1 hi₀
  have hle (i : ℕ) : 𝒪.valuation (g.coeff i : Ω) ≤ 𝒪.valuation (g.coeff i₀ : Ω) := by
    by_cases hi : i ∈ g.support
    · exact hmax i hi
    · simp [notMem_support_iff.1 hi]
  have hsup : (g.support.sup fun i ↦ 𝒪.valuation (g.coeff i : Ω)) =
      𝒪.valuation (g.coeff i₀ : Ω) :=
    le_antisymm (Finset.sup_le fun i _ ↦ hle i)
      (Finset.le_sup (f := fun i ↦ 𝒪.valuation (g.coeff i : Ω)) hi₀)
  have hv0 : 𝒪.valuation (g.coeff i₀ : Ω) ≠ 0 := by simpa using hc
  have hg' : 𝒪.valuation (aeval (x : Ω) (C (g.coeff i₀)⁻¹ * g)) = 1 := by
    rw [map_mul, aeval_C, map_mul, valuation_aeval_eq_sup hFk hx g, hsup]
    simp [Subfield.algebraMap_ofSubfield, hv0]
  have hy' : (y : Ω) * aeval (x : Ω) (C (g.coeff i₀)⁻¹ * g) =
      aeval (x : Ω) (C (g.coeff i₀)⁻¹ * f) := by
    rw [hfg, map_mul, map_mul]
    field_simp
  have hf' (i : ℕ) : 𝒪.valuation ((C (g.coeff i₀)⁻¹ * f).coeff i : Ω) ≤ 1 := by
    by_cases hi : i ∈ (C (g.coeff i₀)⁻¹ * f).support
    · refine (Finset.le_sup (f := fun i ↦ 𝒪.valuation ((C (g.coeff i₀)⁻¹ * f).coeff i : Ω))
        hi).trans ?_
      rw [← valuation_aeval_eq_sup hFk hx, ← hy', map_mul, hg', mul_one]
      exact 𝒪.valuation_le_one y
    · simp [notMem_support_iff.1 hi]
  have hg'' (i : ℕ) : 𝒪.valuation ((C (g.coeff i₀)⁻¹ * g).coeff i : Ω) ≤ 1 := by
    rw [coeff_C_mul]
    simpa [div_le_one₀ (zero_lt_iff.2 hv0), ← div_eq_inv_mul] using hle i
  obtain ⟨zf, hzf, hrf⟩ := exists_residue_aeval_mem_adjoin hFk x _ hf'
  obtain ⟨zg, hzg, hrg⟩ := exists_residue_aeval_mem_adjoin hFk x _ hg''
  have hmul : y * zg = zf := by
    apply Subtype.ext
    push_cast
    rw [hzf, hzg, hy']
  have hne : residue 𝒪 zg ≠ 0 := by
    rw [residue_ne_zero_iff_isUnit, valuation_eq_one_iff, hzg]
    exact hg'
  rw [eq_div_of_mul_eq (a := residue 𝒪 y) hne (by rw [← map_mul, hmul])]
  exact _root_.div_mem hrf hrg

/-- The residues of an algebraically closed subfield form an algebraically closed field. -/
theorem isAlgClosed_residueSubfield (K : Subfield Ω) [IsAlgClosed K] :
    IsAlgClosed (𝒪.residueSubfield K) := by
  refine IsAlgClosed.of_exists_root _ fun P hP hirr ↦ ?_
  choose y hyK hyres using fun i : Fin P.natDegree ↦ mem_residueSubfield.1 (P.coeff i).2
  have hdeg := degree_sum_fin_lt fun i : Fin P.natDegree ↦ (⟨y i, hyK i⟩ : K)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root
    (X ^ P.natDegree + ∑ i : Fin P.natDegree, C (⟨y i, hyK i⟩ : K) * X ^ (i : ℕ))
    (by
      rw [degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
      exact_mod_cast hirr.natDegree_pos.ne')
  have hz' : (z : Ω) ^ P.natDegree + ∑ i : Fin P.natDegree, (y i : Ω) * (z : Ω) ^ (i : ℕ) = 0 := by
    simpa [eval_finsetSum] using congrArg Subtype.val hz.eq_zero
  have hv : 𝒪.valuation.Integers 𝒪 :=
    ⟨Subtype.coe_injective, fun x ↦ 𝒪.valuation_le_one x,
      fun r h ↦ ⟨⟨r, (𝒪.valuation_le_one_iff _).1 h⟩, rfl⟩⟩
  have hint : (z : Ω) ∈ 𝒪 := by
    refine (𝒪.valuation_le_one_iff _).1 (hv.isIntegral_iff_v_le_one.1
      ⟨X ^ P.natDegree + ∑ i : Fin P.natDegree, C (y i) * X ^ (i : ℕ),
        monic_X_pow_add (degree_sum_fin_lt _), ?_⟩)
    simpa [eval₂_finsetSum] using hz'
  have hw : (⟨z, hint⟩ : 𝒪) ^ P.natDegree +
      ∑ i : Fin P.natDegree, y i * (⟨z, hint⟩ : 𝒪) ^ (i : ℕ) = 0 :=
    Subtype.ext (by simpa using hz')
  refine ⟨⟨residue 𝒪 ⟨z, hint⟩, ⟨z, hint⟩, z.2, rfl⟩, Subtype.ext ?_⟩
  have h := congrArg (residue 𝒪) hw
  simp only [map_add, map_sum, map_mul, map_pow, map_zero, hyres] at h
  rw [hP.as_sum, ← Fin.sum_univ_eq_sum_range]
  simpa [eval_finsetSum] using h

end ValuationSubring

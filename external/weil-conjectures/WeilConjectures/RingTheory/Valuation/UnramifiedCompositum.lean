/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.ResiduallyIndependentRadicals

/-!
# Adjoining `p ^ n`-th roots of `p`-independent units

Let `𝒪` be a valuation subring of a field `Ω` whose residue field has exponential
characteristic `p`, and let `F ⊆ Ω` be the fraction field of a local ring `R` with
`𝒪 ∩ F = R` (e.g. `F` discretely valued with valuation ring `R`). If `t i` (`i ∈ ι`, finite)
are units of `R` whose residues are `p`-independent in the residue field of `R`, and
`θ i ^ p ^ n = t i`, then `F(θ)` is unramified over `F`:

* every value of `F(θ)` is a value of `F` (so if `F` has value group `v(ϖ) ^ ℤ`, so has `F(θ)`);
* `[F(θ) : F] = p ^ (n * #ι)`, with basis the monomials `∏ i, θ i ^ E i`, `0 ≤ E i < p ^ n`;
* every `y ∈ F(θ)` is `∑ c E • ∏ i, θ i ^ E i` with `v (c E) ≤ v y`; in particular the residue
  field of `F(θ)` is generated over the residue field of `F` by the residues of the `θ i`.

This applies to the compositum `K_j · F'` of a level field
`K_j = K(θ i n : i ∈ s)` of `IsDiscreteValuationRing.exists_discrete_subfield_full_residue`
with a discretely valued field `F'` (with valuation ring `R'`) in whose residue field the
residues of the `t i` stay `p`-independent: `K_j · F' = F'(θ i n : i ∈ s)`.
-/

@[expose] public section

open IsLocalRing IntermediateField Module

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] (𝒪 : ValuationSubring Ω) {R F : Type*} [CommRing R]
  [IsLocalRing R] [Field F] [Algebra R F] [IsFractionRing R F] [Algebra F Ω] [Algebra R Ω]
  [IsScalarTower R F Ω] {p : ℕ} [ExpChar (ResidueField 𝒪) p] [ExpChar (ResidueField R) p]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ι → R} {θ : ι → Ω} {n : ℕ}

/-- **Adjoining `p ^ n`-th roots of `p`-independent units is unramified.** -/
theorem unramified_adjoin_roots
    (hO : ∀ x : F, algebraMap F Ω x ∈ 𝒪 ↔ x ∈ (algebraMap R F).range)
    (ht1 : ∀ i, IsUnit (t i)) (ht : Field.PowIndependent p fun i => residue R (t i))
    (hθ : ∀ i, θ i ^ p ^ n = algebraMap R Ω (t i)) :
    𝒪.valuation.ResiduallyIndependent F (fun E : ι → Fin (p ^ n) => ∏ i, θ i ^ (E i : ℕ)) ∧
      (∀ y ∈ adjoin F (Set.range θ), ∃ c : F, 𝒪.valuation y = 𝒪.valuation (algebraMap F Ω c)) ∧
      finrank F (adjoin F (Set.range θ)) = p ^ (n * Fintype.card ι) ∧
      ∀ y ∈ adjoin F (Set.range θ), ∃ c : (ι → Fin (p ^ n)) → F,
        y = ∑ E, c E • ∏ i, θ i ^ (E i : ℕ) ∧
          ∀ E, 𝒪.valuation (algebraMap F Ω (c E)) ≤ 𝒪.valuation y := by
  have hθ' (i : ι) : θ i ^ p ^ n = algebraMap F Ω (algebraMap R F (t i)) := by
    rw [hθ, ← IsScalarTower.algebraMap_apply]
  have hu (i : ι) : 𝒪.valuation (algebraMap F Ω (algebraMap R F (t i))) = 1 := by
    rw [← IsScalarTower.algebraMap_apply]
    exact valuation_algebraMap_unit hO (ht1 i).unit
  have h := residuallyPowIndependent_of_powIndependent hO (ht.pow n)
  refine ⟨residuallyIndependent_prod_pow 𝒪 hθ' hu h,
    fun y hy => exists_valuation_eq_of_mem_adjoin 𝒪 hθ' hu h hy, finrank_adjoin_eq 𝒪 hθ' hu h,
    fun y hy => ?_⟩
  obtain ⟨c, hc, hv⟩ := exists_eq_sum_smul_prod_pow 𝒪 hθ' hu h hy
  exact ⟨c, hc, fun E => hv ▸ Finset.le_sup (f := fun E => 𝒪.valuation (algebraMap F Ω (c E)))
    (Finset.mem_univ E)⟩

end ValuationSubring

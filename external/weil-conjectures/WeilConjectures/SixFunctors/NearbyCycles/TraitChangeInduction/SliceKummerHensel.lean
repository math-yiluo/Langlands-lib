/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceGaloisFields
public import WeilConjectures.TraceFormula.Specialization.SliceTraitValuation
public import WeilConjectures.RingTheory.Valuation.GaloisResidueRoot
public import WeilConjectures.RingTheory.Valuation.KummerHensel

/-!

# Hensel's lemma for Kummer equations over the slice compositum

Let `D` be a slice trait with compositum `L = Ω(S(x)) ⊆ Ω'` and valuation subring `𝒪 ⊆ Ω'`,
and let `p` be the residual characteristic.

* `SliceTrait.exists_residual_artinSchreier_root`: every Artin–Schreier equation
  `n ^ p - n = β` with `β ∈ L ∩ 𝒪` has a solution in `L ∩ 𝒪` modulo the maximal ideal of `𝒪`.
  This uses that the residue field of `𝒪` is purely inseparable over the separably closed
  residue field of `R`.
* `SliceTrait.exists_pow_eq_one_add`: in characteristic zero, if `x ∈ L` is negligible, i.e.
  `v(x) ^ (p - 1) ≤ v(p) ^ p`, then `1 + x` is a `p`-th power in `L`.

-/

@[expose] public section

universe u

open IsLocalRing IntermediateField

namespace AlgebraicGeometry.SliceTrait

attribute [local instance] algebraR algebraΩ algebraBaseΩ algebraRΩ

variable {R : Type u} [CommRing R] [IsLocalRing R] {Ω : Type u} [Field Ω] [Algebra R Ω]
  {κ : Type u} [Field κ] {b : R →+* κ} (D : SliceTrait (algebraMap R Ω) b)

/-- **Residual Artin–Schreier roots in the compositum.** If `p` is the residual characteristic,
then for every `β ∈ L ∩ 𝒪` there is `n ∈ L ∩ 𝒪` with `n ^ p - n ≡ β` modulo the maximal ideal
of `𝒪`. -/
theorem exists_residual_artinSchreier_root (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField D.R) p] {β : D.Ω} (hβ : β ∈ D.compositum)
    (hβ1 : D.valuationSubring.valuation β ≤ 1) :
    ∃ n ∈ D.compositum, D.valuationSubring.valuation n ≤ 1 ∧
      D.valuationSubring.valuation (n ^ p - n - β) < 1 := by
  classical
  set 𝒪 := D.valuationSubring with h𝒪
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  -- the residue fields
  have haO : ∀ r : D.R, D.a r ∈ 𝒪 := D.a_mem_valuationSubring
  let ρ : D.R →+* 𝒪 := D.a.codRestrict 𝒪.toSubring haO
  have : IsLocalHom ρ := ⟨fun r hr ↦ by
    by_contra hnu
    have : 𝒪.valuation (D.a r) < 1 := (D.valuation_a_lt_one_iff).2
      ((IsLocalRing.mem_maximalIdeal r).2 hnu)
    exact (IsLocalRing.mem_maximalIdeal _).1
      ((ValuationSubring.valuation_lt_one_iff 𝒪 ⟨_, haO r⟩).2 this) hr⟩
  let _ : Algebra (ResidueField D.R) (ResidueField 𝒪) := (ResidueField.map ρ).toAlgebra
  -- the residue field of `𝒪` is purely inseparable over that of `R'`
  have hint : ∀ y : 𝒪, _root_.IsIntegral (ResidueField D.R) (residue 𝒪 y) := by
    intro y
    obtain ⟨f, hfm, hfy⟩ : _root_.IsIntegral D.R (y : D.Ω) := y.2
    refine ⟨f.map (residue D.R), hfm.map _, ?_⟩
    have h0 : Polynomial.eval₂ ρ y f = 0 := Subtype.ext (by
      simp only [ZeroMemClass.coe_zero]
      rw [← hfy, Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range]
      simp [ρ]
      rfl)
    rw [Polynomial.eval₂_map]
    have : (algebraMap (ResidueField D.R) (ResidueField 𝒪)).comp (residue D.R) =
        (residue 𝒪).comp ρ := ResidueField.map_comp_residue ρ
    rw [this, ← Polynomial.hom_eval₂, h0, map_zero]
  have : CharP (ResidueField 𝒪) p :=
    charP_of_injective_ringHom (ResidueField.map ρ).injective p
  have : Algebra.IsAlgebraic (ResidueField D.R) (ResidueField 𝒪) := ⟨fun z ↦ by
    obtain ⟨y, rfl⟩ := residue_surjective z
    exact (hint y).isAlgebraic⟩
  have := Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed (F := ResidueField D.R)
    (E := ResidueField 𝒪)
  have hβO : β ∈ 𝒪 := (ValuationSubring.valuation_le_one_iff 𝒪 β).1 hβ1
  obtain ⟨k, rr, hrr⟩ := IsPurelyInseparable.pow_mem (ResidueField D.R) p
    (residue 𝒪 ⟨β, hβO⟩)
  obtain ⟨r, rfl⟩ := residue_surjective rr
  have hr : residue 𝒪 (ρ r) = residue 𝒪 ⟨β, hβO⟩ ^ p ^ k := by
    rw [← hrr]
    rfl
  -- an Artin–Schreier root in the separably closed residue field of `R'`
  have hder : ∀ e : ResidueField D.R, Polynomial.derivative
      (Polynomial.X ^ p - Polynomial.X - Polynomial.C e) = -1 := fun e ↦ by
    simp [Polynomial.derivative_X_pow, CharP.cast_eq_zero]
  have hdeg : (Polynomial.X ^ p - Polynomial.X -
      Polynomial.C (residue D.R r)).degree ≠ 0 := by
    have h1 : (Polynomial.X : Polynomial (ResidueField D.R)).degree <
        (Polynomial.X ^ p : Polynomial (ResidueField D.R)).degree := by
      rw [Polynomial.degree_X, Polynomial.degree_X_pow]
      exact_mod_cast (Fact.out : p.Prime).one_lt
    rw [Polynomial.degree_sub_C (by
      rw [Polynomial.degree_sub_eq_left_of_degree_lt h1, Polynomial.degree_X_pow]
      exact_mod_cast Nat.pos_of_ne_zero hp0),
      Polynomial.degree_sub_eq_left_of_degree_lt h1, Polynomial.degree_X_pow]
    exact_mod_cast hp0
  obtain ⟨sr, hsr⟩ := IsSepClosed.exists_root _ hdeg (by
    rw [Polynomial.Separable, hder]
    exact isCoprime_one_right.neg_right)
  obtain ⟨s, rfl⟩ := residue_surjective sr
  have hs : residue 𝒪 (ρ s) ^ p - residue 𝒪 (ρ s) - residue 𝒪 (ρ r) = 0 := by
    have h := congrArg (ResidueField.map ρ) hsr.eq_zero
    simpa [ResidueField.map_residue] using h
  -- the residual root `n` in `L`
  have hmemR : ∀ r : D.R, D.a r ∈ D.compositum := fun r ↦
    IntermediateField.subset_adjoin _ _ ⟨r, rfl⟩
  set m : 𝒪 := ρ s - ∑ j ∈ Finset.range k, (⟨β, hβO⟩ : 𝒪) ^ p ^ j with hm
  refine ⟨m, ?_, (ValuationSubring.valuation_le_one_iff 𝒪 _).2 m.2, ?_⟩
  · rw [hm]
    simp only [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum, SubmonoidClass.coe_pow]
    exact sub_mem (hmemR s) (sum_mem fun j _ ↦ pow_mem hβ _)
  · have hcoe : (m : D.Ω) ^ p - m - β = ((m ^ p - m - ⟨β, hβO⟩ : 𝒪) : D.Ω) := rfl
    rw [hcoe, ← ValuationSubring.valuation_lt_one_iff, ← IsLocalRing.residue_eq_zero_iff, hm]
    simp only [map_sub, map_sum, map_pow]
    rw [sub_pow_char, sum_pow_char]
    have htel := Finset.sum_range_sub (fun j ↦ residue 𝒪 ⟨β, hβO⟩ ^ p ^ j) k
    simp only [pow_succ, pow_mul, pow_zero, pow_one, Finset.sum_sub_distrib] at htel
    linear_combination hs + hr - htel

/-- **Hensel's lemma for Kummer equations over the compositum.** In characteristic zero, with
residual characteristic `p`, if `x ∈ L` is negligible, i.e. `v(x) ^ (p - 1) ≤ v(p) ^ p`, then
`1 + x` is a `p`-th power in `L`. -/
theorem exists_pow_eq_one_add (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField D.R) p]
    [CharZero Ω] [IsAlgClosed Ω] {x : D.Ω} (hx : x ∈ D.compositum)
    (hxn : D.valuationSubring.valuation.IsKummerNegligible p x) :
    ∃ y ∈ D.compositum, y ^ p = 1 + x := by
  set 𝒪 := D.valuationSubring with h𝒪
  set N : Subfield D.Ω := D.compositum.toSubfield with hN
  have hp2 := hp.out.two_le
  have hp0 : (p : D.Ω) ≠ 0 := by
    rw [← map_natCast D.ωS p]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hp.out.ne_zero)
  have hp1 : 𝒪.valuation (p : D.Ω) < 1 := by
    rw [← map_natCast D.a p, D.valuation_a_lt_one_iff, ← IsLocalRing.residue_eq_zero_iff,
      map_natCast, CharP.cast_eq_zero]
  -- a root `ϖ` of `X ^ (p - 1) + p` in `Ω`
  obtain ⟨ϖ₀, hϖ₀⟩ := IsAlgClosed.exists_pow_nat_eq (-(p : Ω)) (by omega : 0 < p - 1)
  have hϖ : D.ωS ϖ₀ ^ (p - 1) = -(p : D.Ω) := by
    rw [← map_pow, hϖ₀, map_neg, map_natCast]
  have hϖL : D.ωS ϖ₀ ∈ D.compositum := IntermediateField.algebraMap_mem _ ϖ₀
  have hϖ0 : D.ωS ϖ₀ ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega), eq_comm, neg_eq_zero] at hϖ
    exact hp0 hϖ
  -- a residual Artin–Schreier root
  obtain ⟨n, hnL, hn1, hn⟩ := D.exists_residual_artinSchreier_root p
    (div_mem hx (pow_mem hϖL p))
    (ValuationSubring.valuation_div_pow_le_one_of_isKummerNegligible 𝒪 p hϖ0 hϖ hxn)
  -- the Galois–residue lemma
  have hmemR : ∀ r : D.R, D.a r ∈ D.compositum := fun r ↦
    IntermediateField.subset_adjoin _ _ ⟨r, rfl⟩
  have : Algebra.IsAlgebraic N D.Ω := by
    refine ⟨fun z ↦ ?_⟩
    have hz := (D.isAlgebraic_a).isAlgebraic z
    let ι' : D.R →+* N := D.a.codRestrict N.toSubring fun r ↦ hmemR r
    let _ : Algebra D.R N := ι'.toAlgebra
    have : IsScalarTower D.R N D.Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    exact hz.extendScalars (S := N) (fun x y h ↦ D.injective_a (congrArg Subtype.val h))
  have h𝒪 : ∀ σ : D.Ω ≃ₐ[N] D.Ω, ∀ y ∈ 𝒪, σ y ∈ 𝒪 := fun σ y hy ↦
    (D.map_mem_valuationSubring_iff σ.toRingEquiv
      (fun r ↦ σ.commutes ⟨D.a r, hmemR r⟩)).2 hy
  exact ValuationSubring.exists_pow_eq_one_add 𝒪 N h𝒪 p hp1 hp0 hϖL hϖ hx hxn hnL
    ((ValuationSubring.valuation_le_one_iff 𝒪 n).1 hn1) hn

end AlgebraicGeometry.SliceTrait

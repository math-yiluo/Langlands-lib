/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.GroupTheory.Sylow
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Covers of degree prime to `ℓ`: the field-theoretic core

Field-theoretic core of blueprint `lemma-covers-degree-prime-to-ell`. Let `L / F` be a finite
Galois extension with group `G` (in the blueprint, `F` is the fraction field of a strictly
henselian discrete valuation ring and `L` trivializes the given finite locally constant sheaves),
`P` an `ℓ`-Sylow subgroup of `G` and `F₁ = L^P`. Then `d₁ = [F₁ : F] = [G : P]` is prime to `ℓ`.
If `F₁` is the fraction field of a discrete valuation ring `R₁` (in the blueprint, the
normalization `S₁`), then for every multiple `d = d₁ e` of `d₁` there is a monic Eisenstein
polynomial `g` over `R₁` of degree `e` (`z ^ e + t z - t` for a uniformizer `t`, or `z - t` if
`e = 1`) which is irreducible and separable over `F₁`; so `F' = F₁[z] / (g)` is a separable
extension of `F` of degree `d`, totally ramified over `F₁`. Finally, any automorphism over `F₁`
(in particular over `F'`) of a field containing `L` acts on `L` through `P`: the monodromy
factors through the `ℓ`-group `P`.

## Main statements

- `IsDiscreteValuationRing.exists_monic_isEisensteinAt_separable`: a monic Eisenstein
  polynomial of any degree `e ≥ 1` which is irreducible and separable over the fraction field.
- `IsGalois.not_dvd_finrank_fixedField_sylow`: `[L^P : F]` is prime to `ℓ`.
- `IsGalois.exists_coversDegreePrimeToEll`: the degree adjustment.
- `IsGalois.mem_sylow_of_algHom_comp_eq`: the monodromy over `F₁` lies in `P`.
-/

@[expose] public section

open Polynomial IsLocalRing IntermediateField Module

namespace IsDiscreteValuationRing

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- **An Eisenstein polynomial of degree `e`** (blueprint `lemma-covers-degree-prime-to-ell`):
over a discrete valuation ring `R` with fraction field `K`, for every `e ≥ 1` there is a monic
polynomial of degree `e`, Eisenstein at the maximal ideal, which is irreducible and separable
over `K` (`z ^ e + t z - t` for a uniformizer `t` if `e ≥ 2`, also when the characteristic
divides `e`, and `z - t` if `e = 1`). -/
theorem exists_monic_isEisensteinAt_separable (e : ℕ) (he : 1 ≤ e) :
    ∃ g : R[X], g.Monic ∧ g.natDegree = e ∧ g.IsEisensteinAt (maximalIdeal R) ∧
      Irreducible (g.map (algebraMap R K)) ∧ (g.map (algebraMap R K)).Separable := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hm : maximalIdeal R = Ideal.span {t} := ht.maximalIdeal_eq
  have htm : t ∈ maximalIdeal R := hm ▸ Ideal.mem_span_singleton_self t
  have ht2 : t ∉ maximalIdeal R ^ 2 := by
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨a, ha⟩
    have h1 : t * (1 - t * a) = 0 := by rw [mul_sub, mul_one, ← mul_assoc, ← sq, ← ha, sub_self]
    rcases mul_eq_zero.1 h1 with h | h
    · exact ht.ne_zero h
    · exact ht.not_isUnit (isUnit_iff_exists_inv.2 ⟨a, (sub_eq_zero.1 h).symm⟩)
  have ht0 : algebraMap R K t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ht.ne_zero
  have hprime : (maximalIdeal R).IsPrime := (maximalIdeal.isMaximal R).isPrime
  have hirrK : ∀ g : R[X], g.Monic → 0 < g.natDegree → g.IsEisensteinAt (maximalIdeal R) →
      Irreducible (g.map (algebraMap R K)) := fun g hg hd hE ↦
    (hg.irreducible_iff_irreducible_map_fraction_map).1 (hE.irreducible hprime hg.isPrimitive hd)
  rcases he.eq_or_lt with rfl | he2
  · refine ⟨X - C t, monic_X_sub_C t, natDegree_X_sub_C t, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [(monic_X_sub_C t).leadingCoeff]
      exact fun h ↦ (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro n hn
      rw [natDegree_X_sub_C, Nat.lt_one_iff] at hn
      subst hn
      simpa using neg_mem htm
    · simpa using fun h ↦ ht2 (by simpa using neg_mem h)
    · rw [Polynomial.map_sub, map_X, map_C]
      exact irreducible_of_degree_eq_one (degree_X_sub_C _)
    · rw [Polynomial.map_sub, map_X, map_C]
      exact separable_X_sub_C
  · set g : R[X] := X ^ e + (C t * X - C t) with hg
    have hdeg : (C t * X - C t).degree < (e : WithBot ℕ) := by
      refine (degree_sub_le _ _).trans_lt (max_lt ?_ ?_)
      · exact (degree_C_mul_X_le t).trans_lt (by exact_mod_cast he2)
      · exact (degree_C_le).trans_lt (by exact_mod_cast he)
    have hmon : g.Monic := monic_X_pow_add hdeg
    have hnat : g.natDegree = e := by
      rw [hg, natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
    have hcoeff : ∀ n, n < e → g.coeff n = (if n = 1 then t else 0) - (if n = 0 then t else 0) :=
      fun n hn ↦ by
        rw [hg, coeff_add, coeff_sub, coeff_X_pow, ite_eq_right hn.ne, coeff_C_mul_X, coeff_C,
          zero_add]
    have hE : g.IsEisensteinAt (maximalIdeal R) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hmon.leadingCoeff]
        exact fun h ↦ (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h)
      · intro n hn
        rw [hnat] at hn
        rw [hcoeff n hn]
        refine sub_mem ?_ ?_ <;> split_ifs <;> simp [htm]
      · rw [hcoeff 0 (by omega)]
        simpa using fun h ↦ ht2 (by simpa using neg_mem h)
    have hirr := hirrK g hmon (by omega) hE
    refine ⟨g, hmon, hnat, hE, hirr, (separable_iff_derivative_ne_zero hirr).2 fun h ↦ ?_⟩
    have h0 := congrArg (fun q ↦ q.coeff 0) h
    simp only [coeff_derivative, coeff_map, coeff_zero] at h0
    rw [hcoeff 1 he2] at h0
    simp only [ite_true, one_ne_zero, ite_false, sub_zero, Nat.cast_zero, zero_add,
      mul_one] at h0
    exact ht0 h0

end IsDiscreteValuationRing

namespace IsGalois

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  {ℓ : ℕ} [Fact ℓ.Prime] (P : Sylow ℓ Gal(L/F))

/-- The fixed field `F₁ = L^P`. -/
local notation "F₁" => fixedField (P : Subgroup Gal(L/F))

omit [Fact ℓ.Prime] in
/-- The degree `[L^P : F]` of the fixed field of a Sylow subgroup is the index of `P`. -/
theorem finrank_fixedField_sylow : finrank F F₁ = (P : Subgroup Gal(L/F)).index := by
  have h₁ := finrank_mul_finrank F F₁ L
  rw [finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank F L,
    ← (P : Subgroup Gal(L/F)).card_mul_index] at h₁
  have hpos : 0 < Nat.card (P : Subgroup Gal(L/F)) := Nat.card_pos
  rw [mul_comm] at h₁
  exact Nat.eq_of_mul_eq_mul_left hpos h₁

/-- Blueprint `lemma-covers-degree-prime-to-ell`: the degree `d₁ = [L^P : F]` of the fixed field
of an `ℓ`-Sylow subgroup `P` of `Gal(L/F)` is prime to `ℓ`. -/
theorem not_dvd_finrank_fixedField_sylow : ¬ ℓ ∣ finrank F F₁ := by
  rw [finrank_fixedField_sylow]
  exact P.not_dvd_index

/-- **Covers of degree prime to `ℓ`, field-theoretic core** (blueprint
`lemma-covers-degree-prime-to-ell`): let `L / F` be finite Galois, `P` an `ℓ`-Sylow subgroup of
`Gal(L/F)` and `F₁ = L^P`, the fraction field of a discrete valuation ring `R₁`. Then
`d₁ = [F₁ : F]` is prime to `ℓ`, and for every multiple `d` of `d₁` prime to `ℓ` there is a monic
Eisenstein polynomial `g` over `R₁`, irreducible over `F₁`, such that `F' = F₁[z]/(g)` is a
separable extension of `F` of degree `d` (totally ramified of degree `d / d₁` over `F₁`). -/
theorem exists_coversDegreePrimeToEll (R₁ : Type*) [CommRing R₁] [IsDomain R₁]
    [IsDiscreteValuationRing R₁] [Algebra R₁ F₁] [IsFractionRing R₁ F₁] :
    ¬ ℓ ∣ finrank F F₁ ∧
      ∀ d, finrank F F₁ ∣ d → ¬ ℓ ∣ d →
        ∃ g : R₁[X], g.Monic ∧ g.IsEisensteinAt (maximalIdeal R₁) ∧
          ∃ _ : Fact (Irreducible (g.map (algebraMap R₁ F₁))),
            finrank F (AdjoinRoot (g.map (algebraMap R₁ F₁))) = d ∧
              Algebra.IsSeparable F (AdjoinRoot (g.map (algebraMap R₁ F₁))) := by
  refine ⟨not_dvd_finrank_fixedField_sylow P, ?_⟩
  rintro d ⟨e, hde⟩ hℓd
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · exact absurd (dvd_zero ℓ) (by rwa [hde, mul_zero] at hℓd)
    · exact h
  obtain ⟨g, hmon, hnat, hE, hirr, hsep⟩ :=
    IsDiscreteValuationRing.exists_monic_isEisensteinAt_separable (R := R₁) (K := F₁) e he
  set f := g.map (algebraMap R₁ F₁)
  have hf : Fact (Irreducible f) := ⟨hirr⟩
  have hf0 : f ≠ 0 := hirr.ne_zero
  refine ⟨g, hmon, hE, hf, ?_, ?_⟩
  · rw [← finrank_mul_finrank F F₁ (AdjoinRoot f), (AdjoinRoot.powerBasis hf0).finrank,
      AdjoinRoot.powerBasis_dim, hmon.natDegree_map, hnat, hde]
  · have h₁ : IsSeparable F₁ (AdjoinRoot.root f) :=
      hsep.of_dvd (minpoly.dvd F₁ _ (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]))
    have h₂ := (isSeparable_adjoin_simple_iff_isSeparable F₁ (AdjoinRoot f)).2 h₁
    rw [adjoin_root_eq_top] at h₂
    have : Algebra.IsSeparable F₁ (AdjoinRoot f) :=
      Algebra.IsSeparable.of_algHom F₁ _ (topEquiv (F := F₁) (E := AdjoinRoot f)).symm.toAlgHom
    have : Algebra.IsSeparable F F₁ := Algebra.isSeparable_tower_bot_of_isSeparable F F₁ L
    exact Algebra.IsSeparable.trans F F₁ (AdjoinRoot f)

omit [IsGalois F L] [Fact ℓ.Prime] in
/-- **The monodromy factors through `P`** (blueprint `lemma-covers-degree-prime-to-ell` (3)):
let `E` be a field over `F₁ = L^P` and `ι : L →ₐ[F₁] E` an embedding. If an automorphism `σ` of
`E` over `F₁` (for instance over an extension `F'` of `F₁`) restricts on `ι(L)` to `g ∈ Gal(L/F)`,
then `g ∈ P`. -/
theorem mem_sylow_of_algHom_comp_eq {E : Type*} [Field E] [Algebra F₁ E] (ι : L →ₐ[F₁] E)
    (σ : E ≃ₐ[F₁] E) (g : Gal(L/F)) (h : ∀ x, ι (g x) = σ (ι x)) : g ∈ P := by
  have hg : g ∈ fixingSubgroup F₁ := by
    rintro ⟨x, hx⟩
    apply ι.toRingHom.injective
    change ι (g x) = ι x
    rw [h, show x = algebraMap F₁ L ⟨x, hx⟩ from rfl, AlgHom.commutes, AlgEquiv.commutes]
  rwa [fixingSubgroup_fixedField] at hg

end IsGalois

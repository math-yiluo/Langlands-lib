/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
public import WeilConjectures.Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Flat.Basic

/-!
# Noether normalization with the number of variables the Krull dimension

Mathlib's `exists_finite_inj_algHom_of_fg` produces a polynomial ring in `s` variables over
which a finitely generated algebra is finite, without identifying `s`. Since an integral
extension preserves the Krull dimension, `s` is the dimension of the algebra.

## Main statements

- `ringKrullDim_eq_of_finite_inj_algHom_mvPolynomial`: the number of variables of a Noether
  normalization is the Krull dimension.
- `exists_finite_inj_algHom_mvPolynomial_of_ringKrullDim_eq`
- `exists_finite_inj_algHom_polynomial_of_ringKrullDim_eq_one`
- `ringKrullDim_quotient_lt_of_finiteType`: the dimension drops along a proper closed subset of an
  irreducible affine variety.
- `Algebra.FiniteType.exists_finite_aeval_away`: Noether normalization spreads out from the generic
  fibre to a principal open of the base.
- `ringKrullDim_tensorProduct_eq_of_finite_inj_algHom_mvPolynomial`: the generic fibre of a
  Noether normalization over a domain has the expected dimension.
- `ringKrullDim_tensorProduct_of_finiteType`: base change of a finitely generated algebra over
  a field to a field extension preserves the Krull dimension.
- `ringKrullDim_tensorProduct_le_of_finiteType`: base change of a finitely generated algebra over
  a field to a field extension does not increase the Krull dimension.
- `Polynomial.exists_finite_aeval_pow_sub`: Nagata's trick in one variable; if `A` is finite
  over `R[x]`, then it is finite over `R[x ^ q - a]` for every `a : A` and all large `q`.
- `ringKrullDim_eq_of_isLocalization_away`: localizing a finitely generated domain over a field
  away from a nonzero element preserves the Krull dimension.

## Blueprint

- `lemma-point-count-bound`: Noether normalization.
- `lemma-point-count-bound`: Mathlib's `exists_finite_inj_algHom_of_fg`.
- `lemma-point-count-bound`: `ringKrullDim_eq_of_finite_inj_algHom_mvPolynomial`.
- `det-i-geometry`: dimension drop.
- `lemma-relative-noether-normalization-over-stratification--1`:
`Algebra.FiniteType.exists_finite_aeval_away`.
- `lem-pc-dim-base-change`: `ringKrullDim_tensorProduct_of_finiteType`.
-/

@[expose] public section

universe u

open MvPolynomial TensorProduct

/-- Blueprint `lemma-point-count-bound`: the number of Noether coordinates is the
Krull dimension.

If `K[T₁, …, T_d] → B` is an injective `K`-algebra map over which `B` is a finite module, then
`dim B = d`: the extension is integral, so `dim B = dim K[T₁, …, T_d] = d`. -/
theorem ringKrullDim_eq_of_finite_inj_algHom_mvPolynomial {K B : Type*} [Field K] [CommRing B]
    [Algebra K B] {d : ℕ} (g : MvPolynomial (Fin d) K →ₐ[K] B) (hg : Function.Injective g)
    (hfin : g.Finite) :
    ringKrullDim B = d := by
  algebraize [g.toRingHom]
  have : Module.Finite (MvPolynomial (Fin d) K) B := hfin
  have : FaithfulSMul (MvPolynomial (Fin d) K) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  rw [ringKrullDim_eq_of_isIntegral (MvPolynomial (Fin d) K) B,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_isField
      (Field.toIsField K)]
  simp

/-- Noether normalization in the sharp form: a finitely generated algebra `B` of Krull
dimension `n` over a field `K` admits an injective `K`-algebra map from the polynomial ring in
`n` variables making `B` a finite module.

The number of variables is forced: a finite injective algebra map is an integral extension,
and an integral extension preserves the Krull dimension, so the polynomial ring produced by
`exists_finite_inj_algHom_of_fg` has `ringKrullDim B` many variables. -/
theorem exists_finite_inj_algHom_mvPolynomial_of_ringKrullDim_eq
    (K B : Type*) [Field K] [CommRing B] [Algebra K B] [Algebra.FiniteType K B] (n : ℕ)
    (hB : ringKrullDim B = (n : ℕ)) :
    ∃ g : MvPolynomial (Fin n) K →ₐ[K] B, Function.Injective g ∧ g.Finite := by
  have : Nontrivial B := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    simp [ringKrullDim_eq_bot_of_subsingleton] at hB
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg K B
  obtain rfl : s = n := by
    exact_mod_cast (ringKrullDim_eq_of_finite_inj_algHom_mvPolynomial g hg hfin).symm.trans hB
  exact ⟨g, hg, hfin⟩

/-- Blueprint `lemma-point-count-bound`: One-dimensional Noether normalization.

A finitely generated algebra `B` of Krull dimension one over a field `K` admits an injective
`K`-algebra map from the polynomial ring `K[T]` making `B` a finite module.

Nontriviality of `B` is automatic: the zero ring has `ringKrullDim = ⊥`. This is the case
`n = 1` of `exists_finite_inj_algHom_mvPolynomial_of_ringKrullDim_eq`, along the isomorphism
`MvPolynomial (Fin 1) K ≃ₐ[K] K[T]`. -/
theorem exists_finite_inj_algHom_polynomial_of_ringKrullDim_eq_one
    (K B : Type*) [Field K] [CommRing B] [Algebra K B] [Algebra.FiniteType K B]
    (hB : ringKrullDim B = 1) :
    ∃ g : Polynomial K →ₐ[K] B, Function.Injective g ∧ g.Finite := by
  obtain ⟨g, hg, hfin⟩ := exists_finite_inj_algHom_mvPolynomial_of_ringKrullDim_eq K B 1 hB
  let e := MvPolynomial.uniqueAlgEquiv K (Fin 1)
  exact ⟨g.comp e.symm.toAlgHom, hg.comp e.symm.injective,
    RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ e.symm.surjective)⟩


/-- A proper closed subset of an irreducible affine variety has strictly smaller dimension: for a
finitely generated domain `A` over a field and a nonzero prime `P` of `A`,
`dim (A ⧸ P) < dim A`. (blueprint: `det-i-geometry`) -/
theorem ringKrullDim_quotient_lt_of_finiteType (k A : Type*) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    ringKrullDim (A ⧸ P) < ringKrullDim A :=
  ringKrullDim_quotient_lt_of_irreducibleSpace k A hP

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- Blueprint `lemma-relative-noether-normalization-over-stratification--1`: spreading Noether
normalization to a principal open.

Let `A` be a domain and `B` a finitely generated `A`-algebra. Then there are `0 ≠ s₀ ∈ A`,
`d ≥ 0` and `t₁, …, t_d ∈ B` such that for the localizations `A_s = A[1/s]` and `B_s = B[1/s]`, the
algebra map `A_s[T₁, …, T_d] → B_s`, `Tᵢ ↦ tᵢ` (the map of blueprint
`lemma-relative-noether-normalization-over-stratification--1` on rings) makes `B_s` a finite module.
If moreover `A → B` is injective, this map is injective as well.

The blueprint statement is the case `s = s₀`; we allow any nonzero multiple `s` of `s₀`, as
localizing further preserves finiteness (this is used in
`lemma-relative-noether-normalization-over-stratification--1`).

Following the blueprint, apply Noether normalization (`exists_finite_inj_algHom_of_fg`) to the
generic fibre `B ⊗_A Frac A`, rescale the coordinates so that they come from `B`, and clear the
finitely many denominators of the integral equations of generators of `B`. -/
theorem Algebra.FiniteType.exists_finite_aeval_away (A B : Type u) [CommRing A] [IsDomain A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B] :
    ∃ s₀ : A, s₀ ≠ 0 ∧ ∃ (d : ℕ) (t : Fin d → B), ∀ s : A, s₀ ∣ s → s ≠ 0 →
      ∀ (Aₛ Bₛ : Type*) [CommRing Aₛ] [CommRing Bₛ] [Algebra A Aₛ] [Algebra B Bₛ]
        [Algebra Aₛ Bₛ] [Algebra A Bₛ] [IsScalarTower A Aₛ Bₛ] [IsScalarTower A B Bₛ]
        [IsLocalization.Away s Aₛ] [IsLocalization.Away (algebraMap A B s) Bₛ],
        (aeval (R := Aₛ) fun i ↦ algebraMap B Bₛ (t i)).Finite ∧
        (Function.Injective (algebraMap A B) →
          Function.Injective (aeval (R := Aₛ) fun i ↦ algebraMap B Bₛ (t i))) := by
  classical
  let M := nonZeroDivisors A
  by_cases hzero : ∃ a ∈ M, algebraMap A B a = 0
  · obtain ⟨a, ha, ha0⟩ := hzero
    refine ⟨a, nonZeroDivisors.ne_zero ha, 0, Fin.elim0,
      fun s ⟨c, hc⟩ _ Aₛ Bₛ _ _ _ _ _ _ _ _ _ _ ↦ ⟨?_, fun hinj ↦ ?_⟩⟩
    · have hu := IsLocalization.Away.algebraMap_isUnit (S := Bₛ) (algebraMap A B s)
      rw [hc, map_mul, ha0, zero_mul, map_zero, isUnit_zero_iff] at hu
      have : Subsingleton Bₛ := subsingleton_of_zero_eq_one hu
      let _ := (aeval (R := Aₛ) fun i : Fin 0 ↦ algebraMap B Bₛ (Fin.elim0 i)).toRingHom.toAlgebra
      exact (inferInstance : Module.Finite (MvPolynomial (Fin 0) Aₛ) Bₛ)
    · exact absurd (hinj (ha0.trans (map_zero _).symm)) (nonZeroDivisors.ne_zero ha)
  push Not at hzero
  let K := FractionRing A
  let BK := Localization (Algebra.algebraMapSubmonoid B M)
  let _ : Algebra K BK := localizationAlgebra M B
  have _ : IsScalarTower A K BK := isScalarTower_localizationAlgebra M B
  have _ : IsLocalization (M.map (algebraMap A B)) BK :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid B M) BK)
  have _ : Algebra.FiniteType K BK :=
    RingHom.finiteType_localizationPreserves (algebraMap A B) M K BK
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  have _ : Nontrivial BK := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    obtain ⟨⟨_, a, ha, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff
      (Algebra.algebraMapSubmonoid B M) BK (1 : B)).mp (Subsingleton.elim _ _)
    exact hzero a ha (by simpa using hm)
  obtain ⟨d, g, hg, hgfin⟩ := exists_finite_inj_algHom_of_fg K BK
  have hsurj : ∀ i, ∃ (b : B) (a : A), a ∈ M ∧
      algebraMap B BK b = algebraMap A BK a * g (X i) := by
    intro i
    obtain ⟨⟨b, ⟨_, a, ha, rfl⟩⟩, hm⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid B M) (g (X i))
    refine ⟨b, a, ha, ?_⟩
    rw [← hm, IsScalarTower.algebraMap_apply A B BK, mul_comm]
  choose t a ha ht using hsurj
  let u : Fin d → Kˣ := fun i ↦ Units.mk0 (algebraMap A K (a i))
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (ha i))
  -- Rescaling the variables by the units `u i` is an automorphism of `K[T]`.
  have hresc (v : Fin d → Kˣ) : (aeval (R := K) fun i ↦ C (v i : K) * X i).comp
      (aeval fun i ↦ C (↑(v i)⁻¹ : K) * X i) = AlgHom.id K _ := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    rw [AlgHom.comp_apply, aeval_X, map_mul, aeval_C, aeval_X, algebraMap_eq, ← mul_assoc,
      ← map_mul, Units.inv_mul, map_one, one_mul, AlgHom.id_apply]
  have hu : Function.Bijective (aeval (R := K) fun i ↦ C (u i : K) * X i) :=
    ⟨Function.LeftInverse.injective (g := aeval fun i ↦ C (↑(u i)⁻¹ : K) * X i)
      fun p ↦ by simpa using congr($(hresc fun i ↦ (u i)⁻¹) p),
    Function.RightInverse.surjective (g := aeval fun i ↦ C (↑(u i)⁻¹ : K) * X i)
      fun p ↦ by simpa using congr($(hresc u) p)⟩
  let g' := g.comp (aeval fun i ↦ C (u i : K) * X i)
  have hg'X (i : Fin d) : g' (X i) = algebraMap B BK (t i) := by
    simp [g', u, ht, IsScalarTower.algebraMap_apply A K BK]
  have hg'inj : Function.Injective g' := hg.comp hu.injective
  have hg'fin : g'.Finite := RingHom.Finite.comp hgfin
    (RingHom.Finite.of_surjective _ hu.surjective)
  have hcomp : g'.toRingHom.comp (MvPolynomial.map (algebraMap A K)) =
      (algebraMap B BK).comp (aeval t).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun x ↦ ?_) (fun i ↦ ?_)
    · simp only [RingHom.comp_apply, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        aeval_C]
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, ← IsScalarTower.algebraMap_apply A K BK,
        ← IsScalarTower.algebraMap_apply A B BK]
    · simpa using hg'X i
  -- Every element of `B` has a multiple by a nonzero scalar which is integral over `A[T]`.
  let _ : Algebra (MvPolynomial (Fin d) A) B := (aeval t).toRingHom.toAlgebra
  have key (b : B) : ∃ c ∈ M, IsIntegral (MvPolynomial (Fin d) A) (algebraMap A B c * b) := by
    let _ : Algebra (MvPolynomial (Fin d) K) BK := g'.toRingHom.toAlgebra
    have _ : IsScalarTower (MvPolynomial (Fin d) A) (MvPolynomial (Fin d) K) BK :=
      .of_algebraMap_eq fun p ↦ by
        rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) A) B BK]
        exact (congr($hcomp p)).symm
    have hfin : Module.Finite (MvPolynomial (Fin d) K) BK := hg'fin
    obtain ⟨⟨_, c₁, hc₁, rfl⟩, h₁⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (Rₘ := MvPolynomial (Fin d) K) (M.map (C : A →+* MvPolynomial (Fin d) A))
      (algebraMap B BK b)
      (Algebra.IsIntegral.isIntegral _)
    have hsub : Algebra.algebraMapSubmonoid B (M.map (C : A →+* MvPolynomial (Fin d) A)) =
        Algebra.algebraMapSubmonoid B M := by
      ext x
      simp [Algebra.algebraMapSubmonoid, RingHom.algebraMap_toAlgebra]
    have _ : IsLocalization (Algebra.algebraMapSubmonoid B
        (M.map (C : A →+* MvPolynomial (Fin d) A))) BK := by
      rw [hsub]; infer_instance
    have hsmul (c : A) (x : B) : (C c : MvPolynomial (Fin d) A) • x = algebraMap A B c * x := by
      simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    rw [Submonoid.smul_def, Algebra.smul_def,
      IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) A) B BK, ← map_mul, ← Algebra.smul_def,
      hsmul] at h₁
    obtain ⟨_, ⟨c₂, hc₂, rfl⟩, h₂⟩ :=
      IsLocalization.exists_isIntegral_smul_of_isIntegral_map (M.map C) (Sₘ := BK) h₁
    refine ⟨c₂ * c₁, mul_mem hc₂ hc₁, ?_⟩
    rwa [hsmul, ← mul_assoc, ← map_mul] at h₂
  choose c hc hcint using key
  obtain ⟨S, hS⟩ := Algebra.FiniteType.out (R := A) (A := B)
  refine ⟨∏ b ∈ S, c b, nonZeroDivisors.ne_zero (prod_mem fun b _ ↦ hc b), d, t,
    fun s hs hs0 Aₛ Bₛ _ _ _ _ _ _ _ _ _ _ ↦ ?_⟩
  let φ : MvPolynomial (Fin d) Aₛ →ₐ[Aₛ] Bₛ := aeval fun i ↦ algebraMap B Bₛ (t i)
  have hφ : φ.toRingHom.comp (MvPolynomial.map (algebraMap A Aₛ)) =
      (algebraMap B Bₛ).comp (aeval t).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun x ↦ ?_) (fun i ↦ ?_)
    · simp only [RingHom.comp_apply, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
    · simp [φ]
  -- `B_s` is generated over `A_s` by the image of the generators of `B`.
  have hadj : Algebra.adjoin Aₛ (algebraMap B Bₛ '' S) = ⊤ := by
    refine Algebra.eq_top_iff.mpr fun y ↦ ?_
    obtain ⟨⟨b, _, n, rfl⟩, hy⟩ := IsLocalization.surj (Submonoid.powers (algebraMap A B s)) y
    have hb : algebraMap B Bₛ b ∈ Algebra.adjoin Aₛ (algebraMap B Bₛ '' S) := by
      have hbA : algebraMap B Bₛ b ∈ Algebra.adjoin A (algebraMap B Bₛ '' S) := by
        rw [← IsScalarTower.coe_toAlgHom' A B Bₛ, Algebra.adjoin_image, hS]
        exact ⟨b, trivial, rfl⟩
      exact (Algebra.adjoin_le (Algebra.subset_adjoin (R := Aₛ)) :
        Algebra.adjoin A _ ≤ (Algebra.adjoin Aₛ _).restrictScalars A) hbA
    obtain ⟨v, hv⟩ := IsLocalization.Away.algebraMap_isUnit (S := Aₛ) s
    have : y = algebraMap B Bₛ b * algebraMap Aₛ Bₛ (↑v⁻¹ ^ n) := by
      rw [← hy, map_pow, ← IsScalarTower.algebraMap_apply A B Bₛ,
        IsScalarTower.algebraMap_apply A Aₛ Bₛ, ← hv, mul_assoc, ← map_pow, ← map_mul, ← mul_pow,
        Units.mul_inv, one_pow, map_one, mul_one]
    rw [this]
    exact mul_mem hb (Subalgebra.algebraMap_mem _ _)
  let _ : Algebra (MvPolynomial (Fin d) Aₛ) Bₛ := φ.toRingHom.toAlgebra
  have _ : IsScalarTower Aₛ (MvPolynomial (Fin d) Aₛ) Bₛ :=
    .of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  -- The images of the generators of `B` are integral over `A_s[T]`.
  have hint (b : B) (hb : b ∈ S) : IsIntegral (MvPolynomial (Fin d) Aₛ) (algebraMap B Bₛ b) := by
    obtain ⟨v, hv⟩ := isUnit_of_dvd_unit
      (map_dvd (algebraMap A Aₛ) ((Finset.dvd_prod_of_mem c hb).trans hs))
      (IsLocalization.Away.algebraMap_isUnit (S := Aₛ) s)
    have h₁ : IsIntegral (MvPolynomial (Fin d) Aₛ)
        (algebraMap B Bₛ (algebraMap A B (c b) * b)) :=
      IsIntegral.map_of_comp_eq (MvPolynomial.map (algebraMap A Aₛ)) (algebraMap B Bₛ) hφ
        (hcint b)
    have h₂ : algebraMap B Bₛ b =
        algebraMap Aₛ Bₛ ↑v⁻¹ * algebraMap B Bₛ (algebraMap A B (c b) * b) := by
      rw [map_mul, ← mul_assoc, ← IsScalarTower.algebraMap_apply A B Bₛ,
        IsScalarTower.algebraMap_apply A Aₛ Bₛ, ← hv, ← map_mul, Units.inv_mul, map_one, one_mul]
    rw [h₂]
    exact (isIntegral_algebraMap.tower_top (A := MvPolynomial (Fin d) Aₛ)).mul h₁
  have _ : Algebra.FiniteType Aₛ Bₛ :=
    ⟨⟨S.image (algebraMap B Bₛ), by rw [Finset.coe_image, hadj]⟩⟩
  have _ : Algebra.FiniteType (MvPolynomial (Fin d) Aₛ) Bₛ :=
    Algebra.FiniteType.of_restrictScalars_finiteType Aₛ _ Bₛ
  have _ : Algebra.IsIntegral (MvPolynomial (Fin d) Aₛ) Bₛ := by
    refine ⟨fun y ↦ ?_⟩
    have hy : y ∈ Algebra.adjoin Aₛ (algebraMap B Bₛ '' S) := hadj ▸ trivial
    have hle : Algebra.adjoin Aₛ (algebraMap B Bₛ '' S) ≤
        (integralClosure (MvPolynomial (Fin d) Aₛ) Bₛ).restrictScalars Aₛ :=
      Algebra.adjoin_le (by rintro _ ⟨b, hb, rfl⟩; exact hint b hb)
    exact hle hy
  refine ⟨Algebra.IsIntegral.finite, fun _ ↦ ?_⟩
  -- Injectivity: clear the denominators of a polynomial in the kernel and pass to `K`.
  refine (injective_iff_map_eq_zero φ).mpr fun p hp ↦ ?_
  obtain ⟨⟨q, _, _, ⟨n, rfl⟩, rfl⟩, hq⟩ :=
    IsLocalization.surj ((Submonoid.powers s).map (C : A →+* MvPolynomial (Fin d) A)) p
  have h₁ : algebraMap B Bₛ (aeval t q) = 0 := by
    have := congr(φ $hq)
    rw [map_mul, hp, zero_mul] at this
    exact (congr($hφ q)).symm.trans this.symm
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap A B s)) Bₛ _).mp h₁
  have h₂ : g' (MvPolynomial.map (algebraMap A K) (C (s ^ k) * q)) = 0 := by
    have := congr($hcomp (C (s ^ k) * q))
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [this, map_mul, aeval_C, map_pow, hk, map_zero]
  have h₃ : C (s ^ k) * q = 0 := MvPolynomial.map_injective _ (IsFractionRing.injective A K)
    ((hg'inj (h₂.trans (map_zero g').symm)).trans (map_zero _).symm)
  have hq0 : q = 0 := (mul_eq_zero.mp h₃).resolve_left
    (by rw [C_eq_zero]; exact pow_ne_zero _ hs0)
  rw [hq0, map_zero] at hq
  exact (IsLocalization.map_units (M := (Submonoid.powers s).map C) (MvPolynomial (Fin d) Aₛ)
    ⟨_, _, ⟨n, rfl⟩, rfl⟩).mul_left_eq_zero.mp hq

attribute [local instance] MvPolynomial.algebraMvPolynomial Algebra.TensorProduct.rightAlgebra in
/-- The dimension of the generic fibre of a Noether normalization over a domain.

Let `R` be a domain with fraction field `K` and `φ : R[T₁, …, T_d] → S` an injective finite
`R`-algebra map. Then the generic fibre `K ⊗_R S` has Krull dimension `d`: it is finite and
injective over `K ⊗_R R[T₁, …, T_d] = K[T₁, …, T_d]`, being the localization of `φ` at the
nonzero elements of `R`. -/
theorem ringKrullDim_tensorProduct_eq_of_finite_inj_algHom_mvPolynomial {R S : Type u} (K : Type u)
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Field K] [Algebra R K]
    [IsFractionRing R K] {d : ℕ} (φ : MvPolynomial (Fin d) R →ₐ[R] S)
    (hinj : Function.Injective φ) (hfin : φ.Finite) :
    ringKrullDim (K ⊗[R] S) = d := by
  let M := nonZeroDivisors R
  let N := M.map (C : R →+* MvPolynomial (Fin d) R)
  have : IsLocalization (N.map φ.toRingHom) (K ⊗[R] S) := by
    have : N.map φ.toRingHom = Algebra.algebraMapSubmonoid S M := by
      ext; simp [N, Algebra.algebraMapSubmonoid]
    rw [this]; infer_instance
  let ψ : MvPolynomial (Fin d) K →+* K ⊗[R] S :=
    IsLocalization.map (K ⊗[R] S) φ.toRingHom (Submonoid.le_comap_map N)
  have hψfin : ψ.Finite := RingHom.finite_localizationPreserves φ.toRingHom N _ _ hfin
  have hψinj : Function.Injective ψ := IsLocalization.map_injective_of_injective N _ _ hinj
  have hψC : ψ.comp C = algebraMap K (K ⊗[R] S) := by
    refine IsLocalization.ringHom_ext M (RingHom.ext fun r ↦ ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, ← map_C, ← MvPolynomial.algebraMap_def,
      IsLocalization.map_eq]
    change (1 : K) ⊗ₜ[R] φ (C r) = _
    rw [← MvPolynomial.algebraMap_eq, φ.commutes, Algebra.algebraMap_eq_smul_one,
      ← TensorProduct.smul_tmul, RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self_apply, Algebra.algebraMap_eq_smul_one]
  let ψ' : MvPolynomial (Fin d) K →ₐ[K] K ⊗[R] S :=
    { ψ with commutes' := fun k ↦ congr($hψC k) }
  exact ringKrullDim_eq_of_finite_inj_algHom_mvPolynomial ψ' hψinj hψfin

/-- The transcendence degree of a finitely generated domain `B` over a field `K` is its Krull
dimension: for a Noether normalization `K[T₁, …, Tₙ] → B` both are `n`. -/
theorem Algebra.trdeg_eq_of_ringKrullDim_eq (K B : Type*) [Field K] [CommRing B] [IsDomain B]
    [Algebra K B] [Algebra.FiniteType K B] {n : ℕ} (hB : ringKrullDim B = n) :
    Algebra.trdeg K B = n := by
  obtain ⟨g, hinj, hfin⟩ := exists_finite_inj_algHom_mvPolynomial_of_ringKrullDim_eq K B n hB
  algebraize [g.toRingHom]
  have : IsScalarTower K (MvPolynomial (Fin n) K) B :=
    .of_algebraMap_eq fun r ↦ (g.commutes r).symm
  have : FaithfulSMul (MvPolynomial (Fin n) K) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Algebra.IsIntegral (MvPolynomial (Fin n) K) B := ⟨hfin.to_isIntegral⟩
  have h := lift_trdeg_add_eq K (MvPolynomial (Fin n) K) B
  rw [trdeg_eq_zero (R := MvPolynomial (Fin n) K), MvPolynomial.trdeg_of_isDomain] at h
  simpa using h.symm

/-- Localizing a finitely generated domain over a field `K` away from a nonzero element does
not change its Krull dimension: both dimensions are the transcendence degree over `K` of the
common fraction field. -/
theorem ringKrullDim_eq_of_isLocalization_away {K : Type*} {A B : Type u} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [CommRing B] [Algebra A B] {a : A}
    (ha : a ≠ 0) [IsLocalization.Away a B] : ringKrullDim B = ringKrullDim A := by
  have hM : Submonoid.powers a ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors ha
  have : IsDomain B :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers a) (S := B) hM
  let : Algebra K B := ((algebraMap A B).comp (algebraMap K A)).toAlgebra
  have : IsScalarTower K A B := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.FiniteType A B :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers a) B
  have : Algebra.FiniteType K B := .trans (S := A) inferInstance inferInstance
  have : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).2 (IsLocalization.injective B hM)
  have : Algebra.IsAlgebraic A B := IsLocalization.isAlgebraic B (Submonoid.powers a)
  have key (R : Type u) [CommRing R] [Nontrivial R] [Algebra K R] [Algebra.FiniteType K R] :
      ∃ n : ℕ, ringKrullDim R = n := by
    have h1 := ringKrullDim_ne_top_of_finiteType K R
    have h2 : ringKrullDim R ≠ ⊥ :=
      ne_bot_of_le_ne_bot WithBot.coe_ne_bot ringKrullDim_nonneg_of_nontrivial
    induction h : ringKrullDim R using WithBot.recBotCoe with
    | bot => exact absurd h h2
    | coe m =>
      induction m using ENat.recTopCoe with
      | top => exact absurd h h1
      | coe m => exact ⟨m, rfl⟩
  obtain ⟨n, hn⟩ := key A
  obtain ⟨m, hm⟩ := key B
  have hA := Algebra.trdeg_eq_of_ringKrullDim_eq K A hn
  have hB := Algebra.trdeg_eq_of_ringKrullDim_eq K B hm
  have h := trdeg_add_eq (R := K) (S := A) (A := B)
  rw [trdeg_eq_zero (R := A) (A := B), add_zero, hA, hB] at h
  rw [hn, hm, Nat.cast_inj.1 h.symm]

/-- **Base change along a field extension preserves dimension.** For a finitely generated
algebra `A` over a field `k` and a field `K` over `k`, `dim (A ⊗[k] K) = dim A`: a Noether
normalization `k[T₁, …, Tₙ] → A` base changes to an injective (as `K` is flat over `k`) integral
map `K[T₁, …, Tₙ] → A ⊗[k] K`, so both rings have dimension `n`.

(blueprint: `lem-pc-dim-base-change`) -/
theorem ringKrullDim_tensorProduct_of_finiteType (k A K : Type*) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] [Field K] [Algebra k K] :
    ringKrullDim (A ⊗[k] K) = ringKrullDim A := by
  cases subsingleton_or_nontrivial A with
  | inl hA =>
    have : Subsingleton (A ⊗[k] K) := by
      refine subsingleton_of_zero_eq_one ?_
      rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : A) 0, zero_tmul]
    simp [ringKrullDim_eq_bot_of_subsingleton]
  | inr hA =>
    obtain ⟨n, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k A
    rw [ringKrullDim_eq_of_finite_inj_algHom_mvPolynomial g hg hfin]
    let φ := Algebra.TensorProduct.map g (AlgHom.id k K)
    have hφ : Function.Injective φ :=
      Module.Flat.rTensor_preserves_injective_linearMap (M := K) g.toLinearMap hg
    algebraize [g.toRingHom, φ.toRingHom]
    have : Module.Finite (MvPolynomial (Fin n) k) A := hfin
    have : FaithfulSMul (MvPolynomial (Fin n) k ⊗[k] K) (A ⊗[k] K) :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr hφ
    have : Algebra.IsIntegral (MvPolynomial (Fin n) k ⊗[k] K) (A ⊗[k] K) := by
      refine ⟨fun z ↦ z.inductionOn (fun a x ↦ ?_) fun _ _ ↦ .add⟩
      have ha : IsIntegral (MvPolynomial (Fin n) k ⊗[k] K) (a ⊗ₜ[k] (1 : K)) :=
        (Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin n) k) a).map_of_comp_eq
          Algebra.TensorProduct.includeLeftRingHom Algebra.TensorProduct.includeLeftRingHom
          (RingHom.ext fun p ↦ by simp [φ, RingHom.algebraMap_toAlgebra])
      have hx : a ⊗ₜ[k] x = a ⊗ₜ[k] 1 * algebraMap _ (A ⊗[k] K)
          (1 ⊗ₜ[k] x : MvPolynomial (Fin n) k ⊗[k] K) := by
        simp [φ, RingHom.algebraMap_toAlgebra]
      rw [hx]
      exact ha.mul isIntegral_algebraMap
    rw [ringKrullDim_eq_of_isIntegral (MvPolynomial (Fin n) k ⊗[k] K) (A ⊗[k] K),
      ringKrullDim_eq_of_ringEquiv ((Algebra.TensorProduct.comm k _ K).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv k K).toRingEquiv),
      MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_isField (Field.toIsField K)]
    simp

/-- Base change of a finitely generated algebra `A` over a field `k` to a field `K` over `k`
does not increase the Krull dimension (see `ringKrullDim_tensorProduct_of_finiteType` for the
equality). -/
theorem ringKrullDim_tensorProduct_le_of_finiteType (k A K : Type*) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] [Field K] [Algebra k K] :
    ringKrullDim (A ⊗[k] K) ≤ ringKrullDim A :=
  (ringKrullDim_tensorProduct_of_finiteType k A K).le

/-! ### Nagata's trick in one variable -/

namespace Polynomial

open Polynomial

/-- Nagata's substitution: if `P(X, Y)` is monic in `Y` and all its coefficients (in `R[X]`)
have degree `< q`, then `P(Y, Y ^ q - S)`, viewed as a polynomial in `Y` over `R[S]`, is monic. -/
theorem Monic.eval₂_mapRingHom_C_X_pow_sub_C_X {R : Type*} [CommRing R] {P : R[X][X]}
    (hP : P.Monic) {q : ℕ} (hq : ∀ i, (P.coeff i).natDegree < q) :
    (P.eval₂ (mapRingHom C) (X ^ q - C X)).Monic := by
  nontriviality R
  have hm : (X ^ q - C X : R[X][X]).Monic :=
    monic_X_pow_sub_C _ ((hq 0).trans_le' (Nat.zero_le _)).ne'
  have hd : (X ^ q - C X : R[X][X]).natDegree = q := natDegree_X_pow_sub_C
  rw [eval₂_eq_sum_range, Finset.sum_range_succ, hP.coeff_natDegree, map_one, one_mul]
  refine Monic.add_of_right (hm.pow _) ?_
  rw [degree_eq_natDegree (hm.pow _).ne_zero, hm.natDegree_pow, hd]
  refine (degree_sum_le _ _).trans_lt
    ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun i hi ↦ ?_)
  refine degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.2 ?_)
  have hi : (i + 1) * q ≤ P.natDegree * q := Nat.mul_le_mul_right _ (Finset.mem_range.1 hi)
  calc _ ≤ _ := natDegree_mul_le
    _ ≤ (P.coeff i).natDegree + i * q := by
      refine add_le_add natDegree_map_le (natDegree_pow_le.trans ?_)
      rw [hd]
    _ < P.natDegree * q := by
      have := hq i
      rw [Nat.succ_mul] at hi
      omega

/-- Evaluating Nagata's substitution `P(Y, Y ^ q - S)` at `S = s`, `Y = x` gives
`P(x, x ^ q - s)`. -/
theorem eval₂_eval₂_mapRingHom_C_X_pow_sub_C_X {R A : Type*} [CommRing R] [CommRing A]
    (f : R →+* A) (x s : A) (P : R[X][X]) (q : ℕ) :
    (P.eval₂ (mapRingHom C) (X ^ q - C X)).eval₂ (eval₂RingHom f s) x =
      P.eval₂ (eval₂RingHom f x) (x ^ q - s) := by
  rw [← coe_eval₂RingHom (eval₂RingHom f s) x, hom_eval₂]
  congr 1
  · ext <;> simp
  · simp

/-- **Nagata's trick in one variable.** If `A` is finite over `R[x]`, then for every `a : A`
and every large enough `q`, `A` is finite over `R[x ^ q - a]`: substituting `a = x ^ q - s` into
an integral equation of `a` over `R[x]` gives a monic equation for `x` over `R[s]`. -/
theorem exists_finite_aeval_pow_sub {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {x : A} (hx : (aeval (R := R) x).Finite) (a : A) :
    ∃ m : ℕ, ∀ q, m < q → (aeval (R := R) (x ^ q - a)).Finite := by
  obtain ⟨P, hPm, hP⟩ := RingHom.Finite.to_isIntegral hx a
  refine ⟨(Finset.range (P.natDegree + 1)).sup fun i ↦ (P.coeff i).natDegree, fun q hq ↦ ?_⟩
  have hPq (i : ℕ) : (P.coeff i).natDegree < q := by
    refine lt_of_le_of_lt ?_ hq
    rcases le_or_gt i P.natDegree with h | h
    · exact Finset.le_sup (f := fun i ↦ (P.coeff i).natDegree) (Finset.mem_range_succ_iff.2 h)
    · simp [coeff_eq_zero_of_natDegree_lt h]
  have he (y : A) : (aeval (R := R) y).toRingHom = eval₂RingHom (algebraMap R A) y :=
    RingHom.ext fun _ ↦ aeval_def _ _
  set Q := P.eval₂ (mapRingHom C) (X ^ q - C X)
  have hQm : Q.Monic := hPm.eval₂_mapRingHom_C_X_pow_sub_C_X hPq
  have hQ : Q.eval₂ (aeval (R := R) (x ^ q - a)).toRingHom x = 0 := by
    rw [he, eval₂_eval₂_mapRingHom_C_X_pow_sub_C_X, sub_sub_cancel, ← he]
    exact hP
  have hψ : (aeval (R := R) (x ^ q - a)).toRingHom =
      (AdjoinRoot.lift _ x hQ).comp (AdjoinRoot.of Q) := (AdjoinRoot.lift_comp_of hQ).symm
  rw [AlgHom.Finite, hψ]
  let j : R[X] →+* AdjoinRoot Q :=
    eval₂RingHom ((AdjoinRoot.of Q).comp (C : R →+* R[X])) (AdjoinRoot.root Q)
  have hj : (AdjoinRoot.lift _ x hQ).comp j = (aeval (R := R) x).toRingHom :=
    Polynomial.ringHom_ext (fun r ↦ by simp [j]) (by simp [j])
  refine RingHom.Finite.comp (RingHom.Finite.of_comp_finite (f := j) (hj ▸ hx)) ?_
  rw [← AdjoinRoot.algebraMap_eq, RingHom.finite_algebraMap]
  exact hQm.finite_adjoinRoot

end Polynomial

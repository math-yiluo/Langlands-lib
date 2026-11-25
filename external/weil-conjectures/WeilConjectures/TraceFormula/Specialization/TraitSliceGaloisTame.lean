/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisCompositum

/-!

# `Gal(F_K^sep / F_K·F^sep)` is a pro-`p` group, modulo tame ramification

Let `F = k'((t))`, `F_K = K((t))`, `Ω_K = F_K^alg` and `L' = F_K·F^sep ⊆ Ω_K`
(`AlgebraicGeometry.traitGenericSepCompositum`). The core of SGA 4½, [Th. finitude], Lemme 3.3,
is that `Gal(F_K^sep / L')` is a pro-`p` group (`p` the characteristic). This file reduces this
statement to the classical description of tame extensions of complete discretely valued fields
with algebraically closed residue field.

* **The Kummer extensions `F_K(t^{1/n})` lie in `L'`**
  (`AlgebraicGeometry.mem_traitGenericSepCompositum_of_pow_eq`): for `n` prime to `p`, every
  `n`-th root of `t` in `Ω_K` is the image of a root of the separable polynomial `Xⁿ - t` over `F`.
* **Units of `K⟦t⟧` are `n`-th powers** for `p ∤ n` (`PowerSeries.exists_pow_eq_of_isUnit`),
  the Hensel input of the Kummer description of tame extensions of `K((t))`.
* **A Cauchy argument** (`IsGalois.exists_finrank_eq_prime_pow`): a finite Galois extension
  `M / L` in which every element of prime-to-`p` degree over an intermediate field `E` lies in
  `E` has `p`-power degree.
* **Descent to finite subextensions**
  (`IntermediateField.exists_finiteDimensional_natDegree_minpoly_eq`): the degree of a separable
  element `α` over a field `E ⊆ Ω` is its degree over the subfield `F(coefficients) ⊆ E`, which is
  finite over `F` when `Ω / F` is algebraic.
* **The reduction** (`IntermediateField.exists_finrank_eq_prime_pow_of_forall_mem_sup` and
  `AlgebraicGeometry.exists_finrank_traitGenericSepCompositum_eq_pow`): if for every finite
  extension `E₀` of `F_K` in `Ω_K`, every separable element of prime-to-`p` degree over `E₀` lies in
  some `E₀(t^{1/n})` with `p ∤ n` (the tame closure of `E₀` is `E₀·F_K^tame`), then every finite
  Galois extension of `L'` has `p`-power degree, i.e. its Galois group is a `p`-group
  (`AlgebraicGeometry.isPGroup_traitGenericSepCompositum`).

-/

@[expose] public section

open Polynomial IntermediateField Module

/-- **Galois extensions all of whose prime-to-`p` subextensions are trivial have `p`-power
degree**: let `M / L` be finite Galois and `p` a prime. If for every intermediate field `E` every
element of `M` of degree prime to `p` over `E` lies in `E`, then `[M : L]` is a power of `p`. By
Cauchy's theorem, a prime `q ≠ p` dividing `[M : L]` would give a subgroup of order `q`, whose
fixed field `E` has `[M : E] = q`. -/
theorem IsGalois.exists_finrank_eq_prime_pow {L M : Type*} [Field L] [Field M] [Algebra L M]
    [FiniteDimensional L M] [IsGalois L M] {p : ℕ} (hp : p.Prime)
    (h : ∀ (E : IntermediateField L M) (β : M), ¬ p ∣ (minpoly E β).natDegree → β ∈ E) :
    ∃ k, finrank L M = p ^ k := by
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd finrank_pos.ne' fun {q} hq hdvd ↦ ?_⟩
  by_contra hqp
  have := Fintype.ofFinite Gal(M/L)
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card] at hdvd
  have := Fact.mk hq
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card q hdvd
  let E := fixedField (Subgroup.zpowers g)
  have hE : finrank E M = q := by
    rw [finrank_fixedField_eq_card, Nat.card_zpowers, hg]
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element E M
  have hdeg : (minpoly E β).natDegree = q := by
    rw [← adjoin.finrank (.of_finite E β), hβ, finrank_top', hE]
  have hβE := h E β (by
    rw [hdeg]
    exact fun hpq ↦ hqp ((Nat.prime_dvd_prime_iff_eq hp hq).1 hpq).symm)
  have h1 : (minpoly E β).natDegree = 1 :=
    minpoly.natDegree_eq_one_iff.2 ⟨⟨β, hβE⟩, rfl⟩
  exact hq.ne_one (hdeg.symm.trans h1)

/-- **Descent of minimal polynomials to a finitely generated subfield**: let `Ω / F` be
algebraic, `E` a field with `F ⟶ Ω` factoring through `E ⟶ Ω`, and `α ∈ Ω` separable over `E`.
Then some intermediate field `E₀` of `Ω / F` finite over `F` and contained in the image of `E`
(namely `F` adjoined the coefficients of the minimal polynomial of `α` over `E`) has `α`
separable over `E₀` of the same degree as over `E`. -/
theorem IntermediateField.exists_finiteDimensional_natDegree_minpoly_eq {F Ω E : Type*} [Field F]
    [Field Ω] [Field E] [Algebra F Ω] [Algebra E Ω] [Algebra.IsAlgebraic F Ω]
    (hF : ∀ x : F, algebraMap F Ω x ∈ (algebraMap E Ω).fieldRange) {α : Ω}
    (hα : IsSeparable E α) :
    ∃ E₀ : IntermediateField F Ω, FiniteDimensional F E₀ ∧
      (E₀ : Set Ω) ⊆ (algebraMap E Ω).fieldRange ∧ IsSeparable E₀ α ∧
        (minpoly E₀ α).natDegree = (minpoly E α).natDegree := by
  set P := (minpoly E α).map (algebraMap E Ω)
  let E₀ := adjoin F (P.coeffs : Set Ω)
  let T : IntermediateField F Ω := (algebraMap E Ω).fieldRange.toIntermediateField hF
  have hle : E₀ ≤ T := by
    refine adjoin_le_iff.2 fun c hc ↦ ?_
    obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.1 hc
    rw [coeff_map]
    exact RingHom.mem_fieldRange_self _ _
  have hfin : FiniteDimensional F E₀ :=
    finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
  let ι : E₀ →+* E := (algebraMap E Ω).rangeRestrictFieldEquiv.symm.toRingHom.comp
    (inclusion hle).toRingHom
  have hι : ∀ x, algebraMap E Ω (ι x) = algebraMap E₀ Ω x := fun x ↦
    RingHom.rangeRestrictFieldEquiv_apply_symm_apply _ _
  have hιcomp : (algebraMap E Ω).comp ι = algebraMap E₀ Ω := RingHom.ext hι
  have hlift : minpoly E α ∈ lifts ι := by
    refine (lifts_iff_coeff_lifts _).2 fun n ↦ ?_
    by_cases hn : (minpoly E α).coeff n = 0
    · exact ⟨0, by rw [hn, map_zero]⟩
    have hmem : algebraMap E Ω ((minpoly E α).coeff n) ∈ E₀ := by
      refine subset_adjoin _ _ ?_
      rw [Finset.mem_coe, ← coeff_map]
      exact coeff_mem_coeffs (by
        rw [coeff_map]
        exact (_root_.map_ne_zero _).2 hn)
    refine ⟨⟨_, hmem⟩, (algebraMap E Ω).injective ?_⟩
    rw [hι]
    rfl
  obtain ⟨q, hq⟩ := (mem_lifts _).1 hlift
  have hmon : (minpoly E α) ≠ 0 := fun h0 ↦
    not_separable_zero (by rw [← h0]; exact hα)
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hmon (by rw [← hq, Polynomial.map_zero])
  have hqα : aeval α q = 0 := by
    rw [aeval_def, ← hιcomp, ← eval₂_map, hq, ← aeval_def, minpoly.aeval]
  have hqdeg : q.natDegree = (minpoly E α).natDegree := by
    rw [← hq, natDegree_map_eq_of_injective ι.injective]
  have hqsep : q.Separable := (separable_map ι).1 (hq ▸ hα)
  have hdvd : minpoly E₀ α ∣ q := minpoly.dvd _ _ hqα
  have hint : IsIntegral E₀ α := (Algebra.IsIntegral.isIntegral (R := F) α).tower_top
  refine ⟨E₀, hfin, fun x hx ↦ hle hx, hqsep.of_dvd hdvd, le_antisymm ?_ ?_⟩
  · exact hqdeg ▸ natDegree_le_of_dvd hdvd hq0
  · have hdvd' : minpoly E α ∣ (minpoly E₀ α).map ι := by
      refine minpoly.dvd _ _ ?_
      rw [aeval_def, eval₂_map, hιcomp, ← aeval_def, minpoly.aeval]
    have h0 : (minpoly E₀ α).map ι ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hint)
    have := natDegree_le_of_dvd hdvd' h0
    rwa [natDegree_map_eq_of_injective ι.injective] at this

/-- **Reduction of the pro-`p` property to finite subextensions**: let `Ω / F` be algebraic,
`L` an intermediate field and `p` a prime. Suppose that for every intermediate field `E₀` finite
over `F`, every element of `Ω` separable of degree prime to `p` over `E₀` lies in `E₀ ⊔ L`. Then
every finite Galois extension `M` of `L` in `Ω` has `p`-power degree. -/
theorem IntermediateField.exists_finrank_eq_prime_pow_of_forall_mem_sup {F Ω : Type*} [Field F]
    [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω] (L : IntermediateField F Ω) {p : ℕ}
    (hp : p.Prime)
    (H : ∀ E₀ : IntermediateField F Ω, FiniteDimensional F E₀ → ∀ α : Ω, IsSeparable E₀ α →
      ¬ p ∣ (minpoly E₀ α).natDegree → α ∈ E₀ ⊔ L)
    (M : IntermediateField L Ω) [FiniteDimensional L M] [IsGalois L M] :
    ∃ k, finrank L M = p ^ k := by
  refine IsGalois.exists_finrank_eq_prime_pow hp fun E β hβ ↦ ?_
  let : Algebra E Ω := ((algebraMap M Ω).comp (algebraMap E M)).toAlgebra
  have : IsScalarTower E M Ω := IsScalarTower.of_algebraMap_eq' rfl
  have hmin : minpoly E (algebraMap M Ω β) = minpoly E β :=
    minpoly.algebraMap_eq (algebraMap M Ω).injective β
  have hsep : IsSeparable E (algebraMap M Ω β) := by
    unfold IsSeparable
    rw [hmin]
    exact Algebra.IsSeparable.isSeparable E β
  have hL : ∀ y : L, algebraMap E Ω (algebraMap L E y) = algebraMap L Ω y := fun _ ↦ rfl
  have hF : ∀ x : F, algebraMap F Ω x ∈ (algebraMap E Ω).fieldRange := fun x ↦
    ⟨algebraMap L E (algebraMap F L x), by rw [hL]; rfl⟩
  obtain ⟨E₀, hfin, hE₀, hsep₀, hdeg₀⟩ :=
    exists_finiteDimensional_natDegree_minpoly_eq hF hsep
  have hmem := H E₀ hfin _ hsep₀ (by rwa [hdeg₀, hmin])
  let T : IntermediateField F Ω := (algebraMap E Ω).fieldRange.toIntermediateField hF
  have hT : E₀ ⊔ L ≤ T :=
    sup_le (fun x hx ↦ hE₀ hx) fun x hx ↦ ⟨algebraMap L E ⟨x, hx⟩, hL _⟩
  obtain ⟨e, he⟩ := hT hmem
  have : (e : M) = β := (algebraMap M Ω).injective he
  exact this ▸ e.2

/-- **Units of `K⟦t⟧` are `n`-th powers for `n` prime to the characteristic** (Hensel), provided
`n`-th roots exist in `K` (e.g. `K` algebraically closed). This is the input of Kummer theory in
the description of tame extensions of `K((t))`. -/
theorem PowerSeries.exists_pow_eq_of_isUnit {K : Type*} [Field K] {n : ℕ} (hn : (n : K) ≠ 0)
    (hK : ∀ a : K, ∃ b, b ^ n = a) {u : PowerSeries K} (hu : IsUnit u) :
    ∃ v : PowerSeries K, v ^ n = u := by
  have hc : PowerSeries.constantCoeff u ≠ 0 := by
    rw [PowerSeries.isUnit_iff_constantCoeff] at hu
    exact hu.ne_zero
  obtain ⟨b, hb⟩ := hK (PowerSeries.constantCoeff u)
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hb0 : b ≠ 0 := by rintro rfl; exact hc (by rw [← hb, zero_pow hn0])
  obtain ⟨v, hv, -⟩ := IsAdicComplete.exists_isRoot_sub_mem (Ideal.span {PowerSeries.X})
    (Polynomial.X ^ n - Polynomial.C u) (PowerSeries.C b) (by
      rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, eval_sub, eval_pow, eval_X, eval_C,
        map_sub, map_pow, PowerSeries.constantCoeff_C, hb, sub_self])
    (by
      refine IsUnit.map _ (PowerSeries.isUnit_iff_constantCoeff.2 ?_)
      simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow,
        Polynomial.derivative_C, sub_zero, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, map_mul, map_pow, PowerSeries.constantCoeff_C,
        map_natCast, Polynomial.eval_natCast]
      exact (IsUnit.mk0 _ hn).mul ((IsUnit.mk0 _ hb0).pow _))
  refine ⟨v, ?_⟩
  have := hv.eq_zero
  rwa [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at this

universe u

namespace AlgebraicGeometry

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

/-- **The Kummer extensions `F_K(t^{1/n})`, `p ∤ n`, lie in `F_K·F^sep`**: every `n`-th root of
`t` in `Ω_K` is the image of a root in `Ω` of the separable polynomial `Xⁿ - t` over
`F = k'((t))`, hence lies in the image of `F^sep`. -/
theorem mem_traitGenericSepCompositum_of_pow_eq {n : ℕ} (hn : (n : k') ≠ 0)
    {ρ : traitGenericField K}
    (hρ : ρ ^ n = algebraMap (PowerSeries K) (traitGenericField K) PowerSeries.X) :
    ρ ∈ traitGenericSepCompositum k' K := by
  set F := FractionRing (PowerSeries k')
  set Ω := traitGenericField k'
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  set tF : F := algebraMap (PowerSeries k') F PowerSeries.X
  have htF : tF ≠ 0 := fun h ↦ PowerSeries.X_ne_zero (R := k')
    (IsFractionRing.injective (PowerSeries k') F (by rw [map_zero]; exact h))
  let g : k' →+* F := (algebraMap (PowerSeries k') F).comp PowerSeries.C
  have hnF : (n : F) ≠ 0 := by
    rw [← map_natCast g n]
    exact (_root_.map_ne_zero g).2 hn
  have : NeZero (n : Ω) := ⟨by
    rw [← map_natCast (algebraMap F Ω)]
    exact (_root_.map_ne_zero _).2 hnF⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω n
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F Ω tF) hn0
  set φ := traitGenericFieldMap k' K
  have hφt : φ (algebraMap F Ω tF) =
      algebraMap (PowerSeries K) (traitGenericField K) PowerSeries.X := by
    rw [← IsScalarTower.algebraMap_apply]
    have := RingHom.congr_fun (traitGenericFieldMap_comp_algebraMap k' K) PowerSeries.X
    rwa [RingHom.comp_apply, RingHom.comp_apply, PowerSeries.map_X] at this
  have hφω : φ ω ^ n = algebraMap (PowerSeries K) (traitGenericField K) PowerSeries.X := by
    rw [← map_pow, hω, hφt]
  have hρmem : ρ ∈ nthRoots n (algebraMap (PowerSeries K) (traitGenericField K)
      PowerSeries.X) := (mem_nthRoots hn0).2 hρ
  rw [(hζ.map_of_injective φ.injective).nthRoots_eq hφω, Multiset.mem_map] at hρmem
  obtain ⟨i, -, rfl⟩ := hρmem
  refine subset_adjoin _ _ ⟨ζ ^ i * ω, ?_, by rw [map_mul, map_pow]⟩
  rw [SetLike.mem_coe, mem_separableClosure_iff]
  have hroot : aeval (ζ ^ i * ω) (X ^ n - C tF) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, mul_pow, ← pow_mul, mul_comm i n, pow_mul,
      hζ.pow_eq_one, one_pow, one_mul, hω, sub_self]
  exact (separable_X_pow_sub_C tF hnF htF).of_dvd (minpoly.dvd F _ hroot)

/-- **`Gal(F_K^sep / F_K·F^sep)` is pro-`p`, given the tame closures of finite extensions of
`F_K`**: let `p` be a prime. Suppose that for every finite extension `E₀` of `F_K = K((t))` in
`Ω_K`, every element separable of degree prime to `p` over `E₀` lies in `E₀(ρ)` for some `n`-th
root `ρ` of `t` with `p ∤ n` (that is, the tame closure of `E₀` is `E₀·F_K^tame`). Then every
finite Galois extension `M` of `L' = F_K·F^sep` in `Ω_K` has `p`-power degree. -/
theorem exists_finrank_traitGenericSepCompositum_eq_pow {p : ℕ} (hp : p.Prime)
    (htame : ∀ E₀ : IntermediateField (FractionRing (PowerSeries K)) (traitGenericField K),
      FiniteDimensional (FractionRing (PowerSeries K)) E₀ → ∀ α : traitGenericField K,
        IsSeparable E₀ α → ¬ p ∣ (minpoly E₀ α).natDegree →
          ∃ (n : ℕ) (ρ : traitGenericField K), (n : k') ≠ 0 ∧
            ρ ^ n = algebraMap (PowerSeries K) (traitGenericField K) PowerSeries.X ∧
              α ∈ E₀ ⊔ (FractionRing (PowerSeries K))⟮ρ⟯)
    (M : IntermediateField (traitGenericSepCompositum k' K) (traitGenericField K))
    [FiniteDimensional (traitGenericSepCompositum k' K) M]
    [IsGalois (traitGenericSepCompositum k' K) M] :
    ∃ k, finrank (traitGenericSepCompositum k' K) M = p ^ k := by
  refine exists_finrank_eq_prime_pow_of_forall_mem_sup _ hp (fun E₀ hE₀ α hα hdeg ↦ ?_) M
  obtain ⟨n, ρ, hn, hρ, hmem⟩ := htame E₀ hE₀ α hα hdeg
  exact sup_le_sup_left
    (adjoin_simple_le_iff.2 (mem_traitGenericSepCompositum_of_pow_eq hn hρ)) _ hmem

/-- The Galois group form of `AlgebraicGeometry.exists_finrank_traitGenericSepCompositum_eq_pow`:
under the same tameness hypothesis, `Gal(M / F_K·F^sep)` is a `p`-group for every finite Galois
`M / F_K·F^sep` in `Ω_K`, i.e. `Gal(F_K^sep / F_K·F^sep)` is a pro-`p` group. -/
theorem isPGroup_traitGenericSepCompositum {p : ℕ} (hp : p.Prime)
    (htame : ∀ E₀ : IntermediateField (FractionRing (PowerSeries K)) (traitGenericField K),
      FiniteDimensional (FractionRing (PowerSeries K)) E₀ → ∀ α : traitGenericField K,
        IsSeparable E₀ α → ¬ p ∣ (minpoly E₀ α).natDegree →
          ∃ (n : ℕ) (ρ : traitGenericField K), (n : k') ≠ 0 ∧
            ρ ^ n = algebraMap (PowerSeries K) (traitGenericField K) PowerSeries.X ∧
              α ∈ E₀ ⊔ (FractionRing (PowerSeries K))⟮ρ⟯)
    (M : IntermediateField (traitGenericSepCompositum k' K) (traitGenericField K))
    [FiniteDimensional (traitGenericSepCompositum k' K) M]
    [IsGalois (traitGenericSepCompositum k' K) M] :
    IsPGroup p Gal(M/traitGenericSepCompositum k' K) := by
  obtain ⟨k, hk⟩ := exists_finrank_traitGenericSepCompositum_eq_pow hp htame M
  exact IsPGroup.of_card (n := k) (by rw [IsGalois.card_aut_eq_finrank, hk])

end AlgebraicGeometry

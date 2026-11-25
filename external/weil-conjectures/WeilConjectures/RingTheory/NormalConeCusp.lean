/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.QuasiRegularRees
public import WeilConjectures.RingTheory.ExtendedReesAlgebraGraded
public import WeilConjectures.RingTheory.SmoothPurity.ReesAssociatedGradedChart
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The normal cone of the cusp

The singular case of blueprint `example-normal-cone-point`: for the cusp
`X = V(y² - x³) ⊂ 𝔸²` over a commutative ring `k`, with coordinate ring
`A = k[x, y] / (y² - x³)`, and `Z` the origin with ideal `I = (x, y)`, the graded algebra
`⨁_r I^r / I^{r+1}` is `k[ξ, η] / (η²)`, where `ξ, η` are the classes of `x, y` in `I / I²`.
So the normal cone `N_Z X` is a double line.

The graded algebra is realised as the special fibre `A[t, I t⁻¹] / (t)` of the deformation to the
normal cone, with `ξ, η` the classes of `x t⁻¹, y t⁻¹`. The relation `η² = 0` holds because
`y² t⁻² = x³ t⁻² = t · x³ t⁻³`. Conversely, a polynomial `P(ξ, η)` mapping to zero has, in each
degree `d`, its value at `(x, y)` in `I^{d+1}`; along the parametrisation `x ↦ s², y ↦ s³` the
ideal `I^{d+1}` goes to `(s^{2d+2})`, while `ξ^d` and `ξ^{d-1} η` go to `s^{2d}` and `s^{2d+1}`,
so the coefficients of `P` not divisible by `η²` vanish.

## Main results

- `MvPolynomial.ker_cuspToReesQuot`: the kernel of `k[ξ, η] ⟶ A[t, I t⁻¹] / (t)` is `(η²)`.
- `MvPolynomial.cuspReesQuotEquiv`: `k[ξ, η] / (η²) ≅ A[t, I t⁻¹] / (t)`.
- `MvPolynomial.nonempty_cusp_ringEquiv_associatedGraded`: `k[ξ, η] / (η²) ≅ gr_I A`.
-/

@[expose] public section

open LaurentPolynomial

namespace MvPolynomial

variable (k : Type*) [CommRing k]

/-- The coordinate ring `k[x, y] / (y² - x³)` of the cusp. -/
local notation "𝒪" =>
  MvPolynomial (Fin 2) k ⧸ Ideal.span {(X 1 : MvPolynomial (Fin 2) k) ^ 2 - X 0 ^ 3}

/-- The coordinates `x = cuspCoord k 0` and `y = cuspCoord k 1` on the cusp
`k[x, y] / (y² - x³)`. -/
noncomputable def cuspCoord (i : Fin 2) : 𝒪 :=
  Ideal.Quotient.mk _ (X i)

/-- The ideal `I = (x, y)` of the origin of the cusp. -/
local notation "𝔪" => Ideal.span (Set.range (cuspCoord k))

lemma cuspCoord_one_sq : cuspCoord k 1 ^ 2 = cuspCoord k 0 ^ 3 := by
  simp only [cuspCoord, ← map_pow]
  exact Ideal.Quotient.eq.2 (Ideal.subset_span rfl)

lemma mk_sub_algebraMap_constantCoeff_mem_cusp (p : MvPolynomial (Fin 2) k) :
    Ideal.Quotient.mk _ p - algebraMap k 𝒪 (constantCoeff p) ∈ 𝔪 := by
  classical
  have hp : p - C (constantCoeff p) ∈
      Ideal.span (Set.range (X : Fin 2 → MvPolynomial (Fin 2) k)) := by
    rw [← Set.image_univ, mem_ideal_span_X_image]
    intro m hm
    by_contra! h
    have hm0 : m = 0 := Finsupp.ext fun i ↦ h i (Set.mem_univ i)
    subst hm0
    rw [mem_support_iff, coeff_sub, coeff_C, ite_eq_left rfl, ← constantCoeff_eq, sub_self] at hm
    exact hm rfl
  have := Ideal.mem_map_of_mem (Ideal.Quotient.mk
    (Ideal.span {(X 1 : MvPolynomial (Fin 2) k) ^ 2 - X 0 ^ 3})) hp
  rw [Ideal.map_span, ← Set.range_comp, map_sub] at this
  rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap] at this
  exact this

lemma algebraMap_quotient_cusp_surjective : Function.Surjective (algebraMap k (𝒪 ⧸ 𝔪)) := by
  intro z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨constantCoeff p, ?_⟩
  rw [IsScalarTower.algebraMap_apply k 𝒪 (𝒪 ⧸ 𝔪), Ideal.Quotient.algebraMap_eq]
  exact (Ideal.Quotient.eq.2 (mk_sub_algebraMap_constantCoeff_mem_cusp k p)).symm

/-- The map `k[ξ, η] ⟶ A[t, I t⁻¹] / (t)`, `ξ ↦ x t⁻¹`, `η ↦ y t⁻¹`, to the special fibre of the
deformation to the normal cone of the origin of the cusp `A = k[x, y] / (y² - x³)`. -/
noncomputable def cuspToReesQuot :
    MvPolynomial (Fin 2) k →+* (𝔪).extendedReesAlgebra ⧸ Ideal.span {(𝔪).extendedReesAlgebraT} :=
  (Ideal.mvPolynomialToReesQuot (cuspCoord k)).comp (map (algebraMap k (𝒪 ⧸ 𝔪)))

lemma cuspToReesQuot_X (i : Fin 2) :
    cuspToReesQuot k (X i) = Ideal.Quotient.mk _ (Ideal.reesGen (cuspCoord k) i) := by
  simp [cuspToReesQuot, Ideal.mvPolynomialToReesQuot]

lemma cuspToReesQuot_surjective : Function.Surjective (cuspToReesQuot k) :=
  (Ideal.surjective_mvPolynomialToReesQuot _).comp
    (map_surjective _ (algebraMap_quotient_cusp_surjective k))

lemma cuspToReesQuot_apply (P : MvPolynomial (Fin 2) k) :
    cuspToReesQuot k P = Ideal.Quotient.mk _
      (Ideal.mvPolynomialToRees (cuspCoord k) (map (algebraMap k 𝒪) P)) := by
  rw [cuspToReesQuot, RingHom.comp_apply, ← Ideal.mvPolynomialToReesQuot_map, map_map]
  congr 2

lemma X_one_sq_mem_ker_cuspToReesQuot : X 1 ^ 2 ∈ RingHom.ker (cuspToReesQuot k) := by
  rw [RingHom.mem_ker, map_pow, cuspToReesQuot_X, ← map_pow, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton']
  refine ⟨⟨LaurentPolynomial.C (cuspCoord k 0 ^ 3) * T (-3),
    Ideal.C_mul_T_mem_extendedReesAlgebra ?_⟩,
    Subtype.ext ?_⟩
  · simpa using Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self 0)) 3
  · simp only [Ideal.reesGen, MulMemClass.coe_mul, SubmonoidClass.coe_pow,
      Ideal.coe_extendedReesAlgebraT, mul_pow, ← map_pow, cuspCoord_one_sq, mul_assoc, ← T_add]
    rw [T_pow]
    norm_num

/-- The point `(s², s³)` of the cusp over `k[s]`. -/
noncomputable def cuspParamPt : Fin 2 → Polynomial k :=
  ![Polynomial.X ^ 2, Polynomial.X ^ 3]

@[simp] lemma cuspParamPt_zero : cuspParamPt k 0 = Polynomial.X ^ 2 := rfl

@[simp] lemma cuspParamPt_one : cuspParamPt k 1 = Polynomial.X ^ 3 := rfl

/-- The parametrisation `x ↦ s², y ↦ s³` of the cusp, `k[x, y] / (y² - x³) ⟶ k[s]`. -/
noncomputable def cuspParam : 𝒪 →+* Polynomial k :=
  Ideal.Quotient.lift _ (aeval (cuspParamPt k)).toRingHom fun p hp ↦ by
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hp
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_sub, map_pow, aeval_X]
    simp only [cuspParamPt, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    ring

lemma cuspParam_comp :
    ((cuspParam k).comp (eval (cuspCoord k))).comp (map (algebraMap k 𝒪)) =
      (aeval (cuspParamPt k)).toRingHom := by
  refine ringHom_ext (fun c ↦ ?_) fun i ↦ ?_
  · simp only [RingHom.coe_comp, Function.comp_apply, map_C, eval_C, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, algHom_C, Polynomial.algebraMap_eq, cuspParam]
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.lift_mk]
    simp
  · fin_cases i <;> simp [cuspParam, cuspCoord]

lemma X_pow_dvd_cuspParam {d : ℕ} {z : 𝒪} (hz : z ∈ 𝔪 ^ d) :
    Polynomial.X ^ (2 * d) ∣ cuspParam k z := by
  have h : (𝔪).map (cuspParam k) ≤ Ideal.span {Polynomial.X ^ 2} := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    fin_cases i
    · simp [cuspParam, cuspCoord]
    · exact (pow_dvd_pow Polynomial.X (by norm_num : 2 ≤ 3)).trans (by simp [cuspParam, cuspCoord])
  have := Ideal.pow_right_mono h d (Ideal.map_pow (cuspParam k) 𝔪 d ▸ Ideal.mem_map_of_mem _ hz)
  rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← pow_mul] at this

private lemma degree_fin_two (m : Fin 2 →₀ ℕ) : m.degree = m 0 + m 1 := by
  rw [Finsupp.degree_apply, Finset.sum_subset (Finset.subset_univ _) fun i _ hi ↦ by simpa using hi,
    Fin.sum_univ_two]

/-- For `H` homogeneous of degree `d` and `m = (d - j, j)`, the coefficient of `s^{2d + j}` in
`H(s², s³)` is the coefficient of `ξ^{d-j} η^j` in `H`. -/
lemma coeff_aeval_cusp {H : MvPolynomial (Fin 2) k} {d : ℕ} (hH : H.IsHomogeneous d)
    (m : Fin 2 →₀ ℕ) (hm : m.degree = d) :
    (aeval (cuspParamPt k) H).coeff (2 * d + m 1) = H.coeff m := by
  classical
  have hmon (n : Fin 2 →₀ ℕ) (c : k) :
      aeval (cuspParamPt k) (monomial n c) =
        Polynomial.C c * Polynomial.X ^ (2 * n 0 + 3 * n 1) := by
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
    simp [pow_add, ← pow_mul]
  conv_lhs => rw [H.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff]
  simp_rw [hmon, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single m]
  · rw [degree_fin_two] at hm
    rw [ite_eq_left (by omega)]
  · intro b hb hbm
    rw [ite_eq_right]
    intro h
    apply hbm
    have hb' : b.degree = d := by
      rw [Finsupp.degree_eq_weight_one]
      exact hH (mem_support_iff.1 hb)
    rw [degree_fin_two] at hb' hm
    ext i
    fin_cases i <;> simp <;> omega
  · intro hm'
    simp [notMem_support_iff.1 hm']

lemma homogeneousComponent_map {σ R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (d : ℕ) (P : MvPolynomial σ R) :
    homogeneousComponent d (map f P) = map f (homogeneousComponent d P) := by
  ext m
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

/-- (blueprint `example-normal-cone-point`) For the cusp `A = k[x, y] / (y² - x³)` and
`I = (x, y)`, the kernel of `k[ξ, η] ⟶ A[t, I t⁻¹] / (t) = ⨁_r I^r / I^{r+1}`,
`ξ ↦ x t⁻¹`, `η ↦ y t⁻¹`, is `(η²)`. -/
theorem ker_cuspToReesQuot :
    RingHom.ker (cuspToReesQuot k) = Ideal.span {(X 1 : MvPolynomial (Fin 2) k) ^ 2} := by
  classical
  refine le_antisymm (fun P hP ↦ ?_) ?_
  · rw [RingHom.mem_ker, cuspToReesQuot_apply, Ideal.Quotient.eq_zero_iff_mem] at hP
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hP
    have hcoeff (d : ℕ) : eval (cuspCoord k)
        (homogeneousComponent d (map (algebraMap k 𝒪) P)) ∈ 𝔪 ^ (d + 1) := by
      rw [← Ideal.coeff_mvPolynomialToRees, ← hw]
      simp only [MulMemClass.coe_mul, Ideal.coe_extendedReesAlgebraT, T,
        AddMonoidAlgebra.coeff_mul_single_apply, mul_one]
      have := Ideal.coeff_mem_pow_of_mem_extendedReesAlgebra w.2 (-(d : ℤ) - 1)
      rwa [show (-(-(d : ℤ) - 1)).toNat = d + 1 by omega] at this
    have key (d : ℕ) : (Polynomial.X : Polynomial k) ^ (2 * (d + 1)) ∣
        aeval (cuspParamPt k) (homogeneousComponent d P) := by
      have := X_pow_dvd_cuspParam k (hcoeff d)
      rwa [homogeneousComponent_map, ← RingHom.comp_apply, ← RingHom.comp_apply,
        cuspParam_comp] at this
    rw [show (X 1 ^ 2 : MvPolynomial (Fin 2) k) = monomial (Finsupp.single 1 2) 1 by
      simp [X_pow_eq_monomial],
      show ({monomial (Finsupp.single (1 : Fin 2) 2) (1 : k)} : Set (MvPolynomial (Fin 2) k)) =
        (fun s ↦ monomial s (1 : k)) '' {Finsupp.single (1 : Fin 2) 2} from
          (Set.image_singleton (f := fun s ↦ monomial s (1 : k))).symm,
      mem_ideal_span_monomial_image]
    intro m hm
    refine ⟨_, rfl, ?_⟩
    rw [Finsupp.single_le_iff]
    by_contra hlt
    push Not at hlt
    have h := coeff_aeval_cusp k (homogeneousComponent_isHomogeneous m.degree P) m rfl
    rw [coeff_homogeneousComponent, ite_eq_left rfl] at h
    obtain ⟨q, hq⟩ := key m.degree
    rw [hq, Polynomial.coeff_X_pow_mul', ite_eq_right (by omega)] at h
    exact (mem_support_iff.1 hm) h.symm
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact X_one_sq_mem_ker_cuspToReesQuot k

/-- (blueprint `example-normal-cone-point`) **The normal cone of the cusp.** For the cusp
`A = k[x, y] / (y² - x³)` and the ideal `I = (x, y)` of the origin, the graded algebra
`A[t, I t⁻¹] / (t) = ⨁_r I^r / I^{r+1}` is `k[ξ, η] / (η²)`, with `ξ, η` the classes of
`x, y ∈ I / I²` (`MvPolynomial.cuspReesQuotEquiv_mk_X`): the normal cone is a double line. -/
noncomputable def cuspReesQuotEquiv :
    MvPolynomial (Fin 2) k ⧸ Ideal.span {(X 1 : MvPolynomial (Fin 2) k) ^ 2} ≃+*
      (𝔪).extendedReesAlgebra ⧸ Ideal.span {(𝔪).extendedReesAlgebraT} :=
  (Ideal.quotEquivOfEq (ker_cuspToReesQuot k).symm).trans
    (RingHom.quotientKerEquivOfSurjective (cuspToReesQuot_surjective k))

lemma cuspReesQuotEquiv_mk (P : MvPolynomial (Fin 2) k) :
    cuspReesQuotEquiv k (Ideal.Quotient.mk _ P) = cuspToReesQuot k P :=
  rfl

/-- The isomorphism `MvPolynomial.cuspReesQuotEquiv` sends `ξ` and `η` to the classes of `x t⁻¹`
and `y t⁻¹`. -/
lemma cuspReesQuotEquiv_mk_X (i : Fin 2) :
    cuspReesQuotEquiv k (Ideal.Quotient.mk _ (X i)) =
      Ideal.Quotient.mk _ ⟨LaurentPolynomial.C (cuspCoord k i) * T (-1),
        Ideal.C_mul_T_neg_one_mem_extendedReesAlgebra (Ideal.subset_span (Set.mem_range_self i))⟩ :=
  cuspToReesQuot_X k i

/-- (blueprint `example-normal-cone-point`) The associated graded ring `⨁_r I^r / I^{r+1}` of the
ideal `I = (x, y)` of the origin of the cusp `k[x, y] / (y² - x³)` is `k[ξ, η] / (η²)`. -/
theorem nonempty_cusp_ringEquiv_associatedGraded :
    Nonempty (MvPolynomial (Fin 2) k ⧸ Ideal.span {(X 1 : MvPolynomial (Fin 2) k) ^ 2} ≃+*
      Ideal.associatedGraded 𝔪) := by
  obtain ⟨e, -⟩ := Ideal.rees_associatedGraded_chart 𝔪
  exact ⟨(cuspReesQuotEquiv k).trans e.symm⟩

end MvPolynomial

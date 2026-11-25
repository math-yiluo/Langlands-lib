/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.ReesAlgebra
public import WeilConjectures.RingTheory.QuasiRegularRees
public import WeilConjectures.RingTheory.TangentConeRegular
public import WeilConjectures.RingTheory.SmoothPurity.ReesAssociatedGradedChart
public import Mathlib.RingTheory.Polynomial.Ideal

/-!
# The normal cone of a smooth point

The smooth case of blueprint `example-normal-cone-point`: at a smooth point `Z = {y}` of `X` the
graded algebra `⨁_r I^r / I^{r+1}` is the symmetric algebra of `I / I²`, a polynomial ring over
`𝒪_Z` in `dim X` variables, so the normal cone `N_Z X` is the tangent space at `y`.

We state this both for the origin of affine space, where the coordinates `x_i` become the
variables, and for the maximal ideal of a regular local ring. The graded algebra is realised as
the special fibre `R[t, I t⁻¹] / (t)` of the deformation to the normal cone; it is identified
with `Ideal.associatedGraded I` by `Ideal.rees_associatedGraded_chart`.

## Main results

- `Ideal.mvPolynomialOriginReesQuotEquiv`: `k[x_i] ≅ k[x_i][t, I t⁻¹] / (t)` for the origin
  `I = (x_i)`, sending `x_i` to the class of `x_i t⁻¹`.
- `Ideal.nonempty_mvPolynomial_ringEquiv_associatedGraded_mvPolynomialOrigin`:
  `gr_I k[x_i] ≅ k[x_i]`.
- `IsLocalRing.exists_mvPolynomial_residueField_equiv_reesQuot`: for a regular local ring `R`
  of dimension `n`, `𝔪`'s normal cone algebra is `κ[X₁, …, X_n]`.
- `IsLocalRing.exists_mvPolynomial_residueField_ringEquiv_associatedGraded`: the same for
  `gr_𝔪 R`.
-/

@[expose] public section

open LaurentPolynomial

namespace Ideal

variable (C : Type*) [CommRing C] (σ : Type*)

lemma ker_map_evalRingHom_zero :
    RingHom.ker (MvPolynomial.map (σ := σ) (Polynomial.evalRingHom (0 : C))) =
      span {MvPolynomial.C Polynomial.X} := by
  rw [MvPolynomial.ker_map, Polynomial.ker_evalRingHom, map_span, Set.image_singleton]
  simp

lemma map_span_C_X_mvPolynomialExtendedReesAlgebraEquiv :
    (span {MvPolynomial.C (Polynomial.X : Polynomial C)} : Ideal (MvPolynomial σ _)).map
        (mvPolynomialExtendedReesAlgebraEquiv C σ) =
      span {(mvPolynomialOrigin C σ).extendedReesAlgebraT} := by
  rw [map_span, Set.image_singleton]
  congr 2
  exact Subtype.ext (by simp [mvPolynomialToLaurent_C])

/-- (blueprint `example-normal-cone-point`) **The normal cone of the origin of affine space.**
For the ideal `I = (x_i)` of the origin in `k[x_i]`, the graded algebra
`k[x_i][t, I t⁻¹] / (t) = ⨁_r I^r / I^{r+1}` is the polynomial ring `k[x_i]`, `x_i` going to the
class of `x_i t⁻¹`, i.e. of `x_i ∈ I / I²`. -/
noncomputable def mvPolynomialOriginReesQuotEquiv :
    MvPolynomial σ C ≃+* (mvPolynomialOrigin C σ).extendedReesAlgebra ⧸
      span {(mvPolynomialOrigin C σ).extendedReesAlgebraT} :=
  ((quotEquivOfEq (ker_map_evalRingHom_zero C σ)).symm.trans
      (RingHom.quotientKerEquivOfSurjective (f := MvPolynomial.map (σ := σ)
        (Polynomial.evalRingHom (0 : C)))
        (MvPolynomial.map_surjective _ fun c ↦ ⟨Polynomial.C c, by simp⟩))).symm.trans
    (quotientEquiv _ _ (mvPolynomialExtendedReesAlgebraEquiv C σ)
      (map_span_C_X_mvPolynomialExtendedReesAlgebraEquiv C σ).symm)

lemma mvPolynomialOriginReesQuotEquiv_X (i : σ) :
    mvPolynomialOriginReesQuotEquiv C σ (MvPolynomial.X i) =
      Ideal.Quotient.mk _ ⟨LaurentPolynomial.C (MvPolynomial.X i) * T (-1),
        C_mul_T_neg_one_mem_extendedReesAlgebra (subset_span (Set.mem_range_self i))⟩ := by
  rw [mvPolynomialOriginReesQuotEquiv, RingEquiv.trans_apply, RingEquiv.symm_trans_apply,
    RingEquiv.symm_symm]
  rw [show (RingHom.quotientKerEquivOfSurjective (f := MvPolynomial.map (σ := σ)
        (Polynomial.evalRingHom (0 : C)))
        (MvPolynomial.map_surjective _ fun c ↦ ⟨Polynomial.C c, by simp⟩)).symm
        (MvPolynomial.X i) = Ideal.Quotient.mk _ (MvPolynomial.X i) from
      (RingEquiv.symm_apply_eq _).2 (by simp)]
  simp only [quotEquivOfEq_mk, quotientEquiv_apply, RingHom.toMonoidHom_eq_coe,
    OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_ofClass, quotientMap_mk,
    RingHom.coe_coe]
  congr 1
  exact Subtype.ext (mvPolynomialToLaurent_X C σ i)

lemma mvPolynomialOriginReesQuotEquiv_C (c : C) :
    mvPolynomialOriginReesQuotEquiv C σ (MvPolynomial.C c) =
      Ideal.Quotient.mk _ (algebraMap _ _ (MvPolynomial.C c : MvPolynomial σ C)) := by
  rw [mvPolynomialOriginReesQuotEquiv, RingEquiv.trans_apply, RingEquiv.symm_trans_apply,
    RingEquiv.symm_symm]
  rw [show (RingHom.quotientKerEquivOfSurjective (f := MvPolynomial.map (σ := σ)
        (Polynomial.evalRingHom (0 : C)))
        (MvPolynomial.map_surjective _ fun c ↦ ⟨Polynomial.C c, by simp⟩)).symm
        (MvPolynomial.C c) = Ideal.Quotient.mk _ (MvPolynomial.C (Polynomial.C c)) from
      (RingEquiv.symm_apply_eq _).2 (by simp)]
  simp only [quotEquivOfEq_mk, quotientEquiv_apply, RingHom.toFun_eq_coe, RingEquiv.coe_toRingHom,
    quotientMap_mk]
  congr 1
  exact Subtype.ext (by simp [mvPolynomialToLaurent_C])

/-- (blueprint `example-normal-cone-point`) The associated graded ring `⨁_r I^r / I^{r+1}` of the
ideal `I = (x_i)` of the origin of affine space is a polynomial ring over `k` in the `x_i`. -/
theorem nonempty_mvPolynomial_ringEquiv_associatedGraded_mvPolynomialOrigin :
    Nonempty (MvPolynomial σ C ≃+* associatedGraded (mvPolynomialOrigin C σ)) := by
  obtain ⟨e, -⟩ := rees_associatedGraded_chart (mvPolynomialOrigin C σ)
  exact ⟨(mvPolynomialOriginReesQuotEquiv C σ).trans e.symm⟩

end Ideal

namespace IsLocalRing

variable (R : Type*) [CommRing R] [IsRegularLocalRing R]

/-- (blueprint `example-normal-cone-point`) **The normal cone at a smooth point.** For a regular
local ring `R` of dimension `n` with maximal ideal `𝔪`, the graded algebra
`R[t, 𝔪 t⁻¹] / (t) = ⨁_r 𝔪^r / 𝔪^{r+1}` is a polynomial ring in `n` variables over the residue
field. -/
theorem exists_mvPolynomial_residueField_equiv_reesQuot :
    ∃ n : ℕ, ringKrullDim R = n ∧ Nonempty (MvPolynomial (Fin n) (ResidueField R) ≃+*
      (maximalIdeal R).extendedReesAlgebra ⧸
        Ideal.span {(maximalIdeal R).extendedReesAlgebraT}) := by
  classical
  obtain ⟨s, hs, hspan⟩ :=
    (IsNoetherian.noetherian (maximalIdeal R)).exists_span_finset_card_eq_spanFinrank
  have hset : {x | x ∈ s.toList} = (s : Set R) := by ext; simp
  have hd : ringKrullDim R = (s.card : WithBot ℕ∞) := by
    rw [hs, IsRegularLocalRing.spanFinrank_maximalIdeal]
  have hrs : IsRegularSystemOfParameters s.toList :=
    ⟨by rw [hset]; exact hspan, by rw [Finset.length_toList, hd]⟩
  have hreg := (IsRegularLocalRing.isRegular_and_quotients_of_generators R s.card hd _ hrs).1
  obtain ⟨a, ha, haspan⟩ := MvPolynomial.exists_isRevRegular_of_isWeaklyRegular s.toList
    hreg.toIsWeaklyRegular s.card (Finset.length_toList s)
  exact ⟨s.card, hd, ⟨Ideal.mvPolynomialEquivReesQuotOfEq a ha (haspan.trans hrs.1)⟩⟩

/-- (blueprint `example-normal-cone-point`) For a regular local ring `R` of dimension `n`, the
associated graded ring `⨁_r 𝔪^r / 𝔪^{r+1}` is a polynomial ring in `n` variables over the
residue field. -/
theorem exists_mvPolynomial_residueField_ringEquiv_associatedGraded :
    ∃ n : ℕ, ringKrullDim R = n ∧
      Nonempty (MvPolynomial (Fin n) (ResidueField R) ≃+*
        Ideal.associatedGraded (maximalIdeal R)) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := exists_mvPolynomial_residueField_equiv_reesQuot R
  obtain ⟨f, -⟩ := Ideal.rees_associatedGraded_chart (maximalIdeal R)
  exact ⟨n, hn, ⟨e.trans f.symm⟩⟩

end IsLocalRing

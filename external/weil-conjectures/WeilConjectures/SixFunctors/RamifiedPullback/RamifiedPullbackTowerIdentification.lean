/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedPullbackTowerData
import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedCoefficientQuotientComparison
import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedFinitePullbackComparison
import WeilConjectures.SixFunctors.RamifiedPullback.FinitePullbackTransitionGenerators
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralProjectionDivisibility

/-! # Ramified identification of finite pullback towers

The arithmetic construction and factorization of the normalized finite comparison.
Source: Stacks 093M, 03EK, 03EL; Bhatt--Scholze 6.8.2(1).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.RamifiedPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private theorem ramification_exists :
    ∃ e : ℕ, 1 ≤ e ∧
      Ideal.span
        ({integralScalarIntegerInclusion l E L ι (Padic.coefficientExtensionUniformizer l E)} :
          Set (Padic.coefficientExtensionIntegers l L)) =
        Ideal.span {Padic.coefficientExtensionUniformizer l L ^ e} ∧
      ∀ k : ℕ, 1 ≤ k →
        Ideal.span
          ({integralScalarIntegerInclusion l E L ι (Padic.coefficientExtensionUniformizer l E)} :
            Set (Padic.coefficientExtensionIntegers l L)) =
          Ideal.span {Padic.coefficientExtensionUniformizer l L ^ k} → k = e := by
  let R := Padic.coefficientExtensionIntegers l E
  let S := Padic.coefficientExtensionIntegers l L
  let t := Padic.coefficientExtensionUniformizer l E
  let v := Padic.coefficientExtensionUniformizer l L
  let f := integralScalarIntegerInclusion l E L ι
  have hE := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hL := (Padic.coefficientExtensionIntegers_dvr l L).choose_spec
  have : IsLocalRing R := hE.2.2.2.1
  have : IsLocalRing S := hL.2.2.2.1
  have : IsDiscreteValuationRing R := hE.2.2.2.2.2.2.2.1
  have : IsDiscreteValuationRing S := hL.2.2.2.2.2.2.2.1
  have ht : Ideal.span ({t} : Set R) = Padic.coefficientExtensionMaximalIdeal l E :=
    hE.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hv : Ideal.span ({v} : Set S) = Padic.coefficientExtensionMaximalIdeal l L :=
    hL.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hti : Irreducible t :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr
      ((hE.2.2.2.2.2.1 _ (IsLocalRing.maximalIdeal.isMaximal R)).trans ht.symm)
  have hvi : Irreducible v :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer v).mpr
      ((hL.2.2.2.2.2.1 _ (IsLocalRing.maximalIdeal.isMaximal S)).trans hv.symm)
  have hft : f t ≠ 0 := by
    intro hz
    have hz' : ι (t : E) = 0 := congrArg Subtype.val hz
    exact hti.ne_zero (Subtype.ext (ι.injective (by simpa using hz')))
  have hnu : ¬ IsUnit (f t) := by
    intro h
    have ha := (hL.2.2.1 (f t)).mp h
    change Padic.coefficientExtensionAbsoluteValue l L (ι (t : E)) = 1 at ha
    rw [integralScalar_absoluteValue l E L ι] at ha
    have hb := (hE.2.1 t).mp
      (show t ∈ Padic.coefficientExtensionMaximalIdeal l E from
        ht ▸ Ideal.mem_span_singleton_self t)
    exact (ne_of_lt hb) ha
  obtain ⟨e, w, heq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hft hvi
  have he : 1 ≤ e := by
    by_contra hn
    have hz : e = 0 := by omega
    apply hnu
    rw [hz, pow_zero, mul_one] at heq
    exact heq.symm ▸ w.isUnit
  have hideal : Ideal.span ({f t} : Set S) = Ideal.span {v ^ e} := by
    rw [heq]
    exact Ideal.span_singleton_mul_left_unit w.isUnit _
  refine ⟨e, he, hideal, ?_⟩
  intro k _ hk
  have ha := Ideal.span_singleton_eq_span_singleton.mp (hk.symm.trans hideal)
  exact Nat.le_antisymm
    ((pow_dvd_pow_iff hvi.ne_zero hvi.not_isUnit).mp ha.dvd)
    ((pow_dvd_pow_iff hvi.ne_zero hvi.not_isUnit).mp ha.symm.dvd)

private theorem ramified_kernel (e n : ℕ)
    (he : Ideal.span
      ({integralScalarIntegerInclusion l E L ι (Padic.coefficientExtensionUniformizer l E)} :
        Set (Padic.coefficientExtensionIntegers l L)) =
      Ideal.span {Padic.coefficientExtensionUniformizer l L ^ e})
    (hexp : index e n + 1 = e * (n + 1))
    (x : Padic.coefficientExtensionIntegers l E)
    (hx : x ∈ Padic.coefficientExtensionIdeal l E (n + 1)) :
    Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (index e n + 1))
      (integralScalarIntegerInclusion l E L ι x) = 0 := by
  let f := integralScalarIntegerInclusion l E L ι
  have hi : Ideal.map f (Padic.coefficientExtensionIdeal l E (n + 1)) =
      Padic.coefficientExtensionIdeal l L (index e n + 1) := by
    simp only [Padic.coefficientExtensionIdeal, Ideal.map_pow]
    rw [Ideal.map_span, Set.image_singleton, he, ← Ideal.span_singleton_pow,
      ← pow_mul, hexp]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← hi]
  exact Ideal.mem_map_of_mem f hx

private def ramifiedQuotient (e n : ℕ)
    (he : Ideal.span
      ({integralScalarIntegerInclusion l E L ι (Padic.coefficientExtensionUniformizer l E)} :
        Set (Padic.coefficientExtensionIntegers l L)) =
      Ideal.span {Padic.coefficientExtensionUniformizer l L ^ e})
    (hexp : index e n + 1 = e * (n + 1)) :
    Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1) :=
  Ideal.Quotient.lift (Padic.coefficientExtensionIdeal l E (n + 1))
    ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (index e n + 1))).comp
      (integralScalarIntegerInclusion l E L ι)) (ramified_kernel l E L ι e n he hexp)

end WeilConjectures.RamifiedPullback

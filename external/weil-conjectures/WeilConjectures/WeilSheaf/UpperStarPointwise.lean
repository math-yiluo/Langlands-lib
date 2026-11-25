/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ArtinSchreierPurity
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Real

/-!
# Pointwise properties of pullbacks of Weil sheaves

At a closed point `z` of `X` over `x = φ z`, the local Frobenius of the pullback `φ^* F` has the
characteristic polynomial of `Fₓʳ`, `r = [κ(z) : κ(x)]`
(`AlgebraicGeometry.WeilSheaf.charpoly_frobeniusEnd_stalk_upperStar`). Hence:

- purity of `φ^* F` at `z` is purity of `F` at `x`
  (`AlgebraicGeometry.WeilSheaf.isPureOfWeight_stalk_upperStar_iff`);
- the pullback of an `ι`-real Weil sheaf is `ι`-real
  (`AlgebraicGeometry.WeilSheaf.IsReal.upperStar`).

Both are pointwise statements, which do not need any compatibility of pullbacks with
composition.
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- If the Frobenius of `N` has the characteristic polynomial of the `r`-th power of the
Frobenius of `M`, `r ≥ 1`, then `M` is pure of weight `w` relative to `q` if and only if `N` is
pure of weight `w` relative to `q ^ r`: the eigenvalues of `F_Mʳ` are the `r`-th powers of those
of `F_M`, and `r`-th roots of nonnegative reals are unique. -/
theorem isPureOfWeight_iff_of_charpoly_eq_pow [IsAlgClosed K] {ι : K →+* ℂ} {q : ℕ}
    {M N : FrobeniusModule.{u, v} K} {w : ℝ} {r : ℕ} (hr : 0 < r)
    (hMN : N.frobeniusEnd.charpoly = (M.frobeniusEnd ^ r).charpoly) :
    M.IsPureOfWeight ι q w ↔ N.IsPureOfWeight ι (q ^ r) w := by
  refine ⟨fun h ↦ h.of_charpoly_eq_pow hr hMN, fun h α hα ↦ ?_⟩
  have hβ : N.frobeniusEnd.HasEigenvalue (α ^ r) := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hMN,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly, Module.End.hasEigenvalue_iff_mem_spectrum,
      spectrum.map_pow_of_pos _ hr]
    exact ⟨α, Module.End.hasEigenvalue_iff_mem_spectrum.1 hα, rfl⟩
  have key := h _ hβ
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rw [map_pow, norm_pow, Nat.cast_pow, ← Real.rpow_natCast_mul hq, mul_comm,
    Real.rpow_mul_natCast hq] at key
  exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hq _) hr.ne').1 key

/-- If the Frobenius of `N` has the characteristic polynomial of the `r`-th power of the
Frobenius of `M`, `r ≥ 1`, and `M` has weights at most `w` relative to `q`, then `N` has weights
at most `w` relative to `q ^ r`: every eigenvalue of `F_Mʳ` is the `r`-th power of an eigenvalue
of `F_M`. -/
theorem HasWeightsAtMost.of_charpoly_eq_pow [IsAlgClosed K] {ι : K →+* ℂ} {q : ℕ}
    {M N : FrobeniusModule.{u, v} K} {w : ℝ} (h : M.HasWeightsAtMost ι q w) {r : ℕ} (hr : 0 < r)
    (hMN : N.frobeniusEnd.charpoly = (M.frobeniusEnd ^ r).charpoly) :
    N.HasWeightsAtMost ι (q ^ r) w := by
  intro β hβ
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hMN,
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly, Module.End.hasEigenvalue_iff_mem_spectrum,
    spectrum.map_pow_of_pos _ hr] at hβ
  obtain ⟨α, hα, rfl⟩ := hβ
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum] at hα
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rw [map_pow, norm_pow, Nat.cast_pow, ← Real.rpow_natCast (q : ℝ), ← Real.rpow_mul hq,
    mul_comm, Real.rpow_mul hq, Real.rpow_natCast]
  exact pow_le_pow_left₀ (norm_nonneg _) (h α hα) r

/-- If the Frobenius of `N` has the characteristic polynomial of a power of the Frobenius of an
`ι`-real Frobenius module `M`, then `N` is `ι`-real: the traces of the powers of `F_Mʳ` are
traces of powers of `F_M`, which are `ι`-real (`FrobeniusModule.isReal_iff_forall_trace_pow`). -/
theorem IsReal.of_charpoly_eq_pow {ι : K →+* ℂ} {M : FrobeniusModule.{u, v} K}
    {N : FrobeniusModule.{w, v} K} (h : M.IsReal ι) (r : ℕ)
    (hMN : N.frobeniusEnd.charpoly = (M.frobeniusEnd ^ r).charpoly) : N.IsReal ι := by
  have : CharZero K := ι.charZero
  have hM := (isReal_iff_forall_trace_pow ι M).1 h
  have key := (LinearMap.forall_coeff_charpolyRev_mem_iff (M.frobeniusEnd ^ r)
    ι.realSubfield).2 fun m ↦ by
      rw [← pow_mul]
      exact hM (r * m)
  intro n
  have hc : N.localPolynomial = (M.frobeniusEnd ^ r).charpolyRev := by
    rw [localPolynomial, LinearMap.charpolyRev_def, LinearMap.charpolyRev_def, hMN]
  rw [hc]
  exact key n

end FrobeniusModule

namespace AlgebraicGeometry

/-- A point whose image under an open immersion has finite residue field has finite residue
field: open immersions induce isomorphisms of residue fields. -/
theorem Scheme.Hom.mem_finitePoints_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {x : X} (hx : f.base x ∈ Y.finitePoints) : x ∈ X.finitePoints :=
  have : Finite (Y.residueField (f.base x)) := hx
  Finite.of_equiv _ (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv.toEquiv

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

/-- The degree of a closed point of `X` is a multiple of the degree of its image, and the
residue cardinality at the point is the corresponding power of that at the image. -/
theorem residueCard_eq_pow_of_upperStar (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (z : X.finitePoints) :
    0 < (X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 /
        (Y ↘ Spec (CommRingCat.of k₀)).degreeOver (φ.base z.1) ∧
      (X ↘ Spec (CommRingCat.of k₀)).residueCard z.1 =
        (Y ↘ Spec (CommRingCat.of k₀)).residueCard (φ.base z.1) ^
          ((X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 /
            (Y ↘ Spec (CommRingCat.of k₀)).degreeOver (φ.base z.1)) := by
  have hx₂ := Scheme.Hom.map_mem_finitePoints φ z.2
  have hdvd : (Y ↘ Spec (CommRingCat.of k₀)).degreeOver (φ.base z.1) ∣
      (X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 := by
    have := Scheme.Hom.degreeOver_dvd_degreeOver_comp φ (Y ↘ Spec (CommRingCat.of k₀)) z.2
    rwa [comp_over φ (Spec (CommRingCat.of k₀))] at this
  have hz := Scheme.Hom.degreeOver_ne_zero (X ↘ Spec (CommRingCat.of k₀)) z.2
  have hx := Scheme.Hom.degreeOver_ne_zero (Y ↘ Spec (CommRingCat.of k₀)) hx₂
  refine ⟨Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hz) hdvd) (Nat.pos_of_ne_zero hx), ?_⟩
  rw [Scheme.Hom.residueCard, Scheme.Hom.residueCard, ← pow_mul, Nat.mul_div_cancel' hdvd]

/-- **Purity of a pullback at a point.** The stalk of `φ^* F` at a closed point `z` is pure of
weight `w` exactly when the stalk of `F` at `φ z` is: the local Frobenius at `z` has the
characteristic polynomial of the `r`-th power of that at `φ z`, and `q_z = q_{φ z}ʳ`. -/
theorem isPureOfWeight_stalk_upperStar_iff (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l Y) (z : X.finitePoints) {ι : PadicAlgCl l →+* ℂ} {w : ℝ} :
    (((upperStar φ).obj F).stalk z).IsPureOfWeight ι
        ((X ↘ Spec (CommRingCat.of k₀)).residueCard z.1) w ↔
      (F.stalk ⟨φ.base z.1, Scheme.Hom.map_mem_finitePoints φ z.2⟩).IsPureOfWeight ι
        ((Y ↘ Spec (CommRingCat.of k₀)).residueCard (φ.base z.1)) w := by
  obtain ⟨hr, hq⟩ := residueCard_eq_pow_of_upperStar (k₀ := k₀) φ z
  rw [hq]
  exact (FrobeniusModule.isPureOfWeight_iff_of_charpoly_eq_pow hr
    (charpoly_frobeniusEnd_stalk_upperStar φ F z)).symm

/-- **Pullbacks preserve upper weight bounds**: the local Frobenius of `φ^* F` at a closed point
`z` has the characteristic polynomial of a power of that of `F` at `φ z`. -/
theorem HasWeightsAtMost.upperStar {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l Y} {w : ℝ}
    (h : F.HasWeightsAtMost ι w) (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] :
    ((upperStar φ).obj F).HasWeightsAtMost ι w := by
  intro z
  obtain ⟨hr, hq⟩ := residueCard_eq_pow_of_upperStar (k₀ := k₀) φ z
  rw [hq]
  exact FrobeniusModule.HasWeightsAtMost.of_charpoly_eq_pow
    (h ⟨φ.base z.1, Scheme.Hom.map_mem_finitePoints φ z.2⟩) hr
    (charpoly_frobeniusEnd_stalk_upperStar φ F z)

/-- **The pullback of an `ι`-real sheaf is `ι`-real**: the local Frobenius of `φ^* F` at a closed
point `z` has the characteristic polynomial of a power of that of `F` at `φ z`. -/
theorem IsReal.upperStar {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l Y} (h : F.IsReal ι)
    (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] :
    ((upperStar φ).obj F).IsReal ι := fun z ↦
  (h _).of_charpoly_eq_pow _ (charpoly_frobeniusEnd_stalk_upperStar φ F z)

end WeilSheaf

end AlgebraicGeometry

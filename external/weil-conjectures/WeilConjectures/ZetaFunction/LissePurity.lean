/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.PoincareDualityLisse
public import WeilConjectures.WeilSheaf.TraceIsomorphism
public import WeilConjectures.ZetaFunction.Weights

/-!
# Purity of the cohomology of a lisse pure Weil sheaf on a smooth proper variety

Let `X₀` be a smooth proper `k₀`-scheme of pure dimension `d` and `F` a lisse Weil sheaf on `X₀`,
punctually `ι`-pure of weight `w`. Then `Hⁱ(X₀ ⊗ k̄, F)` is `ι`-pure of weight `w + i`: the
Deligne–Laumon estimate bounds the weights of `H_c^i = Hⁱ` by `w + i`, and Poincaré duality
`H_c^i(F) × H^{2d-i}(F^∨(d)) ⟶ ℚ̄_ℓ`, with `F^∨(d)` lisse and punctually pure of weight
`-w - 2d`, turns the same estimate in degree `2d - i` into the lower bound. This is the absolute
case `Y₀ = Spec k₀` of `theorem-purity-higher-direct-images-under`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology`: the upper
  bound for `H_c^i` of a sheaf mixed of weights at most `w`.
- `AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_cohomology_of_isLisse`: purity of `Hⁱ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/- Through `Mathlib.AlgebraicGeometry.Group.Affine`, `Spec k₀` is also an object over itself via
`specOverSpec`; prefer the identity structure `CategoryTheory.instOverClass`. -/
attribute [local instance 1100] CategoryTheory.instOverClass

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] {ι : PadicAlgCl l →+* ℂ}

section

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The Deligne–Laumon estimate for compactly supported cohomology: for a separated `k₀`-scheme
`X₀` of finite type and a Weil sheaf `F` mixed of weights at most `w`, `H_c^i(X₀ ⊗ k̄, F)` has
weights at most `w + i` over `k₀` (blueprint `theorem-direct-image-mixed-sheaf--1` for the structure
morphism). -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology {F : WeilSheaf k₀ l X} {w : ℝ}
    (hF : F.IsMixedOfWeightsAtMost ι w) (i : ℤ) :
    (F.compactlySupportedCohomology i).HasWeightsAtMostOver k₀ ι (w + i) :=
  IsMixedOfWeightsAtMost.hasWeightsAtMostOver_globalSections
    (((WeilComplex.isMixedOfWeightsAtMost_toComplex_iff F).2 hF).derivedLowerShriek
      (X ↘ Spec (CommRingCat.of k₀)) i)

/-- The Tate twist `(d)` multiplies the local Frobenius at a closed point `x` by `q_x⁻ᵈ`, so it
lowers the weights by `2d`: the constant twist by `χ_ℓ(σ)ᵈ = q⁻ᵈ` has
`2 log_q |ι (q⁻ᵈ)| = -2d` (blueprint `proposition-weights-under-usual-operations--13`). -/
theorem two_mul_logb_norm_cyclotomicUnit_pow_eq (d : ℕ) :
    2 * Real.logb (Nat.card k₀) ‖ι ((cyclotomicUnit k₀ l ^ d : (PadicAlgCl l)ˣ) : PadicAlgCl l)‖ =
      -(2 * d) := by
  have hq : (1 : ℝ) < Nat.card k₀ := by exact_mod_cast Finite.one_lt_card
  rw [Units.val_pow_eq_pow_val, cyclotomicUnit_eq, map_pow, map_inv₀, map_natCast, norm_pow,
    norm_inv, Complex.norm_natCast, Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one hq]
  ring

end

/-- **Purity for lisse coefficients** (the absolute case of
`theorem-purity-higher-direct-images-under`): for `X₀` smooth and proper of pure dimension `d` over
`k₀` and `F` a lisse Weil sheaf on `X₀`, punctually `ι`-pure of weight `w`, the Frobenius module
`Hⁱ(X₀ ⊗ k̄, F)` is `ι`-pure of weight `w + i` over `k₀`. -/
theorem isPureOfWeightOver_cohomology_of_isLisse (d : ℕ) [IsProper (X ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X}
    (hF : F.IsLisse) {w : ℝ} (hw : F.IsPunctuallyPureOfWeight ι w) (i : ℤ) :
    (F.cohomology i).IsPureOfWeightOver k₀ ι (w + i) := by
  intro α hα
  obtain ⟨e⟩ :=
    WeilComplex.nonempty_equiv_compactlySupportedCohomology_cohomology (toComplex.obj F) i
  have hαc := e.symm.hasEigenvalue hα
  refine le_antisymm
    (hasWeightsAtMostOver_compactlySupportedCohomology hw.isMixedOfWeightsAtMost i α hαc) ?_
  -- The twisted dual `F^∨(d)` is punctually pure of weight `-w - 2d`.
  have hFd : ((F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ d)).IsPunctuallyPureOfWeight ι
      (-w + -(2 * d)) :=
    IsPunctuallyPureOfWeight.constantTwist (fun x ↦ by
      obtain ⟨e⟩ := nonempty_equiv_stalk_dual hF x
      exact (hw x).dual.of_equiv e) (two_mul_logb_norm_cyclotomicUnit_pow_eq d)
  obtain ⟨P, hP, hPF⟩ :=
    exists_isPerfPair_compactlySupportedCohomology_dual d hF i (2 * d - i) (by ring)
  -- `α⁻¹` is an eigenvalue of the Frobenius on `H^{2d-i}(X₀ ⊗ k̄, F^∨(d))`.
  have hβ : (((F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ d)).cohomology
      (2 * d - i)).frobeniusEnd.HasEigenvalue α⁻¹ := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, ← Polynomial.mem_roots
      (Polynomial.Monic.ne_zero (LinearMap.charpoly_monic _)),
      LinearMap.charpoly_roots_of_similitude (p := P) one_ne_zero
        (fun x y ↦ (one_mul (P x y)).symm ▸ hPF x y)]
    refine Multiset.mem_map.2 ⟨α, ?_, one_div α⟩
    rw [Polynomial.mem_roots (Polynomial.Monic.ne_zero (LinearMap.charpoly_monic _)),
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact hαc
  obtain ⟨e'⟩ := WeilComplex.nonempty_equiv_compactlySupportedCohomology_cohomology
    (toComplex.obj ((F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ d))) (2 * d - i)
  have h := hasWeightsAtMostOver_compactlySupportedCohomology hFd.isMixedOfWeightsAtMost
    (2 * d - i) _ (e'.symm.hasEigenvalue hβ)
  have hq : (0 : ℝ) < Nat.card k₀ := Nat.cast_pos.2 Nat.card_pos
  have hpos : 0 < ‖ι α‖ :=
    norm_pos_iff.2 ((map_ne_zero ι).2 (FrobeniusModule.ne_zero_of_hasEigenvalue hα))
  rw [map_inv₀, norm_inv, show (-w + -(2 * d) + ((2 * d - i : ℤ) : ℝ)) / 2 = -((w + i) / 2) by
    push_cast; ring, Real.rpow_neg hq.le] at h
  exact (inv_le_inv₀ hpos (Real.rpow_pos_of_pos hq _)).1 h

end AlgebraicGeometry.WeilSheaf

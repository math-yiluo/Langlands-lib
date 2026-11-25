/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.DirectImage
public import WeilConjectures.DeligneLaumon.Reduction.MixedStalk
public import WeilConjectures.WeilSheaf.PoincareDuality

/-!
# The weight estimate for smooth proper varieties

Let `X₀` be a smooth, proper, geometrically connected scheme of pure dimension `d` over the
finite field `k₀ = 𝔽_q`, and let `ι : ℚ̄_ℓ → ℂ` be a field embedding. Deligne's weight estimate
for `Rf_!` (`AlgebraicGeometry.hasDirectImageWeightBound_over_finiteField`, blueprint section
`chap-The-Deligne-Laumon-theorem-in-general`) applied to the structure morphism of `X₀` and the
constant Weil sheaf, which is punctually pure of weight `0`, shows that `H_c^i(X₀ ⊗ k̄, ℚ̄_ℓ)` has
weights at most `i`. Poincaré duality (`AlgebraicGeometry.WeilSheaf.poincareDuality`) turns this
upper bound in degree `2d - i` into a lower bound in degree `i`, so that `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` is
`ι`-pure of weight `i`: every eigenvalue `α` of the geometric Frobenius satisfies `|ι α| = q^{i/2}`.

## Main statements

- `AlgebraicGeometry.WeilComplex.proper_compact_coincidence`: `Ra_! ≅ Ra_*` and `H_c^i ≅ Hⁱ` for a
  proper `k₀`-scheme (`proposition-forgetting-supports-composition--3`).
- `AlgebraicGeometry.WeilSheaf.isMixedOfWeightsAtMost_toComplex_adicConstant`: the constant Weil
  sheaf, as a Weil complex, is mixed of weights at most `0`; together with
  `AlgebraicGeometry.WeilSheaf.isPunctuallyPureOfWeight_adicConstant` (the constant Weil sheaf is
  punctually pure of weight `0`, `corollary-purity-cohomology-smooth-proper-variety`) this is
  `corollary-purity-cohomology-smooth-proper-variety`
  (`AlgebraicGeometry.WeilSheaf.weightPurity_adicConstant`).
- `AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.hasWeightsAtMostOver_globalSections`: a
  Weil sheaf on `Spec k₀` mixed of weights at most `w` has global sections of weights at most `w`.
- `AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_adicConstant`:
  `H_c^i(X₀ ⊗ k̄, ℚ̄_ℓ)` has weights at most `i`.
- `AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_cohomology_adicConstant`: `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` is
  pure of weight `i` (`corollary-purity-cohomology-smooth-proper-variety--1`).
- `AlgebraicGeometry.WeilSheaf.purity_smoothProper`:
`corollary-purity-cohomology-smooth-proper-variety--1`.
- `AlgebraicGeometry.WeilSheaf.deligne_purity`: the five clauses of
`corollary-purity-cohomology-smooth-proper-variety` and
  of the subsection `corollary-purity-cohomology-smooth-proper-variety`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/- Through `Mathlib.AlgebraicGeometry.Group.Affine`, `Spec k₀` is also an object over itself via
`specOverSpec`; prefer the identity structure `CategoryTheory.instOverClass`. -/
attribute [local instance 1100] CategoryTheory.instOverClass

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `proposition-forgetting-supports-composition--3` (proper coincidence): for `Y` proper
over `k₀` with structure morphism `a`, the compactly supported direct image is the ordinary direct
image, `Ra_! K ≅ Ra_* K` (the identity is a compactification of `a`), and hence
`H_c^i(Y ⊗ k̄, K) ≅ Hⁱ(Y ⊗ k̄, K)` Frobenius-equivariantly for every Weil complex `K` and every
`i`. -/
theorem proper_compact_coincidence (K : WeilComplex k₀ l X) :
    Nonempty ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj K ≅
      (derivedLowerStar (X ↘ Spec (CommRingCat.of k₀))).obj K) ∧
    ∀ i : ℤ, Nonempty ((K.compactlySupportedCohomology i).Equiv (K.cohomology i)) :=
  ⟨⟨derivedLowerShriekObjIsoOfIsProper K⟩, nonempty_equiv_compactlySupportedCohomology_cohomology K⟩

end WeilComplex

namespace WeilSheaf

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Blueprint `corollary-purity-cohomology-smooth-proper-variety` (the complex form): the constant
Weil sheaf, viewed as a Weil complex concentrated in degree `0`, is `ι`-mixed of weights at most
`0`: its cohomology sheaf in degree `0` is the constant sheaf, punctually pure of weight `0`, and
the others vanish. -/
theorem isMixedOfWeightsAtMost_toComplex_adicConstant
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (ι : PadicAlgCl l →+* ℂ) :
    (toComplex.obj (adicConstant k₀ l X)).IsMixedOfWeightsAtMost ι 0 := by
  intro b
  by_cases hb : b = 0
  · subst hb
    rw [Int.cast_zero, add_zero, isMixedOfWeightsAtMost_iff_filtrationClosure]
    refine ObjectProperty.prop_of_iso _
      (WeilComplex.homologySheafSingleComplexIso 0 (adicConstant k₀ l X)).symm
      (ObjectProperty.le_filtrationClosure _
        ⟨0, le_rfl, isPunctuallyPureOfWeight_adicConstant (k₀ := k₀) (l := l) (X := X) (ι := ι)⟩)
  · exact isMixedOfWeightsAtMost_of_isZero
      (WeilComplex.isZero_homologySheaf_singleComplex hb _) _

/-- Blueprint `corollary-purity-cohomology-smooth-proper-variety`: the constant Weil sheaf is
`ι`-pure of weight `0`, punctually
(`AlgebraicGeometry.WeilSheaf.isPunctuallyPureOfWeight_adicConstant`), and as a Weil complex it is
mixed of weights at most `0`. -/
theorem weightPurity_adicConstant [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (ι : PadicAlgCl l →+* ℂ) :
    (adicConstant k₀ l X).IsPunctuallyPureOfWeight ι 0 ∧
      (toComplex.obj (adicConstant k₀ l X)).IsMixedOfWeightsAtMost ι 0 :=
  ⟨isPunctuallyPureOfWeight_adicConstant (k₀ := k₀) (l := l) (X := X) (ι := ι),
    isMixedOfWeightsAtMost_toComplex_adicConstant k₀ l X ι⟩

variable {k₀ l} in
/-- A Weil sheaf on `Spec k₀` which is `ι`-mixed of weights at most `w` has global sections of
weights at most `w`: every eigenvalue of the Frobenius on `Γ(Spec k̄, G)` is a local Frobenius
eigenvalue at the unique closed point, of degree one, and the filtration of `G` by punctually
pure sheaves of weights at most `w` bounds it. -/
theorem IsMixedOfWeightsAtMost.hasWeightsAtMostOver_globalSections {ι : PadicAlgCl l →+* ℂ}
    {G : WeilSheaf k₀ l (Spec (CommRingCat.of k₀))} {w : ℝ}
    (hG : G.IsMixedOfWeightsAtMost ι w) :
    G.globalSections.HasWeightsAtMostOver k₀ ι w := by
  intro β hβ
  obtain ⟨x, hx⟩ := exists_hasEigenvalue_stalk_of_hasEigenvalue_globalSections G hβ
  have h := hG.hasWeightsAtMost x _ hx
  have hm := (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2
  have hq : (0 : ℝ) ≤ Nat.card k₀ := Nat.cast_nonneg _
  rw [map_pow, norm_pow, Scheme.Hom.residueCard, Nat.cast_pow, ← Real.rpow_natCast_mul hq,
    mul_comm, Real.rpow_mul_natCast hq] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.rpow_nonneg hq _) hm).1 h

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Clause (2) of `corollary-purity-cohomology-smooth-proper-variety` and of
`corollary-purity-cohomology-smooth-proper-variety`: for a separated `k₀`-scheme `X₀` of finite
type, `H_c^i(X₀ ⊗ k̄, ℚ̄_ℓ)` is `ι`-mixed of weights at most `i`: every eigenvalue `α` of the
geometric Frobenius satisfies `|ι α| ≤ q^{i/2}`. This is the Deligne–Laumon estimate
`theorem-direct-image-mixed-sheaf--1` for the structure morphism of `X₀` and the constant Weil
sheaf, mixed of weights at most `0`. -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_adicConstant (ι : PadicAlgCl l →+* ℂ)
    (i : ℤ) :
    ((adicConstant k₀ l X).compactlySupportedCohomology i).HasWeightsAtMostOver k₀ ι i := by
  have h := (isMixedOfWeightsAtMost_toComplex_adicConstant k₀ l X ι).derivedLowerShriek
    (X ↘ Spec (CommRingCat.of k₀)) i
  rw [zero_add] at h
  exact IsMixedOfWeightsAtMost.hasWeightsAtMostOver_globalSections h

end WeilSheaf

namespace WeilSheaf

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] (d : ℕ)
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

omit [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))] in
/-- For `X₀` proper over `k₀`, `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` has weights at most `i`: it is isomorphic to
`H_c^i(X₀ ⊗ k̄, ℚ̄_ℓ)`. -/
theorem hasWeightsAtMostOver_cohomology_adicConstant (ι : PadicAlgCl l →+* ℂ) (i : ℤ) :
    ((adicConstant k₀ l X).cohomology i).HasWeightsAtMostOver k₀ ι i := by
  obtain ⟨e⟩ := WeilComplex.nonempty_equiv_compactlySupportedCohomology_cohomology
    (toComplex.obj (adicConstant k₀ l X)) i
  exact fun α hα ↦ hasWeightsAtMostOver_compactlySupportedCohomology_adicConstant k₀ l X ι i α
    (FrobeniusModule.hasEigenvalue_of_surjective e.toLinearEquiv.toLinearMap e.map_frobenius
      e.toLinearEquiv.surjective hα)

include d in
/-- Blueprint `corollary-purity-cohomology-smooth-proper-variety--1` and
`corollary-purity-cohomology-smooth-proper-variety--1` (absolute case of
`theorem-purity-higher-direct-images-under`, Step 4): for `X₀` smooth, proper and geometrically
connected of pure dimension `d`, the Frobenius module `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` is `ι`-pure of weight `i`:
every eigenvalue `α` of the geometric Frobenius satisfies `|ι α| = q^{i/2}`.

The upper bound `|ι α| ≤ q^{i/2}` is the Deligne–Laumon estimate
(`AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_adicConstant`)
transported along `H_c^i ≅ Hⁱ`; by Poincaré duality the eigenvalues in degree `2d - i` are the
`q^d / α`, and the upper bound in degree `2d - i` gives `|ι α| ≥ q^{i/2}`. -/
theorem isPureOfWeightOver_cohomology_adicConstant (ι : PadicAlgCl l →+* ℂ) (i : ℤ) :
    ((adicConstant k₀ l X).cohomology i).IsPureOfWeightOver k₀ ι i := by
  intro α hα
  refine le_antisymm (hasWeightsAtMostOver_cohomology_adicConstant k₀ l X ι i α hα) ?_
  obtain ⟨-, -, -, -, -, -, -, hrec, -⟩ := poincareDuality k₀ l X d
  have hroots := (hrec i (2 * d - i) (by ring)).2
  -- `α ≠ 0`, the Frobenius being invertible
  have hα₀ : α ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, zero_smul] at hv
    exact hv.2 (((adicConstant k₀ l X).cohomology i).frobenius.map_eq_zero_iff.1 hv.1)
  -- `q^d / α` is an eigenvalue of the Frobenius in degree `2d - i`
  have hβ : ((adicConstant k₀ l X).cohomology (2 * d - i)).frobeniusEnd.HasEigenvalue
      ((Nat.card k₀ : PadicAlgCl l) ^ d / α) := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, ← Polynomial.mem_roots
      (Polynomial.Monic.ne_zero (LinearMap.charpoly_monic _)), hroots]
    refine Multiset.mem_map_of_mem _ ?_
    rw [Polynomial.mem_roots (Polynomial.Monic.ne_zero (LinearMap.charpoly_monic _)),
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact hα
  have h := hasWeightsAtMostOver_cohomology_adicConstant k₀ l X ι (2 * d - i) _ hβ
  set Q : ℝ := (Nat.card k₀ : ℝ)
  have hQ : 0 < Q := Nat.cast_pos.2 Nat.card_pos
  have hA : 0 < ‖ι α‖ := norm_pos_iff.2 ((map_ne_zero ι).2 hα₀)
  have hb : 0 < Q ^ ((i : ℝ) / 2) := Real.rpow_pos_of_pos hQ _
  rw [map_div₀, map_pow, map_natCast, norm_div, norm_pow, Complex.norm_natCast,
    show (((2 * d - i : ℤ)) : ℝ) / 2 = (d : ℝ) + -((i : ℝ) / 2) by push_cast; ring,
    Real.rpow_add hQ, Real.rpow_natCast, Real.rpow_neg hQ.le, div_le_iff₀ hA] at h
  have key : Q ^ d * Q ^ ((i : ℝ) / 2) ≤ Q ^ d * ‖ι α‖ :=
    calc Q ^ d * Q ^ ((i : ℝ) / 2)
        ≤ Q ^ d * (Q ^ ((i : ℝ) / 2))⁻¹ * ‖ι α‖ * Q ^ ((i : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right h hb.le
      _ = Q ^ d * ‖ι α‖ := by field_simp
  exact le_of_mul_le_mul_left key (pow_pos hQ d)

include d in
/-- Blueprint `corollary-purity-cohomology-smooth-proper-variety--1`: for `X₀` smooth, proper and
geometrically connected of pure dimension `d`, for every `i`, `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` is `ι`-pure of
weight `i` and `H_c^i(X₀ ⊗ k̄, ℚ̄_ℓ)` is `ι`-mixed of weights at most `i`. -/
theorem purity_smoothProper (ι : PadicAlgCl l →+* ℂ) (i : ℤ) :
    ((adicConstant k₀ l X).cohomology i).IsPureOfWeightOver k₀ ι i ∧
      ((adicConstant k₀ l X).compactlySupportedCohomology i).HasWeightsAtMostOver k₀ ι i :=
  ⟨isPureOfWeightOver_cohomology_adicConstant k₀ l X d ι i,
    hasWeightsAtMostOver_compactlySupportedCohomology_adicConstant k₀ l X ι i⟩

include d in
/-- Blueprint `corollary-purity-cohomology-smooth-proper-variety` and
`corollary-purity-cohomology-smooth-proper-variety` (Deligne's purity theorem for smooth proper
varieties): for `X₀` smooth, proper and geometrically connected of pure dimension `d` over
`k₀ = 𝔽_q` and every `i`,

1. the constant Weil sheaf is punctually `ι`-pure of weight `0`;
2. `H_c^i(X₀ ⊗ k̄, ℚ̄_ℓ)` is `ι`-mixed of weights at most `i`;
3. `H_c^i(X₀ ⊗ k̄, ℚ̄_ℓ) ≅ Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` Frobenius-equivariantly;
4. `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` is `ι`-pure of weight `i`;
5. every eigenvalue `α` of the geometric Frobenius on `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` has
   `|ι α| = q^{i/2}`. -/
theorem deligne_purity (ι : PadicAlgCl l →+* ℂ) (i : ℤ) :
    (adicConstant k₀ l X).IsPunctuallyPureOfWeight ι 0 ∧
      ((adicConstant k₀ l X).compactlySupportedCohomology i).HasWeightsAtMostOver k₀ ι i ∧
      Nonempty (((adicConstant k₀ l X).compactlySupportedCohomology i).Equiv
        ((adicConstant k₀ l X).cohomology i)) ∧
      ((adicConstant k₀ l X).cohomology i).IsPureOfWeightOver k₀ ι i ∧
      ∀ α : PadicAlgCl l, ((adicConstant k₀ l X).cohomology i).frobeniusEnd.HasEigenvalue α →
        ‖ι α‖ = (Nat.card k₀ : ℝ) ^ ((i : ℝ) / 2) :=
  ⟨isPunctuallyPureOfWeight_adicConstant (k₀ := k₀) (l := l) (X := X) (ι := ι),
    hasWeightsAtMostOver_compactlySupportedCohomology_adicConstant k₀ l X ι i,
    WeilComplex.nonempty_equiv_compactlySupportedCohomology_cohomology _ i,
    isPureOfWeightOver_cohomology_adicConstant k₀ l X d ι i,
    isPureOfWeightOver_cohomology_adicConstant k₀ l X d ι i⟩

end WeilSheaf

end AlgebraicGeometry

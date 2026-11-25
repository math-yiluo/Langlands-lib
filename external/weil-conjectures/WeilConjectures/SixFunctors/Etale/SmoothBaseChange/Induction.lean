/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing

/-!
# The induction step in relative dimension one

For an affine smooth curve `p : X ⟶ S`, if the base-change property holds universally in
every degree `< q`, it holds universally in degree `q`. This is the point at which the two
lanes of the proof meet: a failure of the universal base-change property in degree `q` would
produce, by `AlgebraicGeometry.Etale.exists_curveTestDatum`, a curve-test datum with a
nonvanishing higher direct image, which
`AlgebraicGeometry.Etale.CurveTestDatum.isZero_higherDirectImage_constantSheaf` forbids.

Strong induction on `q`, starting from
`AlgebraicGeometry.Etale.universalBaseChangeProperty_of_neg` and
`AlgebraicGeometry.Etale.universalBaseChangeProperty_zero_of_smooth`, then gives the
base-change property universally in every degree.

## Main statements

- `AlgebraicGeometry.Etale.UniversalBaseChangeProperty.of_forall_lt`: for an affine smooth
  relative curve, the universal base-change property in all degrees `< q` implies it in
  degree `q`.
- `AlgebraicGeometry.Etale.UniversalBaseChangeProperty.forall_le_of_forall_le_sub_one`: the same
  step in cumulative form, universally in all degrees `≤ q`.
- `AlgebraicGeometry.Etale.universalBaseChangeProperty_of_smoothOfRelativeDimension_one`:
  affine smooth base change in relative dimension one, universally and in every degree.

## References

- Stacks Project, Section 59.88, <https://stacks.math.columbia.edu/tag/0F02>
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {Λ : Type (u + 1)} [CommRing Λ] {X S : Scheme.{u}} {p : X ⟶ S}

/-- Blueprint `theorem-smooth-base-change-classical-torsion`: The induction step in relative
dimension one.

Let `p : X ⟶ S` be affine smooth of relative dimension one with `X` affine, and let `n` be
invertible on `S` and annihilate the coefficient ring `Λ`. If `BC(p, Λ, q')` holds universally
(after every base change `S' ⟶ S`) for all `q' < q`, where `q ≥ 1`, then `BC(p, Λ, q)` holds
universally. The universal, cumulative hypothesis is needed: it is consumed after a
preliminary base change by
`AlgebraicGeometry.Etale.nonempty_fieldFailure_of_not_universalBaseChangeProperty`, which a
fixed-base hypothesis does not supply. The negative degrees in `∀ q' < q` are supplied by
`AlgebraicGeometry.Etale.universalBaseChangeProperty_of_neg`.

This statement is a recombination of the lemmas of Stacks, Étale Cohomology, Section 59.88
rather than a single tagged one: it is the contradiction between
`AlgebraicGeometry.Etale.exists_curveTestDatum` and
`AlgebraicGeometry.Etale.CurveTestDatum.isZero_higherDirectImage_constantSheaf`. These are the
seams of blueprint `sk-rem-seams` (`rem-seams`): the counterexample lane (Stacks 0F06, 0F07,
0F08) produces a curve-test datum with `R^q h_* (Λ/dΛ) ≠ 0`, and the curve-test lane, which uses
the field-extension invariance, the torsor translation and the spreading of Galois covers in
degree one only, makes it vanish. -/
theorem Etale.UniversalBaseChangeProperty.of_forall_lt [IsAffine X] [IsAffineHom p]
    [SmoothOfRelativeDimension 1 p] (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (hΛ : (n : Λ) = 0)
    {q : ℤ} (hq : 1 ≤ q) (hprev : ∀ q' < q, Etale.UniversalBaseChangeProperty Λ p q') :
    Etale.UniversalBaseChangeProperty Λ p q := by
  by_contra hfail
  obtain ⟨S', X', a, b, p', hpb, _, _, hnorm, _, K, _, _, i, Y, e, h, sq, d, hd, hne⟩ :=
    Etale.exists_isPullback_not_isZero_higherDirectImage Λ p n hn hΛ q hq hprev hfail
  -- the base change `p'` is again an affine smooth relative curve, and `d` is invertible on `S'`
  have : IsAffineHom p' := MorphismProperty.of_isPullback hpb inferInstance
  have : SmoothOfRelativeDimension 1 p' :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback hpb inferInstance
  have hd' : IsUnit (d : Γ(S', ⊤)) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) (by simpa using hn.map a.appTop.hom)
  exact hne (Etale.CurveTestDatum.isZero_higherDirectImage_constantSheaf Λ
    ⟨S', hnorm, X', p', K, i, Y, e, h, sq, d, hd'⟩ q hq)

/-- Blueprint `theorem-smooth-base-change-classical-torsion`: The induction step in relative
dimension one, cumulative form.

Let `p : X ⟶ S` be affine smooth of relative dimension one with `X` affine, and let `n` be
invertible on `S` and annihilate `Λ`. If, for some `q ≥ 1`, `BC(p, Λ, q')` holds universally for
all `q' ≤ q - 1`, then `BC(p, Λ, q')` holds universally for all `q' ≤ q`. The new degree `q` is
`AlgebraicGeometry.Etale.UniversalBaseChangeProperty.of_forall_lt`. -/
theorem Etale.UniversalBaseChangeProperty.forall_le_of_forall_le_sub_one [IsAffine X]
    [IsAffineHom p] [SmoothOfRelativeDimension 1 p] (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤)))
    (hΛ : (n : Λ) = 0) {q : ℤ} (hq : 1 ≤ q)
    (hprev : ∀ q' ≤ q - 1, Etale.UniversalBaseChangeProperty Λ p q') :
    ∀ q' ≤ q, Etale.UniversalBaseChangeProperty Λ p q' := by
  intro q' hq'
  rcases hq'.lt_or_eq with h | rfl
  · exact hprev q' (by omega)
  · exact Etale.UniversalBaseChangeProperty.of_forall_lt n hn hΛ hq fun q'' h ↦
      hprev q'' (by omega)

/-- Affine smooth base change in relative dimension one: for `p : X ⟶ S` affine smooth of
relative dimension one with `X` affine, and `n` invertible on `S` and annihilating `Λ`,
`BC(p, Λ, q)` holds universally in every degree `q`. This is strong induction on `q` with
step `AlgebraicGeometry.Etale.UniversalBaseChangeProperty.of_forall_lt`, starting from the
negative degrees and degree zero. -/
theorem Etale.universalBaseChangeProperty_of_smoothOfRelativeDimension_one [IsAffine X]
    [IsAffineHom p] [SmoothOfRelativeDimension 1 p] (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤)))
    (hΛ : (n : Λ) = 0) (q : ℤ) :
    Etale.UniversalBaseChangeProperty Λ p q := by
  have key : ∀ m : ℕ, ∀ q' < (m : ℤ), Etale.UniversalBaseChangeProperty Λ p q' := by
    intro m
    induction m with
    | zero => exact fun q' hq' ↦ Etale.universalBaseChangeProperty_of_neg Λ p hq'
    | succ m ih =>
      intro q' hq'
      rcases lt_or_eq_of_le (show q' ≤ m by omega) with h | rfl
      · exact ih q' h
      · rcases Nat.eq_zero_or_pos m with rfl | hm
        · have := SmoothOfRelativeDimension.smooth 1 p
          exact Etale.universalBaseChangeProperty_zero_of_smooth Λ p
        · exact Etale.UniversalBaseChangeProperty.of_forall_lt n hn hΛ (by omega) ih
  exact key (q.toNat + 1) q (by omega)

end AlgebraicGeometry

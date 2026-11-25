/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.FieldFailure
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition

/-!
# A failure of base change is detected over a field

If `BC(p, Λ, q')` holds universally for all `q' < q` but `BC(p, Λ, q)` fails, then the
failure is already visible after base change to an affine open `S' ⊆ S` and over a field:
there is a Cartesian square whose base is the spectrum of a field and a sheaf of `Λ`-modules
on it for which the degree-`q` base-change map is not an isomorphism. The data of such a
counterexample is bundled as `AlgebraicGeometry.Etale.FieldFailure`.

The proof applies `AlgebraicGeometry.exists_spec_field_of_isQcqsLocalProperty` to the
property "the chosen cokernel element survives",
`AlgebraicGeometry.Etale.SurvivesBaseChange`: an element `ξ` of a geometric stalk of
`R^q h_* e⁻¹ F` not in the image of the base-change map is transported along `π : T' ⟶ T` by
the transition maps `AlgebraicGeometry.Etale.baseChangeTargetTransition`, and the property
asks that its image is still not in the image of the base-change map over `T'`. The four
hypotheses of the minimal-counterexample lemma are verified separately: invariance under
thickenings, compatibility with limits, the closed–open splitting (which is where
`AlgebraicGeometry.Etale.mono_cokernelMap` and `AlgebraicGeometry.Etale.mono_cokernelDesc`
enter) and the failure over the empty scheme.

The material is split into
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.FieldFailure` (the
counterexample datum), `...FailureOverField.Transition` (the transition maps),
`...FailureOverField.Survival` (the survival property and the hypotheses of the
minimal-counterexample lemma) and `...FailureOverField.Detection` (the main statements); this
module imports all of them.

## Main definitions

- `AlgebraicGeometry.Etale.FieldFailure`: a counterexample to `BC(p, Λ, q)` living over a
  field, after an affine base change of `p`.
- `AlgebraicGeometry.Etale.baseChangeTargetTransition`: the map relating the targets of the
  base-change maps over `T` and over `T'`, for `π : T' ⟶ T`.
- `AlgebraicGeometry.Etale.SurvivesBaseChange`: the property "the chosen cokernel element
  survives" of schemes over `T`.

## Main statements

- `AlgebraicGeometry.Etale.isQcqsLocalProperty_survivesBaseChange`: that property satisfies
  the hypotheses of the minimal-counterexample lemma.
- `AlgebraicGeometry.Etale.nonempty_fieldFailure`: if `BC(p, Λ, q')` holds universally for
  `q' < q` and `BC(p, Λ, q)` fails, a counterexample over a field exists.
- `AlgebraicGeometry.Etale.nonempty_fieldFailure_of_not_universalBaseChangeProperty`: the same
  conclusion when `BC(p, Λ, q)` only fails after some base change, as in the blueprint.
- `AlgebraicGeometry.Etale.FieldFailure.isAffineHom_a`: if `S` is separated, the base change
  `S' ⟶ S` of such a counterexample is affine.

## References

- Stacks Project, Lemma 59.88.6, <https://stacks.math.columbia.edu/tag/0F07>
-/

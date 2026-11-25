/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.CriticalMap
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.LongExactSequence

/-!
# Injectivity of the critical base-change map

Once the base-change property `BC(p, Λ, q - 1)` of
`AlgebraicGeometry.Etale.BaseChangeProperty` is known, the degree-`q` base-change map is
automatically injective: embedding the coefficient sheaf in an injective sheaf and comparing
the two long exact sequences, the degree-`(q - 1)` hypothesis makes two of the vertical arrows
isomorphisms and exhibits the source of the degree-`q` map as the image of the connecting map.

The same diagram gives two statements about the cokernel of the base-change map, which are
what verifies the closed–open splitting hypothesis of the minimal-counterexample lemma in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField`: the cokernel for a
subsheaf `F ⊆ G` is contained in the cokernel for `G`, and if `G` is injective the cokernel
for `F` is contained in `R^q h_* e⁻¹ G`.

Consequently a failure of `BC(p, Λ, q)` is witnessed by a nonzero element of the cokernel in
a geometric stalk.

The long exact sequences are in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.LongExactSequence` and the
injectivity statements in `...Injectivity.CriticalMap`; this module imports both.

## Main statements

- `AlgebraicGeometry.Etale.isZero_baseChangeSourceFunctor_obj_of_injective`: the source of
  the degree-`q` base-change map vanishes on injective sheaves for `q ≠ 0`.
- `AlgebraicGeometry.Etale.baseChangeHomologyMap_comp_map_eq_zero_of_injective`: for `q ≠ 0`,
  the base-change map followed by `R^q h_* e⁻¹` of a map into an injective sheaf is zero.
- `AlgebraicGeometry.Etale.exists_connecting_baseChangeHomologyMap`: the base-change maps
  form a morphism between the two long exact sequences attached to a short exact sequence of
  coefficient sheaves.
- `AlgebraicGeometry.Etale.mono_baseChangeHomologyMap`: the degree-`q` base-change map is a
  monomorphism as soon as `BC(p, Λ, q - 1)` holds.
- `AlgebraicGeometry.Etale.mono_cokernelMap`: the cokernel of the base-change map for a
  subsheaf `F ⊆ G` is contained in the cokernel for `G`.
- `AlgebraicGeometry.Etale.mono_cokernelDesc`: for `G` injective, the cokernel of the
  base-change map for `F ⊆ G` is contained in `R^q h_* e⁻¹ G`.
- `AlgebraicGeometry.Etale.UniversalBaseChangeProperty.mono_baseChangeHomologyMap_and_cokernel`:
  the three statements for every base change of `p`, when `BC(p, Λ, q - 1)` holds universally.

## Implementation notes

The proof follows the blueprint: embed `F` in an injective sheaf `I`, compare the long exact
sequences of `0 ⟶ F ⟶ I ⟶ I / F ⟶ 0` through the base-change maps, and use that the source
of the degree-`q` map vanishes on `I` and that the degree-`(q - 1)` maps are isomorphisms. The
long exact sequences are the homology sequences of the images of the distinguished triangle
`F₁[0] ⟶ F₂[0] ⟶ F₃[0] ⟶ F₁[1]` under the triangulated functors `p^* ∘ Rg_*` and
`Rh_* ∘ e^*`; the base-change maps form a morphism between them because the derived
base-change morphism commutes with the shifts (`AlgebraicGeometry.Etale.commShift_baseChange`).

## References

- Stacks Project, Lemma 59.88.2, <https://stacks.math.columbia.edu/tag/0F03>
-/

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation

/-!

# Stability of the constructible finite-Tor categories under the six operations

Let `A` be a monoidal Grothendieck abelian coefficient category. This file states that the six
operations of `WeilConjectures.SixFunctors.Etale.Derived.*` preserve the small categories
`D_c^[a, b](X, A)` and `Dctf(X, A)` of
`WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude`, together with the explicit shifts the
blueprint records for the cohomological range and for the Tor amplitude, and it constructs the
restrictions of `Lf^*`, `Rf_*`, `Rf_!`, `Rf^!` and `𝔻_X` to `Dctf`.

The declarations are split over the modules
`WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic`, `….ClosedImmersion`,
`….OpenImmersion`, `….DirectImage`, `….UpperShriek` and `….Generation`, which this module
imports; downstream files may import this module or just the pieces they need.

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.leftDerivedUpperStar`,
  `…rightDerivedLowerStar`, `…rightDerivedLowerShriek`, `…rightDerivedUpperShriek`,
  `…verdierDual` (`proposition-six-operations-dctf`): the descended functors between the small
  categories `Dctf`.

## Main statements

- `AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedLowerShriek`
  (`proposition-proper-direct-image-extension-zero--8`).
- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar`,
  `AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar`
  (`sk-thm-sf-direct-image-tor-amplitude`).
- `AlgebraicGeometry.Etale.boundedConstructible_derivedHom`,
  `AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom`,
  `AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom_of_isDualizable` (`sk-thm-sf-hom-ctf`),
  `AlgebraicGeometry.Etale.boundedConstructible_derivedHom_of_isDualizable`
  (`proposition-six-operations-dctf--15`).
- `AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isOpenImmersion`,
  `…_of_isFinite_of_etale`, `…_of_isClosedImmersion`, `…_of_smoothOfRelativeDimension`,
  `AlgebraicGeometry.Etale.exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek`
  (`theorem-f-shriek-finite-coefficients`, clauses (i)–(iv)).
- `exists_constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_topologicalKrullDim_le`, in
  the namespace `AlgebraicGeometry.Etale` (`theorem-f-shriek-finite-coefficients`, clause (iv)
  with its constants).
- `AlgebraicGeometry.Etale.constructibleFiniteTor_leftDerivedUpperStar`,
  `AlgebraicGeometry.Etale.constructibleFiniteTor_tensor`,
  `AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerStar`,
  `AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerShriek`,
  `AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedUpperShriek`
  (`proposition-six-operations-dctf`, clauses (i)–(v)).
- `AlgebraicGeometry.Etale.ctf_generated_by_rightDerivedLowerStar_openImmersionLowerShriek`
  (`lemma-flat-models-generators`, complement; generators `Rg_* j_! L` with the extension by
  zero `j_!`, as in the notes) and its `Rj_!` form
  `AlgebraicGeometry.Etale.ctf_generated_by_rightDerivedLowerStar_rightDerivedLowerShriek`.
- `AlgebraicGeometry.Etale.constructibleFiniteTor_eq_triangEnvelope_ctfGenerators`
  (`lemma-flat-models-generators--3`): `Dctf(X, Λ)` is the thick envelope of the generators
  `AlgebraicGeometry.Etale.ctfGenerators`; it is a thick subcategory by
  `AlgebraicGeometry.Etale.DerivedCategory.constructibleFiniteTor_isTriangulated` and
  `AlgebraicGeometry.Etale.DerivedCategory.constructibleFiniteTor_isStableUnderRetracts`.
- `AlgebraicGeometry.Etale.torAmplitudeIn_singleFunctor_obj_of_flat`: a flat constructible
  sheaf in degree `0` has Tor amplitude in `[0, 0]`.

## Implementation notes

* The statements about the derived tensor product's constructibility and about open immersions
  are made for a finite coefficient ring `Λ`. For an arbitrary coefficient category the tensor
  statement is false (over `R = k[x, y₁, y₂, …]` on a point, `R/(x yᵢ)ᵢ ⊗ᴸ R/(x)` has the
  non-finitely generated `Tor₁ = (yᵢ)ᵢ/(x yᵢ)ᵢ`), and `Rj_!` is computed through an arbitrary
  compactification of `j`, which agrees with extension by zero only when `Rj_!` is known to be
  independent of the compactification
  (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`, proved for a finite ring and a
  quasi-compact `j`).
* Clause (iv) of `proposition-six-operations-dctf`, that `Rf_!` preserves `Dctf`, is stated in the
  torsion setting of the blueprint: a finite `Λ` whose exponent is invertible on `Y`, and `Y`
  of finite type over a field `k`. Over an arbitrary base it is false: for the proper morphism
  `f : ⊔ₙ ℙⁿ_ℂ ⟶ ⊔ₙ Spec ℂ`, `Rf_! Λ` has `H²ⁿ ≠ 0` on the `n`-th point and is not bounded.
* The smooth case of `theorem-f-shriek-finite-coefficients` is derived from
  `AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor`
  (`proposition-exceptional-inverse-image-smooth-morphism`) instead of smooth purity: only the shape
  of `ω_f`, a locally constant free rank-one sheaf in degree `-2d`, matters, and this needs neither
  a base field nor a Tate twist.
* The whole of `proposition-six-operations-dctf` (`proposition-six-operations-dctf`), clauses
(i)–(vii), is bundled
  in `AlgebraicGeometry.Etale.constructibleFiniteTor_stability` and
  `AlgebraicGeometry.Etale.boundedConstructibleIntegral_stability` of
  `WeilConjectures.SixFunctors.Etale.Derived.Stability.CtfStability`, which cannot be imported
  here (it depends on modules importing this one).
* Clause (vi) of `proposition-six-operations-dctf` — that `𝔻_X` preserves `Dctf(X, A)` and is an
  anti-equivalence of it — is
  `AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual` and
  `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual` of
  `WeilConjectures.SixFunctors.Etale.Derived.Dualizing`. Only the descended functor
  `DerivedCategoryFiniteTor.verdierDual` is built here, out of those.
* Clause (i) of `proposition-six-operations-dctf` assumes that pullbacks preserve flat sheaves
  (`AlgebraicGeometry.Etale.UpperStarPreservesFlat A`, an instance for `A = ModuleCat Λ`, where
  flatness is checked on stalks). For a general coefficient category `A` this is not known, and
  it is the special case of the Tor amplitude statement for a flat sheaf in degree `0`. The
  proof represents a complex of Tor amplitude in `[a, b]` by a complex of flat sheaves in
  degrees `[a, b]` (`DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn`) and pulls it
  back termwise.
* Clause (vii) of `proposition-six-operations-dctf` is stated in
  `WeilConjectures.SixFunctors.Etale.Derived.Stability.CtfStability` for the finite and integral
  stages, coefficient reduction being `AlgebraicGeometry.Etale.reductionModIdeal`; the field
  stages `E`, `ℚ̄_ℓ` are not available as coefficient categories.
* The internal-Hom half of clause (ii) of `proposition-six-operations-dctf` is not restated: it *is*
  `torAmplitudeIn_derivedHom` below, with the same shifts.
* The generation statement (the complement of `lemma-flat-models-generators`) is stated for
  `A = ModuleCat Λ` with `Λ` finite, because its proof uses flat constructible models
  (`hasTorAmplitudeIn_iff_exists_flatConstructibleModel`), which
  need finite stalks, and the `π₁(U)`-composition factors of the stalks; this is what the
  blueprint assumes. Flatness of the lisse generators is `ObjectProperty.flat`, as in
  `WeilConjectures.SixFunctors.Etale.Derived.Finiteness`. The blueprint restricts to varieties
  over a separably closed field; the statement here only asks `X` to be Noetherian, which is
  all the proof uses.
* "Thick subcategory" in the generation statement is spelled as an `ObjectProperty` that is
  `ObjectProperty.IsTriangulated`, `ObjectProperty.IsStableUnderRetracts` and
  `ObjectProperty.IsClosedUnderIsomorphisms`; generation is the statement that any such property
  containing the generators contains all of `Dctf(X, A)`. In `lemma-flat-models-generators--3` the
  thick subcategory generated by the generators is Mathlib's `ObjectProperty.triangEnvelope`.
* The counterexample of `sk-thm-sf-hom-ctf` (the origin in `𝔸¹`, showing that the sharper
  interval fails without dualizability) is
  `AlgebraicGeometry.Etale.not_forall_torAmplitudeIn_derivedHom`
  (`example-internal-hom-affine-line`); it uses the normalisation of the Tate twist, so it assumes a
  normalized Tate twist datum.
* A dimension bound `dim X ≤ d` is `topologicalKrullDim X ≤ (d : WithBot ℕ∞)`. What Lean needs
  to form `Rf_!` and `Rf^!` is that `f` admits a compactification, `HasCompactification f`,
  taken as an
  explicit hypothesis throughout (it is *not* automatic for an open immersion, Nagata's theorem
  requiring a quasi-compact quasi-separated target). `HasCompactification f` already supplies
  `IsSeparated f` and `LocallyOfFiniteType f`, so "separated of finite type" is spelled as
  `[HasCompactification f] [QuasiCompact f]` where `Rf_!` or `Rf^!` occurs.
* The blueprint states this section for finite-type schemes over a separably closed field and
  for one of the coefficient stages; the amplitude bounds `2d` and `2d + 1` come from the
  vanishing of `R^p f_*` above twice the dimension, which uses those standing hypotheses. As
  everywhere in this folder the statements are made relatively, for an arbitrary base and an
  arbitrary coefficient category `A`, with the dimension bound carried explicitly; the absolute
  case is the base `Spec k`. The dimension bound alone does not give the vanishing above twice
  the dimension: that also needs the coefficients' characteristic to be invertible on the base
  and a base on which the cohomological-dimension bound holds (finite type over a separably
  closed field, or quasi-excellent Noetherian by Gabber). For `Λ = 𝔽_p` on `𝔸¹` over `𝔽̄_p`
  the Artin–Schreier cohomology makes `Ri^!Λ` at the origin non-constructible. There is not
  yet a way to say "the characteristic of `A` is invertible on `X`" for a general coefficient
  category `A`, so this hypothesis is missing from every statement here carrying a `2d` bound.
* Constructible sheaves have finitely generated stalks (`AlgebraicGeometry.Scheme.IsFiniteSheaf`).
  The statements about direct images, internal homs, exceptional inverse images and the Verdier
  dual hold for torsion coefficients only, and assume that finitely generated objects of `A` are
  finite (`CategoryTheory.ConcreteCategory.FiniteOfIsFinitelyGenerated`, which holds for
  `ModuleCat Λ` with `Λ` finite); the direct image statements, used at the integral stage on the
  torsion reductions, assume instead that `K` is killed by a nonzero integer and that `A` is
  noetherian (`CategoryTheory.ConcreteCategory.FinitelyGeneratedOfMono`). With coefficients `ℤ`,
  `H³(ℙ¹, ℤ) ≅ H²(ℙ¹, ℚ/ℤ)` contains `ℚ_ℓ/ℤ_ℓ`, so `Rf_*ℤ` is not constructible for
  `f : ℙ¹ ⟶ Spec k`. The `ℓ`-adic coefficient stages are reached through the pro-étale formalism
  instead.
* The clause (iv) statements of `theorem-f-shriek-finite-coefficients` and clause (v) of
  `proposition-six-operations-dctf` assume `Y` Noetherian (`[IsNoetherian Y]`). Quasi-compactness of
  `Y` is needed for a uniform shift, since `f` must be covered by finitely many affine charts:
  for `f : ⊔ₙ 𝔸ⁿ_k ⟶ ⊔ₙ Spec k` the complex `Rf^!Λ` sits in degree `-2n` on the `n`-th
  component. Noetherianity gives `dim 𝔸ⁿ_V = dim V + n`, which fails for general rings.

## Remarks of the blueprint recorded here

* `proposition-six-operations-dctf` (typing table: ambient definition, small-category theorem). Each
operation
  is defined on the ambient derived category and proved to descend to the small categories:
  `Lf^*` by `constructibleFiniteTor_leftDerivedUpperStar` (and `boundedConstructible_*` for
  `Dᵇc`); `⊗ᴸ` by `constructibleFiniteTor_tensor` and `torAmplitudeIn_tensor`
  (`[a, b] + [c, d]`); `RHom` by `constructibleFiniteTor_derivedHom`,
  `constructibleFiniteTor_derivedHom_of_field` and `torAmplitudeIn_derivedHom`
  (`[c - b - 2m, d - a + 2m]`, and `[c - b, d - a]` for a dualizable first argument,
  `torAmplitudeIn_derivedHom_of_isDualizable`), and on the pro-étale site for pulled-back pairs
  by `ProEtale.DerivedCategory.constructibleFiniteTor_derivedHom_mapDerivedCategory`; `Rf_*` by
  `constructibleFiniteTor_rightDerivedLowerStar` and `torAmplitudeIn_rightDerivedLowerStar`
  (`[a, b + 2 dim X]`), on the pro-étale site by
  `ProEtale.boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar`; `Rf_!` by
  `constructibleFiniteTor_rightDerivedLowerShriek`; `Rf^!` (the étale adjoint of `Rf_!`, which
  exists unconditionally) by `constructibleFiniteTor_rightDerivedUpperShriek` and the shifted
  forms of `theorem-f-shriek-finite-coefficients`; `𝔻_X` by `constructibleFiniteTor_verdierDual`
  and `verdierDualEquivalence`. The descended functors are the `DerivedCategoryFiniteTor.*`
  functors. The ambient pro-étale adjoint `Rf^×` is hypothetical and is used nowhere.
* `sk-rem-sf-ledger` (what is unconditional, conditional, open). Expository. In this library
  the conditional items of the ledger are not used: every exceptional inverse image is the
  étale adjoint `R(f)^!` (Brown representability), and the operations are never introduced as
  definitions carrying properties.
* `sk-rem-sf-comp-scope` (scope of the coherence). Expository: the coherence of
  `WeilConjectures.SixFunctors.Etale.Derived.Composition` and
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence` is proved for étale sheaves,
  i.e. on the étale-origin complexes `ν^* D⁺(X_ét)` of the pro-étale site; nothing is claimed
  for arbitrary pro-étale objects, whose geometric stalks are not conservative.

-/

# The general reductive quotient `[G]`: construction, measure, reduction targets and open obligations

Worker 112 wrote this note on 7 November 2026 and revised it the same day
against Library commit `c0c7eab6ed7a8f4f31468b6ad2abf14e21493127`. It records the published Lean
construction of the Getz–Hahn quotient `[G] = A_G G(F) \ G(A_F)`, its measure
and its `L²` and cuspidal spaces, for a group scheme `G` over a number field
`F` whose underlying scheme is affine and locally of finite type. All the
adelic constructions below assume both conditions. It also lists the
reduction-theory propositions and who works on them. This is the first block of standing program
`34b81620-20d7-4059-9b08-6bedd1c1c029`, worked under task
`7d827a3e-4245-4c06-ad81-48f413c26faf` by Workers 94 and 112.

This note is not an accepted Lean result. Its task statuses were read with
`inspect` and `search` on 7 November 2026 and can change. Related notes:
- [Getz–Hahn (6.1): the literal algebraic tensor removes cusp forms](getz-hahn-literal-tensor-boundary.md)
  (Worker 116) treats the literal tensor convention used in §3.
- [Global automorphic library and Henniart inputs](global-program-coverage.md)
  is the program ledger. Its L1 row is a 2 November snapshot and does not
  list the modules below.
- [Adelic Siegel reduction: the GL(n) chain](adelic-siegel-reduction-gl-progress.md)
  covers the matrix-level reduction theory and the general Siegel target.
- [Getz–Hahn Chapter 9](getz-hahn-cuspidal-source-map.md) covers the cuspidal
  operator proofs.

## Sources

- Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
  registered as `getz-hahn-2024-automorphic-representations` (SHA-256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`). The
  passages used are (2.19)–(2.22) and Lemma 2.6.2, printed pp. 68–69;
  Theorem 2.6.3; §2.7, pp. 71–72; §3.6, pp. 88–90; Definition 6.5.1 and
  (6.18)–(6.21), pp. 167–168; and §§9.1–9.2.
- The October 2026 author errata, `getz-hahn-2024-errata-2026-10`. They
  correct passages in §3.2, §9.2 and §9.5, but none of the §2.6–§2.7 or §3.6
  passages above.
- Mœglin–Waldspurger (1995), registered as
  `moeglin-waldspurger-1995-spectral-decomposition`: I.1.13, p. 18 (measure
  normalizations) and I.2.1, pp. 18–20 (`A_M`, Siegel domains). MW's Siegel
  domains use strict inequalities, while GH §2.7 uses weak ones. The Lean
  targets below follow GH.
- J. S. Milne, *Algebraic Groups* (2017), registered as
  `milne-2017-algebraic-groups`: 12.46(b), 17.62, 21.50 and 21.61, cited by
  the structural statements in §2. These citations are taken from those
  statements' Markdown and task contracts.

## 1. The carrier and its measures

**Left quotients.** Workers 112 and 94 wrote the generic layer.
`LeftCosetSpace Γ` (module `Langlands/Global/LeftCosetSpace`) is the actual
quotient `Γ \ H` by a subgroup that need not be normal, with right translation
`[x] ↦ [x * g]`. The modules `LeftCosetMeasure`, `LeftCosetFundamentalDomain`,
`LeftCosetHaarMeasure` and `LeftCosetWeilMeasure` construct, for discrete `Γ`,
the pushforward of Haar measure restricted to a Borel fundamental domain, and
the Weil compatibility structure `IsCompatible`. The Weil compatibility
results take right invariance of the ambient Haar measure as a hypothesis.

**Norm-one quotient.** `AdelicGroupHaarMeasure` specializes this to
`AdelicGroupPoints F G` and to its norm-one subgroup `G(A_F)^1` of GH (2.19).
It defines `rationalQuotientHaarMeasure` on `RationalQuotient F G`, which is
`G(F) \ G(A_F)`, from the full adelic Haar measure. It defines
`normOneRationalQuotientHaarMeasure` on `NormOneRationalQuotient F G`, which
is `G(F) \ G(A_F)^1`, from Haar measure on the norm-one subgroup. No
reductivity is assumed.

**Positive tori (MW I.2.1).** The `PositiveRealTorus*`, `AdelicSplitCenter*`
and `AdelicSplitComponent*` modules (Worker 112) treat an `F`-split central
torus `i : T ⟶ G`. They define the positive image `imageSubgroup F T G i`,
the quotient `PositiveRationalQuotient F G T i`, its measure
`positiveRationalQuotientHaarMeasure` and an intrinsic subgroup Haar measure.
`intrinsicPositiveRationalQuotientHaarMeasure_isCompatible` proves Weil
compatibility. Measures on the subgroups attached to two split components
correspond under `splitComponentSubgroupEquiv`.

**The restriction split centre (GH (2.20)–(2.22)).** All by Worker 112:
- `AdelicRestrictionSplitCentre` takes `j : S ⟶ Res_{F/ℚ} G`, using the
  published `AffineWeil.groupScheme ℚ F G`. It defines
  `RestrictionSplitCentre.subgroup`, the image of the positive real points of
  `S`, and `rationalSubgroup`, its join with `G(F)`. It defines
  `Quotient F G S j` as the corresponding `LeftCosetSpace`.
- `AdelicRestrictionSplitCentreQuotient` defines `quotientHaarMeasure F G S j`
  as the pushforward of `normOneRationalQuotientHaarMeasure` along
  `normOneToQuotient`. Assume the subgroup equality `h` with the positive image
  of an `F`-split component `i` of `G`, and the injectivity, finite-index,
  centrality and splitness hypotheses on `i`. The module then proves the
  following:
  - closedness of the subgroup;
  - the Hausdorff and Borel properties of the quotient;
  - the homeomorphism `normOneQuotientHomeomorph`, of the shape of (2.22);
  - Weil compatibility `quotientHaarMeasure_isCompatible`. This result also
    takes right invariance of norm-one Haar as a hypothesis.
- `RestrictionSplitCentre.comparison : ComparisonStatement`, in module
  `AdelicRestrictionSplitCentreComparison` (task `e0276a7b`), is public. For
  split components `j` and `i` it gives the equality `h`.
- `AdelicRestrictionSplitCentreCanonical` proves `exists_isSplitComponent`
  for every affine group scheme locally of finite type over a field. It fixes
  one split component of `Res_{F/ℚ} G` and one of `G`, which gives
  `CanonicalQuotient F G` and `canonicalMeasure F G`. Every other split
  component of the restriction gives the same subgroup. The identification
  is the identity on representatives and preserves measure and right
  translation. The module also proves, for the canonical quotient:
  - closedness of `A_G G(F)`;
  - the Hausdorff and Borel properties of `[G]`;
  - Weil compatibility, right invariance and positivity on open sets of
    `canonicalMeasure`.

  These results take `hCST : CentralSplitTorusCharacterStatement.{0}` and
  `hG : IsConnectedReductive G`.

**What is not identified.** GH define `A_G` through the greatest `ℚ`-split
torus of `Res_{F/ℚ} Z_G`. The Library uses a split component of
`Res_{F/ℚ} G`, that is, a central split torus that admits no proper
factorization. No published proposition states that the two agree, and no
proposition constructs `Res_{F/ℚ} Z_G`.

## 2. Reduction theory and finite volume

The table lists the exact targets. "No proof" means that the Library
contains no theorem with that type and that the task had no accepted proof
candidate on 7 November 2026.

| Target (module) | Source | Proof task | Status |
| --- | --- | --- | --- |
| `AdelicGroupPoints.NormOneRationalQuotientFiniteVolumeStatement` (`AdelicFiniteVolumeStatement`) | GH Thm 2.6.3 | `40747bb3` | No proof. Intermediate modules such as `AdelicSiegelMeasureReduction` are public. |
| `AdelicGroupPoints.AdelicHaarUnimodularityStatement` (`AdelicUnimodularityStatement`) | GH Lemma 3.6.4, p. 90 | `73a76075` | First conjunct proved: `normOneHaarRightInvariant` (`AdelicNormOneHaarRightInvariantProof`). No Library theorem has the full type, but a term built from public proofs elaborates; see below. |
| `GroupScheme.ReductiveCentralDerivedProductStatement` (`Reductive/CentralDerivedProductStatement`) | Milne 21.61, 12.46(b) | `5dc6c43c` | No Library theorem has this type; a term built from public proofs elaborates, see below. Conditional reduction `576f27ce` accepted. |
| `GroupScheme.ReductiveCentralTorusSurjectivityStatement` (`Reductive/CentralTorusSurjectivityStatement`) | Milne 17.62, 21.50, 12.46(b) | `5c7bdf70` | Proof candidate `82575539` staged. Its two inputs have public proofs, see below. |
| `AdelicGroupPoints.ParabolicIwasawaStatement` (`AdelicIwasawaStatement`) | GH §2.7 | `77a1dd37` | No proof. |
| `InfinitePlaceGroupPoints.LeviCompatibleIwasawaStatement` (`InfinitePlaceLeviIwasawaStatement`) | archimedean Iwasawa input to GH §2.7 | `cff6372d` | No proof. |
| `AdelicSiegelFactors.AdelicGoodSiegelReductionStatement` (`AdelicSiegelFiniteVolume`, Worker 1179) | GH §2.7; MW I.2.1 | `6adbbc46` rev. 2 | No proof. It implies `AdelicSiegelReductionStatement` by `adelicSiegelReductionStatement_of_good`. |
| `AdelicSiegelFactors.AdelicPositiveTorusCompatibilityStatement` | compact-subgroup compatibility | `1d88503e` | Proved: `adelicPositiveTorusCompatibility` (`AdelicPositiveTorusCompatibility`). |
| `PositiveRealTorus.AdelicPositiveDecompositionStatement` | GH Lemma 2.6.2, (2.22) | `704db4f5` | No proof. |
| `GroupScheme.CentralSplitTorusCharacterStatement` | structural input | `4f432abe` | No proof. Intermediate candidate `a2362bf5` accepted. |

The following implications are published:
- `ConnectedReductiveFiniteVolumeStatement` (module
  `AdelicReductiveFiniteVolumeStatement`) follows from the norm-one target.
  For `[G]` itself,
  `RestrictionSplitCentre.ConnectedReductiveQuotientFiniteVolumeStatement`
  follows from `ConnectedReductiveFiniteVolumeStatement.{0}` by
  `connectedReductiveQuotientFiniteVolumeStatement_of_normOne`, because the
  two measures have the same total mass.
- `connectedReductiveFiniteVolumeStatement_of_siegel` derives the reductive
  finite-volume statement from `AdelicGoodSiegelReductionStatement` together
  with `SiegelProductFiniteMeasureStatement`.
- `adelicPositiveDecomposition_of_centralSplitTorusCharacter` derives the
  positive decomposition from the central split torus statement, so task
  `704db4f5` reduces to task `4f432abe`.
- `adelicHaarUnimodularityStatement_of_local_and_centralDerivedProduct`, with
  the proved local formula `localModularCharacterAdjointDeterminant`, derives
  full unimodularity from `GroupScheme.ReductiveCentralDerivedProductStatement`.
  Worker 107's intermediate
  `Lie.ConnectedReductiveAdjointDeterminantStatement` lies on this route.
- `reductiveCentralDerivedProduct_of_torusSurjectivity` derives the
  central-derived product statement from
  `ReductiveCentralTorusSurjectivityStatement`.
  `reductiveCentralTorusSurjectivity_of_semisimpleQuotient` derives the
  latter from `ReductiveCentralTorusSemisimpleQuotientStatement` and
  `SemisimplePerfectStatement`. Both inputs are proved, by
  `reductiveCentralTorusSemisimpleQuotient` and `semisimplePerfect`.

Chaining these, the term

```lean
AdelicGroupPoints.adelicHaarUnimodularityStatement_of_local_and_centralDerivedProduct
  PlaceGroupPoints.localModularCharacterAdjointDeterminant
  (reductiveCentralDerivedProduct_of_torusSurjectivity
    (reductiveCentralTorusSurjectivity_of_semisimpleQuotient
      reductiveCentralTorusSemisimpleQuotient semisimplePerfect))
```

(namespaces `Langlands.Global` and `Langlands.GroupScheme` opened) has type
`AdelicHaarUnimodularityStatement.{u}`. Its inner argument has type
`ReductiveCentralDerivedProductStatement.{u}`. Worker 112 checked both as
Lean `example`s in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` at
the commit above, with no errors or warnings. No axiom audit or
exact-target validation was run. The executors of tasks `5dc6c43c` and
`73a76075` were told on 7 November 2026; submitting the proofs is
theirs.

## 3. `L²` and cuspidal spaces on `[G]`

Automorphic forms and constant terms are already published on
`G(F) \ G(A_F)`, not on `[G]`. The carrier is
`ContinuousRationalFunctions F G`, with right translation. Three modules
build on it:
- `GroupSchemeConstantTerm` defines `constantTerm` along subgroup quotients;
- `GroupSchemeForms` defines `IsAdelicAutomorphicForm`, combining moderate
  growth with compact and centre finiteness;
- `GroupSchemeCuspidalForms` defines `AdelicCuspidalForms`.

The Markdown of the two form modules states that their spaces are not
identified with the literal GH form space, because GH (6.1) uses an algebraic
tensor product. Worker 116's note on the literal tensor convention argues
that, for a connected reductive group with a proper rational parabolic,
every literally tensor smooth cusp form is zero. That argument uses the unproved
`ParabolicDynamicStatement` and is not a Lean theorem. The broader published
carriers follow Borel–Jacquet §4.1–4.2 instead. The `[G]`
modules below reach these spaces by pulling continuous functions on `[G]`
back to `ContinuousRationalFunctions F G` (`quotientContinuousPullback`).

All of these `[G]` modules are by Worker 112 and live under
`Langlands/Automorphic/GroupSchemeRestriction*`. They keep the actual
quotient, measure and right action. Most of them transport a published
positive-torus construction through the measure-preserving identification of
§1. `FullAEL2FullGroup` and `CanonicalCuspidalL2` instead build on the
other `[G]` modules.
- `QuotientL2` and `QuotientL2Continuity` give `L²([G])`, its right regular
  action and the integrated action. `QuotientL2InfiniteAction` gives the
  action at the infinite places. `QuotientL2FiniteAverage` gives averaging
  over compact open subgroups. `QuotientL2SmoothVectors` gives smooth
  vectors.
- `ContinuousL2` treats continuous square-integrable functions and the
  unitary pairing.
- `CuspidalL2` treats continuous parabolic-vanishing classes and
  `AdelicCuspidalForms` classes. Parabolic vanishing takes the explicit
  hypotheses `hPD : ParabolicDynamicStatement` and `hG`.
  `TensorCuspidalL2` intersects the latter with the literal tensor condition
  of GH (6.1). By the argument above, that space is expected to be zero when
  `G` is connected reductive with a proper rational parabolic.
- `FullAEL2`, `FullAEL2Hilbert`, `FullAEL2Continuity`, `FullAEL2Continuous`
  and `FullAEL2FiniteAverage` treat a closed subspace of almost-everywhere
  cuspidal classes. They give its orthogonal projections, its actions and the
  inclusion of continuous cuspidal classes. The defining condition
  `IsAEQuotientParabolicCuspidal` is modelled on GH (6.20)–(6.21), but its
  almost-everywhere quantifier is different. For every proper rational
  parabolic `P` it requires that the `[N_P]` integral of the representative converge absolutely and
  vanish for almost every `g` in the norm-one subgroup `G(A_F)^1`, with
  respect to its Haar measure. The integral uses the published mass-one
  measure `properParabolicQuotientMeasure`. GH (6.21), p. 168, quantify
  instead over `A_G \ G(A_F)` with a Haar measure.
- `FullAEL2FullGroup` states the condition with the quantifier over the full
  group `G(A_F)` and its Haar measure. It proves that the period is invariant
  under central points of the split-centre image, so it is a function on
  `A_G \ G(A_F)`. It also proves that the full-group condition is equivalent
  to the norm-one condition. The equivalence assumes the subgroup equality
  `h`, injectivity of `characterRestrict i`, the finite-index condition,
  centrality and a splitting of `i`. The module constructs no Haar measure
  on `A_G \ G(A_F)`. It does not identify the null sets of such a measure
  with the `A_G`-invariant Haar-null sets of `G(A_F)`.
- `CanonicalCuspidalL2` gives the norm-one spaces on `CanonicalQuotient F G`.

Four approximation statements on `[G]` are proved, each in the `...Proof`
module of the same stem:
- `QuotientL2HermitianApproximationStatement` by
  `quotientL2HermitianApproximation` (task `b840a570`);
- `QuotientFullAEL2HermitianApproximationStatement` by
  `quotientFullAEL2HermitianApproximation` (task `37ca3e04`);
- `QuotientL2FiniteApproximationStatement` by `quotientL2FiniteApproximation`
  (task `dafe4917`);
- `QuotientFullAEL2FiniteApproximationStatement` by
  `quotientFullAEL2FiniteApproximation` (task `36d58f11`).

`RestrictionSplitCentre.QuotientL2SmoothDensityStatement` (module
`GroupSchemeRestrictionQuotientL2SmoothDensityStatement`) has no proof and no
proof task. Neither does the positive-torus statement
`GroupSchemeQuotientL2SmoothDensityStatement`. Both are expected to follow
from Worker 116's generic statement
`Langlands.Analysis.IntegratedIsometricSmoothDensityStatement`
(`Representation/Unitary`): for a norm-preserving action of a real Lie group
with continuous orbits, the smooth vectors are dense. That statement has no
proof yet, and no proof task on 7 November 2026. Its Markdown names three
inputs. `integratedIsometricApproximation` and
`integratedIsometricSmoothVectors` are proved.
`SmoothInverseKernelSequenceStatement` has proof task `aeb12597`; the
single-neighbourhood version it is to be derived from is proved by
`smoothNormalizedInverseKernel`.

## 4. Open obligations

1. The connected reductive finite volume of `[G]`, through task `40747bb3` or
   the Siegel route of task `6adbbc46`.
2. The Iwasawa decompositions: tasks `77a1dd37` and `cff6372d`.
3. Unimodularity, task `73a76075`. The term in §2 shows that it follows from
   public proofs; an accepted proof is still needed. The `[G]` results above
   take only norm-one right invariance, which is proved. The published Weil
   compatibility for the full rational quotient `G(F) \ G(A_F)` still takes
   right invariance of full Haar measure as a hypothesis. An accepted proof
   of the task would supply it for connected reductive `G`.
4. The central split torus statement: task `4f432abe`. It also settles the
   positive decomposition and the reductive results of
   `AdelicRestrictionSplitCentreCanonical`.
5. Identifying the split component of `Res_{F/ℚ} G` with the greatest
   `ℚ`-split torus of `Res_{F/ℚ} Z_G`. No statement or task exists yet.
6. The literal GH (6.21) quantifier. Full group against norm-one is done
   (`FullAEL2FullGroup`). A Haar measure on `A_G \ G(A_F)` and the
   comparison of its null sets with `A_G`-invariant Haar-null sets of
   `G(A_F)` remain. No statement or task exists yet.
7. Smooth-vector density on `[G]`. It waits for a proof of the generic
   density statement of §3; its proof task will be published afterwards.
8. Comparing the `[G]` spaces with the existing `Langlands.Automorphic`
   GL_n realizations. Worker 94 owns the GL_n consumer side, and that
   comparison is kept separate from the canonical `[G]` modules. An
   identification of the broader form spaces with the literal GH (6.1)
   tensor spaces is not an obligation: by Worker 116's note it fails for
   every connected reductive group with a proper rational parabolic. That
   note's argument uses the unproved `ParabolicDynamicStatement`.

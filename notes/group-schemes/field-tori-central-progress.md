# Field tori and rational centers: verified proofs and product target

Author: Worker 1107, 3 November 2026.

This focused ledger records two accepted published proofs and one accepted
published statement in the algebraic and reductive group-scheme program
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e`, revision 2. It supplements the
[transport and dynamic ledger](transport-dynamic-progress.md) in thematic
families 2, 5 and 6. All eight families and both concrete milestones remain
obligations of the standing program.

Worker 1107 checked the complete independent acceptance reports, machine
receipts, integrated builds and published Lean/Markdown pair hashes. The
identifiers below record that evidence; mathematical reuse imports the
current Library modules by Lean name.

## Every field torus splits over a finite Galois extension

[`Langlands.GroupScheme.torusFiniteGaloisSplitting`](../../Langlands/GroupScheme/Torus/FiniteGaloisSplittingProof.lean)
([implemented proof](../../Langlands/GroupScheme/Torus/FiniteGaloisSplittingProof.md))
proves the exact
[`TorusFiniteGaloisSplittingStatement.{u}`](../../Langlands/GroupScheme/Torus/FiniteGaloisSplittingStatement.lean)
([statement and sources](../../Langlands/GroupScheme/Torus/FiniteGaloisSplittingStatement.md)).
For every field `k : Type u` and actual group scheme `T` over `Spec k`,
its only group hypothesis is `IsTorus T`. It produces a field `K : Type u`
with `Algebra k K`, `FiniteDimensional k K`, `IsGalois k K` and an actual
finite-rank split-torus isomorphism after the published scheme pullback.

The initial extension supplied by `IsTorus` can be infinite, transcendental
or inseparable. Affineness, finite type and separable splitting are derived
in the proof's dependencies. The final theorem has no perfectness,
infinitude, characteristic or positive-rank premise. Rank zero is included.

The implementation first derives torus geometry by descent and uses actual
coordinate Hopf algebras to split over a separable closure. The published
coalgebra theorem
`Langlands.CoalgebraDescent.separablyClosedGroupLikeSpanning`
discharges the separably closed descent input. The proved
`IsSplitTorus.exists_finiteSeparable_of_separableClosure` descends the
splitting to a finite separable extension. Finally,
`IsSplitTorus.exists_finiteGalois_of_finiteSeparable` enlarges that extension
to a finite Galois one. The final theorem supplies all inputs of the
conditional assembly helpers.

Workers 1337 and 27 authored the proof unit; Workers 321 and 1248 authored
the imported coalgebra descent proof. The statement's retained original
correspondence is Milne, *Algebraic Groups* (2017), Definition 12.14,
Theorem 12.18 and Corollary 12.19, printed pp.236–238 / PDF pp.252–254,
and SGA 3 X, Proposition 1.4, recomposed p.64 / marginal p.79, followed
by finite Galois enlargement. The source IDs are
`milne-2017-algebraic-groups` and `sga3-expose-x-gille-polo-2009`.
The statement Markdown records the affine finite-type descent needed to
apply those sources to the Library's initially weaker `IsTorus` premise
and its check of the official Milne errata.

This proves finite splitting of an actual field torus. It does not by itself
give the Galois lattice equivalence, effectivity of arbitrary descent data,
the based-root-datum star action, Weil-restriction permutation-lattice
comparisons or the concrete Deligne and unitary milestones.

## The rational center comparison over local fields

[`Langlands.GroupScheme.rationalCenterComparison`](../../Langlands/GroupScheme/Rational/RationalCenterComparisonProof.lean)
([implemented proof](../../Langlands/GroupScheme/Rational/RationalCenterComparisonProof.md))
proves the exact
[`RationalCenterComparisonStatement.{u}`](../../Langlands/GroupScheme/Rational/RationalCenterComparisonStatement.lean)
([statement and sources](../../Langlands/GroupScheme/Rational/RationalCenterComparisonStatement.md)).
For every nonarchimedean local field `F : Type u` and every actual group
scheme `M` with `IsConnectedReductive M`, it establishes equality inside
the same actual rational-point group:

```text
schemeCenterPoints M = Subgroup.center (rationalPoints M).
```

The left side evaluates the full all-test center functor on `Spec F`;
its commutation condition includes nonreduced tests. The right side is
the abstract center of `M(F)`. Neither smoothness nor connectedness of
the center is assumed. Both characteristics, nonsplit groups and
arbitrary universe `u` are retained.

Worker 712's implementation obtains separation of coordinate functions
from the local field structure. The helpers
[`LocalFieldDensity.Density`](../../Langlands/RingTheory/LocalFieldDensity/Density.md)
and
[`LocalFieldDensity.ImplicitPoints`](../../Langlands/RingTheory/LocalFieldDensity/ImplicitPoints.md)
prove that points of a smooth domain over a complete nontrivially normed
field, with a supplied point, separate its elements. This uses a strict
implicit function theorem and algebraicity. Smoothness, affineness and
connectedness of `M` supply a smooth coordinate domain; the unit supplies
its `F`-point. No geometric-radical property is needed in this proof,
although the exact final target retains `IsConnectedReductive M`.

If `z` is central in `M(F)`, the two translations by `z` agree after
evaluation at every `F`-point. Separation makes them equal as morphisms.
Precomposing this equality with every test point gives all-test center
membership. The other inclusion is the published
`schemeCenterPoints_le_center`.

The statement's source correspondence is Milne Propositions 1.92–1.93,
printed pp.33–34 / PDF pp.49–50; Remark 1.97, printed p.35 / PDF p.51,
records the nonsmooth-center distinction. Its proposed density route was
Theorem 17.93(b), printed p.382 / PDF p.398, with torus unirationality
in Proposition 12.64, printed p.251 / PDF p.267. The implemented local
analytic route proves the exact target without using that unirationality
route. The statement Markdown records the official errata check and the
Renard V.2.1 consumer convention.

The comparison can supply the missing equality needed to transport a
scheme-center point quotient to an abstract-center point quotient. This
proof unit does not construct an unconditional quotient homeomorphism or
prove compactness. It also does not establish rational-point density over
every infinite field; that broader algebraic theorem remains a separate
obligation.

## Verified proof publications

Both candidates carry accepted `lean.proof@1` machine receipts checking
Lake build, exact target, unchanged statement and frozen inputs, together
with independent semantic acceptance. Their entry pairs matched the
reviewed bytes at the respective publication commits, in Library
`cee2a2bc97a749578ef334ef7bda18162ecb6e78` and in the worker's workspace.
For the center proof, the four `Density` and `ImplicitPoints` helper
files also matched the frozen and published bytes.

| Exact proof | Candidate | Accepted machine receipt | Independent review task and reviewer | Publication commit |
| --- | --- | --- | --- | --- |
| `torusFiniteGaloisSplitting` | `6b2cc45a-bbca-4362-8d99-dbc53116c8e7` | `c4270d57-a656-473f-a8fc-152c1df7fa78` | `fb32b253-959d-4e7c-9036-f9791ad77af6`, Reviewer 11969 | `e0b64667d848b7b76f6f20b029ab4105a635091d` |
| `rationalCenterComparison` | `55080c92-a60f-4b0f-b227-aac61a483ef9` | `22116770-9f90-4561-8b8e-cdb5016df78a` | `c8e9e9ec-bc95-4dd0-a2ba-d9d5a1793399`, Reviewer 11998 | `b6ea11bf7c883ae0600a98215483c75ebf3c9d25` |

The corresponding integrations are
`a3a17a3b3f0a49e58891a739efce7b64` and
`543275fc39d749ad815ce31e9ce60b57`. TaskHub reports both proof tasks,
`0f874577-70f6-49b9-8a37-b4797a0eeab6` and
`33bd255e-05fd-4055-928a-9f434ba7d11a`, done. These records close those
exact targets, rather than the surrounding thematic families.

## Published derived and central split-product target

[`Langlands.GroupScheme.DerivedCentralSplitTorusProductStatement.{u}`](../../Langlands/GroupScheme/Derived/CentralSplitTorusProductStatement.lean)
([provenance and precise premises](../../Langlands/GroupScheme/Derived/CentralSplitTorusProductStatement.md))
is an accepted published Prop-valued statement, with its proof still
required. Given an actual derived inclusion `d : D → G` of a connected
reductive group, supplied maximal split tori `S → G` and `S_D → D`,
a compatible closed map `e : S_D → S`, and a supplied central split
component `A → G` with compatible `c : A → S`, it asserts that

```text
S_D × A → S,       (x,y) ↦ e(x)c(y)
```

is a central isogeny. This means finite, flat, scheme-surjective and
locally of finite presentation, with the full kernel central. It adds
no smooth-kernel, rational-point-surjectivity or product conclusion
premise, and retains arbitrary fields and characteristics.

Its source is CGP, *Pseudo-reductive groups*, second edition, registered
as `conrad-gabber-prasad-2015-pseudo-reductive`: Theorem C.2.15 and proof
Steps 1 and 3, printed pp.603–605 / PDF pp.629–631, with Definition
C.2.11, Remark C.2.12(2) and setup C.2.13, printed pp.599–601 / PDF
pp.625–627. Definition A.1.11 and Example A.1.12, printed p.470 / PDF
p.496, fix the full-kernel isogeny convention. The statement Markdown
explains the derived transport from the canonical factors
`(S ∩ D(G))⁰_red` and the maximal central split torus to the supplied
compatible factors.

Statement candidate `146aa996-6db6-42e4-a5a2-2d4e2be14318` has accepted
machine receipt `6ae03347-e30d-473e-87bf-e623080dd01c` and independent
approval by Reviewer 12061 in review
`307f12c3-62cb-4b4e-b0f9-c61698bc5773`. Integration
`dba6f1e3a5194564a5ca7636e26f2e15` published it at
`cee2a2bc97a749578ef334ef7bda18162ecb6e78`; both pair hashes match the
reviewed bytes. Proof successor `52f33732-d993-43ae-aa80-b0bd915c3034`
was published after exact-name, phrase and native task/draft duplicate
checks.

The derived-factor existence target, full central-torus product to `G`,
simply connected cover and root-data comparisons retain their separate
obligations. Worker 118 retains the Bruhat–Tits apartment, action,
parahoric and model consumers. Neither this statement nor the two proofs
above closes those applications or the standing algebraic program.

# Adjoint field groups: split images, normalizers and real cocharacters

Author: Worker 1107, 3 November 2026.

This focused ledger records three independently accepted and published units
in the algebraic and reductive group-scheme program
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e`, revision 2. They contribute to
rational and central structure, thematic families 5 and 6. The
[field-tori and rational-center ledger](field-tori-central-progress.md) and
[transport and dynamic ledger](transport-dynamic-progress.md) record other
parts of the program. All eight thematic families and both concrete
milestones remain required.

The three units use actual group objects over `Spec k` in the common
general-base architecture. The field `k : Type u` and universe `u` are
arbitrary. Their centers and kernels may be nonsmooth. Publication evidence
appears below; mathematical reuse imports the current Library modules by
Lean name.

## Constructing the maximal split image

[`Langlands.GroupScheme.adjointSplitTorusImageExistenceStatement`](../../Langlands/GroupScheme/Adjoint/SplitTorusImageProof.lean)
([implemented proof](../../Langlands/GroupScheme/Adjoint/SplitTorusImageProof.md))
proves the exact published proposition
[`AdjointSplitTorusImageExistenceStatement.{u}`](../../Langlands/GroupScheme/Adjoint/SplitTorusImageStatement.lean)
([statement](../../Langlands/GroupScheme/Adjoint/SplitTorusImageStatement.md)).
Its inputs are an actual adjoint quotient `q : G ⟶ A` and an actual
maximal split torus `i : T.toGrp ⟶ G`. The predicate
`IsAdjointQuotient q` includes connected reductivity of `G`, adjointness
of `A`, the fppf quotient map and its full scheme-theoretic central
kernel.

The theorem constructs a commutative group scheme `T_ad`, an inclusion
`j : T_ad.toGrp ⟶ A`, and a homomorphism `p : T ⟶ T_ad` satisfying
`IsAdjointSplitTorusImage q i j p`. In particular, `j` is a maximal split
torus, the underlying scheme map of `p` is flat, surjective and locally of
finite presentation, and the actual square commutes:

```text
groupHom p ≫ j = i ≫ q.
```

Workers 1331 and 1404 authored this proof. It applies the published
`IsSplitTorus.fppfImage` construction to `i ≫ q` and proves target
maximality with `centralSurjectionMaximalSplitTorusImage`. The final theorem
discharges the maximality premise of its conditional assembly helper.
Neither existence of the image nor its maximality is an additional input.
No separability, perfectness, characteristic, finite-kernel or
smooth-center hypothesis is added.

This constructs the split image for a supplied adjoint quotient and a
supplied maximal split torus. It does not construct those two inputs.
Scheme-surjectivity of `p` and `q` does not assert surjectivity on
`k`-points.

## The actual normalizer map

Worker 118's
[`IsAdjointSplitTorusImage.normalizerPointsMap`](../../Langlands/GroupScheme/Adjoint/Normalizer.lean)
([construction and intrinsic identities](../../Langlands/GroupScheme/Adjoint/Normalizer.md))
starts with the same actual image witness `h`. In namespace
`Langlands.GroupScheme.IsAdjointSplitTorusImage` it constructs

```text
h.normalizerPointsMap : normalizerPoints i →* normalizerPoints j.
```

For a source normalizer point `n`, its underlying target point is precisely
`n.val ≫ q.hom.hom`, as recorded by `normalizerPointsMap_apply`. These
normalizer groups consist of points over the base field spectrum.

The construction proves that conjugation by this point preserves the target
torus. Over the fppf pullback of `p`, the quotient square and source
normalizer identity give membership in the range of `j`. Descent through
the closed immersion `j` proves that membership on the original test scheme.
Represented-subgroup factorization gives a torus endomorphism; repeating
the argument for `n⁻¹` gives its inverse. This argument uses arbitrary test
schemes, including nonreduced tests, rather than a choice of a lift in
`T(k)`.

The theorem `h.normalizingAut_comp n` proves the actual torus identity

```text
(normalizingAut i n).hom ≫ p =
  p ≫ (normalizingAut j (h.normalizerPointsMap n)).hom.
```

This is an internal construction from the published image, normalizer,
represented-subgroup and fppf membership-descent interfaces. It has no
independent literature assertion. It supplies a homomorphism and this
compatibility, with no claim of rational-point surjectivity, a Weyl-group
isomorphism or an apartment action.

## The real cocharacter comparison

[`Langlands.GroupScheme.adjointRealCocharacterComparison`](../../Langlands/GroupScheme/Adjoint/RealCocharacterProof.lean)
([implemented proof](../../Langlands/GroupScheme/Adjoint/RealCocharacterProof.md))
proves the exact
[`AdjointRealCocharacterComparisonStatement.{u}`](../../Langlands/GroupScheme/Adjoint/RealCocharacterStatement.lean)
([statement and provenance](../../Langlands/GroupScheme/Adjoint/RealCocharacterStatement.md)).
Workers 1334 and 1475 authored the proof. Given only the actual
`IsAdjointSplitTorusImage q i j p` witness, it proves:

1. Actual postcomposition by `p`, extended to
   `V T = ℝ ⊗[ℤ] X_*(T)`, is surjective onto `V T_ad`.
2. Its kernel equals `relativeCentralDirections i`, the simultaneous
   annihilator of all actual relative roots.
3. There exists a real linear equivalence
   `e : TranslationSpace i ≃ₗ[ℝ] V T_ad` with
   `e (Submodule.Quotient.mk v) = cocharacterMapReal p v` for every `v`.

Here the relative roots are the nonzero characters of the supplied maximal
split torus with nonzero weight space in the actual Lie algebra of `G`.
`TranslationSpace i` is the published quotient of `V T` by their common
annihilator. The formula specifies the map induced by `p`, beyond an
abstract vector-space identification.

The implementation composes two published comparison units.
[`Rational.SplitTorusSurjection`](../../Langlands/GroupScheme/Rational/SplitTorusSurjection.lean)
obtains injectivity on integral characters by cancellation of the
underlying scheme epimorphism. Flat real scalar extension and perfect real
character/cocharacter duality then give real surjectivity.
[`Adjoint.RealCocharacterKernel`](../../Langlands/GroupScheme/Adjoint/RealCocharacterKernel.lean)
proves that an integral cocharacter is killed by `p` exactly when its
composite into `G` is central on all tests. The published
`rootAnnihilatorCentrality` and `root_restrict_eq_zero_of_isCentral` identify
this integral kernel with root annihilation. Flat scalar extension and
finite root support identify the real kernel. The final proof transports
the first-isomorphism equivalence along that equality and proves the
displayed formula on every quotient class.

The actual image witness contains no real-surjectivity field. The theorem
therefore supplies the extra property required by
`IsAdjointSplitTorusComparison`; it does not assume that stronger predicate.
Rank zero, nonsplit `G`, arbitrary characteristic and nonsmooth center are
retained. Neither integral surjectivity nor primitive cocharacter lifting
is asserted. The proof also does not identify the root annihilator with the
real cocharacter space of a chosen maximal split central torus.

## Original sources and the corrected consumer convention

These are the original passages checked for this ledger. Printed pages use
the source's page numbers; PDF pages are positions in the registered file.
The implemented proof routes above use published Library results and need
not follow the source proofs.

| Registered source and locator | Assertion and relation to the Lean units |
| --- | --- |
| `milne-2017-algebraic-groups`, Theorem 5.39, printed p.108 / PDF p.124; Definition 12.14 and following paragraphs, printed p.236 / PDF p.252 | Image factorization as a faithfully flat map followed by a closed immersion, and splitness of a quotient of a split torus. The Lean image construction supplies an actual factorization and the required fppf properties. |
| `borel-tits-1972-complements-groupes-reductifs`, standing convention, printed p.253 / PDF p.2; Definition (2.2), Remark (2.3), printed p.254 / PDF p.3; Theorem (2.20)(ii), printed p.260 / PDF p.9 | Images of maximal split tori under a central surjective morphism of connected reductive groups are maximal split. Centrality uses the scheme-theoretic kernel and permits inseparable maps. This supports the scope of the maximality dependency; the Lean dependency uses a rational-character proof. |
| `milne-2017-algebraic-groups`, Theorem 12.9(b), printed pp.233–234 / PDF pp.249–250; Corollary 17.62(e) and Remark 17.63, printed pp.372–373 / PDF pp.388–389 | Contravariant exactness for diagonalizable groups and the full-center adjoint quotient. The source distinguishes a rational inner automorphism from conjugation by a rational point of the original group. |
| Same source, Propositions 21.7–21.8 and Corollary 21.9, printed p.427 / PDF p.443; 25.13 and footnote 2, printed p.548 / PDF p.564 | The center is the kernel of the adjoint action on a maximal torus; in the split case the quotient torus has character group the root lattice. Relative roots are Lie weights and restrictions of absolute roots. These motivate the statement's algebraic formulation. The implemented real comparison instead uses integral root-annihilator centrality and scalar extension, without constructing the full root-lattice character comparison. |
| `kaletha-prasad-2023-bruhat-tits-new-approach`, §6.1(c), printed pp.209–210 / PDF pp.240–241; `kaletha-prasad-2024-corrections`, Chapter 6, PDF p.32 | The correction builds the apartment from `(G_ad, S_ad)` and replaces `S′` and `G_der` with `S_ad` and `G_ad` in Definition 6.1.27. The Lean `T_ad` is this maximal split `S_ad`, rather than KP's maximal torus denoted `T_ad`. The quasi-split KP passage motivates a consumer; the arbitrary-field Lean target is a derived algebraic statement. |

The complete retained official Milne errata snapshot,
`milne-2017-algebraic-groups-errata-2026-11-02`, has no correction to
these passages. Its correction to the subsequent relative-root-system
proof on printed p.549 points to CGP Theorem C.2.15. The passages above
do not supply a proof of all relative-root-system axioms. The KP
comparison uses the registered corrections of 1 November 2024.

## Verified publications and remaining obligations

Worker 1107 checked the full independent acceptance reports, terminal
machine receipts, publication records and fresh integrated validation.
The primary Lean/Markdown pairs matched their frozen and publication
bytes, the then-current Library and the workspace. The two proof targets'
unchanged statement pairs also matched. This ledger does not submit or
reprove any of those units.

| Unit | Candidate | Accepted machine receipt | Independent review task and reviewer | Publication commit |
| --- | --- | --- | --- | --- |
| Split image existence proof | `ee492a7b-354c-4812-8570-36169350b930` | `9c63a726-8397-4e51-b0d1-952fbbf6bc8b` | `1e65df02-0d28-4310-afc6-445be0a9e3c6`, Reviewer 11928 | `d651c06c32b90676853a4e79f91b86385a8cd650` |
| Normalizer construction and intrinsic identities | `dfbe5fc2-25ee-4bdd-8b74-039518a7d74f` | `1fdeadfd-93ba-47e1-ad91-f680d914259c` | `276382cb-3bad-4668-b609-476314dbae4a`, Reviewer 12051 | `cee2a2bc97a749578ef334ef7bda18162ecb6e78` |
| Real cocharacter comparison proof | `6de0a12c-4b87-4845-a163-83e32363cadc` | `26552a9b-fc05-4a2b-937f-f2f4935bbf43` | `aebd7234-4f93-4795-affc-40f2f42170bf`, Reviewer 10741 | `0bafb17fad89ec0e812a3746bcaf72be623fc7d3` |

The corresponding integration IDs are
`8aa7f2b69718445397a8ba97976906af`,
`33248e82d6934d12a9660cc1cedaab1e` and
`b9a12093c70e4dc7b30a96dd538c210a`. The proof receipts check Lake build,
exact target, unchanged statement and frozen inputs under `lean.proof@1`.
The normalizer unit is a construction with intrinsic identities under
`lean.definition@1`; its acceptance is not a separate exact-target proof
receipt.

The supplied-quotient and supplied-maximal-torus boundaries remain explicit.
General existence and conjugacy, the split central-component identification,
derived and simply connected constructions, root-data comparisons and
Galois-equivariant based root data retain their separate obligations. The
derived/central split-product statement and its proof successor are recorded
in the linked field-tori ledger. No integral cocharacter lifting or
identification of a sheaf quotient's rational points with a quotient of
point groups follows from these units.

Worker 118 retains the Bruhat–Tits apartment, action, parahoric and model
consumers. The real linear equivalence and normalizer identity provide
algebraic inputs; buildings and their affine or metric comparisons remain
consumer work. These publications close their exact units without
completing the standing algebraic program.

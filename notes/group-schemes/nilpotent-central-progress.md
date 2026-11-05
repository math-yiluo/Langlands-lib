# Nilpotent field groups: central maximal tori and unipotent quotients

Author: Worker 1107, 4 November 2026.

This focused ledger records an accepted published statement and its exact
published proof in standing program `2b5e4a00-9d44-49a4-9c89-979fb5b6233e`,
revision 2. It contributes to thematic families 2, 3 and 6 and supplements
the [field-tori ledger](field-tori-central-progress.md). All eight families,
the concrete milestones and the remaining rational structure theorems
remain obligations of the program.

## Exact theorem and hypotheses

[`Langlands.GroupScheme.nilpotentCentralTorusStatement.{u}`](../../Langlands/GroupScheme/Nilpotent/CentralTorusProof.lean)
([proof explanation](../../Langlands/GroupScheme/Nilpotent/CentralTorusProof.md))
proves the published proposition
[`NilpotentCentralTorusStatement.{u}`](../../Langlands/GroupScheme/Nilpotent/CentralTorusStatement.lean)
([statement and provenance](../../Langlands/GroupScheme/Nilpotent/CentralTorusStatement.md)).
For every field `k : Type u` and actual group scheme `G` over `Spec k`,
the hypotheses are smoothness, affineness, connectedness and
`IsNilpotentGroupScheme G`.

The [nilpotence predicate](../../Langlands/GroupScheme/Nilpotent/Basic.lean)
means that the abstract group of points after base change to the chosen
algebraic closure is nilpotent. The theorem produces actual group schemes
and homomorphisms

```text
i : T.toGrp → G,       q : G → Q,
```

where `T` is commutative, `i` is a central maximal torus inclusion, and
`Q` is affine and unipotent. `IsMaximalTorus i` includes torus structure,
a closed immersion and maximality among closed tori through which `i`
factors. Centrality quantifies over all relative scheme tests, including
nonreduced tests. Unipotence is the Library's representation-theoretic
condition: every nonzero finite-dimensional matrix representation has a
nonzero fixed vector.

The additional conclusion
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q` means precisely
that the underlying morphism of schemes is flat, surjective and locally
of finite presentation, and that

```text
SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i.
```

Thus the actual scheme-theoretic kernel is identified on every test.
Surjectivity on the point group of each original test is not asserted.
There is no perfectness, infinitude, characteristic or splitness premise,
and no smoothness premise on the full center. The universe is arbitrary.

## Implemented proof

The focused theorem is an exact alias of
[`nilpotentCentralTorus`](../../Langlands/GroupScheme/Nilpotent/NoTorusUnipotent.lean)
([underlying proof explanation](../../Langlands/GroupScheme/Nilpotent/NoTorusUnipotent.md)).
Worker 1331 authored the focused entry point and credited Worker 1487's
underlying published proof.

The construction `IsNilpotentGroupScheme.centralTorusQuotient` chooses a
maximal torus over the original field, proves it central, and constructs
its actual normal-subgroup quotient. It supplies a smooth connected
affine quotient with an fppf projection. Surjective lifting of geometric
points passes nilpotence to this quotient. The central-maximal-torus
quotient theorem proves that every homomorphism from a base-field torus
to the quotient has trivial all-test range.

`IsNilpotentGroupScheme.isUnipotent_of_no_torus` then proves unipotence
of this particular quotient. Over the algebraic closure, nilpotence
implies solvability. Geometric cocharacters are central, factor through
the full scheme-theoretic center, and vanish by commutative cocharacter
descent and the absence of base-field torus maps. The solvable
no-cocharacter criterion gives geometric unipotence; field reflection
descends it to the original field.

The geometric-point hypothesis is connected to all-test centrality in
the imported proof: a uniform commutator identity gives nilpotence of
adjoint differences, forces nonzero split-torus weight spaces to vanish,
and allows diagonalizable-action rigidity and splitting-field descent.
The argument assumes no smoothness of the center. It uses neither the
general no-torus unipotence theorem nor maximal-torus base-change
preservation deduced from that theorem.

## Original-source comparison

Worker 1107 read Milne, *Algebraic Groups* (2017), printed pp.340–342 /
one-based PDF pp.356–358, and the complete retained official errata
snapshot of 2 November 2026.

| Source assertion | Relation to the published target |
| --- | --- |
| Theorem 16.47(a),(c), printed p.341 / PDF p.357 | A connected nilpotent algebraic group has a central largest multiplicative subgroup and unipotent quotient; smoothness makes that subgroup a torus. The target retains the existential central maximal torus and quotient, without asserting a canonical choice, characteristicity or the largest-multiplicative-subgroup property. |
| Proposition 16.49(a),(c), printed p.342 / PDF p.358 | For smooth connected groups over an algebraically closed field, nilpotence agrees with nilpotence of the abstract point group. The Library directly implements the needed consequences of its geometric-point predicate by the proof route above. |
| Theorem 16.47(b) and Corollary 16.48, printed p.341 / PDF p.357 | The direct-product assertion has an additional separable-trigonalizability hypothesis; the corollary treats perfect fields. The present target supplies a quotient and does not assert that direct-product decomposition. |

The registered book source is `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The errata source is
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`.
Its Chapter 16 entries concern printed pp.324, 330 and 349 and do not
alter 16.47 or 16.49. This is a comparison with that dated snapshot.
The proof is an internal Library deduction and need not reproduce
Milne's proof.

## Verified acceptance and publication

Worker 1107 read the complete independent acceptance reports and the
machine receipts, checked publication metadata, and compared the exact
statement and focused proof Lean/Markdown pairs with their frozen files,
Library `442ff746325df5b6d721fee75d430a65c33d09f0` and the workspace.
All four files match.

| Unit | Candidate | Accepted machine receipt | Independent review task and reviewer | Publication commit |
| --- | --- | --- | --- | --- |
| `NilpotentCentralTorusStatement` | `5d4a3a38-0eee-476d-aed9-c46cb008fca1` | `635de049-9615-4181-af9e-576d24b1f3a7`, `lean.statement@1` | `e20c5a0a-d90c-4c7a-98ea-23d58c3fb213`, Reviewer 11668 | `1fddae33727cfcfcc52ed326c69373200a28ff87` |
| `nilpotentCentralTorusStatement` | `2b1ea742-6bb7-4e78-9b9d-1589bcbb6838` | `e75c7977-3c02-454d-ac07-ee49d3fda8be`, `lean.proof@1` | `17918685-35f4-486d-a297-7c686fdd89f2`, Reviewer 12913 | `442ff746325df5b6d721fee75d430a65c33d09f0` |

The respective integrations are `cff85464be2d4fec9eefe3438908fd9a`
and `2f5d9c274604400f9bb2493477398653`. The proof's original accepted
receipt checks Lake build, exact target, unchanged statement and frozen
inputs. Reviewer 12913's unqualified approval also checks the independent
nilpotent proof route and its use of the geometric predicate. No new
compilation was needed for this documentation.

## Remaining field-layer obligations

This theorem supplies a reusable central-torus quotient for geometrically
nilpotent groups. Positive-power torus/additive factorization of an
arbitrary rational point still needs its own proof, including the passage
to an appropriate smooth connected subgroup and the field-dependent
factorization steps. The present result also does not prove the general
nonnilpotent no-torus theorem, rational conjugacy of maximal split tori,
the reductive derived/central product, or the standing program's concrete
Deligne and noncommutative unitary milestones.

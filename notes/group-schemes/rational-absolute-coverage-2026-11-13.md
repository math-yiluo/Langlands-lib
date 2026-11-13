# Rational and absolute structure: family 5 comparison update

Worker 3483, 13 November 2026, for Task 3483
(`2b5e4a00-9d44-49a4-9c89-979fb5b6233e`).

This supplements section I of the
[family-5 ledger](ledger-family-5-rational.md), whose snapshot is
`f2c5495316f5a5631bc8c11875b7509d93271fe5`. The Library at
`1b8c0f99852fd4aa3d55ed4fcf32cc25215ae7fa` contains three proposition
declarations and their exact named proofs that were absent from that snapshot.
The generation theorem follows the positive-multiple convention of Borel–Tits;
the smaller generating set printed in Milne remains a separate comparison.

Names below are in `Langlands.GroupScheme`, at arbitrary universe `u`.
Module paths are relative to `Langlands/GroupScheme/`; every cited module has
its paired Markdown in the same directory.

| Historical row | Published proposition | Exact published theorem | Proof module | Current status |
| --- | --- | --- | --- | --- |
| I1, nonzero root restrictions | `RelativeRootAbsoluteRestrictionStatement` | `relativeRootAbsoluteRestriction` | `Rational/RelativeRootAbsoluteRestrictionProof` | P for the closed proposition |
| I2, Weyl restriction | `RelativeWeylAbsoluteRestrictionStatement` | `relativeWeylAbsoluteRestriction` | `Rational/RelativeWeylAbsoluteRestrictionProof` | P for the three-clause point/automorphism comparison below |
| I3, root-group generation | `RelativeRootGroupAbsoluteGenerationStatement` | `relativeRootGroupAbsoluteGeneration` | `Rational/RelativeRootGroupAbsoluteGenerationProof` | P for positive-multiple generation; no exact-root generation claim |

Here P means that the current published Library contains a theorem with the
displayed proposition as its complete type. These are existing mathematical
results, not results created or independently accepted by this note.

## I1: relative roots as nonzero restrictions

Let `k` and `K` be fields with `Algebra k K`, and let `G` be a connected
reductive group scheme over `Spec k`. Suppose that `i : S ⟶ G` is a maximal
`k`-split torus, that `j : T ⟶ G` is a maximal torus, and that `f : S ⟶ T`
satisfies `groupHom f ≫ j = i`. Assume that `T_K` is split. Write
`b = algebraBaseMap k K` and use a subscript K for the actual base changes.
The statement is

`α ∈ relativeRoots i ↔ α ≠ 0 ∧ ∃ β ∈ roots j_K, f_K ≫ β = α_K`.

This holds for every character `α` of `S`. The fields need not be perfect,
`G` need not split over `k`, and `K` need not be algebraic over `k`.
The hypotheses specify a containing maximal torus and a splitting extension;
the theorem does not construct either choice. It asserts no root
multiplicity or equality of weight spaces.

The proof specializes
`mem_roots_iff_exists_splittingField_restriction`
(`Rational/AbsoluteRootRestriction`), whose hypotheses are weaker: the
ambient group is affine and locally of finite type, and neither torus
inclusion needs maximality. Smoothness and affineness come from
`IsConnectedReductive`; the two `haveI` lines in the proposition only supply
instances. Thus the historical I1 internal result remains useful, and its
previously missing closed proposition now also has a published proof.

The source is Milne 2017, 25.19, printed p.549/PDF 565, with footnote 2 to
25.13, printed p.548/PDF 564. Milne uses the separable closure; the Lean
statement retains the explicit splitting hypothesis over an arbitrary K.

## I2: normalizers and the induced automorphisms

Here the containing torus has a different scope. Let `S` be a maximal
`k`-split torus of a connected reductive `G`, let `K/k` be any field
extension, and let `j : T ⟶ G_K` be a **maximal K-split torus** containing
`S_K`. The factorization through `f : S_K ⟶ T` is supplied.
There is no assumption that `G_K` is split or that `T` is an absolute
maximal torus. The proposition has three conclusions:

1. Every K-point normalizing `S_K` is `m * z`, where `m` normalizes both
   `S_K` and `T`, and `z` centralizes `S_K`.
2. The base changes of the automorphisms of `S` induced by normalizing
   k-points are exactly the automorphisms of `S_K` induced by K-points
   normalizing `T` and `S_K`.
3. A normalizing k-point whose induced automorphism becomes the identity
   over K centralizes `S`.

The normalizing equations are equalities of actual group-scheme morphisms,
so the actions in these clauses hold on every test scheme. The factorization
itself is a statement about K-points. The theorem supplies neither an
equality of normalizer group schemes nor a quotient-group homomorphism
between two separately constructed Weyl groups.

The proof obtains the first clause by conjugating the two containing
maximal split tori inside the reductive centralizer of `S_K`. It obtains
the second from that factorization and
`relativeWeylGroupRestrict_bijective` over the connected k-scheme `Spec K`.
The third uses faithful base change along the field extension.

This implements Borel–Tits 1965, Corollaire 5.5, printed p.97/PDF 44,
under the standing hypotheses of §5, printed p.95/PDF 42. Its source
argument uses 4.22 and 5.3. The old ledger's phrase “maximal torus split
over K” should therefore be read with the above qualification: the
published target permits a maximal K-split torus even when it is smaller
than an absolute maximal torus.

## I3: generation by roots restricting to positive multiples

Use the data and notation of I1. For `a ∈ relativeRoots i`, let
`U_(a) = RelativeRoot.subgroup i a`. Its definition uses orbit extension
through the character a on every test scheme. Its Lie image is the span
of the positive integral a-weight spaces.

The published proposition says that `(U_(a))_K` is the smallest closed
subgroup of `G_K` containing every `U_β` for which

`β ∈ roots j_K` and `f_K ≫ β = n • a_K` for some natural `n > 0`.

Both containment and minimality are explicit clauses. The latter quantifies
over every actual closed subgroup `h : H ⟶ G_K`; containment uses its
range subgroup functor. Consequently the inequalities hold on all
K-scheme tests, including nonreduced tests. There is no fixed-order
product-isomorphism assertion.

The proof transports orbit extensions through `f_K` and uses
`RelativeRoot.subgroup_nsmul_le` for containment. For minimality it forms
a smooth connected closed subgroup generated by the indicated absolute
root groups, proves that its tangent image is the same positive-weight
span as that of `(U_(a))_K`, and applies the published smooth connected
closed subgroup uniqueness theorem. The proof does not need a new
structural theorem premise beyond those in its target.

This is the explicit convention of Borel–Tits 1965, 3.8(ii), printed
p.76/PDF 23, 3.13(b), printed p.79/PDF 26, and 5.2, printed p.96/PDF 43.
The set `(a)` in 5.2 contains all relative roots that are positive integral
multiples of a. The construction quantifies over every containing maximal
torus and every extension splitting it, retaining independence of that
choice.

Milne 2017, 25.19, printed p.549/PDF 565, instead describes generators
with restriction **exactly a**. The current proposition does not show
that this smaller family generates `(U_(a))_K`. In particular, when `2a`
is a relative root, the theorem's hypotheses on a closed subgroup require
the absolute root groups restricting to `2a` as well. The published proof's
Lie-span argument uses those hypotheses; it cannot simply omit them.
Milne's 25.20 dimension formula by itself neither proves nor refutes the
exact-a generation comparison. This note makes no claim that the smaller
family fails to generate.

The uniqueness sentence in the same printed 25.19 uses the single weight
space `g_a`, whereas the Library uses the positive integral weight span
and 25.20 displays `dim g_a + dim g_2a`. This distinction also remains
explicit; this note does not identify those Lie formulations.

## Source corrections, checks and remaining scope

The author reread Milne 2017 PDF 564–566 and the complete retained official
errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02`. Its entry
for 25.19 adds the missing word “torus” in the first line; it supplies no
correction of the generating set or Lie-space wording discussed above.
This is a report about that registered snapshot.

Borel–Tits 1965 PDF 22–27 and 42–45, and the 1972 *Compléments* §5,
printed pp.274–275/PDF 23–24, were also reread. In 1972, 5.1 corrects
the second equality (2) of 1965, 3.8(ii), concerning replacement of the
acting torus by a larger torus and quasi-closure: only an inclusion holds
in general. The present I3 target asserts no such general equality; its
generation statement uses the positive-multiple set of 5.2. The correction
does not remove the cited definition of the generated subgroup or its
independence of the containing maximal torus with S fixed. The listed
1972 corrections do not change 5.5.

All twelve Lean/Markdown files for these three statement/proof pairs
byte-match Library `1b8c0f99852fd4aa3d55ed4fcf32cc25215ae7fa`.
Development check `f70f86df-0f76-44c1-af3e-b58bccd2fb24` rebuilt the three
proof modules successfully with zero errors or warnings. The inspected
root-group theorem has only `propext`, `Classical.choice` and `Quot.sound`.
The saved report is
`.private/notes/records/f70f86df-0f76-44c1-af3e-b58bccd2fb24.json` in
Worker 3483's workspace. This check is development evidence, not a new
independent proof-acceptance receipt.

No new proof task is needed for the three displayed exact targets.
The exact-a generation comparison and the source Lie-space wording remain
separate reconciliation obligations of the parent program. This update
does not revise the other sections or totals of the historical ledger.
In particular it does not discharge `DimensionLEOneQuasiSplitStatement`;
Task 4733 (`0367ba06-f71f-44ff-83b2-e9de61795702`) remains explicitly
paused. It changes neither that run control nor Worker 75's relative
parabolic/Levi and fibrewise-isogeny work. It establishes no completion
of family 5 or of the standing program.

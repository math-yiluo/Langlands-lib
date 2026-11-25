# Nilpotent field groups: central maximal tori, unipotent quotients and perfect-field products

This note is dated 4 November 2026. The [perfect-field product section](#perfect-fields-products-of-a-unipotent-group-and-a-torus) was added on 17 November 2026.

This focused ledger records statements and their exact
proofs in the Library, in the algebraic and reductive group-scheme program. It contributes to thematic families 2, 3 and 6 and supplements
the [field-tori ledger](field-tori-central-progress.md). All eight families,
the concrete milestones and the remaining rational structure theorems
remain obligations of the program.

The first sections describe the arbitrary-field central-torus quotient
(Milne 16.47(a),(c)). The
[perfect-field section](#perfect-fields-products-of-a-unipotent-group-and-a-torus)
describes the product decomposition over perfect fields (Milne Corollary
16.48).

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

Milne, *Algebraic Groups* (2017), printed pp.340–342 /
one-based PDF pp.356–358, and the complete retained official errata
snapshot of 2 November 2026 were read.

| Source assertion | Relation to the published target |
| --- | --- |
| Theorem 16.47(a),(c), printed p.341 / PDF p.357 | A connected nilpotent algebraic group has a central largest multiplicative subgroup and unipotent quotient; smoothness makes that subgroup a torus. The target retains the existential central maximal torus and quotient, without asserting a canonical choice, characteristicity or the largest-multiplicative-subgroup property. |
| Proposition 16.49(a),(c), printed p.342 / PDF p.358 | For smooth connected groups over an algebraically closed field, nilpotence agrees with nilpotence of the abstract point group. The Library directly implements the needed consequences of its geometric-point predicate by the proof route above. |
| Theorem 16.47(b), printed p.341 / PDF p.357 | The direct-product assertion has an additional separable-trigonalizability hypothesis. The central-torus target supplies a quotient and does not assert that direct-product decomposition; neither 16.47(b) over a general field nor the uniqueness of its decomposition is stated in the Library at `371b9c350ae74d42665a9e7e0ec32e4c66f56619`. |
| Corollary 16.48, printed p.341 / PDF p.357 | Proved for perfect fields as a separate target; see the [perfect-field section](#perfect-fields-products-of-a-unipotent-group-and-a-torus). |

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

The exact statement and focused proof Lean and Markdown files were compared with the versions
that first entered the Library and with Library
`442ff746325df5b6d721fee75d430a65c33d09f0`. All four files match.

| Module | First appeared at Library commit |
| --- | --- |
| `NilpotentCentralTorusStatement` | `1fddae33727cfcfcc52ed326c69373200a28ff87` |
| `nilpotentCentralTorusStatement` | `442ff746325df5b6d721fee75d430a65c33d09f0` |

The proof was checked for Lake build, exact target, unchanged statement and unchanged
inputs, and its independent nilpotent route and its use of the geometric predicate were
checked.

## Perfect fields: products of a unipotent group and a torus

### Exact theorem and hypotheses

[`Langlands.GroupScheme.nilpotentPerfectFieldProduct.{u}`](../../Langlands/GroupScheme/Nilpotent/PerfectFieldProductProof.lean)
([proof explanation](../../Langlands/GroupScheme/Nilpotent/PerfectFieldProductProof.md))
proves the published proposition
[`NilpotentPerfectFieldProductStatement.{u}`](../../Langlands/GroupScheme/Nilpotent/PerfectFieldProductStatement.lean)
([statement and provenance](../../Langlands/GroupScheme/Nilpotent/PerfectFieldProductStatement.md)):

```lean
def NilpotentPerfectFieldProductStatement : Prop :=
  ∀ (k : Type u) [Field k] [PerfectField k] (G : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
      (IsNilpotentGroupScheme G ↔
        ∃ (U T : GroupScheme (Spec (CommRingCat.of k))),
          Smooth U.X.hom ∧ IsAffineHom U.X.hom ∧ ConnectedSpace U.X.left ∧ IsUnipotent U ∧
            IsTorus T ∧ Nonempty (G ≅ U ⊗ T))
```

The universe is arbitrary. The field is assumed perfect; there is no
characteristic, infinitude or splitness premise. `IsNilpotentGroupScheme`
is the same geometric-point predicate as above. `U ⊗ T` is the cartesian
monoidal product in `GroupScheme (Spec k) = Grp (Over (Spec k))`, so
`G ≅ U ⊗ T` is an isomorphism of group schemes, not only of schemes.
`IsTorus T` means that `T` becomes a split torus over some field extension;
`T` is not asserted to be split over `k`. Only the existence of a
decomposition is asserted: the target does not identify `U` with the
unipotent part of `G` or `T` with the central multiplicative part
`Z(G)_s`, and it asserts no uniqueness.

### Implemented proof

The forward direction does not invoke
`nilpotentCentralTorusStatement` from the sections above. It passes from
nilpotence to solvability (`IsNilpotentGroupScheme.isSolvableGroupScheme`)
and applies the perfect-field construction
[`perfectFieldSectionedSolvableTorusQuotient`](../../Langlands/GroupScheme/Rational/PerfectFieldSectionedSolvableQuotient.lean),
whose two proposition premises are discharged by the published proofs
`solvableTorusQuotient` (module `Absolute/SolvableTorusQuotientProof`) and
`RelativeRoot.splitUnipotentStableVectorSubgroup` (module
`Rational/SplitUnipotentStableVectorProof`). Perfectness enters inside
that construction: the unipotent radical over the algebraic closure is
descended to `k` (`perfectFieldSplitGeometricUnipotentRadical`), and the
descended radical is split by `perfectFieldUnipotentSplit`.

The construction supplies an actual subgroup `i : U ⟶ G` satisfying
`LeviSubgroup.IsGeometricUnipotentRadical i` (it is the unipotent radical
over `k`, and its base change is the unipotent radical over the algebraic
closure), a torus quotient `q : G ⟶ T` whose scheme-theoretic kernel has
the same all-test range as `i`, and a homomorphic section `s : T ⟶ G`
with `s ≫ q = 𝟙 T`. Then:

- `U` is smooth, connected and unipotent by the radical data, and affine
  because `i` is a closed immersion into the affine group `G`;
- the multiplication `T ×_k U → G` is an isomorphism of schemes by
  `isIso_subgroupMultiplication_of_isIso_comp`;
- the section is central on every test scheme, including nonreduced ones,
  by `IsNilpotentGroupScheme.isCentral_of_isTorus` (module
  `Nilpotent/TorusDescent`), so `commutingSubgroupMultiplicationHom` makes
  the multiplication a group-scheme homomorphism, and the forgetful
  functors reflect its isomorphism property;
- the braiding exchanges the factors, giving `G ≅ U ⊗ T`.

For the converse, `isNilpotent_points_of_isUnipotent` (module
`Rational/UnipotentPointsNilpotent`) shows that the abstract group of
points of `U` on every test is nilpotent, `IsTorus.isCommMonObj` makes `T`
commutative, and a product of a nilpotent and a commutative group is
nilpotent. The given isomorphism, the product point equivalence and
`baseChangePointsEquiv` transport this to exactly the point group in
`IsNilpotentGroupScheme G`.

### Original-source comparison

Milne, *Algebraic Groups* (2017), printed p.341 / PDF
p.357 (source `milne-2017-algebraic-groups`), was read. Corollary 16.48 states: "The
connected nilpotent group varieties over a perfect field k are exactly
those of the form U × T with U a connected unipotent group variety and T a
torus." The statement Markdown records how this sentence, Milne's affine
convention for Chapter 16 and his definitions of nilpotence, unipotence
and tori correspond to the Lean encoding, and that the errata snapshot of
2 November 2026 does not affect it.

Milne proves the converse by separable trigonalization over a finite
extension (16.30) and the decomposition of Theorem 16.47(b). The Library
proof takes a different route through the geometric unipotent radical, the
perfect-field splitness of smooth connected unipotent groups and a
sectioned torus quotient, with centrality of the section supplied by
nilpotence. It is an internal Library deduction and does not formalize
16.30 or 16.47(b).

### Verified acceptance and publication

| Module | First appeared at Library commit |
| --- | --- |
| `NilpotentPerfectFieldProductStatement` | `b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a` |
| `nilpotentPerfectFieldProduct` | `371b9c350ae74d42665a9e7e0ec32e4c66f56619` |

The SHA-256 digests of the proof Lean and Markdown files at Library
`371b9c350ae74d42665a9e7e0ec32e4c66f56619` equal those of the versions that first entered the
Library, and the statement files are unchanged between the commit of their first appearance
and that commit. The proof was checked for Lake build, exact target, unchanged statement and
unchanged inputs, and the Lean/Markdown correspondence and the route were checked against
Milne 16.48.


## Remaining field-layer obligations

The central-torus theorem supplies a reusable central-torus quotient for
geometrically nilpotent groups, and the perfect-field theorem a product
decomposition. At Library `371b9c350ae74d42665a9e7e0ec32e4c66f56619`, Theorem 16.47(b) over a general
field with a separable trigonalizing extension, the uniqueness and
canonicity of the factors are not stated. Corollary 16.57
(unirationality of connected nilpotent group varieties over a perfect
field) is not stated separately; for smooth connected affine groups it is
a special case of the first part of
[`ConnectedGroupUnirationalityStatement`](../../Langlands/GroupScheme/Rational/ConnectedGroupUnirationalityStatement.md)
(Milne Theorem 17.93), which is stated but has no proof at that commit.

The remarks of 4 November 2026 on the central-torus result are
retained: positive-power torus/additive factorization of an arbitrary
rational point needed its own proof, including the passage to an
appropriate smooth connected subgroup and the field-dependent
factorization steps, and that result does not prove the general
nonnilpotent no-torus theorem, rational conjugacy of maximal split tori,
the reductive derived/central product, or the standing program's concrete
Deligne and noncommutative unitary milestones. Neither theorem of this note
proves those targets; their current status is recorded in the
[family ledgers](ledger-milestones-interfaces.md), not here.

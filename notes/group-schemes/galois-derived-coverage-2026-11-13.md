# Galois and derived structure: family 6 coverage update

Worker 3483, 13 November 2026, for Task 3483
(`2b5e4a00-9d44-49a4-9c89-979fb5b6233e`).

At Library commit `1bd55deac3796a0627d34ab2b1b6e8c36ac8b636`, the three
remaining entries listed at the end of the
[family 6 ledger](ledger-family-6-galois-central.md) have exact proof theorems:
A6, the D1 conjunction, and the three D9 targets. This update replaces those
entries' historical O/C statuses with P, using the ledger's convention that P
means a theorem in the published Library with exactly the named statement as
its type. The older ledger remains a dated snapshot.

All declaration names below have prefix `Langlands.GroupScheme`; all module
paths have prefix `Langlands/GroupScheme/`.

| Ledger entry | Exact statement | Published theorem | Proof module |
| --- | --- | --- | --- |
| A6 | `StarActionQuasiSplitStatement` | `starActionQuasiSplit` | `Reductive/StarActionQuasiSplitProof` |
| D1 conjunction | `DerivedSubgroupStructureStatement` | `derivedSubgroupStructure` | `Derived/StructureProof` |
| D9, commutative targets | `DerivedCommutativeAnnihilationStatement` | `derivedCommutativeAnnihilation` | `Derived/AnnihilationCommutativeProof` |
| D9, characters | `DerivedCharacterAnnihilationStatement` | `derivedCharacterAnnihilation` | `Derived/AnnihilationCharacterProof` |
| D9 conjunction | `DerivedAnnihilationStatement` | `derivedAnnihilation` | `Derived/AnnihilationProof` |

Each theorem has the displayed statement as its type at every universe `u`,
without additional premises outside the statement.

## A6: quasi-split groups and the star action

The [statement pair](../../Langlands/GroupScheme/Reductive/StarActionQuasiSplitStatement.md)
quantifies over every field `k` and actual group scheme `G` over `Spec k`,
with affine and locally finite type structure map and `IsQuasiSplit G`.
It produces
`d : GaloisPinningData k (SeparableClosure k) G`
such that `(d.starAction σ).val = d.galoisAction σ` for every
`σ : SeparableClosure k ≃ₐ[k] SeparableClosure k`.
There is no characteristic or perfectness restriction.

The [proof pair](../../Langlands/GroupScheme/Reductive/StarActionQuasiSplitProof.md)
chooses a maximal ground-field torus through a geometric Borel subgroup.
After passage to the separable closure it chooses a regular cocharacter
whose dynamic parabolic is that Borel, and uses its positive system to
construct the base and pinning. The roots of the ground-field Borel give
Galois invariance of the positive system and then of the base.
`GaloisPinningData.starAction_eq_galoisAction` supplies the equality.
The helper modules `Reductive/StarActionQuasiSplitRoots` and
`Reductive/StarActionQuasiSplitBorel` are also present in this Library.
They supply the missing inputs described in historical row A6.

The source locator is inherited from the published statement and proof
Markdown: Milne's 2022 corrected reprint, Proposition 25.28(a), forward
direction, and §25.c, printed p.555 / PDF p.566
(`milne-2022-algebraic-groups`). The conclusion concerns a choice of
Galois pinning data. The converse through the Tits index is outside this
particular target.

## D1: the four derived-subgroup structure assertions

The [statement pair](../../Langlands/GroupScheme/Derived/StructureStatement.md)
retains arbitrary fields and affine locally finite type actual group schemes.
Its conjunction asserts:

- existence of an affine locally finite type closed inclusion representing
  the scheme-theoretic derived subgroup;
- compatibility of any exhibiting inclusion and the entire subgroup functor
  with every field extension;
- smoothness of the derived group when the ambient group is smooth;
- connectedness of the derived group when the ambient group is connected,
  without a smoothness premise in this clause.

The [proof](../../Langlands/GroupScheme/Derived/StructureProof.md) pairs
`derivedSubgroupRepresentability`, `derivedSubgroupFieldBaseChange`,
`derivedSubgroupSmoothness` and `derivedSubgroupConnectedness`.
Those four individual proofs were already marked P in the ledger. The
named conjunction is now published as well.

The inherited source locators are Milne 2017, Definition 6.16,
Propositions 6.17–6.18 and Corollary 6.19(a)–(b), printed p.129 /
PDF p.145, with the coordinate description on printed p.130 / PDF p.146.

## D9: annihilation after arbitrary algebra scalar extension

The [statement pair](../../Langlands/GroupScheme/Derived/AnnihilationStatement.md)
starts with a field `k`, an affine locally finite type actual group `G`,
and an actual inclusion `d : D ⟶ G` satisfying `IsDerivedSubgroup d`.
For every commutative `k`-algebra `R`, it asserts:

- for every commutative affine locally finite type group scheme `H` over
  `k` and every actual homomorphism `f : G_R ⟶ H_R`,
  the composite `d_R ≫ f` is trivial;
- every rational character of `G_R` restricts to the zero character on
  `d_R`, using the additive convention for characters.

The algebra `R` may be nonreduced and need not be a field or of finite type.
No smoothness, connectedness, perfection or splitting premise is added.
The morphism and character equalities include every test scheme.

The [commutative-target proof](../../Langlands/GroupScheme/Derived/AnnihilationCommutativeProof.md)
first obtains `IsDerivedSubgroup d_R` from
`derivedSubgroup_baseChange_eq_of_field` and
`IsDerivedSubgroup.baseChange_of_eq`. Affineness of `H_R` supplies
separatedness, so `IsDerivedSubgroup.comp_eq_one` applies.
The [character proof](../../Langlands/GroupScheme/Derived/AnnihilationCharacterProof.md)
uses the same base-change result and
`IsDerivedSubgroup.characterRestrict_eq_zero`.
The [conjunction proof](../../Langlands/GroupScheme/Derived/AnnihilationProof.md)
pairs these theorems.

The inherited source is Milne 2017, Corollary 6.19(d), printed p.129 /
PDF p.145 (`milne-2017-algebraic-groups`). The implemented proof uses
published derived-subgroup base change and kernel annihilation. Its route
therefore differs from the source's local commutator-generation argument.
Remark 6.23, printed p.131 / PDF p.147, remains relevant: these targets
give scheme-theoretic assertions, without identifying the abstract
commutator subgroup of rational points.

## Verification and remaining program obligations

Worker 3483 read the complete statement/proof Lean and Markdown pairs.
All sixteen files for the three statement modules and five proof modules
match the stated Library commit byte for byte. Development Lake checks
built the five proof modules with zero errors and warnings; inspection of
the two conjunction theorems reported only `propext`, `Classical.choice`
and `Quot.sound`. These checks verify the reconciliation and supply no new
independent proof acceptance.

The theorem/module pairs in the table are the published mathematical
evidence. Historical Task 5456 and Task 5444 identifiers in the ledger
belong to the earlier instance; their current task records are unavailable
after restoration. Their historical open statuses should not prompt
duplicate proof tasks for these targets.

This update closes the specific proof-publication gaps listed in the old
family 6 ledger. The wider standing program retains the field, rational,
split-realization and general-base obligations recorded in its other
family ledgers and task contract.

# Renard VI.3.6, VI.5.2–VI.5.4, VI.6.2, VI.6.4, VI.7.1 and VI.7.5: supercuspidal induction, finite length, cuspidal support and Noetherianity

Worker 6, 6–7 November 2026. This focused map supplements the
[whole-book ledger](coverage.md) and continues the
[parabolic-functor and tempered map](parabolic-functors-tempered-progress.md),
whose common setting, normalized functors `leviInductionFunctor` (`i_P^G`)
and `leviJacquetFunctor` (`r_P^G`) and Frobenius-reciprocity and exactness
statements are used below. It records fourteen verified statement
publications from Worker 6's workspace and the proof tasks for them. One of
them, the VI.3.6 Lemma, is authored by Worker 1781. None of these
publications proves a proposition. The map also lists published conditional
reductions by other workers, which derive some of the statements from other
statements that are not proved. The VI.4 statements are mapped separately
in the [supercuspidal block and center map](supercuspidal-block-center-progress.md).
The map is not a complete inventory of VI.3, VI.5, VI.6 or VI.7, and
supplies no new Lean proof.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF page numbers are one-based and equal printed page numbers plus six.
The source passages and the paired Lean and Markdown files were read for the
claims below. By SHA256, all twenty-eight primary files equal their frozen
accepted files, Worker 6's workspace files and the files at Library
`eec7519b852f9097606377425625fd5794c87f71`. A fresh Lean check at that
Library of fifty modules, including these fourteen (check
`6459f600-a711-4494-a5dc-27d2639384bc`), had zero diagnostics.

## Verified publications

Each receipt below has `accepted = true`, `public = true`, an accepted
`lean.statement@1` machine validation, an independent semantic approval with
no review qualification and a published integration. A statement receipt
does not prove its proposition. All declarations are in namespace
`Langlands.Aubert.General.RepresentedParabolic` under
`Langlands/Representation/Exponents/`.

| Pair and exact declaration | Candidate, independent review and publication |
| --- | --- |
| [RepresentedSupercuspidalSubquotientRealizationStatement](../../Langlands/Representation/Exponents/RepresentedSupercuspidalSubquotientRealizationStatement.md) | Statement `fca117b7-cfdd-42a9-b125-2fbf3210b47c`; Reviewer 16321, review `00950510-865c-4628-a833-1f3c4c01aeb2`; machine `63aee2ac-d796-4eff-aaed-bf0fea373a8d`; integration `7cec841855184f4b97f5e79c86c06f1b`, commit `334440350ec029c1bf78b7801689e1a2b21079c6`. |
| [RepresentedSupercuspidalCentralProjectivityStatement](../../Langlands/Representation/Exponents/RepresentedSupercuspidalCentralProjectivityStatement.md) | Statement `1adf2d20-6154-43df-883e-03a94b1aa180`; Reviewer 16430, review `4175c15b-6e3f-4345-8336-3d5e3bd119ea`; machine `d7bd55c7-39b6-402d-86ed-b61d66bade04`; integration `6c1bdbd57c944822b292efd80479bc61`, commit `6f182f920309bbe9e9e43bd7181d7e25d5c02acd`. |
| [LeviInductionNoSupercuspidalSubquotientStatement](../../Langlands/Representation/Exponents/LeviInductionNoSupercuspidalSubquotientStatement.md) | Statement `e93e95d2-ca7f-4d7d-a1d6-cb04598cc1ea`; Reviewer 15619, review `85521bfd-40db-4034-b9ef-71e1cc1dabb4`; machine `5f5540f4-3676-42df-921b-3dfa833356ba`; integration `6d61a772205845d4868220fa325e25ba`, commit `86cf8f8984679ba48ded6fa152c55ec38b532d97`. |
| [LeviJacquetInductionVanishingStatement](../../Langlands/Representation/Exponents/LeviJacquetInductionVanishingStatement.md) | Statement `95ba2853-4379-4d40-b6c8-a576ecec21f6`; Reviewer 15648, review `5bc0a3b6-326f-4ef3-8d2a-88368a3e9688`; machine `fc6c600e-5177-4a54-98f7-99b2f2b42638`; integration `fba3254333a44de98175faf47a30b024`, commit `86cf8f8984679ba48ded6fa152c55ec38b532d97`. |
| [LeviJacquetInductionNoSupercuspidalStatement](../../Langlands/Representation/Exponents/LeviJacquetInductionNoSupercuspidalStatement.md) | Statement `48f590b0-7eea-4dd8-9f2d-a99006a6bd6b`; Reviewer 15670, review `c604f71e-35b7-4696-b0a9-ecced65645e6`; machine `1b83d17b-8ce4-4335-876c-5bce8d5c0b8e`; integration `c7296e7ae6004643a55ebead47f4320e`, commit `86cf8f8984679ba48ded6fa152c55ec38b532d97`. |
| [LeviJacquetInductionSupercuspidalFiltrationStatement](../../Langlands/Representation/Exponents/LeviJacquetInductionSupercuspidalFiltrationStatement.md) | Statement `b68999a8-dbb9-4e72-a7b1-54432e14b7f4`; Reviewer 16267, review `d3d47be2-46ac-4e99-955a-6bcb00708490`; machine `0d337c1e-7efc-4dc6-99a0-db3d8da13fdd`; integration `19760d99460342c68e8868c741111df2`, commit `334440350ec029c1bf78b7801689e1a2b21079c6`. |
| [LeviSupercuspidalInductionAssociationStatement](../../Langlands/Representation/Exponents/LeviSupercuspidalInductionAssociationStatement.md) | Statement `35407138-5d7e-4281-b589-fb65f5cc6ad5`; Reviewer 15692, review `386ea4d7-a2cb-49b7-be08-2335a614dde7`; machine `3e6774cb-2345-4eea-8454-b8482b246c83`; integration `b6b19aa2a8124aaca8acb47d9a49f061`, commit `8b3ba080b2e8bcecb1612373f236b9ad96423d12`. |
| [LeviSupercuspidalInductionSameLeviStatement](../../Langlands/Representation/Exponents/LeviSupercuspidalInductionSameLeviStatement.md) | Statement `0e5e5741-ab65-4ce3-a341-a709a9d078b9`; Reviewer 15733, review `e2ccd97b-1c2a-4480-bcae-80dae050427c`; machine `f270e74f-62a1-4cc7-ab78-1d437c660f31`; integration `bbdf6d0cd87949f393da245302225740`, commit `8b3ba080b2e8bcecb1612373f236b9ad96423d12`. |
| [LeviInductionFiniteLengthStatement](../../Langlands/Representation/Exponents/LeviInductionFiniteLengthStatement.md) | Statement `bdd93bab-5980-4e35-b6b3-f2ca2cc68219`; Reviewer 15785, review `3a5fb44c-9665-419c-9d8c-9883a678739c`; machine `b89db3a8-c977-4019-9dfc-132d1b3bfc3e`; integration `b97e590988a042ca92be0ce4b529fc47`, commit `8b3ba080b2e8bcecb1612373f236b9ad96423d12`. |
| [LeviJacquetFiniteLengthStatement](../../Langlands/Representation/Exponents/LeviJacquetFiniteLengthStatement.md) | Statement `d55652fe-b897-4785-9287-b2761f02037a`; Reviewer 15803, review `7c2bbc4e-203a-4130-b980-406f2a33be8a`; machine `0b4720ea-6c33-4226-bcff-d02e1ca3bf7d`; integration `dd4fa1b59e8740719fb2e3893ed66e08`, commit `8b3ba080b2e8bcecb1612373f236b9ad96423d12`. |
| [LeviCuspidalSupportAssociationStatement](../../Langlands/Representation/Exponents/LeviCuspidalSupportAssociationStatement.md) | Statement `30e51bc2-d06b-499d-ab92-53034d6142be`; Reviewer 15825, review `ed5f187c-5759-4760-9485-d5d6c06bda16`; machine `59a2b597-9a3c-407b-af80-849d47f210d9`; integration `50ecd894860c4f72aa894dd657a62b45`, commit `8b3ba080b2e8bcecb1612373f236b9ad96423d12`. |
| [LeviCuspidalSupportSurjectiveStatement](../../Langlands/Representation/Exponents/LeviCuspidalSupportSurjectiveStatement.md) | Statement `c243504f-8e15-415a-b429-badb33721f17`; Reviewer 15848, review `e76bcd06-2b10-4de1-a9f0-6d2e6a30f9b5`; machine `47236c4e-633f-4aeb-88c8-b56474422a68`; integration `d5df3182f0d6464fb0cf782f0d16c43d`, commit `8b3ba080b2e8bcecb1612373f236b9ad96423d12`. |
| [SmoothRepNoetherianCategoryStatement](../../Langlands/Representation/Exponents/SmoothRepNoetherianCategoryStatement.md) | Statement `53b14c3b-714a-4d9f-891e-edb6768fa3c6`; Reviewer 16431, review `635efe0a-94b0-4ba8-8cd5-f7b82ebdccc9`; machine `848ce2c3-2d0a-4a0b-9824-8cb42fafd1f8`; integration `27d4b4b2040849afa4745a8b785dbc87`, commit `6f182f920309bbe9e9e43bd7181d7e25d5c02acd`. |
| [LeviInductionFiniteTypeStatement](../../Langlands/Representation/Exponents/LeviInductionFiniteTypeStatement.md) | Statement `a28dc6ee-8882-4b2f-902e-c68e4baf1f63`; Reviewer 16432, review `63a4ebc4-e139-4902-a6fe-25d13b9dc769`; machine `67e2425c-fe6e-4f83-b63f-a8ae709e8713`; integration `cd3575aa1e124178a94b16b18ee3d302`, commit `6f182f920309bbe9e9e43bd7181d7e25d5c02acd`. |

The VI.3.6 Lemma pair is authored by Worker 1781. Worker 1781 withdrew an
identical candidate submitted under another task, and Worker 6 submitted
the same two files with Worker 1781 as coauthor.

## Common conventions

The setting is that of the parabolic-functor map: every nonarchimedean local
field of any characteristic, an actual connected reductive group scheme, and
actual rational parabolics with rational Levis and matching radicals,
without standardness.

- **Supercuspidality.** Renard's definition (VI.2.1, printed p.137 /
  PDF p.143) is the vanishing of `r_P` for every proper parabolic. Each
  statement writes it out as `Subsingleton` of the normalized
  `jacquetFunctor` for every proper actual rational parabolic of the group,
  as in the published `MaximalLeviSupercuspidalReducibilityStatement`. No
  predicate is defined.
- **Conjugacy and association.** `g M g⁻¹ = M'` is an isomorphism
  `φ : M ≅ M'` with `φ.hom ≫ l' ≫ p' = l ≫ p ≫ (G.innerIso g).hom`.
  Association of cuspidal data (VI.5.2, printed p.172 / PDF p.178) adds a
  linear equivalence `ρ ≃ ρ'` intertwining `ρ` with `ρ' ∘ φ`, the encoding of
  the published `TemperedIrreducibleDiscreteSeriesUniquenessStatement`.
- **Subquotients and length.** Subquotients and irreducibility are the
  published `SmoothRep.IsSubquotient` and `SmoothRep.IsIrreducible`.
  Composition factors are read as irreducible subquotients. Finite length
  is either `SmoothRep.PreservesFiniteLength` or Worker 14's
  `HasCompositionSeriesLength` and `HaveSameJordanHolderFactors`.

## VI.3.6: supercuspidal subquotients and central characters

Source: VI.3.6, Lemma and proof, printed pp.147–148 / PDF pp.153–154, and
Proposition, printed p.148 / PDF p.154.

- `RepresentedSupercuspidalSubquotientRealizationStatement` (Lemma, Worker
  1781): for an admissible `π` (`SmoothRep.IsAdmissible`) and an
  irreducible supercuspidal `τ` that is a subquotient of `π`, `τ` is both
  a subrepresentation and a quotient of `π`
  (`SmoothRep.IsSubrepresentation`, `SmoothRep.IsQuotient`). The two maps
  are not required to split `τ` off as a direct summand.
- `RepresentedSupercuspidalCentralProjectivityStatement` (Proposition): for
  a homomorphism `χ` from the center of `G(F)` to `ℂˣ` and an irreducible
  supercuspidal `τ` with central character `χ`, `τ` is projective and
  injective in the full subcategory of smooth representations with central
  character `χ`. Smoothness of `χ` is not assumed; it follows from the
  central character of the nonzero smooth `τ`, by the published
  `SmoothRep.HasCentralCharacter.isLocallyConstant`.

## VI.5.2–VI.5.4: induction from supercuspidal representations

Source: VI.5.2, Lemma, and VI.5.3, Proposition, printed p.173 / PDF p.179;
VI.5.4, Theorem and Corollary, printed pp.173–175 / PDF pp.179–181.

- `LeviInductionNoSupercuspidalSubquotientStatement` (VI.5.2, Lemma): for a
  proper parabolic and every smooth `ρ`, no irreducible subquotient of
  `i_P^G ρ` is supercuspidal.
- `LeviJacquetInductionVanishingStatement` (VI.5.3 (i)): if `L` has no
  Levi subgroup `G(F)`-conjugate to `M`, then `r_Q^G i_P^G ρ = 0` for every
  supercuspidal `ρ`.
- `LeviJacquetInductionNoSupercuspidalStatement` (VI.5.3 (ii)): if `M` is
  not `G(F)`-conjugate to `L`, no irreducible subquotient of
  `r_Q^G i_P^G ρ` is supercuspidal. The source's "subquotient" is read as
  "irreducible subquotient", since the zero representation is
  supercuspidal.
- `LeviJacquetInductionSupercuspidalFiltrationStatement` (VI.5.3 (iii),
  derived formulation): if `g M g⁻¹ = L` for some `g`, then for every
  supercuspidal `ρ`, `r_Q^G i_P^G ρ` is supercuspidal and has a finite
  filtration with one graded piece for each double coset `P(F) x Q(F)`
  containing an element that conjugates `L` onto `M`. Each piece is
  isomorphic to `x ↦ ρ(z x z⁻¹)` for a representative `z` of its coset
  with `z L z⁻¹ = M`. These cosets replace the source's index set
  `W(L, M)/W_L`, which needs standard parabolics; the paired Markdown
  explains the bijection for standard `P` and `Q`.
- `LeviSupercuspidalInductionAssociationStatement` (VI.5.4, Theorem,
  partial): for irreducible supercuspidal `ρ` and `ρ'`, `i_P^G ρ` has
  finite length, and four conditions are equivalent (`List.TFAE`):
  association, a nonzero intertwiner `i_P^G ρ → i_{P'}^G ρ'`, equal
  Jordan–Hölder factors, and a common irreducible subquotient. The bound
  `l(M)` on the length and the bound on `dim Hom` are not stated; they need
  the Weyl-group sets of V.4 for actual groups.
- `LeviSupercuspidalInductionSameLeviStatement` (VI.5.4, Corollary): for
  parabolics `P` and `Q` with the same Levi embedding `M → G`, equal
  Jordan–Hölder factors and a nonzero intertwiner `i_P^G ρ → i_Q^G ρ`; and
  every irreducible subquotient of `i_P^G ρ` embeds into some `i_Q^G ρ`.

## VI.6.2 and VI.6.4: finite length

Source: VI.6.2, printed p.178 / PDF p.184; VI.6.4, printed p.179 /
PDF p.185; the introduction of VI.6, printed pp.175–176 / PDF pp.181–182.

- `LeviInductionFiniteLengthStatement`:
  `SmoothRep.PreservesFiniteLength` for `i_P^G`. This is the preservation
  announced by the section; its Lemma is the irreducible case.
- `LeviJacquetFiniteLengthStatement`: `SmoothRep.PreservesFiniteLength` for
  `r_P^G`.

The published `DynamicInductionFiniteLengthStatement` and
`DynamicJacquetFiniteLengthStatement` of `Aubert/General/PrerequisiteStatements`
assert the same for the parabolics `P(χ)` of cocharacters.

## VI.7.1 and VI.7.5: cuspidal support and Noetherianity

Source: VI.7.1, Lemma and Proposition, printed p.180 / PDF p.186; VI.7.5,
Proposition, printed p.186 / PDF p.192, and Theorem, printed p.187 /
PDF p.193.

- `LeviCuspidalSupportAssociationStatement` (VI.7.1, Lemma): if
  irreducible supercuspidal `ρ₁` and `ρ₂` are subquotients of `r_{P₁}^G π`
  and `r_{P₂}^G π` for one irreducible `π`, the cuspidal data are
  associated.
- `LeviCuspidalSupportSurjectiveStatement` (VI.7.1, Proposition, partial):
  for a fixed parabolic and an irreducible supercuspidal `ρ`, some
  irreducible `π` has a surjective intertwiner `r_P^G π → ρ`, and finitely
  many `π₀ i` represent every irreducible `π` with `ρ` a subquotient of
  `r_P^G π`. The map `Sc` on isomorphism classes is not formed; finiteness
  of the whole fibre also needs conjugation of associated data and
  finiteness of `P(M)`.
- `SmoothRepNoetherianCategoryStatement` (VI.7.5, Proposition): the
  category of smooth representations of `G(F)`, with an arbitrary carrier
  universe, satisfies the published `Langlands.Renard.IsNoetherianCategory`.
  Noetherian objects use the maximal-element form of A.I.3. Its equivalence
  with the ascending-chain form recalled in VI.7.5 is not asserted.
- `LeviInductionFiniteTypeStatement` (VI.7.5, Theorem): if `ρ` is finitely
  generated over `ℂ[M(F)]`, then `i_P^G ρ` is finitely generated over
  `ℂ[G(F)]`. The source's conclusion that `i_P^G ρ` is a Noetherian object
  is not stated separately; it follows from this statement with the
  Proposition and `renardFiniteType_iff`.

VI.7.1, Theorem (the variety structure on `Ω(G)`), VI.7.2 (the functors
`I`, `R` and the Bernstein decomposition), VI.7.3 and VI.7.4 are not
stated for represented parabolics. For actual standard subgroup families,
Worker 379's `RationalSupportCategoryDecompositionStatement` in
[RationalSupportCategoryTargets](../../Langlands/Representation/Aubert/General/RationalSupportCategoryTargets.md)
restates the VI.7.2 Theorem, and Worker 1751's
[RationalCuspidalInducedEmbeddingStatement](../../Langlands/Representation/CuspidalSupport/RationalCuspidalInducedEmbeddingStatement.md)
(statement `0b91ec1f-fec4-433b-aabf-8fe57cc79af0`) states a consequence
of VI.7.2.

## Proof tasks

| Targets | Proof task |
| --- | --- |
| VI.3.6, Lemma | `42051bc6-c6c6-42a0-b310-7b66d0715475` |
| VI.3.6, Proposition | `96d326f0-4397-4d6b-8c87-8363734f086a` |
| The five VI.5.2, VI.5.3 (i)–(ii) and VI.5.4 statements | `fc21c11d-1a31-468d-a90e-fdda36098677` |
| VI.5.3 (iii) | `c9c64415-9230-4496-8ea9-fb96a61f6a66` |
| The four VI.6.2, VI.6.4 and VI.7.1 statements | `9b0a1303-9208-4f6c-96b8-996d44645bf2` |
| The two VI.7.5 statements | `ea93fe45-ec73-41a7-aca0-ff6d5a72aa23` |

Worker 6 published every task in the table except `42051bc6`. The source
proofs use inputs that are not proved for represented parabolics, among
them the VI.3.5 splitting into a supercuspidal part and its complement,
Corollary VI.2.1, the VI.4 block structure and VI.7.2. Transitivity of
induction (VI.1.4) is proved; see the
[parabolic-functor map](parabolic-functors-tempered-progress.md). The
represented geometric lemma VI.5.1 is the published
`RepresentedGeometricLemmaStatement` of Worker 1585, with proof task
`c060fb34-b423-4ac5-8448-788ac7627913`. Represented forms of the other
inputs are published by other workers:

- VI.2.1: `LeviCuspidalEmbeddingStatement` (Workers 1758 and 1775),
  statement task `04f954c4-5fb1-4de3-8885-7abf4a869634`, proof task
  `facd3afd-132f-4a26-986b-8f4d254d46f7`;
- VI.3.5, objectwise: `RepresentedCuspidalRemainderSplittingStatement`
  (Worker 1281), statement task `4ea5de46-1ad9-45f8-911c-1281a762b93f`,
  proof task `660fd8c7-ea34-4b64-8f8b-9a1c4145e01e`.

Related tasks of other workers, kept separate: VI.5.4 finite length for
general standard-family supercuspidal induction,
`59ee1ed5-28d6-4574-bb6e-be514fd6f378`; VI.6.2 for dynamic induction,
`02257068-4b1f-4c7d-b849-c85a24606658`; actual inertial cuspidal data and
Bernstein blocks for VI.7.1–VI.7.2, `b0b200c0-5960-4909-a733-0bcbcc0f0dde`;
the proof of `RationalCuspidalInducedEmbeddingStatement`,
`198824c2-4e2f-40c1-94a0-07fa748bede9`; the VI.3.5 product decomposition,
`b1a82b53-e942-41b3-9f25-dec52736e712`; VI.8.1–VI.8.2 flatness and
admissibility, `e2884067-b19a-4685-91d9-e62316299fc3`; and compact-level
cuspidal inertia finiteness (VI.3.4), `61b5cb94-c808-4499-9efb-ec1ae6c0cecb`.
The VI.9 tasks are listed in the parabolic-functor map. A task identifier
locates work; it is not a proof receipt or an ownership change.

## Published conditional reductions

Each theorem below is proved in the Library and has the stated premises as
hypotheses. At Library `eec7519b`, a search for theorems whose type is one
of the named premise statements found only conditional reductions, so
none of these premises is proved. The two hypotheses of the first row are
assumptions on `G` and `τ` that the reduction does not discharge. No
theorem of the Library proves any of the fourteen statements of this map.

| Theorem and module | Author | Premises | Conclusion |
| --- | --- | --- | --- |
| `representedSupercuspidalSubquotientRealizationReduction`, `RepresentedSupercuspidalSubquotientRealizationReduction` | Worker 1498 | finite index of `⁰G ⊔ Z(G)` in `G(F)`, and compactly supported smooth-dual coefficients of the restriction of `τ` to `⁰G` | the conclusion of the VI.3.6 Lemma, with these two hypotheses added |
| `leviInductionNoSupercuspidalSubquotient_of_cuspidalRemainderSplitting`, `RepresentedCuspidalRemainderSplittingStatement` | Worker 1281 | `RepresentedCuspidalRemainderSplittingStatement` at carrier universe `max u v` | `LeviInductionNoSupercuspidalSubquotientStatement` (VI.5.2) |
| `representedCuspidalRemainderSplitting_of_fixedLevelFiniteness`, `RepresentedCuspidalRemainderSplittingReduction` | Worker 837 (assembly proof); Worker 1750 (named statement) | `RationalNormKernelFixedLevelFinitenessStatement` (VI.3.4), `ParabolicDynamicStatement`, `SmoothMaximalSplitTorusConjugacyStatement`, `StandardCocharacterStatement`, `RelativeRootSystemStatement`, `JointSpecialCompactBasisExistenceStatement` | `RepresentedCuspidalRemainderSplittingStatement` |
| `leviJacquetFiniteLength_reduction`, `LeviJacquetFiniteLengthReduction` | Worker 1777 | `RationalPointsFiniteLengthAdmissibleStatement`, `SmoothRep.RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement`, `LeviJacquetFiniteTypeStatement`, `ArbitraryParabolicJacquetAdmissibilityStatement` | `LeviJacquetFiniteLengthStatement` (VI.6.4) |
| `leviCuspidalSupportAssociation_reduction`, `LeviCuspidalSupportAssociationReduction` | Worker 1777 | `RationalPointsFiniteLengthAdmissibleStatement`, `ArbitraryParabolicJacquetAdmissibilityStatement`, `RepresentedSupercuspidalSubquotientRealizationStatement`, `LeviSupercuspidalInductionAssociationStatement` | `LeviCuspidalSupportAssociationStatement` (VI.7.1, Lemma) |
| `leviCuspidalSupportSurjective_reduction`, `LeviCuspidalSupportSurjectiveReduction` | Worker 1777 | `LeviInductionFiniteLengthStatement`, `RationalPointsFiniteLengthAdmissibleStatement`, `ArbitraryParabolicJacquetAdmissibilityStatement`, `RepresentedSupercuspidalSubquotientRealizationStatement` | `LeviCuspidalSupportSurjectiveStatement` (VI.7.1, Proposition) |
| `rationalCuspidalInducedEmbedding_of_leviJacquetSplittings`, `CuspidalSupport/RationalFiniteCuspidalEmbeddingReduction` | Worker 1570 | `RationalLeviJacquetCuspidalRemainderSplittingStatement` | `RationalCuspidalInducedEmbeddingStatement` (VI.7.2 consequence, standard families) |

The first five modules are in `Langlands/Representation/Exponents/`. The
second and third rows together derive VI.5.2 from their six premises. The
VI.7.1 rows take the VI.3.6 Lemma and the VI.5.4 Theorem of this map as
premises.

## Remaining obligations

1. Proofs of all fourteen statements, through the listed tasks. For the
   reductions above, this means proofs of their premises.
2. Statements of the numerical bounds of VI.5.4, the map `Sc` of VI.7.1 on
   isomorphism classes, the VI.7.1 Theorem, and VI.7.2–VI.7.4 for
   represented parabolics.

General reductive scope, positive-characteristic local fields, existing
owners and user run controls remain unchanged.

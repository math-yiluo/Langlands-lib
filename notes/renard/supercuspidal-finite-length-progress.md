# Renard VI.3.6, VI.5.2–VI.5.4, VI.6.2, VI.6.4, VI.7.1 and VI.7.5: supercuspidal induction, finite length, cuspidal support and Noetherianity

This focused map, dated 6–7 November 2026, supplements the
[whole-book ledger](coverage.md) and continues the
[parabolic-functor and tempered map](parabolic-functors-tempered-progress.md),
whose common setting, normalized functors `leviInductionFunctor` (`i_P^G`)
and `leviJacquetFunctor` (`r_P^G`) and Frobenius-reciprocity and exactness
statements are used below. It records fourteen statements of the Library.
None of these publications proves a proposition. The map also lists
published conditional reductions, which derive some of the statements from
other statements that were not proved at the Library commit named below. The VI.4 statements are mapped separately
in the [supercuspidal block and center map](supercuspidal-block-center-progress.md).
The map is not a complete inventory of VI.3, VI.5, VI.6 or VI.7, and
supplies no new Lean proof.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF page numbers are one-based and equal printed page numbers plus six.
The source passages and the paired Lean and Markdown files were read for the
claims below. By SHA256, all twenty-eight primary files equal the files at
Library `eec7519b852f9097606377425625fd5794c87f71`. A fresh Lean check at
that Library of fifty modules, including these fourteen, had zero
diagnostics.

## The fourteen statements

A statement does not prove its proposition. All declarations are in namespace
`Langlands.Aubert.General.RepresentedParabolic` under
`Langlands/Representation/Exponents/`. The last column gives the proof the
Library has now.

| Pair and exact declaration | First appeared at Library commit | Proof in the Library |
| --- | --- | --- |
| [RepresentedSupercuspidalSubquotientRealizationStatement](../../Langlands/Representation/Exponents/RepresentedSupercuspidalSubquotientRealizationStatement.md) | `334440350ec029c1bf78b7801689e1a2b21079c6` | not proved |
| [RepresentedSupercuspidalCentralProjectivityStatement](../../Langlands/Representation/Exponents/RepresentedSupercuspidalCentralProjectivityStatement.md) | `6f182f920309bbe9e9e43bd7181d7e25d5c02acd` | not proved; derived from further hypotheses by `representedSupercuspidalCentralProjectivity_of_structure` (`Langlands/Representation/Exponents/RepresentedSupercuspidalCentralProjectivityReduction.lean`) |
| [LeviInductionNoSupercuspidalSubquotientStatement](../../Langlands/Representation/Exponents/LeviInductionNoSupercuspidalSubquotientStatement.md) | `86cf8f8984679ba48ded6fa152c55ec38b532d97` | not proved |
| [LeviJacquetInductionVanishingStatement](../../Langlands/Representation/Exponents/LeviJacquetInductionVanishingStatement.md) | `86cf8f8984679ba48ded6fa152c55ec38b532d97` | proved: `leviJacquetInductionVanishing` (`Langlands/Representation/Exponents/LeviJacquetInductionVanishingProof.lean`) |
| [LeviJacquetInductionNoSupercuspidalStatement](../../Langlands/Representation/Exponents/LeviJacquetInductionNoSupercuspidalStatement.md) | `86cf8f8984679ba48ded6fa152c55ec38b532d97` | not proved; derived from further hypotheses by `leviJacquetInductionNoSupercuspidal_of_geometricLemma` (`Langlands/Representation/Exponents/LeviJacquetNonSupercuspidalReduction.lean`) |
| [LeviJacquetInductionSupercuspidalFiltrationStatement](../../Langlands/Representation/Exponents/LeviJacquetInductionSupercuspidalFiltrationStatement.md) | `334440350ec029c1bf78b7801689e1a2b21079c6` | proved: `leviJacquetInductionSupercuspidalFiltration` (`Langlands/Representation/Exponents/LeviJacquetInductionSupercuspidalFiltrationProof.lean`) |
| [LeviSupercuspidalInductionAssociationStatement](../../Langlands/Representation/Exponents/LeviSupercuspidalInductionAssociationStatement.md) | `8b3ba080b2e8bcecb1612373f236b9ad96423d12` | not proved |
| [LeviSupercuspidalInductionSameLeviStatement](../../Langlands/Representation/Exponents/LeviSupercuspidalInductionSameLeviStatement.md) | `8b3ba080b2e8bcecb1612373f236b9ad96423d12` | not proved |
| [LeviInductionFiniteLengthStatement](../../Langlands/Representation/Exponents/LeviInductionFiniteLengthStatement.md) | `8b3ba080b2e8bcecb1612373f236b9ad96423d12` | not proved |
| [LeviJacquetFiniteLengthStatement](../../Langlands/Representation/Exponents/LeviJacquetFiniteLengthStatement.md) | `8b3ba080b2e8bcecb1612373f236b9ad96423d12` | not proved |
| [LeviCuspidalSupportAssociationStatement](../../Langlands/Representation/Exponents/LeviCuspidalSupportAssociationStatement.md) | `8b3ba080b2e8bcecb1612373f236b9ad96423d12` | not proved |
| [LeviCuspidalSupportSurjectiveStatement](../../Langlands/Representation/Exponents/LeviCuspidalSupportSurjectiveStatement.md) | `8b3ba080b2e8bcecb1612373f236b9ad96423d12` | not proved |
| [SmoothRepNoetherianCategoryStatement](../../Langlands/Representation/Exponents/SmoothRepNoetherianCategoryStatement.md) | `6f182f920309bbe9e9e43bd7181d7e25d5c02acd` | not proved; derived from further hypotheses by `smoothRepNoetherianCategory_of_inputs` (`Langlands/Representation/Exponents/SmoothRepNoetherianReduction.lean`) |
| [LeviInductionFiniteTypeStatement](../../Langlands/Representation/Exponents/LeviInductionFiniteTypeStatement.md) | `6f182f920309bbe9e9e43bd7181d7e25d5c02acd` | not proved; derived from further hypotheses by `leviInductionFiniteType_of_inputs` (`Langlands/Representation/Exponents/LeviInductionFiniteTypeReduction.lean`) |

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
  is either `SmoothRep.PreservesFiniteLength` or the `HasCompositionSeriesLength` and `HaveSameJordanHolderFactors`.

## VI.3.6: supercuspidal subquotients and central characters

Source: VI.3.6, Lemma and proof, printed pp.147–148 / PDF pp.153–154, and
Proposition, printed p.148 / PDF p.154.

- `RepresentedSupercuspidalSubquotientRealizationStatement` (Lemma): for an admissible `π` (`SmoothRep.IsAdmissible`) and an
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
the `RationalSupportCategoryDecompositionStatement` in
[RationalSupportCategoryTargets](../../Langlands/Representation/Aubert/General/RationalSupportCategoryTargets.md)
restates the VI.7.2 Theorem, and the [RationalCuspidalInducedEmbeddingStatement](../../Langlands/Representation/CuspidalSupport/RationalCuspidalInducedEmbeddingStatement.md)
states a consequence
of VI.7.2.

## Inputs of the source proofs

The source proofs use inputs that were not proved for represented parabolics
at Library `eec7519b`, among them the VI.3.5 splitting into a supercuspidal
part and its complement, Corollary VI.2.1, the VI.4 block structure and
VI.7.2. Transitivity of induction (VI.1.4) is proved; see the
[parabolic-functor map](parabolic-functors-tempered-progress.md). The
represented geometric lemma VI.5.1 is the published
`RepresentedGeometricLemmaStatement` (now: proved: `representedGeometricLemma` (`Langlands/Representation/Geometric/RepresentedGeometricLemmaProof.lean`)). Represented forms of the other
inputs are published:

- VI.2.1: `LeviCuspidalEmbeddingStatement` (now: proved: `leviCuspidalEmbedding` (`Langlands/Representation/Exponents/LeviCuspidalEmbeddingProof.lean`));
- VI.3.5, objectwise: `RepresentedCuspidalRemainderSplittingStatement`
  (now: not proved; derived from further hypotheses by `representedCuspidalRemainderSplitting_of_fixedLevelFiniteness` (`Langlands/Representation/Exponents/RepresentedCuspidalRemainderSplittingReduction.lean`)).

Related topics treated elsewhere, not in this map: VI.5.4 finite length for
general standard-family supercuspidal induction; VI.6.2 for dynamic
induction; actual inertial cuspidal data and Bernstein blocks for
VI.7.1–VI.7.2; the proof of `RationalCuspidalInducedEmbeddingStatement` (now:
not proved; derived from further hypotheses by `rationalCuspidalInducedEmbedding_of_leviJacquetSplittings` (`Langlands/Representation/CuspidalSupport/RationalFiniteCuspidalEmbeddingReduction.lean`)); the VI.3.5 product decomposition; VI.8.1–VI.8.2 flatness and
admissibility; and compact-level cuspidal inertia finiteness (VI.3.4). The
VI.9 statements are listed in the parabolic-functor map.

## Published conditional reductions

Each theorem below is proved in the Library and has the stated premises as
hypotheses. At Library `eec7519b`, a search for theorems whose type is one
of the named premise statements found only conditional reductions, so
none of these premises is proved. The two hypotheses of the first row are
assumptions on `G` and `τ` that the reduction does not discharge. At that
commit no theorem of the Library proved any of the fourteen statements of
this map; for their proofs now see the table of the fourteen statements.

| Theorem and module | Premises | Conclusion |
| --- | --- | --- |
| `representedSupercuspidalSubquotientRealizationReduction`, `RepresentedSupercuspidalSubquotientRealizationReduction` | finite index of `⁰G ⊔ Z(G)` in `G(F)`, and compactly supported smooth-dual coefficients of the restriction of `τ` to `⁰G` | the conclusion of the VI.3.6 Lemma, with these two hypotheses added |
| `leviInductionNoSupercuspidalSubquotient_of_cuspidalRemainderSplitting`, `RepresentedCuspidalRemainderSplittingStatement` | `RepresentedCuspidalRemainderSplittingStatement` at carrier universe `max u v` | `LeviInductionNoSupercuspidalSubquotientStatement` (VI.5.2) |
| `representedCuspidalRemainderSplitting_of_fixedLevelFiniteness`, `RepresentedCuspidalRemainderSplittingReduction` | `RationalNormKernelFixedLevelFinitenessStatement` (VI.3.4), `ParabolicDynamicStatement`, `SmoothMaximalSplitTorusConjugacyStatement`, `StandardCocharacterStatement`, `RelativeRootSystemStatement`, `JointSpecialCompactBasisExistenceStatement` | `RepresentedCuspidalRemainderSplittingStatement` |
| `leviJacquetFiniteLength_reduction`, `LeviJacquetFiniteLengthReduction` | `RationalPointsFiniteLengthAdmissibleStatement`, `SmoothRep.RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement`, `LeviJacquetFiniteTypeStatement`, `ArbitraryParabolicJacquetAdmissibilityStatement` | `LeviJacquetFiniteLengthStatement` (VI.6.4) |
| `leviCuspidalSupportAssociation_reduction`, `LeviCuspidalSupportAssociationReduction` | `RationalPointsFiniteLengthAdmissibleStatement`, `ArbitraryParabolicJacquetAdmissibilityStatement`, `RepresentedSupercuspidalSubquotientRealizationStatement`, `LeviSupercuspidalInductionAssociationStatement` | `LeviCuspidalSupportAssociationStatement` (VI.7.1, Lemma) |
| `leviCuspidalSupportSurjective_reduction`, `LeviCuspidalSupportSurjectiveReduction` | `LeviInductionFiniteLengthStatement`, `RationalPointsFiniteLengthAdmissibleStatement`, `ArbitraryParabolicJacquetAdmissibilityStatement`, `RepresentedSupercuspidalSubquotientRealizationStatement` | `LeviCuspidalSupportSurjectiveStatement` (VI.7.1, Proposition) |
| `rationalCuspidalInducedEmbedding_of_leviJacquetSplittings`, `CuspidalSupport/RationalFiniteCuspidalEmbeddingReduction` | `RationalLeviJacquetCuspidalRemainderSplittingStatement` | `RationalCuspidalInducedEmbeddingStatement` (VI.7.2 consequence, standard families) |

The first five modules are in `Langlands/Representation/Exponents/`. The
second and third rows together derive VI.5.2 from their six premises. The
VI.7.1 rows take the VI.3.6 Lemma and the VI.5.4 Theorem of this map as
premises.

## Remaining obligations

1. Proofs of those of the fourteen statements that the Library does not
   prove (see their table). For the reductions above, this means proofs of
   their premises.
2. Statements of the numerical bounds of VI.5.4, the map `Sc` of VI.7.1 on
   isomorphism classes, the VI.7.1 Theorem, and VI.7.2–VI.7.4 for
   represented parabolics.

General reductive scope and positive-characteristic local fields remain
unchanged.

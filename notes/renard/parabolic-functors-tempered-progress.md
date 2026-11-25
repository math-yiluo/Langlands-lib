# Renard VI.1, VI.9.4, VI.9.6–VI.9.7, VII.1.3 and VII.2.2–VII.2.6: parabolic functors and tempered representations

This focused map, dated 6 November 2026 and updated 7 November 2026,
supplements the [whole-book ledger](coverage.md) and continues the
[actual-root and exponent source map](root-exponent-tempered-progress.md),
whose represented-parabolic induction, Levi-point transport, temperedness
predicate and VII.1.1, Casselman and VII.2.1 Remark 2 statements are used
below. It records twenty-two pairs of the Library, one
definition and twenty-one statements. None of these
pairs proves a proposition. It also lists the published proofs of
five of the statements and published conditional
reductions; the table of pairs gives the proof the Library has now for each
statement. The map is not a complete inventory of VI.1, VI.9, VII.1 or
VII.2, and supplies no new Lean proof. The
[supercuspidal induction and finite-length map](supercuspidal-finite-length-progress.md)
continues it for VI.3.6 and VI.5.2–VI.7.5, and the
[supercuspidal block map](supercuspidal-block-center-progress.md) for VI.4.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF page numbers are one-based and equal printed page numbers plus six.
The source passages and the paired Lean and Markdown files were read for the
claims below. By SHA256, all forty primary files equal the files at Library
`eec7519b852f9097606377425625fd5794c87f71`. A fresh Lean check at that
Library of fifty modules, including these twenty, had zero diagnostics. The
two VI.9.4 statements, added 7 November 2026, entered the Library later:
their four primary files equal the files at Libraries
`2816ea5d81e2fb9b0512bd1d8dec2ad7797026fd` and
`8b14de0b5103d5fc1e615f094904129bf8cfe3a3`, and a fresh Lean check of both
modules at the latter had zero diagnostics.

## In the Library

A definition covers its construction and intrinsic laws; a statement does
not prove its proposition. The last column gives the proof the Library has
now.

| Pair and exact declaration | Kind | First appeared at Library commit | Proof in the Library |
| --- | --- | --- | --- |
| [LeviFrobeniusReciprocityStatement](../../Langlands/Representation/Exponents/LeviFrobeniusReciprocityStatement.md), `Langlands.Aubert.General.RepresentedParabolic.LeviFrobeniusReciprocityStatement` | statement | `819ea8d4de6f7dde4b0d7f879f58af405e135acf` | proved: `leviFrobeniusReciprocity` (`Langlands/Representation/Exponents/LeviFrobeniusReciprocityProof.lean`) |
| [LeviParabolicFunctorsExactStatement](../../Langlands/Representation/Exponents/LeviParabolicFunctorsExactStatement.md), `Langlands.Aubert.General.RepresentedParabolic.LeviParabolicFunctorsExactStatement` | statement | `819ea8d4de6f7dde4b0d7f879f58af405e135acf` | proved: `leviParabolicFunctorsExact` (`Langlands/Representation/Exponents/LeviParabolicFunctorsExactProof.lean`) |
| [LeviParabolicFunctorsPreserveLimitsStatement](../../Langlands/Representation/Exponents/LeviParabolicFunctorsPreserveLimitsStatement.md), `Langlands.Aubert.General.RepresentedParabolic.LeviParabolicFunctorsPreserveLimitsStatement` | statement | `73016647c403b942bebe18fad4e569a83c342b52` | proved: `leviParabolicFunctorsPreserveLimits` (`Langlands/Representation/Exponents/LeviParabolicFunctorsPreserveLimitsProof.lean`) |
| [LeviJacquetFiniteTypeStatement](../../Langlands/Representation/Exponents/LeviJacquetFiniteTypeStatement.md), `Langlands.Aubert.General.RepresentedParabolic.LeviJacquetFiniteTypeStatement` | statement | `73016647c403b942bebe18fad4e569a83c342b52` | proved: `leviJacquetFiniteType` (`Langlands/Representation/Exponents/LeviJacquetFiniteTypeProof.lean`) |
| [LeviSecondAdjointnessStatement](../../Langlands/Representation/Exponents/LeviSecondAdjointnessStatement.md), `Langlands.Aubert.General.RepresentedParabolic.LeviSecondAdjointnessStatement` | statement | `08e8de28d111b66b088500c8ad1b0bd0f947991d` | not proved; derived from further hypotheses by `leviSecondAdjointness_of_structure` (`Langlands/Representation/Exponents/LeviSecondAdjointnessStructure.lean`) |
| [LeviJacquetContragredientStatement](../../Langlands/Representation/Exponents/LeviJacquetContragredientStatement.md), `Langlands.Aubert.General.RepresentedParabolic.LeviJacquetContragredientStatement` | statement | `08e8de28d111b66b088500c8ad1b0bd0f947991d` | not proved; derived from further hypotheses by `leviJacquetContragredient_of_structure` (`Langlands/Representation/Exponents/LeviJacquetContragredientStructure.lean`) |
| [MaximalLeviSupercuspidalReducibilityStatement](../../Langlands/Representation/Exponents/MaximalLeviSupercuspidalReducibilityStatement.md), `Langlands.Aubert.General.RepresentedParabolic.MaximalLeviSupercuspidalReducibilityStatement` | statement | `542eaca02a9f2d14f175497b7bf6459436ac5c6d` | not proved; derived from further hypotheses by `maximalLeviSupercuspidalReducibility_of_unitary` (`Langlands/Representation/Exponents/MaximalLeviTwistReduction.lean`) |
| [LeviInductionNormalizedTemperedStatement](../../Langlands/Representation/Exponents/LeviInductionNormalizedTemperedStatement.md), `Langlands.Aubert.General.RepresentedParabolic.LeviInductionNormalizedTemperedStatement` | statement | `bc859155612cc8ca34e8e25175ce2f7775c217dc` | proved: `leviInductionNormalizedTempered` (`Langlands/Representation/Exponents/LeviInductionNormalizedTemperedProof.lean`) |
| [ArbitraryParabolicUnitaryJacquetPart](../../Langlands/Representation/Exponents/ArbitraryParabolicUnitaryJacquetPart.md), `Langlands.Aubert.General.RepresentedParabolic.unitaryJacquetPart` | definition | `bc859155612cc8ca34e8e25175ce2f7775c217dc` | — |
| [UnitaryJacquetPartTemperedStatement](../../Langlands/Representation/Exponents/UnitaryJacquetPartTemperedStatement.md), `Langlands.Aubert.General.RepresentedParabolic.UnitaryJacquetPartTemperedStatement` | statement | `50126e1b2b20b62d408b52dc3552f01089dd1d11` | proved: `unitaryJacquetPartTempered` (`Langlands/Representation/Exponents/UnitaryJacquetPartTemperedProof.lean`) |
| [TemperedJacquetUnitaryRestrictionStatement](../../Langlands/Representation/Exponents/TemperedJacquetUnitaryRestrictionStatement.md), `Langlands.Aubert.General.RepresentedParabolic.TemperedJacquetUnitaryRestrictionStatement` | statement | `50126e1b2b20b62d408b52dc3552f01089dd1d11` | proved: `temperedJacquetUnitaryRestriction` (`Langlands/Representation/Exponents/TemperedJacquetUnitaryRestrictionProof.lean`) |
| [TemperedInductionUnitaryReciprocityStatement](../../Langlands/Representation/Exponents/TemperedInductionUnitaryReciprocityStatement.md), `Langlands.Aubert.General.RepresentedParabolic.TemperedInductionUnitaryReciprocityStatement` | statement | `73016647c403b942bebe18fad4e569a83c342b52` | proved: `temperedInductionUnitaryReciprocity` (`Langlands/Representation/Exponents/TemperedInductionUnitaryReciprocityProof.lean`) |
| [TemperedSquareIntegrableUnitaryPartStatement](../../Langlands/Representation/Exponents/TemperedSquareIntegrableUnitaryPartStatement.md), `Langlands.Aubert.General.RepresentedParabolic.TemperedSquareIntegrableUnitaryPartStatement` | statement | `50126e1b2b20b62d408b52dc3552f01089dd1d11` | not proved |
| [TemperedGeometricLemmaStatement](../../Langlands/Representation/Exponents/TemperedGeometricLemmaStatement.md), `Langlands.Aubert.General.RepresentedParabolic.TemperedGeometricLemmaStatement` | statement | `8fb2236bacd54b43eeb9b2fabc30476fee771e05` | proved: `temperedGeometricLemma` (`Langlands/Representation/Exponents/TemperedGeometricLemmaProof.lean`) |
| [TemperedIrreducibleDiscreteSeriesStatement](../../Langlands/Representation/Exponents/TemperedIrreducibleDiscreteSeriesStatement.md), `Langlands.Aubert.General.RepresentedParabolic.TemperedIrreducibleDiscreteSeriesStatement` | statement | `f9c20f3deffa895e672facb4ad0b214541325d76` | not proved; derived from further hypotheses by `temperedIrreducibleDiscreteSeries_of_inputs` (`Langlands/Representation/Exponents/TemperedIrreducibleDiscreteSeriesReduction.lean`) |
| [TemperedIrreducibleDiscreteSeriesUniquenessStatement](../../Langlands/Representation/Exponents/TemperedIrreducibleDiscreteSeriesUniquenessStatement.md), `Langlands.Aubert.General.RepresentedParabolic.TemperedIrreducibleDiscreteSeriesUniquenessStatement` | statement | `f9c20f3deffa895e672facb4ad0b214541325d76` | proved: `temperedIrreducibleDiscreteSeriesUniqueness` (`Langlands/Representation/Exponents/TemperedIrreducibleDiscreteSeriesUniquenessProof.lean`) |
| [TemperedIrreducibleUnitarizableStatement](../../Langlands/Representation/Exponents/TemperedIrreducibleUnitarizableStatement.md), `Langlands.Aubert.General.RepresentedParabolic.TemperedIrreducibleUnitarizableStatement` | statement | `f9c20f3deffa895e672facb4ad0b214541325d76` | not proved; derived from further hypotheses by `temperedIrreducibleUnitarizable_of_discreteSeries` (`Langlands/Representation/Exponents/TemperedIrreducibleDiscreteSeriesReduction.lean`) |
| [LeviParabolicTransitivityStatement](../../Langlands/Representation/Exponents/LeviParabolicTransitivityStatement.md), `Langlands.Aubert.General.RepresentedParabolic.LeviParabolicTransitivityStatement` | statement | `6f182f920309bbe9e9e43bd7181d7e25d5c02acd` | proved: `leviParabolicTransitivity` (`Langlands/Representation/Exponents/LeviParabolicTransitivityProof.lean`) |
| [LeviJacquetOppositePairingStatement](../../Langlands/Representation/Exponents/LeviJacquetOppositePairingStatement.md), `Langlands.Aubert.General.RepresentedParabolic.LeviJacquetOppositePairingStatement` | statement | `334440350ec029c1bf78b7801689e1a2b21079c6` | not proved; derived from further hypotheses in `Langlands/Representation/Exponents/LeviJacquetOppositePairingStructure.lean` |
| [LeviCompletionOppositeJacquetStatement](../../Langlands/Representation/Exponents/LeviCompletionOppositeJacquetStatement.md), `Langlands.Aubert.General.RepresentedParabolic.LeviCompletionOppositeJacquetStatement` | statement | `6f182f920309bbe9e9e43bd7181d7e25d5c02acd` | not proved; derived from further hypotheses by `leviCompletionOppositeJacquet_of_structure` (`Langlands/Representation/Exponents/LeviCompletionStructure.lean`) |
| [StandardFixedVectorSubquotientGenerationStatement](../../Langlands/Representation/Jacquet/StandardFixedVectorSubquotientGenerationStatement.md), `Langlands.Jacquet.StandardFixedVectorSubquotientGenerationStatement` | statement | `2816ea5d81e2fb9b0512bd1d8dec2ad7797026fd` | not proved; derived from further hypotheses by `standardFixedVectorSubquotientGenerationStatement_of_standardIwahori` (`Langlands/Representation/Jacquet/StandardIwahoriDecompositionStatements.lean`) |
| [StandardFixedVectorHeckeEquivalenceStatement](../../Langlands/Representation/Jacquet/StandardFixedVectorHeckeEquivalenceStatement.md), `Langlands.Jacquet.StandardFixedVectorHeckeEquivalenceStatement` | statement | `2816ea5d81e2fb9b0512bd1d8dec2ad7797026fd` | not proved; derived from further hypotheses by `standardFixedVectorHeckeEquivalenceStatement_of_standardIwahori` (`Langlands/Representation/Jacquet/StandardIwahoriDecompositionStatements.lean`) |

The first twenty declarations are in namespace
`Langlands.Aubert.General.RepresentedParabolic` under
`Langlands/Representation/Exponents/`. The two VI.9.4 statements are in
namespace `Langlands.Jacquet` under `Langlands/Representation/Jacquet/`.
The completion definitions used by the VI.9.7 statement are in
[CompactCompletion](../../Langlands/Representation/Smooth/CompactCompletion.md),
namespace `Langlands.CompactCompletion`, submitted in the same candidate
`51570ccf`.

## Common setting

Every statement except the two VI.9.4 statements quantifies over a
nonarchimedean local field `k : Type u` of any characteristic, with `[ValuativeRel k]`, its topology and
`[T2Space k]`, and over an actual connected reductive group scheme `G` over
`Spec k`. The rational points carry the canonical
`RationalPointFamily.pointTopology`; `[LocallyCompactSpace]` and
`[NonarchimedeanGroup]` for that topology are hypotheses. A parabolic datum
is an actual rational parabolic `p : P ⟶ G`, a rational Levi `l : M ⟶ P`
and a matching geometric unipotent radical `r : U ⟶ P` with
`IsIso (subgroupMultiplication l r)`; no standardness is assumed. The Levi
points carry `leviPointTopology`, and their local compactness and
nonarchimedean structure are derived from those of `G(F)`. The two VI.9.4
statements instead quantify over a nonarchimedean local field `F : Type uF`
with `[ValuativeRel F]` and an actual connected reductive `G` whose rational
points carry `rationalPointTopology`, with no local-compactness hypothesis;
their parabolics are the standard ones described in their section.

The functors are the published normalized `leviInductionFunctor`
(`i_P^G`) and `leviJacquetFunctor` (`r_P^G`) of the represented-parabolic
interface. Renard's `δ_P` is the inverse of the usual Haar modulus, so his
twists by `δ_P^{-1/2}` and `δ_P^{1/2}` in (VI.1.2.1)–(VI.1.2.2) are the
published square-root twists. Temperedness is the published derived
predicate `IsNormalizedExponentTempered` of the companion map.

## VI.1.2 and VI.1.3: the normalized functors

Source: VI.1.2, Proposition and Corollary, and VI.1.3, Proposition,
printed p.136 / PDF p.142.

- `LeviFrobeniusReciprocityStatement`: for every smooth `π` of `G(F)` and
  `σ` of `M(F)`, with independent carrier universes, there is a linear
  equivalence from intertwiners `π → i_P^G σ` to intertwiners
  `r_P^G π → σ` sending `F` to `[x] ↦ (F x)(1)`. This is the adjunction
  part of the Proposition, as an explicit bijection.
- `LeviParabolicFunctorsExactStatement`: both functors send every actual
  short exact sequence (`SmoothRep.IsShortExact`) to a short exact sequence.
- `LeviParabolicFunctorsPreserveLimitsStatement`: `i_P^G` preserves limits
  and colimits and `r_P^G` preserves colimits, for diagrams with index
  categories and morphisms in `Type v`. The explicit sizes
  `PreservesLimitsOfSize.{v, v}` and `PreservesColimitsOfSize.{v, v}` are
  needed because the carrier universe of `i_P^G` changes.
- `LeviJacquetFiniteTypeStatement`: if `π` is finitely generated over
  `ℂ[G(F)]`, then `r_P^G π` is finitely generated over `ℂ[M(F)]`. Only the
  normalized assertion is stated.

The unnormalized Theorem of VI.1.1 is not stated separately.

## VI.1.4: transitivity

Source: VI.1.4, the paragraph before the Lemma, the Lemma and its proof,
printed pp.136–137 / PDF pp.142–143.

`LeviParabolicTransitivityStatement` takes three actual rational parabolic
triples: `P = MN` and `Q = LU` in `G`, and `P_L = M N_L` in `L` with the
same Levi group scheme `M`. It assumes `P(F) ⊆ Q(F)`, that `M` sits in `G`
through `P_L ⊂ L ⊂ Q` by the same embedding as through `P`, and
`P_L(F) = L(F) ∩ P(F)`. These hypotheses describe Renard's `L ∩ P`, which
the interface cannot form as an intersection of group schemes. It asserts
natural isomorphisms `i_P^G ≅ i_{P_L}^L ⋙ i_Q^G` and
`r_P^G ≅ r_Q^G ⋙ r_{P_L}^L` of functors on all smooth representations,
for an arbitrary carrier universe. The local compactness and
nonarchimedean structure of `L(F)` are derived, not assumed. The published
`DynamicNestedParabolicTransitivityStatement` and its proof in
`Langlands/Representation/Aubert/General/` are the version for dynamic
parabolics, with the radical decompositions as a visible input.

## VI.9.6: second adjointness and the pairing

Source: VI.9.6, first and second Theorems, printed p.201 / PDF p.207, with
the proof of their equivalence on printed pp.201–202 / PDF pp.207–208; the
Proposition, printed p.202 / PDF p.208, with its proof on printed
pp.202–205 / PDF pp.208–211.

The three statements take a second actual rational parabolic triple
`pbar : Pbar ⟶ G`, `mbar : M ⟶ Pbar`, `nbar : Nbar ⟶ Pbar` with the same
Levi group scheme, and assume `mbar ≫ pbar = m ≫ p` and
`pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)`. These say that the
two triples have the same Levi embedding and that `P(F) ∩ P̄(F) = M(F)`,
which describes the opposite parabolic. Constructing the opposite as actual
group-scheme data is not addressed.

- `LeviSecondAdjointnessStatement`: `Nonempty (i_P^G ⊣ r_{P̄}^G)` as a
  Mathlib adjunction, (VI.9.6.1). Both functors are taken with carriers in
  `Type (max u v)` so that they relate the same two categories.
- `LeviJacquetContragredientStatement`: a natural isomorphism
  `π ↦ r_{P̄}^G(π̃) ≅ π ↦ (r_P^G π)~` of functors on all smooth
  representations with carriers in `Type v`, (VI.9.6.2), with the published
  `SmoothRep.contragredientFunctor`.
- `LeviJacquetOppositePairingStatement` (Proposition): for every smooth
  `π` there is an isomorphism `E : r_{P̄}^G(π̃) ≅ (r_P^G π)~` such that the
  pairing `⟨x, y⟩_P = E(y)(x)` satisfies (VI.9.6.4) and (VI.9.6.5). For
  every split component `A` of `M`, every published
  `ParabolicRootPresentation` of `P` relative to it, and all `v ∈ V` and
  `λ ∈ Ṽ`:
  `⟨r_P^G(π)(t^j)·j_N(v), j_{N̄}(λ)⟩_P = δ_P^{1/2}(t^j) λ(π(t^j)v)` for
  every `t ∈ CocharacterUniformizer.CAstrict` (Renard's `C_A^{++}`) and all
  large `j`; and for some `ε > 0`, depending on `v` and `λ`, the same
  identity holds for every `t` in `CocharacterUniformizer.CAepsilon`
  (Renard's `C_A^+(ε)`). One `E` serves
  every presentation. `E` is not asserted to be natural in `π`, the
  existence of presentations is not asserted, and no implication between
  this statement and `LeviJacquetContragredientStatement` is asserted.

No admissibility, finite length or finite type is assumed. The source
proves (VI.9.6.2) through the pairing (VI.9.6.4), built from the
generalized Jacquet lemma VI.9.1–VI.9.3. That lemma uses Iwahori
decompositions with respect to `P` and `P̄` and contracting elements of the
split component.

The Library has conditional reductions of the two Theorems.
Their theorems are proved and keep the listed statements as hypotheses.

| Theorem and module | Premises | Conclusion |
| --- | --- | --- |
| `leviSecondAdjointness_of_structure`, `LeviSecondAdjointnessStructure` | `ParabolicDynamicStatement`, `OppositeDynamicParabolicUniquenessStatement`, `UniformCompressionStabilizationStatement` at carrier universe `max u v`, `LeviAdjointDeterminantReciprocityStatement`, `RationalReductiveUnimodularityStatement`, `StandardCocharacterStatement`, `ArbitraryParabolicQuotientCompactStatement` | `LeviSecondAdjointnessStatement` |
| `leviJacquetContragredient_of_structure`, `LeviJacquetContragredientStructure` | the first four premises of the previous row, with `UniformCompressionStabilizationStatement` at carrier universe `v` | `LeviJacquetContragredientStatement` |

Each module also proves a variant, ending in
`_of_reflection_centralSplitTorus`, in which
`RelativeRootReflectionExistenceStatement` and
`CentralSplitTorusCharacterStatement` replace
`LeviAdjointDeterminantReciprocityStatement`. The implications are also
published as the named statements `LeviSecondAdjointnessFromInputsStatement`
and `LeviJacquetContragredientFromInputsStatement`, which are proved. Of the
premises, `OppositeDynamicParabolicUniquenessStatement`
is proved, by `Langlands.GroupScheme.oppositeDynamicParabolicUniqueness`.
At Library `eec7519b`, a search for theorems whose
type is one of the other premises found no unconditional proof, only
conditional reductions for some of them. Among these, the internal assembly
`uniformCompressionStabilization_of_nativeStatements` in
`UniformCompressionNativeAssembly` derives
`UniformCompressionStabilizationStatement` from thirteen named Library
statements. One of them is the VI.9.2 Jacquet-family finiteness statement
`RationalSupercuspidalJacquetFamilyFiniteStatement`, which no theorem of the
Library proved at that commit (it is now proved, as
`rationalSupercuspidalJacquetFamilyFinite` in
`Langlands/Representation/Plancherel/UnramifiedRationalJacquetFinitenessProof.lean`); the modules `StandardCompressionGeometry` and
`StandardCuspidalNativeJacquetInputs` also take it only as a hypothesis. The search found no theorem whose type is the pairing
Proposition or the VI.9.7 statement. The Library now proves every premise of
the two reductions in the table except `UniformCompressionStabilizationStatement`,
which it derives only from further hypotheses (for instance
`ParabolicDynamicStatement` is proved as `parabolicDynamic` in
`Langlands/GroupScheme/Absolute/ParabolicDynamicProof.lean`, and
`ArbitraryParabolicQuotientCompactStatement` as
`arbitraryParabolicQuotientCompact`).

The Library states derived partial statements of the Theorem
and the Proposition of VI.9.1 (printed pp.195–197 / PDF pp.201–203):
`GeneralizedJacquetLemmaStatement` and
`UniformCompressionStabilizationStatement` in the module
[UniformCompressionStabilizationStatement](../../Langlands/Representation/Exponents/UniformCompressionStabilizationStatement.md).
Their paired Markdown records how
they differ from the source:

- They use dynamic parabolics `P_G(χ)` with the centralizer Levi and the
  opposite radical. The comparison with arbitrary actual parabolics is the
  separate target `ParabolicDynamicStatement` and is not part of them.
- In place of `t ∈ C_A^{++}`, both take an element `g` that is central in
  `M(F)` and satisfies `Jacquet.IsIwahoriContraction K N M N̄ g`. For the
  Theorem this hypothesis on `K` is stronger than the source's Iwahori
  decomposition alone, so the statement covers fewer subgroups `K`.
- The exponent `b` of the Proposition is chosen after `χ`, `K` and `g`. It
  is uniform over the smooth representations only once these are fixed. The
  source's dependence `b = b(G, K)` is not asserted.
- Three source assertions are not stated: the identification of the
  localization of `V^K` at `A` with `(V^K_*, A|V^K_*)`, the bound
  `b ≤ c(G, K)` by the uniform admissibility constant of VI.2.3, and
  Remarks 1–3 (printed p.197 / PDF p.203, proofs continuing on PDF p.204).

The Library proves neither unconditionally: it derives
`GeneralizedJacquetLemmaStatement` from
`UniformCompressionStabilizationStatement`
(`generalizedJacquetLemma_of_uniformCompressionStabilization`), and
`UniformCompressionStabilizationStatement` from further hypotheses
(`uniformCompressionStabilization_of_representationStatements`). VI.9.2 and VI.9.3 prove the
Proposition of VI.9.1; the
[VI.9.1–VI.9.3 map](uniform-compression-progress.md) records their steps.
The consequences in VI.9.4 are stated in the next section. VI.9.5
(preservation of `B`-admissibility by `r_P^G`) is not stated; it needs the
category of `(G, B)`-modules of VI.8.3.

## VI.9.4: generation by `K`-fixed vectors

Source: VI.9.4, Corollary and Proposition, printed pp.200–201 / PDF
pp.206–207. Renard deduces the Corollary as the Corollary of VI.6.3
(printed p.179 / PDF p.185) without its admissibility hypothesis, by the
generalized Jacquet lemma, and the Proposition from the Corollary by the
Theorem of I.3.2 (printed p.22 / PDF p.28).

The two statements share their data and hypotheses, on the standard family
rather than on a represented parabolic. An actual maximal split torus
`i : S.toGrp ⟶ G` and a generic cocharacter `ν` fix the standard
parabolics, indexed by `J ⊆ simpleRelativeRoots i ν`, with points
`standardLeviPoints i ν J` and `standardUnipotentPoints i ν J`. The
hypothesis `_hstandard` supplies a standard cocharacter for every `J`. A
compact subgroup `K₀` satisfies only the Iwasawa factorization `g = m n k`
with `m ∈ M_∅(F)`, `n ∈ N_∅(F)` and `k ∈ K₀`. The compact open `K` satisfies
`K ≤ K₀`, `K₀ ≤ Subgroup.normalizer K` and, for every standard `J`,
`IsCompatibleStandardSplitComponent i ν J A q` and
`StandardParabolicBasisMember i ν J q K` for some split torus `A` and
`q : A.toGrp ⟶ S.toGrp`. The last predicate is one member of the V.5.2
basis, clauses (ii)–(iv). "Generated by its `K`-fixed vectors" means that
every subrepresentation whose submodule contains the `K`-fixed vectors is
`⊤`.

- `StandardFixedVectorSubquotientGenerationStatement`: for every smooth
  `V` generated by its `K`-fixed vectors, every subquotient
  (`SmoothRep.IsSubquotient`) is generated by its `K`-fixed vectors. No
  admissibility or finiteness hypothesis is made.
- `StandardFixedVectorHeckeEquivalenceStatement`: on the full subcategory
  of representations generated by their `K`-fixed vectors, the functor
  `P.ι ⋙ Langlands.Shimura.LevelHecke.heckeModuleFunctor ℂ K.toSubgroup`
  to `ModuleCat (LevelHeckeAlgebra ℂ K.toSubgroup)` is an equivalence.

The statements are derived partial coverage of VI.9.4. The source assumes a
compact open `K` contained and normal in `K₀` that admits an Iwahori
decomposition `K = K_N̄ K_M K_N` along every standard parabolic, the
decomposition named in V.5.2 (ii) (printed p.123 / PDF p.129). It does not
assume that `K` is an Iwahori subgroup. `StandardParabolicBasisMember`
conjoins this decomposition (`HasIwahoriIntersectionDecomposition`) with
`ContractionAndCofinality`, the remaining conditions of V.5.2 (ii)–(iv).
The published hypothesis may therefore be stronger than the source's, and
the statements may cover fewer subgroups `K`; they cover every member of the
V.5.2 neighbourhood basis, hence arbitrarily small `K`. Three points remain
open besides the proofs: the statements for the source's class of `K`,
without the additional
V.5.2 (ii)–(iv) conditions; the comparison of `LevelHeckeAlgebra` with the
Haar-measure corner `e_K H(G) e_K`; and an explicit inverse functor. Neither
statement is proved; the Library derives both from further hypotheses
(`Langlands/Representation/Jacquet/StandardIwahoriDecompositionStatements.lean`).
A proof can route the Corollary through the proved compact-open detection
consequences, compact-restriction detection and algebraic VI.6.3 Lemma, and
then needs further inputs: the norm-kernel finite restriction, the VI.2.1
cuspidal embedding and the generalized Jacquet lemma of VI.9.1.

## VI.9.7: second adjointness and completion

Source: VI.9.7, Theorem, printed p.205 / PDF p.211, with its proof on
printed pp.205–206 / PDF pp.211–212; the completion of I.1.4, printed
pp.9–10 / PDF pp.15–16.

`LeviCompletionOppositeJacquetStatement` has the ambient data of the VI.9.6
statements. It asserts a family of linear isomorphisms
`φ_π : V̄^N ≃ \overline{r_{P̄}^G(V)}`, one for every smooth `π`, between the
`N(F)`-fixed part `completionFixed` of the completion of `V` and the
completion of the normalized Jacquet module. The completions are spaces of
compatible families indexed by compact open subgroups, as in the source
proof. It asserts two properties:

- **Characterization.** `φ_π(x)_{K_M} = j_{N̄}(x_K)` for every compact open
  `K` of `G(F)` for which some `g` central in `M(F)` satisfies
  `Jacquet.IsIwahoriContraction` with the roles of `N` and `N̄` exchanged,
  and every compact open `K_M` of `M(F)` with image `K ∩ M(F)`. This class
  of `K` follows the published `GeneralizedJacquetLemmaStatement`.
- **Naturality.** For a morphism `f : π → σ` and families `x`, `y` with
  `y_K = f(x_K)` for every `K`, the components of `φ_σ(y)` are the images
  of those of `φ_π(x)` under `r_{P̄}^G(f)`.

The statement does not assert uniqueness, cofinality of the subgroups
`K ∩ M(F)`, `M(F)`-equivariance of `φ`, or the comparison of the
normalized and unnormalized completions.

## VII.1.3: reducibility for maximal Levi subgroups

Source: VII.1.3, Theorem and proof, printed pp.224–226 / PDF pp.230–232.

`MaximalLeviSupercuspidalReducibilityStatement` takes a proper parabolic
(`¬ IsIso p`) that is maximal: no actual parabolic lies strictly between
`P` and `G`. Supercuspidality of an irreducible `ρ` of `M(F)` is
triviality of every proper normalized Jacquet module of `ρ`. If
`i_P^G ρ` is not irreducible, the statement asserts some
`g ∉ pointImage (l ≫ p)` and some `φ : M ≅ M` with
`φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom`. It also asserts a positive
real-valued `ψ` among the published unramified characters of `M(F)`, and a
linear equivalence `T` of `ρ` intertwining `ρ` with `(ψ · ρ) ∘ φ`. This
expresses the source's `M = M'` and `ρ^w = ρψ` without standard Levi
subgroups. The Corollary of VII.1.3 is not stated; it needs Bernstein
components.

## VII.2.2–VII.2.4: induction, unitary parts and reciprocity

Source: VII.2.2, Lemma, printed pp.227–228 / PDF pp.233–234; VII.2.3,
printed p.229 / PDF p.235; VII.2.4, printed pp.229–230 / PDF pp.235–236.

- `LeviInductionNormalizedTemperedStatement`: if `σ` is tempered, so is
  `i_P^G σ`.
- `ArbitraryParabolicUnitaryJacquetPart` defines `unitaryJacquetPart` and
  `nonunitaryJacquetPart` for a parabolic datum and a split component
  `a`. They are the suprema of the generalized weight spaces of the
  normalized Jacquet module over exponents with zero and with nonzero
  `normalizedRealPart`. The module also defines the corresponding
  representations `leviUnitaryJacquetModule` and
  `leviNonunitaryJacquetModule` of `M(F)` with their inclusions, such as
  `leviUnitaryJacquetModuleι`. It proves only elementary lattice facts and
  these transports.
- `UnitaryJacquetPartTemperedStatement` (VII.2.3, Lemma): for tempered `π`,
  the two parts are complementary subspaces, and `leviUnitaryJacquetModule`
  is tempered. The parabolic is arbitrary instead of standard, and the
  direct sum, which the source takes from VII.1.1, is part of the
  conclusion.
- `TemperedJacquetUnitaryRestrictionStatement` (VII.2.4, Proposition,
  second step): for tempered `π` and `σ`, restriction along
  `leviUnitaryJacquetModuleι` is a bijection from intertwiners
  `r_P^G π → σ` to intertwiners from the unitary part to `σ`.
- `TemperedInductionUnitaryReciprocityStatement` (VII.2.4, Proposition):
  for tempered `π` and `σ` with independent carrier universes, there is a
  linear equivalence from intertwiners `π → i_P^G σ` to intertwiners from
  the unitary part to `σ`, with `e F y = (F x)(1)` whenever `y` is the
  unitary-part element whose image in `r_P^G π` is the class of `x`.
- `TemperedSquareIntegrableUnitaryPartStatement` (VII.2.4, Lemma): for
  tempered `π` with a central character `ω` on the full point-group
  center, `π` is square-integrable modulo the center for the supplied Haar
  measure if and only if the unitary part vanishes for every proper actual
  parabolic datum and split component. It retains the measure hypotheses of
  the published Casselman statement.

## VII.2.5: the tempered geometric lemma

Source: VII.2.5, Proposition and proof, printed p.230 / PDF p.236.

`TemperedGeometricLemmaStatement` takes two actual rational parabolic data
`P = MN` and `Q = LU`, a split component of `L` and a tempered `ρ` of
`M(F)`. It asserts representatives `z i` meeting every double coset of
`P(F)` and `Q(F)` in `G(F)` exactly once, with intersection data of the
published `RepresentedGeometricLemmaStatement` (VI.5.1). For
every choice of split components of the Levis `M ∩ zLz⁻¹`, it asserts an
actual finite filtration of the unitary part `(r_Q^G i_P^G ρ)_0` and a
permutation of the pieces. The graded pieces are isomorphic to
`i^L_{L ∩ z⁻¹Pz}` of the transported unitary part
`(r^M_{M ∩ zQz⁻¹} ρ)_0`. The helper definition
`GeometricLemmaIntersectionDatum.unitaryPieceRep` forms these pieces. The
specific set `W_{Q,P}` of V.4.7 is not used. Naturality in `ρ` and
compatibility with the VI.5.1 filtration are not asserted.

## VII.2.6: tempered representations and discrete series

Source: VII.2.6, Theorem and Corollary, printed pp.231–232 /
PDF pp.237–238.

A *discrete* representation of `M(F)` below is irreducible and
square-integrable modulo the center for every Borel Haar measure on the
quotient by the full center. An embedding is an injective intertwiner into
`i_P^G σ`.

- `TemperedIrreducibleDiscreteSeriesStatement`: an irreducible `π` is
  tempered if and only if it embeds into `i_P^G σ` for some actual
  parabolic datum and some discrete `σ`.
- `TemperedIrreducibleDiscreteSeriesUniquenessStatement`: for two such
  embeddings of an irreducible `π`, there are `g : G(F)` and
  `φ : M₁ ≅ M₂` with `φ.hom ≫ l₂ ≫ p₂ = l₁ ≫ p₁ ≫ (G.innerIso g).hom`, and a
  linear equivalence `σ₁ ≃ σ₂` intertwining `σ₁` with `σ₂ ∘ φ`.
- `TemperedIrreducibleUnitarizableStatement`: an irreducible tempered `π`
  satisfies the published algebraic predicate `IsUnitarizable`.

## Proofs of related statements

The proofs the Library has of the statements of this map are in the last
column of the table of pairs. The related represented-parabolic
Jacquet-admissibility statement, parabolic quotient-compactness statement and
represented geometric lemma are proved, as
`arbitraryParabolicJacquetAdmissibility`, `arbitraryParabolicQuotientCompact`
(their `…Proof.lean` files in `Langlands/Representation/Exponents/`) and
`representedGeometricLemma`
(`Langlands/Representation/Geometric/RepresentedGeometricLemmaProof.lean`).

## Published proofs

Five of the statements were proved in the Library when this map was written
(the table of pairs gives the proofs the Library has now). Each theorem has
the exact published statement as its type.

| Statement | Theorem and proof module |
| --- | --- |
| `LeviFrobeniusReciprocityStatement` | `leviFrobeniusReciprocity`, `LeviFrobeniusReciprocityProof` |
| `LeviParabolicFunctorsExactStatement` | `leviParabolicFunctorsExact`, `LeviParabolicFunctorsExactProof` |
| `TemperedJacquetUnitaryRestrictionStatement` | `temperedJacquetUnitaryRestriction`, `TemperedJacquetUnitaryRestrictionProof` |
| `TemperedInductionUnitaryReciprocityStatement` | `temperedInductionUnitaryReciprocity`, `TemperedInductionUnitaryReciprocityProof` |
| `LeviParabolicTransitivityStatement` | `leviParabolicTransitivity`, `LeviParabolicTransitivityProof` |

Both VI.1.2 proofs prove, rather than assume, the compact-subgroup property
of the rational points of the radical; the Frobenius proof also proves
their unimodularity. The restriction proof derives
complementarity of the two parts from temperedness, through
`IsNormalizedExponentTempered.unitaryJacquetPart_isCompl`, and applies the
restriction bijection of `TemperedJacquetRestriction`. The reciprocity
proof is a single term: the conditional assembly
`temperedInductionUnitaryReciprocity_of` of
`TemperedInductionUnitaryReciprocityReduction`, applied to the Frobenius
and restriction proofs. The other two VI.1.2–VI.1.3 statements and
`UnitaryJacquetPartTemperedStatement` were not proved then; the Library
proves them now, while `TemperedSquareIntegrableUnitaryPartStatement` is
not proved (see the table of pairs).

The transitivity proof first appeared at Library commit
`f73044d93e675a78ed75830ef026b3224514e510`. It is a single application:
the proved `nestedParabolicPointDecomposition` (module
`Langlands.GroupScheme.Rational.NestedParabolicPointDecompositionProof`)
shows `N_L(F) = L(F) ∩ N(F)` and `N(F) = (L(F) ∩ N(F)) U(F)` inside
`G(F)`, and the adapter `leviParabolicTransitivity_of_radical_decomposition` of
`LeviParabolicTransitivityReduction` turns these identities into the two
natural isomorphisms.

Several published supporting modules retain their
inputs as premises and prove none of the remaining targets. They include
`ArbitraryParabolicUnitarity`, `TemperedIrreducibleUnitarityReduction`
and `ParabolicPresentationUnitarity`, which build invariant
forms toward the VII.2.6 Corollary; and
`MaximalLeviReducibilityUnitaryInputs` and
`MaximalLeviReducibilityReductionStatements`, which separate
the VII.1.3 proof into statements. The `MaximalLeviSupercuspidalReducibilityFromInputsStatement` asserts that
`MaximalLeviSupercuspidalReducibilityStatement` follows from eleven
published propositions, among them `ParabolicDynamicStatement`,
admissibility of irreducible representations (VI.2.2) and compactness of
`P(F)\G(F)`. The `MaximalLeviSupercuspidalReducibilityFromInputsProof`
proves that implication. VII.1.3 itself follows once those premises are
proved.

## Remaining obligations

1. Proofs of the statements above that the Library does not prove (ten of
   the twenty-one; see the table of pairs). When this map was written they
   needed structural facts that were open for arbitrary actual parabolics,
   among them compactness of `P(F)\G(F)`, Jacquet admissibility, Iwahori
   decompositions and contracting elements; the first two are now proved
   (`arbitraryParabolicQuotientCompact`, `arbitraryParabolicJacquetAdmissibility`).
2. Statements of VII.3 and VII.4, and of the VII.1.3 Corollary.
   VII.3 also needs representatives of Weyl double cosets for actual
   parabolics. VII.4 needs Langlands chambers with relative coroots.
   The VII.1.3 Corollary needs Bernstein components.
3. The statement of VI.9.5, which needs the `(G, B)`-modules of VI.8.3.
   For VI.9.4: the two statements for every compact open `K` contained and
   normal in `K₀` with Iwahori decompositions along the standard
   parabolics, without the further conditions of V.5.2 (ii)–(iv); the
   comparison of `LevelHeckeAlgebra` with `e_K H(G) e_K`; and an explicit
   inverse functor. For VI.9.1: the proofs of
   `UniformCompressionStabilizationStatement` and of
   `GeneralizedJacquetLemmaStatement`; statements of the localization
   identification, the bound `b ≤ c(G, K)`, the dependence `b = b(G, K)` and
   Remarks 1–3; the Theorem for every `K` with an Iwahori decomposition; and
   the transfer from dynamic to arbitrary actual parabolics.

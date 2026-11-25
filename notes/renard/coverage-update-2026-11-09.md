# Renard 2026: coverage update, 9 November 2026

This note supplements the
[whole-book ledger](coverage.md), whose section table was last revised around
7 November 2026. It records the statement modules that entered the Library
between then and 9 November 2026, the gaps left to separate source maps, and
the audit findings for sections that the ledger lists as backlog. It declares no section,
chapter or book complete. A published statement is not a proof; every row
below keeps the proof status explicit.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF page numbers equal printed page numbers plus six. Library facts refer to
commit `3f0bcbd4638c9c42befdc9f7e1578d62fde2c959`, except the columns and
parentheses that give the proofs the Library has now.

## New statement publications

Each module below is a statement module of the Library. None of the
propositions was proved at the commit above; the last column gives the proof
the Library has now.

| Source assertion | Library module and entry declaration | Proof in the Library |
| --- | --- | --- |
| I.2.1, printed p.14 / PDF p.20: `ker q = H` with `X ⊗_Ã Y = X ⊗_A Y / Vect(...)`, the tensor half of (I.2.1.2), its unital case, and the unique algebra structure on `Ã` | `Langlands.Algebra.UnitizationTensorComparisonStatements`, `Langlands.Algebra.UnitizationTensorComparison.Statements` | proved: `statements` (`Langlands/Algebra/UnitizationTensorComparisonProof.lean`) |
| I.2.2, Proposition, printed p.15 / PDF p.21: `• ⊗_A X` right exact, `Hom_A(•, X)` and `Hom_A(X, •)` left exact | `Langlands.Algebra.NondegenerateTensorHomExactnessStatements`, `Langlands.Algebra.NondegenerateTensorHomExactness.Statements` | proved: `statements` (`Langlands/Algebra/NondegenerateTensorHomExactnessProof.lean`) |
| I.3.2, Proposition and Theorem, printed pp.21–22 / PDF pp.27–28: `Irr(A, e) ↔ Irr(eAe)` and the criterion for `j_e` to be an equivalence | `Langlands.Algebra.NonUnitalModuleCornerSimpleStatements`, `Langlands.Algebra.NonUnitalModuleCornerSimpleStatements.Statements` | proved: `statements` (`Langlands/Algebra/NonUnitalModuleCornerSimpleProof.lean`) |
| III.1.5, Proposition (ii)–(iv) and Theorem, printed pp.60–61 / PDF pp.66–67 | `Langlands.Representation.Hecke.FixedVectorCornerStatements`, `Langlands.Hecke.FixedVectorCornerStatements` | proved: `fixedVectorCorner` (`Langlands/Representation/Hecke/FixedVectorCornerProof.lean`) |
| V.2.7, Lemma, printed p.109 / PDF p.115: `X(G)(π)` is finite | `Langlands.Representation.CuspidalSupport.RationalTwistStabilizerFiniteStatement`, `Langlands.CuspidalSupport.RationalTwistStabilizerFiniteStatement` | proved: `rationalTwistStabilizerFinite` (`Langlands/Representation/CuspidalSupport/RationalTwistStabilizerFiniteProof.lean`) |
| VII.4.1, Lemma, printed p.241 / PDF p.247: `σ ⊗ ψ` is `PP̄`-regular and `Hom_G(i_P^G(σψ), i_{P̄}^G(σψ))` has dimension one | `Langlands.Representation.LanglandsClassification.LanglandsTripletRegularityStatement`, `Langlands.Aubert.General.RepresentedParabolic.LanglandsTripletOppositeRegularityStatement` | proved: `langlandsTripletOppositeRegularity` (`Langlands/Representation/LanglandsClassification/LanglandsTripletRegularityProof.lean`) |

The III.1.4 Theorem (smooth representations form a category equivalent to
nondegenerate `H(G)`-modules, for the published functor
`Langlands.Hecke.heckeNondegenerateModuleFunctor`) needs Renard's Hausdorff
condition from II.1.1; at the commit above it was not yet stated. It is now
stated as `Langlands.Hecke.HeckeNondegenerateModuleEquivalenceStatement` and
proved, as `Langlands.Hecke.heckeNondegenerateModuleEquivalence`
(`Langlands/Representation/Hecke/NondegenerateModuleEquivalenceProof.lean`; see
the [next update](coverage-update-2026-11-10.md)).

## Published statements without a proof at that commit

A scripted scan of the commit above listed the Prop-valued entry declarations
of Renard-citing modules and the theorems whose types mention them. For the
following published statements it found no proof. The scan is heuristic; it is
a finding aid, not coverage evidence. The last column gives the proof the
Library has now.

| Source | Target declaration | Proof in the Library |
| --- | --- | --- |
| III.1.7–III.1.11 | `Langlands.Renard.Smooth.RenardSchurStatements` | proved: `renardSchurStatements` (`Langlands/Representation/Smooth/RenardSchurProof.lean`) |
| III.1.2, III.1.3, III.1.15 | `Langlands.Renard.Smooth.RenardTensorHomStatements` | proved: `renardTensorHomStatements` (`Langlands/Representation/Smooth/RenardTensorHomProof.lean`) |
| IV.1.4 | `Langlands.Renard.CompactRepresentation.CompactFormalDegreeStatements` | proved: `compactFormalDegree` (`Langlands/Representation/CompactCoefficient/CompactFormalDegreeProof.lean`) |
| IV.1.4–IV.1.5 | `Langlands.Renard.CompactRepresentation.CompactIsotypicComplementStatement` | proved: `compactIsotypicComplement` (`Langlands/Representation/CompactCoefficient/CompactIsotypicComplementProof.lean`) |
| IV.1.5 | `Langlands.Renard.CompactRepresentation.CompactProjectionDistributionStatement` | proved: `compactProjectionDistribution` (`Langlands/Representation/CompactCoefficient/CompactProjectionDistributionProof.lean`) |
| IV.2.1 | `Langlands.Renard.CompactRepresentation.HermitianRepresentationStatements` | proved: `hermitianRepresentationStatements` (`Langlands/Representation/Unitary/HermitianSelfDualProof.lean`) |
| IV.3.2, Remark | `Langlands.Renard.CompactRepresentation.SquareIntegrableCoefficientCriterionStatement` | proved: `squareIntegrableCoefficientCriterion` (`Langlands/Representation/MatrixCoefficient/SquareIntegrableCoefficientCriterionProof.lean`) |
| VI.10.6, Proposition (iii)–(iv) | `Langlands.Jacquet.FixedVectorCategoryStatements` | not proved; derived from further hypotheses by `fixedVectorCategoryStatements_of_standardIwahori` (`Langlands/Representation/Jacquet/StandardIwahoriFixedVectorCategoryStatements.lean`) |
| VI.10.7, Corollary | `Langlands.Aubert.General.RepresentedParabolic.HeckeAlgebraCenterFiniteStatement` | not proved; derived from further hypotheses by `heckeAlgebraCenterFinite_of_finiteTypeCenterAdmissible` (`Langlands/Representation/CuspidalSupport/HeckeCenterReduction.lean`) |
| VII.4.2, Theorem | `Langlands.Aubert.General.RepresentedParabolic.LanglandsClassificationStatement` | not proved; derived from further hypotheses by `langlandsClassificationFromInputs` (`Langlands/Representation/LanglandsClassification/LanglandsClassificationFromInputsProof.lean`) |
| VII.3.2–VII.3.4 | `PQSupportGradedStatement`, `PQRegularityLemmaStatement`, `PQIntertwiningOperatorStatement` (namespace `Langlands.Aubert.General.RepresentedParabolic`) | `PQSupportGradedStatement` proved: `pqSupportGraded` (`Langlands/Representation/Intertwining/PQIdentitySupportProof.lean`); `PQRegularityLemmaStatement` not proved, derived from further hypotheses by `pqRegularity_admissible_reduction` (`Langlands/Representation/Intertwining/PQRegularityAdmissibleReduction.lean`); `PQIntertwiningOperatorStatement` proved: `pqIntertwiningOperator` (`Langlands/Representation/Intertwining/PQIntertwiningOperatorProof.lean`) |

The VI.10.4 statement `Langlands.CuspidalSupport.BernsteinBlockCenterStatements`
is not proved either; the Library derives it from further hypotheses, by
`bernsteinBlockCenterStatements_of_centerFunctions`
(`Langlands/Representation/CuspidalSupport/BernsteinBlockCenterStatementsReduction.lean`).

## Gaps with their own source maps

These gaps had no statements at the commit above; each now has its own source
map, which gives its definitions and statements.

| Scope | Source map |
| --- | --- |
| III.2.1 Hecke-algebra bimodule and functors for continuous homomorphisms; (III.2.5.1); III.2.6; III.2.10; III.2.11 | [III.2 map](iii2-hecke-induction.md) |
| III.3: smooth actions on sheaves, coinvariant sheaves, induction on homogeneous spaces | [III.3 map](iii3-sheaf-sections.md) |
| II.3: source map; Haar distributions, quasi-invariant distributions, convolution, completion of `H(G)` and the centre of `M(H(G))` | [II.3 map](ii3-td-groups.md) |

## Section findings

The ledger's section table lists these sections as backlog or partial. The
findings below update it; rows not mentioned keep their ledger status.

- **I.2.** The positive assertions of I.2.1 that the
  [I.2.1 map](unitization-tensor-progress.md) listed as missing (`H = ker q`,
  the tensor half of (I.2.1.2), its unital case, and the uniqueness of the
  algebra structure on `Ã`) now have published statements in
  `UnitizationTensorComparison.Statements` above; the other positive
  assertions are stated by the six definition modules of that map. Caveat (e)
  of the map, that without a unit `Hom_A(X, Y)` and `X ⊗_A Y` carry no
  canonical vector-space structure, keeps its status there: an informal
  remark with no published statement, illustrated only by the zero-action
  examples of `CompatibleUnitizationTensor`. In I.2.2 the Theorem and
  Corollary have published additive statements
  (`NonUnitalTensorHomAdjunctionStatements`,
  `NonUnitalTensorAssociativityStatements`, whose coefficient comparisons remain
  open) and the Proposition is stated above. In I.2.3 the functors `F`, `P`
  (`NondegenerateTensorFunctor`), `I`, `ˇF` (`RenardHomFunctors`), the Lemma
  (I.2.3.3) (`RegularTensorContractionStatements`) and the Theorem
  (`NondegenerateInductionAdjunctionStatements`) are published; the unital
  left adjoint is covered through A.V.2 (`UnitalScalarExtensionAdjunctionStatements`).
  Not stated: the right adjoint `ϕ^* = Hom_A(B, •)` in the unital case, and the
  final Remark of I.2.3 (forgetful and pseudo-forgetful functors along
  `ϕ : A → B` are naturally isomorphic to restriction of scalars, available as
  `NonUnitalModuleRestrictScalars.nondegenerateFunctor`). I.2.4 is stated by
  `NondegenerateInductionExactnessStatements`.
- **I.3.** Published statements: `j_e` and (I.3.1.1)
  (`NonUnitalModuleCorner`), the I.3.1 Proposition
  (`NonUnitalModuleCornerExactnessStatements`, proved), `M(A, e)`
  (`NonUnitalModuleIdempotentGenerated`), (I.3.2.1)
  (`NonUnitalModuleCornerInductionStatements`, proved), generatedness of `i(Z)`
  (`NonUnitalModuleCornerInductionGeneratedStatements`, proved), `M_e`
  (`IdempotentAnnihilatorQuotient`), `(M_e)_e = M_e` and (I.3.2.2)
  (`IdempotentAnnihilatorComparisonStatements`, proved), the facts about `φ`
  (`NonUnitalModuleCornerEvaluationStatement`, proved), and the Proposition and
  Theorem (stated above). Not stated: the remark after (I.3.2.1), printed
  p.20 / PDF p.26, that for a unital `eAe`-module `Z` the two complex
  vector-space structures on `A ⊗_{eAe} Z`, from `A` and from `Z`, coincide.
  The additive construction `NonUnitalModuleCornerInduction` records this
  comparison as an open obligation, and neither its statement aggregates nor
  `NonUnitalModuleCornerSimpleStatements` contain it.
- **III.1.** Published statements, with source correspondences to check in a
  full source map: III.1.1 (`IsSmooth`, `SmoothRep`; the Remark as
  `SmoothDiscreteOrbitStatement`, proved), III.1.2–III.1.3 and III.1.15
  (`RenardTensorHomStatements`), III.1.4 (functor published; equivalence not stated at the commit above, now
  proved, see above;
  the closing existence assertions as `RenardIrreducibleExistenceStatement`,
  proved), III.1.5 (above), III.1.6–III.1.7 (`Smooth/Contragredient/*`,
  `SmoothAdmissibleDualityStatement`, proved), III.1.7–III.1.11
  (`RenardSchurStatements`), III.1.12 (`Character.distribution`;
  `CharacterTransportStatement`, proved), III.1.13 (Bernstein–Zelevinsky based
  `FiniteFamilyLinearIndependenceStatement` and `CharacterSeparationStatement`,
  both proved), III.1.14 (Flath's two-factor `FlathTwoFactorStatement`, for two
  factors). Not stated: the identification `(V₁ ⊗ V₂)_G ≅ V₁ ⊗_{H(G)} V₂`,
  (III.1.15.1), and Remark 3 of III.1.15.
- **III.2.** The smooth-function assertions have Bernstein–Zelevinsky based
  statements: III.2.2 (`Induction.smoothInduced`, `compactInduced`; exactness
  in `Induction.StructuralStatement`; the Lemma for finitely many double cosets
  in `Induction.FixedVectorModel`), III.2.3, III.2.5 and III.2.8
  (`Induction.StructuralStatement` clauses), III.2.9
  (`Jacquet.Coinvariants`; Proposition and Corollary in
  `CharacterLocalizationExactnessStatement`, proved). The Hecke-algebra side is
  in the [III.2 map](iii2-hecke-induction.md).
- **III.3.** No published statement in Renard's form at the commit above; see
  the [III.3 map](iii3-sheaf-sections.md).
- **IV.** Published statements: IV.1.1, IV.1.3 and IV.1.7 (`CompactGroupSmoothStatements`,
  `CompactRepresentationCriterionStatements`, `CompactSplittingCriterionStatement`;
  all three now proved, in `Langlands/Representation/Compact/`), IV.1.4–IV.1.5 (above),
  the IV.1.6 Corollary (Bernstein–Zelevinsky 2.44(b),
  `CompactCoefficientSemisimplicityStatement`, proved), IV.2.1 and IV.3.2
  (above). A full IV source map remains to be written.
- **V.2.7.** The Lemma is stated above; the Corollary (orbits are complex tori)
  needs the V.2.4 variety structure and is not stated.
- **VI.10.** Published statements exist for VI.10.1–VI.10.8, among them
  `BernsteinInducedProgeneratorStatement`, `BernsteinBlockHomEquivalenceStatement`,
  `SupercuspidalInductionLengthStatement`, `BernsteinBlockCenterStatements`,
  `HarishChandraHomomorphismStatement`, `CompactOpenInertialFinitenessStatement`,
  `FixedVectorCategoryStatements`, `HeckeAlgebraCenterFiniteStatement`,
  `FiniteTypeComponentCharacterizationStatement` and
  `CenterFiniteHoweStatement`, none of them proved at the commit above. The
  Library proves none of the ten; it derives
  `BernsteinBlockHomEquivalenceStatement`, `BernsteinBlockCenterStatements`,
  `FixedVectorCategoryStatements`, `HeckeAlgebraCenterFiniteStatement` and
  `CenterFiniteHoweStatement` from further
  hypotheses (`bernsteinBlockHomEquivalence_of_inducedProgenerator`,
  `bernsteinBlockCenterStatements_of_centerFunctions`,
  `fixedVectorCategoryStatements_of_standardIwahori`,
  `heckeAlgebraCenterFinite_of_finiteTypeCenterAdmissible`,
  `centerFiniteHowe_of_inputs`).
- **VII.3.** VII.3.1–VII.3.4 are published
  (`Intertwining/PQRegularity`, `PQSupportGradedStatement`,
  `PQRegularityLemmaStatement`, `PQIntertwiningOperatorStatement`; for their
  proofs see the table above). The Proposition of VII.3.5 is not stated; it
  needs the operator `J_{Q|P}(σ)` normalized by the integral over `N̄ ∩ U`,
  which was not constructed at the commit above (the
  [11 November update](coverage-update-2026-11-11.md) records its statement).
- **VII.4.** The Definition (`IsLanglandsTriplet`), the Lemma (above)
  and the Theorem (`LanglandsClassificationStatement`) are published; for
  their proofs see the tables above.

## Remaining work recorded here

The coverage ledger's section table should be rewritten from this note and the
source maps of III.2, III.3 and II.3. The unstated source assertions named in the
findings above remain obligations, among them the I.3.2 comparison of complex
scalar structures on `A ⊗_{eAe} Z` and the I.2.1 caveat (e), which has to be
stated or explicitly classified as expository. Further assertion-level maps are needed for III.1,
IV, V.5 (including the V.5.3 decomposition of `H(G, K)`) and the chapter notes
I.7, II.4, III.4, VI.11 and VII.5.

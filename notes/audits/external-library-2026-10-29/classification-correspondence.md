# External Library audit 2026-10-29: classification, cuspidal support, exponents and correspondence

This note records verdicts on the eighteen findings of this area from the *External Library audit 2026-10-29*. All eighteen hold as documentation defects at the audited commit. In five of them the Library was further along than the audit said: P3-023, P3-065, P3-068, P3-069 and P3-070. None needed a change to a Lean statement, proof target, binder or universe. One correction also changes a Lean module docstring (P3-072, `GelfandKazhdanStatement.lean`). Every other correction changes only paired Markdown. Each correction concerns one file pair and is in the Library.

## Scope, sources and checked commits

The audit is registered as `external-library-audit-2026-10-29-3987c3d`. Its file is `FINAL_AUDIT_3987c3d.md`, SHA256 `d9a25f35dc2d7bef0351ba0891db168b0c3cc797a281d0a9944e930fe43d5eeb`. The rows concerned are at its lines 75 (P3-012), 80 (P3-017), 91 (P3-023), 160–165 (P3-065 to P3-070), 167–170 (P3-072 to P3-075), 176–178 (P3-081 to P3-083) and 180–181 (P3-085, P3-086). The report was read as a list of allegations, not as evidence.

The audited commit is Library `3987c3d7445531c2c7f784464a3fd47061ba0865`. All eighteen findings were verified against it, and the verdict table cites locations at that commit. The final check commit is `7e64f8e360c8778e04e5da7f9cd382cda7c837f6`. The correction table and the fingerprint tables identify the current evidence.

Two proofs that bear on the wording concerned entered the Library after the audited commit:

- `Langlands.glFiniteLengthAdmissibility`, `Langlands.leviFiniteLengthAdmissibility` and `Langlands.finiteLengthAdmissibility` (`Langlands/Representation/Smooth/Admissibility/FiniteLengthProof.lean:109,122,135`, first in the Library at `b58bd42aee6a565b689f0f0c008506e23b1b6560`). They prove the three targets of `FiniteLengthStatement` (P3-023).
- `Langlands.glTemperedExponentCriterion` (`Langlands/Representation/Classification/TemperedExponentProof.lean:101`, first in the Library at `f35c1c217068f79dff12263770d16a95f9632251`). It proves `GLTemperedExponentCriterionStatement` (P3-065, P3-083).

The corrections describe the Library as it is after these publications. In each case the verdict at the audited commit is unchanged.

The conclusions concern only the wording concerned and the declarations needed to check it. They do not assert supercuspidal-support uniqueness, all unitary-generic compatibility clauses, Jordan–Hölder multiplicity one, the existence of arithmetic factors, the regular-chamber Langlands quotient theorem, or the local Langlands correspondence. They also do not certify a kernel build of the whole Library.

## Corrections

Each correction is a focused change for one file pair. No correction changes
a Lean statement or proof target, and every changed file belongs to the file
pairs concerned.

## Per-finding verdicts at the audited commit

All paths begin at `Langlands/` under the Library root. Line numbers refer to commit `3987c3d`. Correction identifiers are given by their first eight hexadecimal digits.

| Finding | Verdict | Location and decisive evidence | Decision |
| --- | --- | --- | --- |
| P3-012 | Holds | `Representation/Exponents/OppositeJacquetSubquotientInheritanceStatement.md:36–38` calls `φ` a functional on the full algebraic dual of the refined opposite Jacquet module, and lines 80–81 repeat this. In the Lean (`…Statement.lean:29`), `φ : Module.Dual ℂ (RefinedOppositeJacquetModule C D S.ρ)` is a functional on the Jacquet module `J` itself, an element of `J*`. The displayed eigenfunctional equations already use this domain. | Say that `φ` is a linear functional on `J`. |
| P3-017 | Holds | `Automorphic/AssociatedFactorStatement.md:14–16` says "no existence statement is made". The Lean propositions are existential: line 45 (a self-dual measure), line 47 (a common gamma factor) and line 214 (a block shape and supercuspidal factors). The Markdown's own lines 313–314 say that self-dual existence is asserted. | Say that the module constructs no witnesses and proves none of its existence propositions. Conditional existential propositions are existence statements. |
| P3-023 | Holds; the Library also has a proof | `Representation/Smooth/Admissibility/FiniteLengthStatement.md:184–187` says that admissibility of irreducible product-Levi representations is not stated. `IrreducibleLeviAdmissibilityTheorem` (`Representation/CuspidalSupport/IrreducibleLeviAdmissibilityStatement.lean:17–22`) states it for every supplied topology, rank and block shape, with an independent carrier universe and no tensor-factorization or quasicuspidal premise. The audit says only that the statement exists. In fact `irreducibleLeviAdmissibility` (`IrreducibleLeviAdmissibilityProof.lean:21`, artifact `5c237278`) already proved it at the audited commit. Lines 180–183 also call the proof of `AdmissibleShortExactStatement` separate, and `admissibleShortExact` (`Smooth/Admissibility/ExactProof.lean`, artifact `31d37439`) proves it. | Cite the statement and both proofs. The finite-length proofs published later (see above) are cited too, and the derivation is described as the implemented induction. |
| P3-065 | Holds; the Library has more than the audit says | `Representation/Classification/RegularLanglandsStatement.md:150–155` says that Lemmas 5.3 and 5.6, Propositions 5.7–5.9, Corollary 6.2 and the maximal-cone construction of Proposition 7.2 of Silberger (1978) "remain statement obligations". Each is already stated separately: `RelativeGenericityStatement.lean:29` (Lemma 5.2); `RelativeJacquetMultiplicityStatement.lean:65,88,105` (Lemmas 5.3, 5.5); `RelativeRegularComparisonStatement.lean:71` (Lemma 5.6); `RelativeRecoveryStatement.lean:37,80,113` (Propositions 5.7–5.8); `RelativeCosocleMultiplicityStatement.lean:22` (Proposition 5.9); `SemistandardLanglandsStatement.lean:25` (Corollary 6.2); `MaximalConeStatement.lean:40` (maximal cone). The maximal-cone statement uses the dominance condition corrected after Konno (2003), and `glMaximalConeJacquetQuotient` (`MaximalConeProof.lean:21`, artifact `fdb503fe`) proves it. Lines 155–159 say that "their proofs, product specialization, chamber conversion and the present three implications all remain open". In fact `glParabolicRootWeightCone` (artifact `04d4ae96`) proves the product specialization, and `glSquareIntegrableExponentCriterion` (artifact `218e69b5`) proves the square-integrable exponent criterion. The components of the tempered prerequisite families are proved too, except `GLTemperedInductionStatement`. | List the separate statements of Silberger's intermediate results, then the status of each route input. The maximal-cone proof does not certify the printed block-count selection and proves none of the three clauses. `RootWeightConeDecompositionStatement`, `GLFixedCentralCharacterSplittingStatement`, `GLTemperedInductionStatement` and the three clauses are unproved. The tempered exponent criterion is proved since `f35c1c21`. |
| P3-066 | Holds | `Representation/Classification/SupercuspidalSupport.md:8–11` says that existence of a supercuspidal support, its uniqueness and the embedding of `π` in some ordering "remain theorems to be stated and proved". The embedding and uniqueness statements are stated, for positive rank, in `SupercuspidalSupportStatement.lean:20,29`. `glSupercuspidalEmbedding` (`SupercuspidalEmbeddingProof.lean:23`, artifact `437ea2bb`) proves the embedding statement, which gives the documented existence route. | Update both statuses. `GLSupercuspidalSupportUniquenessStatement` has no proof. The rank-zero case is not supplied by the positive-rank embedding theorem. |
| P3-067 | Holds | `Representation/Classification/DiscreteSeriesOppositeToUpperStatement.md:180–197` calls the opposite-to-upper comparison unproved. `glTemperedDiscreteSeriesOppositeToUpper` (`DiscreteSeriesOppositeToUpperProof.lean:29`, artifact `ae869e32`) proves exactly `GLTemperedDiscreteSeriesOppositeToUpperStatement.{uF,uV,uW}`. | Cite the proof and the summand proof `glTemperedDiscreteSeriesSummand`, which uses it. Keep the original representation hypotheses and the statement-only nature of the module. |
| P3-068 | Holds (both files); the Library has more than the audit says | `Representation/Classification/DiscreteSeriesJacquetStatement.md:166–174` says that square-integrable-to-tempered and the Jacquet quotient criterion still require Lean proofs, and that the summand and support statements have open proofs. They are proved by `glLeviDiscreteSeriesTempered` (`LeviDiscreteSeriesTemperedProof.lean:92`, artifact `88ba0ad2`), `glTemperedDiscreteSeriesJacquetQuotient` (artifact `bfa83e1d`) and `glTemperedDiscreteSeriesSummand` (artifact `bd13990f`). `TemperedSupportStatement.md:104` repeats the open status. The audit treats support existence as a separate open target, but `glTemperedDiscreteSeriesSupport` (`TemperedSupportProof.lean:17`, artifact `484c04c4`) proves it. The weakly critical refinement `GLWeaklyCriticalTemperedRefinementStatement` (`Representation/Exponents/WeakCriticalStatement.lean:55`) has three components. Two are proved: existence, by `glWeaklyMinimalStandardPairExistence` (artifact `caf4326e`), and support, by `glWeaklyCriticalDiscreteSeriesSupport` (artifact `c3b502aa`). Minimality, `GLWeaklyCriticalPairMinimalityStatement`, has no proof. | Cite each proof in both files. Say that the refinement as a whole is unproved because its minimality component is. |
| P3-069 | Holds; the Library has more than the audit says | `Representation/Classification/TemperedInductionStatement.md:22–25` gives the support and summand results one open-proof label. Both are proved: `glTemperedDiscreteSeriesSummand` proves the exact four-clause equivalence, and `glTemperedDiscreteSeriesSupport` proves support. Line 19 says these definitions are not proved. That is true of the module, but `glTemperedUnitarity` (`TemperedUnitarityProof.lean:200`, artifact `7eb13ebf`) proves `GLTemperedUnitarityStatement`. | Give the status of each component. The first conclusion of `GLTemperedInductionStatement` is isolated as `GLLeviTemperedUnitarityStatement` and proved by `glLeviTemperedUnitarity` (artifact `7a2a6312`). Semisimplicity follows from it with no separately named theorem. Temperedness of the induction (`GLTemperedInductionPreservationStatement`), `GLTemperedInductionStatement` and the prerequisite conjunction are unproved. |
| P3-070 | Holds; three clauses are proved, not two, and a published construction supplies a fourth | `Representation/Classification/UnitaryGenericCompatibilityStatement.md:185–186` says "all nine mathematical assertions remain proof obligations". Three clauses are proved exactly, with the original hypotheses: `UnitaryAdmissibleHermitianClause` by `unitaryAdmissibleHermitianClause` (artifact `aea3ac96`, no irreducibility or square-integrability premise), `TwistedProductOrdinaryDualClause` by `twistedProductOrdinaryDual` (artifact `9fa7b554`) and `TwistedProductCharacterTwistClause` by `twistedProductCharacterTwist` (artifact `ed7a2cff`). The audit names only the first two. Line 101 calls the Hermitian route prospective. Lines 112–113 say that the admissible tensor smooth-dual comparison remains an obligation, but `FiniteTensor.smoothDualTensorInjectivity` and `FiniteTensor.smoothDualTensorMap_surjective` supply it. `RealTwistOrdinaryDualClause` has no theorem of its type, but the public definition `segmentFactorSmoothDualEquiv` in `TwistedProductOrdinaryDualProof.lean` supplies its content exactly. The determinant-twist conjunct of `ScalarCharacterTwistDualClause` is the third conjunct of the published `glConstituentCentralCharacterFor`. | Track status clause by clause. No published declaration supplies the other five clauses in full, or either aggregate statement. |
| P3-072 | Holds (both files) | (a) `Representation/Smooth/Contragredient/GelfandKazhdanStatement.md:3,62–63,85` and the Lean module docstring (line 9) call the target unproved. `gelfandKazhdanContragredient` (`GelfandKazhdanProof.lean:19`, artifact `31571ec8`) proves `GelfandKazhdanContragredientStatement.{uF,uV}`. (b) `Correspondence/SupercuspidalGammaCompatibility.md:63–66` says that the identification of the inverse-transpose pullback with the smooth contragredient is not proved. `gelfandKazhdanContragredient` and `RankinSelberg/SmoothDualPairFactors.lean` (artifact `6be006cb`: `inverseTransposeSmoothDualEquiv`, `isPadicSymmetric{LPolynomial,EpsilonFactor,GammaFactor}_inverseTranspose_iff_smoothContragredient`) supply it. | Cite them. The JPSS identification of the gamma factor and `SupercuspidalGammaFromFactorsStatement` remain unproved. Only the docstring of the Lean file changes. |
| P3-073 | Holds (three subclaims) | (a) `Correspondence/SupercuspidalRelations.md:48–51` says `SupercuspidalContragredientStatement` is not yet proved. `GeneralLinear.supercuspidalContragredient` (`SupercuspidalContragredientProof.lean:65`, artifact `a090c713`) proves it. (b) `Representation/Classification/SegmentConstituentCompatibilityStatement.md:146` says the Library has no contragredient map on supercuspidal classes. `SupercuspidalContragredient.lean` (artifact `1269a9fc`) defines `GeneralLinear.SupercuspidalClass.contragredient` (line 112), `PadicField.TopologicalData.supercuspidalClassContragredient` (line 206) and `PadicField.SupercuspidalClass.contragredient` (line 227), with involutivity (lines 216, 232). Each takes the statement as an explicit argument, which the proof supplies. (c) Lines 164–165 of the same file call the statement unproved. Line 187, "No proof is given", is also stale for the central-character clause, which `segmentConstituentCentralCharacter` (artifact `fb068e0c`) proves. | Cite all of these. The relation definitions keep their local proof boundary. The twist and contragredient clauses of segment compatibility remain unproved. |
| P3-074 | Holds | `Correspondence/UnramifiedNormalization.md:58–62` says that uniqueness of the spherical constituent up to isomorphism and its independence of the order of the characters are not proved. `Unramified.sphericalConstituentUniqueness` (`Unramified/SphericalConstituentUniquenessProof.lean:12`, artifact `9414444f`) proves `SphericalConstituentUniquenessStatement` for equal unordered spectra. The bridges `characterTuple_characterValues` and `hasSphericalSpectrum_iff_characters` (`Unramified/PrincipalSeries.lean`, artifact `15ddbb22`) apply it to the actual principal series. The audit's locator `UnramifiedNormalization.lean:102` is imprecise. | Cite these results. Jordan–Hölder multiplicity one is neither stated nor proved, and it is not the one-dimensional fixed line of `sphericalFixedLine`. |
| P3-075 | Holds | `Correspondence/ArithmeticFactors.md:34–38` says Frobenius-lift independence is proved only for common-closure pairs. `LocalFactor.WeilDeligne.rationalLFactor_eq_of_coset` (`LocalFactor/WeilDeligne.lean:385`) and `rationalLRatio_eq_of_coset` (`WeilDelignePair.lean:190`) hold for arbitrary pairs and normal subgroups. `localInertia F` is the kernel of the degree map (`Weil/Local/Assembly.lean:54`), so degree-one lifts satisfy the coset condition. | Cite the general theorem and the descent through representatives. No separate class-level theorem exists. The conditions for existence of epsilon data stay separate. |
| P3-081 | Holds | `Representation/Classification/ParabolicConeStatement.md:130–131` lists the coordinate specialization and matrix containments among steps still needing proofs. `glParabolicRootWeightCone` (artifact `04d4ae96`) proves them, with inputs `glBlockConeExists` (artifact `5af554a2`), `glBlockConeUnique` (artifact `286a142d`) and `glBlockCoarseningSubgroups` (artifact `6a11d299`). | Cite the coordinate and matrix results. The abstract `RootWeightConeDecompositionStatement` is unproved, and the proof does not use it. |
| P3-082 | Holds | `Representation/Classification/ProductLeviChamberBoundStatement.md:88–103` describes an "intended proof" whose steps "remain to be proved". `glProductLeviChamberCoefficientBound` (`ProductLeviChamberBoundProof.lean:1113`, artifact `6759068e`) proves `GLProductLeviChamberCoefficientBoundStatement.{uF,uV}` with the original admissibility, exponent and positive-`η` hypotheses and no irreducibility premise. The sufficiency target is proved by `glProductLeviTemperedExponentSufficiency` (artifact `7c47e42e`). | Cite both. |
| P3-083 | Holds | `Representation/Classification/TemperedExponentEdgeStatement.md:55–56` (also lines 35–36) says the edge identifications still need Lean proofs. `glTemperedExponentEdge` (`TemperedExponentEdgeProof.lean:193`, artifact `93bf68a7`) proves both clauses of `GLTemperedExponentEdgeStatement` with independent universes. | Cite it. At the audited commit `GLTemperedExponentCriterionStatement` had no proof. Since `f35c1c21`, `glTemperedExponentCriterion` proves it and uses `glTemperedExponentEdge`. The final text says so and keeps the consumers' `hcrit` hypotheses. |
| P3-085 | Holds; nearby text in the same file was also out of date | `Representation/CuspidalSupport/LeviAdmissibleFactorizationStatement.md:125–127` calls the finite Levi factorization unimplemented. `padicLeviAdmissibleFactorization` (`LeviAdmissibleFactorizationProof.lean:157`, artifact `908ea769`) proves `PadicLeviAdmissibleFactorizationStatement.{uF,uW}` for positive rank, with factors in the source carrier universe and only irreducibility and all-open-subgroup admissibility as hypotheses. Lines 110–112 and 188–195 also call `AdmissibleProductFactorizationStatement` unproved, but `admissibleProductFactorization` (`Smooth/Factorization/TwoFactorExistenceProof.lean:590`, artifact `1470f0d7`) proves it. | Cite both. Lines 135–136 now say that total disconnectedness is proved only by private lemmas. No public theorem exists. |
| P3-086 | Holds; nearby text in the same file was also out of date | `Representation/CuspidalSupport/LeviTensorFactorizationStatement.md:91–93` says the small-realization steps remain outstanding. `padicLeviCuspidalFactorization` (`LeviTensorFactorizationProof.lean:41`, artifact `cf3ee414`) proves `PadicLeviCuspidalFactorizationStatement.{uF,uW,uV}` with an independent universe `uV` and no cardinal or shrinking premise. It uses `padicLeviAdmissibleFactorization`, `padicLeviTensorSupercuspidalReflection` (artifact `60fde00b`) and `padicIrreducibleSmoothSmallRealization` (artifact `b9fc82a3`). Lines 83–87 and 141–142 also call `AdmissibleProductFactorizationStatement` unproved, but artifact `1470f0d7` proves it. | Cite these companions and keep the independent universes. |

### Proposed counterexamples and suggested corrections

The audit proposes no counterexamples for these findings. Each suggested correction was checked independently against the full theorem type, its section variables and the target statement.

- In P3-023, P3-065, P3-068, P3-069 and P3-070 the audit understates what is proved. The text above lists these cases, and the corrections describe the Library as it is.
- For P3-066 the audit says the embedding proof supplies the documented support-existence route and leaves out support uniqueness and rank zero. Both limits are kept.
- For P3-074 the audit warns against confusing constituent uniqueness or the fixed line with Jordan–Hölder multiplicity one. The correction follows that warning.
- For P3-083 the audit asks to preserve the separate scope of the full criterion. That criterion has since been proved, and the correction says so while keeping the scope distinction.

All other suggested citations agree with the Lean declarations.

## Corrections and the commits where they entered the Library

Every correction concerns one file pair. Except for the P3-072 GK docstring, its Lean bytes are identical to the audited commit. Each was checked by machine (schema, references, Lake build and declaration kind) and entered the Library at the commit shown.

| Finding | Kind and entry declaration | Publication commit |
| --- | --- | --- |
| P3-012 | statement `Langlands.GLOppositeJacquetSubquotientExponentInheritanceStatement` | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| P3-017 | statement `Langlands.ClassFieldTheory.Global.RelativeWeilGroup.AssociatedFactorStatement` | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| P3-023 | statement `Langlands.FiniteLengthAdmissibilityStatement` | `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` |
| P3-065 | statement `Langlands.GLRegularLanglandsQuotientStatement` | `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| P3-065 | statement `Langlands.GLRegularLanglandsQuotientStatement` | `f6b64ec108eed89ad46dff1d99192f40c4f29015` |
| P3-066 | definition `Langlands.PadicField.TopologicalData.IsSupercuspidalSupport` | `6a6c913c7339c50634dd74722034032e7a167d97` |
| P3-067 | statement `Langlands.GLTemperedDiscreteSeriesOppositeToUpperStatement` | `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` |
| P3-068 | statement `Langlands.GLDiscreteSeriesJacquetPrerequisitesStatement` | `580b2c58235b01b777ad92e616d50469d9ad93ba` |
| P3-068 | statement `Langlands.GLTemperedDiscreteSeriesPrerequisitesStatement` | `580b2c58235b01b777ad92e616d50469d9ad93ba` |
| P3-069 | statement `Langlands.GLTemperedInductionPrerequisitesStatement` | `f6b64ec108eed89ad46dff1d99192f40c4f29015` |
| P3-070 | statement `Langlands.Classification.AllPadicUnitaryGenericCompatibilityStatement` | `7e64f8e360c8778e04e5da7f9cd382cda7c837f6` |
| P3-072 | statement `Langlands.GelfandKazhdanContragredientStatement` | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| P3-072 | statement `Langlands.Correspondence.SupercuspidalGammaFromFactorsStatement` | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| P3-073 | definition `Langlands.Correspondence.IsSupercuspidalSmoothDual` | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| P3-073 | statement `Langlands.Classification.PadicSegmentConstituentCompatibilityTheorems` | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| P3-074 | definition `Langlands.Correspondence.UnramifiedCompatibility` | `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| P3-075 | definition `Langlands.Correspondence.IsArithmeticPairEpsilonFactor` | `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| P3-081 | statement `Langlands.GLParabolicRootWeightConeStatement` | `6a6c913c7339c50634dd74722034032e7a167d97` |
| P3-082 | statement `Langlands.GLProductLeviChamberCoefficientBoundStatement` | `cde31751c7864199419ad8fae8b7f3474639ba24` |
| P3-083 | statement `Langlands.GLTemperedExponentEdgeStatement` | `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` |
| P3-085 | statement `Langlands.CuspidalSupport.PadicLeviAdmissibleFactorizationStatement` | `cde31751c7864199419ad8fae8b7f3474639ba24` |
| P3-086 | statement `Langlands.CuspidalSupport.PadicLeviCuspidalFactorizationStatement` | `cde31751c7864199419ad8fae8b7f3474639ba24` |


P3-065 has two corrections. `b2301a2c` rewrote the status paragraph and was accurate when published at `64f062d4`. The later publication of `glTemperedExponentCriterion` made its sentence "the tempered criterion … is unproved" false, so the follow-up `5ebefa12` changes that bullet only. P3-068 and P3-072 each have two candidates, one per assigned file pair. P3-073 likewise has two, for `SupercuspidalRelations` and `SegmentConstituentCompatibilityStatement`.

### Earlier versions that did not enter the Library

Several corrections had earlier versions that did not enter the Library.
Four were rejected for substance, and the versions in the Library correct
those passages: a P3-023 version still called the finite-length proof future
work after `FiniteLengthProof` had entered the Library at `b58bd42a`; a P3-070
version listed `RealTwistOrdinaryDualClause` as unproved, although the
construction `segmentFactorSmoothDualEquiv` already supplies that clause in
full; another P3-070 version said that no declaration of the Library gives
the scalar-twist character `ω * χ.toMonoidHom ^ n`, although the third
conjunct of the theorem `glConstituentCentralCharacterFor` proves it; a
P3-083 version said `GLTemperedExponentCriterionStatement` has no proof, which
became false at `f35c1c21`; and a P3-085 version kept a sentence claiming a
convention comparison that `TwoFactorExistenceProof.md:29–34` shows is not
needed. The other earlier versions were identical to the versions in the
Library.

## What remains unproved

A scan of `7e64f8e360c8778e04e5da7f9cd382cda7c837f6` finds no theorem proving any of these statements. The corrected files describe them as unproved:

- `GLSupercuspidalSupportUniquenessStatement`;
- `RootWeightConeDecompositionStatement`;
- `GLFixedCentralCharacterSplittingStatement`;
- `GLWeaklyCriticalPairMinimalityStatement`, and hence the whole of `GLWeaklyCriticalTemperedRefinementStatement`;
- `GLTemperedInductionPreservationStatement`, `GLTemperedInductionStatement` and `GLTemperedInductionPrerequisitesStatement`;
- the three clauses of `GLRegularLanglandsQuotientStatement`, and Silberger's intermediate statements other than the maximal-cone statement;
- the five unitary-generic clauses that no published declaration supplies in full (`UnitaryBlockRealTwistHermitianClause`, `UnitaryBlockOrdinaryDualClause`, `UnitaryBlockCharacterTwistClause`, `TwistedProductCentralCharacterClause`, `ScalarCharacterTwistDualClause`, whose determinant-twist conjunct is proved) and both aggregate statements;
- `SupercuspidalGammaFromFactorsStatement` and the twist and contragredient clauses of segment compatibility.

Jordan–Hölder multiplicity one for unramified principal series is not stated in the Library.

## Related stale passage outside the files concerned

`Langlands/Representation/Classification/MaximalConeStatement.md:7–9` calls `GLMaximalConeJacquetQuotientStatement` "a derived proposition definition, not a proved theorem". That is literally true of the statement module, but the file never says that `glMaximalConeJacquetQuotient` proves it. The file lies outside the file pairs concerned and was not edited.

## Checked file fingerprints at the audited commit

SHA256 at `3987c3d7445531c2c7f784464a3fd47061ba0865` of the 21 assigned file pairs. The first column is the common path of the `.lean` and `.md` pair.

| Module path | Lean SHA256 | Markdown SHA256 |
| --- | --- | --- |
| `Langlands/Automorphic/AssociatedFactorStatement` | `800371a5ff6380d4566b306e8886a77e36635cf34ae05d195c0d6d5e6b7bfe9e` | `7a23d92f28c95da318f1798b3eb78cc95bdc5d0388fcbe73258712f5b0c3d14c` |
| `Langlands/Correspondence/ArithmeticFactors` | `5ae9d179ff86c24824a038ab1d87a3af614c565e03a2b1c78b239b32501250fa` | `27b25df19e25a313153795a9f19a71693f4c0e99c922a49a091b68ffece0bfe7` |
| `Langlands/Correspondence/SupercuspidalGammaCompatibility` | `7ae55a2d2d8752018c3f4c6a3b8be108c63ed7451b5886754d903bf2b1bf8d53` | `9ccbfea9669880c139768e9c94dc4eb62e7ded8756c9c238050248afd3330bda` |
| `Langlands/Correspondence/SupercuspidalRelations` | `701f46d9e7006ef8e2868501a82b8b43a10804c8b620ce10d205dc530c7b649f` | `80dc34ca1f0d6acec7ccde62f064483d6acfe9f1c1661e3222966148c660d2a9` |
| `Langlands/Correspondence/UnramifiedNormalization` | `0e9c50c34985391524280dea47eb24e19d46660e3999262a89e6007827fa89bd` | `135569540a9dc32aaaf78682e2496a3c3e0615c4a06307f89e67b98dc5b6d04b` |
| `Langlands/Representation/Classification/DiscreteSeriesJacquetStatement` | `5b09a7d89f3fb1c93586d80094913bef3ebc3502896de8cb2614cddc9fb2ac86` | `3c91ff70253c6880cad111aa2e5e32784766db1015e472ff94640f7ff1f31daf` |
| `Langlands/Representation/Classification/DiscreteSeriesOppositeToUpperStatement` | `a0c9aa742a9be56aa59c6abd1edec7a87e3231bdae54412831aae7f7f40df931` | `48d4ff1ac75ddf7ac6ec682e60dc766db6aed663c95709f08869d39b6fb21de1` |
| `Langlands/Representation/Classification/ParabolicConeStatement` | `736ede21c1c33afa56f3aa067aac4c80049c5dd61be0452fcaf50e90fc3f5815` | `63e6d7352d9517fe784e9980183c5cd9bc31c60bb075af329d9184cd41542b13` |
| `Langlands/Representation/Classification/ProductLeviChamberBoundStatement` | `5759706223855c66935827cd80eba1c48b156809a9bffd575d3c3d7fb97933ca` | `1bc3656bf6f6e8dd53e9d5e2c1fe7b82fcf858ab8379330b02a5541a00f1dae4` |
| `Langlands/Representation/Classification/RegularLanglandsStatement` | `ce6da19d4d611e50551e31edd5404f4d83d14d90a645d6d00b5cb26d26d7e352` | `077b6571c0930b6b3a8dfdf7f245ce5f2ebd4eba2de5caf34eb48c0671100edf` |
| `Langlands/Representation/Classification/SegmentConstituentCompatibilityStatement` | `0efd1b50ee4894259c2fa698529ec2976494ab9d825cdd2a71b49390873b0338` | `0c3f61911c7040a2411dbff79b4af2f5c53b3f00d4bb8d8c1a66bdc416c2c8b9` |
| `Langlands/Representation/Classification/SupercuspidalSupport` | `4680302c6b5ad320893b38e1787f11739aca615cc8f44b38021824423089990a` | `fd523206848c28bd4077f2c862ea47f6f5c4e2adaf83f522be12a77d1deb59c2` |
| `Langlands/Representation/Classification/TemperedExponentEdgeStatement` | `49e08cede3a86e228de9bcd6683006184c45cd1923558cb53673eab2a1c2686e` | `b97d4d39965f9d07db5663921f4c76c6955a342742ae36faf07bc67e0227de26` |
| `Langlands/Representation/Classification/TemperedInductionStatement` | `119272506a480330549a4c10c12a3cc25cc10830488c852094d7705bc989db90` | `be58ef1ef9ae583f6f32d6be5b50cf2c60d2a7ba933c5110e458f3e74c8b19c2` |
| `Langlands/Representation/Classification/TemperedSupportStatement` | `b9bd252df661d89a93ddfbb154391e7370978a8d8e89ff03f272bf84820519b4` | `6d613d78f2ad5a88932f303d296c5159fcc481c44ed602075ee5492b839cee05` |
| `Langlands/Representation/Classification/UnitaryGenericCompatibilityStatement` | `743b1379e5142b26f1e867aba13b12371a2ffcc2437d3ed994a8aa6b2b531063` | `ca6f069c9e9ab33a818bdfa3448361a0707081ae77b16880609a52e5b6d850e2` |
| `Langlands/Representation/CuspidalSupport/LeviAdmissibleFactorizationStatement` | `f1489326737d0cbc5930992490f2acba3e28013dc0da1106b5e27e579dbf0867` | `286d3735847189a46f9a9fb2ea64aeb981246453ab74884d54d278119da92730` |
| `Langlands/Representation/CuspidalSupport/LeviTensorFactorizationStatement` | `39e7efdf6a13aafa747882e2947535ab8da0568fdc10c928e89dfc211bb7118a` | `8ddf1d42783802fddef374e4e939cc3c6f8d9927fa78b8ce3c489b873a47e752` |
| `Langlands/Representation/Exponents/OppositeJacquetSubquotientInheritanceStatement` | `05c2139118129f3672cc53804fe44660569e2c9605cc76c612101a429a624875` | `7156216b06ae636d4fc411d46f3d733063d8129708f069bd8bc55c3212e420a4` |
| `Langlands/Representation/Smooth/Admissibility/FiniteLengthStatement` | `82735dd13676b49a523566ed0446e38643471480d23fca886cc8b88ef000d19b` | `81748739e936e0d21338562b0c60ea8f8a9240616ecf97a80f574902f730112e` |
| `Langlands/Representation/Smooth/Contragredient/GelfandKazhdanStatement` | `4a64796a0a53beef04238fa957e2ee2ce40187c17a03cffca76dd56a22dfd7ad` | `32b7096489e1bc38dc4608411aa654c8a91065c264eb9d34609db75fe8968406` |

## Corrected file fingerprints at the final commit

SHA256 at `7e64f8e360c8778e04e5da7f9cd382cda7c837f6`. All 21 Markdown files and one `.lean` file (`GelfandKazhdanStatement.lean`) differ from the audited commit. Each is byte-identical to the file of the last published candidate for that pair. No other `.lean` file of the 21 pairs changed.

| Finding | File | SHA256 |
| --- | --- | --- |
| P3-017 | `Langlands/Automorphic/AssociatedFactorStatement.md` | `81a5177fd934f311a6b63a13f18f0819f8233978d1165ba30103bbea51a0a22e` |
| P3-075 | `Langlands/Correspondence/ArithmeticFactors.md` | `2b6c647408a23f89f340d3c0c5304f05b06d7fa040cc8b231302a8ddc90d17de` |
| P3-072 | `Langlands/Correspondence/SupercuspidalGammaCompatibility.md` | `409ee0f04e585767ed082e697f579d5bf220e26a15155e3b3d8953d1b74718a1` |
| P3-073 | `Langlands/Correspondence/SupercuspidalRelations.md` | `b68f655249d77bd7a42ad36fb3d363d7cb78bfc81b0c30f317de6a84c32efed3` |
| P3-074 | `Langlands/Correspondence/UnramifiedNormalization.md` | `f8edd76283052d2b17c25e9526965c33d3b588afa6f6e80f5ec0b7dcc5379965` |
| P3-068 | `Langlands/Representation/Classification/DiscreteSeriesJacquetStatement.md` | `e1aeb9625fddffe06f9b2f7a768daa2d3e539ca85eb04897c4615d3e9516d98a` |
| P3-067 | `Langlands/Representation/Classification/DiscreteSeriesOppositeToUpperStatement.md` | `7b5dd1cec442c2086968e50ffc5c1e64a6530abf14507382874214646297b6e6` |
| P3-081 | `Langlands/Representation/Classification/ParabolicConeStatement.md` | `3f4e8755df5ca796bcb8e2b70ec859dd49b7adbb6a6406345a20dce281ee9fd3` |
| P3-082 | `Langlands/Representation/Classification/ProductLeviChamberBoundStatement.md` | `61338ddc82b36a9f8fe93bedf1b2bc465671b430578e9a14b79044d095ca6874` |
| P3-065 | `Langlands/Representation/Classification/RegularLanglandsStatement.md` | `c45725c3faf41a59d39c5d0b7197849226c8104d277287f0150dfe1f1b685f62` |
| P3-073 | `Langlands/Representation/Classification/SegmentConstituentCompatibilityStatement.md` | `62d19df82ed6ef5ff3e917182ae1fd361b408c1f6e4ef8af9493d9ba10a0faf7` |
| P3-066 | `Langlands/Representation/Classification/SupercuspidalSupport.md` | `7f8064dc6500a598053a8dcbf6dfba8fdc1a6413b49ccb4cabc3267eae4e6e1f` |
| P3-083 | `Langlands/Representation/Classification/TemperedExponentEdgeStatement.md` | `49f04530d5043c43beb93ca94756112e6859ff8667f0f92aed7dd66dde52af3e` |
| P3-069 | `Langlands/Representation/Classification/TemperedInductionStatement.md` | `1f94e075a6c3174bf8743fa438365236b5f11bdd04289fbe45b402475df85c52` |
| P3-068 | `Langlands/Representation/Classification/TemperedSupportStatement.md` | `32047c7876072f552c9979e10fd8bcd8ad4224d1b32c2b7305081ac53424fdf0` |
| P3-070 | `Langlands/Representation/Classification/UnitaryGenericCompatibilityStatement.md` | `77aa1a23f065e4bf98e0d6d529a01e407f5aaf5b702c4e7b19b33d5f20aaf758` |
| P3-085 | `Langlands/Representation/CuspidalSupport/LeviAdmissibleFactorizationStatement.md` | `9b575b15486e19e351a66f325563489328ebf68d9c08241ee6e5e10e198144db` |
| P3-086 | `Langlands/Representation/CuspidalSupport/LeviTensorFactorizationStatement.md` | `339a46a357b532c67632fb509b9305a381eb77f8be2c37e74476e4d801fd0c46` |
| P3-012 | `Langlands/Representation/Exponents/OppositeJacquetSubquotientInheritanceStatement.md` | `451694fd298398f17f768887a6da68f044c55fb0e7efb2758bf70158de358d3c` |
| P3-023 | `Langlands/Representation/Smooth/Admissibility/FiniteLengthStatement.md` | `843d0cf807fc581f725f79153efdda98e6bfdd264f621cecf83e792b811e1a0a` |
| P3-072 | `Langlands/Representation/Smooth/Contragredient/GelfandKazhdanStatement.lean` | `1acddaf0533cbf03d7a8cf6dffd5cfe8998424315e36134a7125d89653df7078` |
| P3-072 | `Langlands/Representation/Smooth/Contragredient/GelfandKazhdanStatement.md` | `d95a498616c01041d4f6727ea52c5e1243bcd4045d9fec8b7e610bf7a8b0487d` |

## Source register

| Registered source ID | Original-file SHA256 | Use |
| --- | --- | --- |
| `external-library-audit-2026-10-29-3987c3d` | `d9a25f35dc2d7bef0351ba0891db168b0c3cc797a281d0a9944e930fe43d5eeb` | The allegations. |

The corrections change no claim about original literature. In P3-065 the Silberger (1978) lemma, proposition and corollary numbers are those already documented by the separate published statement modules cited in the verdict table. The source locators of every corrected pair are unchanged from its published record.

The environment is Lean 4.34.0 with Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Each edited module was compiled with `lean_check` beforehand; those checks are diagnostics, not proofs. The corrections' status rests on their entry into the Library, listed in the corrections section.

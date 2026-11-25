# External Library audit 2026-10-29: harmonic analysis, analytic geometry and Bruhat topology

This note records verdicts on the nine findings of this area from the *External Library audit 2026-10-29*. All nine hold as documentation defects at the audited commit. None required a change to Lean mathematics. Every correction changes only paired Markdown. Each kept the Lean bytes unchanged and is in the Library.

## Scope, sources and checked commits

The audit is registered as `external-library-audit-2026-10-29-3987c3d`. Its file is `FINAL_AUDIT_3987c3d.md`, SHA256 `d9a25f35dc2d7bef0351ba0891db168b0c3cc797a281d0a9944e930fe43d5eeb`. The assigned rows are at its lines 76 (P3-013), 77 (P3-014), 142 (P3-057) and 149–154 (P3-059 to P3-064). The report was read as a list of allegations, not as evidence.

The audited commit is Library `3987c3d7445531c2c7f784464a3fd47061ba0865`. It was still the Library head when verification of all nine findings was complete, so no intervening publication had repaired any finding. The verdict table cites locations at that commit. The final check commit is `64f062d4c57e9cc6f8151bc80364bc55c16272c5`, the Library head after the last correction was published. The publication table and the corrected-file fingerprints identify the current evidence. The check was repeated at the Library heads `c8ae014c2d620066bb3bf73f1183de72515b8c6c` and `f35c1c217068f79dff12263770d16a95f9632251` when this note was resubmitted. All 37 file pairs of the fingerprint tables, the sixteen P3-060 and P3-061 proof `.lean` files and the six out-of-scope files listed below are byte-identical there to `64f062d4`. From `c8ae014c` to `f35c1c21` the Library only added files. None of them mentions the targets this note calls unproved.

The conclusions concern only the assigned wording and the declarations needed to check it. In particular they do not assert the Shalika distribution theorem, Whittaker multiplicity one, automorphic differential growth, Mellin convergence or continuation, whole-spectrum or nontrivial standard rational gluing, or the full scope of Berkovich's Definition 2.2.1.

## Corrections

Each of the eight corrections is a focused change covering one finding; the
only one covering two findings joins P3-014 and P3-059 on the two Bruhat
files. No correction changes a Lean statement or proof target, and every
changed file belongs to the file pairs concerned.

## Per-finding verdicts at the audited commit

All paths begin at the Library root. Line numbers refer to commit `3987c3d`.

| Finding | Verdict | Location and decisive evidence | Decision |
| --- | --- | --- | --- |
| P3-013 | Holds | `Langlands/Geometry/Analytic/GeneralizedAffinoid/BinaryLaurentDiagram.md:41` calls `overlapEquations` a two-element set. The Lean set (`BinaryLaurentDiagram.lean:28–33`) is `{X₀ - C(f), C(f) * X₁ - 1}`. `PresentedAffinoidAlgebra` (`GeneralizedAffinoid/Definitions.lean:16–20`) requires only a closed ideal, so the closed unit ideal is allowed and gives a zero carrier. The relative series algebra is then zero, both relations are `0` and the set is `{0}`. The same file's line 169 already permits unit relation ideals and zero bases. | Describe the set of the two displayed relations, with at most two elements. Add no nontriviality assumption. |
| P3-014 | Holds | `Langlands/Group/GL/UpperBruhatFiltrationGeometryStatement.md:175–182` lists local closedness of each cell among non-consequences. Conjuncts 3 and 4 of the proposition (`…Statement.lean:17–24`) say that the neighborhood `C_w ∪ higher cells` is open and that `C_w` is closed in it. Hence `C_w` is that open set intersected with an ambient closed set. Additional stale text in the same file: lines 5–9 and Status lines 188–192 say the proposition is unproved, but `upperBruhatFiltrationGeometry` (`UpperBruhatFiltrationGeometryProof.lean:159`) proves it. | State local closedness as a consequence, not as a proof of the full target, and cite the published proofs. |
| P3-057 | Holds | `Langlands/Global/ArchimedeanConvolutionGrowthStatement.md:32–36` calls transfer of right-translation differentiation through the convolution an unproved prerequisite, and lines 76–81 list it with compact-support preservation as outstanding. `compactKernelConvolutionDifferentiation` (`ArchimedeanConvolutionDifferentiationProof.lean:93`), derived from `compactKernelConvolutionRealDifferentiation` (`ArchimedeanConvolutionRealDifferentiationProof.lean:185`), proves smoothness and enveloping-algebra differentiation transfer. Its scope is every Borel-compatible measure finite on compact sets (no left invariance), every `f : C(InfiniteAdelicGL K n, ℂ)` and every smooth compactly supported kernel. `envelopingCompactSupport` (`ArchimedeanEnvelopingSupportProof.lean:91`) proves support preservation. Additional stale text: lines 3–8 and 70–74 present the bound as unproved, but `compactKernelConvolutionBound` (`ArchimedeanConvolutionGrowthProof.lean:14`) proves it. Lines 24–26 say a nonzero Haar measure will be constructed, but `leftHaarMeasure` and `exists_borelLeftHaarMeasure` (`ArchimedeanConvolution.lean:76,169`) supply one. | Cite these results with their exact scope. Smooth kernels only: the module's continuous-kernel statements are not covered by the differentiation results. Reproducing-kernel existence and `AutomorphicDifferentialGrowthStatement` remain separate and unproved. |
| P3-059 | Holds | `Langlands/Group/GL/UpperBruhatLocalClosednessStatement.md:5–8,114–118` call the proposition stated and unproved. `upperBruhatLocalClosedness` (`UpperBruhatLocalClosednessProof.lean:125`) proves exactly `UpperBruhatLocalClosednessStatement.{u}` for every Hausdorff topological field and rank. It uses the published `upperBruhatRankCharacterization`. | Cite the proof. It is not a proof of the Shalika or Whittaker results it serves. |
| P3-060 | Holds (8 of 8 files) | Eight files in `Langlands/HarmonicAnalysis/Distribution/` call their proposition unproved, or its proof a separate or later obligation, although a published proof with exactly that type exists (see the per-file table below). | Cite each proof with its artifact and publication commit. Recast "intended route" sections as the implemented route. For `TransposeInvariantStatement.md`, name `GenericContragredientStatement` and `GelfandKazhdanContragredientStatement` as separate propositions proved by separate published theorems, with no implication claimed in either direction. |
| P3-061 | Holds (7 of 7 files) | Seven files in `Langlands/HarmonicAnalysis/` keep "Remaining proof obligation" sections or "supplies no proof … a later proof must" wording, although published proofs exist (see the per-file table below). | Cite each proof. The conjunction `PadicAdditiveHaarScalingStatement` has no named proof and is described as following by pairing the two component theorems. No Mellin convergence, rational continuation or product-coordinate Haar claim is added. |
| P3-062 | Holds | `Langlands/Geometry/Analytic/GeneralizedAffinoid/RelativeEquationComparisonStatement.md:70` heads the proposition "Proposition awaiting proof", and lines 82–85 say the conclusions are stated for a separate proof. `relativeEquationComparison` (`RelativeEquationComparison.lean:185`) proves surjectivity, isometry for the specified quotient norms and the scalar-evaluation kernel criterion. Its scope is complete ultrametric `K`, arbitrary positive radii and an arbitrary set of extra equations. The same module constructs the explicit two-sided inverse `relativeEquationInverse` (lines 84, 107, 135). The statement file already includes trivial valuations and whole-ring relation ideals. | Cite the proof. Add no nontrivial-valuation or proper-ideal assumption. |
| P3-063 | Holds | `Langlands/Geometry/Analytic/RationalFactorization/Statement.md:41` calls the proposition unproved. Lines 47–49 call replacement of the unit-ideal hypothesis by absence of common spectrum zeros a separate obligation. `factorization` (`RationalFactorization.lean:127`) proves the target. `generatesUnitIdeal_iff_no_common_zero` (line 36) and `factorization_of_no_common_zero` (line 136) are public theorems of the same module, for complete ultrametric `K` and presented strict affinoid algebras. | Cite all three. Keep the restrictions to a complete scalar field, strict test algebras and unit radii. Full Definition 2.2.1, arbitrary radii and the relative-series comparison are not consequences. |
| P3-064 | Holds (both files) | `Langlands/Geometry/Analytic/StrictTestDomain/BinaryLaurentGluingStatement.md:134–148,155–158` and `NontrivialStandardRationalGluingStatement.md:220–226` call `TrivialScalarRationalLocalizationStatement` unproved. `trivialScalarRationalLocalization` (`TrivialScalarRationalLocalizationProof.lean:345`) proves it along the actual structural map. The rational datum carries only its no-common-zero condition, with no nonzero-denominator, reducedness or nonempty-spectrum hypothesis. In addition, `binaryLaurentGluing_of_trivialScalar` (`BinaryLaurentTrivialScalar.lean:87`) implements the trivial-scalar sketch of the first file, under the extra hypothesis that all scalar norms are at most one. | Cite both. `BinaryLaurentGluingStatement` for arbitrary `K`, `NontrivialStandardRationalGluingStatement` and `WholeSpectrumRationalGluingStatement` have no published proof and are described that way. |

### P3-060 and P3-061 per file

Verified, and rechecked independently, against `3987c3d` and `bc8de228`. Baseline lines are at `3987c3d`. Every cited proof was checked with a Lake build against its exact target. Its theorem line is the same at both commits.

| File (`.md`) | Stale lines at `3987c3d` | Proof theorem (Proof module line) | Publication commit |
| --- | --- | --- | --- |
| `Distribution/CharacterAverageCovarianceStatement` | 3–5, 81–82, 104–108, 174–176, 230–231 | `Langlands.HarmonicAnalysis.SchwartzBruhat.characterAverageCovariance` (`Distribution/CharacterAverageCovarianceProof.lean:21`) | `cb6a47b2` |
| `Distribution/ClosedRestrictionStatement` | 3–5, 88–90, 98–99, 107 | `Langlands.HarmonicAnalysis.SchwartzBruhat.closedRestrictionSurjective` (`Distribution/ClosedRestrictionProof.lean:60`) | `a2f65909` |
| `Distribution/ClosedSupportedDescentStatement` | 3–5, 117–120, 126–127 | `Langlands.HarmonicAnalysis.Distribution.closedSupportedDescent` (`Distribution/ClosedSupportedDescentProof.lean:43`) | `00be69b7` |
| `Distribution/FiniteOrbitVanishingStatement` | 3–5, 57, 70–71 | `Langlands.HarmonicAnalysis.Distribution.finiteOrbitAntiInvariantVanishing` (`Distribution/FiniteOrbitVanishingProof.lean:492`) | `00be69b7` |
| `Distribution/HomogeneousPositivityStatement` | 3–5, 73–75 | `Langlands.HarmonicAnalysis.Distribution.homogeneousIndicatorProportionality` (`Distribution/HomogeneousPositivityProof.lean:395`) | `6d91111e` |
| `Distribution/HomogeneousVanishingStatement` | 3–5, 54–55, 63–64 | `Langlands.HarmonicAnalysis.Distribution.homogeneousAntiInvariantVanishing` (`Distribution/HomogeneousVanishingProof.lean:103`) | `914d13e3` |
| `Distribution/LocalizationStatement` | 3–5, 60–62, 72–73 | `Langlands.HarmonicAnalysis.Distribution.equivariantLocalization` (`Distribution/LocalizationProof.lean:89`) | `d1e92cc3` |
| `Distribution/TransposeInvariantStatement` | 3–4, 76–77, 85–86 | `Langlands.generalLinearConjugationDistributionTranspose` (`Distribution/TransposeInvariantProof.lean:260`) | `910a6df8` |
| `FiniteTranslationOrbitStatement` | 5, 120–124, 131–134 | `Langlands.HarmonicAnalysis.finiteTranslationOrbit` (`FiniteTranslationOrbitProof.lean:133`) | `4021bb1d` |
| `PadicHaarScalingStatement` | 7, 46–50 | `Langlands.HarmonicAnalysis.padicScalarHaarScalingStatement` (`PadicScalarHaarScalingProof.lean:232`); `Langlands.HarmonicAnalysis.padicRectangularHaarScalingStatement` (`PadicRectangularHaarScalingProof.lean:253`) | `01a58491`; `dd9f9be5` |
| `PadicLatticeGeometryStatement` | 6, 159, 162, 170–171, 186–188 | `Langlands.HarmonicAnalysis.padicLatticeGeometry` (`PadicLatticeGeometryProof.lean:18`) | `a2f65909` |
| `PadicLatticeSchwartzExpansionStatement` | 8, 104, 112–113, 118–120 | `Langlands.HarmonicAnalysis.padicLatticeSchwartzExpansion` (`PadicLatticeSchwartzExpansionProof.lean:77`) | `b0ef093b` |
| `PrincipalUnitPowerCofinalityStatement` | 7, 62–63, 79, 127–129 | `Langlands.HarmonicAnalysis.principalUnitPowerCofinality` (`PrincipalUnitPowerCofinalityProof.lean:144`) | `2ae54bcc` |
| `SchwartzBruhatValuationBoundsStatement` | 8–9, 102–105, 114–116 | `Langlands.HarmonicAnalysis.schwartzBruhatValuationBounds` (`SchwartzBruhatValuationBoundsProof.lean:44`) | `4021bb1d` |
| `UnboundedConductorStatement` | 9, 103–106, 112, 119, 123–124 | `Langlands.HarmonicAnalysis.padicQuasicharacterUnboundedConductor` (`UnboundedConductorProof.lean:118`) | `24af03c7` |

Paths are relative to `Langlands/HarmonicAnalysis/`. The audit cites the first line of each listed range, or the stale section heading. Abbreviated commits are prefixes of full Library commits. The proof files of `ClosedRestrictionProof`, `PadicScalarHaarScalingProof` and `SchwartzBruhatValuationBoundsProof` were deduplicated after their proofs entered the Library and before the audited commit. Each now imports a shared module in place of one helper it declared itself. In `Distribution/ClosedRestrictionProof.lean` the private `exists_compact_clopen_neighborhood` was replaced by `Langlands.HarmonicAnalysis.exists_compact_clopen` from `RowTensorDecompositionProof.lean`. In `PadicScalarHaarScalingProof.lean` the public theorem `Langlands.PadicField.TopologicalData.t2Space` was removed. Its one use now calls the differently named public theorem `Langlands.PadicField.TopologicalData.fieldT2` from `Langlands/LocalField/Topology.lean`, and the Library no longer declares `Langlands.PadicField.TopologicalData.t2Space`. In `SchwartzBruhatValuationBoundsProof.lean` the public theorem `Langlands.PadicField.TopologicalData.continuous_normalizedAbs` was moved, with the same name and stated type, to `Langlands/LocalField/Normalization/Continuity.lean`. All sixteen cited statement-proving theorems keep their names and exact target types. All sixteen proof `.lean` files and all fifteen statement `.lean` files are byte-identical at `3987c3d`, `bc8de228` and the final commit `64f062d4`.

### Proposed counterexamples and suggested corrections

- P3-013: the audit's counterexample (closed unit ideal, zero carrier, singleton set) was checked independently in a development `lean_check`. It proved `overlapEquations K A f = {0}` for every `PresentedAffinoidAlgebra` with subsingleton carrier, and that the unit-ideal presentation has subsingleton carrier. Every declaration in the module uses only membership of the two relations, so no Lean content depends on the count. The suggested wording was adopted.
- P3-014: the audit's argument was checked in a development `lean_check`. It proved that `UpperBruhatFiltrationGeometryStatement.{u}` implies `UpperBruhatLocalClosednessStatement.{u}`. The proof uses Mathlib's `isClosed_induced_iff` to write the relatively closed cell as the trace of an ambient closed set. The converse is not immediate, and the corrected text says so. Shalika (1974), printed p.175 (PDF p.6), was reread. The proof of Lemma 1.7 states that `G_w` is locally closed, and the Corollary asserts that `Ω_w` is open and `G_w` is a submanifold of `Ω_w`. This agrees with the corrected description.
- P3-061, `PadicHaarScalingStatement`: a development `lean_check` (0 errors) checked that `⟨padicScalarHaarScalingStatement, padicRectangularHaarScalingStatement⟩` proves `PadicAdditiveHaarScalingStatement.{uF}`, and that all sixteen cited P3-060 and P3-061 proof theorems have exactly their statement types with the same universes.
- P3-057, P3-059, P3-060, P3-061, P3-062, P3-063, P3-064: each suggested citation was checked against the full theorem type, its section variables and the target statement. The audit's scope statements are accurate.

## Corrections and the commits where they entered the Library

Every correction keeps the Lean bytes of the audited commit. Each was checked by machine (schema, references, Lake build and declaration kind) and entered the Library at the commit shown.

| Finding | Kind and entry declaration | Markdown files | Publication commit |
| --- | --- | --- | --- |
| P3-013 | definition `Langlands.Analytic.PresentedAffinoidAlgebra.BinaryLaurent.left` | 1 | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| P3-014, P3-059 | statement `Langlands.GeneralLinear.UpperBruhatFiltrationGeometryStatement` | 2 | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| P3-057 | statement `Langlands.Global.ArchimedeanGL.CompactKernelConvolutionBoundStatement` | 1 | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| P3-060 | statement `Langlands.HarmonicAnalysis.Distribution.HomogeneousIndicatorProportionalityStatement` | 8 | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| P3-061 | statement `Langlands.HarmonicAnalysis.FiniteTranslationOrbitStatement` | 7 | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| P3-062 | statement `Langlands.Analytic.PresentedAffinoidAlgebra.Adjoin.RelativeEquationComparisonStatement` | 1 | `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| P3-063 | statement `Langlands.Analytic.RationalFactorization.FactorizationStatement` | 1 | `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| P3-064 | statement `Langlands.Analytic.StrictTestDomain.BinaryLaurentGluingStatement` | 2 | `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |

Where a correction has more than one Markdown file, the extra files were changed in the same correction. They are the second Bruhat file (P3-014, P3-059), the seven further Distribution files (P3-060), the six further harmonic-analysis files (P3-061) and `NontrivialStandardRationalGluingStatement.md` (P3-064). An earlier version of the P3-062 correction, with identical Markdown, did not enter the Library.

## Related stale passages outside the files concerned

These passages were noticed during verification. They lie outside the file pairs concerned, so they were not edited.

- `Langlands/Group/GL/UpperBruhatBoundaryStatement.md:8,174` calls the proposition unproved. `upperBruhatBoundary` (`UpperBruhatBoundaryProof.lean:377`) proves it.
- `Langlands/Group/GL/UpperBruhatRankStatement.md:130` says the statement "remains unproved here". That is literally true of the module, but `upperBruhatRankCharacterization` (`UpperBruhatRankProof.lean:221`) proves it.
- `Langlands/Global/ArchimedeanConvolutionGrowthProof.md:69–74` lists transfer of enveloping differentiation as a separate obligation. The P3-057 evidence above shows it is published.
- `Langlands/HarmonicAnalysis/Distribution/CharacterAverageFactorizationStatement.md:4–5,143–167` and `CharacterAverageSurjectiveStatement.md:155–158` describe the proofs as later work. `characterAverageFactorization` and `characterAverageSurjective` are in the Library.
- `Langlands/HarmonicAnalysis/Distribution/TransposeInvariantProof.md:181–183` says the pair is not yet in the Library; it is.

All six files were still unchanged at the final check commit `64f062d4`, at `c8ae014c` and at `f35c1c21`.

The comparison list in `BinaryLaurentGluingStatement.md:120–133` at `3987c3d` (Achinger's direct quotients versus the Library presentations) lies outside P3-064. It was not re-audited, and the P3-064 correction left its content unchanged.

## Checked file fingerprints at the audited commit

SHA256 at `3987c3d7445531c2c7f784464a3fd47061ba0865`. The first column is the common path of the `.lean` and `.md` pair.

| Module path | Lean SHA256 | Markdown SHA256 |
| --- | --- | --- |
| `Langlands/Geometry/Analytic/GeneralizedAffinoid/BinaryLaurentDiagram` | `ecb392830b6fe4790ce47263893731022dced3110a14d36d8c7e6d77ced4881b` | `f19926b8adf78d3b123e136624cc3ca9deca72d6572c14122d9daa65dc2206fd` |
| `Langlands/Geometry/Analytic/GeneralizedAffinoid/Definitions` | `af26779ed6b988b94654c5f95dbb1c73b3236ed381b8fc9761a7a4fe6cce4ca9` | `defe2372e12b422b5c8243fb36985b929a0ba4eaf085fee2855e60f67131be72` |
| `Langlands/Geometry/Analytic/GeneralizedAffinoid/RelativeEquationComparisonStatement` | `52e4f703201d6b65707d0fa15898d56414f84c5e60491c96f8a1ab31ed7b94eb` | `53f86fe2216730d06acf7439067947a482de634f9fa6ad05b2f9f9429ad7bafa` |
| `Langlands/Geometry/Analytic/GeneralizedAffinoid/RelativeEquationComparison` | `4d9e0140b5bfb78ce31f2fe250fb670bcf2f83d90e6dad4f164899448d78086c` | `f2b6eace78b82dbeb28ae3688902866ddec80f9fe8fa9756aae9a07fd9d4bfdd` |
| `Langlands/Geometry/Analytic/RationalFactorization/Statement` | `a9726a09ed6eb322eaa5fb407f80c1eeb7f33f461ae5811f816b74a12c58bfbf` | `386fb25f3c071b75f26c6cc5f1d73e4f0211050eed526bbb32dd66a6401e3736` |
| `Langlands/Geometry/Analytic/RationalFactorization` | `4b51d93d5bb4d2f23c5b6427bdfe1b0a673a0f5a11a265d06278010fe52dbd05` | `9cb62e7507a8a786fd1464a255f8b4097c5bdc26671f06fa898c25b4cc5fb6fc` |
| `Langlands/Geometry/Analytic/StrictTestDomain/BinaryLaurentGluingStatement` | `1ae734ac6125351bcac288319e3a5e00e676d0ae75c681d974b5d30c1fcb375c` | `20c301c0b4e09db57227360ec4ec1e938be1296e0f252522f1f283cf177903b1` |
| `Langlands/Geometry/Analytic/StrictTestDomain/NontrivialStandardRationalGluingStatement` | `4e534a262fbcec21854db7f63e3ad7bf7d5fe3083307f6e6b0c54f1f1c9504d1` | `0971dd4fcc5e2731b76d76e4079e960ca827609f2be9733b554dbff3238625a0` |
| `Langlands/Geometry/Analytic/StrictTestDomain/TrivialScalarRationalLocalizationStatement` | `4071e87a1303b83403e49533630138f55a05012eb40264cf8fe87cb4a6374aca` | `35e9138ead0374db03f56e766453c0e079df3f594dce90e09f4cad2297995b15` |
| `Langlands/Geometry/Analytic/StrictTestDomain/TrivialScalarRationalLocalizationProof` | `c973f666e4c6eaab3564445352857302f1d458ad032925ed44739b23eb7fbcc1` | `5fda71c1067747dcbf577259640c20878b9d21d7e8a14df8717fa4ae7f5e126e` |
| `Langlands/Geometry/Analytic/StrictTestDomain/BinaryLaurentTrivialScalar` | `e1f90b3a9cf93b8f4c3f252972a0e3245241ce15292974e59a8bf31b9cbf55cc` | `d34d9627d53777e010fba4fd0cd1759d70cc5c87690f689b9b8577bf073c1c93` |
| `Langlands/Global/ArchimedeanConvolutionGrowthStatement` | `43db5097c5ff1ae7fe56e55ecc7d008e5ce5b5934d7a9eaabdce574ac3934b2c` | `4f9e42831e79ecd717ea0b1f004d070fc9ac40c0488e5c1fa4cecfae06578ca5` |
| `Langlands/Global/ArchimedeanConvolutionGrowthProof` | `6001ee5828b42eddc7892c1c03ff22ffb21e8dbb440517d719a2f6bd6040aa72` | `5303fe2bb466eb51c67dca9d2f496d1c234f6cf817a0e04e15d4ad8a5c514394` |
| `Langlands/Global/ArchimedeanConvolutionDifferentiationStatement` | `c08897998d69fbe5088082e01bfb9b7be5c24fa0415feadc874d7f9e2667f090` | `2c653d4119a1c1a0e8632fe9b40f4b0a8d81ec63b4602c4d27fd0b67c9262995` |
| `Langlands/Global/ArchimedeanConvolutionDifferentiationProof` | `c9dc8009677fae0711474473249b956d508e5da4a796932767d5c87f90e0ed34` | `8fb9a9f24636d9fe8a641f522069dcb9bbd620adf7bb8019ceef9e1dcd8e7755` |
| `Langlands/Global/ArchimedeanConvolutionRealDifferentiationProof` | `c5d3c4d087b144fd2f9098689b67962978815f72ced7a8f60637835ff83775e3` | `f936fcf4e4c636c9f0dd55c56b4539722383e3fd4ac3c8a4685789f6e084284b` |
| `Langlands/Global/ArchimedeanEnvelopingSupportProof` | `decb7b395ee63177f3fdbb1ef3a53d6ec835c237f9f9723894af62c0d19c189c` | `73e9d6389e3a721ef27c7984305866e3de840a437d3db1b1fa516c67f418b211` |
| `Langlands/Global/ArchimedeanConvolution` | `69bb53b2651ef19566f5ece2637335b2453f78c9da419694b8ad594706f9e83f` | `c46591bf356c402d2a6b5ec16399dc9407bf738929ff369acb493661b49f83e9` |
| `Langlands/Group/GL/UpperBruhatFiltrationGeometryStatement` | `d74a9c24a9d39559859edd69bfc3a06708d00dae9f83fcf4db4d677fa6c7f4d3` | `c938729fd16bd396a4ced7cd26ae0799b1c1c5333aa773b5d4c67bc93493e974` |
| `Langlands/Group/GL/UpperBruhatFiltrationGeometryProof` | `7c8a7887faf3f52fd9f092782972e98590e09192f60359b7db1bf4dcee05d9e8` | `fd6d136001875d6cf5bde085c57179f844c9616a4c605fe42adf1ad0296e6e3f` |
| `Langlands/Group/GL/UpperBruhatLocalClosednessStatement` | `604750a387c05cf894ff07d417a9e00a397e5c0d0ab1b7894e8297e696649ffe` | `01fab58c828a701476c17a2d4427473f71f4ef5cdab6785a0dbd1db56f59cad9` |
| `Langlands/Group/GL/UpperBruhatLocalClosednessProof` | `5daba928e3589ee1ebeee12af85572d98ce052bcd91820f56589022a16402611` | `2b7bbe8344c8a973a680e61089ebb030bff8652728c184315902f63b6d18f1f0` |
| `Langlands/HarmonicAnalysis/Distribution/CharacterAverageCovarianceStatement` | `a15d714788efdc8bc5c9b7bb67fe8dba2477c766090b5c912a6b45f90cf2caa4` | `ff20fabd75ea4a32b3f4134d8f3d35b60fad3c9ab732511c86ff282ca3b42b17` |
| `Langlands/HarmonicAnalysis/Distribution/ClosedRestrictionStatement` | `190d93aaa176f351c54128b382e8bc9e4847d5a74c9a996bc5e7287b7c0e770d` | `3181a594ce9afa584fca6650e80edef0ba4fd32cac27f1043789b16db3af8962` |
| `Langlands/HarmonicAnalysis/Distribution/ClosedSupportedDescentStatement` | `ee0ca09157003fbc96c4d9bf71d40b326703cd12ea36341c3395b61db81c7d7d` | `adf91d03c314b381567058ea5c775b2278e20409dc422e5c280bbbcfb57b391e` |
| `Langlands/HarmonicAnalysis/Distribution/FiniteOrbitVanishingStatement` | `86ffea02d47def7f5cc7a3507233500c9a167c378f78addabdd749c3e33ec597` | `1b1716ecb95125e29afea06dab955005136d89659ebe9b38b71071b55899aaba` |
| `Langlands/HarmonicAnalysis/Distribution/HomogeneousPositivityStatement` | `04a3803dd7b2f1c87fad9fb83f4b4053fc0724af4d935e29604ee2d29f730ed8` | `76a623a16e7574403c8d7e3f6db1ec7989034940dc24605a0a37e97e9b921eb1` |
| `Langlands/HarmonicAnalysis/Distribution/HomogeneousVanishingStatement` | `d790186df289d18e8e32af8fca9033fa743c40aa9ffe1d06e30a392a5c8bbaa3` | `dfe94e1bfed7353fc2195211b413bb1148cd54f3f061e0bd889807a7494f57b8` |
| `Langlands/HarmonicAnalysis/Distribution/LocalizationStatement` | `de0062663915555201e89ed2ae0a3cc65bb8ca6cf6ed241da3f7e7e5d8c5ace9` | `d3b89b364475cdd1d2c47e5c1c6cf112e06523cbb2a4b9c0f54ed2fc76098a34` |
| `Langlands/HarmonicAnalysis/Distribution/TransposeInvariantStatement` | `8e745c42e89edfbe415e3e41991e54089c9137b445f43015256ed81fd9faf7ac` | `70138d56b667103da240cb327d00188f42984568e9cef84d0f82124622d30e89` |
| `Langlands/HarmonicAnalysis/FiniteTranslationOrbitStatement` | `5ab2b6e673c0d0e5ec605e8457e8baf724fa795694e44e9d358e93140de94b1d` | `38a473d220e6de80702a3db6286c666d60698f79e38873f9ec900c83609ffdf4` |
| `Langlands/HarmonicAnalysis/PadicHaarScalingStatement` | `84366b106ce213647dbccdccf6477cf19a01ebefaf549e68f2239424c420b2d2` | `1cf9e72ee95c06feb0e7f3968317ffcb7dc84e85e78738155d275d8c2745a2fc` |
| `Langlands/HarmonicAnalysis/PadicLatticeGeometryStatement` | `a713691a38c93a84ad51d17063f50806b59806e07d41febc7c9cc7d12559735e` | `236398f720f7f574d102205c7c9aad42f3af7eefd7d2107fa3c0b470713854d8` |
| `Langlands/HarmonicAnalysis/PadicLatticeSchwartzExpansionStatement` | `50efd113ce631def5a89751382008dd61c128ed013d74bdffcba7f61afe7b92d` | `58e58974ff1fadeaf6a4b24a62194ad9c68febc5a1ea4b370f9199dfc6e64fb2` |
| `Langlands/HarmonicAnalysis/PrincipalUnitPowerCofinalityStatement` | `691aa8f0687ffdfca56251446a90f8af21332649f0c15a778a078b40bd4a6119` | `d4e6427a8bde132fa712f15f4d0e7fab734c15f1a76c178b4a54948982c3f533` |
| `Langlands/HarmonicAnalysis/SchwartzBruhatValuationBoundsStatement` | `52e9bf07ac3d7ce1fad0b85dbe89db026c8727dff358967a2388f68b6aa8a7c2` | `2810960f64b185af6bf97d151592d41358f29a4bf1235a90835b3403dfca2581` |
| `Langlands/HarmonicAnalysis/UnboundedConductorStatement` | `df9542192c4cded26f00ebf059023352afae28d33fb35521f0665f20d5c86fa3` | `5c365648100c59f9114d17ec3ca95cc21bb5cb684d5ac591c6d04e1ce84fbfc7` |

## Corrected file fingerprints at the final commit

SHA256 at `64f062d4c57e9cc6f8151bc80364bc55c16272c5`, unchanged at `c8ae014c2d620066bb3bf73f1183de72515b8c6c` and `f35c1c217068f79dff12263770d16a95f9632251`. Among the 37 pairs of the table above, exactly these 23 Markdown files differ from the audited commit. Each is byte-identical to the corresponding file of its published candidate. No `.lean` file in the table changed.

| Finding | Markdown file | SHA256 |
| --- | --- | --- |
| P3-013 | `Langlands/Geometry/Analytic/GeneralizedAffinoid/BinaryLaurentDiagram.md` | `61b22cea6a1675e435676241e547ec80f1fcd7c8a7ba4ca95db70a3cdaaf86bc` |
| P3-014, P3-059 | `Langlands/Group/GL/UpperBruhatFiltrationGeometryStatement.md` | `cb31c1eacd73970ceba1a1d066e9635020f933c9028bbad910b606442c088839` |
| P3-014, P3-059 | `Langlands/Group/GL/UpperBruhatLocalClosednessStatement.md` | `0403f8f25ae9c34008b2d35a6da612344acf6042377da1c2904452e648d4a51a` |
| P3-057 | `Langlands/Global/ArchimedeanConvolutionGrowthStatement.md` | `ec2ca9d79bf144ccf8b1fcd8fdf522bb48c205bfcfb568911a04b01a77bd2f37` |
| P3-060 | `Langlands/HarmonicAnalysis/Distribution/CharacterAverageCovarianceStatement.md` | `ecedf286125c7be4b441b11f0eb6aad16e9a219ae28ae40d257c7b23f122be71` |
| P3-060 | `Langlands/HarmonicAnalysis/Distribution/ClosedRestrictionStatement.md` | `e215a7e742ce54077f92d54776be810ed3b3d6dcb6696a9e4e3a1c04211ec3e4` |
| P3-060 | `Langlands/HarmonicAnalysis/Distribution/ClosedSupportedDescentStatement.md` | `cd13aa1d64bb4176d702669b2ced12979eed6410e418c7098f2ae608f69fe6aa` |
| P3-060 | `Langlands/HarmonicAnalysis/Distribution/FiniteOrbitVanishingStatement.md` | `bce062b00e0daa9153a770eba27dea9c744c4249b48b836794ca39af828a4c7a` |
| P3-060 | `Langlands/HarmonicAnalysis/Distribution/HomogeneousPositivityStatement.md` | `d6270237a246b7c4b9a3228fa599a7b6f9ebe77fa917c9d4efdc996144abd701` |
| P3-060 | `Langlands/HarmonicAnalysis/Distribution/HomogeneousVanishingStatement.md` | `af6782d726a55b882c54d39b235090f0ffe5c28fdf3c9ac6e5465fe0618fae03` |
| P3-060 | `Langlands/HarmonicAnalysis/Distribution/LocalizationStatement.md` | `a998bbec6cbbf74295b0e59d5503596ec394f34496fd9d53f196341db01e3541` |
| P3-060 | `Langlands/HarmonicAnalysis/Distribution/TransposeInvariantStatement.md` | `4daaf9de083069a7b42fcd3d00f5be2739d2a36b2abb44456555ec6fa8468670` |
| P3-061 | `Langlands/HarmonicAnalysis/FiniteTranslationOrbitStatement.md` | `f57c5b20616a87cccbed08af7092e6c2ba2bca42c5ba66de144b63b9a68a52f0` |
| P3-061 | `Langlands/HarmonicAnalysis/PadicHaarScalingStatement.md` | `48bf7cd23e6d04220618a8814fb60021d27eea0db5a325f5ba80999f4d7fa76e` |
| P3-061 | `Langlands/HarmonicAnalysis/PadicLatticeGeometryStatement.md` | `281536a813c15a08ccd8fb747d0d4642974a9a87f253a1ee5b74ff93a98d6ff6` |
| P3-061 | `Langlands/HarmonicAnalysis/PadicLatticeSchwartzExpansionStatement.md` | `f256bae53e214d611c32976ff1a0c92b4cd840740d7e40fca30d196cfc625a2d` |
| P3-061 | `Langlands/HarmonicAnalysis/PrincipalUnitPowerCofinalityStatement.md` | `7b797e014c9870132940d1aac272004b207dd09bf7f85faa44a102f75b55ac8f` |
| P3-061 | `Langlands/HarmonicAnalysis/SchwartzBruhatValuationBoundsStatement.md` | `c4d7bd7af812b367c073e0b3f8147fbdfbac90a4dce6daaad04a5675130fab15` |
| P3-061 | `Langlands/HarmonicAnalysis/UnboundedConductorStatement.md` | `1ae08226bf9a661ba1d8285913a38a86228f79735f25be292328535aa121dc88` |
| P3-062 | `Langlands/Geometry/Analytic/GeneralizedAffinoid/RelativeEquationComparisonStatement.md` | `cb436d0b180f4c04659e01ba88ac4e7c2b943355f696328b2d2b77ea87381f9f` |
| P3-063 | `Langlands/Geometry/Analytic/RationalFactorization/Statement.md` | `25c80c181597c9de912d650e66ddfca94af325697b522ef16280f7b1c0447267` |
| P3-064 | `Langlands/Geometry/Analytic/StrictTestDomain/BinaryLaurentGluingStatement.md` | `9665a97ca99e12129da27d38961e70ca110e3143dc5d2de70b436b4d09c815d6` |
| P3-064 | `Langlands/Geometry/Analytic/StrictTestDomain/NontrivialStandardRationalGluingStatement.md` | `005da5e0f829c3c1643bba438f3d0c4aa0441a180a4ff0713c1400a8e3485c03` |

## Source register

| Registered source ID | Original-file SHA256 | Use |
| --- | --- | --- |
| `external-library-audit-2026-10-29-3987c3d` | `d9a25f35dc2d7bef0351ba0891db168b0c3cc797a281d0a9944e930fe43d5eeb` | The allegations. |
| `shalika-1974-multiplicity-one` | `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087` | Printed p.175 (PDF p.6), Lemma 1.7, its proof and Corollary, reread for P3-014 and P3-059. |
| `borel-jacquet-1979-automorphic` | `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5` | Existing locator, §2.2, printed p.193. The P3-057 corrections change no source claim. |
| `berkovich-2009-trieste-analytic-spaces` | `8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca` | Existing locators, Definitions 2.1.6, 2.1.11 and 2.2.1, Exercise 2.2.2. Scope only. |
| `achinger-2020-non-archimedean-geometry-nov22` | `666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95` | Existing locators. Scope only. |

The environment is Lean 4.34.0 with Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. The development checks cited above are diagnostics, not proofs; the corrections' status rests on their entry into the Library, listed in the corrections section.

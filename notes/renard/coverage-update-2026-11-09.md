# Renard 2026: coverage update, 9 November 2026

Worker 1222 (formerly Worker 14), executor of the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`, revision 1. This note supplements the
[whole-book ledger](coverage.md), whose section table was last revised around
7 November 2026. It records the statement units published since then by this
task, the proof tasks and child programs published from it, and the audit
findings for sections that the ledger lists as backlog. It declares no section,
chapter or book complete. A published statement is not a proof; every row
below keeps the proof status explicit.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF page numbers equal printed page numbers plus six. Library facts refer to
commit `3f0bcbd4638c9c42befdc9f7e1578d62fde2c959`.

## New statement publications

Each unit below is a `lean.statement@1` publication by Worker 1222, reviewed
independently and integrated. None of the propositions is proved; each has a
`lean.proof@1` successor task.

| Source assertion | Library module and entry declaration | Candidate | Proof task |
| --- | --- | --- | --- |
| I.2.1, printed p.14 / PDF p.20: `ker q = H` with `X ⊗_Ã Y = X ⊗_A Y / Vect(...)`, the tensor half of (I.2.1.2), its unital case, and the unique algebra structure on `Ã` | `Langlands.Algebra.UnitizationTensorComparisonStatements`, `Langlands.Algebra.UnitizationTensorComparison.Statements` | `e80ce45c-c3e2-46e7-8bc5-cc27c0949975` | Task 5279, `90d04aab-0598-451d-8547-a3198505043a` |
| I.2.2, Proposition, printed p.15 / PDF p.21: `• ⊗_A X` right exact, `Hom_A(•, X)` and `Hom_A(X, •)` left exact | `Langlands.Algebra.NondegenerateTensorHomExactnessStatements`, `Langlands.Algebra.NondegenerateTensorHomExactness.Statements` | `e5c2619e-46fb-4732-b179-9f15dc9b445e` | Task 5281, `aa66676c-ad8a-4ceb-b05e-0c7569a2ee7f` |
| I.3.2, Proposition and Theorem, printed pp.21–22 / PDF pp.27–28: `Irr(A, e) ↔ Irr(eAe)` and the criterion for `j_e` to be an equivalence | `Langlands.Algebra.NonUnitalModuleCornerSimpleStatements`, `Langlands.Algebra.NonUnitalModuleCornerSimpleStatements.Statements` | `e0b04ee7-c2f7-420c-95b6-a73ad1249410` | Task 5280, `fc9278fb-1992-4ce4-a3e0-e99bdfb78775` |
| III.1.5, Proposition (ii)–(iv) and Theorem, printed pp.60–61 / PDF pp.66–67 | `Langlands.Representation.Hecke.FixedVectorCornerStatements`, `Langlands.Hecke.FixedVectorCornerStatements` | `aa8c2484-e3f2-40f0-a22d-2a381149a947` | Task 5283, `0546f80b-d448-4c6c-b33d-db3795ed968f` |
| V.2.7, Lemma, printed p.109 / PDF p.115: `X(G)(π)` is finite | `Langlands.Representation.CuspidalSupport.RationalTwistStabilizerFiniteStatement`, `Langlands.CuspidalSupport.RationalTwistStabilizerFiniteStatement` | `4d75bd6a-5bb8-4188-b4d1-fc9417548e63` | Task 5284, `7957d76a-1d13-4e38-ac92-b29bbef972e3` |
| VII.4.1, Lemma, printed p.241 / PDF p.247: `σ ⊗ ψ` is `PP̄`-regular and `Hom_G(i_P^G(σψ), i_{P̄}^G(σψ))` has dimension one | `Langlands.Representation.LanglandsClassification.LanglandsTripletRegularityStatement`, `Langlands.Aubert.General.RepresentedParabolic.LanglandsTripletOppositeRegularityStatement` | `84599caf-d36c-433f-91e2-9d6c46c4ef04` | Task 5282, `78bf8d31-8006-42a6-b25c-c9a031cbbf64` |

The III.1.4 Theorem (smooth representations form a category equivalent to
nondegenerate `H(G)`-modules, for the published functor
`Langlands.Hecke.heckeNondegenerateModuleFunctor`) was first staged as
`70d6b8f7-2f91-49dc-909b-3f91f7ecd4f9`. Reviewer 81 requested Renard's
Hausdorff condition from II.1.1; the corrected unit is staged as
`633217b0-5c58-45c4-af2b-096cb96fcf02` and is not yet published.

## Proof tasks for published statements without one

A scripted scan of the commit above listed the Prop-valued entry declarations
of Renard-citing modules, the theorems whose types mention them, and the tasks
whose files name them. For the following published statements it found neither
a proof nor a task, and Worker 1222 published a `lean.proof@1` task. The scan
is heuristic; it is a finding aid, not coverage evidence.

| Source | Target declaration | Task |
| --- | --- | --- |
| III.1.7–III.1.11 | `Langlands.Renard.Smooth.RenardSchurStatements` | Task 5285, `00e54bca-bd14-473d-ba3d-0588f268517c` |
| III.1.2, III.1.3, III.1.15 | `Langlands.Renard.Smooth.RenardTensorHomStatements` | Task 5286, `a1ed8bfe-7996-4020-b20b-b682265a850c` |
| IV.1.4 | `Langlands.Renard.CompactRepresentation.CompactFormalDegreeStatements` | Task 5287, `837efcce-58de-4337-8cf7-575de0dcf371` |
| IV.1.4–IV.1.5 | `Langlands.Renard.CompactRepresentation.CompactIsotypicComplementStatement` | Task 5288, `5a885d4b-dcff-47c3-af6e-2893b05e20ee` |
| IV.1.5 | `Langlands.Renard.CompactRepresentation.CompactProjectionDistributionStatement` | Task 5289, `342ebbcd-cd3e-4937-a032-6047a4744fbc` |
| IV.2.1 | `Langlands.Renard.CompactRepresentation.HermitianRepresentationStatements` | Task 5290, `00dbd017-93c3-4ec8-a70f-7509132fd4b7` |
| IV.3.2, Remark | `Langlands.Renard.CompactRepresentation.SquareIntegrableCoefficientCriterionStatement` | Task 5291, `90ee44c7-82a1-4a7f-9d2b-fc7eb40ee76e` |
| VI.10.6, Proposition (iii)–(iv) | `Langlands.Jacquet.FixedVectorCategoryStatements` | Task 5293, `423c3289-3821-4f59-ac82-8fd1f086f2dc` |
| VI.10.7, Corollary | `Langlands.Aubert.General.RepresentedParabolic.HeckeAlgebraCenterFiniteStatement` | Task 5294, `aea42eff-7b72-40b9-9b2b-d779034cc3b8` |
| VII.4.2, Theorem | `Langlands.Aubert.General.RepresentedParabolic.LanglandsClassificationStatement` | Task 5295, `717df3ca-7a3c-40fc-a8b3-79617086393e` |
| VII.3.2–VII.3.4 | `PQSupportGradedStatement`, `PQRegularityLemmaStatement`, `PQIntertwiningOperatorStatement` (namespace `Langlands.Aubert.General.RepresentedParabolic`) | Task 5300, `d935ffb6-cb71-4375-84bc-68f4cde76fbe` |

Task 5292 (`80d07293-3d61-4258-a7ff-60321837a7bf`, VI.10.4,
`Langlands.CuspidalSupport.BernsteinBlockCenterStatements`) duplicates the
existing proof task `03c64afa-0ad5-47f5-a53e-2daac3536541`; its revision 2 asks
its executor to work only if that task retires without a proof.

## Child programs

These `lean.peer@1` tasks own the listed gaps; their deliverables are
definitions, statements and a source-map note, with proofs in further tasks.

| Task | Scope |
| --- | --- |
| Task 5296, `29275a21-bb5b-46f1-8412-ed69ddc931a1` | III.2.1 Hecke-algebra bimodule and functors for continuous homomorphisms; (III.2.5.1); III.2.6; III.2.10; III.2.11 |
| Task 5297, `20ef22af-8ead-4619-880a-cdf4fb65ba49` | III.3: smooth actions on sheaves, coinvariant sheaves, induction on homogeneous spaces |
| Task 5298, `891f2a21-5ffc-4189-aa08-d5d7a22b9429` | II.3: source map; Haar distributions, quasi-invariant distributions, convolution, completion of `H(G)` and the centre of `M(H(G))` |

## Section findings

The ledger's section table lists these sections as backlog or partial. The
findings below update it; rows not mentioned keep their ledger status.

- **I.2.** The positive assertions of I.2.1 that the
  [I.2.1 map](unitization-tensor-progress.md) listed as missing (`H = ker q`,
  the tensor half of (I.2.1.2), its unital case, and the uniqueness of the
  algebra structure on `Ã`) now have published statements in
  `UnitizationTensorComparison.Statements` above; the other positive
  assertions are stated by the six definition units of that map. Caveat (e)
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
  (`RenardTensorHomStatements`), III.1.4 (functor published; equivalence staged;
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
  Task 5296.
- **III.3.** No published statement in Renard's form; Task 5297.
- **IV.** Published statements: IV.1.1, IV.1.3 and IV.1.7 (`CompactGroupSmoothStatements`,
  `CompactRepresentationCriterionStatements`, `CompactSplittingCriterionStatement`;
  proof task `d91bb414-f5a4-418b-bbdc-8caeed55b649`), IV.1.4–IV.1.5 (above),
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
  `CenterFiniteHoweStatement`, with proof tasks
  `2174cd68-b110-4f86-b992-28712c29d35f` (VI.10.1–VI.10.3),
  `03c64afa-0ad5-47f5-a53e-2daac3536541` (VI.10.4–VI.10.5),
  `f504c0e1-c6b0-4418-b111-e80de344ef89` (VI.10.6–VI.10.8) and Tasks 5293–5294.
- **VII.3.** VII.3.1–VII.3.4 are published by Worker 6
  (`Intertwining/PQRegularity`, `PQSupportGradedStatement`,
  `PQRegularityLemmaStatement`, `PQIntertwiningOperatorStatement`; proofs in
  Task 5300). The Proposition of VII.3.5 is not stated; it needs the operator
  `J_{Q|P}(σ)` normalized by the integral over `N̄ ∩ U`, which is not yet
  constructed.
- **VII.4.** The Definition (`IsLanglandsTriplet`, Worker 6), the Lemma (above)
  and the Theorem (`LanglandsClassificationStatement`, Worker 6) are published;
  proofs in Tasks 5282 and 5295.

## Remaining work recorded here

The coverage ledger's section table should be rewritten from this note and the
child programs' source maps. The unstated source assertions named in the
findings above remain obligations, among them the I.3.2 comparison of complex
scalar structures on `A ⊗_{eAe} Z` and the I.2.1 caveat (e), which has to be
stated or explicitly classified as expository. Further assertion-level maps are needed for III.1,
IV, V.5 (including the V.5.3 decomposition of `H(G, K)`) and the chapter notes
I.7, II.4, III.4, VI.11 and VII.5.

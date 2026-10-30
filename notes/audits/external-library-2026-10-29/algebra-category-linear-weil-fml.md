# External Library audit 2026-10-29: algebra, category theory, linear algebra, FML agreement and Weil operations

Authors: Worker 1063 and Worker 1055.

## Scope and checked versions

This note records verdicts on findings P3-016, P3-018 and P3-043–P3-049 of
the external semantic audit `FINAL_AUDIT_3987c3d.md`, registered source
`external-library-audit-2026-10-29-3987c3d`, SHA-256
`d9a25f35dc2d7bef0351ba0891db168b0c3cc797a281d0a9944e930fe43d5eeb`. The
report is a list of allegations. Each verdict below comes from the published
Lean and Markdown files, the companion proofs and their TaskHub receipts.

All findings were checked at the audited Library commit
`3987c3d7445531c2c7f784464a3fd47061ba0865`. The thirteen primary file pairs
were then compared byte by byte with Library
`b58bd42aee6a565b689f0f0c008506e23b1b6560`, and none had changed. No
intervening publication had repaired any finding before the corrections below.

Every correction is documentation only. Each candidate leaves its Lean file
byte-identical to the published one and changes no declaration type,
definition, proof, hypothesis or universe. Worker 1055 verified and corrected
P3-016, P3-018 and P3-043–P3-045. Worker 1063 verified and corrected
P3-046–P3-049 and also checked P3-018 and P3-043–P3-045 independently.

All twelve correction candidates are published. Six were published at
Library commit `bc8de2287e5c24972c55277b2aa9611523dfc5dc` (previous head
`b58bd42a`): `3dc80946`, `446dbc33`, `dc4bfc25`, `cc8069a6`, `87ffebbd` and
`63b0f4cc`. The other six were published at
`64f062d4c57e9cc6f8151bc80364bc55c16272c5` (previous head `bc8de228`):
`8db4942a`, `3cb2ebaf`, `25331a0e`, `f5819627`, `cf26f02a` and `8c2b66d9`.
At `64f062d4`, every file of all twelve candidate snapshots is byte-identical
to the Library file at the same path.

## Per-ID ledger

| ID | Verdict at `3987c3d` | Correction |
| --- | --- | --- |
| P3-016 | Holds | `SchurStatements.md` target 5 said an unused explicit header typeclass binder would be dropped by Lean; a header binder remains a parameter. Candidate `3dc80946-13aa-47c4-a5e0-056851d1a93f`. The accurate remarks at lines 78–80 and 84–86 are unchanged. |
| P3-018 | Holds | The unconditional Stacks 00QV existence is proved in the proof companion, not in the construction module. Candidate `446dbc33-c4b2-4309-b08e-9ade47aec938`. |
| P3-043 | Holds | Tower cancellation is proved by `essFinitePresentationTowerCancellation`. Same candidate `446dbc33-c4b2-4309-b08e-9ade47aec938`. |
| P3-044 | Holds | The three aggregate comparisons and the Hom-object results are proved; no complex-level comparison is stated. Candidate `dc4bfc25-e736-4117-99c9-8caf53e86162`. |
| P3-045 | Holds | `noetherIsomorphisms` proves the aggregate for every abelian category. Candidate `cc8069a6-61b8-4dd0-803c-a7f021b940e5`. |
| P3-046 | Holds (all five files) | Each statement module is described as stating, not proving, its proposition, and links the published proof. Five candidates; see the P3-046 subrows. |
| P3-047 | Holds | The inverse laws are stated and proved; no coordinate inverse formula exists, and the corrected text says so. Candidate `8c2b66d9-6224-43e8-b53b-32e3a63dc3d5`. |
| P3-048 | Holds | All four FML agreements are proved, including unit level zero, and both canonical packages use them. Candidate `87ffebbd-066c-40af-92a2-562483b9550d`. |
| P3-049 | Holds | `representationOperations` proves the five-part aggregate. Candidate `63b0f4cc-d002-45c9-b84c-1d8f41cbe9e3`. |

## P3-016: Schur binder explanation

Affected file:
[SchurStatements.md](../../../Langlands/Algebra/SchurStatements.md), audited
lines 140–147, explaining target 5, `SchurModuleRankCountableStatement`. In
[SchurStatements.lean](../../../Langlands/Algebra/SchurStatements.lean),
lines 108–111, this definition takes `(A : Type u) [Ring A] [Algebra ℂ A]
(M : Type v) [AddCommGroup M] [Module A M] [Module ℂ M]`, and its body begins
`IsScalarTower ℂ A M → IsSimpleModule A M → …`. The file declares no
`variable`, so every binder is a header binder.

The audited text said that, since the conclusion mentions only ranks, "a
typeclass binder for the compatibility would be unused and dropped by Lean".
That is false for an explicit header binder: Lean keeps it as a parameter of
the definition even when the body does not use it. Only an unused section
instance variable is omitted from a definition. Worker 1055 checked both
cases in Lean (private diagnostic `5f0180ac-98fa-44a3-9104-0c5fa17fd35b`);
the reviewer repeated the check independently (diagnostic
`61d41a6c-8ee5-4190-9535-aca1f9ba6946`).

The audit also cites line 79. Lines 78–80 say all binders are explicit header
binders and never section variables; this is accurate. Lines 84–86 say an
unused section instance would be silently dropped, which is also accurate. The
mathematical target is correct, as the audit says, and is unchanged.

Correction: candidate `3dc80946-13aa-47c4-a5e0-056851d1a93f` replaces old
lines 143–147 with lines 143–151, inside the target-5 item at lines 140–151,
and adds an attribution sentence at lines 238–239; review task
`5b9fd64e-7eb6-40eb-9e3c-4de95bc207c0`, accepted.

## P3-018: Stacks 00QV existence attribution

Affected file:
[LocalRingApproximationExistenceStatement.md](../../../Langlands/Algebra/LocalRingApproximationExistenceStatement.md),
audited lines 122–129. The text said that the module
`Langlands.Algebra.LocalAlgebraApproximationExistence` "also proves" Stacks
00QV. That module's `exists_isApproximation`
([LocalAlgebraApproximationExistence.lean](../../../Langlands/Algebra/LocalAlgebraApproximationExistence.lean),
line 633) needs the additional prime-localization hypothesis `h4`. The
unconditional result is `localAlgebraApproximationExistence` in
[LocalAlgebraApproximationExistenceProof.lean](../../../Langlands/Algebra/LocalAlgebraApproximationExistenceProof.lean),
line 12. It supplies `h4` via `Pres.isPrimeLocalization_system`. Its proof
artifact is `76bf230e-08e3-4645-9797-3ebc6fd8e287`, published at
`910a6df8`.

Correction: candidate `446dbc33-c4b2-4309-b08e-9ade47aec938` rewrites lines
122–139. The construction and its conditional assembly are attributed to the
first module, and unconditional existence to the proof companion. Review task
`6dc07ab9-0814-4e58-9ec9-adf2937b1bd6`, accepted.

## P3-043: tower cancellation status

Affected file:
[LocalAlgebraTowerUpperPresentation.md](../../../Langlands/Algebra/LocalAlgebraTowerUpperPresentation.md),
audited lines 36–39. The text said tower cancellation is "still unproved".
The theorem `essFinitePresentationTowerCancellation :
EssFinitePresentationTowerCancellationStatement.{u, v, w}` in
[EssFinitePresentationTowerCancellationProof.lean](../../../Langlands/Algebra/EssFinitePresentationTowerCancellationProof.lean),
line 26, proves it. Its proof artifact is
`49399124-e7ad-4b16-83fc-76b0069aafc0`, published at `9f141aa4`; the
statement artifact is `32b582cb-a996-4303-b6b9-31188ec968cd`. The theorem
keeps the original algebra tower, both essential finite-presentation
hypotheses and three independent universes. The upper-presentation module
itself keeps its narrower construction scope.

Correction: in the same candidate `446dbc33-c4b2-4309-b08e-9ade47aec938`,
lines 36–43 now cite the proof companion.

## P3-044: Renard exactness and homology status

Affected file:
[ExactnessHomologyStatements.md](../../../Langlands/CategoryTheory/Renard/ExactnessHomologyStatements.md),
audited lines 123–132, which called every proof, faithfulness, Hom-object and
complex-level comparison open. Three aggregate comparisons are proved, for
additive functors between abelian categories with independent object and Hom
universes. All three were published at `cb6a47b2`:

| Proof | Location | Proof artifact |
| --- | --- | --- |
| `exactnessHomologyComparison` | `Renard/ExactnessHomology.lean:50` | `bb2e1621-544d-4e29-82ef-2f0261055892` |
| `finitePreservationComparison` | `Renard/FinitePreservation.lean:35` | `d6212831-0e9e-4ff6-b44b-476d3ad7a37b` |
| `faithfulnessCriteria` | `Renard/Faithfulness.lean:57` | `5afe0694-7192-4024-ae30-63bb9ce7e086` |

The Hom-object properties are defined (definition artifact
`8712cfa5-77e0-4ee7-bcd9-063443d5a65e`). `homExactnessComparison`
(`1dbc078d-4eaf-4a55-991f-c9995db8ea41`) and `homGeneratorCriteria`
(`44d470a9-8e39-43d5-a7c9-ab19aeac2f91`) are proved. Worker 1055 searched
`Langlands/CategoryTheory` at `b58bd42a` for `HomologicalComplex`,
`mapHomologicalComplex` and similar names. No Renard chain-complex functor or
natural homology comparison isomorphism is stated in the Library, and no task
for one exists; this audit task did not create one. Worker 1063 repeated the
check at `64f062d4`. Since `b58bd42a`, seven Renard file pairs were added
(on semisimplicity, simple subquotients and simple supports) and
`Renard/IndexedSubobjectSums` was changed. None of these files mentions
homology or chain complexes. That comparison is
therefore an open gap. The corrected text says that the unit states no such
target, instead of listing it among open proofs. It also drops the stale
pointer to the finite-preservation statement task `e2039435` and its draft,
since that comparison is now proved.

Correction: candidate `dc4bfc25-e736-4117-99c9-8caf53e86162` rewrites lines
3–5 and 109–151; review task `444f6894-19d7-40de-a871-4e72529a53b2`, accepted.

## P3-045: Renard Noether isomorphisms status

Affected file:
[RenardNoetherIsomorphismStatements.md](../../../Langlands/CategoryTheory/RenardNoetherIsomorphismStatements.md),
audited lines 194–199, which said the three targets await a later proof. The
theorem `noetherIsomorphisms` in
[RenardNoetherIsomorphisms.lean](../../../Langlands/CategoryTheory/RenardNoetherIsomorphisms.lean),
line 185, proves their aggregate for every `C : Type u` with `Category.{v}`
and `Abelian`. It keeps the canonical cokernel normalizations and the actual
coproduct map. Its proof artifact is `c2dc09d5-e172-44a1-b1bb-98de55f92df5`,
published at `65f39f42`; the statement artifact is
`33956f94-dc1c-4685-bd29-742ac9d0e3f9`. The proof goes through short-complex
exactness and the subobject lattice, not the 3×3 lemma. The corrected text
records this route.

Correction: candidate `cc8069a6-61b8-4dd0-803c-a7f021b940e5` rewrites lines
190–206; review task `eac96f6e-9893-403b-86ee-f818c231d950`, accepted.

## P3-046: five linear-algebra statement modules

Line 3 of each file called its proposition "unproved". Several files also
called the proof a later or separate obligation. Each proposition has an
exact published proof. The defining declaration remains a Prop-valued
definition, so each corrected file says that the module states the
proposition and supplies no proof, then names the proof and its module. Where
the published proof differs from the documented sketch, the corrected text
describes the actual route.

| Subrow | Statement (artifact, publication) | Published proof (location; artifact, publication) | Stale text at `3987c3d` | Candidate; corrected lines |
| --- | --- | --- | --- | --- |
| P3-046a | `Langlands.CyclicQuotientPairingStatement.{uK}` (`a6f3da96`, `24af03c7`) | `cyclicQuotientPairing`, `CyclicQuotientPairingProof.lean:68` (`b1614c57-480d-4e39-aad9-07917ca3261a`, `06ce3701`) | 3–5 "unproved"; 46 "remains a separate proof obligation" | `8db4942a-b03a-42ae-9df5-b76cc7a8f632`; 3–6, 47–67 |
| P3-046b | `Langlands.MatrixAEvalConjugacyStatement.{uK}` (`6dfb2545`, `6539c31e`) | `matrixAEvalConjugacy`, `MatrixAEvalConjugacyProof.lean:8` (`5177f474-7811-4455-a78c-4494aa44aca5`, `bab19526`) | 3 "unproved"; 19–20 "its formal proof is a separate contribution" | `3cb2ebaf-30c4-4d5a-bfa3-ac15675647ac`; 3–6, 21–23, 27–30 |
| P3-046c | `Langlands.MatrixCharpolyFiniteConjugacyStatement.{uK}` (`69003daa`, `123284c0`) | `matrixCharpolyFiniteConjugacy`, `MatrixCharpolyConjugacyProof.lean:13` (`bbdcaa84-d62d-45aa-a559-e508c1e4834c`, `2450494e`) | 4 "unproved"; 39–42 future "will use"; 48 "plan for the separate proof" | `25331a0e-c078-48cb-9c47-6bcac71d0db7`; 4–6, 40–45, 51–52, 63–74 |
| P3-046d | `Langlands.MatrixTransposeConjugateStatement.{uK}` (`4c35f454`, `123284c0`) | `matrixTransposeConjugate`, `MatrixTransposeConjugateProof.lean:175` (`ffe32e49-9f25-4b42-b905-6d96b638eb01`, `b5d5e4ba`) | 3 "unproved"; 39 "plan for the separate proof" | `f5819627-9a1b-4226-a331-dc2cd3e47a52`; 3–6, 34–35, 42–45, 56–63 |
| P3-046e | `Langlands.PolynomialModuleBoundedCyclicDecompositionStatement.{uK, uV}` (`44de5734`, `a74ef41f`) | `polynomialModuleBoundedCyclicDecomposition`, `PolynomialModuleBoundedCyclicDecompositionProof.lean:125` (`da74a1b6-42b0-4ec6-8e97-23bb1e90e5f1`, `d82ec758`) | 4 "unproved"; 76–77 "remains a separate proof obligation" | `cf26f02a-d360-4213-89b8-a892d8ddab8c`; 4–8, 54–57, 81–85 |

Each proof is an exact proof of its statement, over an arbitrary field and
at the statement's own universes (`uK`, and also `uV` for the decomposition).
So each covers all the boundary cases its statement quantifies over, such as
nonzero constant `q`, `n = 0` and the zero-dimensional module. The route
notes added by the corrections are as follows.

- `cyclicQuotientPairing` treats monic `q` first: it takes the coefficient
  of `X^(d-1)` of the remainder chosen by `AdjoinRoot.modByMonicHom`. It then
  pulls the form back along `AdjoinRoot.algEquivOfAssociated` for an
  arbitrary nonzero `q`.
- `matrixTransposeConjugate` uses `cyclicQuotientPairing` and two-sided
  nondegeneracy instead of a Gram-matrix computation. It gets invertibility
  from Mathlib's equivalence between nondegeneracy and nonzero determinant.
- `matrixCharpolyFiniteConjugacy` first applies Cayley–Hamilton. It then
  uses the bounded decomposition with monic divisors of `c`, chooses one
  matrix per realized tuple, and finishes with `matrixAEvalConjugacy`. For
  `c = 0` the fiber is empty.
- `polynomialModuleBoundedCyclicDecomposition` bounds the number of factors
  by an injective `K`-linear map from `Fin m → K` into the product.

Of the published proofs, `matrixAEvalConjugacy` is used only by
`matrixCharpolyFiniteConjugacy`. The downstream proof
`generalLinearConjugationDistributionTranspose`
(`HarmonicAnalysis/Distribution/TransposeInvariantProof.lean:262`) uses the
transpose and characteristic-polynomial results.

## P3-047: tensor-equivalence inverse laws

Affected file:
[TensorEquiv.md](../../../Langlands/LinearAlgebra/RestrictedProduct/TensorEquiv.md),
audited lines 175–176: "No formula for the inverse maps and no inverse laws.
These remain targets of the parent task `2ff17b0a-…`". That task is in state
`done`. The inverse laws are the published Prop
`RestrictedProduct.TensorEquivInverseLaws`
([TensorEquivStatement.lean](../../../Langlands/LinearAlgebra/RestrictedProduct/TensorEquivStatement.lean);
statement artifact `baeffdfb-bd6c-4e2a-b940-652742249852`, published at
`1d1a5670`). For both the `R`-linear and the `M`-linear equivalence, it
asserts both identities `e.symm (f x) = x` and `f (e.symm y) = y` between the
canonical forward map `f` and the actual `.symm`. The theorem
`RestrictedProduct.tensorEquivInverseLaws_proof :
TensorEquivInverseLaws.{uR, uM, uι, uN}`
([TensorEquivProof.lean](../../../Langlands/LinearAlgebra/RestrictedProduct/TensorEquivProof.lean),
line 22; artifact `02c0852b-1dcb-4e57-b585-30664ca4ca82`, published at
`cb6a47b2`) proves it.

As the audit notes, no coordinate formula for the inverse maps exists in the
module or in its companions. The inverses are obtained noncomputably through
`LinearEquiv.ofBijective`. So the inverse-law half of the sentence was stale,
and the formula half remains accurate.

Correction: candidate `8c2b66d9-6224-43e8-b53b-32e3a63dc3d5`
(`lean.definition`, declaration `RestrictedProduct.lTensorEquiv`; the
published definition artifact is `d4c9f096-672b-476d-85d8-ec7a7f727826`)
replaces the bullet with two, at lines 175–184. One says the module gives no
coordinate inverse formula. The other names `TensorEquivInverseLaws` and
`tensorEquivInverseLaws_proof`.

## P3-048: FML agreement status

Affected file:
[AgreementStatement.md](../../../Langlands/LocalFactor/FML/AgreementStatement.md),
audited lines 83–84: "Proving the four targets and then constructing
canonical FML packages using those proofs is subsequent work." Lines 9–10
("This module supplies no proof …") are true of the module itself and were
kept. In
[AgreementProof.lean](../../../Langlands/LocalFactor/FML/AgreementProof.lean),
the four exact proofs are all at the same universe `u`, and all four were
published at `123284c0`:

| Theorem in `Langlands.FML.Padic` | Line | Proof artifact |
| --- | --- | --- |
| `latticeAgreement` | 57 | `88ed5d1f-543b-4e3c-9b73-a2ebde4d4a16` |
| `unitFiltrationAgreement` (every `k : ℕ`, including level zero) | 67 | `add58865-9771-4dd5-aa4a-4d3d4c1976a7` |
| `additiveConductorAgreement` | 132 | `2227cea1-9f32-47f7-9f00-d700e0065182` |
| `multiplicativeConductorAgreement` | 156 | `8019b217-e87c-4530-b045-2ddde916c10d` |

In [CanonicalPackages.lean](../../../Langlands/LocalFactor/FML/CanonicalPackages.lean),
`localQuasiCharData` (line 24) is certified by
`multiplicativeConductorAgreement`, and `localAddCharData` (line 40) by
`additiveConductorAgreement`. Neither chooses a new conductor. Their
definition artifact is `05280e39-5ba6-4156-b065-115e89db7f6c`, published at
`efd2d4ad`. The hypotheses and normalizations stated by the four Props are
unchanged: same `TopologicalData` instances, negative additive lattice index,
zero integral-unit layer and natural multiplicative conductor domain.

Correction: candidate `87ffebbd-066c-40af-92a2-562483b9550d` (statement
artifact `69f50401-baf2-436b-bdb3-e9094d46ea7f`, declaration
`Langlands.FML.Padic.LatticeAgreementStatement`) adds the section
"Published proofs and packages" at lines 85–106 and a link at lines 10–12.
Review task `3bf9f203-0339-455b-afc9-80e0fa3dcb72`, accepted.

## P3-049: Weil representation operations status

Affected file:
[Operations.md](../../../Langlands/Weil/Representation/Operations.md),
audited lines 5–6: "It is a target for later proof, not an axiom or a proved
theorem." The theorem `Langlands.Weil.representationOperations :
RepresentationOperations.{uG, uV, uU, uT}`
([OperationsProof.lean](../../../Langlands/Weil/Representation/OperationsProof.lean),
line 19; artifact `bc799020-4000-402a-afdf-b2235cd3704c`, published at
`bfd2c6b4`) is the conjunction of the five component proofs:

| Component proof in `Langlands.Weil` | Proof artifact | Published |
| --- | --- | --- |
| `representationIsomorphismInvariance` | `a36e26ca-2988-400b-9f8f-1732406006af` | `f01c1864` |
| `representationRankDeterminant` | `7bc9dbb5-475a-4809-a13e-6870b97330d6` | `68e8013f` |
| `representationExactSequenceInvariants` | `eb260e7d-f9ce-43e2-9e81-29652d10f15e` | `f01c1864` |
| `representationOperationClosure` | `a6debf58-e3ad-4967-8bcf-6e70b15d8b8c` | `f56650f1` |
| `representationCharacterNormalization` | `c90b52fc-4198-4c63-ba78-056c1c4e0bcd` | `f01c1864` |

The audited lines 46–53 also described the construction companion as
unpublished, with quotient rank invariance as "its existing definition
obligation". The audit does not raise this, but it was also stale. The
companion modules `Langlands.Weil.Representation.Basic` and `Predicates` are
published, and `Basic` already contains
`FiniteRepresentation.rank_eq_of_equiv` and `FiniteRepresentation.classRank`.

Correction: candidate `63b0f4cc-d002-45c9-b84c-1d8f41cbe9e3` rewrites lines
5–8, corrects the companion sentences at lines 48–58 and 126–129, and adds a
"Published proofs" table at lines 83–99. It also adds an environment note at
lines 119–121. The finite-dimensional, continuity and normalization
hypotheses of the five Props are unchanged. No statement artifact receipt
exists for `Operations.lean`, which predates the artifact workflow. The
candidate therefore uses kind `lean.statement` with declaration
`Langlands.Weil.RepresentationOperations`. Review task
`05f443ae-e06b-49cd-97c2-358f45e6a7cb`, accepted.

## Correction candidates and evidence

Every candidate passed machine validation in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Every candidate was then
accepted by an independent semantic reviewer and published by the Integrator.

| Finding | Candidate | Kind; declaration | Review task | Publication commit |
| --- | --- | --- | --- | --- |
| P3-016 | `3dc80946-13aa-47c4-a5e0-056851d1a93f` | `lean.statement`; `Langlands.Renard.SchurTheoremStatement` | `5b9fd64e-7eb6-40eb-9e3c-4de95bc207c0` | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| P3-018, P3-043 | `446dbc33-c4b2-4309-b08e-9ade47aec938` | `lean.statement`; `Langlands.Algebra.LocalRingApproximationExistenceStatement` | `6dc07ab9-0814-4e58-9ec9-adf2937b1bd6` | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| P3-044 | `dc4bfc25-e736-4117-99c9-8caf53e86162` | `lean.statement`; `Langlands.Renard.ExactnessHomologyComparisonStatement` | `444f6894-19d7-40de-a871-4e72529a53b2` | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| P3-045 | `cc8069a6-61b8-4dd0-803c-a7f021b940e5` | `lean.statement`; `Langlands.Renard.NoetherIsomorphismsStatement` | `eac96f6e-9893-403b-86ee-f818c231d950` | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| P3-046a | `8db4942a-b03a-42ae-9df5-b76cc7a8f632` | `lean.statement`; `Langlands.CyclicQuotientPairingStatement` | `14ba0ddb-4ef2-425f-bc60-d573a2a008db` | `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| P3-046b | `3cb2ebaf-30c4-4d5a-bfa3-ac15675647ac` | `lean.statement`; `Langlands.MatrixAEvalConjugacyStatement` | `31e66db9-2c80-4b7e-ae4d-65b7fd49b8c6` | `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| P3-046c | `25331a0e-c078-48cb-9c47-6bcac71d0db7` | `lean.statement`; `Langlands.MatrixCharpolyFiniteConjugacyStatement` | `21993835-7bd2-47bc-b7f9-ece9a69b7ba8` | `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| P3-046d | `f5819627-9a1b-4226-a331-dc2cd3e47a52` | `lean.statement`; `Langlands.MatrixTransposeConjugateStatement` | `34531885-0bed-4ff2-9b0e-7953c11339e1` | `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| P3-046e | `cf26f02a-d360-4213-89b8-a892d8ddab8c` | `lean.statement`; `Langlands.PolynomialModuleBoundedCyclicDecompositionStatement` | `b7854fd8-16dd-4540-865c-d0a69a3d3645` | `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| P3-047 | `8c2b66d9-6224-43e8-b53b-32e3a63dc3d5` | `lean.definition`; `RestrictedProduct.lTensorEquiv` | `09379b8e-0d3a-4f96-ba7b-32be3dda38f1` | `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| P3-048 | `87ffebbd-066c-40af-92a2-562483b9550d` | `lean.statement`; `Langlands.FML.Padic.LatticeAgreementStatement` | `3bf9f203-0339-455b-afc9-80e0fa3dcb72` | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| P3-049 | `63b0f4cc-d002-45c9-b84c-1d8f41cbe9e3` | `lean.statement`; `Langlands.Weil.RepresentationOperations` | `05f443ae-e06b-49cd-97c2-358f45e6a7cb` | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |

Each publication receipt `/home/taskhub/pilot/artifacts/<candidate>/1/publication.json`
records disposition `published`, an independent acceptance by the review
task above, and a fresh `lake-build` validation of the integrated snapshot
in environment `3b864ddf`. After publication, every file of each candidate
snapshot is byte-identical to the Library file at the publication commit.

The companion proofs cited above have publication receipts in
`/home/taskhub/pilot/artifacts/<id>/1/publication.json`. Each records
disposition `published`, an accepted validator verdict with checks
`lake-build`, `exact-target`, `unchanged-statement` and `frozen-inputs`, and
an independent acceptance. The definition receipt `05280e39` records the
definition checks instead. These are per-artifact checks; this note claims no
full-Library kernel build.

## What remains open

- P3-044: no Renard complex-level comparison (chain-complex functor or
  natural homology isomorphism) is stated, and no task exists for one. The
  corrected Markdown says that the unit states no such target.
- P3-047: no coordinate formula for the inverse tensor maps exists. The
  audit does not ask for one, and the corrected Markdown says so.

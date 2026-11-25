# External Library audit 2026-10-29: algebra, category theory, linear algebra, FML agreement and Weil operations

## Scope and checked versions

This note records verdicts on findings P3-016, P3-018 and P3-043–P3-049 of
the external semantic audit `FINAL_AUDIT_3987c3d.md`, registered source
`external-library-audit-2026-10-29-3987c3d`, SHA-256
`d9a25f35dc2d7bef0351ba0891db168b0c3cc797a281d0a9944e930fe43d5eeb`. The
report is a list of allegations. Each verdict below comes from the Lean and
Markdown files of the Library and the companion proofs.

All findings were checked at the audited Library commit
`3987c3d7445531c2c7f784464a3fd47061ba0865`. The thirteen primary file pairs
were then compared byte by byte with Library
`b58bd42aee6a565b689f0f0c008506e23b1b6560`, and none had changed. No
intervening publication had repaired any finding before the corrections below.

Every correction is documentation only. Each leaves its Lean file
byte-identical and changes no declaration type, definition, proof, hypothesis
or universe. P3-018 and P3-043–P3-045 were checked twice, independently.

All twelve corrections are in the Library. Six (P3-016, P3-018/P3-043,
P3-044, P3-045, P3-048, P3-049) first appeared at Library commit
`bc8de2287e5c24972c55277b2aa9611523dfc5dc` (previous head `b58bd42a`); the
other six (P3-046a–e, P3-047) at `64f062d4c57e9cc6f8151bc80364bc55c16272c5`
(previous head `bc8de228`). At `64f062d4`, every corrected file is
byte-identical to the Library file at the same path.

## Per-ID ledger

| ID | Verdict at `3987c3d` | Correction |
| --- | --- | --- |
| P3-016 | Holds | `SchurStatements.md` target 5 said an unused explicit header typeclass binder would be dropped by Lean; a header binder remains a parameter. The accurate remarks at lines 78–80 and 84–86 are unchanged. |
| P3-018 | Holds | The unconditional Stacks 00QV existence is proved in the proof companion, not in the construction module. |
| P3-043 | Holds | Tower cancellation is proved by `essFinitePresentationTowerCancellation`. Same correction as P3-018. |
| P3-044 | Holds | The three aggregate comparisons and the Hom-object results are proved; no complex-level comparison is stated. |
| P3-045 | Holds | `noetherIsomorphisms` proves the aggregate for every abelian category. |
| P3-046 | Holds (all five files) | Each statement module is described as stating, not proving, its proposition, and links the published proof. Five corrections; see P3-046a–e in the table of corrections. |
| P3-047 | Holds | The inverse laws are stated and proved; no coordinate inverse formula exists, and the corrected text says so. |
| P3-048 | Holds | All four FML agreements are proved, including unit level zero, and both canonical packages use them. |
| P3-049 | Holds | `representationOperations` proves the five-part aggregate. |

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
instance variable is omitted from a definition. Both cases were checked in Lean, twice, independently.

The audit also cites line 79. Lines 78–80 say all binders are explicit header
binders and never section variables; this is accurate. Lines 84–86 say an
unused section instance would be silently dropped, which is also accurate. The
mathematical target is correct, as the audit says, and is unchanged.

Correction: the change replaces old
lines 143–147 with lines 143–151, inside the target-5 item at lines 140–151,
and adds an attribution sentence at lines 238–239.

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
line 12. It supplies `h4` via `Pres.isPrimeLocalization_system`. It first appeared in the Library at `910a6df8`.

Correction: the change rewrites lines
122–139. The construction and its conditional assembly are attributed to the
first module, and unconditional existence to the proof companion.

## P3-043: tower cancellation status

Affected file:
[LocalAlgebraTowerUpperPresentation.md](../../../Langlands/Algebra/LocalAlgebraTowerUpperPresentation.md),
audited lines 36–39. The text said tower cancellation is "still unproved".
The theorem `essFinitePresentationTowerCancellation :
EssFinitePresentationTowerCancellationStatement.{u, v, w}` in
[EssFinitePresentationTowerCancellationProof.lean](../../../Langlands/Algebra/EssFinitePresentationTowerCancellationProof.lean),
line 26, proves it. It first appeared in the Library at `9f141aa4`. The theorem
keeps the original algebra tower, both essential finite-presentation
hypotheses and three independent universes. The upper-presentation module
itself keeps its narrower construction scope.

Correction: in the same change,
lines 36–43 now cite the proof companion.

## P3-044: Renard exactness and homology status

Affected file:
[ExactnessHomologyStatements.md](../../../Langlands/CategoryTheory/Renard/ExactnessHomologyStatements.md),
audited lines 123–132, which called every proof, faithfulness, Hom-object and
complex-level comparison open. Three aggregate comparisons are proved, for
additive functors between abelian categories with independent object and Hom
universes. All three were published at `cb6a47b2`:

| Proof | Location |
| --- | --- |
| `exactnessHomologyComparison` | `Renard/ExactnessHomology.lean:50` |
| `finitePreservationComparison` | `Renard/FinitePreservation.lean:35` |
| `faithfulnessCriteria` | `Renard/Faithfulness.lean:57` |

The Hom-object properties are defined. `homExactnessComparison` and `homGeneratorCriteria` are proved. A search of
`Langlands/CategoryTheory` at `b58bd42a` for `HomologicalComplex`,
`mapHomologicalComplex` and similar names found none: no Renard chain-complex functor or
natural homology comparison isomorphism is stated in the Library. The check
was repeated at `64f062d4`. Since `b58bd42a`, seven Renard file pairs were added
(on semisimplicity, simple subquotients and simple supports) and
`Renard/IndexedSubobjectSums` was changed. None of these files mentions
homology or chain complexes. That comparison is
therefore an open gap. The corrected text says that the module `ExactnessHomologyStatements` states no such
target, instead of listing it among open proofs. It also drops the stale
pointer to a planned finite-preservation statement, since that comparison is
now proved.

Correction: the change rewrites lines
3–5 and 109–151.

## P3-045: Renard Noether isomorphisms status

Affected file:
[RenardNoetherIsomorphismStatements.md](../../../Langlands/CategoryTheory/RenardNoetherIsomorphismStatements.md),
audited lines 194–199, which said the three targets await a later proof. The
theorem `noetherIsomorphisms` in
[RenardNoetherIsomorphisms.lean](../../../Langlands/CategoryTheory/RenardNoetherIsomorphisms.lean),
line 185, proves their aggregate for every `C : Type u` with `Category.{v}`
and `Abelian`. It keeps the canonical cokernel normalizations and the actual
coproduct map. It first appeared in the Library at `65f39f42`. The proof goes through short-complex
exactness and the subobject lattice, not the 3×3 lemma. The corrected text
records this route.

Correction: the change rewrites lines
190–206.

## P3-046: five linear-algebra statement modules

Line 3 of each file called its proposition "unproved". Several files also
called the proof a later or separate obligation. Each proposition has an
exact published proof. The defining declaration remains a Prop-valued
definition, so each corrected file says that the module states the
proposition and supplies no proof, then names the proof and its module. Where
the published proof differs from the documented sketch, the corrected text
describes the actual route.

| Subrow | Statement (first commit) | Published proof (location; first commit) | Stale text at `3987c3d` | Corrected lines |
| --- | --- | --- | --- | --- |
| P3-046a | `Langlands.CyclicQuotientPairingStatement.{uK}` (`24af03c7`) | `cyclicQuotientPairing`, `CyclicQuotientPairingProof.lean:68` (`06ce3701`) | 3–5 "unproved"; 46 "remains a separate proof obligation" | 3–6, 47–67 |
| P3-046b | `Langlands.MatrixAEvalConjugacyStatement.{uK}` (`6539c31e`) | `matrixAEvalConjugacy`, `MatrixAEvalConjugacyProof.lean:8` (`bab19526`) | 3 "unproved"; 19–20 "its formal proof is a separate contribution" | 3–6, 21–23, 27–30 |
| P3-046c | `Langlands.MatrixCharpolyFiniteConjugacyStatement.{uK}` (`123284c0`) | `matrixCharpolyFiniteConjugacy`, `MatrixCharpolyConjugacyProof.lean:13` (`2450494e`) | 4 "unproved"; 39–42 future "will use"; 48 "plan for the separate proof" | 4–6, 40–45, 51–52, 63–74 |
| P3-046d | `Langlands.MatrixTransposeConjugateStatement.{uK}` (`123284c0`) | `matrixTransposeConjugate`, `MatrixTransposeConjugateProof.lean:175` (`b5d5e4ba`) | 3 "unproved"; 39 "plan for the separate proof" | 3–6, 34–35, 42–45, 56–63 |
| P3-046e | `Langlands.PolynomialModuleBoundedCyclicDecompositionStatement.{uK, uV}` (`a74ef41f`) | `polynomialModuleBoundedCyclicDecomposition`, `PolynomialModuleBoundedCyclicDecompositionProof.lean:125` (`d82ec758`) | 4 "unproved"; 76–77 "remains a separate proof obligation" | 4–8, 54–57, 81–85 |

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
These remain targets of the parent task …". The inverse laws are the published Prop
`RestrictedProduct.TensorEquivInverseLaws`
([TensorEquivStatement.lean](../../../Langlands/LinearAlgebra/RestrictedProduct/TensorEquivStatement.lean); first in the Library at `1d1a5670`). For both the `R`-linear and the `M`-linear equivalence, it
asserts both identities `e.symm (f x) = x` and `f (e.symm y) = y` between the
canonical forward map `f` and the actual `.symm`. The theorem
`RestrictedProduct.tensorEquivInverseLaws_proof :
TensorEquivInverseLaws.{uR, uM, uι, uN}`
([TensorEquivProof.lean](../../../Langlands/LinearAlgebra/RestrictedProduct/TensorEquivProof.lean),
line 22; first in the Library at `cb6a47b2`) proves it.

As the audit notes, no coordinate formula for the inverse maps exists in the
module or in its companions. The inverses are obtained noncomputably through
`LinearEquiv.ofBijective`. So the inverse-law half of the sentence was stale,
and the formula half remains accurate.

Correction: the change to the definition module of
`RestrictedProduct.lTensorEquiv` replaces the bullet with two, at lines 175–184. One says the module gives no
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

| Theorem in `Langlands.FML.Padic` | Line |
| --- | --- |
| `latticeAgreement` | 57 |
| `unitFiltrationAgreement` (every `k : ℕ`, including level zero) | 67 |
| `additiveConductorAgreement` | 132 |
| `multiplicativeConductorAgreement` | 156 |

In [CanonicalPackages.lean](../../../Langlands/LocalFactor/FML/CanonicalPackages.lean),
`localQuasiCharData` (line 24) is certified by
`multiplicativeConductorAgreement`, and `localAddCharData` (line 40) by
`additiveConductorAgreement`. Neither chooses a new conductor. Their
definition module first appeared in the Library at `efd2d4ad`. The hypotheses and normalizations stated by the four Props are
unchanged: same `TopologicalData` instances, negative additive lattice index,
zero integral-unit layer and natural multiplicative conductor domain.

Correction: the change to the statement module of
`Langlands.FML.Padic.LatticeAgreementStatement` adds the section
"Published proofs and packages" at lines 85–106 and a link at lines 10–12.

## P3-049: Weil representation operations status

Affected file:
[Operations.md](../../../Langlands/Weil/Representation/Operations.md),
audited lines 5–6: "It is a target for later proof, not an axiom or a proved
theorem." The theorem `Langlands.Weil.representationOperations :
RepresentationOperations.{uG, uV, uU, uT}`
([OperationsProof.lean](../../../Langlands/Weil/Representation/OperationsProof.lean),
line 19; first in the Library at `bfd2c6b4`) is the conjunction of the five component proofs:

| Component proof in `Langlands.Weil` | Published |
| --- | --- |
| `representationIsomorphismInvariance` | `f01c1864` |
| `representationRankDeterminant` | `68e8013f` |
| `representationExactSequenceInvariants` | `f01c1864` |
| `representationOperationClosure` | `f56650f1` |
| `representationCharacterNormalization` | `f01c1864` |

The audited lines 46–53 also described the construction companion as
unpublished, with quotient rank invariance as "its existing definition
obligation". The audit does not raise this, but it was also stale. The
companion modules `Langlands.Weil.Representation.Basic` and `Predicates` are
published, and `Basic` already contains
`FiniteRepresentation.rank_eq_of_equiv` and `FiniteRepresentation.classRank`.

Correction: the change rewrites lines
5–8, corrects the companion sentences at lines 48–58 and 126–129, and adds a
"Published proofs" table at lines 83–99. It also adds an environment note at
lines 119–121. The finite-dimensional, continuity and normalization
hypotheses of the five Props are unchanged. In the table of corrections
below, this correction is listed under the statement
`Langlands.Weil.RepresentationOperations`.

## Corrections and the commits where they entered the Library

Every correction was checked by machine with Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, and entered the Library at the
commit shown.

| Finding | Corrected declaration | Commit at which it entered the Library |
| --- | --- | --- |
| P3-016 | statement `Langlands.Renard.SchurTheoremStatement` | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| P3-018, P3-043 | statement `Langlands.Algebra.LocalRingApproximationExistenceStatement` | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| P3-044 | statement `Langlands.Renard.ExactnessHomologyComparisonStatement` | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| P3-045 | statement `Langlands.Renard.NoetherIsomorphismsStatement` | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| P3-046a | statement `Langlands.CyclicQuotientPairingStatement` | `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| P3-046b | statement `Langlands.MatrixAEvalConjugacyStatement` | `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| P3-046c | statement `Langlands.MatrixCharpolyFiniteConjugacyStatement` | `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| P3-046d | statement `Langlands.MatrixTransposeConjugateStatement` | `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| P3-046e | statement `Langlands.PolynomialModuleBoundedCyclicDecompositionStatement` | `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| P3-047 | definition `RestrictedProduct.lTensorEquiv` | `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| P3-048 | statement `Langlands.FML.Padic.LatticeAgreementStatement` | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| P3-049 | statement `Langlands.Weil.RepresentationOperations` | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |

Each correction was built with Lake when it entered the Library, and every
corrected file is byte-identical to the Library file at that commit.

The companion proofs cited above were each checked with a Lake build,
against their exact targets, with statements and inputs unchanged; the FML
canonical packages were checked as definitions. These are per-module checks;
this note claims no full-Library kernel build.

## What remains open

- P3-044: no Renard complex-level comparison (chain-complex functor or
  natural homology isomorphism) is stated. The
  corrected Markdown says that the module `ExactnessHomologyStatements` states no such target.
- P3-047: no coordinate formula for the inverse tensor maps exists. The
  audit does not ask for one, and the corrected Markdown says so.

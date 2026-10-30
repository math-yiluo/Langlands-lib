# External Library audit 2026-10-29: induction, Whittaker constructions, compact coefficients and smooth representations

Worker 1059 and Worker 1066. This note records the verdicts for the thirteen
findings P3-024, P3-071, P3-076–P3-080, P3-084 and P3-087–P3-091, assigned by
task `91a18ec4-62e3-46b4-9a78-3f9612d4c07f`, revision 2. The source report is
the registered `external-library-audit-2026-10-29-3987c3d`, file
`FINAL_AUDIT_3987c3d.md` (findings at its lines 92, 166, 171–175, 179 and
182–186). Its allegations were treated as unverified. They were checked
against complete Lean declarations, universes, imports, proof companions,
paired Markdown, the original source where a finding concerns one, and the
authoritative candidate, review and publication records.

Worker 1066 verified and corrected P3-024, P3-071 and P3-076–P3-080. Worker
1059 verified and corrected P3-084 and P3-087–P3-091, and also re-verified
every verdict of Worker 1066 independently. Worker 1059 wrote this note.

## Snapshots and verdict convention

All thirteen findings **hold** at the audited Library commit
`3987c3d7445531c2c7f784464a3fd47061ba0865` (A below). Each defect is a
status claim in documentation: paired Markdown, and in one case a Lean module
docstring, calls a proposition unproved or a proof "still needed", although a
published Library theorem at A already proves exactly that proposition. Every
correction is documentation-only. No Lean declaration, type, hypothesis,
universe, import or proof was changed. The only Lean byte change is the module
docstring of `CompatibleMonomialFixedStatement.lean` (P3-078).

No intervening publication repaired any finding. At each Library head from
`b58bd42aee6a565b689f0f0c008506e23b1b6560` (the first head after A) to C,
the owned files were compared with the previous head. Each owned file changed
only at the publication of its own correction. The comparison snapshot of this
edition is Library `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` (C below), at
which the last corrections, D4 and D5, were published. At C every owned file
has exactly the bytes of its published correction, or the bytes of A if no
correction changed it (see the fingerprints below). Every cited proof module,
and both adjacent files named at the end, are byte-identical at A and C.

All locations are Library-relative. `Wh`, `Par`, `Ind`, `Geo`, `Exp`, `CC`,
`Smooth`, `HA` and `Group` abbreviate `Langlands/Representation/Whittaker`,
`Langlands/Representation/Parabolic`, `Langlands/Representation/Induction`,
`Langlands/Representation/Geometric`, `Langlands/Representation/Exponents`,
`Langlands/Representation/CompactCoefficient`,
`Langlands/Representation/Smooth`, `Langlands/HarmonicAnalysis` and
`Langlands/Group`.
Line numbers refer to A unless a candidate or C is named.

The Lean environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`). A private `lean_check`
probe (diagnostic `7faa2f7e-58e1-439e-8703-c53fbc67428a`, not a Library file)
elaborated, at independent universe variables, each theorem cited below as a
term of exactly its stated proposition. It reported zero errors and warnings,
and only the axioms `propext`, `Classical.choice` and `Quot.sound` for the
eleven declarations whose axioms it printed (ten cited theorems and the P3-024
equality below). The probe also checked these derived facts:

- `characterChangeElement a n = GeneralLinear.Iwasawa.diagonalUnits (fun i => a ^ (n - i))`,
  proved by `Units.ext rfl` (P3-024; Worker 1066 found the same in diagnostic
  `9f9f410b`, and Worker 1059 in diagnostic `e2eea19b-47e9-47cf-93ea-df2813ccd003`);
- `padicRowFourierSurjectivity F T d` for an arbitrary `T : F.TopologicalData`,
  and `twoBlockWhittakerExtension_of_rowFourierSurjectivity` applied to its
  canonical specialization, give `TwoBlockWhittakerExtensionStatement` (P3-080);
- `normalizedSecondAdjointness.2 : RefinedSecondAdjointnessClause` (P3-090);
- `PadicGeometricWeylTheorems` follows by an anonymous constructor from the
  three conjunct proofs; no Library theorem states it as one declaration
  (P3-087).

## Per-finding ledger

Each verdict is for A. The correction keys refer to the release table below.
"Repaired at C" means that the keyed correction is published and C contains it.

| Finding / subclaim | Verdict at A | Location in A and Lean evidence | Decision and status at C |
|---|---|---|---|
| **P3-024** | **Holds** | Wh/CharacterChange.md:20–21: "The Library has no diagonal-torus embedding to reuse." `GeneralLinear.Iwasawa.diagonalUnits` (Wh/Iwasawa.lean:278; proof artifact `e4518542`, published at `18fac9a1`) is the homomorphism from unit tuples to invertible diagonal matrices. `characterChangeElement` (Wh/CharacterChange.lean:27) is built directly but equals `diagonalUnits` of the tuple `i ↦ a^(n-i)` by `Units.ext rfl`. | Key D1. The paragraph now names `diagonalUnits`, says this module does not import it, states the equality and says no Library lemma records it. Repaired at C. |
| P3-024: suggested wording | Accurate in substance | The audit asks to describe `characterChangeElement` as "an explicit specialization". It is not defined through `diagonalUnits`; the two coincide definitionally. The sentence was true when written: `Wh/Iwasawa.lean` did not exist at CharacterChange's publication commit `ef274d37`. | The correction states equality, not a definitional dependency. |
| **P3-071** | **Holds** | Par/FineAmbientQuotientTransportStatement.md:5, 58–59 ("The intended proof"), 73–74 ("no proof of this proposition is published"). `fineAmbientQuotientTransport` (Par/FineAmbientQuotientTransportProof.lean:20; `a3966c99`, published at `00be69b7`) has type exactly `FineAmbientQuotientTransportStatement` at the same four universes and follows the described route. | Key D2. Cites the exact proof; route now described as the implemented one. Repaired at C. |
| **P3-076** | **Holds** | See the subrows. | Key D3. Repaired at C. |
| P3-076 (a): prerequisite | Holds | Wh/BruhatCompatibleSupportStatement.md:241–246 call `CharacterAverageSurjectiveStatement` "proof pending". `characterAverageSurjective` (HA/Distribution/CharacterAverageSurjectiveProof.lean:110; `f5ed0e18`, published at `cb6a47b2`) proves it; `CharacterAverageSurjectiveStatement.surjective_standardCharacterAverage` (HA/Distribution/CharacterAverageSurjectiveStatement.lean:71) specializes it. | Cites both. |
| P3-076 (b): the target itself | Holds (beyond the audit) | md:7 ("unproved"), 225–228, 266–268 and 286 ("A separate proof task follows") deny a proof of the target. `bruhatCompatibleSupport` (Wh/BruhatCompatibleSupportProof.lean:194; `591b752d`, published at `4e6ed28c`) proves `BruhatCompatibleSupportStatement` exactly. | Cites the target's own proof. |
| P3-076 (c): audit caution | Does not hold | The audit says to update the dependency "only" because "the Bruhat compatible-support target is separate". It is separate from the prerequisite, but its own proof is published (subrow b). Leaving md:7 and 286 unchanged would keep a false claim. | Not followed; see the P3-076 section. |
| **P3-077** | **Holds** | Wh/BruhatFiberCharacterCovarianceStatement.md:9–10 ("unproved proposition"), 176–180, 229–231 and 268 call the target unproved. `bruhatFiberCharacterCovariance` (Wh/BruhatFiberCharacterCovarianceProof.lean:26; `21eb8285`, published at `8c73c345`) proves it exactly under the statement's measure hypotheses. | Key D3. Opening, proof-route, scope and consumer passages updated. Repaired at C. |
| P3-077: generic covariance | Holds (beyond the audit) | md:205–209 call the generic covariance result of task `5117fcbc` unproved. `characterAverageCovariance` (HA/Distribution/CharacterAverageCovarianceProof.lean:21; `c6cadd36`, published at `cb6a47b2`) proves `CharacterAverageCovarianceStatement`. Neither the fiber statement nor its proof uses it. | Now cited as proved and unused. |
| **P3-078** | **Holds** | Wh/CompatibleMonomialFixedStatement.md:5 ("unproved") and 152–153 ("A proof is left to a separate task"); the Lean module docstring (Wh/CompatibleMonomialFixedStatement.lean:8–9) says "unproved proposition". `compatibleMonomialFixed` (Wh/CompatibleMonomialFixedProof.lean:413; `6e7d99cc`, published at `910a6df8`) proves it exactly. | Key D3. Markdown and docstring cite the proof; no declaration changed. Repaired at C. |
| **P3-079** | **Holds** | Wh/GenericDualStatement.md:3 ("unproved proposition"), 68–69 and 130–131. `genericContragredient` (Wh/GenericDualProof.lean:19; `3e3ae338`, published at `91863c20`) proves `GenericContragredientStatement` exactly, through `gelfandKazhdanContragredient` (Smooth/Contragredient/GelfandKazhdanProof.lean:19; `31571ec8`, published at `4021bb1d`) and `Whittaker.explicitSmoothDualFunctional` (`18fc6585`, published at `a6c8885e`). | Key D4. Repaired at C. |
| P3-079: inverse transpose | Holds (beyond the audit) | md:37–38 say the group-geometry task "remains responsible" for a bundled inverse-transpose homomorphism. `GeneralLinear.inverseTranspose` (Group/GL/Maps.lean:96) exists at A; the statement does not import it, and the proof identifies the two by `Units.ext`/`rfl`. | Key D4 cites it. Repaired at C. |
| **P3-080** | **Holds** | See the subrows. | Keys D5 and D6. Repaired at C. |
| P3-080 (a): statement Markdown | Holds | Wh/TwoBlockExtensionAssemblyStatement.md:32–34: "The unchanged parent target still requires an unconditional surjectivity theorem". `padicRowFourierSurjectivity` (HA/PadicRowFourierSurjectivityProof.lean:17; `604d70c0`, published at `61f87bbe`) proves `PadicRowFourierSurjectivityStatement F T d` for every p-adic field, every `T : F.TopologicalData` and every `d`, including `d = 0`. | Key D5 (statement pair). Repaired at C. |
| P3-080 (b): proof Markdown | Holds | Wh/TwoBlockExtensionAssemblyProof.md:51–53: "An unconditional proof of that analytic family is still needed". Same evidence. The proof module does not import `PadicRowFourierSurjectivityProof` or `TwoBlockExtensionProof`, transitively. | Key D6, child task `3a8e7d5e-19be-40c1-95bf-6ce1708b8d28`. Repaired at C. |
| P3-080 (c): audit caution | Does not hold | The audit says to cite the specialization "without claiming a separately exported unconditional extension wrapper". `twoBlockWhittakerExtension` (Wh/TwoBlockExtensionProof.lean:12–16; `682c991b`, published at `e9af3dd7`) is exported. It proves `TwoBlockWhittakerExtensionStatement.{uF, uV₁, uV₂}` unconditionally, by applying the assembly theorem to that specialization. | Both corrections name it, and keep the assembly proposition and its proof conditional. |
| P3-080 (d): Lean interface | Correct; no change | `TwoBlockExtensionAssemblyStatement` remains an implication with the row-surjectivity premise; `twoBlockWhittakerExtension_of_rowFourierSurjectivity` (Wh/TwoBlockExtensionAssemblyProof.lean:92; `284a8cb7`, published at `8d85a8df`) proves it. | Unchanged. |
| **P3-084** | **Holds** | See the subrows. | Key E1. Repaired at C. |
| P3-084 (a): opening | Holds | CC/SemisimplicityStatement.md:5–6: "its truth has not been proved in Lean". `compactCoefficientSemisimplicity` (CC/SemisimplicityProof.lean:383; `1e1f8f18`, published at `cddb0412`) takes exactly the statement's binders and proves `CompactCoefficientSemisimplicityStatement.{uG, uV} G μ`. | Cites it. |
| P3-084 (b): relation paragraph | Holds in part | md:163: "Both are unproved". False for semisimplicity. True for `CompactCoefficientSplittingStatement`: no Lean file other than CC/SplittingStatement.lean mentions it, and no theorem proves it. | Only the semisimplicity half is corrected; the splitting statement is still described as unproved. |
| P3-084 (c): source | Accurate; no change | md:3–4 and 144–151 quote Bernstein–Zelevinsky 1976, Theorem 2.44(b), last sentence: "In particular, any finite module is completely reducible." Checked in `bernstein-zelevinsky-1976-representations-gln`, printed p.28 = PDF page 28 (SHA256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`). | Unchanged. The correction says the Lean proof does not follow Theorem 2.42 or the projectors of Section 2.43. |
| **P3-087** | **Holds** | Geo/WeylDefinitions.md:69–71 list uniqueness of minimal representatives, Bruhat bijectivity and standardness of the intersection triples as "unproved obligations". At A: `weylMinimalRepresentativeUniqueness` (Geo/WeylUniquenessProof.lean:117; `1e54306f`, published at `dd9f9be5`), `weylMinimalRepresentativeTheorem` (Geo/WeylMinimalRepresentativeProof.lean:121; `be673197`, published at `9488f812`), `padicParabolicBruhat` (Geo/PadicParabolicBruhatProof.lean:39; `66197c1e`, published at `3f303847`), `padicStandardIntersectionsTheorem` (Geo/StandardIntersectionsProof.lean:185; `454f2f13`, published at `67dfb8a2`). | Key E2. Cites the four theorems with their exact scopes (injectivity for every rank, bijectivity for positive rank, the inverse-permutation convention, three equalities for `(B, C, w)` and three for `(C, B, w⁻¹)`). Says no single declaration proves `PadicGeometricWeylTheorems` and the geometric lemma is a separate target. Repaired at C. |
| **P3-088** | **Holds** | Ind/CompactScalarStatement.md:7–8 ("awaiting proof"), 87–89 and 108–114 ("A proof must still construct…"). `glParabolicCompactScalarIntegral` (Ind/CompactScalarProof.lean:35; `ceff0623`, published at `b01da032`) has type exactly `GLParabolicCompactScalarIntegralStatement.{uF}`. | Key E3. Adds "Proof status": `K` and `μ` constructed before the quantifiers, full block modulus identified with the modular character, implemented route. Scalar result not extended to duality or unitarity. Repaired at C. |
| **P3-089** | **Holds** | Ind/NormalCoinvariantKernelStatement.md:107 ("Elementary proof route still to be implemented") and 130 ("part of the future proof"). `compactInductionNormalCoinvariantKernel` (Ind/NormalCoinvariantKernelProof.lean:273; `5b05899e`, published at `6543e70e`) has type exactly `CompactInductionNormalCoinvariantKernel.{uG,uV}`. | Key E4. Adds "Proof status", keeping both universes and every hypothesis: basis, closedness, normality, containment, smoothness. Repaired at C. |
| **P3-090** | **Holds** | Exp/RefinedQuotientOppositeCharacterStatement.md:128 ("without proof") and 155–161 ("A future proof must establish each ingredient…", naming task `eb76bbde`). `normalizedSecondAdjointness` (Par/SecondAdjointnessProof.lean:18; `4be76e11`, published at `d8425b46`): its second component is a term of `RefinedSecondAdjointnessClause`. `refinedQuotientOppositeCharacter` (Exp/RefinedQuotientOppositeCharacterProof.lean:40; `ba2fd5e6`, published at `a8a83747`) proves the statement exactly from it. | Key E5. Cites both, keeps the proposition interface and states that no ingredient may become a hypothesis. Repaired at C. |
| **P3-091** | **Holds** | Ind/UnitaryStatement.md:151 ("Remaining proof obligations"), 166–167 and 228–234 ("these preservation proofs remain to be formalized"). `glNormalizedParabolicInductionUnitarity`, `glNormalizedProductInductionUnitarity` and `glNormalizedInductionUnitarity` (Ind/UnitaryProof.lean:19, 36, 55; `cd7dcc1a`, published at `06ce3701`) prove the three propositions exactly, at independent `uF`, `uV`. md:166–167 also call the Haar-module comparison an obligation; `glBlockModulusHaar` (Group/GL/BlockModulusHaarProof.lean:123) proves it. | Key E6. Adds "Proof status": no added admissibility, irreducibility or finite-dimensionality hypothesis; scalar input from `glParabolicCompactScalarIntegral`, tensor form from `FiniteTensor.invariantPositiveForm`. Repaired at C. |

## P3-024: diagonal units

Worker 1066 found, and Worker 1059 confirmed with an independent check, that
`characterChangeElement a n` and
`diagonalUnits (fun i : Fin (n + 1) => a ^ (n - i))` are equal by
`Units.ext rfl`. Their values and inverses agree definitionally. The audit's
mathematical claim is correct. Its wording "explicit specialization" would
suggest that one is defined through the other. The correction avoids that: it
states the equality, notes that the module does not import
`Wh/Iwasawa`, and says no Library lemma records the equality. JPSS 1983,
Section 2.1, printed p.385, is the module's source for the diagonal character
change. The finding concerns only the Library-internal remark, so no source
claim is at issue.

## P3-076–P3-078: Bruhat compatible support and its inputs

The three statement pairs were written before their proofs, and their
Markdown kept the planning language. At A each target has a published exact
proof: `bruhatCompatibleSupport`, `bruhatFiberCharacterCovariance` and
`compatibleMonomialFixed`. The audit's caution for P3-076 is inaccurate. It
is true that a proof of the prerequisite `CharacterAverageSurjectiveStatement`
does not by itself prove the compatible-support target. But that target has
its own published proof, which takes step 1 of the plan from
`bruhatFiberCharacterCovariance` and the surjectivity from
`characterAverageSurjective`. Correction D3 therefore cites each proof as the
proof of its own statement. It does not present a prerequisite as a proof of
the target. For P3-077 the correction keeps the statement's explicit measure
hypotheses. It says the generic covariance theorem is now proved but is not
used, because the fiber statement translates the first factor by a
`d`-dependent element. For P3-078 the correction says the proof is a
self-contained argument with root transvections, not a transcription of
Shalika's (1.5) (Shalika 1974, printed p.174). The source citation itself is
unchanged.

## P3-079: generic contragredient

`genericContragredient` takes the first conclusion, a linear equivalence
`E : V ≃ SmoothDual ρ` with `E (ρ (g⁻¹)ᵀ v) = ρ̃ g (E v)`, from
`gelfandKazhdanContragredient`, which needs only admissibility and
irreducibility. It takes nonvanishing and the
inverse-character covariance from `explicitSmoothDualFunctional` and its two
lemmas, applied to the given functional. Worker 1066 re-read JPSS 1983,
Section 2.1, p.386, equation (4), which the statement cites. The correction
leaves that citation and the generic irreducible admissible scope unchanged.
The Lean docstring was already accurate.

## P3-080: row-Fourier surjectivity and the extension wrapper

Both assembly notes said that an unconditional row-surjectivity theorem was
still needed. At A, `padicRowFourierSurjectivity` proves the family for every
topological data, so its canonical specialization supplies the full premise
of `TwoBlockExtensionAssemblyStatement`. The audit's caution is inaccurate.
The Library exports `twoBlockWhittakerExtension`, which proves the
unconditional `TwoBlockWhittakerExtensionStatement` in exactly this way. The
corrections name both theorems. They keep the assembly proposition an
implication, and the assembly proof conditional on its explicit premise. Its
module imports neither `PadicRowFourierSurjectivityProof` nor
`TwoBlockExtensionProof`.

The statement half is an ordinary `lean.statement` candidate of this task
(D5). The proof Markdown needs a `lean.proof` candidate. Staging one under
this task's policy `lean.peer@1` was refused ("A machine-checked candidate
requires its original task policy"), so Worker 1066 published the focused child
task `3a8e7d5e-19be-40c1-95bf-6ce1708b8d28` (policy `lean.proof@1`;
publishers Worker 1066 and Worker 1059). It carries Worker 1066's draft as
draft revision 1 of this task (content key
`c2ce3615481b4ad14825adb6c238280502959f7d5cadff870d7ec1f36815cfa6`). Worker 980
executed it. Its candidate was published as D6, and the child task is
completed.

## P3-084: semisimplicity and splitting

The audit distinguishes semisimplicity from the separately bundled splitting
target, and that distinction is correct. `compactCoefficientSemisimplicity`
proves `CompactCoefficientSemisimplicityStatement` for every group and measure
satisfying the statement's binders, with independent universes and no
hypothesis on the representation. It proves nothing about
`CompactCoefficientSplittingStatement`, which no Library theorem proves.
Correction E1 corrects only the semisimplicity status and keeps "has no proof
in the Library" for the splitting statement. The quotation of
Bernstein–Zelevinsky's Theorem 2.44(b) was checked against the source (see
the table). The new "Proof status" section says that the Lean proof does not
follow BZ's route through Theorem 2.42 and the projectors of Section 2.43. It
also says that the proof accepts `SigmaCompactSpace G`, `Measure.Regular μ`
and `Measure.IsMulRightInvariant μ` but does not use them; the statement keeps
these hypotheses.

## P3-087–P3-091: Weyl geometry, induction and second adjointness

Each of these statement pairs predates its proof, and the proofs were
published before A. The corrections keep each statement module described as
proof-free and add the exact proof's name, module and scope. Every
qualification required by the area is retained: the inverse-permutation
convention and the separate geometric-lemma target (P3-087); the full block
modulus, the probability Haar normalization on `K`, and no extension to
duality or unitarity (P3-088);
closedness, normality, containment, smoothness and two independent universes
(P3-089); the proposition interface and all admissibility hypotheses of the
refined clause (P3-090); and independent field and carrier universes with no
added admissibility restriction (P3-091). The alternative disintegration
route in UnitaryStatement's proof plan is kept as the plan written with the
statement, and the actual route is described separately.

## Corrections and release evidence

Every correction is a focused ordinary candidate that edits only Markdown, and
for D3 one Lean docstring, of the owned file pairs listed in the fingerprint
tables. D6 is a candidate of the child task described under P3-080; every
other correction is a candidate of this task. The bases are A or a later head
whose owned files equal A, except for already published corrections of this
task.

| Key | Findings | Candidate (policy) | Author | Machine validation | Independent review | Publication |
|---|---|---|---|---|---|---|
| D1 | P3-024 | `aa77db84-d976-44f6-81bd-b8ad173844a8` (`lean.definition`) | Worker 1066 | `33d205eb-c9da-4ee3-971e-d51f6ea0453e` (accepted) | task `3f3cfda5-ed77-4f77-b89d-54602ccdbf7b`, approved by Reviewer 4602, no qualifications | Integration `3fa9976cb76b4631a0579b7c6d525809` (batch `498cd055f707477e9a3f5ed7a92e04e5`, approve, no qualifications, fresh integrated Lake build accepted); Library `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| D2 | P3-071 | `556c14c6-7a52-4df8-b0d4-20a54bd5c61a` (`lean.statement`) | Worker 1066 | `c228c6ea-1f5f-4cda-abdf-a4549ad57345` (accepted) | task `e8f3119b-f07c-4286-9efc-d4d7f84c0d13`, approved by Reviewer 4613, no qualifications | Integration `20d93dc67d4d4dbabd69d5b455009d7f` (batch `498cd055f707477e9a3f5ed7a92e04e5`, approve, no qualifications, fresh integrated Lake build accepted); Library `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| D3 | P3-076, P3-077, P3-078 | `8b2d7668-4a6d-4142-ba71-7f5c817e8401` (`lean.statement`) | Worker 1066 | `ed5af7a2-b2d5-4279-b3af-5660148a9564` (accepted) | task `cff13a8c-0260-47c1-b541-b0b37ed3e110`, approved by Reviewer 4664, no qualifications | Integration `1b069e296abb4c2c82a726d70aadb1ee` (batch `289cd90d6d7147ce8016ea239c85dce3`, approve, no qualifications, fresh integrated Lake build accepted); Library `6a6c913c7339c50634dd74722034032e7a167d97` |
| D4 | P3-079 | `8fe7a3a2-0e1b-424b-93b5-8af5a8461b44` (`lean.statement`), resubmits `9af9d66c` | Worker 1066 | `056ee0e7-af3f-41bd-9608-56968607428d` (accepted) | task `1d38b536-1f7d-42ef-8604-6e0f2a22a707`, approved by Reviewer 4747, no qualifications | Integration `18b1a297cc7e499195205a8ecbf683ed` (batch `8e63a9d684c34de2ab37ceba21c8d400`, approve, no qualifications, fresh integrated Lake build accepted); Library `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` |
| D5 | P3-080 (a) | `40e2aeff-8b8c-40e0-857c-cb4b421a2acd` (`lean.statement`), resubmits `68c4b9c1` | Worker 1066 | `54627dc3-d45d-4db0-9d23-5da76c170b24` (accepted) | task `dda588ba-8268-4afe-8179-e0712279d004`, approved by Reviewer 4750, no qualifications | Integration `d349e95dcd5c4734b3f188561fc33da7` (batch `8e63a9d684c34de2ab37ceba21c8d400`, approve, no qualifications, fresh integrated Lake build accepted); Library `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` |
| D6 | P3-080 (b) | `25d58629-432e-41aa-9c01-24c3db6858e7` (`lean.proof`), child task `3a8e7d5e-19be-40c1-95bf-6ce1708b8d28` | Worker 980 | `7358408f-0970-4001-8617-7c53a8c86c8c` (accepted; exact target, unchanged statement) | task `25af9922-185a-4923-b5c8-626e426401c8`, approved by Reviewer 4724, no qualifications | Integration `242100387fc9419d98fbccadf9a581af` (batch `18c3545d35894e979aa9890314e49d25`, approve, no qualifications, fresh integrated Lake build accepted); Library `cde31751c7864199419ad8fae8b7f3474639ba24` |
| E1 | P3-084 | `88cdfa48-64d7-4eb3-b7b6-5ec4013609c6` (`lean.statement`), resubmits `19e56067` | Worker 1059 | `6345216b-5922-4c15-a9da-10909597da2c` (accepted) | task `51f119e8-1f3f-4dbb-ae63-d088ff10c3c9`, approved by Reviewer 4741, no qualifications | Integration `e801bf35cbd44258bb70fece8507b3ad` (batch `18c3545d35894e979aa9890314e49d25`, approve, no qualifications, fresh integrated Lake build accepted); Library `cde31751c7864199419ad8fae8b7f3474639ba24` |
| E2 | P3-087 | `ead840cc-0dfe-4661-a01f-c45ce2629451` (`lean.definition`) | Worker 1059 | `217fb4e0-6778-481b-be51-60e30d43a4e3` (accepted) | task `2920f27e-8f6e-430b-8b2d-b52d98d8ee1e`, approved by Reviewer 4634, no qualifications | Integration `6122da1bece54566a3b89de910bc321b` (batch `601d50d0ad7d477ba5cfaa8c405869d0`, approve, no qualifications, fresh integrated Lake build accepted); Library `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| E3 | P3-088 | `2d00ed44-109b-4aa3-bbdc-524f86f988e9` (`lean.statement`) | Worker 1059 | `b47f768d-1a1a-436f-88a4-7aa6e85ef2d5` (accepted) | task `630caf42-134e-421f-96c9-b390c08ad81a`, approved by Reviewer 4659, no qualifications | Integration `aa39c87fef734bbe89198c176b745552` (batch `601d50d0ad7d477ba5cfaa8c405869d0`, approve, no qualifications, fresh integrated Lake build accepted); Library `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| E4 | P3-089 | `af6b51a8-8c5d-44e2-b642-88f39d4e8f73` (`lean.statement`) | Worker 1059 | `90856b0d-62a2-49cc-84fe-8ac6a23b8b4d` (accepted) | task `06eaaa23-0dde-4007-b2c1-40a9f8901861`, approved by Reviewer 4661, no qualifications | Integration `3c098b6e148044d9bc623109924fc246` (batch `601d50d0ad7d477ba5cfaa8c405869d0`, approve, no qualifications, fresh integrated Lake build accepted); Library `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| E5 | P3-090 | `a420ae8f-0872-4a8c-a77c-8f3c1d9f45fe` (`lean.statement`), resubmits `45d06534` | Worker 1059 | `a309cb3c-7ea6-4d62-b87e-931a3b90e820` (accepted) | task `a622814f-bf04-4ebb-9cf8-324df8ce79c6`, approved by Reviewer 4744, no qualifications | Integration `0696a611a33b49f7b265b5a8c22f349f` (batch `18c3545d35894e979aa9890314e49d25`, approve, no qualifications, fresh integrated Lake build accepted); Library `cde31751c7864199419ad8fae8b7f3474639ba24` |
| E6 | P3-091 | `1c171e01-c64e-45d2-be7e-88f075b3b2bd` (`lean.statement`) | Worker 1059 | `cf577f3d-ef06-4d02-aaf2-2d62cf9edd37` (accepted) | task `7ae777a9-efa3-43a9-bdc3-997c78ae3c44`, approved by Reviewer 4667, no qualifications | Integration `01e64cbe2de4455794b6be38f89f2ca3` (batch `289cd90d6d7147ce8016ea239c85dce3`, approve, no qualifications, fresh integrated Lake build accepted); Library `6a6c913c7339c50634dd74722034032e7a167d97` |
| (withdrawn) | P3-024 | `91a4ccda-91ef-4a87-b714-6589de329352` (`lean.definition`) | Worker 1059 | `4c318fc4-cb35-4b53-88fb-683f410246fc` (accepted) | task `1bb6823c-3c38-40c8-b112-7d443c31909a`, approved by Reviewer 4592; candidate then withdrawn | Not published. A duplicate of D1, prepared before the split of findings was agreed. It was withdrawn after a recheck that D1 covered the same paragraph with byte-identical Lean. |
| (superseded) | P3-079 | `9af9d66c-042d-4815-90be-4450e72edc7a` (`lean.statement`) | Worker 1066 | `7826303a-e8bb-4269-9115-8b2748282802` (accepted) | task `ae6a8afd-807a-4b82-b141-0276a9d580ad`, approved by Reviewer 4704; review then invalidated | Not published. Superseded by the task revision; resubmitted byte-identically as D4. |
| (superseded) | P3-080 (a) | `68c4b9c1-0bab-4bcf-93b3-31de801b2ccd` (`lean.statement`) | Worker 1066 | `2412b213-d5f1-4700-8acd-e435e7fdf2de` (accepted) | task `d4d7f5bb-bca8-4613-8a53-f84ce5d851cb`, approved by Reviewer 4717; review then invalidated | Not published. Superseded by the task revision; resubmitted byte-identically as D5. |
| (superseded) | P3-084 | `19e56067-ca34-4c90-a598-fee5821e1e55` (`lean.statement`) | Worker 1059 | `912c73c5-e8eb-4c3c-92ac-266470a2d559` (accepted) | task `5841dd37-d4b5-495d-bde6-5fdabcef249e`, approved by Reviewer 4705; review then invalidated | Not published. Superseded by the task revision; resubmitted byte-identically as E1. |
| (superseded) | P3-090 | `45d06534-f4d7-4143-88ee-82e9f9c0b262` (`lean.statement`) | Worker 1059 | `e9b3469e-6b54-4271-9b48-151e8d58ac86` (accepted) | task `5e5b8255-3217-4bd9-893d-fa5f6707eb82`, approved by Reviewer 4692; review then invalidated | Not published. Superseded by the task revision; resubmitted byte-identically as E5. |

On 2026-10-30 Worker 0 revised this task from revision 1 to revision 2, as
the operator decided. Only one sentence of the objective changed. Under
revision 2 the task's executors may make corrections inside the task: each
correction is a focused candidate covering one reviewable unit, and each is
independently validated, reviewed and published. A separate child task is
needed only when a correction changes a Lean statement or proof target, or
touches files outside the task's assigned file pairs. The corrections D1–D5
and E1–E6 were made inside this task under revision 2, which covers both the
corrections already published when it was issued and the remaining ones. The
table lists the receipts as they were issued: D1–D3, E2–E4 and E6 were
validated, reviewed and published while revision 1 was current.

The revision superseded the four approved but not yet integrated revision-1
candidates, which are listed as superseded above, and invalidated their
reviews. Each was resubmitted under revision 2 as a new candidate whose
repository files, statement data and coauthors equal those of the superseded
candidate byte for byte. Each resubmission then went through fresh machine
validation, independent review and publication. D6 belongs to child task
`3a8e7d5e`, which was not revised. That task exists only because TaskHub
accepts a `lean.proof` candidate only under a task with that policy (see
P3-080). No retrospective child task was created.

Machine validation is not semantic acceptance. This note itself requires
separate independent review and publication.

## Adjacent passages outside this task's files

Two passages outside the owned files were found during verification. They
are not assigned findings, and they were not edited here:

- Group/GL/BlockModulus.md:47 (at A and C) says identification of the
  explicit block modulus with Haar scaling on the unipotent radical "remains a
  separate theorem obligation". `glBlockModulusHaar`
  (Group/GL/BlockModulusHaarProof.lean:123) proves
  `GLBlockModulusHaarStatement`, which states that identification. This
  status remark is stale and needs a separate focused correction.
- Geo/WeylStatement.md:73 calls the Bourbaki and Borel–Tits citations of
  BZ77 "proof-source obligations for future proof work". The same sentence
  correctly says the pair does not verify the cited proofs. The Lean proofs of
  P3-087 do not transcribe those sources, so this is at most a dated phrase,
  not a false status claim.

## File fingerprints

SHA256 of the owned pairs. The first table identifies the audited versions at
A. The second gives the same files at C and the correction that changed each
pair. Each changed file at C equals the same path in that correction's
published candidate bundle. Each file not changed equals A. In particular, the
only Lean file that differs between A and C is
`Wh/CompatibleMonomialFixedStatement.lean`, whose module docstring D3
changed.

| Pair stem | Lean in A | Markdown in A |
|---|---|---|
| CC/SemisimplicityStatement | `8e9f7ff68c7a2d61193f5f08891fb818f4985955ee680c83cc1421b4554a0389` | `97882c43180a11a77ec7f1ccef84597a9487de8d872c9af7b15d5c3eb601c09d` |
| Exp/RefinedQuotientOppositeCharacterStatement | `f690d650816c4b2e8fa327dc24958864b6225f6baea86aa3d6493332804af9d2` | `89dd29bc265d6ab3be5953b6ef2e52cd260d16df251913c2f2dfcd0e71f5c17c` |
| Geo/WeylDefinitions | `5f71ddd64c10ba33884b1b1ab684443ec650192a73b77bd487011fdadf138d01` | `8d37f82d12562fe51afce5e98b3373cea79f2b4e71f7d7e46c1430b005153365` |
| Ind/CompactScalarStatement | `fd4be35392bb9fe32c0af81a7474a2c7fa1187d3a8c143a8c0f3ed9c1383df60` | `ab1745a7cb3bee925d1479af1eea81be40d38e0e1143730ae0d5c069e56857b2` |
| Ind/NormalCoinvariantKernelStatement | `c811cab396e838a417d485078731575cde5eb9654aa6b06469718132974980ad` | `b66cf500810edf2acdb38c3a60af05d423318264f895f126f2431caf4b6b6cb6` |
| Ind/UnitaryStatement | `af0bb472c57e9399f0554a1217d79459724f334854ad2c46330cb74275643ec4` | `f8248e8e7310fb8ab13103561c0370f17d8b28121c0168ee7c841f4fd4ee4e99` |
| Par/FineAmbientQuotientTransportStatement | `6828496afdedad28a2cdd029fbc8311d1319be224cc8c9de18f628f2c66482df` | `c3336971937ba40ba856d8a2ab88fd0694b997f0fb5ab3c5092389c828a417d0` |
| Wh/BruhatCompatibleSupportStatement | `b383eace4776390224d0ed609ab5bcf59d824efadcec0b1b21849bd7f8996200` | `c3c2ad8cbe644b0e5b3f0fba4543b53d1e0bd83c071b7048ea928f2667204fb0` |
| Wh/BruhatFiberCharacterCovarianceStatement | `a07533bd75d944b0fd8e617cdcea65052a3e63cc4882843a420780d833203762` | `9c465899ba74a31b59074ed6b71daccb902b8ae1f71d3be5ccf989a2c748a372` |
| Wh/CharacterChange | `0156e7b1f733656f8c93596ce76c6ff7bcde7f2cd1f18330e41d4a041298abaa` | `240d261f0442613f490d8cb1501c68b8d4993bab321ea2c05691c9efecd74c88` |
| Wh/CompatibleMonomialFixedStatement | `479e760d9af72e3e54d70a5d2d86c3c670810cf8128ad422a6a8e9c02df22f9f` | `f094789766c33b42459b36cb9202cefc91ec63d8ad1f58d67ae6d667b7214dbb` |
| Wh/GenericDualStatement | `ddcb075d9e8307c215df6b6a6c202cee748f6a883bc4a5fcc1e870dcd063b64b` | `8c4913ddde11afeb297638d6db7a312c2ab76e67f3ce8feaf07a5c6b86134155` |
| Wh/TwoBlockExtensionAssemblyProof | `c3ca43282daa8877b678472e9041a8d14bc847413ffd4fd776a4df7afb7ff088` | `72049e3d439a09b8b01f0c523eb8769d3b62131cd514219dd4845ab606571080` |
| Wh/TwoBlockExtensionAssemblyStatement | `53cac3707d8c6f359f7cce518437e548827f80382999f744a8cac4c0770c1ff5` | `a2bb97ed91ab19f3ff60b5a93ecd707706dd02035062eff18b5ffa863f2d6531` |

| Pair stem | Changed by | Lean in C | Markdown in C |
|---|---|---|---|
| CC/SemisimplicityStatement | E1 | `8e9f7ff68c7a2d61193f5f08891fb818f4985955ee680c83cc1421b4554a0389` | `ddd9132288f52ad3186fca3d3de164bc913d56021bfd8222117d9350622c6a70` |
| Exp/RefinedQuotientOppositeCharacterStatement | E5 | `f690d650816c4b2e8fa327dc24958864b6225f6baea86aa3d6493332804af9d2` | `2d2c3df8b39c9dcdce9340e99c0acd2c2a2ccb473a43a9f53a5d7539fb2a2295` |
| Geo/WeylDefinitions | E2 | `5f71ddd64c10ba33884b1b1ab684443ec650192a73b77bd487011fdadf138d01` | `979ea6916e2fb3c7ebb427e9954719472602cb84de027ac9338b22df95e74513` |
| Ind/CompactScalarStatement | E3 | `fd4be35392bb9fe32c0af81a7474a2c7fa1187d3a8c143a8c0f3ed9c1383df60` | `b867f459d6df8e5cafbd5632b086a188373e6cc8e760d59cb3192ed0d451208c` |
| Ind/NormalCoinvariantKernelStatement | E4 | `c811cab396e838a417d485078731575cde5eb9654aa6b06469718132974980ad` | `fc92226d5279df3dc2405216643ab783b1e3943d9f805ab21c644ba0a7fa321c` |
| Ind/UnitaryStatement | E6 | `af0bb472c57e9399f0554a1217d79459724f334854ad2c46330cb74275643ec4` | `c0d63ebc54631077ddc54d850cc34898e45cfae877cd1d9994682749859b92d2` |
| Par/FineAmbientQuotientTransportStatement | D2 | `6828496afdedad28a2cdd029fbc8311d1319be224cc8c9de18f628f2c66482df` | `7e83aec5d155264a99fde67c34e5f478f7c69a286ab327130308614b5bcdd749` |
| Wh/BruhatCompatibleSupportStatement | D3 | `b383eace4776390224d0ed609ab5bcf59d824efadcec0b1b21849bd7f8996200` | `f71a341ba7475dd3c62c5da930fb100ff2f8d6fa5e8f72412125fca850c3de02` |
| Wh/BruhatFiberCharacterCovarianceStatement | D3 | `a07533bd75d944b0fd8e617cdcea65052a3e63cc4882843a420780d833203762` | `2569f067e1558faf79382e05f1fee498d9d1b58b79fc4fb32609025bd5ebc73e` |
| Wh/CharacterChange | D1 | `0156e7b1f733656f8c93596ce76c6ff7bcde7f2cd1f18330e41d4a041298abaa` | `cf7605ca7cc468added2f943aabb0565351f3434949491f6320fb3b2cefb2bc1` |
| Wh/CompatibleMonomialFixedStatement | D3 | `7c3434178b17b5eacc7811a7efa09652122f84fb837099a119c81e1e59e40f1f` | `9f1af9115219bd98c21dbd13e412c6dd9eee916bf41e11bfb4afadd7eaf04335` |
| Wh/GenericDualStatement | D4 | `ddcb075d9e8307c215df6b6a6c202cee748f6a883bc4a5fcc1e870dcd063b64b` | `f8ad321e73452eedee235744bf38f772d51001055ef1ce825757b12b738f861f` |
| Wh/TwoBlockExtensionAssemblyProof | D6 | `c3ca43282daa8877b678472e9041a8d14bc847413ffd4fd776a4df7afb7ff088` | `a064068aa127cbc838d343d3e6911340adad9092adcafcb906d18b5378fc18af` |
| Wh/TwoBlockExtensionAssemblyStatement | D5 | `53cac3707d8c6f359f7cce518437e548827f80382999f744a8cac4c0770c1ff5` | `d9ad484d3dec4c313ab1478f29214418480fd5642c4823dad67c32b25ebf741b` |

The audit report has SHA256
`d9a25f35dc2d7bef0351ba0891db168b0c3cc797a281d0a9944e930fe43d5eeb`.

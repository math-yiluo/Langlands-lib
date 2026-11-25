# External Library audit 2026-10-29: induction, Whittaker constructions, compact coefficients and smooth representations

This note records the verdicts for the thirteen findings P3-024, P3-071,
P3-076–P3-080, P3-084 and P3-087–P3-091 of the external Library audit of
2026-10-29. The source report is
the registered `external-library-audit-2026-10-29-3987c3d`, file
`FINAL_AUDIT_3987c3d.md` (findings at its lines 92, 166, 171–175, 179 and
182–186). Its allegations were treated as unverified. They were checked
against complete Lean declarations, universes, imports, proof companions,
paired Markdown, the original source where a finding concerns one, and the
record of the corrections that entered the Library. Every verdict was
verified twice, independently.

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
the audited files were compared with the previous head. Each audited file changed
only at the publication of its own correction. The comparison snapshot of this
edition is Library `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` (C below), at
which the last corrections, D4 and D5, were published. At C every audited file
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
Line numbers refer to A unless C is named.

The Lean environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. A `lean_check` probe (not a
Library file) elaborated, at independent universe variables, each theorem cited below as a
term of exactly its stated proposition. It reported zero errors and warnings,
and only the axioms `propext`, `Classical.choice` and `Quot.sound` for the
eleven declarations whose axioms it printed (ten cited theorems and the P3-024
equality below). The probe also checked these derived facts:

- `characterChangeElement a n = GeneralLinear.Iwasawa.diagonalUnits (fun i => a ^ (n - i))`,
  proved by `Units.ext rfl` (P3-024; two separate diagnostics found the same);
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
| **P3-071** | **Holds** | Par/FineAmbientQuotientTransportStatement.md:5, 58–59 ("The intended proof"), 73–74 ("no proof of this proposition is published"). `fineAmbientQuotientTransport` (Par/FineAmbientQuotientTransportProof.lean:20; in the Library since `00be69b7`) has type exactly `FineAmbientQuotientTransportStatement` at the same four universes and follows the described route. | Key D2. Cites the exact proof; route now described as the implemented one. Repaired at C. |
| **P3-076** | **Holds** | See the subrows. | Key D3. Repaired at C. |
| P3-076 (a): prerequisite | Holds | Wh/BruhatCompatibleSupportStatement.md:241–246 call `CharacterAverageSurjectiveStatement` "proof pending". `characterAverageSurjective` (HA/Distribution/CharacterAverageSurjectiveProof.lean:110; in the Library since `cb6a47b2`) proves it; `CharacterAverageSurjectiveStatement.surjective_standardCharacterAverage` (HA/Distribution/CharacterAverageSurjectiveStatement.lean:71) specializes it. | Cites both. |
| P3-076 (b): the target itself | Holds (beyond the audit) | md:7 ("unproved"), 225–228, 266–268 and 286 ("A separate proof task follows") deny a proof of the target. `bruhatCompatibleSupport` (Wh/BruhatCompatibleSupportProof.lean:194; in the Library since `4e6ed28c`) proves `BruhatCompatibleSupportStatement` exactly. | Cites the target's own proof. |
| P3-076 (c): audit caution | Does not hold | The audit says to update the dependency "only" because "the Bruhat compatible-support target is separate". It is separate from the prerequisite, but its own proof is published (subrow b). Leaving md:7 and 286 unchanged would keep a false claim. | Not followed; see the P3-076 section. |
| **P3-077** | **Holds** | Wh/BruhatFiberCharacterCovarianceStatement.md:9–10 ("unproved proposition"), 176–180, 229–231 and 268 call the target unproved. `bruhatFiberCharacterCovariance` (Wh/BruhatFiberCharacterCovarianceProof.lean:26; in the Library since `8c73c345`) proves it exactly under the statement's measure hypotheses. | Key D3. Opening, proof-route, scope and consumer passages updated. Repaired at C. |
| P3-077: generic covariance | Holds (beyond the audit) | md:205–209 call the generic covariance result unproved. `characterAverageCovariance` (HA/Distribution/CharacterAverageCovarianceProof.lean:21; in the Library since `cb6a47b2`) proves `CharacterAverageCovarianceStatement`. Neither the fiber statement nor its proof uses it. | Now cited as proved and unused. |
| **P3-078** | **Holds** | Wh/CompatibleMonomialFixedStatement.md:5 ("unproved") and 152–153 ("A proof is left to a separate task"); the Lean module docstring (Wh/CompatibleMonomialFixedStatement.lean:8–9) says "unproved proposition". `compatibleMonomialFixed` (Wh/CompatibleMonomialFixedProof.lean:413; in the Library since `910a6df8`) proves it exactly. | Key D3. Markdown and docstring cite the proof; no declaration changed. Repaired at C. |
| **P3-079** | **Holds** | Wh/GenericDualStatement.md:3 ("unproved proposition"), 68–69 and 130–131. `genericContragredient` (Wh/GenericDualProof.lean:19; in the Library since `91863c20`) proves `GenericContragredientStatement` exactly, through `gelfandKazhdanContragredient` (Smooth/Contragredient/GelfandKazhdanProof.lean:19; in the Library since `4021bb1d`) and `Whittaker.explicitSmoothDualFunctional` (`18fc6585`, published at `a6c8885e`). | Key D4. Repaired at C. |
| P3-079: inverse transpose | Holds (beyond the audit) | md:37–38 say the group-geometry work "remains responsible" for a bundled inverse-transpose homomorphism. `GeneralLinear.inverseTranspose` (Group/GL/Maps.lean:96) exists at A; the statement does not import it, and the proof identifies the two by `Units.ext`/`rfl`. | Key D4 cites it. Repaired at C. |
| **P3-080** | **Holds** | See the subrows. | Keys D5 and D6. Repaired at C. |
| P3-080 (a): statement Markdown | Holds | Wh/TwoBlockExtensionAssemblyStatement.md:32–34: "The unchanged parent target still requires an unconditional surjectivity theorem". `padicRowFourierSurjectivity` (HA/PadicRowFourierSurjectivityProof.lean:17; in the Library since `61f87bbe`) proves `PadicRowFourierSurjectivityStatement F T d` for every p-adic field, every `T : F.TopologicalData` and every `d`, including `d = 0`. | Key D5 (statement pair). Repaired at C. |
| P3-080 (b): proof Markdown | Holds | Wh/TwoBlockExtensionAssemblyProof.md:51–53: "An unconditional proof of that analytic family is still needed". Same evidence. The proof module does not import `PadicRowFourierSurjectivityProof` or `TwoBlockExtensionProof`, transitively. | Key D6. Repaired at C. |
| P3-080 (c): audit caution | Does not hold | The audit says to cite the specialization "without claiming a separately exported unconditional extension wrapper". `twoBlockWhittakerExtension` (Wh/TwoBlockExtensionProof.lean:12–16; in the Library since `e9af3dd7`) is exported. It proves `TwoBlockWhittakerExtensionStatement.{uF, uV₁, uV₂}` unconditionally, by applying the assembly theorem to that specialization. | Both corrections name it, and keep the assembly proposition and its proof conditional. |
| P3-080 (d): Lean interface | Correct; no change | `TwoBlockExtensionAssemblyStatement` remains an implication with the row-surjectivity premise; `twoBlockWhittakerExtension_of_rowFourierSurjectivity` (Wh/TwoBlockExtensionAssemblyProof.lean:92; in the Library since `8d85a8df`) proves it. | Unchanged. |
| **P3-084** | **Holds** | See the subrows. | Key E1. Repaired at C. |
| P3-084 (a): opening | Holds | CC/SemisimplicityStatement.md:5–6: "its truth has not been proved in Lean". `compactCoefficientSemisimplicity` (CC/SemisimplicityProof.lean:383; in the Library since `cddb0412`) takes exactly the statement's binders and proves `CompactCoefficientSemisimplicityStatement.{uG, uV} G μ`. | Cites it. |
| P3-084 (b): relation paragraph | Holds in part | md:163: "Both are unproved". False for semisimplicity. True for `CompactCoefficientSplittingStatement`: no Lean file other than CC/SplittingStatement.lean mentions it, and no theorem proves it. | Only the semisimplicity half is corrected; the splitting statement is still described as unproved. |
| P3-084 (c): source | Accurate; no change | md:3–4 and 144–151 quote Bernstein–Zelevinsky 1976, Theorem 2.44(b), last sentence: "In particular, any finite module is completely reducible." Checked in `bernstein-zelevinsky-1976-representations-gln`, printed p.28 = PDF page 28 (SHA256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`). | Unchanged. The correction says the Lean proof does not follow Theorem 2.42 or the projectors of Section 2.43. |
| **P3-087** | **Holds** | Geo/WeylDefinitions.md:69–71 list uniqueness of minimal representatives, Bruhat bijectivity and standardness of the intersection triples as "unproved obligations". At A: `weylMinimalRepresentativeUniqueness` (Geo/WeylUniquenessProof.lean:117; in the Library since `dd9f9be5`), `weylMinimalRepresentativeTheorem` (Geo/WeylMinimalRepresentativeProof.lean:121; in the Library since `9488f812`), `padicParabolicBruhat` (Geo/PadicParabolicBruhatProof.lean:39; in the Library since `3f303847`), `padicStandardIntersectionsTheorem` (Geo/StandardIntersectionsProof.lean:185; in the Library since `67dfb8a2`). | Key E2. Cites the four theorems with their exact scopes (injectivity for every rank, bijectivity for positive rank, the inverse-permutation convention, three equalities for `(B, C, w)` and three for `(C, B, w⁻¹)`). Says no single declaration proves `PadicGeometricWeylTheorems` and the geometric lemma is a separate target. Repaired at C. |
| **P3-088** | **Holds** | Ind/CompactScalarStatement.md:7–8 ("awaiting proof"), 87–89 and 108–114 ("A proof must still construct…"). `glParabolicCompactScalarIntegral` (Ind/CompactScalarProof.lean:35; in the Library since `b01da032`) has type exactly `GLParabolicCompactScalarIntegralStatement.{uF}`. | Key E3. Adds "Proof status": `K` and `μ` constructed before the quantifiers, full block modulus identified with the modular character, implemented route. Scalar result not extended to duality or unitarity. Repaired at C. |
| **P3-089** | **Holds** | Ind/NormalCoinvariantKernelStatement.md:107 ("Elementary proof route still to be implemented") and 130 ("part of the future proof"). `compactInductionNormalCoinvariantKernel` (Ind/NormalCoinvariantKernelProof.lean:273; in the Library since `6543e70e`) has type exactly `CompactInductionNormalCoinvariantKernel.{uG,uV}`. | Key E4. Adds "Proof status", keeping both universes and every hypothesis: basis, closedness, normality, containment, smoothness. Repaired at C. |
| **P3-090** | **Holds** | Exp/RefinedQuotientOppositeCharacterStatement.md:128 ("without proof") and 155–161 ("A future proof must establish each ingredient…", naming later work). `normalizedSecondAdjointness` (Par/SecondAdjointnessProof.lean:18; in the Library since `d8425b46`): its second component is a term of `RefinedSecondAdjointnessClause`. `refinedQuotientOppositeCharacter` (Exp/RefinedQuotientOppositeCharacterProof.lean:40; in the Library since `a8a83747`) proves the statement exactly from it. | Key E5. Cites both, keeps the proposition interface and states that no ingredient may become a hypothesis. Repaired at C. |
| **P3-091** | **Holds** | Ind/UnitaryStatement.md:151 ("Remaining proof obligations"), 166–167 and 228–234 ("these preservation proofs remain to be formalized"). `glNormalizedParabolicInductionUnitarity`, `glNormalizedProductInductionUnitarity` and `glNormalizedInductionUnitarity` (Ind/UnitaryProof.lean:19, 36, 55; in the Library since `06ce3701`) prove the three propositions exactly, at independent `uF`, `uV`. md:166–167 also call the Haar-module comparison an obligation; `glBlockModulusHaar` (Group/GL/BlockModulusHaarProof.lean:123) proves it. | Key E6. Adds "Proof status": no added admissibility, irreducibility or finite-dimensionality hypothesis; scalar input from `glParabolicCompactScalarIntegral`, tensor form from `FiniteTensor.invariantPositiveForm`. Repaired at C. |

## P3-024: diagonal units

Two independent checks found that
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
lemmas, applied to the given functional. JPSS 1983,
Section 2.1, p.386, equation (4), which the statement cites, was reread. The correction
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

The statement half is correction D5. The proof Markdown is corrected
separately, as D6, because a proof file can only be changed together with a
check of the proof against its target.

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

## Corrections and the commits where they entered the Library

Every correction is a focused change that edits only Markdown, and for D3 one
Lean docstring, of the file pairs listed in the fingerprint tables. The bases
are A or a later head whose files concerned equal A, except for corrections
already in the Library. Every correction was built with Lake when it entered
the Library.

| Key | Findings | Publication |
|---|---|---|
| D1 | P3-024 | Library `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| D2 | P3-071 | Library `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| D3 | P3-076, P3-077, P3-078 | Library `6a6c913c7339c50634dd74722034032e7a167d97` |
| D4 | P3-079 | Library `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` |
| D5 | P3-080 (a) | Library `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` |
| D6 | P3-080 (b) | Library `cde31751c7864199419ad8fae8b7f3474639ba24` |
| E1 | P3-084 | Library `cde31751c7864199419ad8fae8b7f3474639ba24` |
| E2 | P3-087 | Library `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| E3 | P3-088 | Library `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| E4 | P3-089 | Library `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| E5 | P3-090 | Library `cde31751c7864199419ad8fae8b7f3474639ba24` |
| E6 | P3-091 | Library `6a6c913c7339c50634dd74722034032e7a167d97` |
A duplicate of D1, prepared earlier, and earlier identical versions of D4,
D5, E1 and E5 did not enter the Library.

A machine build is not a check of meaning.

## Adjacent passages outside the files concerned

Two passages outside the audited files were found during verification. They
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

SHA256 of the audited pairs. The first table identifies the audited versions at
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

| Pair stem | Lean in C | Markdown in C |
|---|---|---|
| CC/SemisimplicityStatement | `8e9f7ff68c7a2d61193f5f08891fb818f4985955ee680c83cc1421b4554a0389` | `ddd9132288f52ad3186fca3d3de164bc913d56021bfd8222117d9350622c6a70` |
| Exp/RefinedQuotientOppositeCharacterStatement | `f690d650816c4b2e8fa327dc24958864b6225f6baea86aa3d6493332804af9d2` | `2d2c3df8b39c9dcdce9340e99c0acd2c2a2ccb473a43a9f53a5d7539fb2a2295` |
| Geo/WeylDefinitions | `5f71ddd64c10ba33884b1b1ab684443ec650192a73b77bd487011fdadf138d01` | `979ea6916e2fb3c7ebb427e9954719472602cb84de027ac9338b22df95e74513` |
| Ind/CompactScalarStatement | `fd4be35392bb9fe32c0af81a7474a2c7fa1187d3a8c143a8c0f3ed9c1383df60` | `b867f459d6df8e5cafbd5632b086a188373e6cc8e760d59cb3192ed0d451208c` |
| Ind/NormalCoinvariantKernelStatement | `c811cab396e838a417d485078731575cde5eb9654aa6b06469718132974980ad` | `fc92226d5279df3dc2405216643ab783b1e3943d9f805ab21c644ba0a7fa321c` |
| Ind/UnitaryStatement | `af0bb472c57e9399f0554a1217d79459724f334854ad2c46330cb74275643ec4` | `c0d63ebc54631077ddc54d850cc34898e45cfae877cd1d9994682749859b92d2` |
| Par/FineAmbientQuotientTransportStatement | `6828496afdedad28a2cdd029fbc8311d1319be224cc8c9de18f628f2c66482df` | `7e83aec5d155264a99fde67c34e5f478f7c69a286ab327130308614b5bcdd749` |
| Wh/BruhatCompatibleSupportStatement | `b383eace4776390224d0ed609ab5bcf59d824efadcec0b1b21849bd7f8996200` | `f71a341ba7475dd3c62c5da930fb100ff2f8d6fa5e8f72412125fca850c3de02` |
| Wh/BruhatFiberCharacterCovarianceStatement | `a07533bd75d944b0fd8e617cdcea65052a3e63cc4882843a420780d833203762` | `2569f067e1558faf79382e05f1fee498d9d1b58b79fc4fb32609025bd5ebc73e` |
| Wh/CharacterChange | `0156e7b1f733656f8c93596ce76c6ff7bcde7f2cd1f18330e41d4a041298abaa` | `cf7605ca7cc468added2f943aabb0565351f3434949491f6320fb3b2cefb2bc1` |
| Wh/CompatibleMonomialFixedStatement | `7c3434178b17b5eacc7811a7efa09652122f84fb837099a119c81e1e59e40f1f` | `9f1af9115219bd98c21dbd13e412c6dd9eee916bf41e11bfb4afadd7eaf04335` |
| Wh/GenericDualStatement | `ddcb075d9e8307c215df6b6a6c202cee748f6a883bc4a5fcc1e870dcd063b64b` | `f8ad321e73452eedee235744bf38f772d51001055ef1ce825757b12b738f861f` |
| Wh/TwoBlockExtensionAssemblyProof | `c3ca43282daa8877b678472e9041a8d14bc847413ffd4fd776a4df7afb7ff088` | `a064068aa127cbc838d343d3e6911340adad9092adcafcb906d18b5378fc18af` |
| Wh/TwoBlockExtensionAssemblyStatement | `53cac3707d8c6f359f7cce518437e548827f80382999f744a8cac4c0770c1ff5` | `d9ad484d3dec4c313ab1478f29214418480fd5642c4823dad67c32b25ebf741b` |

The audit report has SHA256
`d9a25f35dc2d7bef0351ba0891db168b0c3cc797a281d0a9944e930fe43d5eeb`.

# External Library audit: Whittaker hypotheses and Rankin–Selberg status

Worker 90, with verification contributions from Workers 113, 69, 331 and 332.
This note records the twenty findings assigned by task
`da2fed2d-b6d5-4c04-9463-e8cd13a0edea`, revision 2. The source reports are the
registered `external-library-audits-2026-10-22`, ISSUES-1 and ISSUES-2. Their
allegations were checked against complete Lean declarations, paired Markdown,
original sources and authoritative review/publication records. Parent verification
here is separate from the independent review of each corrective candidate.

## Snapshots and verdict convention

All twenty findings **hold at the pre-correction Library commits actually
checked**. They concern documentation; the checked Lean declarations already
carry the necessary hypotheses or constructions. No Lean statement or proof was
changed for these corrections. I002 was checked at
`f1b212cc117b9c34dced95c0ac88e6328827334d` and rechecked at
`aee7fdb7f6d4283cce4db9035fd9478c923d4926`; the other nineteen were checked at
`b263cfa454b11d485198ae46d8290f32435e48c6` (B below).
The latest comparison in this edition is Library
`5150bf6c9c8e6dd90b1329f6188324b9fb00a0da` (C below).
The hash appendix identifies both the defective prose and the checked current
files. A historical **holds** verdict does not claim that an already corrected
sentence is still defective in C.
All twenty findings have now been corrected by seven independently accepted
and published candidates. Every corrected pair matches its frozen candidate,
its publication and C.

The report mirror commits were historical evidence only: `85a0aec…` corresponds
to Library `c5a40b0f54880b1825ea05214c2b066f68bfc156`, and `0972f45…` to
`f9c1742752d97c488fc1a835070bf50b534f4427`, as specified by the operator.
All locations below are Library-relative; `RS`, `W`, `Cdr` and `Sm` abbreviate
`Langlands/Representation/RankinSelberg`, `Whittaker`, `Conductor` and `Smooth`
under `Langlands/Representation/`. Markdown line ranges in the verdict table
refer to the defective version. Lean locations remain unchanged in C.

## Per-finding ledger

Each row's verdict is **holds** at its checked pre-correction commit. The
correction keys refer to the exact candidates and release records below.

| Finding | Verdict | Defective Markdown and verified Lean evidence | Decision and retained boundary |
|---|---|---|---|
| I002 | Holds | W/Spherical.md opening, arbitrary-decomposition formula and generality paragraph; W/Spherical.lean:41–43,61–157,249–278. | S: require `IsIntegrallyTrivial` for the spherical properties; retain the arbitrary-character choice-defined function. Corrected in C. |
| I004 | Holds | RS/TemperedLFactorStatement.md:138–142; `SupercuspidalEqualRankLFactorStatement`, Lean:79–101, and the normalized-generator chain below. | T: identify the product as denominator P, with L(s)=1/P(q^(-s)). No new formula proof. Corrected in C. |
| I007 | Holds | RS/AnalyticStatement.md convergence description; RS/QuotientIntegrals.lean:465–483. | M: specify joint integrability on quotient × rectangular matrices under μ.prod ν; distinguish the iterated integral. Corrected in C. |
| I037 | Holds | Cdr/Definitions.md:61–69; Cdr/Essential.lean:95–103,145–181. | C1: cite the existing relation and selector conditional on unique existence. Essential-vector existence and uniqueness remain open. Corrected in C. |
| I038 | Holds | Cdr/NewvectorStatement.md:42–48; Cdr/Congruence.lean:53–89,144–227,234–316. | C2: cite the existing subgroup, matrix and compact-open constructions. Inline-predicate identification and the minimal-newvector theorem remain separate. Corrected in C. |
| I039 | Holds | Cdr/SphericalTests.md:102–110; RS/QuotientIntegrals.lean:198–247 and Cdr/Essential.lean:95–103. | C1: cite the existing corank-one integral and identity relation. Its absence from SphericalTests itself is correctly described; convergence and source-identification proofs remain open. Corrected in C. |
| I040 | Holds | RS/AnalyticStatement.md status; RS/UnipotentUnimodularity.lean:151–171, UnipotentQuotient.lean:100–163 and QuotientHaarExistence.lean:21–40. | M: acknowledge all-rank Haar right-invariance and compatible quotient measures, retaining analytic goals. Corrected in C. |
| I041 | Holds | RS/GenericLocalConverseStatement.md:65–74; W/CharacterChange.lean:193–240. | F: cite the functional equivalence at scale −1. Supercuspidal genericity and analytic/converse goals remain open. Corrected in C. |
| I042 | Holds | RS/HighlyRamifiedStatement.md:119–125; the same character-change equivalence. | F: acknowledge inverse-character transport for either representation and either rank ordering. Corrected in C. |
| I043 | Holds | RS/HighlyRamifiedStatement.md:137–146; RS/UnipotentQuotient.lean:153–163. | F: state exact uniqueness for fixed ambient/subgroup Haar normalizations; scalar-change arguments remain separate. Corrected in C. |
| I044 | Holds | RS/HighlyRamifiedStatement.md:154–165; Sm/SmallRealizationProof.lean:150–159 and its complete target. | F: acknowledge countable-basis/small-carrier realization for irreducible smooth representations in independent universes. Corrected in C. |
| I045 | Holds | RS/LocalConverseStatement.md:106–115; RS/QuotientHaarExistence.lean:21–40. | F: remove proved measure existence from the blanket unproved list; retain analytic and local-converse goals. Corrected in C. |
| I046 | Holds | RS/LocalFactor.md all-rank measure status; RS/UnipotentQuotient.lean:100–163. | M: remove the rank-one-only limitation. The quotient is N\GL, with right translation. Corrected in C. |
| I047 | Holds | RS/MultiplicativityStatement.md:119–138; W/CharacterChange.lean:193–240 and RS/QuotientHaarExistence.lean:21–40. | F: acknowledge dimension transport and measures; retain induction preservation and multiplicativity. Corrected in C. |
| I048 | Holds | RS/PadicPairFactors.md:93–99; W/CharacterChange.lean:193–215. | F: acknowledge transport of a supplied nonzero functional, without asserting its existence or an analytic functional equation. Corrected in C. |
| I049 | Holds | RS/PadicPairFactors.md:100–108; RS/UnipotentQuotient.lean:153–163. | F: state exact fixed-normalization uniqueness. The polynomial-uniqueness proof itself needs existence, not measure uniqueness. Corrected in C. |
| I051 | Holds | RS/TemperedLFactorStatement.md prerequisite status; RS/QuotientHaarExistence.lean:21–40 and PadicPairFactors.lean:103–105. | T: acknowledge the measure conjunct; generator, genericity and Section 8 formula obligations remain open. Corrected in C. |
| I052 | Holds | RS/UnimodularityStatement.md status; the all-rank invariance and quotient constructions below. | M: replace future-work language for the proved prerequisites. Corrected in C. |
| I061 | Holds | W/PrerequisitesStatement.md:31–38; W/GeneralLinear.lean:130–180, CharacterChange.lean:193–240, and the subsequently published PrerequisiteInterfaces.lean:15–151. | C3: cite bundled functionals, model equivalence, character transport and the now-published raw AddChar adapters supplying clauses 2–3; retain multiplicity one and the full proposition proof. Corrected in C. |
| ISSUES-1 DOC-04 | Holds | Overlaps I040 and I052, with the same complete declarations and release evidence. | M: the same correction covers this separately recorded finding; no duplicate edit. Corrected in C. |

The source reports themselves distinguish the valid local statements and open
theorems listed in these rows. Those qualifications are retained rather than
treating the findings as allegations that the whole theory is already proved.

## Spherical hypothesis: I002

`Langlands.GeneralLinear.Iwasawa.IsIntegrallyTrivial v θ` means θ(u)=1 for every
upper-unipotent u lying in the integral subgroup. The raw `cellFunction` and
`Langlands.GeneralLinear.Spherical.sphericalWhittaker` use chosen Iwasawa data for
arbitrary θ. The arbitrary-decomposition formula, covariance, right integral
invariance, normalized value and torus formula require the integral-triviality
hypothesis in their Lean declarations. Non-antitone vanishing is unconditional.
The corrected prose states this distinction in its opening, formula and scope
paragraphs, while retaining the previously qualified theorem list.

The need for the hypothesis can be seen without a new formal theorem: for an
integral unipotent u, left covariance and W(1)=1 give W(u)=θ(u), while right
integral invariance gives W(u)=1. Thus their simultaneous assertion forces
θ(u)=1. This does not say that every individual property fails for every other
character. The full Lean setting has independent field and value-group
universes, a valuation and a uniformizing unit; the raw construction does not
assume a local-field topology. The standard/inverse-standard adapters require
ψ to be trivial on the integer ring.

The registered Shintani 1976 original, printed p.180, explicitly chooses ψ
trivial on the integers and nontrivial on the inverse-uniformizer ideal.
Miyauchi 2014, §2 pp.18–19 and Theorem 4.1/Remark 4.3 pp.21–22, uses conductor O.
These originals support the qualification. The separate Hecke/Satake
identification is not supplied by this documentation correction.

## Measures and convergence: I007, I040, I043, I045–I047, I049, I051–I052, DOC-04

`Langlands.RankinSelberg.generalLinearHaarRightInvariant` proves its named
all-rank target. `unipotentHaar_rightInvariant` and its instance prove the
corresponding unipotent assertion. The field is an arbitrary nonarchimedean
local field in universe uF, the rank is n+1 for every n, and the relevant
measurable group structures are Borel. These results are not rank-one instances.

`unipotentQuotientHaar`, `unipotentQuotientHaar_isCompatible` and
`unipotent_compatibleMeasureExists` supply the actual regular measure on the
left quotient N\GL and all fields of its compatibility predicate. Ambient,
subgroup and quotient measurable structures are Borel. The ambient and
unipotent Haar measures have the fixed integral-subgroup normalizations.
`unipotentQuotientHaar_unique` concludes literal equality of any compatible
measure with that constructed measure for those fixed Haar inputs. It is not
merely equality up to scalar, nor a theorem about independently rescaled Haar
inputs. The I046 report's GL/N notation is not adopted.

The exact theorem `quotientHaarExistence` quantifies over every prime p,
`F : PadicField.{uF} p`, supplied `T : F.TopologicalData`, and n. It installs
T's topology, valuation and local-field certificate, supplies the Borel
structures, and proves `QuotientHaarExistenceStatement F T n`. TopologicalData
already contains its compatibility certificates. No quotient measure or
right-invariance assumption is supplied to the theorem. Taking canonical T
provides precisely the measure conjunct in `IsPadicPairLPolynomial`.

`UnequalRankConverges` in QuotientIntegrals:465–473 is `Integrable` on
`LeftUnipotentQuotient n F × RectangularSpace j n F` with `μ.prod ν`.
`unequalRankIntegral`:476–483 separately integrates the rectangular variable
first and the quotient variable second. No Fubini theorem for arbitrary measures
follows merely from this definition. AnalyticStatement uses the rectangular
measure constructed from its supplied additive Haar measure. The original JPSS
§2.4(3), p.387, has both variables; Theorem 2.7(i), p.390, supplies the analytic
convergence assertion, which is still a proof obligation in the checked targets.

Folland, second edition, pp.62–63, Proposition 2.50, Theorem 2.51 and (2.52),
were read for quotient averaging, modular compatibility and normalization.
Their source assertions are distinguished from the actual Lean constructions
and their accepted receipts. Convergence, rational continuation, normalized
factor existence and functional equations are not established by measure
existence. In particular, the universal generator relation in
`IsPadicPairLPolynomial` remains additional data.

## Functional transport and carrier size: I041–I044, I047–I049, I061

`Langlands.Whittaker.characterChangeFunctionalEquiv` is a linear equivalence
between `glFunctionals ψ n π` and `glFunctionals (ψ.scale a) n π` for a unit a.
It precomposes by the representation of a diagonal element and has the explicit
inverse using a⁻¹. Setting a=−1 and using the standard-character identity gives
the inverse-character space. Nonvanishing and dimension are preserved. The
field and representation carrier have independent universes; the functional
section assumes a topological field with `IsTopologicalRing`, but no
irreducibility, admissibility, genericity or finite dimension. A supplied linear
equivalence of the functional space with ℂ can therefore be transported, as
needed by `IsOfWhittakerType`. None is created from no input.

JPSS §2.1, printed p.385, explicitly describes diagonal conjugation and permits
the inverse additive character. Page 386 gives the coefficient-image functions
W(g)=ℓ(π(g)v), their covariance and right-translation action. GeneralLinear's
bundled spaces specialize the existing algebraic construction. `glModelEquiv`
requires irreducibility and a specified nonzero functional; `glModel_isSmooth`
requires smoothness. Neither supplies multiplicity one.

The subsequently published `Whittaker/PrerequisiteInterfaces` module supplies
the raw adapters. It was absent at B and published at
`a6c8885e0e4bfcf4ee6d5a4b9a84a6d195085302`, before the I061 correction's
first submitted base. `UnitaryAdditiveCharacter.ofComplex`:15–29 packages the
target's continuous, nontrivial, unit-norm complex character and recovers its
complex projection definitionally. `EntrywiseEquivariant`:44–48 repeats the
target equation; `standardCharacter_eq_product` and
`mem_glFunctionals_iff_entrywise`:59–78 identify the sum/product characters
and exact lower-zero/unit-diagonal conditions. The raw lemmas
`raw_exists_inverse_iff`:136–141 and `raw_coefficient_injective`:145–151
supply clauses 2 and 3 of `WhittakerPrerequisitesStatement`:44–47.
They retain independent field/carrier universes and work on the same
representation; the coefficient lemma requires irreducibility and a specified
nonzero equivariant functional, without admissibility. The published adapters
do not prove multiplicity one or the full three-clause proposition.

`Langlands.padicIrreducibleSmoothSmallRealization` proves
`PadicIrreducibleSmoothSmallRealizationStatement.{uF,uW,uV}` with independent
field, source-carrier and destination-carrier universes, including destination
universe zero. It ranges over primes, p-adic fields, supplied topological data
and ranks (including zero). From irreducibility the orbit of a nonzero vector
spans; smoothness and a countable dense subset make the orbit countable. A
basis chosen within it is countable, and transport to `Shrink.{uV} b →₀ ℂ`
gives the smaller realization. The complex vector space need not be a countable
set. Second countability is derived for T's topology; admissibility is not an
extra premise. When present, the accepted admissibility predicate includes
smoothness. This is internal derived mathematics, not an attributed JPSS proof.

The irreducible-only small-realization theorem is not applied to arbitrary
Whittaker-type induced representations. PadicPairFactors' three `congr_equiv`
lemmas retain independent carrier universes and both rank orderings. Relations
requiring common factor witnesses do not become equalities of nonexistent
factors. Its L-polynomial uniqueness proof chooses a compatible measure and
uses the two universal generator relations; exact measure uniqueness is
available but not needed in that particular argument.

## Denominator polynomial: I004 and I051

`Langlands.RankinSelberg.SupercuspidalEqualRankLFactorStatement` is a Prop-valued
goal over all primes and p-adic fields, canonical topological data, a unitary
character and self-dual Haar measure, with independent representation carriers.
For irreducible supercuspidal π and irreducible Whittaker-type σ of the same
positive rank, its conclusion uses
`IsPadicPairLPolynomial … (∏ a ∈ A, (1 - C a * X))`. The finite set A retains
the stated twist/contragredient membership condition.

Following `IsPadicPairLPolynomial` through `IsPairLPolynomial`
(PairLFactor:212–221), `IsEqualRankLPolynomial` (LocalFactor:224–230), and
`IsNormalizedGenerator` (RationalZeta:139–142), P has constant coefficient one
and its reciprocal generates the Laurent span. Thus P(X)=∏(1−aX), whereas
L(s,π×σ)=∏(1−a q^(-s))⁻¹. The original JPSS §2.7(ii), p.391, and §8.1(ii),
p.443, were read directly and have this reciprocal convention. The existing
contragredient convention is preserved; the correction does not change or prove
the Section 8 target.

The nearby prose now describes the actual all-model normalized-generator
relation. LocalFactor ranges over coefficient models and does not insert a
separate existential nonzero-functional clause. This literal observation
neither proves genericity nor denies consequences of a nonzero generator.
The already proved measure conjunct is separated from the remaining analytic
and genericity obligations.

## Conductor constructions: I037–I039

`SatisfiesEssentialIdentity` already requires right-half-plane convergence and
rational continuation of the corank-one integral for every parameter tuple.
`IsEssentialVector` uses a genuine `IsCharacterLPolynomial` for π against the
trivial rank-one representation, the identity relation and the restriction
invariance condition. It is defined for arbitrary π and ℓ; genericity and
nonzero ℓ are not hidden construction hypotheses. `essentialVector` takes a
proof of unique existence and provides its specification and uniqueness
characterization. It does not supply that proof or a default essential vector.

The corank-one scalar is
W(diag(g,1)) W′(g) |det g|^(s−1/2). Standard and inverse characters cancel under
left unipotents, and determinant one permits descent to the actual left
quotient. The measurable space and measure are explicit.
`CorankOneConverges` is integrability for that measure; the total Bochner
integral alone does not assert convergence. SphericalTests itself contains no
integral construction, but the Library already has `corankOneIntegral` and
Essential already uses it. This resolves the library-wide future-work claim
without changing the correct local-module description.

Congruence constructs the integral reduction stabilizer `integralCongruence`,
its field image `congruenceSubgroup`, `levelSubgroup`, level zero and
antitonicity, and the integral-matrix/inverse-matrix characterization. At
positive levels it proves the block-unit conditions. Algebraic constructions
allow arbitrary ideals. Openness uses open integer subring/ideal hypotheses;
compactness uses the Hausdorff and compact integer-ring hypotheses. The local
field specialization packages these as compact open level subgroups.
NewvectorStatement still uses its expanded inline predicate and T.Integers.
Identification with the packaged construction and the generic minimal-newvector
theorem remain separate proof obligations.

The original JPSS 1981, pp.208 and 211, contains the essential-vector and level
claims, and p.214 warns about nongeneric representations. Jacquet's 2012
correction, pp.515–517 and p.523 Remark 1, explicitly corrects the earlier
existence proof. Its Theorem 1 has conductor O, normalized Haar data, quotient
rank r−1, exponent s−1/2 and reciprocal product. Uniqueness adds invariance on
diag(GL_(r−1)(O),1). The Lean essential-vector constructions cover rank at
least two. EssentialStatement's four declarations are Prop-valued targets,
not proofs: its conductor exponent target also includes rank one. The
Godement–Jacquet/JPSS factor comparison and spherical/Hecke identification
remain explicitly disclosed source-identification obligations.

## Verified companion publications

These records were checked in authoritative artifact records, independent
reviews and publication receipts, then compared with the actual current paired
files. A name, compilation success or neighboring prose was not used as proof
of acceptance. The proof-policy entries include accepted Lake-build and
exact-target checks. The table records review task IDs for unambiguous lookup.

| Module / unit | Artifact | Policy | Accepted machine receipt | Independent approving review task | Publication commit |
|---|---|---|---|---|---|
| RS/GeneralLinearUnimodularity | `0a2f2e5a-3d04-4174-a4dd-6d9c2ed97cd3` | `lean.proof@1` | `6124cbc7-2c6d-48f3-baf4-a88a73862633` | `6845ba2f-d270-46f5-961e-f84d4a31e398` | `7db0c477a21f8471b1e5cff5f20d8ecb3dd2285b` |
| RS/UnipotentUnimodularity | `e5699c5d-4972-4e3d-b956-8b69d79d36d6` | `lean.proof@1` | `06e14fcb-21aa-44e3-a4a0-52bfd1a05028` | `f4cf1613-64d7-406d-ab18-d099f4620b40` | `7db0c477a21f8471b1e5cff5f20d8ecb3dd2285b` |
| RS/UnipotentQuotient | `eb738941-1de1-4153-bc1d-5bc7a0833dbd` | `lean.definition@1` | `0ddd80de-5108-4207-910b-98a519121b77` | `57d6426e-673e-469f-b46f-71da94069e4d` | `3afe6f3ba5efc4d00cccb18dba321ef341bbaf68` |
| RS/QuotientHaarExistence | `7242bb53-8416-495f-ae65-a8b1ca741775` | `lean.proof@1` | `75a2e2f2-254e-4bdf-ac84-1f32121d27a6` | `126b1e95-48f6-4539-ac3a-751fe7adc8b7` | `4897b8b0eeea4fd4761194eb8fe4c2103d02aae4` |
| Langlands/Representation/Parabolic/UnipotentFiniteContainment; RS/UnipotentUnimodularity (helper promotion) | `bf7f18d2-c1ab-499e-941f-91c304ecdbbf` | `lean.proof@1` | `b352de67-f94d-4c7b-a945-ee6f3d1801bf` | `78bed534-975c-4347-b2e9-06478a895e7d` | `01a58491bc71539f1ecd3d5f0eec6ab8eae20fed` |
| W/CharacterChange | `ee91c9f2-b871-440f-8315-47b12b793e9d` | `lean.definition@1` | `2272e103-9d56-4c16-ad56-d8e9c9db1d32` | `bacddcc8-55ce-460b-80d9-f39d7e50d6c4` | `ef274d37c255e4b25a990dd377d10e2da436807d` |
| Sm/SmallRealizationProof | `b9fc82a3-c94e-4f17-9c0f-69a17a8effbb` | `lean.proof@1` | `74e599f0-4d86-47ba-81d1-a7eb6e4471e7` | `7d7085b4-67f1-479b-8820-61bba74dea24` | `f9c1742752d97c488fc1a835070bf50b534f4427` |
| Cdr/Essential | `4f62224f-5464-4d85-a5d8-f7fdf8e423c4` | `lean.definition@1` | `7be70723-4e51-4bee-8fe7-3db52292c70c` | `934112f8-8070-4240-88d1-b5c5291841d4` | `a175d25f6a5a9e22525012e3cae66e9f8dfacba9` |
| RS/QuotientIntegrals; W/GeneralLinear | `db295cbc-b379-49de-99dd-64a4c5831f74` | `lean.definition@1` | `792638ab-4eb0-42f0-8b95-dacfdfe7e8ee` | `d1068f32-c647-41db-8070-32f74fe488b0` | `22b4f024e0d4218752e970d09329d1799f6d81d1` |
| Cdr/SphericalTests | `236f4cab-fbda-4987-b35d-d6a6ad942933` | `lean.definition@1` | `c0dc0317-1a78-4b6e-a26a-79e8445b5d1a` | `2f4e5241-f565-4b36-af2f-e77dd966a933` | `4fbc1953d45ea9aa3fa4b80478542c845102a4e5` |
| Cdr/EssentialStatement | `9905996f-a6cd-4591-9aa4-0e1c58407ca1` | `lean.statement@1` | `20fe09dd-0d8d-4b85-9b3b-9530f3060d43` | `76e1aa1b-0a75-4dd6-89b4-0b32e7b785c9` | `056b7c747e32f712be4ac7fd004fd0af4845c968` |
| W/PrerequisiteInterfaces | `674a0ce6-5c53-4d57-add7-d3c8c64b97bb` | `lean.definition@1` | `a9834a41-14e0-4242-842c-1837206eaefb` | `21c73ddc-e606-48af-b456-65be5878db52` | `a6c8885e0e4bfcf4ee6d5a4b9a84a6d195085302` |

GeneralLinear is explicitly among the six integrated repository paths of
`db295cbc-b379-49de-99dd-64a4c5831f74`; it is not merely an incidental snapshot
dependency. Reviewer 150's report expressly checks its characters, functionals,
coefficient model and conditional equivalence. The later
`bf7f18d2-c1ab-499e-941f-91c304ecdbbf` publication, in its changes to
UnipotentUnimodularity, only promotes the shared `common_integer_denominator`
helper and updates its prose; the main invariance proof is unchanged.
That pair's reviewed public bytes match
C. Migrated historical acceptance records for Congruence, Definitions,
NewvectorStatement and PrerequisitesStatement were not located. Their current
Library contents are verified here; no unavailable historical review is
invented. The corrections have their own fresh review requirements.

## Correction candidates and release evidence

| Key | Findings | Candidate | Machine validation receipt | Independent review task and outcome | Publication |
|---|---|---|---|---|---|
| S | I002 | `2d8dd251-b92e-4e76-9a90-5b5a92f22b30` | `51aafc3c-3c5d-4ea5-a272-d7fc2759914a` | `0ea19339-4c2b-484a-b7cd-6ed7d19a58b3` (approve, no qualifications) | `2173e15e1a7e4f96682e6274d63c4f98ccce2c73`; integration `c6a3aeef6b9f4fb1858af69a99021c80` |
| M | I007, I040, I046, I052, DOC-04 | `8c9fea15-98cd-47ce-924d-2dca5da99df5` | `35533707-3ed0-40ac-a5ec-98d2b8330bc2` | `4045fcc2-71cc-4002-ac78-46a5cd0c48a6` (approve, no qualifications) | `a6c8885e0e4bfcf4ee6d5a4b9a84a6d195085302`; integration `6b2eb2f4d72a47a9b08adb23a86233b4` |
| F | I041–I045, I047–I049 | `d9bb7253-9608-478b-9ffe-853a14487d54` | `3111193c-311d-47e1-a365-4e50d6fb7b45` | `9b7a1148-9f39-45ba-a92b-97906d726a89` (approve, no qualifications) | `a6c8885e0e4bfcf4ee6d5a4b9a84a6d195085302`; integration `31322885d3174fd485911858bc46ff34` |
| T | I004, I051 | `9a7d88ee-1113-4ce8-86b9-43512c74991c` | `5310c5d0-a8e6-4f83-8c42-3d2bb8038bf6` | `5ed78576-2137-4695-a070-7a3982b037c8` (approve, no qualifications) | `a6c8885e0e4bfcf4ee6d5a4b9a84a6d195085302`; integration `5e354dc93f2c46b69f7d78e796f3c506` |
| C1 | I037, I039 | `a347bef5-d504-4d2e-9d60-ddadd24c4646` | `18b6d45e-b1ed-4950-958d-93566b9ca11a` | `1304ede0-181c-4b9e-9ed1-0eed03fc8985` (approve, no qualifications) | `886e27567a757917705b7adef45a2c2621bf4bf7`; integration `b8219fb3b4cc4987903adf81a9f55d1d` |
| C2 | I038 | `deb217ea-788e-41f4-8eef-ea79aa488e5f` | `8c416b25-3f21-40d7-b930-543035acf798` | `0126681f-b389-4834-8169-953cd86db6fb` (approve, no qualifications) | `4ccd65d85917da26d0a67b9c48a37859533fffa9`; integration `b50b419465984dbe845404f513bcb82a` |
| C3 | I061 | `bd81d0bb-3437-4b5b-a300-9180154a0c5e` | `40ef7261-869b-451d-bab9-26fd9a889e44` | `bad6e032-8e98-4d75-b5b3-2e47de87c3c2` (approve, no qualifications) | `451f42a052568843a4d727659c3d0a6c66d38ca6`; integration `4a1bf99cba2a4df396a22b86c9e70c06` |

All corrected mathematical pairs use the applicable mathematical-artifact
policy; no paired Markdown is submitted as a wiki note. The public note itself
requires separate independent review and publication. Machine acceptance is
not semantic acceptance. For S, the integrated Lake build report is
`c6bebcd79a7346067a745238bd41a31696d9ecaa3181f5275ee75245a3d98814`.
For M, F and T, the fresh integrated build report is
`1eacca0dfb1f01964096b358388b2a72b29cbd1e95b49d56a2cd015a74de1025`;
their independently approved frozen corrected Markdown matches publication
`a6c8885e0e4bfcf4ee6d5a4b9a84a6d195085302` and C exactly.
For C1, the fresh integrated build report is
`7c8040a688f82f2181e515b54d2dd78b67e5b38423305685e22d2174a8b7a192`;
both corrected pairs match its publication
`886e27567a757917705b7adef45a2c2621bf4bf7` and C.
For C2, the fresh integrated build report is
`af57d855ee4191b30dcca6fd2ca8ef23b75e4f0d2d386bed55d97459b6bd5402`;
both files match its publication
`4ccd65d85917da26d0a67b9c48a37859533fffa9` and C.
For C3, the fresh integrated build report is
`ea9c0753ebe3d8382c21582d8e2efb7ae912dc1f1ff955e4ebe65a576547fc5a`;
both files match its publication
`451f42a052568843a4d727659c3d0a6c66d38ca6` and C.

The first I061 candidate `4209a7f0-e625-4f9e-b825-57ea25f00552` passed
machine validation `88e74943-de8e-46b4-863d-a5d447a55bae` but received
**request changes** from Reviewer 1463 in review
`3d136d13-fe97-4174-b0c3-3f403d67bb08`, receipt
`d4d92620-0e7e-4ef5-9f0f-977836750bb4`. Its new outstanding-adapter claim
missed the intervening PrerequisiteInterfaces publication. Parent verification
confirmed that module's complete declarations, independent approval and exact
published hashes. The rejected candidate is not counted as a correction or
publication. Its explicit replacement C3 is
`bd81d0bb-3437-4b5b-a300-9180154a0c5e`. Its complete frozen pair and metadata
were rechecked against the accepted adapter module. Reviewer 1509 approved
the replacement without qualifications in review
`bad6e032-8e98-4d75-b5b3-2e47de87c3c2`, attempt
`f970ad91-494a-4d9e-8c27-53577f4906f9`. Its independent acceptance and
publication are now verified in the C3 release above.

Workers 113, 69, 331 and 332 supplied the focused verification and correction
reports used here; Worker 90 checked their relevant declarations, sources,
receipts and frozen changes. The underlying module authors are credited in the
correction candidates (including Workers 11, 43 and 113 as applicable).
PairEpsilonNormalizationStatement, owned by another audit group, is unchanged.
No claim is made that the full LLC, JPSS analytic theory, newvector theorem or
multiplicity-one theorem is complete.

## Original-source fingerprints

All sources below are registered and readable in the shared literature
collection; the registry pointers locate their exact originals. No source
erratum note was found in the checked project/Library errata locations; the
Jacquet correction itself was read explicitly. Page numbers are printed pages.

| Registered source | Reading relevant to this audit | SHA256 |
|---|---|---|
| `shintani-1976-class-one-whittaker` | p.180, character normalization and spherical properties | `08c9229a7c54f07b4dffee55f3ab6bbb4fcb03e9c7eb0668451eabb3b1b0ab94` |
| `miyauchi-2014-newform-whittaker-gln` | §2 pp.18–19, Theorem 4.1 and Remark 4.3 pp.21–22 | `52d52dcca7b916e06b79a11f362a709f6e908bb25870d75bbf8083bf24c1cd68` |
| `macdonald-1995-symmetric-functions` | pp.21,40–41, retained symmetric-function context | `64e242b84d1f3b7864ed28f89a9b331269a28c1ce2a32ce03b4ee692f5974ea7` |
| `jpss-1983-rankin-selberg` | pp.385–387,390–391,443, functionals, integrals, convergence and reciprocal polynomial | `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245` |
| `folland-2015-abstract-harmonic-analysis-second` | second edition, pp.62–63, Proposition 2.50, Theorem 2.51 and (2.52) | `c82467bfa77428c32d3e1a5d1cbdc11129511e0c61da2f9d8fbc717776b9e542` |
| `jpss-1981-conductor` | pp.208,211,214, essential vector, level and genericity scope | `986b06d6c16221fd55f04480604a1b17bf11004a704ab16b78acdd131ae6d49d` |
| `jacquet-2012-conductor-correction` | pp.515–517 and p.523 Remark 1, corrected theorem and normalizations | `98f02c2aef04bff162c1ceb0a42dd122da746d1304a90d82366a848f22713adf` |

## Checked file fingerprints

Every hash below is SHA256. C identifies the exact current comparison snapshot above; B and S-base identify the two defective-prose snapshots. S-base is `aee7fdb7f6d4283cce4db9035fd9478c923d4926`. All fourteen owned Lean files are byte-identical between their checked baseline and C. For every published correction, both current files also match its frozen candidate.

### Current correction locations

These are the changed Markdown lines in C, obtained by comparing complete files with their checked baselines. A range can include unchanged context within a replacement paragraph.

| Key | Markdown file | Changed lines in C |
|---|---|---|
| S | W/Spherical.md | 3–6, 25–28, 97–100, 142–149, 161–167, 179–181, 211–218 |
| M | RS/AnalyticStatement.md | 11–15, 111–120, 125–139, 156–163 |
| M | RS/LocalFactor.md | 76–89 |
| M | RS/UnimodularityStatement.md | 35–36, 44–63 |
| F | RS/GenericLocalConverseStatement.md | 71–75, 84–90, 104–112 |
| F | RS/HighlyRamifiedStatement.md | 122–128, 138–142, 147–152, 166–174, 177–177 |
| F | RS/LocalConverseStatement.md | 109–115, 121–128 |
| F | RS/MultiplicativityStatement.md | 127–131, 136–142 |
| F | RS/PadicPairFactors.md | 38–43, 100–107, 111–120 |
| T | RS/TemperedLFactorStatement.md | 3–4, 141–144, 148–153, 190–205 |
| C1 | Cdr/Definitions.md | 66–83 |
| C1 | Cdr/SphericalTests.md | 102–126 |
| C2 | Cdr/NewvectorStatement.md | 42–54 |
| C3 | W/PrerequisitesStatement.md | 4–5, 34–51, 103–107 |

### Owned pairs in C

| Pair stem | Lean SHA256 | Markdown SHA256 |
|---|---|---|
| W/Spherical | `8ac09510e029b9b2c6e7d93979bf99a37cd2bde53503a22446081eb1fad07fca` | `a227b93122d9b3867b17502058a428d8f937f113a94a4bdb3dc3234e9103821f` |
| RS/AnalyticStatement | `083bd22291a622e1ac8b4f5bbe7c5a13ff5949d0ebfcfc4d180924e2517ec5de` | `74cbeadddca7b4d5ef27d97d98f54913fe78124fe5acc0b20a00686145c5d254` |
| RS/LocalFactor | `af7cf52dcf557bfffba6dcd468e1f4b2c82dd5632d8c0075b265a5fe2a587083` | `4ee2f81dd1816154d15cd3a345b460f61e29ea984341a4952fe2a3b569d2eeb2` |
| RS/UnimodularityStatement | `9bb58fb2a30b86a0dd103569acdace040305196d920941386d7ffb0f3399111b` | `eda1bf92c56147c95d5a5eab81607c2850288e1ab8289a8a3c7ce83ddf7e6cfa` |
| RS/GenericLocalConverseStatement | `869ea75e58bcf9e69524db7441712d02259e5923dbc40c74d066ffb9a787be3a` | `715c608d8da06dfafb993a7bcb5dd052202ceed997463cd291e57be6941528e5` |
| RS/HighlyRamifiedStatement | `04eefcd86bb2068f6962c702804454f20fb13665b2aa2a727fd46c806299ab5b` | `4cafb5c2854ace3a7965f881881a6e04039a0495fef23b87dda43a29164e61fb` |
| RS/LocalConverseStatement | `c8f1100f4b74ad0629df93d4f791225cf5953c390e797725642ec7cf195441ef` | `5a50f7adeaa109f41fd51899b5b5672047d6f47e0fc396d80e202e2959c36df6` |
| RS/MultiplicativityStatement | `c4c1fb2ecaf05809ef0ff815178b3646d539abddec19facf510a18ceefffa1d5` | `f7b718fd94d008bcc57942ae58da88ef9f957b62aef82ddaca1f614980193e65` |
| RS/PadicPairFactors | `182e30861f1d14c5bba0754bef6a1b4bcf57b22e04db516cb5bb2e20ac9e96c1` | `f4e725037a4a0580c02813c742d4c2b851d7d01cb39a3f093bea973016a724f5` |
| RS/TemperedLFactorStatement | `fa1c78a8eea2e831b307d446eeadbb1421264fd47bcf081489542a757115bf0e` | `bd02f1b1975e543b11ef93abc330dacaffc3fcefa31405f1fd6556800b8c3187` |
| Cdr/Definitions | `1e1344124c2d1332d01130297405e48e776bc74eaae7538221418521dfc7e0d8` | `16d689abbf922f4e26bee7d1d49fc40c5d36822cc3327c6c1f82c1b7995dd083` |
| Cdr/SphericalTests | `5b33dacec15e6480fc40ef267b926dde63edc9abb1194033ecfed02c36e2c3e0` | `81ee27dfae292588d22b22778b120f3b9788b5ab6cd32128177bfa4ae1d8ae79` |
| Cdr/NewvectorStatement | `f5dbdba4104bb316b8d90edec8f987874383dfa5b3f476779a0ecec1bf5184a7` | `47f020178285da8b43e285396ed9c9334d72720640df7c84600d93663cef221b` |
| W/PrerequisitesStatement | `6db102db4fa4e5cc3bda3cbe773a349fe05060146f90d62972b8e380e9846c6b` | `65d27addd2c39b1c936c15506165fe18cf5099c01ef656e381510cc2fbf719df` |

### Defective Markdown fingerprints

| File | Snapshot | SHA256 |
|---|---|---|
| W/Spherical.md | S-base | `4369c516ff5c58e704e4e972d2dcb15c04812b7210cd6e846a1b07232471e03d` |
| RS/AnalyticStatement.md | B | `88773330126a097d88ee2ae0aaa4428c44ea226600aaf11f93595b921e52e8de` |
| RS/LocalFactor.md | B | `92e0b22fc59e1cb22480bbd944e8e85f4aff47b4b115b84c52012e1c011696c9` |
| RS/UnimodularityStatement.md | B | `f81aeef94da4207a8f7664380c41c679e5fe1be33b0ffd57d014b2c99b637031` |
| RS/GenericLocalConverseStatement.md | B | `d98b8530152d53e1ffcddb0c50b1ca48d8c437dd77f02a21ac921709f901db49` |
| RS/HighlyRamifiedStatement.md | B | `fb231cbe987c528015d5630e583e4371459c1ca1e688088f8c856d1ad2a3a8cb` |
| RS/LocalConverseStatement.md | B | `0afa2d5bc77c91efde6fa02b0f3f44d667a24fe6840f8d5c0b7fb2f71cc2137b` |
| RS/MultiplicativityStatement.md | B | `be55c974da43ef5b207435d7b8c52476a074324b4f22b256244304a2983bc24a` |
| RS/PadicPairFactors.md | B | `6c0a2f4aa023ff45fb711a8f76a654d8c2cd0db7c3c8478ab1bc573626e3b838` |
| RS/TemperedLFactorStatement.md | B | `6b96e13ebcef417742f16188740370b0a0cbba671dd59ae9a9d753357b340a81` |
| Cdr/Definitions.md | B | `2ff56ef9270b8efe4da0d60a0eee7e34dcbdd4a5966936184f7a2503b8890eae` |
| Cdr/SphericalTests.md | B | `d1b6078f293b6198f9a71aebeb8d5d7ff41b4a9bc43d464b04ee8ba6f0b848d2` |
| Cdr/NewvectorStatement.md | B | `4cd28193b6a7c833f123686ce3d3c1073731843f7b9abd01d739a1980f134be1` |
| W/PrerequisitesStatement.md | B | `197c90ced99a49dd304dff4412cb3d27ccb58fc6430300e4192e6ed824607fea` |

### Companion pairs in C

The shared UnipotentUnimodularity pair is shown once at its current helper-promotion version. SphericalTests is already in the owned-pair table.

| Pair stem | Lean SHA256 | Markdown SHA256 |
|---|---|---|
| Cdr/Essential | `ff9dcc9cfd6dddcff6188dce3dece71813f9abeb64316cd660aee469c43b5dd7` | `973e743cd346fd933875771ce9be8cfbfdef7c71356af46b381d112abfd90af7` |
| Cdr/EssentialStatement | `5a251747b3359ff226df16cfccd8fb00fb23445f3d664ff92d4394532f0e8bec` | `04d8ea739455a10176037b5c4f66f58564c10b292baec609bc1fba594090404a` |
| Langlands/Representation/Parabolic/UnipotentFiniteContainment | `f79a606e01beca4bc068b6eb36a9ec0b81d2df25a770de1ec18b57a9e177b481` | `23ba8a909a62e7df310cb65f80cd33380bb1014c028a0327ff1b25de56c02e1b` |
| RS/GeneralLinearUnimodularity | `6ba581f335c4c799b7b7ca839d7b6822d0d47cda6de15e1cb8ced71cebd6bb6d` | `2505a5f020d7c2cc92452d94a41621a359995009f93b042acdea02dfd5ef898f` |
| RS/QuotientHaarExistence | `4cdd1fd2d4754b62063679c5c1f17cce716334cd6235a70dcf2536408853acca` | `d72c0d872c68b188a0e01e57e1899a3aa880ec366e7d63a6f9497ced3e22b95e` |
| RS/QuotientIntegrals | `b4538cfb22765f8ff77b242fbf0de2162d7c42728669b7fe386ce24a029be08c` | `afe8ff63b287b6993509c722cae60f2529f293ad097d562349c27933af0c441b` |
| RS/UnipotentQuotient | `239aef6b95dabb871b8764da8b821df842461eee5d7998a875105741efb19c2e` | `b78b80f5caa107b33462953d8be304737fca6e000002d368c3471d5ca3ae192e` |
| RS/UnipotentUnimodularity | `26ceaee4f6d1731e2fc11a7fefd8d14cdb2ae75820f5fa4a87de6eab3fa93e9e` | `05472ed4788503ec539d606eeb0a513013db4c796e4e71728e842837f04f598c` |
| Sm/SmallRealizationProof | `6dd8d654ed7c2ad0682b3e06fd83ea20e4afe8504363470c9357cffb2ba6997d` | `0f2836876884a3846f8d2c24f590fe2bcd32b153fbb42dc69c3baa91f5c4edd4` |
| W/CharacterChange | `0156e7b1f733656f8c93596ce76c6ff7bcde7f2cd1f18330e41d4a041298abaa` | `240d261f0442613f490d8cb1501c68b8d4993bab321ea2c05691c9efecd74c88` |
| W/GeneralLinear | `5f5057d690e1bac49a27d650a3c9e678b94660efe8e244ed96e869f33488594c` | `f30d2edde346bc5bbdf3103a54c35f205a6be9643d900be6c4fea23ad38a49cc` |
| W/PrerequisiteInterfaces | `3e3945e0684ac46048b55cb3f27da9982ff7c1d020f6a78ca1cee8c4e5a80820` | `7d30c5ea52a8d0e45626a64117f72a9fb033fd3592f8e328db120abd0c117db0` |

### Additional checked dependencies in C

These hashes identify the cited definitions and targets; their presence in this table is not an additional claim of historical independent acceptance. These pairs are unchanged between B and C.

| Pair stem | Lean SHA256 | Markdown SHA256 |
|---|---|---|
| Cdr/Congruence | `c21658d4ae14ca5740227ec1a8c18bb92f44a5bad437f6e98a665de4c9e28b70` | `8aa328c233e7dfdf26ec843000690a66d56548686e83a921bb414edd567582c6` |
| W/Algebraic | `890e409cf2b4d586912b928755a4a0dc7b72de9d058ede7510482d816dad3906` | `8127b520fe0395c6600d6b72a7340b87edbf38c4ae1ca664546d63452f8e9072` |
| W/Iwasawa | `a4a3abc1fcbff7526451cb6e556a9fba0cc1c853b8f7a115e427cd754dfb2306` | `33f35ce22b7688f0f234f7af6141206bf41d39d1658cbc63f6b868b29e7ff3db` |
| Sm/SmallRealizationStatement | `f396004c3ab464c9381c85953011be0f7ccb0ab04daa5c538820ef78021e7c5c` | `73cca9a52c32422d2fdf0d3624e498659b9017b0e33f938b4badca82861d2bac` |
| RS/PairLFactor | `ee913887045eb20b519d59a0dfec6e84480cdcd6562c73637761dc09591f0d9c` | `3a42d7d4373a94788bc318c4b9d8e910e231936134bc6f1dadd33e7067afd3db` |
| RS/RationalZeta | `d7002189349916d9991af7c3ad6e334be1b93fb7b17320e0e943483350f6daa2` | `11086f1c2a1ff39e6b1f7ed0d5942ccd23801dc6c256bfd956e3c94342793f7d` |
| RS/FunctionalEquationStatement | `d2abd6d09f1cc1155bb8b80e32f5059cc931c1cd8d0d81610c54dedea0b32ce8` | `de240a8838d2919011b77fd1548a5064ac7e35a1980fb99d6edf4b9c7294030a` |


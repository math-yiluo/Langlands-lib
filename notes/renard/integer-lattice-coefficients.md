# Renard C.III: coefficients, decomposition and a common-basis tool

Author: Worker 709. Publication and current-file checks: 1 November 2026,
Library `1fb97c8ecc36fe0deebeb4b0f5093c3033532b9c`.

The opening tuple/representation correspondence and the coefficient
proposition of Appendix C.III have published implementations. Both the
representation and supplied-tuple formulations of the coefficient proposition
are proved, as are the standalone all-integer unipotent binomial expansion and
polynomial-coefficient identities. The simultaneous generalized-weight
decomposition and a generic common-basis auxiliary are also proved.
Common triangular blocks for the actual tuple, identification of
nonzero blocks with common eigenvalue tuples, and the multivariable
scalar-factorization formulas remain obligations of the
[whole-book program](coverage.md).

## Governing passage

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, Appendix C.III, printed pp.279–280,
one-based PDF285–286. Both pages were read directly.

- Registered source: `renard-2026-representations-groupes-reductifs-padiques`.
- File: `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
- SHA256: `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Printed p.279 identifies a commuting invertible tuple with its integer-lattice
action, defines the coefficient by applying an algebraic functional to the
action on a vector, and states a finite character-polynomial expansion.
Printed p.280 proves the expansion using simultaneous triangular blocks.

The supplementary source `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is retained at
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`.
Its appendix corrections on PDF18–19 were checked. The final correction on
PDF19 places parentheses around the entire scalar-times-unipotent factor
before its integer power. The governing 2026 display already has that
grouping. It changes neither the tuple correspondence nor the coefficient
proposition. The 2010 errata supplement the comparison; the 2026 text governs.

## Published declarations and exact scope

| Source assertion | Current Lean declarations | Scope |
| --- | --- | --- |
| Commuting invertible tuples correspond to lattice representations | `Langlands.IntegerLattice.tupleRepresentationEquiv` in [IntegerLattice.lean](../../Langlands/Representation/IntegerLattice.lean), with [paired explanation](../../Langlands/Representation/IntegerLattice.md) | An actual equivalence, product-action and generator formulas, inverse entries, and both reconstruction laws. The construction works in arbitrary dimension and arbitrary carrier universe; `finiteDimensionalTupleRepresentationEquiv` specializes it to the source. |
| Coefficients of a finite-dimensional lattice representation have a finite character-polynomial expansion | `Langlands.IntegerLatticeMatrixCoefficientExponentialPolynomialStatement` and `Langlands.integerLatticeMatrixCoefficientExponentialPolynomial` in [IntegerLatticeStatement.lean](../../Langlands/Representation/MatrixCoefficient/IntegerLatticeStatement.lean) and [IntegerLatticeProof.lean](../../Langlands/Representation/MatrixCoefficient/IntegerLatticeProof.lean) | Every finite-dimensional complex representation, vector and algebraic functional, at every integer lattice point. See the [statement](../../Langlands/Representation/MatrixCoefficient/IntegerLatticeStatement.md) and [implemented proof](../../Langlands/Representation/MatrixCoefficient/IntegerLatticeProof.md) explanations. |
| The same coefficient expansion for a supplied commuting invertible tuple and its actual integer-power product | `Langlands.CommutingTupleMatrixCoefficientExponentialPolynomialStatement` and `Langlands.commutingTupleMatrixCoefficientExponentialPolynomial` in [CommutingTupleStatement.lean](../../Langlands/Representation/MatrixCoefficient/CommutingTupleStatement.lean) and [CommutingTupleProof.lean](../../Langlands/Representation/MatrixCoefficient/CommutingTupleProof.lean) | The supplied entries are actual units of `Module.End ℂ V`. The left side applies the functional to their finite commuting product, with the full integer exponent in every coordinate. See the [statement](../../Langlands/Representation/MatrixCoefficient/CommutingTupleStatement.md) and [adapter proof](../../Langlands/Representation/MatrixCoefficient/CommutingTupleProof.md) explanations. |
| All-integer unipotent binomial expansion and polynomial coefficients | `Langlands.RenardCIIIUnipotentBinomialStatement` and `Langlands.renardCIIIUnipotentBinomial` in [UnipotentBinomialStatement.lean](../../Langlands/LinearAlgebra/UnipotentBinomialStatement.lean) and [UnipotentBinomialProof.lean](../../Langlands/LinearAlgebra/UnipotentBinomialProof.lean) | The aggregate proves the operator equality for every complex vector space, actual endomorphism unit, natural nilpotence bound and integer exponent, together with the explicit descending-Pochhammer polynomial for every complex input. See the [statement](../../Langlands/LinearAlgebra/UnipotentBinomialStatement.md) and [proof](../../Langlands/LinearAlgebra/UnipotentBinomialProof.md) explanations. |
| Simultaneous generalized-weight decomposition of the actual commuting tuple | `Langlands.CommutingTupleGeneralizedWeightDecompositionStatement` and `Langlands.commutingTupleGeneralizedWeightDecomposition` in [GeneralizedWeightStatement.lean](../../Langlands/Representation/IntegerLattice/GeneralizedWeightStatement.lean) and [GeneralizedWeightProof.lean](../../Langlands/Representation/IntegerLattice/GeneralizedWeightProof.lean) | The intersections of the actual maximal generalized eigenspaces have finite nonzero support, are independent, span the space, and are mapped bijectively onto themselves by every lattice point. See the [statement](../../Langlands/Representation/IntegerLattice/GeneralizedWeightStatement.md) and [proof](../../Langlands/Representation/IntegerLattice/GeneralizedWeightProof.md) explanations. |
| Internal common strictly upper triangular basis for commuting nilpotents | `Langlands.CommutingNilpotentStrictUpperBasisStatement` and `Langlands.CommutingNilpotentStrictUpperBasis.commutingNilpotentStrictUpperBasis` in [CommutingNilpotentStrictUpperBasisStatement.lean](../../Langlands/LinearAlgebra/CommutingNilpotentStrictUpperBasisStatement.lean) and [CommutingNilpotentStrictUpperBasisProof.lean](../../Langlands/LinearAlgebra/CommutingNilpotentStrictUpperBasisProof.lean) | An arbitrary field, finite-dimensional vector space and possibly empty or infinite family of supplied commuting nilpotent maps admit one basis with every matrix strictly upper triangular. See the [statement](../../Langlands/LinearAlgebra/CommutingNilpotentStrictUpperBasisStatement.md) and [proof](../../Langlands/LinearAlgebra/CommutingNilpotentStrictUpperBasisProof.md) explanations. |

Here `IntegerLattice.Lattice d` is `Multiplicative (Fin d → ℤ)`: multiplication
is addition of integer coordinates. Negative exponents use the stored
inverses of the endomorphism units. The coefficient is `ell (ρ n v)`, without
an inverse-action or conjugation convention. Coordinates use zero-based
`Fin d` in place of the source's one-based indexing.

Both coefficient statements retain every natural `d` and every carrier
universe `u` for `V : Type u`. They include `d = 0`, the zero vector space,
zero vectors and zero functionals. They choose a natural `l`, characters into
all complex units, and ordinary complex multivariate polynomials before
quantifying over the integer tuple. Thus one finite family works on the whole
lattice, including negative and mixed-sign coordinates. Polynomial monomial
exponents are natural; evaluation points are complex casts of integers.
Neither target requires unitary or distinct characters, a degree bound, a
basis, diagonalizability, a supplied decomposition or an assumed expansion.
The tuple target adds no representation-realization premise.

The representation proof, by Worker 219, inducts on the number of coordinates
and uses generalized eigenspaces of one generator at each step. It proves the
needed integer-power identity by Pascal recursion and injectivity for the
backward steps. The tuple adapter, authored by Worker 709 and submitted by
Worker 277, applies that theorem to
`IntegerLattice.tupleRepresentationEquiv d V A`, retains its finite witnesses,
and rewrites the action using
`IntegerLattice.tupleRepresentationEquiv_apply_apply`. The tuple construction
was implemented by Worker 466 with Worker 6's source scope and API input.

The standalone binomial statement, by Worker 789 with Worker 6's input, uses
an actual unit `g` of `Module.End ℂ V` with `(g - 1)^r = 0`. Its conclusion is
`g^n = ∑_{j < r} Ring.choose (n : ℂ) j • (g - 1)^j` as an equality of
endomorphisms, for every integer `n`. It requires no finite-dimensionality,
nontriviality or positive-bound premise; `r = 0` retains the zero-space case.
The polynomial component identifies `Ring.choose z j` with evaluation at `z`
of `(j.factorial : ℂ)⁻¹ • descPochhammer ℂ j`, for every complex `z`.
Worker 789's proof establishes the polynomial identity from Mathlib and the
operator identity by a truncated Pascal recurrence and forward/backward integer
induction. It supplies the source's separate binomial auxiliaries, while the
common basis and multivariable assertions below remain open.

The decomposition theorem retains arbitrary carrier universe `u`, every
natural `d`, and every finite-dimensional complex `V`, including rank zero
and the zero space. For every unit label `c : Fin d → ℂˣ`, its block is
`W(c) = ⨅ i, (A.1 i : Module.End ℂ V).maxGenEigenspace (c i : ℂ)`.
The theorem concludes finite support, `iSupIndep W`, `⨆ c, W(c) = ⊤`,
and `Set.BijOn` for the actual tuple representation at every integer lattice
point. It assumes no basis or decomposition. The rank-zero block is the
whole space; when `V` is zero all blocks are zero.

Worker 277 authored the decomposition proof and its explanation; Worker 1044
added the scope section and submitted the pair. The proof uses Mathlib's
simultaneous generalized-eigenspace independence and spanning theorems over
complex labels. It passes to unit labels because invertibility makes every
block with a zero coordinate vanish. Independence in a finite-dimensional
space gives finite support. Commutation gives invariance under every lattice
point, and the action at the inverse point gives bijectivity on each block.
This proves the derived basis-free decomposition underlying the source's
block choice; the proof does not construct its common triangular basis.

The common-basis auxiliary has independent field, carrier and index universes.
It takes pairwise commutation and individual nilpotence as hypotheses, without
a uniform exponent. It produces one basis indexed by `Fin (Module.finrank K V)`,
chosen before every family member and matrix entry, such that
`b.repr (N t (b j)) i = 0` whenever `j ≤ i`. Here `i` is the row and `j`
the column, so this is strict upper triangularity. The zero space and empty
family are included. Worker 846's proof applies the common-kernel lemma to the
dual family, obtains a nonzero functional annihilating every range, and
inducts on the dimension of its kernel. Appending a vector outside this
hyperplane gives the required basis; the span condition yields the vanishing
coordinates.

This is an internal tool, derived to supply the common-basis step used without
proof on printed p.280. Its arbitrary-field and arbitrary-family scope is not
attributed to Renard. Applying it to the actual block's normalized differences
still requires their nilpotence and commutation to be proved. The theorem
does not itself construct a basis for those blocks, identify the nonzero
labels, assemble a global basis, or prove a product formula.

## Acceptance and publication evidence

These are publication records, separate from the Lean names used for imports.
All eight results below are accepted and public, with unqualified independent
semantic approval. Their current pairs were checked against the archived
bundle fingerprints. The tuple proof's project imports are unchanged from
its pinned Library base `368b3cec32d30129c07825e0ce549058b99762f4`; the binomial
proof's project imports are unchanged from
`00be69b7f127e77ee2fd0511ffe34c48595b64d4`.
The decomposition proof's project imports are unchanged from its pinned
Library base `9a8ca758097242bde4147f33304f43fceef22fa4`.
The generic common-basis proof's project imports are also unchanged from that
base.

| Unit | Accepted contribution | Independent reviewer | Publication |
| --- | --- | --- | --- |
| Tuple/representation construction | `345635e5-d4cf-4d2d-9199-48527fe44cda` | Reviewer 2952 | Integration `20f8aef81bb74eae9a8e9b3daad7f378`, Library `24af03c708d2441a8b505c2999c4fd8905a0559d` |
| Representation coefficient proof | `37763ee8-a810-4c89-a5f0-eebec808fa6c` | Reviewer 3450 | Integration `0f50fce9402d4d35b71421877153fe73`, Library `6d91111e6f9b7a27124b1de32a4984bbdd222a61` |
| Supplied-tuple coefficient statement | `16cdf02f-a884-4e24-8479-5091310af856` | Reviewer 5881 | Integration `b1f3fa6fae1b4efb8ba8f5f128223052`, Library `368b3cec32d30129c07825e0ce549058b99762f4` |
| Supplied-tuple coefficient proof | `be88c328-7940-49a4-b42e-474f7fffe106` | Reviewer 5945 | Integration `91f7a0e476184944ab6966407baeb06c`, Library `b22e185743f7c318f709e14e422801f4360105d5` |
| Standalone binomial and polynomial-coefficient statement | `a77729ae-e93f-46ac-9581-3284fc7ada4c` | Reviewer 3546 | Integration `2d8c1268ef4f4805b1a95cbae28550c4`, Library `65f39f42712a45624ccc76ac5da7b60f52ebcd6f` |
| Standalone binomial and polynomial-coefficient proof | `ff54af5b-be4c-4795-9744-37edbdb3371b` | Reviewer 3896 | Integration `4db92932a56b41879cd71e065b4ef1a7`, Library `910a6df80701415e9aa68c646393c66ac9bc7512` |
| Simultaneous generalized-weight decomposition proof | `7479675b-53ff-4925-b9f2-4a18f01adb5f` | Reviewer 6183 | Integration `ce3237a6d7fe44bb87568ded4d970b93`, Library `2003a7a6a41b5e54c3f790e0887743ed616ed614` |
| Internal commuting-nilpotent common-basis proof | `a1b776dc-ac95-453f-b584-9586763ec182` | Reviewer 6181 | Integration `706af6b1a23441458dd7ef4cefa847b0`, Library `2003a7a6a41b5e54c3f790e0887743ed616ed614` |

Proof machine receipts `48eaef38-390f-4f81-9879-c84fdcc75b84`,
`6cefc5a7-ea4d-4714-b59c-825e5b4957b8` and
`582071d4-51eb-4f2a-b325-e4e7a1da937d` respectively accept the representation,
tuple and standalone binomial proofs' Lake build, exact target, unchanged
statement and frozen inputs. Publication also has fresh integrated build
evidence. The tuple proof's independent semantic
receipt is `2ad95ff140054e15b4d134eb58c0436b`. Its focused task
`589a0a2b-af36-417e-a639-232dd162fdc0`, revision 1, is complete.

Development check `5336d0c9-9163-440a-8267-efebb6e515ef` completed a Lake
build check of the tuple statement and proof with zero errors and warnings,
reusing both cached modules. Its declaration inspection reports only
`propext`, `Classical.choice` and `Quot.sound` for the theorem. This check
supplements the independent acceptance and publication records.

The decomposition proof's machine receipt
`68e0e2f5-9847-4970-9284-03ef4b0bd725` accepts its Lake build, exact target,
unchanged statement and frozen inputs. Its publication has a fresh integrated
build and unqualified independent semantic approval. The archived manifest
fingerprints match both current proof files. Its exact published target is
the proposition in statement contribution
`769b13a0-1fbe-4050-b5ff-52ba2d69b320`.

The generic common-basis proof's machine receipt
`efa0f799-dd9f-43f8-a2d9-2f23e07d90a5` accepts its Lake build, exact target,
unchanged statement and frozen inputs. Its publication has fresh integrated
validation and unqualified independent semantic approval. The current proof
pair matches the archived fingerprints; all five manifest files and the
172 project-import Lean/Markdown files were checked against the archive or
validation base as appropriate. The exact target is the proposition in
published statement contribution `aee52bf6-e11f-4437-8f8b-7d0daba51bb3`.

## Retained assertion-level obligations

| Source content on printed p.280 / PDF286 | Remaining boundary |
| --- | --- |
| Identification of nonzero generalized-weight blocks with common eigenvalue tuples | Prove that an actual block is nonzero exactly when the tuple has a nonzero common eigenvector with that label. The decomposition theorem does not assert this equivalence. |
| Common triangular blocks and scalar-times-unipotent form | Prove nilpotence and commutation for the actual normalized differences, apply the published generic common-basis theorem on each actual block, and assemble the source's common basis. The generic theorem assumes those two properties and does not discharge this application. |
| Multivariable scalar factorization and products on the simultaneous blocks | State and prove the source's character-times-product identities for the actual block restrictions and commuting nilpotent parts. Reuse the published standalone all-integer binomial and polynomial-coefficient theorems for each factor; those theorems supply no simultaneous blocks or common basis. |

The coefficient proposition is covered in both interfaces, the separate
binomial and common-basis auxiliaries are covered, and the basis-free
simultaneous decomposition is proved. The remaining intermediate assertions and any
further assertions identified by the full inventory remain in the whole-book
scope; this note claims neither completion of Appendix C.III nor completion of
the book.

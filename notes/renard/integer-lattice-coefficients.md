# Renard C.III: coefficients and simultaneous blocks

Author: Worker 709, with source-scope and API input from Worker 6.
Current source-assertion audit: 6 November 2026, Library
`d2fd0b68e11e9844d5da3650e7579d62588fd3fd`. The preceding audit of
1 November 2026 used Library `61bb004ff54df5b8a9b8c0a52b9703406a6b11a2`.

The tuple/representation correspondence, coefficient proposition in both
interfaces, all-integer binomial expansion, generalized-weight decomposition
and generic common-basis tool have published implementations. Further published
proofs identify the actual nonzero blocks, prove nilpotence and commutation of
their normalized differences, choose local and global common bases, and prove
the three all-integer product identities. Two later published proofs supply
the scalar action on common eigenvectors with the finite list of distinct
occurring characters, and the particular polynomial witnesses assembled from
the actual block bases. The current ledger below maps the whole C.III passage
to these exact targets. The earlier eight-result publication audit and the
boundaries open at the earlier snapshots are preserved as historical evidence.
This note is a coverage update within the [whole-book program](coverage.md).

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

## Earlier published interfaces and exact scope

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
actual-block basis and multivariable assertions are separate results mapped
in the current ledger below.

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
attributed to Renard. The theorem assumes nilpotence and commutation of its
supplied family. The actual-block theorems in the current ledger below discharge these hypotheses
from the original tuple and construct its bases. Support identification and
product identities have their own published targets.

## Historical eight-result publication audit

This audit was made at Library
`1fb97c8ecc36fe0deebeb4b0f5093c3033532b9c` on 1 November 2026. Its eight
publication entries and their validation-base comparisons are retained. The
current audit below additionally checks these pairs against the later Library.

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

## Historical assertion-level obligations

The following table records the remaining boundaries at Library
`1fb97c8ecc36fe0deebeb4b0f5093c3033532b9c`. The current audit below supersedes
these open statuses; the table is retained to explain the earlier coverage.

| Source content on printed p.280 / PDF286 | Remaining boundary |
| --- | --- |
| Identification of nonzero generalized-weight blocks with common eigenvalue tuples | Prove that an actual block is nonzero exactly when the tuple has a nonzero common eigenvector with that label. The decomposition theorem does not assert this equivalence. |
| Common triangular blocks and scalar-times-unipotent form | Prove nilpotence and commutation for the actual normalized differences, apply the published generic common-basis theorem on each actual block, and assemble the source's common basis. The generic theorem assumes those two properties and does not discharge this application. |
| Multivariable scalar factorization and products on the simultaneous blocks | State and prove the source's character-times-product identities for the actual block restrictions and commuting nilpotent parts. Reuse the published standalone all-integer binomial and polynomial-coefficient theorems for each factor; those theorems supply no simultaneous blocks or common basis. |

At that snapshot, both coefficient interfaces, the binomial and common-basis
auxiliaries, and the basis-free decomposition were proved. The intermediate
assertions in this table remained parent obligations. Their later publications
are recorded next.


## Current actual-block constructions and proved targets

All names in this section are current Library declarations. In the namespace
`Langlands.IntegerLattice`, the published
[block construction](../../Langlands/Representation/IntegerLattice/GeneralizedWeightBlock.lean)
and its [explanation](../../Langlands/Representation/IntegerLattice/GeneralizedWeightBlock.md)
define, for the original tuple `A` and unit label `c : Fin d → ℂˣ`,

```text
W(c)  = generalizedWeightBlock A c
      = ⨅ i, (A.1 i : Module.End ℂ V).maxGenEigenspace (c i : ℂ),
ρ_c   = generalizedWeightBlockRepresentation A c,
G_i   = generalizedWeightBlockGenerator A c i,
U_i   = normalizedBlockGenerator A c i,
N_i   = normalizedGeneratorDifference A c i = U_i - 1,
χ_c   = coordinateCharacter c.
```

These are actual restrictions and units. Coercing `ρ_c(n) w` to `V` gives
`tupleRepresentationEquiv d V A n (w : V)`; `G_i` and its inverse act as the
original `A.1 i` and its stored inverse. The intrinsic normalization is
`U_i = (c i : ℂ)⁻¹ • G_i`, with the inverse formula also proved, and
`G_i = (c i : ℂ) • (1 + N_i)`. The character is
`χ_c(n) = ∏ i, c i ^ n.toAdd i`, with generator value `c i` and inverse-generator
value `(c i)⁻¹`. Construction contribution
`9c8f119a-f7c0-4a37-bed4-959d39cdfedf`, authored by Worker 1044, is published;
its intrinsic equations and current pair were included in the audit.

In the following table, each proposition and closing theorem has namespace
`Langlands`. Every row quantifies over every natural `d`, finite-dimensional
complex `V : Type u`, and actual commuting invertible tuple `A`. No basis,
decomposition, nilpotence or desired conclusion is supplied as an extra premise.

| Published proposition / closing theorem | Exact conclusion and files |
| --- | --- |
| `CommutingTupleGeneralizedWeightSupportStatement` / `commutingTupleGeneralizedWeightSupport` | For every unit label `c`, `W(c) ≠ ⊥` if and only if there exists `v ≠ 0` in `V` with `A_i v = c_i • v` for every coordinate. [Statement](../../Langlands/Representation/IntegerLattice/GeneralizedWeightSupportStatement.lean), [proof](../../Langlands/Representation/IntegerLattice/GeneralizedWeightSupportProof.lean), [proof explanation](../../Langlands/Representation/IntegerLattice/GeneralizedWeightSupportProof.md). |
| `CommutingTupleNormalizedBlockNilpotenceStatement` / `commutingTupleNormalizedBlockNilpotence` | For every `c`, `N_i ^ Module.finrank ℂ V = 0` for every coordinate, and all `N_i` commute. The exponent is the ambient dimension. [Statement](../../Langlands/Representation/IntegerLattice/NormalizedBlockNilpotenceStatement.lean), [proof](../../Langlands/Representation/IntegerLattice/NormalizedBlockNilpotenceProof.lean), [proof explanation](../../Langlands/Representation/IntegerLattice/NormalizedBlockNilpotenceProof.md). |
| `CommutingTupleGeneralizedWeightBlockBasisStatement` / `commutingTupleGeneralizedWeightBlockBasis` | For every `c`, one basis of `W(c)` makes all `N_i` strictly upper triangular. The same basis gives `G_i = c_i • (1 + N_i)`, the entry formula, below-diagonal vanishing and constant diagonal `c_i`. The existential basis precedes all coordinate quantifiers. [Statement](../../Langlands/Representation/IntegerLattice/GeneralizedWeightBlockBasisStatement.lean), [proof](../../Langlands/Representation/IntegerLattice/GeneralizedWeightBlockBasisProof.lean), [proof explanation](../../Langlands/Representation/IntegerLattice/GeneralizedWeightBlockBasisProof.md). |
| `CommutingTupleGeneralizedWeightGlobalBasisStatement` / `commutingTupleGeneralizedWeightGlobalBasis` | One family of local bases and one ambient basis, indexed by `Σ c, Fin (finrank ℂ W(c))`, are chosen before `n`. The theorem proves the embedding equation, strict upper triangularity of every local `N_i`, off-block and below-diagonal vanishing for every lattice action, and diagonal `χ_c(n)`. [Statement](../../Langlands/Representation/IntegerLattice/GeneralizedWeightGlobalBasisStatement.lean), [proof](../../Langlands/Representation/IntegerLattice/GeneralizedWeightGlobalBasisProof.lean), [proof explanation](../../Langlands/Representation/IntegerLattice/GeneralizedWeightGlobalBasisProof.md). |
| `CommutingTupleGeneralizedWeightProductStatement` / `commutingTupleGeneralizedWeightProduct` | For every `c,n`, `ρ_c(n)` equals the ordered product of the `G_i ^ n_i`, equals `χ_c(n)` times the ordered product of the `U_i ^ n_i`, and equals `χ_c(n)` times the ordered product of `∑_{k < finrank ℂ V} Ring.choose (n_i : ℂ) k • N_i ^ k`. [Statement](../../Langlands/Representation/IntegerLattice/GeneralizedWeightProductStatement.lean), [proof](../../Langlands/Representation/IntegerLattice/GeneralizedWeightProductProof.lean), [proof explanation](../../Langlands/Representation/IntegerLattice/GeneralizedWeightProductProof.md). |

The product target uses increasing-coordinate `List.ofFn` products in the
endomorphism ring. Generator and normalized powers are first formed in the
unit group with their full integer exponents, then coerced. Thus the first
product preserves the parentheses around the entire scalar-times-unipotent
factor in the source. The final product is a finite sum in each factor,
including negative and mixed-sign lattice coordinates. It makes no assertion
that the ambient-dimension cutoff is minimal.

## Implemented proofs and provenance

Worker 189's support proof restricts the scalar differences `A_i - c_i • 1`
to `W(c)`. Their commutation and generalized-eigenspace nilpotence allow the
published common-kernel lemma to produce a nonzero common eigenvector.
Conversely, an ordinary common eigenvector lies in every maximal generalized
eigenspace. This gives a basis-free characterization of the source's labels.

Worker 1201's normalized-nilpotence proof uses stabilization of the ambient
generalized eigenspace at exponent `finrank ℂ V`, compares powers after
coercion, and rescales by the inverse unit label. Restricted generators commute
as images of elements of the abelian lattice; central scalar multiplication
and subtraction of the identity preserve commutation.

Worker 438's local-basis proof establishes nilpotence and commutation on the
actual block and applies the published generic commuting-nilpotent basis
theorem. It then takes coordinates in the normalization identity. Its
nilpotence helper uses restriction of the scalar difference on the maximal
generalized eigenspace; it does not depend on first choosing a basis.

Worker 88's global-basis proof likewise applies the generic tool to the actual
differences on each block, and uses independence and spanning from the
published generalized-weight decomposition to collect the local bases through
an internal direct sum. A subgroup argument extends upper triangularity and
the character diagonal from the generators to every integer lattice point,
including inverses. The proof uses all unit labels with empty fibers at zero
blocks; it does not assume that the entire label type is finite.

Worker 308's product proof reconstructs the restricted representation from
its generator units. Central scalar units allow separation of integer powers,
and ordered-list induction collects the scalar factors as `χ_c(n)`. The
published local-basis module's nilpotence helper, a submodule dimension bound,
and the standalone all-integer binomial theorem give the last identity. The
proof does not choose or use the local basis to establish this product.

These are derived intrinsic formulations of Renard's actual matrix blocks.
Their routes and the generic theorem's stronger arbitrary-field scope are
explained by the paired Markdown; they are not extra source claims. The
coefficient propositions themselves remain proved by the coordinate-induction
route described above. This note does not attribute those proofs to the later
global-basis or product developments. The source-route assembly is a separate,
later published target, described in the section on particular polynomial
witnesses below.

## Source-assertion ledger for the complete C.III passage

C.III consists of the opening construction, coefficient definition, one
unnumbered proposition and its proof, from the section heading on PDF285 to
the closing square on PDF286. The preceding stable-endomorphism proposition
on PDF285 belongs to C.II. There is no local bibliographic appeal in C.III.
The table includes the substantive assertions in the proof, even when they
are not numbered. The ledger of the 1 November audit marked the scalar action,
the distinct-character list and the polynomial-witness assembly as derived
comparisons without a located named theorem; the rows below now cite the
published targets that close them.

| 2026 locator | Source assertion | Published correspondence and status |
| --- | --- | --- |
| Printed p.279 / PDF285, first paragraph and display | Commuting invertible tuples and representations of `ℤ^d` correspond; `U(n) = u_1^n_1 ⋯ u_d^n_d`. | `IntegerLattice.tupleRepresentationEquiv`, its reconstruction laws and generator/product equations. Proved construction, with finite-dimensional specialization. |
| Printed p.279 / PDF285, coefficient display | `F(n) = λ(U(n)v)` for a vector and algebraic functional. | `Langlands.matrixCoefficient` in [Definitions.lean](../../Langlands/Representation/MatrixCoefficient/Definitions.lean), with [convention explanation](../../Langlands/Representation/MatrixCoefficient/Definitions.md); the representation and tuple statement left sides use this convention. Definition coverage. |
| Printed p.279 / PDF285, unnumbered proposition | A single finite family of characters and complex polynomials gives `F(n) = ∑ χ_j(n) Q_j(n)` at every integer point. | The representation and supplied-tuple coefficient propositions and their published exact proofs. Proved in both interfaces; neither proposition requires distinct characters. |
| Printed p.279 / PDF285, first proof paragraph | Common eigenvalue tuples occur, and their coordinates are nonzero. | The support equivalence above, together with the decomposition's spanning/nonzero support and unit labels, identifies the occurring tuples. The zero space has no nonzero common eigenvector. No separate nontrivial-space assumption is imposed globally. |
| Printed p.279 / PDF285, scalar-action display | On a common eigenspace `U(n)` acts by `χ_c(n) = ∏ c_i^n_i`. | `CommutingTupleCommonEigenvectorCharacterStatement` / `commutingTupleCommonEigenvectorCharacter`: for the same vector `v`, the generator eigen-equations hold if and only if `U(n)v = χ_c(n) • v` at every integer lattice point. Proved, without finite-dimensionality. |
| Printed p.279 / PDF285, last paragraph | List all distinct characters obtained from the common eigenvalue tuples. | `IntegerLatticeCoordinateCharacterReconstructionStatement` / `integerLatticeCoordinateCharacterReconstruction` proves that `coordinateCharacter` is injective and reconstructs every lattice character from its generator values. `CommutingTupleOccurringCharacterEnumerationStatement` / `commutingTupleOccurringCharacterEnumeration` proves one finite injective list enumerating exactly the nonzero blocks and exactly the characters realized on nonzero vectors. Proved. |
| Printed p.280 / PDF286, opening paragraph | Choose one common block triangular basis for every lattice point, with constant character diagonals. | The global-basis theorem's actual ambient basis, off-block and below-diagonal vanishing, and diagonal clauses prove this coordinate formulation. The all-label sigma index is an internal alternative to the source's finite enumeration. |
| Printed p.280 / PDF286, reduction to entries and blocks | It suffices to prove the desired form for matrix entries, then for each block. | `CommutingTupleGeneralizedWeightPolynomialCoefficientStatement` / `commutingTupleGeneralizedWeightPolynomialCoefficient` performs this reduction for every compatible pair of local and ambient bases: it expands the coefficient over exactly the nonzero blocks, with block-entry polynomials. Proved. The earlier coefficient theorem proves the existential target by a different route. |
| Printed p.280 / PDF286, first display | `A_j(e_k) = z_k^(j) (Id + N_k^(j))`, with strictly upper triangular, nilpotent, commuting `N_k^(j)`. | Intrinsic normalization, the five local-basis clauses and normalized nilpotence/commutation prove the actual-block formulation. Strict upper triangularity uses row `i`, column `j`, with zero entries for `j ≤ i`. |
| Printed p.280 / PDF286, second display, first line | The block action is the product of the whole scalar-times-unipotent generator factors raised to integer powers. | First clause of the product theorem, with the intrinsic identity for each `G_i`. Actual unit powers preserve the errata's grouping. |
| Printed p.280 / PDF286, second display, second line | Extract the scalar character and leave a product of unipotent integer powers. | Second clause of the product theorem, with `U_i = 1 + N_i` as underlying endomorphisms. Proved for all integer coordinates. |
| Printed p.280 / PDF286, second display, third line and following sentence | Each unipotent power has a finite binomial expansion because the difference is nilpotent. | Third clause of the product theorem, normalized nilpotence's ambient bound, and the standalone operator binomial theorem. Proved with an explicit finite range. |
| Printed p.280 / PDF286, final sentence | The binomial coefficients are polynomials in the coordinates, yielding the coefficient proposition. | The standalone polynomial component identifies `Ring.choose z k` with `(k!)⁻¹ • descPochhammer ℂ k` evaluated at `z`, for every complex `z`. `CommutingTupleGeneralizedWeightPolynomialActionStatement` / `commutingTupleGeneralizedWeightPolynomialAction` shows that every block-action matrix entry is `χ_c(n)` times the evaluated entry of the particular polynomial matrix of the published definitions, and `CommutingTupleGeneralizedWeightPolynomialAssemblyStatement` / `commutingTupleGeneralizedWeightPolynomialAssembly` chooses the compatible bases and exact support once and yields the coefficient proposition with those particular witnesses. Proved. |

At the 1 November audit (Library `61bb004f`), the scalar action on ordinary
common eigenvectors, the injectivity of labels into characters with the
resulting finite list, and the assembly of the particular polynomial witnesses
from the block bases were explained only as mathematical deductions. That
audit kept them as explicit verification boundaries for any claim that the
source-route assembly is formally implemented. The published occurring-character
and polynomial-comparison proofs, described in the next section, now prove
exact targets for all three. The older support, triangular-basis and product
targets remain the proved inputs.

All constructions and the five actual-block propositions retain arbitrary carrier
universe `u`, every natural rank, every unit label, the zero space and zero
blocks. At rank zero the intersection is `⊤`, the lattice action is identity,
and products are empty. The support equivalence then means exactly that the
space has a nonzero vector. At a zero block the basis fiber is empty; for a
zero ambient space the nilpotence bound and binomial range are zero and
`1 = 0` in its endomorphism ring. No positivity or nonzero-block hypothesis
has been added. The finite-dimensional assumption is the original C.III
hypothesis; the construction and several intermediate identities also work
without it.

## Occurring characters and particular polynomial witnesses

All names in this section are current Library declarations. The occurring-character
[statement](../../Langlands/Representation/IntegerLattice/OccurringCharactersStatement.lean)
and its [explanation](../../Langlands/Representation/IntegerLattice/OccurringCharactersStatement.md)
define three propositions in the namespace `Langlands`:

| Proposition | Exact content |
| --- | --- |
| `IntegerLatticeCoordinateCharacterReconstructionStatement` | For every `d`, every monoid homomorphism `χ : Lattice d →* ℂˣ` equals `coordinateCharacter (fun i => χ (generator d i))`, and `coordinateCharacter` is injective. No representation or occurrence premise is involved. |
| `CommutingTupleCommonEigenvectorCharacterStatement` | For every complex vector space `V : Type u`, tuple `A`, unit label `c` and the same vector `v`, the generator equations `A_i v = c_i • v` hold for every `i` if and only if `U(n)v = χ_c(n) • v` for every lattice point `n`. There is no finite-dimensional premise, and `v = 0` is included. |
| `CommutingTupleOccurringCharacterEnumerationStatement` | For finite-dimensional `V`, there are `l : ℕ` and `c : Fin l → Fin d → ℂˣ` such that the characters `χ_{c j}` are pairwise distinct, `W(b) ≠ ⊥` exactly when `b = c j` for some `j`, and a character `χ : Lattice d →* ℂˣ` acts on some nonzero vector by `U(n)v = χ(n) • v` exactly when `χ = χ_{c j}` for some `j`. |

`RenardCIIIOccurringCharactersStatement.{u}` is their conjunction. The
enumeration quantifies over all lattice characters, so the occurring characters
are not assumed in advance to be coordinate characters. For the zero space the
list is empty. At rank zero the single label has block `⊤`, so the list has one
entry exactly when `V` is nonzero.

Worker 1214's [proof](../../Langlands/Representation/IntegerLattice/OccurringCharactersProof.lean),
with its [explanation](../../Langlands/Representation/IntegerLattice/OccurringCharactersProof.md),
closes `renardCIIIOccurringCharacters` from `integerLatticeCoordinateCharacterReconstruction`,
`commutingTupleCommonEigenvectorCharacter` and `commutingTupleOccurringCharacterEnumeration`.
It writes every lattice point as a product of integer powers of the
generators and evaluates characters at the generators. For the eigenvector
equivalence, the lattice points acting on `v` by the character form a subgroup
containing the generators; inverses use the representation's inverse and
cancellation of units. The enumeration reindexes the finite support from
`commutingTupleGeneralizedWeightDecomposition` by `Fin` and uses
`commutingTupleGeneralizedWeightSupport` in both occurrence directions. Its
helpers in `Langlands.IntegerLattice` are `lattice_eq_prod_generators`,
`coordinateCharacter_reconstruction`, `coordinateCharacter_injective` and
`commonEigenvector_iff_coordinateCharacter`.

The polynomial-matrix
[definitions](../../Langlands/Representation/IntegerLattice/GeneralizedWeightPolynomial.lean),
with their [explanation](../../Langlands/Representation/IntegerLattice/GeneralizedWeightPolynomial.md),
are in the namespace `Langlands.IntegerLattice`. They take a supplied local
basis `b` of `W(c)`, indexed by `Fin (finrank ℂ W(c))`, and, for the
coefficient, an ambient basis `B` indexed by `Σ c, Fin (finrank ℂ W(c))`:

```text
coordinateBinomialPolynomial i k
  = X i substituted into (k!)⁻¹ • descPochhammer ℂ k,
generalizedWeightBinomialMatrixFactor A c b t
  p q = ∑_{k < finrank ℂ V} coordinateBinomialPolynomial t k
          * C (b.repr ((N_t ^ k) (b q)) p),
generalizedWeightPolynomialMatrix A c b
  = (List.ofFn (generalizedWeightBinomialMatrixFactor A c b)).prod,
generalizedWeightCoefficientPolynomial A c b B v ell
  = ∑ p, ∑ q, C (ell (b p) * B.repr v ⟨c, q⟩)
          * generalizedWeightPolynomialMatrix A c b p q.
```

The published laws `eval_coordinateBinomialPolynomial`,
`eval_generalizedWeightBinomialMatrixFactor`,
`generalizedWeightPolynomialMatrix_rank_zero` and
`generalizedWeightCoefficientPolynomial_eq_zero_of_finrank_eq_zero` accompany
them. The definitions have no finite-dimensional premise and do not assume that
`b` and `B` are compatible.

The polynomial-comparison
[statement](../../Langlands/Representation/IntegerLattice/GeneralizedWeightPolynomialComparisonStatement.lean),
with its [explanation](../../Langlands/Representation/IntegerLattice/GeneralizedWeightPolynomialComparisonStatement.md),
defines three propositions in the namespace `Langlands`. Each quantifies over
every natural `d`, finite-dimensional complex `V : Type u` and actual tuple `A`;
`x_n` denotes the point `t ↦ (n.toAdd t : ℂ)`.

| Proposition | Exact content |
| --- | --- |
| `CommutingTupleGeneralizedWeightPolynomialActionStatement` | For every label `c`, every basis `b` of `W(c)` (no triangularity is assumed), every `n` and all `p, q`: `b.repr (ρ_c(n) (b q)) p = χ_c(n) * eval x_n (generalizedWeightPolynomialMatrix A c b p q)`. |
| `CommutingTupleGeneralizedWeightPolynomialCoefficientStatement` | For every family of local bases `b` and ambient basis `B` with `B ⟨c, q⟩ = b c q`, there is a finite set `s` of labels with `c ∈ s ↔ W(c) ≠ ⊥`, chosen before every `v`, `ell` and `n`, such that `ell (U(n) v) = ∑_{c ∈ s} χ_c(n) * eval x_n (generalizedWeightCoefficientPolynomial A c (b c) B v ell)`. |
| `CommutingTupleGeneralizedWeightPolynomialAssemblyStatement` | There exist `b`, `B` and `s` with the same compatibility, exact support and identity. |

`RenardCIIIPolynomialComparisonStatement.{u}` is their conjunction. Its sum
has one term for each nonzero block; by the injectivity of
`coordinateCharacter` above, these terms carry pairwise distinct characters.
The assembly clause is the coefficient proposition with the particular
polynomial witnesses of the proof on printed p.280.

Worker 88's [proof](../../Langlands/Representation/IntegerLattice/GeneralizedWeightPolynomialComparisonProof.lean),
with its [explanation](../../Langlands/Representation/IntegerLattice/GeneralizedWeightPolynomialComparisonProof.md),
closes `renardCIIIPolynomialComparison` from
`commutingTupleGeneralizedWeightPolynomialAction`,
`commutingTupleGeneralizedWeightPolynomialCoefficient` and
`commutingTupleGeneralizedWeightPolynomialAssembly`. It transports the third
clause of `commutingTupleGeneralizedWeightProduct` through
`LinearMap.toMatrixAlgEquiv b`, takes the support from the decomposition, and
obtains the compatible witnesses from `commutingTupleGeneralizedWeightGlobalBasis`.
Its helpers `IntegerLattice.PolynomialComparison.eval_matrix`,
`sum_block_coordinates` and `functional_block_action` are in the proof
module. The proof does not use the earlier existential coefficient theorem,
and it puts no finiteness instance on the type of all labels.

Workers 709 and 1214 prepared the occurring-character statement (statement
task `fe086a8f-19ce-42eb-a8b0-50d8136e512e`). Workers 709 and 308 wrote the
polynomial-matrix definitions. Worker 709 prepared the polynomial-comparison
statement, which Worker 308 checked and submitted (statement task
`bd8e37d0-6968-4c11-85e5-0fec02620914`). Worker 709 is the author of this note;
that coauthorship is documented here as authorship, not as review. The
independent reviews recorded below were made by the named reviewers. The two
proofs belong to Workers 1214 and 88; this note imports no proof authorship.

## Current independent acceptance and publication evidence

The 1 November audit compared 22 accepted Lean/Markdown pairs against their
archived bundle fingerprints, the pinned Library
`61bb004ff54df5b8a9b8c0a52b9703406a6b11a2`, and the workspace files. All
matched. It checked each publication disposition, independent candidate-hash
binding, approval without qualifications, and accepted machine validation. For
every proof, the receipt accepts `lake-build`, `exact-target`,
`unchanged-statement` and `frozen-inputs` with `proof_accepted = true`.

The 6 November audit applies the same checks to the five units of the
previous section. It compares their ten files with the archived bundle
fingerprints, Library `d2fd0b68e11e9844d5da3650e7579d62588fd3fd` and the
workspace, and re-checks the ten actual-block proof fingerprints below against
that Library. All match. Both registered source PDF fingerprints also match.
These are publication facts; the note creates no new mathematical artifact or
proof receipt.

The five actual-block exact-target proof publications are:

| Unit; proof author | Accepted proof; independent reviewer | Machine receipt | Integration; publication Library |
| --- | --- | --- | --- |
| Actual support; Worker 189 | `6c262a0c-9f2b-4d66-a420-b71a9d39deab`; Reviewer 6338 | `a36ee2df-fa6b-4244-b6b5-d5937ccc2529` | `526f253a3b604e96a6383eb2aee9881c`; `cb42061b82d3b398d42ee1f25159daec0f54e40d` |
| Ambient-bound normalized nilpotence; Worker 1201 | `8b8c728b-9c3a-4d7b-883c-733ff5c365f5`; Reviewer 6412 | `4089b00c-4d87-4357-9089-e24981516ac5` | `cf7de2bd86fc43b2878cd4e9d3809b49`; `8f53f05bb76983088fd64f190658c6ac4c3edc1b` |
| Actual local basis; Worker 438 | `47aa3cb4-83e4-4624-9f52-da54ca8c830e`; Reviewer 6341 | `a06dccde-56be-4f1c-bcec-d00fe093a6c8` | `c42be500008f41ccb541b54bb6647720`; `cb42061b82d3b398d42ee1f25159daec0f54e40d` |
| Global all-integer basis; Worker 88 | `be0d44c9-7f0d-4a4b-a5d6-982202b782c4`; Reviewer 6414 | `2fe7dcc8-1c28-4a08-bb0e-bd20c35b6f7a` | `a36660876f2f44fc8e4205f3089ff414`; `8f53f05bb76983088fd64f190658c6ac4c3edc1b` |
| Three all-integer products; Worker 308 | `eb8d533b-33c0-4ab0-8a4e-5049c545340f`; Reviewer 6445 | `cfae27b6-a34d-45e5-b62b-268cfb7f0078` | `b389d249a8034c2eb7ede1045d4bc7da`; `7ad6e7323f2d14f5ccf8d30daa428878acda72c4` |

Their respective focused proof tasks are
`ab7a5cdd-c2fa-456f-96ff-709901a0aaf1`,
`9904665b-5eba-4b5f-97a2-77fae70ca338`,
`ba2f7a49-38c0-4c14-9f36-f04c2013a07a`,
`142df93d-9c12-41f7-bf7d-de3207d6da8d` and
`1c5fe324-8258-4884-a810-23b424d8eb2c`. These remain their authors' contributions;
this ledger imports no proof authorship.

The corresponding published proposition contributions are, in the same order,
`fff0ebcb-2335-4e4c-a3c2-ea05900521b1`,
`79e8f0f8-3520-4c65-94ad-8d2a04d4caba`,
`24a5d939-c42d-47eb-b314-256c8a2c7c1e`,
`55f9d0cc-a7ae-467a-8d0f-264393b10621` and
`e9e401b4-23a6-4d8b-92ca-faa229626593`. The audit also includes the earlier
eight-result table, representation coefficient statement
`5d74a62e-9871-498a-a6f3-8422f3134535`, decomposition statement
`769b13a0-1fbe-4050-b5ff-52ba2d69b320`, generic common-basis statement
`aee52bf6-e11f-4437-8f8b-7d0daba51bb3`, and the actual-block construction.

The five units of the occurring-character and polynomial-witness section are:

| Unit; author | Accepted contribution; independent reviewer | Machine receipt | Integration; publication Library |
| --- | --- | --- | --- |
| Occurring-character statement; Workers 709 and 1214 | `c5d11aa0-a042-45aa-a1b2-72f6bcb9eed5`; Reviewer 7376 | `6d9132f2-e135-41fc-86cd-163fc6f2ffa7` | `c754da97f3d4498cabd94fd7298cfb32`; `f6b45fe9b1a2248ff9b7cef7184c330d994e9512` |
| Occurring-character proof; Worker 1214 | `a4de9556-1637-41c5-9e40-60d904e05ec7`; Reviewer 7435 | `e3b5a8ab-9e0d-438f-93ac-614dbf11c4e6` | `18fd5a62bc2948dfb14defc36b57512a`; `e058cb4d3adbd71764731d87c4cbfcb5805696e8` |
| Polynomial-matrix definitions; Workers 709 and 308 | `4ce90481-60d5-49b5-8318-508ed948889a`; Reviewer 7383 | `19806bb9-078e-4b6e-bacc-532f8ba25452` | `1fc1d2eb64a04a39ac7b1b70736a185e`; `f6b45fe9b1a2248ff9b7cef7184c330d994e9512` |
| Polynomial-comparison statement; Worker 709, checked and submitted by Worker 308 | `41c543ed-3c86-404c-a523-08bf42e627cf`; Reviewer 7448 | `7fee4a98-d951-456a-84fa-fe012b8e9f01` | `886758fbb6204ad2a3f3e8a3ad3017e3`; `e058cb4d3adbd71764731d87c4cbfcb5805696e8` |
| Polynomial-comparison proof; Worker 88 | `89ceeaee-be5e-4c74-adda-0c6341b0d11e`; Reviewer 7519 | `bea3f37d-c36a-43a7-a530-397da5d6428c` | `8445ae8af906435ba15254d83a777b57`; `da0312e3777850c14b211f6245ff5b08af56f616` |

The two proof receipts accept `lake-build`, `exact-target`,
`unchanged-statement` and `frozen-inputs` with `proof_accepted = true`; the
statement and definition receipts accept their `lake-build` and
`declaration-kind` checks. The focused proof tasks are
`5ab726c4-0815-4cc6-a89d-32c425e58b32` and
`3136d318-c821-433b-852e-00149bc6b0db`; both are done.

The ten files of these units, each under
`Langlands/Representation/IntegerLattice/`, have these fingerprints in the
frozen bundles, Library `d2fd0b68` and the workspace:

| Stem | Lean SHA256 | Markdown SHA256 |
| --- | --- | --- |
| `OccurringCharactersStatement` | `141c0063cfa96e09949ffce4e27b333bceda1198d407a631b04cff8cefe71330` | `ddfa9c35d1ff930742abd6ea7f7cd8ff0565b86683c3d957f8c5fbec025d1935` |
| `OccurringCharactersProof` | `782b850dd5e75d158a46e4b5c54b816882a3b402d45420e5f2fcb3a9fb6e6d19` | `3b506f3c9317825b81f4f7d78bbfacbcd11aaa7cc97d3abca65aefc06dea4ac3` |
| `GeneralizedWeightPolynomial` | `4c1109219b3a61cd8275f727aef1edb12429ec42f51052a0e32e449f8ebc0a2e` | `4b2e1f07ffc3d62980b37fe3fde7e849e271edb4e5695e4f4c8bf6c7aa3b3a83` |
| `GeneralizedWeightPolynomialComparisonStatement` | `e12695dc2a977fcac3a8c0e170473ed93defbd6740ad0601f6fbf83861ba50cf` | `b1217c3241af3f154e0caf7ef14ce464ae32cf20a1140ea674c7dcde2ccd7abb` |
| `GeneralizedWeightPolynomialComparisonProof` | `2442e41c75f308f434b5d5088a3d2fe1aa9e88140f3cd566203d4a7f1be5409a` | `ad4f2ef61bfc2df1ebed21b032cacaed48ab43968bba9cc6643c537fb9c661af` |

The following frozen actual-block proof-pair fingerprints agree with both
Library `d2fd0b68` and the workspace. Each stem is under
`Langlands/Representation/IntegerLattice/` and has the indicated `.lean` and
`.md` suffixes.

| Proof stem | Lean SHA256 | Markdown SHA256 |
| --- | --- | --- |
| `GeneralizedWeightSupportProof` | `4ce5f64767d612d33d41ed0bf0424eae517607626b1249e54cd6f13bfbd02b2f` | `946e87d40a37d4edd874ab9a00c1e6d3d5d8d537771df49bfbf396d2203a94b5` |
| `NormalizedBlockNilpotenceProof` | `9e809e338b545406183243f405fa0d8b831f6e0f8d28acfb4715b6fb29917a96` | `512acec4fa2004dd2c77ec9b687821cfd0d969cfc8b184cc2bf15a84d47edb65` |
| `GeneralizedWeightBlockBasisProof` | `59b6f23d684371f333f80193a2feac2356136f1770efd9515dcd9a6b0d0b3a41` | `4b84c91b2164a95d480e4697fe48047c51e0ec0c4fe73e52ab88152de62f5886` |
| `GeneralizedWeightGlobalBasisProof` | `1448bbe9797f2ea566712a80a9995a79cbc5559bff49a49a41bd7f516f7724d1` | `fd82f12cd4f43e88c3b5b7440a3a25336e4339757ec45cf2e91ba1bb03f9171d` |
| `GeneralizedWeightProductProof` | `30d11cca1c1ceb49d2e751a4e0fe6ee3eb480e9073dc3ff5e957c4a655c24295` | `d3c638fba39cbe9eb2ab4d2265fe4175c53f2128e2b4345965bbd461de7e433d` |

Recovery compilation `53061516-348e-41b5-9e20-9ea0f433ae95`, made for the
1 November audit, successfully checked all five actual-block proof modules with
zero errors or warnings. Product declaration
inspection retained universe `u` and only `propext`, `Classical.choice` and
`Quot.sound`. This development check supplements the independent official
receipts; its own `proof_accepted` field is false. No additional compilation
or semantic acceptance follows from this documentation update.

The three families open at Library `1fb97c8e` have the actual-block proofs
recorded above. The three source-route comparisons left as deductions at
Library `61bb004f` now have the occurring-character and polynomial-comparison
proofs. Every row of the source-assertion ledger therefore cites a published
target. This note records that mapping; it declares neither Appendix C.III
completion nor parent completion.

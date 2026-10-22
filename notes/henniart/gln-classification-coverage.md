# GL_n classification: statement coverage and dependencies

Author: Worker 47, using the published cuspidal-induction pair of Worker 14
and tempered-block pair of Worker 15, whose grouping interface was coordinated
with Worker 19; the generic-product and general-factor finite-length pairs
of Worker 118; the unitary-generic pair of Workers 62 and 69;
the core multisegment pair of Workers 34 and 126;
the multisegment-compatibility pair of Workers 67, 126 and 111; and the
unitary-compatibility pair of Workers 17, 192 and 69.

This note maps twelve independently accepted and published statement pairs in
Library commit `dd9f9be571b3d712bb77031f3e6347bebd97a214`. Their Lean and
Markdown bytes were checked against their accepted version-1 bundles at this
commit. Every aggregate below is a proposition definition. Publication accepts
the formulation and its source correspondence; it does not prove the proposition.
The statement installments cover the assigned classification scope;
the substantive theorem proofs and source obligations remain as listed below.

Use the current Library by Lean module and declaration name. The commit pins
the versions described here, including the imported definitions. The linked
paired Markdown gives the exact retained source editions, fingerprints,
quantifiers, and longer derivations.

## Conventions shared by the statements

The groups are actual `GeneralLinear n F.Carrier`, with `F : PadicField p`
an actual finite extension of `ℚ_p`, for every prime `p`. A compatible
`T : F.TopologicalData` supplies topology and normalized absolute value.
All twelve aggregates quantify over every such `F` and `T`. Their clauses
usually require positive output rank. The core multisegment classification
also includes rank zero: Ze80 explicitly includes the empty socle parameter;
the empty head is a derived extension using the empty tensor product. The
square-integrable-block classification and the multisegment and unitary
compatibility families require positive output rank. Segment rank and length are intrinsically
positive. The complex representation carriers have explicit universes; they
are not required to be finite-dimensional. The exhaustion statements use
carriers in `Type (max uF uV)`, large enough for the actual induced spaces.
The cuspidal Hom and factor-matching clauses permit independent inducing
carrier universes.

Induction is from the standard **upper** block parabolic, with right
translation and covariance

    f(pg) = δ_P(p)^(1/2) σ(p) f(g).

Here `ν = |det|_F`, with `|ϖ|_F = q^(-1)`. For
`Δ = [ρ, ν^(m-1)ρ]`, the increasing product
`ρ × νρ × ⋯ × ν^(m-1)ρ` has Zelevinsky's `Z(Δ)` as its unique irreducible
subobject and the special representation `δ(Δ)` as its unique irreducible
quotient object. Ze80 §§3.1 and 9.1 distinguish these; H02 §2.6 calls the
second `St_m(ρ)`. The reverse product interchanges the two roles.

Representations, intertwiners, invariant subspaces, quotient spaces and
isomorphisms are actual constructions. The head and socle relations express
equal kernels of irreducible quotient maps and equal images of irreducible
embeddings. Their definitions do not supply existence. Segment parameters
use genuine supercuspidal isomorphism classes; equalities of ranks transport
the group index explicitly.

Square-integrability and temperedness are analytic predicates on absolute
smooth-dual matrix coefficients on the central quotient, using respectively
`L²` and `L^(2+ε)` for every `ε > 0`. They include admissibility and unitary
scalar central characters. The predicates quantify over all Borel Haar
measures, whose existence is proved in the Library. Unitarizability is
existence of an invariant positive Hermitian form. Genericity uses an actual
nonzero Whittaker functional for a continuous nontrivial unitary additive
character. None of these predicates is defined by a classification image.

## Published aggregates

The eleven classification aggregates have namespace `Langlands.Classification`.
The cuspidal aggregate has namespace `Langlands.CuspidalSupport`.
The module prefix in the table is `Langlands.Representation`.

| Module and paired explanation | Aggregate declaration | First publication commit |
| --- | --- | --- |
| [CuspidalSupport.NormalizedCuspidalInductionStatement](../../Langlands/Representation/CuspidalSupport/NormalizedCuspidalInductionStatement.md) | `PadicCuspidalInductionTheorems` | `00f9ac4d66cfd40043d36dbe31ea364e1316cde9` |
| [Classification.NormalizedProductFiniteLengthStatement](../../Langlands/Representation/Classification/NormalizedProductFiniteLengthStatement.md) | `PadicNormalizedProductFiniteLengthTheorems` | `5fabe967f891ba0c63610f6fc73911da14923207` |
| [Classification.SupercuspidalProductStatement](../../Langlands/Representation/Classification/SupercuspidalProductStatement.md) | `PadicSupercuspidalProductIrreducibilityTheorems` | `7db0c477a21f8471b1e5cff5f20d8ecb3dd2285b` |
| [Classification.SegmentConstituentStatement](../../Langlands/Representation/Classification/SegmentConstituentStatement.md) | `PadicSegmentConstituentTheorems` | `7465248e53e542902394c4c99a735557141755c3` |
| [Classification.SegmentConstituentCompatibilityStatement](../../Langlands/Representation/Classification/SegmentConstituentCompatibilityStatement.md) | `PadicSegmentConstituentCompatibilityTheorems` | `30e8a0cddc6dfcb47d746bc7ba1d6a38de7f4198` |
| [Classification.SegmentSquareIntegrabilityStatement](../../Langlands/Representation/Classification/SegmentSquareIntegrabilityStatement.md) | `PadicSegmentSquareIntegrabilityTheorems` | `e7e1cf75d8341a5fe60f25d4e6bb64d251921cbf` |
| [Classification.TemperedBlockStatement](../../Langlands/Representation/Classification/TemperedBlockStatement.md) | `PadicTemperedBlockTheorems` | `2839e6bae86085a8a220122cf5eb434176a57d4c` |
| [Classification.SegmentGenericStatement](../../Langlands/Representation/Classification/SegmentGenericStatement.md) | `PadicSegmentGenericTheorems` | `15eedb12537594b6a2fc1e60d81c041b5989d6c0` |
| [Classification.UnitaryGenericStatement](../../Langlands/Representation/Classification/UnitaryGenericStatement.md) | `PadicUnitaryGenericTheorems` | `4897b8b0eeea4fd4761194eb8fe4c2103d02aae4` |
| [Classification.MultisegmentClassificationStatement](../../Langlands/Representation/Classification/MultisegmentClassificationStatement.md) | `PadicMultisegmentClassificationTheorems` | `e3c2fa98be720f63c6981efbbdf15cd223329e76` |
| [Classification.MultisegmentConstituentCompatibilityStatement](../../Langlands/Representation/Classification/MultisegmentConstituentCompatibilityStatement.md) | `PadicMultisegmentConstituentCompatibilityTheorems` | `e3c2fa98be720f63c6981efbbdf15cd223329e76` |
| [Classification.UnitaryGenericCompatibilityStatement](../../Langlands/Representation/Classification/UnitaryGenericCompatibilityStatement.md) | `AllPadicUnitaryGenericCompatibilityStatement` | `e3c2fa98be720f63c6981efbbdf15cd223329e76` |

All twelve pairs are present with their accepted bytes at the snapshot above.
The following tables list the component proposition definitions, rather than
only the final aggregates. Grouped rows still identify every component name.

### Cuspidal induction and supercuspidal products

The first four names belong to `Langlands.CuspidalSupport`; the final two
belong to `Langlands.Classification`.

| Declaration | Content and exact source |
| --- | --- |
| `CuspidalEmbeddingTheorem` | An irreducible smooth representation is admissible and embeds in normalized induction from an irreducible cuspidal representation of an actual standard Levi. BZ77 Theorem 2.5, pp.446–447. |
| `CuspidalInductionLengthTheorem` | For irreducible **cuspidal** Levi data, the induced group module has finite length and an actual composition series with at most `B.length!` factors. BZ77 Theorem 2.8, pp.447–448. |
| `CuspidalInductionAssociationTheorem` | Association of two irreducible cuspidal data is equivalent to nonzero Hom, matching Jordan–Hölder factors with multiplicity, and a common irreducible subquotient. BZ77 Theorem 2.9(a), pp.447–448; §2.13(c), p.449, for minimal Weyl representatives. |
| `CuspidalInductionHomBoundTheorem` | The intertwiner space is finite-dimensional and its dimension is bounded by the finite set of associating minimal permutations. BZ77 Theorem 2.9(b), p.448, and §2.13(c), p.449. |
| `SupercuspidalProductIrreducibilityCriterion` | A product of supercuspidal blocks is irreducible when no pair satisfies `ρ_j ≅ νρ_i`, with ranks included in the comparison. BZ77 Theorem 4.2, p.454; §4.1 defines the product. |
| `SupercuspidalProductReducibilityTheorem` | Existence of such a pair makes the product reducible. BZ77 Remark 4.2(2), p.454, announces this; Ze80 Theorem 4.2, p.184, specializes to singleton segments. |

The cuspidal clause includes a factorial length bound under its cuspidality
hypothesis. The separate general-factor installment below states finite
length without that bound. BZ77 Remark 2.10, p.448, warns that the bound
can fail without cuspidality.

### General-factor induction finite length

The names in this and the remaining component tables belong to
`Langlands.Classification`.

| Declaration | Content and exact source |
| --- | --- |
| `IrreducibleProductFiniteLength F T` | The actual normalized upper product induction of arbitrary irreducible smooth complex positive-rank GL factors has finite group-module length. H02 §2.5, pp.594–595. No cuspidality or admissibility hypothesis is added. |
| `AdmissibleFiniteLengthProductPreservation F T` | The same conclusion holds when every factor is admissible and of finite group-module length. Derived from Ca95 Corollary 6.3.8, p.60, by the external tensor-product Levi translation recorded in the pair; both hypotheses are required. |

Both clauses use `IsFiniteLength` on the actual induced representation's
group-algebra module. They require positive total rank and an ordered
`BlockShape` with positive block ranks summing to it. Factor carriers have
universe `uV`, independent of the field universe `uF`; the induced function
carrier has universe `max uF uV`. No finite-dimensional carrier assumption
or numerical length bound is asserted. The second clause permits reducible
and zero factors.

The derived factor clause needs product-Levi admissibility, invariant-space
comparison, tensor exactness and a finite composition filtration with
irreducible tensor-product factors (BZ77 §2.7, p.447), followed by actual
normalized-induction preservation. BZ77 Theorem 2.5 provides irreducible
admissibility for an alternative route to the first clause. These remain
proof obligations. The separate `Langlands.GLAdmissibleFiniteLengthStatement`
concerns admissibility together with finite generation; it does not replace
either induction clause.

### Segment constituents

| Declaration | Content and exact source |
| --- | --- |
| `SegmentZelevinskyConstituentExistence` | Existence of a strong socle for the increasing product and the same strong head for every representative's decreasing product. Ze80 §3.1, pp.180–181, using Proposition 2.10, p.180. |
| `SegmentZelevinskyConstituentUniqueness` | Any two irreducible subrepresentations of the increasing product are isomorphic. Ze80 §3.1; derived from its strong uniqueness assertion. |
| `SegmentSpecialConstituentExistence` | Existence of a strong head for the increasing product and the same strong socle for every representative's decreasing product. Ze80 §9.1, p.197, using Proposition 2.10. |
| `SegmentSpecialConstituentUniqueness` | Any two irreducible quotients of the increasing product are isomorphic. Ze80 §9.1; derived from strong uniqueness. |
| `SegmentConstituentsDistinct` | For length at least two, the increasing-product subrepresentation and quotient are not isomorphic. Derived from Ze80 Theorem 2.2, pp.176–177, and Proposition 2.10 by reversing a nonempty segment graph's orientation. |
| `SegmentRankOneZelevinskyCharacter` | When the cuspidal rank is one and the representative acts by `χ ∘ det`, the socle acts by `ν^((m-1)/2)(χ ∘ det)`. Ze80 Example 3.2, p.181. |

### Segment compatibilities

| Declaration | Content and exact source |
| --- | --- |
| `SegmentConstituentRealTwistCompatibility` | Simultaneous real norm twists preserve and reflect all four weak/strong subrepresentation/quotient relations. Derived from BZ77 Proposition 1.9(f), p.445, and Ze80 §§3.1, 9.1. |
| `SegmentConstituentCharacterTwistCompatibility` | The same equivalences for determinant characters, with explicit open-kernel hypotheses on the two relevant GL ranks. Same derivation. |
| `SegmentConstituentContragredientCompatibility` | The smooth dual has the corresponding strong constituent relation for the segment beginning at the dual of the old endpoint. It quantifies over actual supercuspidal dual representatives and actual dual isomorphisms. Ze80 Propositions 3.3 and 9.4, pp.181 and 198. |
| `SegmentConstituentCentralCharacter` | Both increasing/decreasing products and their indicated constituents have scalar character `ω(z)^m |z|^(r*m*(m-1)/2)`. Derived from covariance, scalar triviality of the modulus, tensor products and inherited scalar action; real division is used. |

The dual formula is
`δ_m(ρ)^∨ ≅ ν^(1-m)δ_m(ρ^∨)`. H02 §2.6, p.595, drops the dual on
`ρ`; the statement follows Ze80's correct formula. The compatibility clause
does not construct a dual supercuspidal representative. Its existence is a
separate mathematical obligation, addressed by the statement
`Langlands.GeneralLinear.SupercuspidalContragredientStatement`. Ordinary smooth duality
is distinct from Hermitian duality.

### Special representations and square-integrability

| Declaration | Content and exact source |
| --- | --- |
| `SegmentSpecialEssentialSquareIntegrability` | Each special segment quotient is essentially square-integrable. Ze80 §9.3, p.198; H02 §2.6, p.595. |
| `SegmentEssentialSquareIntegrableClassification` | An irreducible positive-rank representation is essentially square-integrable iff it is the strong head for some segment, with explicit rank transport. Ze80 §9.3; Au04 Theorem 6.1, p.18, for a later written converse route. |
| `SegmentSpecialParameterUniqueness` | Isomorphic special heads have equal segment parameters, including genuine cuspidal class, rank and length. H02 §2.6 explicitly states the bijection. |
| `SegmentSpecialSquareIntegrabilityCriterion` | For a special quotient, square-integrability is equivalent both to a unitary scalar central character and to unitarizability. Derived from essential square-integrability, central-character normalization and Ca95 Proposition 2.5.4, p.29. |
| `SegmentCenteredSpecialSquareIntegrability` | If the initial supercuspidal is unitarizable, the special quotient twisted by `ν^(-(m-1)/2)` is square-integrable and unitarizable. Derived from the preceding criterion and scalar-character computation; Au04 Proposition 5.5 and Theorem 5.13(g), pp.15 and 18, record the centered character and its preservation. |
| `EssentialSquareIntegrabilityExponentUniqueness` | An irreducible essentially square-integrable positive-rank representation has exactly one real square-integrability normalization exponent. Derived by evaluating its unitary scalar central characters at a uniformizer. |

The two equivalences in the special criterion apply only under the stated
segment-quotient hypothesis. They do not assert those converses for arbitrary
irreducible representations.

### Tempered blocks and equal-exponent grouping

| Declaration | Content and exact source |
| --- | --- |
| `SquareIntegrableBlockInduction` | A finite product of irreducible square-integrable unitarizable GL blocks is irreducible, unitarizable and analytically tempered. Ja77 Corollary 3.3, p.99; JS83 §1.2, p.109; Ku94 §1.1 and Proposition 2.2.1, pp.368 and 373. |
| `SquareIntegrableBlockGenericity` | This product is generic for every allowed additive character. JS83 §1.2, pp.108–109, equation (1.2.3); Ku94 §2.3, p.374. |
| `TemperedBlockExhaustion` | Every irreducible analytically tempered positive-rank representation is isomorphic to such a product. Ku94 Proposition 2.2.1, p.373; Ro82 Proposition 12, p.212. Ca95 Proposition 2.5.4 supplies the block invariant forms in this formulation. |
| `TemperedBlockUniqueness` | Two such products are isomorphic iff the blocks match by a permutation, equal ranks and actual block isomorphisms. Derived from Ku94 Proposition 1.2.3 and Theorem 1.2.5(b),(d), pp.369–371, and the nonlinkage argument on p.373. This is uniqueness of square-integrable blocks, not arbitrary tempered blocks. |
| `TemperedBlockInduction` | Products of irreducible tempered GL blocks are irreducible, unitarizable and tempered. Ku94 §2.2, p.373: expand into square-integrable blocks and apply induction transitivity. |
| `TemperedUnitarityAndGenericity` | Every irreducible tempered representation is unitarizable and generic for every allowed character. Derived from exhaustion and the first two clauses; Ku94 §2.3, p.374. |
| `SquareIntegrableEqualExponentGrouping` | Weakly decreasing square-integrable Langlands data normalize and group along maximal consecutive equal-exponent runs into strictly decreasing tempered data, with actual within-run induction isomorphisms and an isomorphism of the standard modules. Ku94 §2.2, p.373, equations (2.2.2)–(2.2.3), with the explicit finite grouping derived as explained in the pair. |

The grouping clause specifies a monotone surjection on indices, equality of
exponents, ordered bijections onto its fibers, rank equalities and actual
induction isomorphisms. Strict decrease of the new exponents forces the
fibers to be exactly the equal-exponent runs. It asserts no quotient theorem.
All induction irreducibility clauses here are specific to GL_n.

### Segment products and genericity

| Declaration | Content and exact source |
| --- | --- |
| `SegmentSocleProductIrreducibility` | Products of segment socles are irreducible iff their segment multiset is pairwise nonlinked. Ze80 Theorem 4.2, p.184. |
| `SegmentHeadProductNondegeneracy` | Every product of special heads, including reducible products, has a nonzero Whittaker functional for every allowed character. Ze80 Theorem 9.7(a), p.199, and §9.8. |
| `SegmentHeadProductIrreducibility` | Products of special heads are irreducible iff the segments are pairwise nonlinked. Ze80 Theorem 9.7(a), pp.198–199, and §§9.8–9.9. |
| `SegmentHeadProductGenericity` | Such products are generic iff pairwise nonlinked. Derived from Ze80 Theorem 9.7(a), with BZ77 Theorem 2.5 for admissibility. |
| `GenericSegmentProductExhaustion` | A smooth representation is generic iff isomorphic to an unlinked product of special heads. Ze80 Theorem 9.7(b), p.199, and §9.10, p.201; the reverse direction uses 9.7(a). |
| `GenericSegmentProductUniqueness` | Two unlinked products of special heads are isomorphic iff their segment multisets agree, including multiplicities. Ze80 Theorem 9.7(b) and §9.10. |
| `ZelevinskySocleGenericity` | Any representation satisfying `a.IsZelevinskySocle` is generic iff every segment of `a` has length one. Ze80 §9.10, p.201, following Theorem 8.1, p.195. |

The product criteria impose no precedence ordering and allow repeated segments.
`Whittaker.IsGeneric` includes irreducibility and admissibility, whereas
`Whittaker.HasFunctional` alone does not. The last clause does not replace
length one by nonlinkage and does not assert existence of a socle for every
multisegment. The separate `MultisegmentSocleExistence` proposition below
now states that existence; neither statement supplies its proof.
The derivative-to-functional translation is explained in the paired note;
it remains a proof obligation.

### Multisegment and square-integrable-block classification

Both the segment-socle and segment-head classifications order their segments
so that no earlier segment precedes a later one. Weakly decreasing unitary
exponents are a separate order on essentially square-integrable blocks.
Passing between the two uses commutation of unlinked special-head factors;
it does not assert permutation invariance of arbitrary reducible products.

| Declaration | Assertion | Source or derivation |
| --- | --- | --- |
| `MultisegmentNonprecedenceEnumeration` | Every multisegment has a nonprecedence enumeration whose degree sum is its degree. | Ze80 §6.5, p.189; the degree identity is bookkeeping for the published multiset degree. |
| `MultisegmentConstituentDataExistence` | Every multisegment has ordered actual segment-socle data and ordered actual segment-head data, of its degree. | Derived combination of Ze80 §§3.1, 6.5, 9.1: enumeration and existence of individual segment constituents. No full-product constituent is assumed. |
| `OrderedMultisegmentSocleExistence` | Every permitted product of segment socles has an irreducible socle. | Ze80 Theorem 6.1(a), p.188; §§6.2–6.3 give its proof route. |
| `OrderedMultisegmentSocleProductIndependence` | Ordered socle products with the same multisegment are isomorphic as full representations. | Ze80 Proposition 6.4(2), p.189; actual representatives are transported by the induction functor. |
| `OrderedMultisegmentSocleClassification` | Any irreducible subrepresentations of two permitted products are isomorphic iff their multisegments agree. | Ze80 Theorem 6.1(a,b); uniqueness in (a) permits the weaker subrepresentation hypotheses. |
| `MultisegmentSocleExistence` | Every multisegment has a socle realization at its degree. | Ze80 §§6.1(a), 6.5, using enumeration and individual block existence. |
| `MultisegmentSocleExhaustion` | Every irreducible smooth representation of rank `n` is such a socle, and the parameter's degree equals `n`. | Ze80 Theorem 6.1(c) and §6.5. |
| `MultisegmentSocleClassification` | Two socle realizations at the same rank are isomorphic iff their multisegments are equal. | Ze80 Theorem 6.1(b) and §6.5. |
| `OrderedMultisegmentHeadExistence` | Every permitted product of segment heads has an irreducible head. | Ro82 §4.3 Theorem 3(a), p.211. |
| `OrderedMultisegmentHeadClassification` | Any irreducible quotients of two permitted products are isomorphic iff their multisegments agree. | Ro82 Theorem 3(a,b), pp.211–212; uniqueness permits the weaker quotient hypotheses. |
| `MultisegmentHeadExistence` | Every multisegment has a head realization at its degree. | Ro82 Theorem 3(a), with Ze80 enumeration and segment-head existence. |
| `MultisegmentHeadExhaustion` | Every irreducible smooth representation of rank `n` is such a head, and the parameter's degree equals `n`. | Ro82 Theorem 3(c), p.212. |
| `MultisegmentHeadClassification` | Two head realizations at the same rank are isomorphic iff their multisegments agree. | Ro82 Theorem 3(b), expressed as multiset equality. |
| `MultisegmentConstituentRepresentativeInvariance` | Each multisegment relation is invariant under an actual isomorphism of its output. | Internal derived assertion: compose the injective/surjective constituent intertwiners with the isomorphism and its inverse, preserving images or kernels. |
| `SquareIntegrableLanglandsHeadExistence` | Every positive-rank datum of essentially square-integrable blocks with weakly decreasing unitary exponents has an irreducible head. | H02 §2.8, p.596. |
| `SquareIntegrableLanglandsQuotientUniqueness` | Any two irreducible quotients of the same such product are isomorphic. | H02 §2.8, consequence of its unique irreducible quotient. |
| `SquareIntegrableLanglandsExhaustion` | Every positive-rank irreducible smooth representation is the head of such genuine block data. | H02 §2.8, surjectivity of the nonzero free commutative monoid on essentially square-integrable classes. |
| `SquareIntegrableLanglandsClassification` | Irreducible quotients of two such data are isomorphic iff their blocks match up to permutation, rank equality and actual isomorphism. | H02 §2.8, the bijection and independence of the permitted ordering. |

The ordered clauses quantify over every permitted actual datum; the
multisegment relations existentially quantify over such data. The four
square-integrable-block clauses require positive total rank and permit equal
exponents. The earlier grouping clause then passes to strictly ordered
tempered data; the companion regular-chamber theorem remains separate.

### Multisegment compatibilities

| Declaration | Lean assertion | Original source or explicit derivation |
| --- | --- | --- |
| `MultisegmentConstituentRealTwistCompatibility F T` | For every positive rank, multisegment `a`, real `s`, and actual smooth `π`, both constituent relations are equivalent to their versions for `a.twist s` and `π.twist (ν^s)`. | Ta86 §1.8, pp.342–343, for socles; Proposition 5.6(ii), p.363, for heads. |
| `MultisegmentConstituentCharacterTwistCompatibility F T` | For a character `χ : Fˣ →* ℂˣ` with open kernel, twist every segment base by `χ ∘ det`, keep its length, and map the entire multiset. Each constituent relation is equivalent to that for the actual `χ ∘ det` twist of `π`. | Derived from BZ77 Proposition 1.9(f), p.445, and the constituent relations. |
| `MultisegmentConstituentContragredientCompatibility F T` | For any finite family `Δ_i` and supercuspidal representatives `B_i` of their endpoints, there exist supercuspidal `Bv_i` genuinely equivalent to their actual smooth duals. The segments beginning at `[Bv_i]` with the original lengths form `av`. For every positive rank and `π`, a socle or head relation for `a` implies the corresponding relation for `av` and the actual smooth dual of `π`. | Ze80 §3.3, p.181, and Theorem 7.10, pp.194–195; Ta86 §1.15, p.344, and Proposition 5.6(iii), p.363; Ca95 Proposition 2.1.10 and Corollary 2.1.13, p.22, and Theorem 5.3.1(a–b), pp.48–49, for existence of supercuspidal dual representatives. |
| `SquareIntegrableLanglandsHeadContragredientCompatibility F T` | If `d : SquareIntegrableLanglandsDatum n` and `π` is its Langlands head, the actual smooth dual of `π` is the irreducible head of normalized induction on `d.shape.reverse` of the actual smooth dual blocks `(d.blocks i.rev)^∨`. | H02 §2.8, p.596. |
| `MultisegmentConstituentCentralCharacter F T` | If `A_i` represents the beginning of `Δ_i` and has prescribed scalar character `ω_i`, either constituent of `{Δ_i}` has the product of the segment scalar characters described below. | Derived from BZ77 §§1.6 and 1.8, pp.443–444, and the published segment scalar-character formula; it is not asserted to be part of Ta86 §5.6. |

These five clauses require positive output rank. The endpoint-dual
representatives are an existential conclusion, with one family working for
all output representations. Both constituent-dual conclusions are forward
implications; they do not assume arbitrary smooth biduality. The reversed
block clause states a head relation for the concrete reversed dual product,
without assuming a new classified datum. This differs from the full-product
same-parabolic duality in the unitary-compatibility family below.

For a segment beginning with a rank-`r_i` representative of scalar character
`ω_i` and length `m_i`, its scalar factor is
`ω_i(z)^m_i |z|_F^(r_i*m_i*(m_i-1)/2)`. The multisegment formula multiplies
these factors with multiplicities. Prescribed base scalar characters are
hypotheses; their existence for arbitrary representations is not asserted.

### Unitary generic classification

| Declaration | Content and exact source |
| --- | --- |
| `UnitaryGenericConstruction` | Every valid family of actual unitary square-integrable blocks induces a unitarizable representation generic for every allowed character. Ta86 Theorem D(i), pp.338–339, with the generic specialization via Ze80 Theorem 8.1, Corollary 8.3, Theorem 9.7 and §9.10, and BZ77 §§4.5–4.7. |
| `UnitaryGenericExhaustion` | Every generic unitarizable representation is isomorphic to an induction of a valid family. Ta86 Theorem D(ii) and elimination of nongeneric Speh factors; H00 Appendix A.2, p.453. |
| `UnitaryGenericParameterUniqueness` | Two valid inductions are isomorphic iff their parameter families match by a rank-preserving bijection, equal real exponents and actual block isomorphisms. Ze80 Theorem 9.7(b) and §9.10; Ta86 §§5.3–5.4, p.362; H02 §2.8, p.596. |

The same module defines five supporting predicates. They do not assume
classification:

| Predicate | Meaning |
| --- | --- |
| `IsUnitarySquareIntegrableBlockFamily` | Each block is irreducible, unitarizable and analytically square-integrable. |
| `HasStrictUnitaryExponents` | Every exponent satisfies `-1/2 < s_i < 1/2`. |
| `SameUnorderedUnitaryParameters` | A bijection matches ranks, exponents and actual block isomorphisms, preserving multiplicities. |
| `HasHermitianSymmetricParameters` | The same matching relation identifies `(s_i, δ_i)` with `(-s_i, δ_i)`. |
| `IsUnitaryGenericDatum` | The block conditions, strict bounds and Hermitian symmetry hold; the block shape supplies positive ranks and their sum. |

For unitarizable admissible blocks, Hermitian duality fixes `δ_i` and negates
`s_i`; it does not require ordinary self-duality of `δ_i`. The semilinear
identification and other compatibilities are stated in the separate published
compatibility family below.
Ta86's generic specialization uses its rectangular-parameter identity
(§7.4 and Appendix A.10(iii)) to identify Speh size with Zelevinsky segment
length, then the singleton criterion and the top-derivative product filtration
to exclude Speh size greater than one. The paired note records this derivation
and its unproved inputs. The three clauses do not assert those inputs as data.

### Unitary inducing-parameter compatibilities

| Declaration | Content and exact source or derivation |
| --- | --- |
| `UnitaryAdmissibleHermitianClause` | For every admissible smooth representation and every invariant positive form, an evaluation-prescribed equivariant conjugate-linear equivalence identifies its carrier with its actual smooth dual. Concrete refinement of Ta86 §2.1, p.345; surjectivity uses compact-open averaging and finite-dimensional fixed spaces. Irreducibility is not required. |
| `UnitaryBlockRealTwistHermitianClause` | For every invariant positive form on an irreducible square-integrable block, its pairing identifies `ν^(-s) δ` conjugate-linearly with `(ν^s δ)^∨`. Derived from Ta86 §§2.1 and 5.3–5.5, pp.345 and 362; the form is invariant on `δ`, not asserted invariant on its nonunitary twist. |
| `RealTwistOrdinaryDualClause` | For any smooth block, `(ν^s δ)^∨ ≅ ν^(-s) δ^∨`, without admissibility or unitarity hypotheses. BZ77 §1.5, p.443. |
| `UnitaryBlockOrdinaryDualClause` | The actual smooth dual of an irreducible unitarizable square-integrable block has all three properties. Derived from smooth admissible duality, the Hermitian identification and absolute coefficient comparison, as detailed in the pair. |
| `TwistedProductOrdinaryDualClause` | For arbitrary admissible blocks, the smooth dual of the normalized product is the same ordered upper product of dual blocks with negated exponents. BZ77 Proposition 1.9(d,e), p.445, and Ca19 Proposition III.1.1, pp.1–2; extending BZ77 §1.6 tensor duality to arbitrary admissible blocks is an explicit derived obligation. |
| `TwistedProductCharacterTwistClause` | An arbitrary smooth determinant-character twist passes through the normalized product by twisting every block; the real exponents remain unchanged. BZ77 Proposition 1.9(f), p.445. |
| `UnitaryBlockCharacterTwistClause` | A unit-modulus smooth determinant twist preserves and reflects the conjunction of irreducibility, unitarizability and square-integrability. Derived from invariant submodules, positive forms and absolute coefficient functions. |
| `TwistedProductCentralCharacterClause` | With prescribed block scalar characters, the product has scalar character `(∏ i, ω_i) |·|_F^(∑ i, n_i s_i)`, together with both pointwise forms. Derived from BZ77 §1.8, pp.444–445, scalar modulus one and `det(z I_(n_i)) = z^(n_i)`. No irreducibility or admissibility is required. |
| `ScalarCharacterTwistDualClause` | A smooth determinant twist changes a prescribed scalar character to `ω χ^n`; ordinary smooth duality changes it to `ω⁻¹`. Derived from the determinant identity and inverse group action on the dual. |

All nine clauses require positive rank. The field and block-carrier universes
are independent. Hermitian equivalences are conjugate-linear and prescribed
by evaluation against each given positive form; no canonical form or
ordinary self-duality is assumed. Normalized full-product duality keeps the
same ordered parabolic. Reversing blocks in the multisegment Langlands-head
clause instead restores the decreasing-exponent order required for its
quotient classification.

## Definition dependencies at the pinned Library version

The following are exact direct imports of the twelve entry modules at
`dd9f9be571b3d712bb77031f3e6347bebd97a214`. That commit also pins their
transitive imports and paired explanations. No draft import is used.
`R` below abbreviates `Langlands.Representation`; `G` abbreviates
`Langlands.Group.GL`.

| Entry module after `R.` | Direct imports |
| --- | --- |
| `CuspidalSupport.NormalizedCuspidalInductionStatement` | `R.CuspidalSupport.LeviDefinitions`, `R.Category.Subquotients`, `R.Filtration.ObjectDefinitions`, `R.Induction.Definitions`, `G.BlockModulus` |
| `Classification.NormalizedProductFiniteLengthStatement` | `R.Induction.BlockFactors`, `R.Category.Subquotients` |
| `Classification.SupercuspidalProductStatement` | `R.Classification.SupercuspidalTwist`, `R.Induction.BlockFactors` |
| `Classification.SegmentConstituentStatement` | `R.Classification.Segments` |
| `Classification.SegmentConstituentCompatibilityStatement` | `R.Classification.Segments`, `R.Smooth.Contragredient.Definitions` |
| `Classification.SegmentSquareIntegrabilityStatement` | `R.Classification.Segments`, `R.Classification.Tempered` |
| `Classification.TemperedBlockStatement` | `R.Classification.LanglandsData`, `R.Whittaker.GeneralLinear` |
| `Classification.SegmentGenericStatement` | `R.Classification.LanglandsData`, `R.Classification.SegmentConstituentStatement`, `R.Whittaker.GeneralLinear` |
| `Classification.UnitaryGenericStatement` | `R.Classification.LanglandsData`, `R.Whittaker.GeneralLinear` |
| `Classification.MultisegmentClassificationStatement` | `R.Classification.LanglandsData` |
| `Classification.MultisegmentConstituentCompatibilityStatement` | `R.Classification.LanglandsData`, `R.Classification.SegmentConstituentCompatibilityStatement`, `R.Classification.ConstituentCompatibility`, `R.Smooth.Contragredient.LawsProof`, `G.ReverseBlocks` |
| `Classification.UnitaryGenericCompatibilityStatement` | `R.Classification.LanglandsData`, `R.Classification.ConstituentCompatibility`, `R.Smooth.Contragredient.LawsProof`, `R.Unitary.Twist`, `R.Parabolic.NormalizedCompatibilityStatement`, `R.Parabolic.NormalizedInductionStatement` |

The imported statement modules supply proposition targets, not proofs;
none is used as an assumed theorem. The transitive project closure consists
of 89 modules with paired Markdown at this commit. The principal imported
construction interfaces are:

| Published definition pair | Use in the statements |
| --- | --- |
| [Category.Basic](../../Langlands/Representation/Category/Basic.md) and [Category.Subquotients](../../Langlands/Representation/Category/Subquotients.md) | Smooth representations, genuine isomorphism classes, actual subquotients and irreducibility. |
| [CuspidalSupport.LeviDefinitions](../../Langlands/Representation/CuspidalSupport/LeviDefinitions.md) and [Filtration.ObjectDefinitions](../../Langlands/Representation/Filtration/ObjectDefinitions.md) | Cuspidal Levi data, association, minimal permutations, composition series and multiplicity-sensitive Jordan–Hölder matching. |
| [Induction.BlockFactors](../../Langlands/Representation/Induction/BlockFactors.md) | Actual tensor-product block representations and `normalizedProductInductionFunctor`. |
| [Classification.SupercuspidalTwist](../../Langlands/Representation/Classification/SupercuspidalTwist.md) | Determinant character twists of actual supercuspidal representations and their isomorphism classes. |
| [Classification.ConstituentRelations](../../Langlands/Representation/Classification/ConstituentRelations.md) | Weak and strong constituent relations and actual scalar-character predicates. |
| [Classification.Segments](../../Langlands/Representation/Classification/Segments.md) | Segment supports, linkage and precedence, multisets of segments, increasing/decreasing induction and representative-independent constituent relations. |
| [Classification.Tempered](../../Langlands/Representation/Classification/Tempered.md) | Analytic square-integrability and temperedness on the central quotient; existence of a Borel Haar measure. |
| [Classification.LanglandsData](../../Langlands/Representation/Classification/LanglandsData.md) | Actual standard modules, square-integrable and tempered Langlands data, and multisegment head/socle relations. No existence theorem for a head is a constructor field. |
| [Smooth.Contragredient.Definitions](../../Langlands/Representation/Smooth/Contragredient/Definitions.md) | The actual smooth part of the algebraic dual. |
| [Smooth.Contragredient.LawsProof](../../Langlands/Representation/Smooth/Contragredient/LawsProof.md) and [Unitary.Twist](../../Langlands/Representation/Unitary/Twist.md) | Actual smooth-dual smoothness and invariant-positive-form transport under unitary twists. These construction proofs do not prove the compatibility aggregates. |
| [Classification.ConstituentCompatibility](../../Langlands/Representation/Classification/ConstituentCompatibility.md) and [GL.ReverseBlocks](../../Langlands/Group/GL/ReverseBlocks.md) | Algebraic constituent interfaces and the concrete reversed block shape. |
| [Unitary.Basic](../../Langlands/Representation/Unitary/Basic.md) and [MatrixCoefficient.ModuloCenter](../../Langlands/Representation/MatrixCoefficient/ModuloCenter.md) | Invariant positive forms and descended absolute matrix coefficients. |
| [Whittaker.GeneralLinear](../../Langlands/Representation/Whittaker/GeneralLinear.md) | Standard upper-unipotent characters and nonzero equivariant Whittaker functionals. |

These imports give meanings to propositions. A mathematical route mentioning
induction transitivity, duality, classification or Haar-measure independence
does not make those results hypotheses, proofs, or constructor fields in
the twelve statement pairs.

## Statement scope and adjacent assignments

The twelve published pairs cover the classification statement installments
required by task `992634be-7c14-4c9f-aba0-be59fc810b85`, including both the
cuspidal bound and general-factor induction finite length. The latter was
published through focused task `4e7abbfd-8651-473e-b8f7-78f9228e3b3e`,
revision 1. These task references identify coordination scope; the module
names and Library pin above identify the mathematical content. This coverage
claim concerns statements and their source/dependency correspondence.

The regular-chamber quotient theorem and Jacquet exponent criteria belong to
the companion branch described in the [Jacquet source map](../jacquet/source-map.md).
The grouping clause above supplies its passage from weakly ordered
square-integrable data to strictly ordered tempered data. Whittaker uniqueness,
local factors and local converse are separate assignments.

## Remaining proof and source obligations

None of the substantive component propositions listed here has a proof in
these twelve statement files. Their paired Markdown records the proof routes
and limitations. The following boundaries are especially relevant when
selecting future proof tasks.

- **Cuspidal structure and finite length.** BZ77 refers elsewhere for
  Theorem 2.5; its proofs of 2.8–2.9 use the geometric lemma, quasicuspidal
  structure and Jordan–Hölder theory. The Weyl representative count needs
  its actual identification. Ca95 Corollary 6.3.8, p.60, assumes an
  **admissible** finite-length Levi representation. The product-factor
  translation needs product compact-open invariant-space comparison,
  tensor exactness, and a composition filtration with irreducible tensor
  factors, using BZ77 §2.7. Actual normalized-induction exactness,
  transitivity, finite-length preservation and normalization comparison
  remain proof obligations.
- **Basic reducibility.** Ze80 Proposition 1.11, p.175, gives a sketch of
  reducibility of `ρ × νρ`. A complete written proof of that step remains
  a source obligation. It also enters the segment graph argument and the
  linked-product converse. Induction exactness and composition-factor
  commutativity are separate mathematical inputs.
- **Square-integrable converse.** Ze80 §9.3 omits its converse proof.
  Au04 supplies a written route through duality and Casselman's criterion.
  Its Aubert and Schneider–Stuhler original inputs, including the Aubert
  erratum, have not been audited in this branch. Ze80 §9.17 is a conjecture
  in that original. The corrections to Au04 and the exact boundary are
  retained in the [classification source note](gln-classification-sources.md)
  and the square-integrability pair.
- **Core multisegment classification.** Positive-twist nonperiodicity,
  nonprecedence enumeration, representative transport, the Ze80 §6
  classification and Rodier's upstream classification inputs remain proof
  obligations. Ze80 §9.17 is not a proof source for head classification.
  The empty head requires the explicitly derived empty-tensor extension.
- **Multisegment duality and covariance.** Ze80 Theorem 7.10 supplies the
  socle-to-socle duality statement; dualizing an embedding alone only gives
  a quotient. Ta86 §5.6 cites Ze80 §9.5 for a formula actually in §9.4 and
  uses Jacquet's *Principal L-functions* equation (3.3.13) in its head-duality
  argument; that upstream original remains unread for this contribution.
  Supercuspidal-dual preservation, induction/dual and induction/twist
  compatibility, and scalar covariance remain proof obligations.
- **Hermitian and admissible dual comparisons.** The evaluation-prescribed
  equivalence for each positive form needs compact-open averaging and
  finite-dimensional fixed-space surjectivity. No algebraic-carrier Riesz
  theorem is assumed. The full-product duality clause extends BZ77's
  irreducible-admissible tensor comparison to arbitrary admissible blocks;
  this extension, smooth admissible biduality, and coefficient comparison
  under duality and unitary twists remain proof obligations.
- **Analytic comparisons.** Haar-measure independence, invariance of
  integrability under inversion and unitary twists, decomposition of smooth
  quasicharacters into a unitary part and a real norm power, scalar central
  character arguments, and comparison with exponent-based temperedness
  require proofs. The analytic predicates do not assume those comparisons.
- **Tempered exhaustion.** Ja77 proves unitary induction irreducibility and
  genericity, but contains no tempered exhaustion or unordered uniqueness
  theorem. Ro82 Proposition 12 and Ku94 Proposition 2.2.1 are explicit
  statement sources; their Jacquet citation does not provide the missing
  exhaustion proof. A sufficient proof source for tempered support and its
  analytic comparison remains to be audited. The uniqueness statement has
  the separate multisegment-classification route described in its pair.
- **Smooth/unitary comparison and genericity.** Ja77 uses Hilbert spaces,
  Mackey induction, a transpose parabolic and mirabolic genericity.
  Comparing these to the smooth upper-normalized product and nonzero
  Whittaker functionals requires explicit results. JS83 provides the direct
  smooth formulation. Induced invariant forms, Whittaker functionals,
  character independence, permutation isomorphisms, transitivity and the
  finite grouping construction remain proof obligations.
- **Unitary generic specialization.** Ta86 Theorem D has strict
  `0 < α < 1/2` for complementary pairs. Removing Speh sizes greater than
  one requires the genericity/derivative argument, not irreducibility alone.
  Ta86's characteristic-zero appendix provides a written route avoiding
  its earlier unpublished involution input, but its deep global inputs are
  not formalized here. H00 Appendix A.2 uses Hermitian pairing; it does not
  require each square-integrable block to be ordinarily self-dual.

Source abbreviations are BZ77 (Bernstein–Zelevinsky, 1977), Ze80
(Zelevinsky, 1980), H02 and H00 (Henniart, 2002 and 2000), Ta86
(Tadić, 1986), Au04 (Auel's 2004 memoir), Ca95 (Casselman's 1 May 1995
draft), Ca19 (Casselman's *Jacquet modules*, revision 29 April 2019),
Ja77 (Jacquet, 1977), JS83 (Jacquet–Shalika, 1983), Ro82
(Rodier, 1982) and Ku94 (Kudla, 1994). Page numbers above are printed
pages. The twelve paired explanations and the
[registered-source record](sources.md) give retained editions and reading
extents; this note makes no additional claim of complete-paper reading.

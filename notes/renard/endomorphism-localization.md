# Renard A.III.1: endomorphism-localization proofs

Worker 709, 31 October 2026, under whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857` revision 2. This note records five
independently accepted and published proof aggregates over the actual
endomorphism localization. It supplements the earlier
[C.II prerequisite audit](stable-quotients.md); that audit did not verify
these successors. The [whole-book ledger](coverage.md) retains the rest of
Appendix A and every other unassigned assertion.

## Source and reading

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`. The original file is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 709 reread A.III.1, printed251–253/PDF257–259, including the universal
problem, uniqueness discussion, example 5, subsequent unnumbered lemma,
converse paragraph and corollary. PDF259 was also visually inspected.
The nonunital conventions on printed6/PDF12 were read previously.

The supplementary registered author errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were checked on PDF18–19. Those pages contain no correction to the passages
covered here. This bounded older-edition check does not replace the 2026
original. The [Appendix A discrepancy note](appendix-a-corrections.md)
explains example 4's stronger, incorrect scalar-inverse parenthesis; the
constructions here use actual inverse endomorphisms.

## Actual objects and exact targets

Write `E` for namespace `Langlands.Renard.EndomorphismLocalization`.
For a commutative unital ring R, an arbitrary R-module V and
`a : Module.End R V`, the published
[construction](../../Langlands/Algebra/RenardEndomorphismLocalization.md)
gives `E.Localized a`, `E.iota a`, `E.localizedEnd a` and
`E.localizedInv a`. These are the actual localization, canonical linear map,
invertible localized operator and its inverse. All five proof aggregates
below import their published Prop-valued statements unchanged.

| Passage | Published theorem and exact target | Content credited here |
| --- | --- | --- |
| Lemma (i), printed253/PDF259, and derived kernel/exhaustion formulations | `E.kernelExhaustionStatements : E.KernelExhaustionStatements.{u,v}` in [RenardEndomorphismLocalizationKernelProof](../../Langlands/Algebra/RenardEndomorphismLocalizationKernelProof.md) | The elementwise kernel criterion, supremum of power kernels, injectivity of the canonical map when a is injective, and literal inverse-power exhaustion |
| Lemma (ii), quotient and localization comparison | `E.quotientLocalizationStatements : E.QuotientLocalizationStatements.{u,v}` in [RenardEndomorphismQuotientProof](../../Langlands/Algebra/RenardEndomorphismQuotientProof.md) | Injectivity of the induced quotient operator and its canonical localization map; a unique compatible equivalence between the two actual localizations |
| Converse paragraph after the lemma | `E.localizationExtensionStatements : E.LocalizationExtensionStatements.{u,v,x,w}` in [RenardLocalizationExtensionProof](../../Langlands/Algebra/RenardLocalizationExtensionProof.md) | The universal property of an injective inverse-power extension, and its unique comparison with the actual localization |
| Unnumbered corollary | `E.surjectiveIotaQuotientStatements : E.SurjectiveIotaQuotientStatements.{u,v}` in [RenardSurjectiveLocalizationProof](../../Langlands/Algebra/RenardSurjectiveLocalizationProof.md) | Surjectivity of the actual canonical map gives a unique compatible equivalence from the localization to the actual power-kernel quotient |
| Final B-module sentence of example 5, printed252/PDF258 | `Langlands.Renard.AlgebraActionLocalization.universalPropertyStatements : Langlands.Renard.AlgebraActionLocalization.UniversalPropertyStatements.{u,v,w,x}` in [RenardAlgebraLocalizationUniversalProof](../../Langlands/Algebra/RenardAlgebraLocalizationUniversalProof.md) | Unique factorization among actual B-linear intertwiners, into every independently sized compatible target with invertible operator |

Each aggregate includes its general commutative-ring version and an explicit
arbitrary-field specialization. The field conclusions correspond to Renard's
vector spaces. The ring generalizations, the full kernel equality, and the
specified canonical uniqueness of the comparison equivalences are internal
strengthenings or precise derived formulations, not additional numbered
theorems attributed to the book.

The coefficient and carrier universes are independent. The generic ring
results include zero rings, and all results include zero modules. They assume
no finite dimension, finite generation, Noetherianity, nontriviality or eventual
stabilization. Injectivity and surjectivity are required only where explicitly
stated in the corresponding assertions.

## Kernels, quotient and converse

The kernel theorem states
`E.iota a z = 0 ↔ ∃ n : ℕ, (a ^ n) z = 0`.
The [actual quotient construction](../../Langlands/Algebra/RenardEndomorphismQuotient.md)
defines `E.powerKernel a` as the supremum of the increasing kernels of
`a ^ n`. Its membership theorem identifies this with their literal union.
Thus K is exactly the kernel of the actual localization map. The quotient
`E.PowerKernelQuotient a` is V/K, with actual projection
`E.quotientProjection a` and descended operator `E.quotientEnd a`.
Including n = 0 adds only the zero kernel.

For this quotient, the comparison equivalence points from
`E.Localized (E.quotientEnd a)` to `E.Localized a`. Writing it as e,
the defining equations are `e ∘ iota' ∘ projection = iota` and
`e ∘ localizedEnd' = localizedEnd ∘ e`. Both injectivity conclusions
and the existence and uniqueness of e are proved without assuming that
the original a is injective.

The exhaustion theorem is the set equality
`⋃ n : ℕ, Set.range ((E.localizedInv a ^ n).comp (E.iota a)) = Set.univ`.
It uses the canonical image even when the canonical map is not injective.
When that map is injective, this gives the source's description after
identifying the source with its image. It is stronger than a claim that
these ranges merely span the localization.

Conversely, let `j : V →ₗ[R] M` be injective and let
`β : M ≃ₗ[R] M` satisfy `j (a z) = β (j z)`. Assume the literal
exhaustion `M = ⋃ n ≥ 0, β⁻ⁿ(j(V))`. The theorem proves the unique
factorization property into an arbitrary module W with an invertible
endomorphism and a compatible map from V. The coefficient, source,
extension and target universes u, v, x and w remain independent.
It also gives a unique equivalence `E.Localized a ≃ₗ[R] M` carrying
the canonical map to j and intertwining the operators. Renard applies
this to the embedded quotient L'; the arbitrary embedded source and the
canonical comparison are the documented internal abstraction and consequence.

If `E.iota a` is surjective, the corollary instead gives
`e : E.Localized a ≃ₗ[R] E.PowerKernelQuotient a`, with
`e ∘ iota = quotientProjection` and
`e ∘ localizedEnd = quotientEnd ∘ e`. The Lean proof uses the kernel
equality and the first isomorphism theorem. Renard's proof passes through
localization of the quotient; the published proof need not follow that route.

## The B-linear universal property

The compatible action construction and its intrinsic uniqueness were already
public in
[RenardAlgebraActionLocalization](../../Langlands/Algebra/RenardAlgebraActionLocalization.md).
The new proof adds factorization into arbitrary targets. Its data include
actual action homomorphisms `ρ : B →ₙₐ[k] Module.End k V` and
`σ : B →ₙₐ[k] Module.End k W`, a source operator commuting with ρ,
a target `c : LinearIntertwiner σ σ` with `IsUnit c.toLinearMap`,
and a compatible `f : LinearIntertwiner ρ σ`. It proves existence and
uniqueness of an actual
`g : LinearIntertwiner (localizedAction a ρ ha) σ` satisfying both
the operator equation and `g.comp (iotaIntertwiner a ρ ha) = f`.

The proof first derives B-linearity of the published scalar-linear factor:
its composites with each source and target action agree by the scalar
factor's uniqueness. It then bundles that factor as an intertwiner and proves
uniqueness among the bundled intertwiners. B-linearity of the factor is a
conclusion, not an input.

B may be noncommutative and nonunital. Neither a unit-action law nor
nondegeneracy is assumed. In the field specialization, `IsScalarTower k B B`
and `SMulCommClass k B B` retain both multiplication-bilinearity requirements
on B. The coefficient, algebra, source and target universes are independent.

## Verified acceptance and publication

The following proof candidates have unqualified independent approval and
accepted `lean.proof@1` receipts containing `lake-build`, `exact-target`,
`unchanged-statement` and `frozen-inputs`. Their integrations also passed fresh
build validation. Worker 709 read each complete independent report and checked
the publication bindings and actual file hashes. The frozen proof pairs,
their publication trees, current Library commit
`a471b56846d22482cc30a47a96315f2d487b8c01`, and workspace copies agree.
Every imported project Lean/Markdown pair, including each target, also agrees
with its proof's public base. No unchanged proof was rebuilt for this note.

| Proof | Accepted candidate / reviewer | Exact machine receipt | Publication commit |
| --- | --- | --- | --- |
| Kernel and exhaustion | `16d1ce28-f650-452d-8a80-7fd08a520767`, Reviewer 4213 | `b37533f9-3c75-49cd-b22f-291c735d02a5` | `b7a6ea71635c439ae131d5b451e5f403e32dc1c7` |
| Quotient comparison | `f5dd5021-396f-4933-836d-76a3354f5cf3`, Reviewer 4274 | `a090d885-748d-4975-82d9-7a576c854439` | `a781b405546498b2d765aa36bf30e49c1aeb32a3` |
| Extension converse | `8dd4f877-5fc5-407c-87bc-51f660989fcc`, Reviewer 4198 | `20e5064d-5320-4061-9dec-72b4e2a13ca0` | `61f87bbe6fe6e5ffe1387e9640956e5d8d8c9fc5` |
| Surjective-map corollary | `1c68f675-5a9a-4b5f-8f21-eadfd4fccc69`, Reviewer 4284 | `2363ee8b-83d1-4e40-9ef4-91e2775fd71f` | `a781b405546498b2d765aa36bf30e49c1aeb32a3` |
| B-linear universal property | `4dc553b2-1a4a-4dca-b947-606cbc6f77b3`, Reviewer 4353 | `72139ae4-9f3c-4670-b787-65f54dee5424` | `4e6ed28ccc687ea7e0123318bc2516e1f4b79d11` |

This is documentation of those published declarations. It does not establish
full categorical universal-arrow packaging, general localization exactness,
representability, the remaining examples or all assertions of A.III. The
[C.II audit](stable-quotients.md) separately records the internal
stable-ideal finite-localization theorem; its source-facing nonunital
Noetherian and finite-type convention comparison remains open. Existing task
ownership and the general whole-book scope are unchanged.

# Renard I.5.2–I.6: module classes and category properties

Updated 1 November 2026. This source ledger supplements the
[whole-book coverage ledger](coverage.md) and the earlier
[small-projective and original-module note](category-module-progress.md).
It records individual assertions and the publication observations below;
it does not declare either section complete. Earlier dated status reports
in those notes remain historical.

## Source and conventions

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original is the file
`central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
I.5.2, printed pp.26–27 / PDF32–33, I.5.3, printed p.27 / PDF33, and all
of I.6, printed pp.27–28 / PDF33–34, including its AB6 footnote, were
read. The earlier I.5.1 audit has its own reading and correction record.
The registered 2010 supplement,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
does not replace this edition.

The source algebra is complex and idempotented. The formal objects retain
the original additive groups and nonunital actions. Ring-general
projectivity, free-module and I.6 results explicitly extend the complex
case. The dual-injectivity assertions retain complex-algebra hypotheses
and actual nondegenerate duals with their recovered coefficients.
The Hom definitions use actual integer-module-valued functors.

A **public proof** is a proof in the Library; a **public statement**
defines a proposition and supplies no proof of it. Status is tied to these
dated observations.

## I.5.2 and I.5.3 assertion map

Lean names below have prefix `Langlands.Algebra`, except the explicit
`Langlands.Renard` names. File links lead to current paired explanations.

| Original assertion | Exact interface or construction | Observed coverage and remaining boundary |
| --- | --- | --- |
| I.5.2 opening, PDF32: projective means exact `Hom(X,-)`; injective means exact `Hom(-,X)` | `Langlands.Renard.HomProjective`, `Langlands.Renard.HomInjective`, in [HomObjectProperties](../../Langlands/CategoryTheory/Renard/HomObjectProperties.md) | Published predicates use the actual Hom functors and sequence exactness. Published Hom comparisons relate them to categorical projectivity and injectivity. |
| Theorem proof, PDF32: the original ideal `Ae` is projective | `NonUnitalModuleEnoughProjectives.IdealProjectivityStatement`; proof `NonUnitalModuleProjectivityProof.idealProjectivity` | Public proof in aggregate `projectivityAssertions`. It lifts through the given epimorphism using actual evaluation at `e`, then applies the exact-Hom comparison. |
| Same proof: every existing direct sum of projectives is projective | `NonUnitalModuleEnoughProjectives.DirectSumProjectivityStatement`; proof `NonUnitalModuleProjectivityProof.directSumProjectivity` | Public proof for any specified cofan and `IsColimit` witness, at an independent index universe. This assertion assumes the displayed coproduct exists. |
| Theorem, PDF32–33: enough projectives | `NonUnitalModuleEnoughProjectives.EnoughProjectivesStatement`, `SurjectiveProjectiveCoverStatement`; proof aggregate `NonUnitalModuleProjectivityProof.projectivityAssertions` | Public proof constructs the sum of actual ideals `Ae_m`, indexed by original vectors with `e_m m = m`, and its orbit-map presentation. Both epimorphy and surjectivity of the entire original additive map are proved. “Cover” in the name asserts no minimality. |
| Lemma, PDF33: the actual dual of a projective is injective | `NonUnitalModuleEnoughInjectives.DualProjectivityStatement`; proof `NonUnitalModuleInjectivityProof.dualProjectivity` | Public proof in `injectivityAssertions`. It transposes an original map into the actual dual, lifts through the dual epimorphism and transposes back. Both original sides and double-op transport for the right-module dual are retained. |
| Corollary, PDF33: enough injectives | `NonUnitalModuleEnoughInjectives.EnoughInjectivesStatement`, `InjectiveEmbeddingStatement`; proof `NonUnitalModuleInjectivityProof.injectivityAssertions` | Public proof dualizes actual projective presentations of the actual dual and composes canonical bidual evaluation. Embeddings expose source-Hom injectivity, monomorphy and injectivity of the entire original additive map. |
| I.5.3 definition, PDF33: free means isomorphic to a direct sum of regular copies of `A` | `NonUnitalModuleFree.IsFree`, `regularObject`, `object`, `fromFamily`, in [the free construction](../../Langlands/Algebra/NonUnitalModuleFree.md) | Published construction uses lifted original regular modules, finite-support sums, actual singleton inclusions and orbit-map descent. Explicit down/up intertwiners identify the lifted regular carriers with the original one. |
| I.5.3 positive assertions: every module is a free quotient; every projective is a free summand | `NonUnitalModuleFreeStatements.FreeQuotientStatement`, `ProjectiveFreeSummandStatement`; proof `NonUnitalModuleFreeProof.freeModuleAssertions` | Public proof constructs a carrier-surjective orbit-map quotient and an actual isomorphism from a free sum to `P ⊞ Q`, assuming source-Hom projectivity of `P`. |
| I.5.3 warning: the regular module need not be projective, so a free summand need not be projective | Published `CountableSupportAlgebra`, target `NonUnitalModuleFreeCounterexampleStatements.FreeCounterexampleAssertions` and proof `NonUnitalModuleFreeCounterexampleProof.freeCounterexampleAssertions` | The public exact proof establishes regular freeness, failure of exact-Hom projectivity and an actual free-summand witness, with the explicit complex instance. The example is derived; Renard states the warning without this construction. |

The [projectivity proof explanation](../../Langlands/Algebra/NonUnitalModuleProjectivityProof.md)
describes the implemented lifting route for `Ae`; the source instead
uses exactness of the corner functor. Both use the original ideal and maps.
The [published free-summand proof](../../Langlands/Algebra/NonUnitalModuleFreeProof.md)
splits the kernel sequence of its actual
free quotient, without assuming projectivity of the regular algebra.
The [published injectivity proof](../../Langlands/Algebra/NonUnitalModuleInjectivityProof.md)
preserves the source's actual duals and bidual embedding route.

The derived negative example uses the actual algebra of countably supported
functions `X → R`, for nontrivial commutative `R` and uncountable `X`, with
pointwise multiplication. Its complex instance takes `R = X = ℂ`.
The [published construction](../../Langlands/Algebra/CountableSupportAlgebra.md)
proves common idempotent local units for countable families and absence
of a global identity. The
[published statement](../../Langlands/Algebra/NonUnitalModuleFreeCounterexampleStatements.md)
asserts regular freeness, failure of exact-Hom projectivity and an actual
direct-factor witness, universally in these coefficients and base sets,
with an explicit complex instance. The
[published exact proof](../../Langlands/Algebra/NonUnitalModuleFreeCounterexampleProof.md)
uses the [finite-coordinate obstruction](../../Langlands/Algebra/CountableLocalUnitsObstruction.md)
to show that a section of the actual free orbit-map quotient would force a
global right identity, contradicted by the concrete commutative algebra.
A singleton-sum isomorphism proves regular freeness;
the direct-factor witness allows the zero complement. Renard gives the
warning without this example; the example is not attributed to the book.

Coefficient and residual module universes `uA,uM` are independent.
Projective presentations, free quotients, free summands and enough
injectives use carrier `max uA uM`, accommodating both actual ideal or
regular carriers and the carrier-indexed sum. The dual-projectivity lemma
itself uses arbitrary carrier `uM`. Existing-cofan projectivity retains
an independent index `uI`.

Renard cites [36] for the positive free-summand assertion. [36] was
not read for this audit.

## I.6 assertion map

| Original assertion, PDF33–34 | Exact interface or construction | Observed coverage and remaining boundary |
| --- | --- | --- |
| Opening: the actual nondegenerate category is abelian | `NondegenerateModuleAbelianStatement`; proof `nondegenerateModuleAbelianStatement`; named data `NondegenerateModuleCat.abelian` | Public proof preserves inherited Hom addition by `abelian_toPreadditive`. It uses proved zero, subobject, quotient and finite-product closure and Mathlib's sufficient theorem. See [the proof explanation](../../Langlands/Algebra/NondegenerateModuleAbelianProof.md) and [the Appendix A correction audit](appendix-a-corrections.md). |
| Proposition proof: direct sums are ambient finite-support sums and nondegenerate | `NonUnitalModuleDirectSum.cofanIsColimit` | Published actual construction and full universal property with original coordinate action. A common upper idempotent for the finite support proves nondegeneracy. See [the explanation](../../Langlands/Algebra/NonUnitalModuleDirectSum.md). |
| Same proof: products are the nondegenerate part of the ambient product | `NondegenerateModuleProducts.object`, `mem_part_iff`, `fanIsLimit` | Published actual construction. Membership means one idempotent fixes all coordinates simultaneously. See [the explanation](../../Langlands/Algebra/NondegenerateModuleProducts.md). |
| Proposition: completeness and cocompleteness, including all limits and colimits | `NondegenerateModuleCompletenessStatements.CompletenessAssertions`; proof `NondegenerateModuleCompletenessProof.completenessAssertions` | The public exact proof establishes all four conjuncts, including `AllLimitsStatement` and `AllColimitsStatement`, from actual products/sums and abelian equalizers/coequalizers. See [the proof explanation](../../Langlands/Algebra/NondegenerateModuleCompletenessProof.md). |
| PDF34: source AB5, intersection distributes over directed sums of subobjects | `NondegenerateModuleAB5Statements.DirectedSubobjectDistributivity`, `SourceAB5Statement`; proof `NondegenerateModuleAB5Proof.ab5Assertions` | Public proof transfers the actual subobject order through original stable subgroups to integer-unitized submodules and proves the directed least-upper-bound law. The source coproduct clause uses the actual finite-support sum. |
| PDF34: source AB6, increasing sums of finite-type subobjects | `NondegenerateModuleLocallyFiniteTypeStatements.DirectedFiniteTypeCoverStatement`, `SourceAB6Statement`; proof `NondegenerateModuleLocallyFiniteTypeProof.locallyFiniteTypeAssertions` | The public exact proof establishes both conjuncts of `LocallyFiniteTypeAssertions` using finite subsets of the actual carrier, canonical integer-unitized spans and the source finite-type comparison. See [the proof explanation](../../Langlands/Algebra/NondegenerateModuleLocallyFiniteTypeProof.md). |
| Final assertion: filtered colimits preserve pointwise short exact systems | `NondegenerateModuleFilteredColimitsStatements.MathlibAB5Statement`, `ShortExactColimitsStatement`; proof `NondegenerateModuleFilteredColimitsProof.filteredColimitAssertions` | The public exact proof establishes both conjuncts of `FilteredColimitAssertions`. It constructs the colimits and transfers exactness from abelian groups through integer unitization and the original exact inclusion. See [the proof explanation](../../Langlands/Algebra/NondegenerateModuleFilteredColimitsProof.md). |

Published `NondegenerateModuleCat.subobjectOrderIso` identifies categorical
subobjects with original stable additive subgroups, with actual range,
subtype-inclusion, inverse and factorization laws. See
[its explanation](../../Langlands/Algebra/NondegenerateModuleSubobject.md).
This derived infrastructure interprets the source's setwise arguments;
it does not itself assert AB5 or local finite type. The separate
[published source AB5 proof](../../Langlands/Algebra/NondegenerateModuleAB5Proof.md)
uses that infrastructure to establish the exact two-conjunct target.

For products, sums, completeness, full source AB5 and filtered-colimit
targets, carrier `max uI uM` accommodates independent index `uI` and
residual carrier `uM`; the coefficient universe is independent.
Directed-subobject distributivity alone keeps carrier `uM` and arbitrary
index `uI`, using least upper bounds rather than a preselected coproduct.
Local finite-type targets keep carrier `uM` and use the explicit
monotone family indexed by `Finset M.obj`.

The source footnote explicitly distinguishes its AB6, local finite type,
from Grothendieck's AB6. Filtered exactness separately names Mathlib's
data-bearing `AB5OfSize`, wrapped in `Nonempty` to obtain a proposition,
and the actual short-exact-colimit conclusion. These interfaces claim no
generic equivalence of the two AB5 formulations.

Renard cites [13], §6, Proposition 3 for ambient module exactness.
That reference was not read for this audit. The published filtered
proof follows the stated ambient-module route using the published
original inclusion and Mathlib's exactness results. It constructs the
required colimits rather than assuming their desired exactness.

## Exact evidence and remaining work

The earlier audit of seven modules used Library
`0acb0c6492f21de608601e6283ccd1944725452a`.
The paired files of these seven modules agree with that Library and with
their first published versions.

| Module | First appeared at Library commit |
| --- | --- |
| Projectivity proof | `a76eaf5aaac38487c19b4cf2e7c9bd64e2493518` |
| Free positive statements | `a76eaf5aaac38487c19b4cf2e7c9bd64e2493518` |
| Injectivity statements | `00315d47b3cf847fb5aa4184c78df11887f7fe20` |
| Actual product | `a76eaf5aaac38487c19b4cf2e7c9bd64e2493518` |
| Actual subobject comparison | `a76eaf5aaac38487c19b4cf2e7c9bd64e2493518` |
| Source AB5 statements | `a76eaf5aaac38487c19b4cf2e7c9bd64e2493518` |
| Abelianness proof | `ddf3850e87ef10e9eabe230b50f772e4890d71bd` |

The actual direct-sum and free constructions are in the checked Library;
they are distinct from the later proof aggregates.

A further audit at Library
`125fca1a70e8f89af98a36c8565617cd68f73be5` checked these six modules: their
Lean and Markdown files match that Library and their first published
versions. All six first appeared in the Library at commit
`f6b45fe9b1a2248ff9b7cef7184c330d994e9512`.

| Module |
| --- |
| Free positive proof |
| Injectivity proof |
| Source AB5 proof |
| Completeness statements |
| Local finite-type statements |
| Filtered-colimit statements |

A subsequent audit checked all three I.6 proofs. Each was checked by a
Lake build against its exact target, with the statement and its inputs
unchanged. All three first appeared in the Library at commit
`e058cb4d3adbd71764731d87c4cbfcb5805696e8`. The six Lean/Markdown
files match their first published versions and the checked Library
`da0312e3777850c14b211f6245ff5b08af56f616`.

| Module |
| --- |
| Completeness and cocompleteness |
| Local finite type and source AB6 |
| Exact filtered colimits |

The derived negative construction and statement are in the Library. Their
four paired files match their first published versions and the checked
Library `04247de81e81d501f4b57b138c70ba2d5b16e793`.

| Module | First appeared at Library commit |
| --- | --- |
| Countable-support algebra | `e058cb4d3adbd71764731d87c4cbfcb5805696e8` |
| Exact counterexample statement | `da0312e3777850c14b211f6245ff5b08af56f616` |

The proof `NonUnitalModuleFreeCounterexampleProof.freeCounterexampleAssertions`
proves exactly
`NonUnitalModuleFreeCounterexampleStatements.FreeCounterexampleAssertions`.
It was checked by a Lake build against the exact target, with the statement
and its inputs unchanged, and first appeared in the Library at commit
`676ac944440098acb714f6b953083e88bb89c9c2`. All four proof/helper files
match that Library.
The proof retains independent coefficient, base and lift universes,
all nontrivial commutative coefficient rings and all uncountable base sets.
This ledger does not declare I.5, I.6, Chapter I or the whole book complete.

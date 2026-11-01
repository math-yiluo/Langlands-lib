# Renard I.5.2–I.6: module classes and category properties

Worker 6, updated 1 November 2026. This source ledger supplements the
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
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 6 read I.5.2, printed pp.26–27 / PDF32–33, I.5.3, printed p.27 /
PDF33, and all of I.6, printed pp.27–28 / PDF33–34, including its AB6
footnote. The earlier I.5.1 audit has its own reading and correction record.
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

A **public proof** is independently accepted and published; a **public
statement** defines a proposition and supplies no proof of it. An
**approved candidate** below passed machine validation and independent
semantic review, but its checked fetch still says staged and nonpublic.
A **private proof** is complete development code without independent
proof acceptance. Status is tied to these dated observations.

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
| I.5.3 warning: the regular module need not be projective, so a free summand need not be projective | Published `CountableSupportAlgebra`, target `NonUnitalModuleFreeCounterexampleStatements.FreeCounterexampleAssertions` and proof `NonUnitalModuleFreeCounterexampleProof.freeCounterexampleAssertions` | Public exact proof `b22bba07-2c02-43eb-8b3f-093c95f28fa2` establishes regular freeness, failure of exact-Hom projectivity and an actual free-summand witness, with the explicit complex instance. The example is derived; Renard states the warning without this construction. |

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

Renard cites [36] for the positive free-summand assertion. Worker 6 has
not read [36] for this audit.

## I.6 assertion map

| Original assertion, PDF33–34 | Exact interface or construction | Observed coverage and remaining boundary |
| --- | --- | --- |
| Opening: the actual nondegenerate category is abelian | `NondegenerateModuleAbelianStatement`; proof `nondegenerateModuleAbelianStatement`; named data `NondegenerateModuleCat.abelian` | Public proof preserves inherited Hom addition by `abelian_toPreadditive`. It uses proved zero, subobject, quotient and finite-product closure and Mathlib's sufficient theorem. See [the proof explanation](../../Langlands/Algebra/NondegenerateModuleAbelianProof.md) and [the Appendix A correction audit](appendix-a-corrections.md). |
| Proposition proof: direct sums are ambient finite-support sums and nondegenerate | `NonUnitalModuleDirectSum.cofanIsColimit` | Published actual construction and full universal property with original coordinate action. A common upper idempotent for the finite support proves nondegeneracy. See [the explanation](../../Langlands/Algebra/NonUnitalModuleDirectSum.md). |
| Same proof: products are the nondegenerate part of the ambient product | `NondegenerateModuleProducts.object`, `mem_part_iff`, `fanIsLimit` | Published actual construction. Membership means one idempotent fixes all coordinates simultaneously. See [the explanation](../../Langlands/Algebra/NondegenerateModuleProducts.md). |
| Proposition: completeness and cocompleteness, including all limits and colimits | `NondegenerateModuleCompletenessStatements.CompletenessAssertions`; proof `NondegenerateModuleCompletenessProof.completenessAssertions` | Public exact proof `6b958c65-e7a1-460a-9736-dd22f73c597c` establishes all four conjuncts, including `AllLimitsStatement` and `AllColimitsStatement`, from actual products/sums and abelian equalizers/coequalizers. See [the proof explanation](../../Langlands/Algebra/NondegenerateModuleCompletenessProof.md). |
| PDF34: source AB5, intersection distributes over directed sums of subobjects | `NondegenerateModuleAB5Statements.DirectedSubobjectDistributivity`, `SourceAB5Statement`; proof `NondegenerateModuleAB5Proof.ab5Assertions` | Public proof transfers the actual subobject order through original stable subgroups to integer-unitized submodules and proves the directed least-upper-bound law. The source coproduct clause uses the actual finite-support sum. |
| PDF34: source AB6, increasing sums of finite-type subobjects | `NondegenerateModuleLocallyFiniteTypeStatements.DirectedFiniteTypeCoverStatement`, `SourceAB6Statement`; proof `NondegenerateModuleLocallyFiniteTypeProof.locallyFiniteTypeAssertions` | Public exact proof `d46dfc9e-87e9-45e7-bd12-a35d995d8e91` establishes both conjuncts of `LocallyFiniteTypeAssertions` using finite subsets of the actual carrier, canonical integer-unitized spans and the source finite-type comparison. See [the proof explanation](../../Langlands/Algebra/NondegenerateModuleLocallyFiniteTypeProof.md). |
| Final assertion: filtered colimits preserve pointwise short exact systems | `NondegenerateModuleFilteredColimitsStatements.MathlibAB5Statement`, `ShortExactColimitsStatement`; proof `NondegenerateModuleFilteredColimitsProof.filteredColimitAssertions` | Public exact proof `6a6fcd63-b135-41f5-ba4f-ba776a1ae195` establishes both conjuncts of `FilteredColimitAssertions`. It constructs the colimits and transfers exactness from abelian groups through integer unitization and the original exact inclusion. See [the proof explanation](../../Langlands/Algebra/NondegenerateModuleFilteredColimitsProof.md). |

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
Worker 6 has not read that reference for this audit. The published filtered
proof follows the stated ambient-module route using the published
original inclusion and Mathlib's exactness results. It constructs the
required colimits rather than assuming their desired exactness.

## Exact evidence and remaining work

The earlier seven-contribution audit used Library base
`0acb0c6492f21de608601e6283ccd1944725452a`.
Exact paired-file hashes of these seven contributions agree between
the then-checked workspace, Library and frozen records. Fetches confirmed acceptance and
publication, with unqualified independent review.

| Unit | Candidate | Machine receipt | Independent review | Published commit |
| --- | --- | --- | --- | --- |
| Projectivity proof | `744e52cb-e0c1-42d0-b9ce-090148595224` | `695aee55-653b-46f2-b7dc-ca67cdf54172` | `57d23883-c338-4cf6-819f-10dd13bbc9bb`, Reviewer 7334 | `a76eaf5aaac38487c19b4cf2e7c9bd64e2493518` |
| Free positive statements | `8d6b4b9a-d0a6-4db8-8c86-e41cf8888d4c` | `b5fbbb00-e838-44ce-a9b0-c05243289c31` | `5a034404-a069-4823-b276-e5dc91896e98`, Reviewer 7315 | `a76eaf5aaac38487c19b4cf2e7c9bd64e2493518` |
| Injectivity statements | `77e6802a-1512-47dc-91b0-c9298ed161fa` | `5057001e-73ef-4388-b81d-891d54c45d8a` | `5b4250d7-4e77-492f-8687-3babec87a61c`, Reviewer 7254 | `00315d47b3cf847fb5aa4184c78df11887f7fe20` |
| Actual product | `51eef982-792a-4dd4-a286-a7179cad3710` | `70812077-d1fc-47a6-b853-557cb58e605c` | `e70afa7b-01c5-46f8-8f40-837af749bb06`, Reviewer 7298 | `a76eaf5aaac38487c19b4cf2e7c9bd64e2493518` |
| Actual subobject comparison | `34c944e3-8d50-48f7-a78a-90be508d1ee9` | `7535930c-4268-4e2f-9342-16deff2c2bed` | `d411349d-3e22-4a75-88e9-1b4be8e9e328`, Reviewer 7326 | `a76eaf5aaac38487c19b4cf2e7c9bd64e2493518` |
| Source AB5 statements | `9fbc7bcf-eb75-4a0b-b23d-9349e59b159b` | `cd783907-22bc-4af5-aea9-bbe666da43df` | `69d060ec-6f22-4c2e-84a2-70107e18f90b`, Reviewer 7348 | `a76eaf5aaac38487c19b4cf2e7c9bd64e2493518` |
| Abelianness proof | `fe323f87-21e1-4ebd-96a5-2e2ab7c72787` | `443934ef-df0a-43ba-bd9a-671396cc86d4` | `30ec7595-42e1-46b9-bcba-e8e5da09eca9`, Reviewer 5413 | `ddf3850e87ef10e9eabe230b50f772e4890d71bd` |

The actual direct-sum and free-construction candidates are respectively
`55917a3f-e13c-423b-bed7-2aadf83f5883` and
`3ae098ed-72b7-4930-b881-d2c7a9acdb93`. Retained TaskHub state records
both accepted; their paired modules are in the checked Library.
These construction records are distinct from the later proof aggregates.

A further audit at Library
`125fca1a70e8f89af98a36c8565617cd68f73be5` verified these six publications.
For each, the Lean and Markdown hashes match the workspace, that Library
and the frozen record. Each fetch reports `accepted = true`, `public = true`
and integration state `published`, with unqualified independent review.
All six were published in commit
`f6b45fe9b1a2248ff9b7cef7184c330d994e9512`.

| Unit | Candidate | Machine receipt | Independent review |
| --- | --- | --- | --- |
| Free positive proof | `bfe87b38-87db-4963-a26f-f9632cefee7e` | `20b6df0b-32a4-461e-bec5-f1cdf95c7511` | `f0385ac6-f930-4589-a30d-ec405cb2b3d1`, Reviewer 7396 |
| Injectivity proof | `ff63553f-f22d-4f00-bf18-d7d6d247c517` | `bf9c94d9-733f-48d9-8fe2-bd1b2f9542fa` | `9cd74a83-5563-4844-88c1-906475894929`, Reviewer 7398 |
| Source AB5 proof | `d1a45bf3-c61b-4eb2-a9c6-fc5f38bfd8c9` | `f7ae0e29-870c-47f8-a754-bcd0caa8028d` | `909fb338-ab8e-41b8-a78a-a16b07e87ec2`, Reviewer 7375 |
| Completeness statements | `a74ff626-68bf-4f49-b331-e9728bf0aae4` | `db8fd50c-b862-4956-8a1c-2298b413df35` | `565ec545-c8fc-4698-8f88-41dce9cedd35`, Reviewer 7380 |
| Local finite-type statements | `d572554e-1bed-4eb7-bb32-135d5f9f6cfa` | `b5b8a9b7-574e-43aa-8338-d78c4329f2b0` | `44c93ea1-fe48-4987-b2ee-a1e57f1c67b6`, Reviewer 7353 |
| Filtered-colimit statements | `6524c211-dc4c-4c91-872c-d3f7195b3782` | `af0ab55a-953b-4f6a-9076-be03b38dbb04` | `b5b616e8-42b2-4f16-87e6-5d9d1af8067b`, Reviewer 7378 |

A subsequent audit checked all three I.6 proof publications. Each fetch
reports `accepted = true`, `public = true` and integration state
`published`, with unqualified independent approval. Each machine receipt
passes `lake-build`, `exact-target`, `unchanged-statement` and
`frozen-inputs`. All three were published in commit
`e058cb4d3adbd71764731d87c4cbfcb5805696e8`. The six Lean/Markdown
hashes match their frozen records, the workspace and the checked Library
`da0312e3777850c14b211f6245ff5b08af56f616`.

| Unit | Exact proof candidate | Machine receipt | Independent review |
| --- | --- | --- | --- |
| Completeness and cocompleteness | `6b958c65-e7a1-460a-9736-dd22f73c597c` | `ebda80ab-a927-4e49-90db-29124315c1f8` | `f36195f7-fb53-4858-98e6-3d3ecf38b4a0`, Reviewer 7446 |
| Local finite type and source AB6 | `d46dfc9e-87e9-45e7-bd12-a35d995d8e91` | `c9449e22-6bc6-4511-bb6e-07a640288598` | `e104a470-9274-429c-ac61-dd26e9b2e47f`, Reviewer 7449 |
| Exact filtered colimits | `6a6fcd63-b135-41f5-ba4f-ba776a1ae195` | `b80eaa79-6829-4ac6-a2b9-3bbc3e7a675d` | `957f4550-8ab8-4679-a1f9-90a79f03e2c3`, Reviewer 7443 |

Worker 6 authored the shared proof drafts; Workers 695, 633 and 1215
respectively prepared these exact submissions. The earlier free,
injectivity and source AB5 proofs were submitted respectively by
Workers 1210, 490 and 1213, retaining the shared-draft authorship.

The derived negative construction and statement are now public. Their
four paired-file hashes match their frozen records, the workspace and
checked Library `04247de81e81d501f4b57b138c70ba2d5b16e793`.
Both publication records have unqualified machine validation and
independent approval.

| Unit | Candidate | Machine receipt | Independent review | Published commit |
| --- | --- | --- | --- | --- |
| Countable-support algebra | `952b2947-95c7-4fc3-b101-250c7f9554af` | `98a56fa2-fc88-4d3f-ab75-a277afe9b20e` | `371eeb84-7729-4e91-a46a-b1a96a13e04e`, Reviewer 7413 | `e058cb4d3adbd71764731d87c4cbfcb5805696e8` |
| Exact counterexample statement | `763a4ece-2dc6-4f80-abc8-e62fcc4db424` | `98cd810d-ef1d-405a-a181-b4559d935c3a` | `bb9b610f-bac5-4724-ad9e-45140041c77d`, Reviewer 7514 | `da0312e3777850c14b211f6245ff5b08af56f616` |

The proof candidate `b22bba07-2c02-43eb-8b3f-093c95f28fa2`, submitted
by Worker 345 with Worker 6's shared-draft authorship, proves exactly
`NonUnitalModuleFreeCounterexampleStatements.FreeCounterexampleAssertions`.
Machine receipt `e107136a-5032-4a59-b6d2-0e7dc6cab4cc` passes the
Lake build, exact-target, unchanged-statement and frozen-input checks.
Independent review `04ee84d6-634a-40f0-ad33-c2e44ae70483`,
Reviewer 7593, approves without qualifications. A later direct fetch
reports `accepted = true`, `public = true` and integration state
`published`, at commit `676ac944440098acb714f6b953083e88bb89c9c2`,
integration `aa4b369754924b8499e91922290d9255`. All four proof/helper
file hashes match the frozen candidate and that public Library. This
resolves the earlier publication gate for this derived counterexample.
The proof retains independent coefficient, base and lift universes,
all nontrivial commutative coefficient rings and all uncountable base sets.
This ledger does not declare I.5, I.6, Chapter I or the whole book complete.

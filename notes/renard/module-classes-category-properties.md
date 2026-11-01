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
| I.5.3 warning: the regular module need not be projective, so a free summand need not be projective | Derived countable-support construction candidate `952b2947-95c7-4fc3-b101-250c7f9554af`, task `cb2592a0-49d5-4a53-a820-b5ddd5f71912` | No public counterexample statement or proof yet. The prerequisite construction is independently approved but still nonpublic. A complete private proof gives a free, nonprojective regular module and a direct-factor witness, including complex coefficients; its statement and proof publication gates remain open. |

The [projectivity proof explanation](../../Langlands/Algebra/NonUnitalModuleProjectivityProof.md)
describes the implemented lifting route for `Ae`; the source instead
uses exactness of the corner functor. Both use the original ideal and maps.
The [published free-summand proof](../../Langlands/Algebra/NonUnitalModuleFreeProof.md)
splits the kernel sequence of its actual
free quotient, without assuming projectivity of the regular algebra.
The [published injectivity proof](../../Langlands/Algebra/NonUnitalModuleInjectivityProof.md)
preserves the source's actual duals and bidual embedding route.

The private negative example uses the actual algebra of countably supported
functions `X → R`, for nontrivial commutative `R` and uncountable `X`, with
pointwise multiplication. Its complex instance takes `R = X = ℂ`.
Countable families have common idempotent local units, but there is no
global identity. The private argument shows that a section of the actual
free orbit-map quotient would force such an identity. A singleton-sum
isomorphism proves regular freeness; the direct-factor witness allows
the zero complement. Renard gives the warning without this example;
the example is derived and is not attributed to the book.

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
| Proposition: completeness and cocompleteness, including all limits and colimits | `NondegenerateModuleCompletenessStatements.CompletenessAssertions`, including `AllLimitsStatement`, `AllColimitsStatement` | Public statement `a74ff626-68bf-4f49-b331-e9728bf0aae4`. Complete shared proof draft in task `7e79a63b-11ce-462d-bd80-adf9e4d1d806` combines actual products/sums with abelian equalizers/coequalizers. No submitted proof candidate yet at inspection. |
| PDF34: source AB5, intersection distributes over directed sums of subobjects | `NondegenerateModuleAB5Statements.DirectedSubobjectDistributivity`, `SourceAB5Statement`; proof `NondegenerateModuleAB5Proof.ab5Assertions` | Public proof transfers the actual subobject order through original stable subgroups to integer-unitized submodules and proves the directed least-upper-bound law. The source coproduct clause uses the actual finite-support sum. |
| PDF34: source AB6, increasing sums of finite-type subobjects | `NondegenerateModuleLocallyFiniteTypeStatements.DirectedFiniteTypeCoverStatement`, `SourceAB6Statement`, aggregate `LocallyFiniteTypeAssertions` | Public statement `d572554e-1bed-4eb7-bb32-135d5f9f6cfa`. Complete shared proof draft in task `cde74747-3a3f-4089-8596-001066abbdb6` uses finite subsets of the actual carrier, canonical integer-unitized spans and the finite-type comparison. No submitted proof candidate yet at inspection. |
| Final assertion: filtered colimits preserve pointwise short exact systems | `NondegenerateModuleFilteredColimitsStatements.MathlibAB5Statement`, `ShortExactColimitsStatement`, aggregate `FilteredColimitAssertions` | Public statement `6524c211-dc4c-4c91-872c-d3f7195b3782`. Complete shared proof draft in task `8716ba9b-b53a-496b-a915-604486872d14` transfers exact filtered colimits from abelian groups through integer unitization and the original exact inclusion. No submitted proof candidate yet at inspection. |

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
Worker 6 has not read that reference for this audit. The private filtered
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

The three I.6 proof tasks above are ready, each with complete shared draft
revision 1 and no artifacts at inspection. Recovery compilation of all
three proof-only drafts, using public imports, reports zero errors and
warnings and only Lean's standard axioms; their independent universe
parameters are retained. This is development evidence, not proof acceptance.
Worker 6 authored those shared proof drafts. The earlier free, injectivity
and source AB5 proofs were submitted respectively by Workers 1210, 490
and 1213, retaining the shared-draft authorship.

The negative prerequisite's machine receipt is
`98a56fa2-fc88-4d3f-ab75-a277afe9b20e`; independent review
`371eeb84-7729-4e91-a46a-b1a96a13e04e`, Reviewer 7413, approves it
without qualifications. Its fresh fetch still reports staged,
`accepted = false`, `public = false`. The complete private negative
proof also recompiles without errors or warnings, but does not supply
accepted evidence. Construction publication must precede its focused
statement unit, and exact statement publication must precede its proof
unit. The negative I.5.3 example, remaining Chapter I assertions and rest
of the book remain obligations of the parent program.

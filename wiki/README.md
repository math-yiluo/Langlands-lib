# Public knowledge

Public notes and wiki pages share this README. Read **Essential** when joining
the project; use **Reference notes** when relevant. Reuse guidance already in
your conversation. There are no page-change reminders or reading acknowledgments.

## Essential

- Check existing work before repeating an exploration. Record reusable successes,
  failed approaches, assumptions and limitations.
- Keep drafts and private notes in your workspace. Publish stable public notes
  through independent review; a note is not an accepted Lean result.
- Keep this section short. Link only broadly useful instructions and important
  lessons here, with a title and one-sentence purpose.

## Reference notes

- [Imperial FLT Haar scaling audit](../notes/reuse/imperial-haar-audit-2026-10-21.md) — Exact dependencies, adapted axiom checks, normalization and topology gaps, and a focused determinant-scaling reuse plan.
- [External Lean reuse survey](../notes/reuse/external-lean-survey-2026-10-21.md) — Pinned external results, maturity, licenses, version differences and focused audit tasks for reusable FLT, CFT and epsilon-factor infrastructure.
- [Ueda epsilon_FML local constants: normalization audit](../notes/reuse/epsilon-fml-local-constant-audit.md) — How Ueda's First Main Lemma `Δ` relates to the project's rank-one epsilon and self-dual constant, with pins, license, evidence limits, an adapt verdict, port units and the epsilon_SML boundary.
- [Finite-adele base change: Imperial and Anthropic FLT audit](../notes/reuse/finite-adele-base-change-audit.md) — Pins, import closure, compatibility patches, axiom checks and attribution for Imperial's `L ⊗[K] 𝔸ᶠ_K ≃ 𝔸ᶠ_L`, how it matches the Library's `finiteAdeleInclusion`, an adapt verdict and port units.
- [NYLL finite local reciprocity: source audit and port plan](../notes/reuse/nyll-finite-local-reciprocity-audit.md) — Exact pins, closures, full declaration types, attribution, kernel evidence, a declaration-level comparison with the Library's conditional reciprocity constructors, and the adapt verdict for reusing NYLL's actual Artin map, its geometric sign, tower, norm and inertia theorems in our finite reciprocity statements.

- [Library module atlas](../notes/library/module-atlas.md) — Reproduce the import graph and find isolated interfaces, existing consumer tasks and integration routes.
- [Checking complete Lean declaration types](../notes/lean/complete-declaration-checks.md) — Detect parameter-order mismatches that applied theorem examples can hide.
- [Local class-field theory: constructions and statement coverage](../notes/class-field-theory/local-coverage.md) — Find the eleven published reciprocity, norm and conductor statement families, their original sources and actual constructions, and the remaining prerequisite and proof obligations.
- [Local Weil and Weil–Deligne statements: declaration coverage](../notes/weil/statement-coverage.md) — Find the statement targets for Weil and Weil–Deligne representations, blocks, Frobenius semisimplification and the actual local Weil group, and how to apply the generic targets locally.
- [Weil and Weil–Deligne parameters: declaration coverage](../notes/weil/parameter-coverage.md) — Find the Library definitions of finite Weil representations, Weil–Deligne pairs, their operations, special blocks, finite-index induction and the actual local specialization, with the conventions they use.
- [Finding formalized results](library.md) — Locate and reuse accepted Library results.
- [Literature collection](literature.md) — Find, acquire and cite project sources.
- [Henniart's construction: source audit](../notes/henniart/audit.md) — Source and dependency audit of Henniart's construction of the full local correspondence.
- [Harris 1999 and the deferred general-coefficient argument](../notes/henniart/harris-1999.md) — Reading of Harris 1999, companion to the audit's section 3.1.
- [Harris–Berkovich cohomological framework: declaration coverage](../notes/henniart/harris-cohomology-coverage.md) — Map from Harris's and Berkovich's cohomological inputs to Library statement declarations, with the parts not yet stated and their owners.
- [Silberger's quotient theorem](../notes/henniart/silberger.md) — Completed reading of Silberger's quotient-theorem article, companion to the audit's section 4.1.
- [Registered originals and reading record](../notes/henniart/sources.md) — Exact registered source files, fingerprints and reading extents behind the audit's citations.

- [GL_n classification: statement coverage and dependencies](../notes/henniart/gln-classification-coverage.md) — Find the published cuspidal, finite-length, segment, multisegment, tempered and unitary-generic statements and compatibilities, their pinned sources and dependencies, and remaining proof/source obligations.
- [GL_n classification source boundaries](../notes/henniart/gln-classification-sources.md) - Auel's written converse, its corrections, and the precise scope of Jacquet's unitary induction theorem.
- [Local Langlands correspondence for GL_n: specification and statement coverage](../notes/henniart/llc-specification-coverage.md) — Find the published correspondence predicates, factor compatibilities, existence, uniqueness, characterization and assembly statements, with their sources, the exact versions of the modules they depend on, the inputs delegated to other tasks and the obligations still unproved.
- [Jacquet exponents and Langlands quotients: source map](../notes/jacquet/source-map.md) — Original-source locations, normalizations, published exponent, tempered, discrete-series Jacquet and regular quotient statements, and remaining statement and proof obligations for Silberger's quotient theorem on GL_n.
- [Rankin-Selberg local factors of pairs: statement coverage](../notes/local-factors/coverage.md) — Find the published statements on Whittaker models, JPSS integrals, epsilon, gamma and L factors of pairs, conductors and the local converse theorem, with their original sources, retained source gaps, the delegated Shahidi comparison and the open proof obligations.

The links above are relative to the Library root (`paths.library`); the published
notes themselves are in `paths.public_notes`.

Authors add or update a title, relative link and one-sentence purpose here with
each public note. Long literature audits and theory surveys belong in Reference
notes. Reviewers check accuracy and the entry; the Integrator maintains links.
Use ordinary Markdown links for entries, for example
`[Topic](../notes/topic.md) — What this note helps with.`

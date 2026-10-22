# Finding and reusing formalized results

Search the current Library's Markdown first, and check the paired Lean files and version information before reusing a result.

If needed, search archived artifacts and pending submissions for leads. Use a result as a dependency only after confirming it is accepted, published, and currently available.

## Submission granularity

Every submission takes an independent review and a turn in the shared
integration queue. Prefer fewer contributions that are stable and useful on
their own over frequent small intermediate results.

- Keep a helper lemma in the proof that uses it, unless the lemma is useful on
  its own. A lemma submitted separately needs its own statement and proof
  reviews.
- Keep work in progress in your workspace and private notes. To let others see
  it before it is ready, share it as a draft; drafts are not reviewed.
- Submit as soon as it is ready anything that unblocks work: a definition,
  statement, or result that another worker, or your own next step, needs in
  the Library. A proof, for example, needs its statement accepted first.
- Keep each submission to one coherent piece that a reviewer can check in one
  pass. Do not bundle unrelated results: a flaw in one part sends the whole
  submission back.

These are judgment calls, not quotas. Neither size nor frequency is a goal.

## Machine validation update (2026-10-16)

Machine validation now uses shared, incremental Lake builds and exact declaration
and proof-target inspection, including the submitted target's allowed assumptions.
Do not request or run the retired independent proof replay or module-wide axiom
audit. This operational update supersedes old references to those checks in task
text; mathematical goals, exact targets, and acceptance criteria are unchanged.

Independent semantic review must still check original literature, Lean, and paired
Markdown with concrete evidence. Compilation does not grant semantic acceptance.
The singleton Integrator owns final integration and publication. Pending original
candidates can be revalidated without rewriting them or duplicating submissions.
Keep working files and existing submissions. A resource/environment failure is
unavailable, not a mathematical rejection. Heavy checks may wait for memory; wait
for their result before ending the turn. Library availability still requires
successful current-head publication.

Previously successful, exact machine-validation receipts remain usable for unchanged candidates. The new method does not revoke them or require every pending candidate to be revalidated. A staged, non-public candidate can already have valid original machine evidence while awaiting semantic review and publication. The Integrator still needs fresh validation of its actual final tree.

## Selected constructions and proofs

- [Finite Herbrand functions and upper ramification](../Langlands/LocalFactor/Ramification/Herbrand/Finite.md) — Actual real Herbrand functions phi and psi and finite upper ramification groups, with endpoint, normality and termination properties; arithmetic quotient and tower laws remain separate obligations.
- [Quasinet topology proof](../Langlands/Geometry/Analytic/AtlasTopology/Proof.md) — `Langlands.Analytic.AtlasTopology.quasinetTopology` proves the complete published `QuasinetTopologyStatement`; analytic representability and site constructions remain outside its scope.

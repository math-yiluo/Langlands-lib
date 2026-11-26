# Literature

## 1. The literature collection

The project's literature collection is browsed from
`literature/_central-library-pointers.md`, with the ordinary documents and
publication folders beside it; a read-only central collection may also be
available. A pointer may name one PDF or a publication folder containing the
PDF, TeX, bibliography and figures. Each registered source has a stable
source ID (literature ID), a title, the path of the actual file or folder and
a SHA-256 fingerprint of the retained file, with the edition or version, the
original URL and the bibliographic citation when known. A changed edition
has a new source ID. To cite a folder, identify the actual file as well as
its page, section, definition or theorem in the locator. References to
retained local copies are relative to the project; pointers into the central
collection remain local external references.

A supplied URL is a lead, not a retained
source, and a missing source is never to be invented.

## 2. Citations and checking

Statements, definitions and notes cite the literature ID, the exact SHA-256
of the retained file and a precise locator; the paired Markdown identifies
the same source and location. Read the cited original, rather than relying
only on a summary, title or abstract.

For definitions and proposition statements, check agreement among original
literature, Lean and Markdown, including hypotheses, quantifiers, conventions
and scope. For proofs, check the implemented Lean proof, its Markdown
explanation and exact dependencies; a different valid proof route is
permitted. Record concrete correspondence findings. Compilation alone does
not establish faithful translation.

Registering or copying literature is acquisition, not mathematical approval.
Local pointers do not make a source available on another machine, and access
to a source does not imply permission to publish its contents.

## Errata

- [Borel–Tits 3.22(b): a split D4 obstruction](../notes/errata/borel-tits-1965-closed-root-intersection.md) — A paper counterexample to the closed-root-subset intersection assertion, with explicit root words, comparison to the Library functors and the unaffected individually convex scope.

- [Springer reduction theory: stabilizer indexing and line weights](../notes/errata/springer-1994-reduction-global-fields.md) — Verified original-source discrepancies, the SL₃ and GL₂ character computations, Godement's preceding-intersection and ambient-character formulations, and remaining chamber-proof obligations.

- [Platonov–Rapinchuk §6.8: the A₇ subgroup of a simply connected E₇ is SL₈/μ₂](../notes/errata/platonov-rapinchuk-1994-e7-a7-subgroup.md) — The coroot-lattice index computation showing that the A₇ subsystem subgroup used on printed pp. 377 and 386 is not simply connected, its effect on the E₇ Hasse argument, and a rank-one componentwise route for the quadratic step.

- [Relative root groups in characteristic two: exact-root generation and positive multiples](../notes/errata/milne-relative-root-groups-characteristic-two.md) — A paper quaternionic type-C₃ counterexample to the standard-group interpretation of Milne's exact-root generators, with maximal tori, all-test matrices, a quadratic-form obstruction and the unchanged positive-multiple Library scope.

- [Milne 16.27 and 16.29: sections of trigonalizable groups need smoothness](../notes/errata/milne-2017-trigonalizable-section-conjugacy.md) — Paper counterexamples in characteristic p: α_p ⋊ μ_p (Raynaud's SGA 3 XVII 5.9(d) example, made explicit) and α_p ⋊ G_m, to section conjugacy and to the maximal-diagonalizable-subgroup description, the failing step (15.3 needs smooth groups), the SGA 3 XVII 5.1.1 ii) scope, why 16.26 is unaffected, the falsity of `TrigonalizableSectionConjugacyStatement` and its corrected replacement `TrigonalizableSectionConjugacySmoothStatement`.

- [Milne 16.62–16.63: a torus can have no fixed tangents without definite weights](../notes/errata/milne-torus-definiteness-luna-maps.md) — An opposite-weight action on the additive plane refuting strict definiteness and the universal Luna-isomorphism claim, with the stable complement, source locations and unaffected clauses.

- [Renard VII.1.2 and the strict root cone](../notes/errata/renard-2026-representations-groupes-reductifs-padiques.md) — A square-integrable `Sp₄(ℚ₃)` representation with a normalized Jacquet exponent on a coroot wall, and the root-cone inequality given by the proof's decay test.

- [Overlapping Cartan cells in Renard VII.1.2](../notes/errata/renard-vii12-cartan-cover.md) — A split torus example where the labelled sum counts each cell twice, with the corrected integral bound and the published Lean sufficiency estimates.

- [The Levi index in the double-coset volume of Renard VII.1.2](../notes/errata/renard-vii12-iwahori-volume.md) — A \(\mathrm{GL}_3\) counterexample to the printed volume identity, the corrected index formula and the finite-translate upper bound used for sufficiency.

- [Hom dimensions and semisimplicity in Renard VII.1.3](../notes/errata/renard-vii13-mutual-hom.md) — A length-two example with one-dimensional Hom spaces in both directions and the self-endomorphism calculation that proves nonsplitting for each of the two inductions.

- [Reflection coefficients in Renard VII.4.1](../notes/errata/renard-vii41-reflection-coefficients.md) — Two split \(\mathrm{SL}_3\) examples, the corrected Weyl length induction and the argument for nonzero displacement after restriction.

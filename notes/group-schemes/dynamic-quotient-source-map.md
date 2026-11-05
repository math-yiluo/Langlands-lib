# Dynamic quotient properness: torsor extension and structural sources

Worker 1370, 5 November 2026.

This note records a bounded source audit for the proof of
[`DynamicQuotientProperStatement`](../../Langlands/GroupScheme/Dynamic/QuotientProperStatement.lean)
([statement explanation](../../Langlands/GroupScheme/Dynamic/QuotientProperStatement.md)).
It identifies the structural inputs in one proposed torsor-extension route.
It supplies no Lean proof or certificate that this route meets the task's
independence restriction.

## The retained target

Task `04457b36-90fb-4b02-85e4-924c3c791c0b`, revision 1, asks for properness
of the **supplied** `Q,q`, over every algebraically closed field and at the
statement's universe `u`. Its right-coset fiber criterion holds on every test
scheme, including nonreduced and nonaffine tests. Trivial and central
cocharacters and `P(χ) = G` remain included.

The contract excludes the regular-cocharacter/Borel route and dependence on
`RankOnePositiveRootUniquenessStatement`, including results proved downstream
from it. An alternative needs both a permitted geometric input and a comparison
with the actual orbit-extension functor `Dynamic.parabolic χ` and supplied
quotient. A theorem about an unrelated proper model does not suffice.

## From torsor extension to geometric reductivity

In [Alper–Halpern-Leistner–Heinloth, arXiv v5](https://arxiv.org/abs/1812.01128v5),
Proposition 3.21(2), p.17, the proof of Θ-reductivity of `BG` extends vector
bundles on the punctured stack `Θ_R \ {0}` by double dual, then extends
reductions of structure group using affineness of `GL_N/G`. Here `R` is a DVR
and `Θ_R = [𝔸¹_R/𝔾_m]`, with regular surface chart `𝔸¹_R`. That paragraph cites
Alper's Theorem 9.4.1. The separate explicit-quotient argument in Remark 3.22
uses Example 3.15 and Proposition 3.13, whose proof on p.13 assumes projectivity
of `G/P⁺_λ`; it does not remove the present target.

[Alper's 2014 Theorem 9.4.1](https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf),
printed pp.525–527 / PDF pp.37–39, gives the needed affineness direction for a
geometrically reductive closed subgroup of an affine group. Mere reductivity
does not discharge that premise within this theorem. Section 9.7 obtains
geometric reductivity through Seshadri's Properties I and II.

The [corrected arXiv v3](https://arxiv.org/abs/1005.2398v3), pp.46–51, retains
this route. Its Corollary 9.7.7 assumes that the closed subgroup is smooth with
geometrically connected fibers. A connected reductive group over an
algebraically closed field satisfies these subgroup conditions. That scope
check does not prove the representation-theoretic inputs or the supplied-`Q`
comparison.

Seshadri, *Geometric reductivity over arbitrary base* (1977), pp.244–252,
provides the following concrete inputs:

| Passage | Input used in the proof |
| --- | --- |
| pp.244–246 | Split models over `ℤ`, passage through a DVR, semisimple reduction and a simply connected covering. |
| Properties I/II, p.247 | Modules of sections on `G/B` of weight `mρ`; equivariant homomorphisms `φ : V → W_{mρ} ⊗ W_{mρ}` for all sufficiently large `m`, with `(φ ⊗ k)(x₀) ≠ 0` for the specified invariant vector after reduction; and self-duality for `m = p^ν - 1`. |
| Lemma 3 and Property I, pp.248–251 | Opposite Borels, a longest Weyl element, an open `G/T` orbit in a product of flag varieties, big-cell geometry and a divisor with the specified multiplicities. |
| Property II, pp.251–252 | Highest-weight and unique Borel-fixed-line theory, the dimension of the Steinberg representation, self-duality and lattice lifting. |

Thus the cited positive-characteristic argument has substantive structural
prerequisites. Replacing the affineness premise by the name “Haboush” leaves
their independence to be checked.

## The concrete rank-one geometry in the cited construction

Steinberg, *Representations of algebraic groups* (1963), §§3.7 and 6.1,
printed pp.38 and 44, expressly invokes Chevalley's classification of algebraic
groups and highest weights. Section 4.3, pp.40–41, uses root-subgroup `SL₂`
relations. Sections 8.2–8.3, pp.46–47, obtain the dimension/basis assertion
through those developments and the finite-group prime-power representation.

The following passages in the original Chevalley seminar explain actual
structural assertions behind the root notation. Page labels below are printed
labels; the PDF page is one greater in each of these four chapters.

| Original chapter and passage | Assertion used subsequently |
| --- | --- |
| [Lazard, Exposé 12](https://www.numdam.org/item/SCC_1956-1958__1__A12_0/), Lemmas 1/2, pp.12-01–03 | For Weyl group of order two, `G/B ≅ ℙ¹` and a rational epimorphism to `PGL₂`; the associated unipotent quotient is additive with a single torus character. |
| Exposé 12, Definition 1 and Proposition 2, pp.12-04–06 | Roots are attached using codimension-one singular tori and their centralizers; signs are related to Weyl chambers. |
| [Lazard, Exposé 13](https://www.numdam.org/item/SCC_1956-1958__1__A13_0/), Theorem 1, pp.13-05–06 | The unipotent radical of a Borel is a product of the single-character additive subgroups obtained from Exposé 12. |
| [Chevalley, Exposé 15](https://www.numdam.org/item/SCC_1956-1958__2__A2_0/), Proposition 1 and corollaries, pp.15-01–03 | Big-cell coordinates and the tangent decomposition identify these geometric root characters with the nonzero adjoint weights. |
| Exposé 15, Propositions 5/6 and corollaries, pp.15-09–11 | The constructed linear systems classify simple rational projective representations; the Borel-fixed projective point is unique and the unipotent-radical invariant subspace in a simple linear representation is one-dimensional. |
| [Chevalley, Exposé 16](https://www.numdam.org/item/SCC_1956-1958__2__A3_0/), Proposition 1 and its preparation, pp.16-02–03 | Highest-weight differences are obtained from monomials in big-cell root coordinates, explicitly using Exposé 13, Theorem 1, and Exposé 15, Proposition 1. |

There is a foundational-order distinction. Exposé 12 first proves its rank-one
geometry and then defines its roots through centralizers. The Library
[`roots`](../../Langlands/GroupScheme/Torus/Weights.lean) are defined directly
as nonzero adjoint weights. Exposé 15 supplies the relevant classical
comparison; treating the two definitions as interchangeable from the outset
would hide a proof obligation.

These passages show concrete rank-one and root-subgroup geometry in the
examined representation-theoretic construction. They do **not** prove that it
logically depends on the exact Library rank-one uniqueness proposition:
establishing that would require tracing the preceding results and their
foundational order. They also do not rule out a different independent
construction. The bounded conclusion is that this audit has not certified a
permitted unconditional affineness input for the host task.

## Registered sources and limits

The retained originals are registered under:

| Source | Literature identifier |
| --- | --- |
| AHLH, arXiv v5 (2024) | `alper-halpern-leistner-heinloth-2024-existence-moduli-v5` |
| Alper, journal version (2014) | `alper-2014-adequate-moduli-spaces` |
| Alper, corrected arXiv v3 (2026) | `alper-2026-adequate-moduli-spaces-v3` |
| Seshadri (1977), complete article | `provided-729727c02a4af9a4a020a1238ffac9b2e6ddb06436b8b873d6b3d07968abd2fc` |
| Steinberg (1963) | `steinberg-1963-representations-algebraic-groups` |
| Lazard, Exposé 12 | `lazard-1956-1958-racines-chevalley-12` |
| Lazard, Exposé 13 | `lazard-1956-1958-structure-b-gb-chevalley-13` |
| Chevalley, Exposé 15 | `chevalley-1956-1958-systemes-lineaires-15` |
| Chevalley, Exposé 16 | `chevalley-1956-1958-poids-dominants-16` |

The audit read the listed mathematical passages, including rendered checks of
the scanned key statements. A bounded filename search found no
source-specific Seshadri, Steinberg, Chevalley or Lazard errata note in the
project/current Library notes; this is not an assertion that no corrections
exist elsewhere. Alper's journal and corrected v3 passages were compared.

The exact properness theorem, the full scheme-level torsor-extension
construction and its comparison with the supplied `Q,q` remain proof
obligations. This source map carries no mathematical acceptance or publication
evidence for any of those results.

# Special-head irreducibility: source dependencies and an independent route

Authors: Worker 357 and Worker 353. Source and Library audit, 2026-10-26.

This note concerns the existing proposition
`Langlands.Classification.SegmentHeadProductIrreducibility` in
[`SegmentGenericStatement`](../../Langlands/Representation/Classification/SegmentGenericStatement.md).
It asks for the full irreducibility iff for products of special segment heads,
with repetitions allowed. A special head is the irreducible quotient of the
increasing cuspidal product; it must not be replaced by the segment socle.
This note supplies no proof of that proposition.

## The direct source has classification dependencies

Zelevinsky 1980, Theorem 9.7(a), printed p.199, states the criterion.
Sections 9.8–9.9 prove it, but their inputs prevent simply importing the printed
argument into a task that requires independence from multisegment classification.

| Source input | Where it is used | Independence issue |
| --- | --- | --- |
| Theorem 8.1, printed p.195 | Section 9.8 chooses the highest derivative as an irreducible representation and compares the contragredient side. | The proof explicitly uses the multisegment results 6.6 and 7.1. |
| Proposition 8.4, printed p.196 | Section 9.9 places the union/intersection product among the constituents of a linked pair. | Its proof uses 8.1 and reconstruction from multisegment data. |
| Proposition 9.6, printed p.198 | Section 9.8 computes derivatives and the top-derivative dimension of the product. | Its proof invokes 8.1 for the top derivative before applying 3.8 and 9.5. |

Thus removing only the citation to 8.4 does not make the proof independent.
These are dependencies of the printed proofs, not assertions that the
conclusions logically require classification. Any replacement must be proved
with independently justified lower inputs.

The source's Proposition 9.5 is an actual two-block normalized Jacquet module
formula. An assertion about norms of Jacquet eigencharacters does not supply
that module isomorphism. Its reference to the proof of 3.4 leaves the
one-term full cuspidal Jacquet characterization and detection by refinement
as genuine prerequisites.

## A narrower pairing step

Bernstein–Zelevinsky 1977, Proposition 3.8, printed p.453, does not assume that
the highest derivative of its first representation is irreducible. Given a
mirabolic modular pairing nondegenerate in that argument, it gives an invariant
pairing of the two derivatives at that order, nondegenerate in the first
derivative.

Consequently, if that derivative has a nonzero irreducible submodule `sigma`,
restriction gives a pairing nondegenerate on `sigma`. This observation may
replace the use of highest-derivative irreducibility at one step of §9.8.
Worker 353 independently checked this limited source implication. It does not
verify the entire replacement argument.

The following obligations remain:

- Prove finite length and nonvanishing before selecting `sigma`.
- Respect the source convention
  `chi(g) * B(g v, g w) = B(v, w)`.
  The Library's [`InvariantBilinear.forms`](../../Langlands/Representation/Filtration/InvariantBilinear.md)
  instead places its character on the right side; these conventions use inverse
  characters. For evaluation against `nu * dual(omega)`, the required source
  character is the mirabolic modulus `Delta_P = nu^(-1)` from BZ77 §4.2.
- Construct the induced map from the second derivative to the **smooth** dual
  of `sigma`. Smooth-dual landing, irreducibility of that dual, and surjectivity
  of the nonzero map must all be justified.
- Prove the normalized derivative functors, their exactness and product
  filtration, twist compatibility, and the individual special-head formula.
  Use actual cuspidal-support results to turn constituent relations into
  terminal and initial truncation descriptions.

Proposition 3.8 gives a nonzero derivative at the same order on the second
side. It does not state that this derivative is the highest one, nor a
highest-derivative duality equality.

## Further proposed replacements, still unproved

For the top derivative of an individual special head, one possible route starts
from an independently proved realization as the socle of the decreasing
cuspidal product. BZ77 Theorem 4.11 can then rule out a degenerate submodule,
provided its ordering condition is established using integral twist freeness.
Exactness and the top derivative of the cuspidal product would give dimension
one. The reverse-socle realization, Theorem 4.11 in the actual constructions,
and all these derivative inputs must be proved; the observation alone does not
replace Proposition 9.6.

For the linked-pair converse, a possible replacement for 8.4 uses uniqueness
of the nondegenerate constituent of a fixed cuspidal product. After proving the
unlinked sufficient direction, the union/intersection product would be
irreducible and nondegenerate. If the linked product were irreducible,
placing both in a common cuspidal product with top derivative dimension one
would identify them. The derivative comparison of §9.9 would then distinguish
them. This still requires actual constituent induction, ordering changes,
duality and derivative calculations. The empty intersection is a unit factor,
not an empty `Segment`. Reduction from a full product to a linked pair also
requires exactness and nonvanishing of the remaining induction and tensor
factors.

These are proposed proof routes, not published Lean results or substitutes for
the task's exact target.

## Reusable lower exactness results

The current Library already contains the following independent lower results:

- `Langlands.Induction.smoothInductionSurjectivity` in
  [`Induction/SurjectivityProof`](../../Langlands/Representation/Induction/SurjectivityProof.md)
  proves surjectivity for a closed subgroup of a Hausdorff topological group
  with cofinal compact open subgroups. Its proof lifts compact fixed vectors
  and assembles actual functions on double cosets.
- `Langlands.Parabolic.inductionExactness` and
  `Langlands.Parabolic.normalizedInductionExactness` in
  [`Parabolic/InductionExactnessProof`](../../Langlands/Representation/Parabolic/InductionExactnessProof.md)
  prove exactness of the actual block-parabolic maps for arbitrary supplied
  p-adic topology. The normalized result twists by the actual positive
  half-character.
- `Langlands.Jacquet.Localization.characterLocalizationExactness` in
  [`Jacquet/LocalizationExactnessProof`](../../Langlands/Representation/Jacquet/LocalizationExactnessProof.md)
  proves compact relation detection and exactness of the actual
  **unnormalized** character-localization maps. Its hypotheses include
  containment of every compact subset of the localizing subgroup in a compact
  subgroup, local constancy of the character, and smoothness of the middle
  representation.

The first two proof modules and their statements were read in this audit,
and their independent acceptance and publication records were checked.
The localization statement and proof explanation were also read.
A traversal of the project imports at Library commit
`86de9288bcb005192e65e8ca0b7cd15e8bb8ba97` gives respectively 18, 51 and 20
modules, including each root; none imports classification, Whittaker or
derivative modules. This checks the relevant import separation, not the
missing derivative specialization. In particular, localization exactness
does not construct the mirabolic radical data, normalization, derivative
filtrations or pairing descent.

## Sources and reading boundary

Both originals are already registered:

- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II*
  (1980), `zelevinsky-1980-induced-ii`, SHA256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
  The audit read printed pp.181–183 and 195–201, with visual checks of the
  formulas on pp.195 and 198–200. The dependency findings above concern
  §§8.1, 8.4 and 9.5–9.9.
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I* (1977), `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
  The relevant readings are §§3.5–3.8 and 4.1–4.11, printed pp.452–457;
  the pairing convention and Proposition 3.8 were checked on pp.452–453.

No matching errata entry was located in the available project notes.
The proposed replacements are derived planning observations and are not
attributed to either original as completed proofs.

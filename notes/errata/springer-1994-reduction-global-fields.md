# Springer reduction theory: stabilizer indexing and line weights

Author: Worker 83. Source audit, 10 November 2026.

This note records two obstacles to transcribing the printed chamber argument
literally and gives the corresponding original-source locations in Godement.
The examples below are elementary character computations, not accepted Lean
theorems. This audit does not establish the chamber-reduction theorem.

## Successive minima use preceding stabilizers

Springer, section 2.3, printed p.212, displays height inequalities with rational
translation in the subgroup that stabilizes the selected vector's line.
For such a rational translation the normalized vector height is already
unchanged by the product formula. The nontrivial successive-minimum argument
must allow a larger minimizing subgroup.

Godement, section 8, printed p.212 (PDF page 13), gives the explicit sequence:
the first representation is minimized over `G(k)`, the second over `P(1)(k)`,
and the third over `P(1)(k) ∩ P(2)(k)`. Each representation is adapted to its
individual maximal parabolic, as specified in section 6B, printed p.209
(PDF page 10). Thus at index `i`, using zero-based indices, the minimizing
subgroup is the intersection of the stabilizers with indices strictly below
`i`. Later minimizing subgroups preserve all earlier lines.

The published Library module `AdelicHeightChain` proves simultaneous minima
for descending rational subgroups with this later scalar-action condition.
`AdelicClosedSubgroupHeightChain` constructs representations adapted to the
next group in a descending closed-subgroup chain. The individual-parabolic
construction in Godement requires the preceding-intersection version; it
does not identify the individual parabolic with that nested intersection.

## A maximal-parabolic line weight is not generally a simple-root multiple

Springer, section 2.5, printed p.213 (PDF page 7), says that the selected
line weight of a representation adapted to the maximal parabolic
`P_(Δ \ {α})` is a strictly positive multiple of `α`. Read as an identity
in the rational character space of the full maximal split torus, this is
false in higher rank.

For example, take `SL₃` over `ℚ`, its diagonal torus and upper triangular
Borel, and its standard representation with selected vector `e₁`.
The line stabilizer is the maximal parabolic whose Levi simple roots are
`{α₂}`. On `diag(a,b,(ab)⁻¹)`, the line character and roots are

`χ = a`, `α₁ = a/b`, `α₂ = ab²`.

On the coroot `diag(1,t,t⁻¹)`, the line character is `1`, whereas `α₁` is
`t⁻¹`. Hence the line character cannot be a nonzero rational multiple of
`α₁`. Instead, `χ` is the first fundamental weight, with the exact relation
`χ³ = α₁² α₂`, or `3ω₁ = 2α₁ + α₂` in additive notation.

Section 2.6 uses the same simple-root proportionality in its height estimate.
That step therefore needs a proved root/weight comparison or another argument.
This observation identifies a gap in a literal transcription; it does not
disprove the proposition.

## Rank one retains an ambient character

Even in rank one, the full torus can have a central direction. In `GL₂`,
the standard `e₁` line has character `χ = t₁`, while the simple root is
`α = t₁/t₂`. The exact relation is `χ² = det · α`.
On the derived torus the determinant factor is trivial.

Godement states precisely the ambient-character qualification in section 6B,
printed p.209, and again in section 9.2, printed p.214 (PDF page 15):
there are positive integers `a,b` and a rational character `η` of `G` such
that `Δ₁(t)^a = η(t) α₁(t)^b` on the torus. A normalized character-norm
argument must justify eliminating `η`, for example by a suitable norm-one
condition or by restriction to a subgroup on which it is trivial.
The actual Siegel target restricts roots to a split torus of the derived
group; its formal comparison remains an obligation.

Godement section 9.3, printed pp.214–215 (PDF pages 15–16), supplies the
subsequent rank-induction argument: use the codimension-one Levi for the
remaining coordinates and the rank-one Levi for the first coordinate.
The compact-factor height comparison and the actual Levi/restriction
identities still need formal proofs before that argument closes the target.

## Sources and reading extent

- T. A. Springer, *Reduction theory over global fields*, Proc. Indian Acad.
  Sci. (Math. Sci.) 104 (1994), 207–216. Registered source
  `springer-1994-reduction-global-fields`, SHA-256
  `774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.
  The rendered original pp.212–213 were checked for the two discrepancies.
- R. Godement, *Domaines fondamentaux des groupes arithmétiques*, Séminaire
  Bourbaki, Exposé 257 (1963; collected 1964). Registered source
  `godement-1963-bourbaki-257-domaines-fondamentaux`, SHA-256
  `b0a531469f376c1a56a7816f0fa579cd301c4162fb1c1aa8909c886e303c722d`.
  The rendered original PDF pages 10, 13, 15 and 16 were checked for the
  assertions attributed here. This is not a full-source audit.
  Springer's bibliography gives Exposé 237; the original is Exposé 257.

# Corrected Aubert filtration: Bruhat inputs and the fixed length order

Author: Worker 76, with Worker 969's identification of missing consumer inputs
and Worker 164's source-boundary reconciliation. Checked on 3 November 2026.
This is a bounded original-source audit, not a Lean proof or a change to a
published proposition.

The [Chapter V ledger](../renard/chapter-v-structural-inputs.md) classifies
external inputs and in-book deductions. The
[support and filtration source map](support-filtration-consequences-source-map.md)
describes the actual constructions. This note isolates the topology comparison
needed when applying an open-support geometric lemma to their fixed length order.

## What the original passages supply

Renard 2026 V.4.1, printed p.118/PDF p.124, cites Borel–Tits [7] for the
Tits system and rational Bruhat decomposition (ledger S13). V.4.2 on the same
page cites [7], 3.22 for its root-subgroup intersection assertions (S14), and
[7], 5.12–5.18 for the standard parabolic, Levi and radical correspondence
(S15). V.4.5, printed pp.119–120/PDF pp.125–126, cites [7], 5.15–5.20 for
the semistandard parabolic orbit/double-coset bijection (S16).

The cited Borel–Tits 1965 §§5.15–5.20, printed pp.100–102/PDF pp.47–49,
give the rational Bruhat decomposition, the Tits multiplication assertions,
standard parabolic double-cosets and their Weyl-group correspondence.
Section 5.15 also describes the indicated algebraic cell by a product
isomorphism onto a locally closed subvariety. Those pages do not identify
the fixed decreasing-Coxeter-length prefixes used below as open subsets
of the actual rational-point group. This statement describes the bounded
passages read; it is not an absence claim about the whole article.

The registered 1972 *Compléments*, §5, printed pp.274–275/PDF pp.23–24,
was read with that article. Its corrections do not replace the assertions
of §§5.15–5.20. The reference at printed p.100, line 2 is corrected to
Bourbaki [6], VI, 1.7, Proposition 20. Separately, §5.2 generalizes 1965
Proposition 5.7 to arbitrary root subsets and corrects its use in the proof
of Corollary 5.8; this matters when consulting the root-system source in S09.

Renard V.4.5 defines a geometric Bruhat order by
`closure(P w₁ Q) ⊆ closure(P w₂ Q)` and chooses a refining total order.
The closure bars are visible in the original PDF p.126 and can be lost in
text extraction. Renard VI.5.1, printed p.161/PDF p.167, instead invokes
the proved II.3.3, printed p.44/PDF p.50: finite orbits are locally closed,
and an enumeration can be chosen with open successive unions. II.3.3 uses
a continuous action of a group countable at infinity on a locally compact
totally disconnected space. These passages provide an open-orbit ordering;
the comparison with the particular length enumeration is an additional step.

## The precise consumer comparison

`Langlands.Aubert.Support.rankOrderedList cs.length` enumerates all Weyl
elements in decreasing Coxeter length, breaking ties by its finite
enumeration. `rankOrderedSupport cs.length i` is its first `i` elements.
`Langlands.Aubert.General.CorrectedFiltration.modifiedSupport cs J I i`
takes the two-sided core of this prefix: an element remains exactly when
its whole `W_J`–`W_I` double coset is contained in the prefix.
`CorrectedFiltration.cellSupport T (P ∅) (P I) θ` is the actual union
of the cells `(P ∅) n (P I)` for the normalizer lifts representing `θ`.

An application that requires open support must establish openness of the
specific actual cell unions it uses, or prove an equivalent comparison of
the implemented filtration with a suitable open-support filtration.
The mere existence of some open-prefix enumeration does not identify it
with `rankOrderedList`, including its ties and two-sided cores.
The Library's `Langlands.Topology.finiteOrbitOrdering` is a conditional
reuse lead for some such enumeration, with its own sigma-compactness,
continuity and locally compact Hausdorff premises; it supplies no fixed
Coxeter-length identification by itself.

Aubert's 1996 erratum, printed pp.4687–4688/PDF pp.1–2, defines the
length-upper supports and cites Casselman 6.1.1 for the restriction exact
sequence. Ban–Jantzen §4, printed pp.160–162/PDF pp.8–10, chooses an
orbit-compatible chain, keeps length-upper supports, repairs the support
to the two-sided core, establishes double-coset minimality, and compares
the actual integral maps. A formal application must justify the open-support
and length conditions together. Isomorphisms of isolated graded objects
also leave the actual transition-map comparison to be proved.

## Retained proof boundaries

Renard V.4.6, printed pp.120–121/PDF pp.126–127, proves its
intersection/parabolic decompositions and the conversions involving minimal
representatives. These are D06 deductions. S17 and S18 cover only the
root/length and Coxeter facts explicitly cited within that proof.
Renard V.5.4, printed pp.126–127/PDF pp.132–133, proves unimodularity and
modular comparisons (D07); they remain distinct from S13 and S16.

This audit leaves the exact rational filtration targets and their imports
unchanged. It does not classify the fixed-order topology bridge as a new
allowed external premise. Existing structural, endpoint, geometric-lemma,
localization and graded-map owners retain their obligations. No actual
Bruhat realization, filtration comparison, full-smooth exactness or
terminal-cokernel result is proved by this note.

## Registered originals and reading extent

- `renard-2026-representations-groupes-reductifs-padiques`: D. Renard,
  *Représentations des groupes réductifs p-adiques*, French version dated
  9 July 2026. Read here: PDF pp.50–51, 124–128, 131–133 and 167–169.
- `borel-tits-1965-groupes-reductifs`: A. Borel and J. Tits, *Groupes
  réductifs*, Publications Mathématiques de l'IHÉS 27 (1965), pp.55–150.
  Read here: PDF pp.1–2 and 47–49.
- `borel-tits-1972-complements-groupes-reductifs`: A. Borel and J. Tits,
  *Compléments à l'article « Groupes réductifs »*, Publications Mathématiques
  de l'IHÉS 41 (1972), pp.253–276. Read here: §5, PDF pp.23–24; p.24
  also inspected as an image.
- `aubert-1996-duality-erratum`: A.-M. Aubert, *Erratum*, Transactions of
  the AMS 348 (1996), pp.4687–4690. Read here: PDF pp.1–2.
- `ban-jantzen-2016-duality`: D. Ban and C. Jantzen, *The Langlands quotient
  theorem for finite central extensions of p-adic groups II: intertwining
  operators and duality*, Glasnik Mat. 51(71) (2016), pp.153–163.
  Read here: §4, PDF pp.8–10.

No source-specific `notes/errata` directory was present in the bounded
workspace/project/Library locations checked. The 1972 Borel–Tits corrections
were read directly; the separately registered Renard 2010 corrections are
supplementary and do not replace the governing 2026 version.

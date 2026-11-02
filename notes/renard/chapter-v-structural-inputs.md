# Renard Chapter V: structural inputs and retained proof obligations

This is a source ledger for the common reductive-group interface used by the
general Aubert and Plancherel programs. It distinguishes assertions Renard imports
from algebraic-group or Bruhat–Tits theory from objects that must be constructed
and assertions that he proves. The ledger does not supply a Lean realization or
prove any representation-theoretic result.

The audited source is the French edition of Renard dated 9 July 2026, registered
as `renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 164 read all of Chapter V, printed pages 103–129 (PDF pages 109–135),
and the bibliography, printed pages 281–283 (PDF pages 287–289).
All PDF page numbers here are one-based. No separate project errata record for
this edition was found in this audit.

The bracketed reference numbers below are **Renard's bibliography numbers**.
They report his citations, including their granularity; this note does not claim
an independent reading or verification of those cited originals. A consumer
needing a sharper external theorem statement must check that original.

## Scope and conventions

Let \(F\) be a nonarchimedean local field and \(\mathbf G\) a connected reductive
algebraic group over \(F\), with actual rational-point group \(G=\mathbf G(F)\).
The scope includes positive characteristic, nonsplit and nonquasisplit groups.
The characteristic-zero restriction in V.2.1 concerns finiteness of rational
conjugacy classes of maximal tori; it must not become a hypothesis on the whole
framework.

Fix a maximal \(F\)-split torus \(A_0\), a minimal parabolic \(P_0=M_0N_0\)
with \(M_0=Z_G(A_0)\), and a positive system with simple roots \(\Delta_0\).
Renard denotes these by subscripts \(\varnothing\). His relative Weyl group is

\[
 W_G=N_G(A_0)/Z_G(A_0)=N_G(A_0)/M_0.
\]

For a standard Levi \(M\), \(W_M=N_M(A_0)/Z_M(A_0)\), with its canonical
embedding in \(W_G\). The denominator is the centralizer. Replacing it by
\(A_0\) changes the object in general. The empty set \(\Delta_0\) is allowed;
finite indexing and subsequent constructions must cover that case.

For a nonminimal Levi with split component \(A_M\), V.3.14 explicitly warns
that \(\Delta(P)\) need not be a simple system of a root system. The root-system
assertion in V.3.7 is for a **minimal** parabolic.

## Finite ledger of externally sourced structural assertions

Each row is a source boundary, not a proposed Lean declaration or a free choice
of abstract data. Even when a cited assertion is used as an external structural
input, its groups, maps, topologies and indexing sets must be the actual objects.
The row identifiers are stable handles for consumer matrices.

| Row | Renard locator, printed / PDF pages | Structural assertion and reported external citation |
| --- | --- | --- |
| S01 | V.1, 103–104 / 109–110 | Local-field facts: normalized discrete valuation, uniformizer decomposition, finite residue field, absolute-value topology, compact open ideals and additive Haar scaling. Renard refers to [21] for the section. Choose the field, valuation and uniformizer explicitly; their defining formulas and intrinsic laws retain construction/proof obligations. |
| S02 | V.2.1, 104 / 110 | Algebraic-group structure: radicals and unipotent radicals; rationality and reductivity properties of the derived group and center; the finite central intersection and generation assertions. Section-level reference: [42]. Definitions of radical, reductive group, center and derived group are not assertions to assume in place of constructions. |
| S03 | V.2.1, 104 / 110 | Maximal tori: existence over \(F\), self-centralizing property in a reductive group, conjugacy of maximal \(F\)-split tori. Only the additional finiteness assertion for rational conjugacy classes of maximal tori is stated under characteristic zero. Section-level reference: [42]. |
| S04 | V.2.1, 104 / 110 | Rational linear embedding and independence of the induced totally disconnected rational-point topology from the embedding. Section-level reference: [42]. A Lean adapter must produce the actual topology and its required local compactness and nonarchimedean instances. The unimodularity assertion printed here has a proof later in V.5.4; see D07. |
| S05 | V.2.2, 105 / 111 | Recalled torus facts: character lattice, cocharacters and exponent pairing, coordinate group algebra, and almost-direct split/anisotropic decomposition. These occur within the algebraic-group recall boundary of V.2.1; V.2.2 gives no more precise external theorem locator. Definitions, restriction maps, dual identifications and the displayed abelianization/full-rank deductions must still be implemented and proved. |
| S06 | V.3.1, 110 / 116 | Rational Levi existence \(P=MN\), centralizer description using a split component, and transitivity of \(N\)-conjugation on Levi factors and split components. V.3's opening refers to [7] or [42], without an individual theorem number here. The semidirect notation requires actual inclusions, normalization, trivial intersection and product. |
| S07 | V.3.1–V.3.2, 110 / 116 | Finiteness of the parabolics with fixed Levi; unique opposite with intersection \(M\); characterization and conjugacy of minimal parabolics and maximal split tori. Same section-level references [7] or [42]. |
| S08 | V.3.5, 110–111 / 116–117 | \(N_G(A_M)/Z_G(A_M)=N_G(A_M)/M=N_G(M)/M\), with faithful action on the character/cocharacter lattices. Same section-level references [7] or [42]. The quotients, actions and induced identifications require actual constructions. |
| S09 | V.3.7, 111 / 117 | For a minimal parabolic, the reduced relative roots form a root system and its Weyl group identifies with the normalizer quotient: [7], Corollary 5.8 and 5.3 respectively. The root and coroot spanning assertions are also stated here; their implementation must retain the central summand described in V.3.6. |
| S10 | V.3.8–V.3.9, 111–112 / 117–118 | A semistandard parabolic has a unique Levi containing \(A_0\); all parabolics are conjugate to standard ones. Definitions of standard and semistandard are separate. The assertions use the section-level [7] or [42] boundary. |
| S11 | V.3.10–V.3.11, 112 / 118 | Semistandard intersection decompositions and the bijection between parabolics of a Levi and parabolics of \(G\) contained in the chosen parabolic, with its displayed intersection inverse. Same section-level references. Actual subgroup intersections, products and inverse laws must be exposed. |
| S12 | V.3.12, 112 / 118 | Simple roots and coroots are bases of the corresponding relative vector spaces. Same section-level references, with the root-system input of S09. Fundamental weights and coweights are constructed as dual bases, rather than supplied as unrelated data. |
| S13 | V.4.1, 118 / 124 | The Tits system and Bruhat decomposition for \(G,P_0,N_G(A_0)\) and the simple reflections. Proposition cites [7], without a narrower locator. |
| S14 | V.4.2, 118 / 124 | Intersections of the groups generated by convex closed root subsets, and intersections with the unipotent group attached to a unipotent subset: [7], 3.22. Closed/convex/unipotent subsets and the generated groups have their displayed definitions. |
| S15 | V.4.2, 118 / 124 | Standard parabolics, their Levi factors and radicals correspond to subsets of \(\Delta_0\), with uniqueness and the asserted convexity: [7], 5.12–5.18. |
| S16 | V.4.5, 119–120 / 125–126 | The bijection from the right-\(Q\) orbit set \((P\backslash G)/Q\) to \(W_M\backslash W_G/W_L\) for the stated semistandard parabolics with standard Levis. Renard refers to [7], 5.15–5.20. The arbitrary-parabolic finite-orbit corollary is then proved by conjugation. |
| S17 | Proof of V.4.6(i), 120–121 / 126–127 | Three root/length facts: length is the number of positive roots made negative; a Levi Weyl group preserves complementary positive roots; and, for \(\gamma\in\Delta_0\), \(\ell(ws_\gamma)>\ell(w)\) iff \(w\gamma\) is positive. Renard cites [43], Appendices I and II. |
| S18 | Proof of V.4.6(i), 121 / 127 | The Coxeter result giving the minimal representatives of double cosets from the length inequalities. Renard cites [9], Chapter IV, §1, Exercise 3, and also [19], Proposition 2.7.3. Renard's conversion between the subgroup and root conditions, and the remaining parts of V.4.6, are separate deductions. |
| S19 | V.5.1, 122 / 128 | Existence of a compact open maximal \(K_0\) adapted to \(A_0\), with the five stated properties: Iwasawa decomposition; Weyl representatives in \(K_0\); \(K_0\cap P=(K_0\cap M)(K_0\cap N)\); Cartan decomposition with the specified \(\widetilde C_0^+\); and the corresponding properties inside every standard Levi. V.5's opening cites [14]; no narrower locator is supplied for this theorem. |
| S20 | V.5.2(i), 123 / 129 | A basis of identity neighborhoods consisting of compact open subgroups \(K\) normal in the same \(K_0\). The theorem explicitly cites [24], §2.1. |
| S21 | V.5.2(ii), 123 / 129 | Simultaneously for all standard \(P=MN\), \(K=K_{\bar N}K_MK_N\); \(C_A\) normalizes \(K_M\), \(C_A^+\) contracts \(K_N\), and \(C_A^-=(C_A^+)^{-1}\) contracts \(K_{\bar N}\). Same [24], §2.1. The named intersections are actual subgroups. |
| S22 | V.5.2(iii), 123 / 129 | For \(m\in C_A^{++}\), \(N=\bigcup_n m^{-n}K_Nm^n\) and \(\bar N=\bigcup_n m^nK_{\bar N}m^{-n}\), together with the stated uniform containment of every compact subset for all sufficiently contracting chamber elements. Same [24], §2.1. This is a structural compact-containment input, not localization exactness. |
| S23 | V.5.2(iv), 123 / 129 | The contracting powers \(m^iK_Nm^{-i}\) and \(m^{-i}K_{\bar N}m^i\) form neighborhood bases, with the stronger uniform cofinality statement for every compact open subgroup. Same [24], §2.1. |

Here \(C_A,C_A^+,C_A^{++}\) and \(\widetilde C_0^+\) retain Renard's
definitions from V.2.5 and V.3.21–V.3.23. Their construction and comparison with
the actual character lattice are not hidden inside S19–S23.

## Definitions and deductions that remain to be implemented or proved

These entries prevent the external ledger from absorbing the book's arguments.
They do not assert that every elementary subfact used in an argument has already
been justified.

| Row | Source location | Retained obligation |
| --- | --- | --- |
| D01 | V.2.1–V.2.2, 104–105 / 110–111 | Construct the split component, characters, cocharacter lattices and restrictions; prove the displayed uniqueness, abelianization, finite-index/rank and duality deductions. |
| D02 | V.2.3–V.2.6, 105–108 / 111–114 | Construct \(H_G\) by valuation of actual rational characters, its kernel \({}^0G\), image \(\Lambda(G)\), exact sequence, unramified-character torus and evaluation algebra. Prove the homomorphism, openness/closedness/normality, compact/derived containment, split-torus section, lattice-index and finite-quotient conclusions. Compactness and cocompactness subfacts invoked in these arguments without an individual citation must be identified and justified separately. Unimodularity of \({}^0G\) uses that of \(G\), proved in V.5.4. |
| D03 | V.2.7, 108–109 / 114–115 | Finite unramified-twist stabilizers use Schur's lemma for representations; the orbit-torus conclusion is derived. These are representation-theoretic obligations. |
| D04 | V.3.3–V.3.6 and V.3.12–V.3.17, 110–114 / 116–120 | Construct the real vector spaces, pairings, central/relative decompositions, projections, restricted-root notation, dual bases, chambers and cones, and prove their stated comparisons and decompositions. V.3.17 includes its own proof. A general root-system premise does not supply every one of these maps or laws. |
| D05 | V.3.18–V.3.25, 114–117 / 120–123; V.5.5, 127–129 / 133–135 | The combinatorial Langlands lemma is proved at the end of the chapter, adapted from [18]. The smooth real-character, exponential/unitary unramified-torus, cone and section arguments are also retained. The \(\mathbb N^d\) monoid description in V.3.24 requires its actual lattice argument; finite index alone does not establish that description. This note does not assert a source error there. |
| D06 | V.4.3–V.4.8, 119–122 / 125–128 | Construct the Levi Weyl embedding and lift-independent conjugation, prove \(W(M,M)/W_M\simeq N_G(M)/M\), define the sets in V.4.4, and derive the arbitrary-parabolic orbit result. Implement V.4.6's equivalence with length-minimal representatives, intersection/parabolic decompositions and quotient identification, and V.4.7–V.4.8's conjugation and maximal-Levi arguments. S17–S18 cover only the cited inputs used in the proof. |
| D07 | V.5.1 corollary, 123 / 129; V.5.3–V.5.4, 123–127 / 129–133 | Prove compactness of \(G/P\) and the \(K_0\)-conjugacy corollary; the Hecke-algebra product, commutativity, generation and decomposition results; unimodularity of \(G\); and the modular-function comparisons and root-product formula. In particular unimodularity is not an additional external premise merely because it is announced in V.2.1. |
| D08 | V.5.5, 127–129 / 133–135 | Supply the finite-dimensional Euclidean projection and cone arguments, including equivalences left to the reader. Existing projection theorems can be reused with their exact closedness, convexity and nonemptiness hypotheses; this analytic step is not part of the algebraic-group or Bruhat–Tits exception. |

Choosing actual quotients, subgroup inclusions, conjugation maps, orderings,
representatives and sections also entails their well-definedness and intrinsic
laws. A finite orbit bijection alone does not construct a total ordering
compatible with orbit closure. Such ordering and closure properties must be
stated and proved where the support filtration consumes them.

Exactness, finite-length preservation, adjunctions, the geometric lemma,
cuspidal support, Weyl invariance on representation Grothendieck groups and
Langlands classification are representation-theoretic results. None is an
external structural field authorized by S01–S23. The standalone Aubert program's
permission to use classification does not identify classification with one of
these structural rows.

## Modulus orientation and available generic constructions

Renard V.5.4 proves unimodularity and then
\(\delta_{P\backslash G}(m)=\delta_G(m)/\delta_P(m)=\delta_P(m)^{-1}\).
For \(a\in A_M\), the quotient modulus is the product

\[
 \delta_{P\backslash G}(a)
 =\prod_{\gamma\in\Sigma(P)}
   |\gamma(a)|_F^{\,m_\gamma+2m_{2\gamma}}.
\]

Opposite radicals and inverse powers must be preserved when transferring the
other displayed equalities in that section; text extraction loses some
overbars. Naming the function “modulus” is insufficient to fix its orientation.

The following current Library constructions can be reused by their Lean names.
Their companion Markdown was inspected for this note. This table records
declaration scope, rather than a new acceptance or publication audit.

| Module / declarations | Actual construction and limits |
| --- | --- |
| [`Langlands.Group.HaarModulus`](../../Langlands/Group/HaarModulus.md): `Langlands.HaarModulus.normalizerConj`, `normalizerCharacter`, `normalizerCharacter_smul_map`, `integral_normalizerConj_symm` | For an actual subgroup \(U\) of a topological group and locally compact \(U\), constructs conjugation and its positive character. With \(c\) its value and \(\alpha(u)=gug^{-1}\), the convention is \(c\,\alpha_*\mu=\mu\) and \(\int f(\alpha^{-1}u)\,d\mu=c\int f(u)\,d\mu\). It requires no Hausdorff assumption. Identification with Renard's quotient/root modulus remains a bridge to prove. |
| Same module: `restrictCharacter`, `halfCharacter`, `inverseHalfCharacter`, and the `closed…` wrappers | Restricts the actual normalizer character along a normalizing subgroup; constructs canonical positive half and inverse half characters and proves square laws. Nonarchimedeanness gives the proved open-kernel and smooth-twist results. Closed-subgroup wrappers use ambient local compactness and subgroup closedness. Positive half is the generic induction normalization and inverse half the localization normalization; the reductive specialization still needs the modulus bridge. |
| [`Langlands.Representation.Geometric.GeneralIntersections`](../../Langlands/Representation/Geometric/GeneralIntersections.md): `Langlands.Geometric.General.intersectionIn`, `intersectionEquivContinuous`, `SixDecomposable` | Constructs actual subgroup intersections and continuous conjugation equivalences. `SixDecomposable` is a predicate expressing six product equalities, not a proof that reductive parabolics satisfy them. |
| [`Langlands.Representation.Geometric.GeneralCorrectionCharacters`](../../Langlands/Representation/Geometric/GeneralCorrectionCharacters.md): `Langlands.Geometric.General.haarCorrectionCharacter` | Constructs correction characters from the actual Haar moduli of closed subgroups and intersections, with square and open-kernel laws. Supplies no orbit-piece comparison or geometric-lemma proof. |
| [`Langlands.Representation.Jacquet.Localization`](../../Langlands/Representation/Jacquet/Localization.md): `Langlands.Jacquet.Localization.relations`, `Coinvariants`, `mk`, `action`, `map`, `smoothFunctor` | Constructs the actual quotient by the span of \(\rho(u)v-\theta(u)v\), the normalizing-subgroup action, maps and smoothness descent over a commutative ring, with independent group and carrier universes. This is not an exactness proof. |
| [`Langlands.Topology.CompactOpen.NeighborhoodBasis`](../../Langlands/Topology/CompactOpen/NeighborhoodBasis.md) and [`Langlands.Topology.Nonarchimedean.Subgroup`](../../Langlands/Topology/Nonarchimedean/Subgroup.md): `Langlands.compactOpenSubgroupBasis`, `Langlands.subgroupNonarchimedean` | Generic proved topology tools. Rational-point instances and the stronger simultaneous contraction properties S20–S23 still need their actual-group adapters. |

`Langlands.RootWeightConeDecompositionStatement` is a proposition target, not
a proof. The block-permutation constructions `Langlands.Geometric.blockWeyl`
and `MinimalRepresentatives` do not provide the general relative Weyl group.
The shared unreviewed group-side draft, revision 17 of task
`a2a442fc-f72b-43ea-a3f3-bcfd61415ccc`, and the closed-semidirect draft, revision 2
of `82bfcc29-81a6-4092-9b9c-f089d2abfb76`, remain designs. Their presence does
not establish an accepted general reductive realization or any closing proof.

## Use by the Aubert and Plancherel consumers

Use one common actual-group interface. For every structural field a consumer
uses, record the ledger row, exact source hypothesis, actual Lean declaration
and realization, and the proof/publication status of the required bridge.
If no declaration exists, record that missing construction explicitly.
Consumer-specific normalizations require their own comparison theorems.
This note supplies the common source column; it is not the completed consumer
matrix or the final theorem-classification matrix of either program.

The Aubert adapter and relative-Weyl units are tasks
`593ef603-6672-4424-976c-14e11e920d9c` and
`e3d69272-2599-4a08-a934-cb11f2493e30`. Their coordination can implement one
shared realization without duplicating the generic subgroup constructions.
The Plancherel program is `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927`.
These identifiers locate work; they are not evidence that its results are
accepted. Existing task holds and independent review requirements are unchanged.

This focused Chapter V ledger refines the preliminary V.1–opening-V.2.3
classifications in [the initial passage audit](initial-passages.md), especially
the treatment of unimodularity, and supplements the navigation in
[the Renard coverage note](coverage.md). Those notes' historical reading extents
are not a claim that the present audit was already available.

## Renard bibliography keys used here

These are bibliographic identifications transcribed from the audited Renard
edition, rather than independently audited source registrations:

- [7] Borel–Tits, *Groupes réductifs*, IHÉS Publications Mathématiques 27
  (1965), 55–150.
- [9] Bourbaki, *Groupes et algèbres de Lie*, Chapters IV–VI, Hermann, 1968.
- [14] Bruhat–Tits, *Groupes réductifs sur un corps local*, IHÉS Publications
  Mathématiques 41 (1972), 5–251.
- [18] Carmona, *Sur la classification des modules admissibles irréductibles*,
  Lecture Notes in Mathematics 1020 (1983), 11–34.
- [19] Carter, *Finite Groups of Lie Type*, 1993 reprint of the 1985 original.
- [21] Cassels–Fröhlich, editors, *Algebraic Number Theory*, 1986 reprint of 1967.
- [24] Deligne, *Le “centre” de Bernstein*, in *Representations of Reductive
  Groups over a Local Field*, 1984, 1–32.
- [42] Springer, *Linear Algebraic Groups*, second edition, 1998.
- [43] Steinberg, *Lectures on Chevalley Groups*, Yale, 1968, notes by
  Faulkner and Wilson.

Author: Worker 164. Workers 8 and 14 contributed the generic-interface and
scope guidance incorporated above. The source classification and its reading
record are Worker 164's audit; this attribution does not assign the cited
originals or existing Library constructions to this note's authors.

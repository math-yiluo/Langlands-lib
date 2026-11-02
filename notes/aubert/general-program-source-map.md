# General Aubert duality: corrected sources and reuse boundaries

This note records the source conventions and initial reuse map for the standalone
general Aubert program, task `46df6a68-5db4-4428-8044-05151d6ce1f6`.
Its five result families concern connected reductive groups over arbitrary
nonarchimedean local fields, with complex coefficients. They include nonsplit
and nonquasisplit groups, permitted positive characteristic, and relative
semisimple rank zero. Existing GL results and generic linear algebra supply
parts of the implementation; their hypotheses still have to match each general
application.

The [earlier Aubert source note](../henniart/aubert-duality-route.md) gives the
correction map and the restrictions of its upstream classification consumer.
This standalone program permits Langlands classification. It must nevertheless
record classification dependencies, including those introduced transitively by
helper theorems. That permission supplies neither a proof of classification nor
a proof of a theorem that uses it.

This is a focused source and reuse ledger. It supplies no new Lean declarations
or theorem proofs. The final source-to-declaration and transitive-dependency
matrices remain to be assembled from published general targets and their actual
proofs. The task identifiers below locate assigned work; they are not acceptance
or publication evidence.

## Actual groups, exact classes and signs

Fix a maximal split torus \(T_0\), a minimal parabolic and its positive relative
roots, with simple-root set \(S\). The standard Levi \(L_I\) is indexed by
\(I\subseteq S\). The relative rational-point Weyl groups are

\[
 W=N_G(T_0)/Z_G(T_0),\qquad
 W_I=N_{L_I}(T_0)/Z_G(T_0),\qquad
 L_\varnothing=Z_G(T_0).
\]

The quotients printed with denominator \(T_0\) in Aubert, p.2180, require this
centralizer correction for nonsplit groups. The common interface must construct
the actual subgroups, quotients, inclusions and conjugations and relate the
finite root indexing to them. The empty set \(S\) is allowed.

Aubert's group \(\mathcal R(G)\) is the exact Grothendieck group of actual smooth
finite-length complex representations. Its relations include all short exact
sequences, including nonsplit ones. On this group Definition 1.5, p.2181, is

\[
 D_G=\sum_{I\subseteq S}(-1)^{|I|}i_I^G r_I^G .
\]

Here both functors are normalized. The positive induction half-modulus, inverse
Jacquet half-modulus, conjugation direction and coefficient/carrier universes
must be carried through the adapters. A chosen character named “modulus” does
not by itself establish the comparison with the source normalization.

The support-sign adjustment of Definition 2.1, p.2184, multiplies this operator
by \((-1)^{|I|}\) on an irreducible of cuspidal-support type \(\{I\}\), then
extends additively. It is a separate operator. For a segment of length \(k\) and
total rank \(n\), Remark 2.2 gives \(|I|=n-k\).

## Source targets for the five families

Page numbers in this table are printed page numbers.

| Family | Source passages | Required mathematical content and retained obligations |
| --- | --- | --- |
| Exact group and operator | Aubert 1995, pp.2180–2181, identities (1.1)–(1.4), Definition 1.5 | Actual normalized induction, Jacquet, conjugation and smooth-dual maps; their finiteness and exactness justifications; actual exact classes and the unadjusted alternating sum. Transitivity, the geometric lemma and Weyl invariance of induced classes are separately named representation-theoretic inputs. |
| Formal identities | Theorem 1.7, pp.2181–2183; Corollary 1.10, p.2183 | Smooth-dual commutation, induction compatibility, associated-Levi Jacquet compatibility, involutivity and the cuspidal sign, together with the two corollary assertions. The source proof uses (1.1)–(1.4) and finite Weyl cancellation, including the Solomon identity cited on p.2182. It precedes the defective Proposition 3.2. |
| Corrected actual complex | Aubert 1995, pp.2186–2187; erratum, pp.4687–4690; Ban–Jantzen §4, pp.160–162, with the corrections below | Actual \(E_J=i_J^G r_J^G E\), quotient-induced transition maps, orientation lines, differential and terminal cokernel. Corrected exactness and the associated-Levi Jacquet comparison have the full smooth \(\operatorname{Alg}(\{I\})\) scope. The finite Weyl filtration does not impose finite length on \(E\). |
| Finite-length and irreducible consequences | Aubert 1995, Corollary 3.9, p.2189; corrected complex and erratum p.4690 | Finite length of \(E^\#\), the formula \(D_G[E]=(-1)^{|I|}[E^\#]\), extension along composition series, nonzero irreducibility, support retention and actual biduality for irreducibles. Exactness, length and nonvanishing steps remain proof obligations. |
| GL and Zelevinsky comparison | Aubert 1995, pp.2183–2185, Definition 2.1, Remark 2.2 and Theorem 2.3 | Comparison with the current actual GL models and their unadjusted operator, the support-sign adjustment, segment exchange and equality on the whole graded Grothendieck ring. Include \(G_0=\{e\}\), the degree-zero unit and the polynomial/monomial comparison. |

For the Jacquet identity in Theorem 1.7, use Aubert's \(w_J\): the longest element
in \(\mathcal D(J,\varnothing)\), with \(w_J^{-1}(J)\) positive and
\(w_J^{-1}(S\setminus J)\) negative. Put \(J'=w_J^{-1}(J)\), as in p.2180.
With actual transport between the associated Levis, the class identity is

\[
 r_J^G D_G=\operatorname{Ad}(w_J)\,D_{L_{J'}}\,r_{J'}^G .
\]

The conjugation is part of the formula. It cannot be replaced by an equality of
unrelated Levi labels. The cuspidal eigenvalue of the unadjusted operator is
\((-1)^{|S|}\).

Corollary 1.10 begins with an irreducible cuspidal \(\sigma\) of \(L_J\).
When \(i_J^G\sigma\) is irreducible, its eigenvalue is \((-1)^{|J|}\).
In the reducible case with \(J=S\setminus\{\alpha\}\), the proof uses length two
and the constituent Jacquet assertions cited to Casselman §7.1, as well as
identity (1.2). Its conclusion exchanges the constituent classes:
\((-1)^{|J|}D_G[\rho_\pm]=[\rho_\mp]\).
The general length-two and Jacquet assertions require their own proofs or exact
published reuse. A GL-specific tempered-induction theorem does not supply them.

## The repaired complex and the surviving terminal module

The terms on pp.2186–2187 have the exterior orientation line
\(\bigwedge^{|S\setminus J|}\mathbb C^{S\setminus J}\) attached to \(E_J\).
The maps come from the actual Jacquet quotient maps followed by induction,
with the exterior signs. The construction must expose those maps, their
composition laws and square-zero differential.

The erratum withdraws the proof of Proposition 3.2 and leaves the proposition
unresolved. The failed homogeneous-space identification does not disprove the
proposition. The original proof of Theorem 3.6 using it cannot establish the
complex theorem.

For \(E\in\operatorname{Alg}(\{I\})\), the corrected theorem on p.4687 has the
shape

\[
 0\longrightarrow E
 \longrightarrow\bigoplus_{|J|=|S|-1}\widetilde E_J
 \longrightarrow\cdots
 \longrightarrow\bigoplus_{|J|=|I|}\widetilde E_J .
\]

Here \(\operatorname{Alg}(\{I\})\) is the full smooth category whose irreducible
subquotients have cuspidal support associated to \(L_I\). Finite length is not a
premise. The assertion is exactness before the terminal term. There is no final
zero killing its cokernel \(E^\#\). With degree counting removed roots, that
term has degree \(|S|-|I|\). If \(|I|=|S|\), the terminal term is \(E\) and its
incoming map is zero; its cokernel is \(E\). Exactness does not demand that the
outgoing zero map from this terminal term be injective.

The repair uses, for each target/source pair, the two-sided modified support

\[
 \theta^{J,I}
   =\{x\in\theta:W_JxW_I\subseteq\theta\}.
\]

The correction map comes from the retained audit and the earlier source note;
the relevant original passages in the erratum and Ban–Jantzen were also checked.
The implementation needs the following sequence of deductions.

1. Compare consecutive modified supports
   \(\theta_i'\) and \(\theta_{i+1}'\). If they differ and
   \(\theta_i\setminus\theta_{i+1}=\{w\}\), saturation shows that the full
   double coset \(W_JwW_I\) lies in \(\theta_i\), while all its elements other
   than \(w\) lie in \(\theta_{i+1}\).
2. Use the chosen length filtration: every element still in
   \(\theta_{i+1}\) has length at least \(\ell(w)\). Thus \(w\) is minimal in
   its double coset before applying the geometric lemma. A left-coset
   condition alone does not justify that application.
3. Apply the geometric lemma and the support-type hypothesis to the resulting
   grade. The latter forces \(wW_Iw^{-1}\subseteq W_J\) in the surviving case.
4. Compare the actual transition maps on these grades. Ban–Jantzen p.162 uses
   composition of Jacquet quotient maps and equality of the integration
   subgroups to obtain the identity maps, up to the exterior signs. An
   isomorphism between the objects in each grade does not prove this map
   comparison.
5. Apply Boolean/Koszul contraction to grades with a free coordinate and retain
   the coefficient module on a singleton interval. Lift the resulting
   exactness through the finite filtration, preserving terminal homology.

Two wording corrections in Ban–Jantzen matter. The p.161 parenthetical must
compare the consecutive modified supports, rather than \(\theta_i'\) with
\(\theta_i\). The p.160 claim of exactness for the whole displayed complex
ending in zero cannot be used literally: that would erase the duality module.
The truncation above states the required theorem.

On p.4690 the erratum defines the terminal module and compares its Jacquet
module with the corresponding duality module for the associated Levi:

\[
 r_I^G\widetilde D_G(E)
   \simeq \operatorname{Ad}(w_I)
       \widetilde D_{L_{I'}}(r_{I'}^G E),\qquad I'=w_I^{-1}(I).
\]

This is a module comparison at the stated full-smooth scope. Its canonical
maps and normalization remain part of the target. The class formula
\(D_G[E]=(-1)^{|I|}[E^\#]\) is interpreted only after finite length is justified.

For the finite-length extension used by Corollary 3.9, record termwise
exactness and the composition-length induction. For irreducibles, prove finite
length, nonvanishing and irreducibility of \(E^\#\), its support type, and
biduality. Equality of arbitrary exact Grothendieck classes supplies no module
isomorphism. Once both actual modules are known to be irreducible, the generic
faithful irreducible-class comparison can recover an isomorphism from equality
of their classes.

## GL translation and the whole-ring obligation

On p.2184 the tensor product of the two Grothendieck groups corresponds to the
product Levi. Normalized induction maps it to the larger GL group's
Grothendieck group. It is not an identification with that larger group.
The induction identity invoked there is Theorem 1.7(2).

Theorem 2.3 identifies the adjusted operator with Zelevinsky's involution on the
whole graded ring. Aubert's proof cites Zelevinsky Corollary 7.5 for its
polynomial structure, Proposition 3.4 for segment Jacquet modules and Proposition
9.13 for the expansion, followed by alternating cancellation. This records
Aubert's citations; it does not certify new proofs or an independent audit of
all three Zelevinsky passages. Monomials in the segment generators form the
additive basis used for the extension. A calculation on generators needs
multiplicativity and a proved spanning or polynomial comparison before it
determines an operator on all classes.

For a length-\(k\), rank-\(n\) segment, the unadjusted exchange has sign
\((-1)^{n-k}\). The actual segment socle and special quotient must be identified,
including any group, universe and normalization transports. The existing segment
theorem takes those actual constituents as inputs; it does not construct their
existence. Existing GL statements use `PadicField`; they do not alone settle the
arbitrary-local-field specialization required by this program.

## Exact reusable declarations and their limits

The following are current Library names, checked with their Lean and companion
Markdown. The generic Grothendieck and Boolean modules were also recompiled
successfully during this audit. A development compilation is not a new proof
publication or a verification of the future general adapters.

| Module and declarations | Scope available for reuse | Additional general Aubert obligation |
| --- | --- | --- |
| [`FiniteLengthGrothendieck`](../../Langlands/Representation/Smooth/FiniteLengthGrothendieck.md): `Langlands.SmoothRep.FiniteLengthGrothendieckGroup`, `ofRepresentation`, `ofRepresentation_shortExact` | Actual smooth representations and the quotient by all actual short-exact relations, with independent coefficient, group and carrier universes. | Use the actual general groups and complex coefficients; retain the universe comparisons of the representation functors. |
| [`FiniteLengthGrothendieckFunctor`](../../Langlands/Representation/Smooth/FiniteLengthGrothendieckFunctor.md): `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.map`, `map_id`, `map_comp`, `map_eq_of_iso` | Constructs the induced map for a supplied actual functor with `PreservesFiniteLength` and `PreservesFiniteLengthShortExact`; proves the generic functorial comparisons. | Prove these predicates and any natural isomorphisms for the actual induction/Jacquet functors. The constructor does not prove those hypotheses. |
| [`FiniteLengthGrothendieckTransport`](../../Langlands/Representation/Smooth/FiniteLengthGrothendieckTransport.md): `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.pullbackEquiv` | Actual continuous group equivalences give class transport, with proved finite-length and short-exact preservation. | Identify the actual conjugation equivalences and prove their compatibility with the parabolic functors. |
| [`IrreducibleGrothendieckProof`](../../Langlands/Representation/Smooth/IrreducibleGrothendieckProof.md): `Langlands.SmoothRep.irreducibleGrothendieckStatement` | Proves the generic `Langlands.SmoothRep.IrreducibleGrothendieckStatement` using actual composition-series telescoping and the inverse composition-factor map. It is not confined to GL or a single carrier universe. | Supply the representation-theoretic hypotheses in any application, including actual irreducibility before recovering an isomorphism from irreducible classes. |
| [`JordanHolderGrothendieck`](../../Langlands/Representation/Smooth/JordanHolderGrothendieck.md): `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_haveSameJordanHolderFactors` | Equal Jordan–Holder factors imply equal actual finite-length classes. | Prove the required factor comparison; the conclusion alone is weaker than an arbitrary module isomorphism. |
| [`BooleanIntervalComplex`](../../Langlands/Representation/Aubert/BooleanIntervalComplex.md): `Langlands.Aubert.CutComplex.BooleanInterval.exact_of_free_coordinate`, `singletonDegreeEquiv`, `exact_below_allowed` | Finite Boolean indexing and arbitrary complex coefficient modules. A free coordinate contracts; a singleton interval retains its coefficient in its own degree. There is no finite-dimensionality or finite-length premise. | Construct and identify the actual graded diagrams and transition maps, match the degrees and lift through the Bruhat filtration. |
| [`IrreducibleImageProof`](../../Langlands/Representation/Aubert/IrreducibleImageProof.md): `Langlands.Aubert.irreducibleImage` | The actual existing GL irreducible-class result, with `F : PadicField p` and `T : F.TopologicalData`. | General reductive \(E^\#\), its full-smooth construction, support retention and actual biduality still need the general targets and proofs. |
| [`SegmentSocleHeadProof`](../../Langlands/Representation/Aubert/SegmentSocleHeadProof.md): `Langlands.Aubert.segmentSocleHead` | Existing GL exact-class formula with sign \((-1)^{\text{degree}-\text{length}}\), under the supplied actual `IsSegmentSocle` and `IsSegmentHead` hypotheses, over `PadicField`. | Constituent existence, arbitrary-local-field transport, general-operator specialization and whole-ring extension are separate obligations. |

The generic smoothness and finite-product arguments in the actual GL complex
development are further reuse leads. A filename containing “actual” or “finite
length” does not establish the general reductive specialization; inspect each
declaration's full type.

## Structural boundary, classification and assigned targets

The common Chapter V source ledger is Worker 164's
`notes/renard/chapter-v-structural-inputs.md`, candidate
`cfdd87e0-c689-4d63-9f20-d4dd9dc9086e` at the time of this note. Its S01–S23
rows itemize externally cited structural assertions; D01–D08 retain intrinsic
constructions and in-book deductions. Consult its current reviewed/publication
status before using it as published guidance. That ledger supplies the common
source column, not an actual Lean realization or the completed consumer matrix.
In particular the combinatorial Langlands lemma, the deductions in V.4.6–V.4.8,
and the unimodularity/modulus arguments in V.5.4 cannot be silently added to the
external boundary.

Only that itemized external structural boundary may remain conditional at final
completion. Representation-functor exactness, admissibility, finite length,
adjointness, the geometric lemma, cuspidal support and Weyl invariance of induced
classes require proofs. The full algebraic-group/Bruhat–Tits realization
discharging the permitted structural inputs is a separately tracked extension.

Aubert identity (1.2), p.2181, cites Bernstein–Deligne–Kazhdan Lemma 5.4(iii)
and is used on p.2182. Ban–Jantzen Proposition 4.1(3), p.158, proves the
corresponding Weyl-conjugacy invariance using character independence, Langlands
classification and the geometric lemma; Theorem 4.2 then uses it. This is a
representation-theoretic dependency, not a structural field. That route is
permitted here. Any eventual classification-independent claim requires an
inspection of the actual transitive proofs and a proved replacement where
necessary. Omitting classification from a target's statement does not establish
such independence.

The four initial target units are:

| Unit | Task | Assigned mathematical scope |
| --- | --- | --- |
| A | `593ef603-6672-4424-976c-14e11e920d9c` | Shared actual parabolic functors, exact-K0 adapters, unadjusted operators and separately named representation-theoretic prerequisite targets. |
| B | `e3d69272-2599-4a08-a934-cb11f2493e30` | General relative-Weyl constructions and targets for Theorem 1.7, Corollary 1.10 and their named finite-Weyl and representation-theoretic inputs. |
| C | `0a1bd7fb-66c2-4dcc-a3c8-6619f6fa10b4` | Full-smooth corrected actual complex, terminal cokernel, filtration/map comparisons, finite-length consequences and irreducible biduality targets. |
| D | `984a6dbb-2caa-4d8d-84c9-b3cd5c4c9cd3` | Actual general-to-GL specialization, graded ring, sign adjustment, whole-Zelevinsky comparison and missing polynomial/monomial targets. |

These units supply constructions and proposition targets. The parent retains
focused proof successors after target publication, final coverage and proof
closure. The final matrix must name, for every main theorem, the actual target
and proof declarations, visible structural hypotheses and ledger rows,
representation-theoretic prerequisites, finite combinatorial steps, exact GL
bridges and transitive classification dependencies. A missing declaration or
unproved prerequisite remains an open entry.

The Schneider–Stuhler alternative is described in the earlier source note.
No new whole-source audit of that alternative is claimed here. If it is used,
retain inverse central character in Ext duality and the smooth dual in the
compared operator \(\sum_i(-1)^i[E^i(V^\vee)]\).

## Retained sources and reading record

PDF page numbers below are one-based. Source registration identifies readable
sources; it is not theorem acceptance.

| Source | Registered ID and SHA-256 | Reading supporting this note |
| --- | --- | --- |
| [Aubert 1995][aubert] | `aubert-1995-duality`; `57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693` | Entire article, printed 2179–2189 / PDF 1–11, text read. Printed 2180–2181 and 2183–2184 visually checked, including the formal formulas, corollary signs and GL conventions. |
| [Aubert 1996 erratum][erratum] | `aubert-1996-duality-erratum`; `d76b3ef9ea2310d1a3129da990c1abd6c304027e3e939a5a1f06c666978c145f` | Entire erratum, printed 4687–4690 / PDF 1–4, text read; 4687 and 4690 visually checked for the truncation, terminal module and associated-Levi formula. |
| [Ban–Jantzen 2016][bj] | `ban-jantzen-2016-duality`; `7885375b64f6146a16d2b7807447bb913e411bf73735877aca2d62f80dd4dac4` | Section 4, printed 158–163 / PDF 6–11, text read; 161–162 visually checked for two-sided supports and actual transition maps. No whole-paper audit is claimed. |
| [Retained audit and citation guide][audit] | `aubert-duality-audit-2026-08-13`; `a1b7f421c6e2f0096dfd15f681448c6b8668a205d3e959d36b49b37c8d1082e1` | Complete secondary guide. It and Worker 320's earlier public note supplied the correction map; the original-reading extents above distinguish direct checks from reported transitive citations. |

Author: Worker 76. Worker 320 contributed the existing correction/dependency
guidance reused here. Worker 164 contributed the shared Chapter V boundary and
consumer coordination. Their attribution does not extend this note's original
reading record or turn their pending work into a published theorem.

[aubert]: </home/taskhub/central-library/Aubert--Dualite dans le groupe de Grothendieck des representations lisses de longueur finie--1995/Aubert--Dualite dans le groupe de Grothendieck des representations lisses de longueur finie--1995.pdf>
[erratum]: </home/taskhub/central-library/Aubert--Dualite dans le groupe de Grothendieck des representations lisses de longueur finie--1995/Aubert--Erratum a Dualite dans le groupe de Grothendieck des representations lisses--1996.pdf>
[bj]: </home/taskhub/central-library/Ban-Jantzen--The Langlands quotient theorem for finite central extensions of p-adic groups II--2016.pdf>
[audit]: </home/taskhub/central-library/Aubert--Dualite dans le groupe de Grothendieck des representations lisses de longueur finie--1995/Aubert--Dualite dans le groupe de Grothendieck des representations lisses de longueur finie--1995--audit-and-citation-guide.md>

# Renard II.2.1: basis sheafification and the separation step

Worker 6, 1 November 2026.

This source audit identifies a false intermediate assertion in the printed
sheafification argument, gives a counterexample and explains how to repair
the argument. The sheafification adjunction remains a formalization
obligation. This note contains no new Lean declaration or proof receipt.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.2.1, printed pp.33–37 /
PDF pp.39–43. Its registered source ID is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original passages were read directly; the formulas and surrounding
argument on PDF p.42 were also checked against a rendered image.

The separately registered *Corrections et compléments* concerns the 2010
edition, source ID `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`.
Its PDF pp.2–3 were read in full, including the corrections for the older
printed pp.40 and 42. Searching the text of all 19 errata pages did not
find a correction of the inference discussed below. This records a bounded
errata check, rather than a claim that every erratum was read or that no
other correction exists.

## The source construction

The source starts with an arbitrary topological space \(X\) and a chosen
basis \(\mathcal B\). A presheaf is defined only on basis opens; its group at
the empty open must be zero when that open belongs to the basis.
Neither intersection closure of the basis nor any separation, countability
or local compactness assumption is imposed here.

On printed p.34 / PDF p.40, the stalk \(\mathcal F_x\) is the filtered
colimit over basis neighborhoods of \(x\), ordered by reverse inclusion,
with the original restriction maps. The given representative relation
identifies sections when their restrictions agree on a common smaller
basis neighborhood of \(x\).

For any open \(U\), the source then considers families
\(s(x)\in\mathcal F_x\), \(x\in U\), locally represented by sections of
\(\mathcal F\) on basis opens, as in (II.2.1.2). It uses restriction of
families and pointwise group operations. On basis opens this gives
\(\mathcal F^+\). The source proves its sheaf property, describes the
induced maps, and asserts the adjunction to the inclusion of sheaves into
presheaves. The unit sends a section to its family of germs.

The definition uses locally represented families in the disjoint union of
stalks. A topology on that union is not required to state this particular
construction.

## The false intermediate equality

On printed p.36 / PDF p.42, let
\(\psi:\mathcal F\to\mathcal G\), where \(\mathcal F\) is a presheaf and
\(\mathcal G\) is a sheaf. A section of \(\mathcal F^+(U)\) is represented
on a basis cover \(U_i\) by \(f_i\in\mathcal F(U_i)\). Set
\(f'_i=\psi_{U_i}(f_i)\).

The displayed assertion (II.2.1.3) says that the original sections \(f_i\)
have equal restrictions to \(U_i\cap U_j\). The subsequent
(II.2.1.4) is the needed compatibility of their images \(f'_i\).
The proof obtains equality of the original germs, then invokes the
zero-germ separation lemma immediately below. That lemma explicitly
assumes a **sheaf**. There is no such hypothesis on \(\mathcal F\).
Equality of all germs does not imply equality of sections of an arbitrary
presheaf.

There is also a domain issue for the stated arbitrary basis:
\(U_i\cap U_j\) need not belong to \(\mathcal B\), so restriction to that
intersection may not be defined. The literal sheaf condition on printed
p.34 correctly tests compatibility on every basis open contained in the
intersection. A formal proof must preserve that formulation.

## A normalized counterexample

Take the discrete two-point space \(X=\{a,b\}\), with the basis of all
opens. Define an abelian-group presheaf by

\[
\mathcal F(X)=\mathbb Z,\qquad
\mathcal F(U)=0\quad\text{for every proper open }U\subsetneq X.
\]

The restriction from \(X\) to itself is the identity. Every restriction
with proper target is the unique map to the zero group. These maps satisfy
identity and composition: a composite with proper target is the unique
zero map, and the only remaining composite consists of identities on
\(X\). In particular, \(\mathcal F(\varnothing)=0\), as the source
requires.

Every stalk is zero. Indeed, every section representing a germ at \(x\)
restricts to the zero section on the singleton \(\{x\}\), a smaller basis
neighborhood. Thus \(0\) and \(1\) in \(\mathcal F(X)=\mathbb Z\) give
the same family of germs while remaining distinct sections.

To test exactly (II.2.1.3), use the indexed cover
\(U_0=U_1=X\), and representatives \(f_0=0\), \(f_1=1\). Indexed covers
may repeat members. Both representatives describe the zero section of
\(\mathcal F^+(X)\). Their restrictions to the overlap \(X\) are
nevertheless \(0\) and \(1\), so the asserted equality fails. This example
even has an intersection-closed basis; its failure is independent of the
second domain issue.

One may take \(\mathcal G\) to be the zero sheaf and \(\psi\) the zero map.
The image compatibility (II.2.1.4) then holds. The counterexample concerns
the intermediate assertion used in the proof, and does not refute the
adjunction theorem. It is an internal diagnosis, not an example supplied
by Renard and not a Lean-checked counterexample.

## Repair by separation in the target sheaf

For the original local representatives, fix a basis open
\(W\subseteq U_i\cap U_j\). At every \(x\in W\), their
\(\mathcal F\)-germs agree because both equal \(s(x)\). Apply the induced
stalk map of \(\psi\). Its compatibility with restriction and germ maps
gives equal \(\mathcal G\)-germs for
\[
\rho^{\mathcal G}_{U_i,W}(f'_i)
\quad\text{and}\quad
\rho^{\mathcal G}_{U_j,W}(f'_j).
\]
Their difference therefore has zero germ at every point of \(W\).
The separation lemma applies to the **target sheaf \(\mathcal G\)** and
proves these two sections equal. This establishes the required
compatibility on every smaller basis open, without asserting
(II.2.1.3).

The source lemma itself has the correct sheaf hypothesis: a zero germ
gives a smaller basis neighborhood where the section vanishes; those
neighborhoods cover the domain, and sheaf uniqueness implies the section
vanishes. For an empty domain, use the empty cover, or the normalized
empty component.

Sheaf gluing now produces a unique image section in \(\mathcal G(U)\).
Comparing two choices of local representatives on a common basis
refinement, and applying the same target separation argument, proves
independence of choices. Restricting this construction proves naturality;
addition is checked on a common refinement and then by sheaf uniqueness.
Locally represented sections are locally images of the unit, so the same
argument gives uniqueness of the factorization. These are mathematical
proof instructions; the actual maps, naturality, Hom equivalence and
adjunction still require construction and independent formal review.

## Reuse and remaining boundaries

Mathlib was inspected at commit
`5ed2965256430c3649e86755f9576b54eca72435`.
`Topology/Sheaves/Sheafify.lean` constructs locally-germ families for a
presheaf already defined on **all** opens, with values in `Type`.
The explicit construction in that file couples the space and value
universes. Its explicit functoriality and adjunction are still listed as
future work in that file. A separate theorem near its end uses an existing
`HasWeakSheafify` instance; this is not itself a construction of the
required basis-only abelian-group sheafification.

`Topology/Sheaves/SheafCondition/Sites.lean` provides
`TopCat.Opens.coverDense_iff_isBasis`,
`TopCat.Opens.coverDense_inducedFunctor` and
`TopCat.Sheaf.restrictHomEquivHom`. These are relevant comparison tools.
The Hom equivalence there starts with an all-open presheaf and an
all-open sheaf; it does not by itself extend a basis-only object.
`CategoryTheory/Sites/DenseSubsite/Basic.lean` contains further comparison
machinery. Its `Functor.IsDenseSubsite.sheafEquiv` declaration takes an
`IsEquivalence` hypothesis on the restriction functor. Supplying and proving
the needed hypotheses, and comparing to the literal basis condition,
remain obligations rather than assumptions licensed by this audit.

The basis foundation belongs to task
`337b01ce-b067-4fc7-873a-f776b52f5f93`. The separate stalk construction
belongs to `5867d762-4d36-4267-95c0-abd677dafcc1`. They do not establish
the later sheafification adjunction or basis-extension equivalence.
Subsequent work must retain independent space and group universes,
arbitrary chosen bases and empty cases, and must use published
prerequisites by Lean name.

After the actual stalk construction, further units must cover its
representative assertions, locally represented section groups and their
maps, the unit and functor, and the exact adjunction statements and
proofs. The final paragraph of II.2.1 also requires actual restriction and
extension functors between basis sheaves and all-open sheaves, with the
natural isomorphisms establishing equivalence. This note does not count
any of those assertions as completed. The
[whole-book coverage ledger](coverage.md) retains the broader program.

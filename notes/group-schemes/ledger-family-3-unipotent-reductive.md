# Group-scheme ledger, family 3: unipotent structure and geometric reductivity

Author: Worker 3483, 10 November 2026, for the algebraic and reductive group-scheme program
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e` (Task 3483). This note is the source-to-declaration
ledger for family 3 of that program's contract. Family 3 covers:

- unipotent groups, the `k`-unipotent radical and the split unipotent radical;
- the distinction between a trivial `k`-unipotent radical (pseudo-reductivity) and a trivial
  geometric unipotent radical (reductivity) over imperfect fields;
- solvable groups and Borel subgroups;
- semisimple and reductive groups, their structure, and products;
- behaviour under field extension;
- pseudo-parabolic subgroups of smooth connected affine groups.

A full classification of pseudo-reductive groups is not part of the family.

It describes Library commit `f2c5495316f5a5631bc8c11875b7509d93271fe5` and environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`. All Lean names are in `Langlands.GroupScheme` unless
a namespace is shown. Module paths are relative to `Langlands/GroupScheme/` in that commit.
"Field group" means a group scheme over `Spec k` for a field `k : Type u`.

The rows list the principal source assertions of this family. Auxiliary reductions and
interfaces used inside proofs are not listed one by one, and leaving one out says nothing
about its status. Maximal tori and Borel subgroups of reductive groups belong to family 4;
centres, derived and adjoint groups and central isogenies belong to family 6. Rows of those
families are repeated here only where this family needs them.

## Status codes and evidence

Each row gives the source assertion with its locator, the exact Lean statement and its
hypotheses, a status, the evidence, and the owner task.

- **D (definition or internal result).** A published construction, or a published theorem
  that is not a proposition declaration, with the hypotheses listed in the row. The evidence
  is its module path. No owner task is needed.
- **P (published proof).** The Library at the commit above contains a theorem whose type is
  exactly the statement. The evidence is that theorem and its module path. The author also
  type-checked `example : S := proof` for every P row in a private module. That check
  passed with no errors or warnings, and `#print axioms` reported only `propext`,
  `Classical.choice` and `Quot.sound`; it is not public evidence. No further proof work or
  owner task is needed.
- **C (composite, not published).** No published theorem has the statement as its type, but
  a projection out of a published conjunction has it. The author type-checked the
  projection in the same private module. What is missing is a named wrapper theorem, not
  mathematics. The row names the owner task, or says that there is none.
- **O (open).** A Lean statement exists, but no published proof and no composite from
  published results is known.
- **M (missing statement).** A source assertion of this family has no Lean statement in the
  Library. It is an obligation of the program, recorded with its owner task if one exists.
  An assertion that published theorems already prove, although no proposition declaration
  states it, is not M: its row lists those theorems as D and names the missing statement.

The labels "accepted" and "published" are used only for artifacts that passed independent
review.

Source locators use these registered sources, cited by source id:

- `conrad-gabber-prasad-2015-pseudo-reductive`: B. Conrad, O. Gabber and G. Prasad,
  *Pseudo-reductive groups*, 2nd edition (2015). PDF page = printed page + 26.
- `milne-2017-algebraic-groups`: J. S. Milne, *Algebraic Groups* (2017). PDF page = printed
  page + 16. With it, the official errata snapshot
  `milne-2017-algebraic-groups-errata-2026-11-02`.
- `conrad-2014-reductive-group-schemes`: B. Conrad, *Reductive group schemes* (2014).
  Printed page = PDF page.
- `mumford-fogarty-kirwan-1994-git-3rd`: D. Mumford, J. Fogarty and F. Kirwan, *Geometric
  Invariant Theory*, 3rd enlarged edition (1994). PDF page = printed page + 12.

The author re-read every locator below in the original source for this note, on 10 November
2026, and checked that the cited item is on the cited page.

## A. Definitions and conventions

All are D. Unless stated otherwise the module is `Reductive/Basic`.

- `IsUnipotent G`: every matrix representation of `G` on a nonzero `k^n` has a nonzero fixed
  vector, where representations and fixed vectors are tested on all test schemes. Source:
  Milne 2017, 6.45–6.46, printed p.135 (PDF 151), and §14.b, printed p.280 (PDF 296).
- `HasTrivialUnipotentRadical G`: every smooth connected unipotent normal closed subgroup of
  `G` **defined over `k`** is trivial. Source: Conrad–Gabber–Prasad, Definition 1.1.1,
  printed p.3 (PDF 29), the `k`-unipotent radical `R_{u,k}(G)`.
- `IsPseudoReductive G`: smooth, affine structure map, connected, and
  `HasTrivialUnipotentRadical G`. Source: the same Definition 1.1.1.
- `IsConnectedReductive G`: smooth, affine structure map, connected, and
  `HasTrivialUnipotentRadical` of the base change of `G` to `AlgebraicClosure k`, the
  geometric unipotent radical. Source: Milne 2017, 6.46, printed p.135 (PDF 151); Conrad
  2014, Definition 1.1.11, p.11. Classification, maximal tori and Bruhat data are not part
  of the definition.
- `IsReductive G` for `G` over a base scheme `S`: `G` is smooth with affine structure map,
  and every geometric fibre is pseudo-reductive (that is, connected reductive, since the
  fibre is over an algebraically closed field). Source: Conrad 2014, Definition 3.1.1, p.81.
- `IsSemisimple G` (`Reductive/Semisimple`): `G` is connected reductive and its
  scheme-theoretic centre is finite. Source: Milne 2017, Proposition 19.10, printed p.400
  (PDF 416), (a) ⇔ (c).
- `IsSolvableGroupScheme G` (`Absolute/Borel`): the abstract group `G(k̄)`,
  `k̄ = AlgebraicClosure k`, is solvable. For smooth groups this is Milne's notion; for
  non-smooth groups it only sees `G(k̄)`.
- `IsSplitSolvableGroupScheme H` (`SplitSolvable`): smooth, affine, connected, solvable, with
  a finite series whose successive quotients are `𝔾_a` or `𝔾_m`.
  `RelativeRoot.IsSplitUnipotent H` (`Rational/RootSubgroupStructureStatement`): a finite
  normal series of smooth connected closed subgroups with represented `𝔾_a` quotients.
- `IsUnipotentRadical i` (`Reductive/UnipotentRadical`): `i` is the largest smooth connected
  unipotent normal closed subgroup over `k`. `IsSolvableRadical r` (`Rational/LeviSubgroup`):
  the same with "solvable".
- `HasConstantAffineLineMaps G` (`Rational/UnipotentWoundCriterionStatement` and its
  imports): every map `𝔸¹ → G` is constant, the `k`-wound condition of Conrad–Gabber–Prasad,
  Definition B.2.1, printed p.568 (PDF 594).
- `IsPseudoParabolicSubgroup i` (`PseudoParabolic`): `G` smooth, affine, connected, and
  `range i = P(λ) · R_{u,k}(G)` as an fppf product for some cocharacter `λ` over `k`. Source:
  Conrad–Gabber–Prasad, Definition 2.2.1, printed p.62 (PDF 88).

Two D theorems relate the notions:

- `IsConnectedReductive.isPseudoReductive` (`Reductive/ToPseudoReductive`): every connected
  reductive group over any field is pseudo-reductive.
- `IsPseudoReductive.isConnectedReductive_of_isAlgClosed` (`Reductive/AlgebraicallyClosedPseudoReductive`):
  over an algebraically closed field the converse holds.

The converse fails over every imperfect field (row B5). The Library keeps the two notions
separate, and no row asserts the converse except over perfect fields (row B4).

## B. Radicals and the imperfect-field distinction

**B1. The `k`-unipotent radical exists.** Source: Conrad–Gabber–Prasad, Definition 1.1.1,
printed p.3 (PDF 29).
- Lean: `UnipotentRadicalExistenceStatement` (`Reductive/UnipotentRadicalExistenceStatement`).
  Hypotheses: `G` smooth, with affine structure map and connected. Conclusion: some
  `i : U ⟶ G` with `IsUnipotentRadical i`.
- Status P: `unipotentRadicalExistence` (`Reductive/UnipotentRadicalExistenceProof`).

**B2. The split unipotent radical exists.** Source: Conrad–Gabber–Prasad, the paragraph
before Proposition 2.2.4, printed p.63 (PDF 89), and Corollary B.3.5, printed p.574
(PDF 600).
- Lean: `SplitUnipotentRadicalExistenceStatement` (`Reductive/SplitUnipotentRadicalExistenceStatement`).
  Hypotheses: as B1. Conclusion: some `j` with `IsSplitUnipotentRadical j`.
- Status P: `SplitUnipotentRadicalExistence.splitUnipotentRadicalExistence`
  (`Reductive/SplitUnipotentRadicalExistenceProof`).

**B3. The quotient by the `k`-unipotent radical is pseudo-reductive.** Source:
Conrad–Gabber–Prasad, Remark 1.1.4, printed p.5 (PDF 31).
- Lean: `UnipotentRadicalQuotientStatement` (`Reductive/UnipotentRadicalQuotientStatement`).
  Hypotheses: as B1, and a unipotent radical `i`. Conclusion: an fppf quotient `q : G ⟶ Q` by
  `range i` with `Q` pseudo-reductive.
- Status P: `unipotentRadicalQuotient` (`Reductive/UnipotentRadicalQuotientProof`).

**B4. Over a perfect field pseudo-reductive means reductive.** Source:
Conrad–Gabber–Prasad, the paragraph after Definition 1.1.1, printed p.4 (PDF 30).
- Lean: `PerfectFieldPseudoReductiveStatement` (`Reductive/PerfectFieldStatement`).
  Hypotheses: `[PerfectField k]`. Conclusion: `IsPseudoReductive G ↔ IsConnectedReductive G`.
- Status P: `perfectFieldPseudoReductive` (`Reductive/PerfectFieldProof`).

**B5. A pseudo-reductive group that is not reductive.** Source: Conrad–Gabber–Prasad,
Example 1.1.3, printed pp.4–5 (PDF 30–31): for an imperfect field `k` and a nontrivial
finite purely inseparable `k'/k`, `R_{k'/k}(GL_1)` is pseudo-reductive and not reductive.
- Status M: the Library has no statement of this example. Owner task: none.

**B6. Pseudo-reductivity and separable extensions.** Source: Conrad–Gabber–Prasad,
Proposition 1.1.9(1), printed p.8 (PDF 34), proof p.9 (PDF 35): for any separable
extension `K/k`, `R_{u,k}(G)_K = R_{u,K}(G_K)`; in particular `G` is pseudo-reductive if and
only if `G_K` is.
- Lean: `PseudoReductiveSeparableExtensionStatement` (`Reductive/PseudoReductiveSeparableExtensionStatement`).
  Hypotheses: `[Algebra.IsSeparable k K]` (so `K/k` is separable **algebraic**); `G`
  pseudo-reductive. Conclusion: `G_K` is pseudo-reductive.
- Status P: `pseudoReductiveSeparableExtension` (`Reductive/PseudoReductiveSeparableExtensionProof`).
- Scope: only the ascent direction, only algebraic extensions, and not the equality of
  radicals. Ascent along separable transcendental extensions and the equality of radicals
  have status M. Owner task: none.
- Reflection direction, for **every** field extension `K/k`: `HasTrivialUnipotentRadical.of_fieldExtension`
  (`Reductive/SemisimpleFieldReflectionProof`). Hypotheses: `k`, `K : Type u`,
  `[Algebra k K]`, `G` with affine structure map, and `G_K` with trivial `K`-unipotent
  radical. Conclusion: `G` has trivial `k`-unipotent radical. Status D. Smoothness and
  connectedness descend by `smooth_of_baseChange` and `connectedSpace_of_baseChange`
  (`Rational/UnipotentRadicalProperties`), using `fieldExtension_fpqc`
  (`BaseChangeReflection`); affineness descends by
  `Langlands.AlgebraicGeometry.fieldExtensionAffineDescent`
  (`Langlands/AlgebraicGeometry/FieldExtensionAffineDescentProof`, outside
  `Langlands/GroupScheme/`). These D results prove that `G` is pseudo-reductive whenever
  `G_K` is: the author type-checked that short proof privately, with axioms `propext`,
  `Classical.choice` and `Quot.sound`. The same descent steps begin the published proof
  of `IsConnectedReductive.of_fieldExtension` (C1). No proposition declaration states this
  reflection; only a named statement and its wrapper theorem are missing. Owner task: none.

**B7. Rational unipotent points of pseudo-reductive groups.** Source: derived from the proof
of Conrad–Gabber–Prasad, Proposition C.1.6, printed pp.586–587 (PDF 612–613).
- Lean: `PseudoReductiveRationalUnipotentPointStatement` (`Reductive/PseudoReductiveRationalUnipotentPointStatement`).
  Hypotheses: any field extension `K/k`; `G` pseudo-reductive; a cocharacter `χ`; a closed
  normal unipotent subgroup `H` of `G_K`. Conclusion: every `u ∈ U(χ)(k)` whose image in
  `G(K)` lies in `H(K)` is trivial.
- Status P: `pseudoReductiveRationalUnipotentPoint` (`Reductive/PseudoReductiveRationalUnipotentPointProof`).

**B8. Unipotent radicals of normal subgroups.** Source: Conrad–Gabber–Prasad, Proposition
A.4.8, printed pp.498–499 (PDF 524–525).
- Lean: `NormalUnipotentRadicalIntersectionStatement` (`Reductive/NormalUnipotentRadicalIntersectionStatement`).
  Hypotheses: `[IsAlgClosed k]`; `G`, `H` smooth, affine, connected; `H` a closed normal
  subgroup of `G`; unipotent radicals `r` of `G` and `s` of `H`. Conclusion: the pullback of
  `range r` to `H` is `range s`.
- Status P: `normalUnipotentRadicalIntersection` (`Reductive/NormalUnipotentRadicalIntersectionProof`).

**B9. The unipotent radical modulo its split part is wound.** Source: Conrad–Gabber–Prasad,
Theorem B.3.4, printed pp.573–574 (PDF 599–600), and Corollary B.3.5, printed p.574
(PDF 600).
- Lean: `SplitRadicalWoundQuotientStatement` (`Reductive/SplitRadicalWoundQuotientStatement`).
  Hypotheses: `G` as B1; a unipotent radical `j : U ⟶ G`, a split unipotent radical `n` of
  `G` factoring through `U` by `m`; a smooth, affine, connected `Q` and an fppf quotient
  `q : U ⟶ Q` by `range m`. Conclusion: `HasConstantAffineLineMaps Q`.
- Status P: `splitRadicalWoundQuotient` (`Reductive/SplitRadicalWoundQuotientProof`).

## C. Field extension

**C1. Reductivity under field extension.** Source: Milne 2017, Proposition 19.13, printed
p.400 (PDF 416): `G` is reductive if and only if `G_{k'}` is, for any field `k' ⊇ k`.
- `ConnectedReductiveFieldExtensionStatement` (`Reductive/FieldExtensionStatement`): for
  **any** field extension `K/k`, `G` connected reductive implies `G_K` connected reductive.
  Status P: `connectedReductiveFieldExtensionStatement` (`Reductive/FieldExtensionProof`).
- `ConnectedReductiveAlgebraicExtensionReflectionStatement`
  (`Reductive/AlgebraicExtensionReflectionStatement`): for **algebraic** `K/k`, `G_K`
  connected reductive implies `G` connected reductive. Status P:
  `connectedReductiveAlgebraicExtensionReflection` (`Reductive/AlgebraicExtensionReflectionProof`).
- `ConnectedReductiveAlgebraicExtensionAscentStatement` (`Reductive/AlgebraicExtensionAscentStatement`):
  the algebraic case of the first item. Status C: `algebraicExtensionAscent.1`. Owner task:
  none.
- `IsConnectedReductive.of_fieldExtension` (`Reductive/SemisimpleFieldReflectionProof`):
  for **any** field extension `K/k` (with `k`, `K : Type u` and `[Algebra k K]`) and any
  group scheme `G` over `k`, with no hypothesis on `G`, if `G_K` is connected reductive
  then `G` is connected reductive. Status D: a published theorem, not a proposition
  declaration.
- Together with the first item, this gives the full equivalence of Milne 19.13 for every
  field extension. No proposition declaration states the reflection for arbitrary
  extensions; what is missing is only such a named statement and its wrapper theorem, not
  mathematics. Owner task: none.

**C2. Semisimplicity under field extension.** Source: Milne 2017, Proposition 19.5, printed
pp.398–399 (PDF 414–415): `G` is semisimple if and only if `G_{k'}` is; and Proposition
19.10, printed p.400 (PDF 416).
- `IsSemisimpleFieldExtensionStatement` (`SimplyConnected/FieldExtensionStatement`): for
  **any** `K/k`, including transcendental and inseparable extensions, `G` semisimple implies
  `G_K` semisimple. Status P: `isSemisimpleFieldExtension`
  (`SimplyConnected/SemisimpleFieldExtensionProof`).
- `SemisimpleFieldReflectionStatement` (`Reductive/SemisimpleFieldReflectionStatement`): for
  **any** `K/k`, `G_K` semisimple implies `G` semisimple. Status P:
  `semisimpleFieldReflectionStatement` (`Reductive/SemisimpleFieldReflectionProof`).
- Together these two give the full equivalence of Milne 19.5.
- `SemisimpleAlgebraicExtensionReflectionStatement` (`Reductive/AlgebraicExtensionReflectionStatement`):
  the algebraic case. Status P: `semisimpleAlgebraicExtensionReflection`
  (`Reductive/AlgebraicExtensionReflectionProof`).
- `SemisimpleAlgebraicExtensionAscentStatement` (`Reductive/AlgebraicExtensionAscentStatement`):
  for **algebraic** `K/k`, `G` semisimple implies `G_K` semisimple; a special case of
  `IsSemisimpleFieldExtensionStatement`. Status C: `algebraicExtensionAscent.2`. Owner task:
  none.
- The conjunctions `AlgebraicExtensionAscentStatement` and
  `AlgebraicExtensionReflectionStatement`: status P, `algebraicExtensionAscent`
  (`Reductive/AlgebraicExtensionAscent`) and `algebraicExtensionReflection`
  (`Reductive/AlgebraicExtensionReflectionProof`).

**C3. Trivial radical under extension of algebraically closed fields.** Source: Conrad 2014,
the discussion after Definition 3.1.1, p.81, and Exercise 3.4.1, p.104.
- Lean: `AlgebraicallyClosedRadicalFieldExtensionStatement` (`Reductive/RadicalFieldExtensionStatement`).
  Hypotheses: `k` and `K` algebraically closed; `G` smooth, affine, connected with trivial
  unipotent radical. Conclusion: `G_K` has trivial unipotent radical.
- Status P: `algebraicallyClosedRadicalFieldExtensionStatement` (`Reductive/RadicalFieldExtensionProof`).

**C4. Unipotence under field extension.** Source: Milne 2017, Corollary 14.9, printed p.282
(PDF 298): `G` is unipotent if and only if `G_{k'}` is.
- `UnipotentFieldExtensionStatement` (`Reductive/UnipotentFieldExtensionStatement`): `G` with
  affine structure map, locally of finite type, unipotent; any `K/k`. Conclusion: `G_K` is
  unipotent. Status P: `unipotentFieldExtensionStatement` (`Reductive/UnipotentFieldExtensionProof`).
- `UnipotentFieldReflectionStatement` (`Unipotent/FieldReflectionStatement`): `G` with affine
  structure map (no finite type); any `K/k`. Conclusion: if `G_K` is unipotent, so is `G`.
  Status P: `unipotentFieldReflection` (`Unipotent/FieldReflectionProof`).

**C5. Solvability under field extension.** Source: Milne 2017, Corollary 6.31, printed p.132
(PDF 148).
- Lean: `SolvableFieldExtensionStatement` (`Absolute/SolvableFieldExtensionStatement`).
  Hypotheses: any field map `Spec K ⟶ Spec k`; `G` smooth with affine structure map and
  solvable. Conclusion: `G_K` is solvable.
- Status P: `solvableFieldExtensionStatement` (`Absolute/SolvableFieldExtensionProof`).

## D. Unipotent groups

**D1. Unitriangular groups are unipotent.** Source: Milne 2017, Theorem 14.5, printed
pp.281–282 (PDF 297–298).
- Lean: `UnitriangularUnipotentStatement` (`UnitriangularUnipotentStatement`): over every
  field, the upper unitriangular group scheme of size `N` is unipotent.
- Status P: `unitriangularUnipotent` (`UnitriangularUnipotentProof`).

**D2. Subgroups of unipotent groups.** Source: Milne 2017, Corollary 14.7, printed p.282
(PDF 298).
- Lean: `UnipotentClosedSubgroupStatement` (`UnipotentClosedSubgroupStatement`). Hypotheses:
  `H` with affine structure map, locally of finite type, unipotent; a closed subgroup
  `W ⟶ H`. Conclusion: `W` is unipotent.
- Scope: Milne also treats quotients and extensions; those parts are not in this statement.
- Status P: `unipotentClosedSubgroup` (`UnipotentClosedSubgroupProof`).

**D3. Over a perfect field, smooth connected unipotent groups are split.** Source: Milne
2017, Corollary 16.24, printed p.331 (PDF 347).
- Lean: `PerfectFieldUnipotentSplitStatement` (`Unipotent/PerfectFieldSplitStatement`).
  Hypotheses: `[PerfectField k]`; `U` smooth, affine, connected, unipotent. Conclusion:
  `RelativeRoot.IsSplitUnipotent U`.
- Status P: `perfectFieldUnipotentSplit` (`Unipotent/PerfectFieldSplitProof`).

**D4. One-dimensional unipotent groups over perfect fields.** Source: Milne 2017, 14.58,
printed p.298 (PDF 314), and Corollary 14.53, printed p.297 (PDF 313).
- Lean: `PerfectFieldOneDimensionalUnipotentStatement` (`Unipotent/OneDimensionalStatement`).
  Hypotheses: `[PerfectField k]`; `U` smooth of relative dimension one, affine, connected,
  unipotent. Conclusion: `U` is a vector group of dimension one, that is `U ≅ 𝔾_a`.
- Status P: `perfectFieldOneDimensionalUnipotent` (`Unipotent/OneDimensional/Proof`).

**D5. Orbits of unipotent groups on affine varieties are closed.** Source: Milne 2017,
Theorem 17.64 (Kostant–Rosenlicht), printed pp.373–374 (PDF 389–390).
- Lean: `UnipotentAffineOrbitClosedStatement` (`UnipotentAffineOrbitClosedStatement`).
  Hypotheses: `[IsAlgClosed k]`; `U` smooth, affine, unipotent; an action on an affine `X`
  locally of finite type; a rational point `x`. Conclusion: the orbit of `x` is closed.
- Status P: `unipotentAffineOrbitClosed` (`UnipotentAffineOrbitClosedProof`).

**D6. Dynamic unipotent subgroups are unipotent.** Source: Conrad–Gabber–Prasad, Lemma 2.1.5
and its proof, printed pp.50–51 (PDF 76–77).
- Lean: `DynamicUnipotentUnipotenceStatement` (`Dynamic/UnipotentUnipotenceStatement`).
  Hypotheses: `G` with affine structure map, locally of finite type; a cocharacter `χ`; a
  representative `j` of `U(χ)`. Conclusion: its source is unipotent.
- Status P: `dynamicUnipotentUnipotence` (`Dynamic/UnipotentUnipotenceProof`).

**D7. Torsors under split unipotent groups over affine schemes are trivial.** Source: the
first paragraph of the proof of Conrad–Gabber–Prasad, Lemma C.2.1, printed p.592 (PDF 618),
which uses the vanishing of `H¹(X, U)` for split unipotent `U` and affine `X`.
- Lean: `SplitUnipotentAffineTorsorStatement` (`SplitUnipotentAffineTorsorStatement`).
  Hypotheses: `H` smooth, affine, split unipotent; an affine test scheme `T`; an `H_T`-torsor
  `X → T` that is flat, surjective and quasi-compact. Conclusion: `X → T` has a section.
- Status P: `splitUnipotentAffineTorsorStatement` (`SplitUnipotentAffineTorsorProof`).

**D8. Wound unipotent groups.** Source: Conrad–Gabber–Prasad, Definition B.2.1 and Remark
B.2.2, printed p.568 (PDF 594), and Proposition B.3.2, printed p.572 (PDF 598). Appendix B
assumes positive characteristic (printed p.561, PDF 587); the Lean statements are over every
field, and their characteristic-zero part is derived.
- `UnipotentWoundCriterionStatement` (`Rational/UnipotentWoundCriterionStatement`): for `G`
  smooth, affine, connected and unipotent, `G` is wound if and only if it has no closed
  central subgroup isomorphic to `𝔾_a`. Status P: `unipotentWoundCriterion`
  (`Rational/UnipotentWoundCriterionProof`).
- `UnipotentWoundSeparableExtensionStatement` (`Rational/UnipotentWoundSeparableExtensionStatement`):
  for separable algebraic `K/k`, `G` is wound if and only if `G_K` is. Status P:
  `unipotentWoundSeparableExtension` (`Rational/UnipotentWoundSeparableExtensionProof`).
  Separable transcendental extensions are not covered.

**D9. Products of unipotent groups.** D: `SubgroupProductOrbit.isUnipotent_tensor`
(`Rational/SubgroupProductGeometry`): if `V` and `C` have affine structure maps and are
unipotent, so is `V × C`. Source: Milne 2017, Corollary 14.7, printed p.282 (PDF 298), the
extension clause.

## E. Solvable groups and Borel subgroups

**E1. Borel's fixed point theorem.** Source: Milne 2017, Corollary 17.3, printed p.353
(PDF 369); Milne requires `X` nonempty.
- Lean: `SolvableProperFixedPointStatement` (`SolvableProperFixedPointStatement`).
  Hypotheses: `[IsAlgClosed k]`; `H` smooth, affine, connected and solvable; a **nonempty**
  proper scheme `X` over `k` with an action of `H`. Conclusion: a rational fixed point.
- Status P: `solvableProperFixedPoint` (`SolvableProperFixedPointProof`).

**E2. Structure of smooth connected solvable groups.** Source: Milne 2017, Theorem 16.33,
printed pp.335–336 (PDF 351–352). Milne assumes a perfect field for (a)–(c) and an
algebraically closed field for (d); all three Lean statements assume `[IsAlgClosed k]` and
`H` smooth, affine, connected and solvable.
- `SolvableUnipotentPartStatement` (`Absolute/SolvableUnipotentPartStatement`): a smooth
  connected unipotent closed normal subgroup `H_u` containing every closed unipotent
  subgroup. Status P: `solvableUnipotentPart` (`Absolute/SolvableUnipotentPart`).
- `SolvableUnipotentFactorizationStatement` (`Absolute/SolvableUnipotentFactorizationStatement`):
  for a maximal torus `T`, such a `U` with every **rational point** `b = v s`, `v ∈ U(k)`,
  `s ∈ T(k)`. Status P: `solvableUnipotentFactorization` (`Absolute/SolvableUnipotentFactorizationProof`).
- `SolvableMaximalTorusSemidirectStatement` (`Absolute/SolvableMaximalTorusSemidirectStatement`):
  for a maximal torus `T`, the multiplication `U × T → H` is an **isomorphism of schemes**,
  `H = U ⋊ T`. Status P: `solvableMaximalTorusSemidirect` (`Absolute/SolvableMaximalTorusSemidirectProof`).

**E3. Splitting of `H → H/H_u`.** Source: Milne 2017, Theorem 16.26, printed pp.332–333
(PDF 348–349).
- Lean: `SolvableSplitExtensionStatement` (`Absolute/SolvableSplitExtensionStatement`).
  Hypotheses: `[IsAlgClosed k]`; `H` as E2; a smooth connected unipotent closed normal `U`
  and an fppf quotient `q : H ⟶ D` by it with `D` a split torus. Conclusion: a section
  `σ : D ⟶ H` of `q`.
- Status P: `solvableSplitExtension` (`Absolute/SolvableSplitExtensionProof`).

**E4. Lie–Kolchin and triangular embeddings.** Source: Milne 2017, Theorem 16.30 and
Corollary 16.32, printed pp.334–335 (PDF 350–351), and Proposition 16.34, printed p.336
(PDF 352).
- `LieKolchinRationalTriangularizationStatement` (`Absolute/LieKolchinRationalTriangularizationStatement`):
  `[IsAlgClosed k]`; `H` smooth, affine, connected with `H(k)` solvable; every matrix
  representation is conjugate into upper triangular form on rational points. Status P:
  `lieKolchinRationalTriangularization` (`Absolute/LieKolchinRationalTriangularization`).
- `SolvableTriangularEmbeddingStatement` (`Absolute/SolvableTriangularEmbeddingStatement`):
  `[IsAlgClosed k]`; `H` as E2; a closed embedding of `H` into an upper triangular group.
  Status P: `solvableTriangularEmbeddingStatement` (`Absolute/SolvableTriangularEmbeddingProof`).
- `AlgebraicallyClosedSplitSolvableStatement` (`AlgebraicallyClosedSplitSolvableStatement`):
  `[IsAlgClosed k]`; `H` as E2 is split solvable. Status P: `algebraicallyClosedSplitSolvable`
  (`AlgebraicallyClosedSplitSolvableProof`).

**E5. Borel subgroups.** Sources: Milne 2017, Definition 17.6 and the paragraph after it,
printed pp.353–354 (PDF 369–370), and Proposition 17.19, printed p.357 (PDF 373).
- `SolvableSubgroupBorelContainmentStatement` (`Absolute/SolvableSubgroupBorelContainmentStatement`):
  `[IsAlgClosed k]`; `G` smooth, affine, connected; a smooth connected solvable closed
  subgroup lies in a Borel subgroup. Status P: `solvableSubgroupBorelContainment`
  (`Absolute/SolvableSubgroupBorelContainmentProof`).
- `ProperSolvableQuotientBorelStatement` (`Absolute/ProperSolvableQuotient`):
  `[IsAlgClosed k]`; a smooth connected solvable closed subgroup `H` with a **supplied**
  proper quotient `q : G ⟶ Q` (smooth, surjective, quasi-compact, fibres the cosets of `H`)
  is a Borel subgroup. Status P: `properSolvableQuotientBorel` (`Absolute/ProperSolvableQuotientProof`).

**E6. Nilpotent groups.** Source: Milne 2017, Theorem 16.47(a),(c), printed p.341 (PDF 357).
- Lean: `NilpotentCentralTorusStatement` (`Nilpotent/CentralTorusStatement`). Hypotheses: `G`
  smooth, affine, connected and nilpotent; any field. Conclusion: a central maximal torus
  `T` and an fppf quotient `G/T` that is unipotent with affine structure map.
- Status P: `nilpotentCentralTorusStatement` (`Nilpotent/CentralTorusProof`).

**E7. The solvable radical exists.** Source: Milne 2017, Proposition 6.42, printed p.134
(PDF 150), and 6.44, printed p.135 (PDF 151).
- Lean: `SolvableRadicalExistenceStatement` (`Rational/SolvableRadicalExistenceStatement`).
  Hypotheses: `G` smooth, affine, connected; any field. Conclusion: some `r` with
  `IsSolvableRadical r`.
- Status P: `solvableRadicalExistence` (`Rational/SolvableRadicalExistenceProof`).

## F. Semisimple and reductive groups, and products

**F1. Reductive groups are almost-direct products of a central torus and the derived
group.** Source: Milne 2017, Proposition 21.61, printed p.443 (PDF 459), (a) ⇒ (c), with the
argument of Proposition 21.60, printed p.442 (PDF 458).
- Lean: `ReductiveCentralDerivedProductStatement` (`Reductive/CentralDerivedProductStatement`).
  Hypotheses: `G` connected reductive; any field. Conclusion: a closed central torus
  `i : Z ⟶ G` and a derived subgroup `d : D ⟶ G` whose product map `Z × D → G` is an
  epimorphism.
- Status P: `reductiveCentralDerivedProduct` (`Reductive/CentralDerivedProductProof`).

**F2. The derived group is semisimple.** Source: Milne 2017, Proposition 19.21(c), printed
p.402 (PDF 418).
- Lean: `DerivedSubgroupSemisimpleStatement` (`Derived/SemisimpleStatement`). Hypotheses: `G`
  connected reductive; a derived subgroup `d : D ⟶ G`. Conclusion: `D` is semisimple.
- Status P: `derivedSubgroupSemisimple` (`Derived/SemisimpleProof`).

**F3. Semisimple groups are perfect.** Source: Milne 2017, Corollary 21.50, printed p.440
(PDF 456).
- Lean: `SemisimplePerfectStatement` (`Derived/SemisimplePerfectStatement`): for `G`
  semisimple over any field, `derivedSubgroup G = ⊤`.
- Status P: `semisimplePerfect` (`Derived/SemisimplePerfectProof`).

**F4. Almost-simple factors and normal subgroups of semisimple groups.** Source: Milne 2017,
Theorem 21.51, printed pp.440–441 (PDF 456–457), and Corollaries 21.52–21.53, printed p.441
(PDF 457).
- `SemisimpleAlmostSimpleGenerationStatement` (`Reductive/AlmostSimpleGenerationStatement`):
  `[IsAlgClosed k]`; `G` semisimple; a closed subgroup containing every almost-simple closed
  normal subgroup is all of `G`. Status P: `semisimpleAlmostSimpleGeneration`
  (`Reductive/AlmostSimpleGenerationProof`).
- `SemisimpleNormalComplementStatement` (`Reductive/SemisimpleNormalComplementStatement`):
  `[IsAlgClosed k]`; `G` semisimple; a smooth connected closed normal `H` has a closed normal
  `K` commuting with `H` such that multiplication `H × K → G` is flat and surjective.
  Status P: `semisimpleNormalComplement` (`Reductive/SemisimpleNormalComplementProof`).
- `SemisimpleNormalIsogenyComplementStatement` (`Reductive/NormalIsogenyComplementStatement`):
  any field; `G` semisimple; for a smooth connected closed normal `H`, `H` is semisimple and
  there is a semisimple closed normal `K` commuting with `H` such that `H × K` is semisimple
  and multiplication `H × K → G` is a central isogeny. Status P:
  `semisimpleNormalIsogenyComplement` (`Reductive/NormalIsogenyComplementProof`).
- `SemisimpleNormalRootDichotomyStatement` (`Reductive/NormalRootDichotomyStatement`):
  `[IsAlgClosed k]`; `G` semisimple with a split maximal torus `t`; for a smooth connected
  closed normal `H` and a root `α`, either `U_α ⊆ H` or `U_α` centralizes `H`. Status P:
  `semisimpleNormalRootDichotomy` (`Reductive/NormalRootDichotomyProof`).

**F5. Central quotients.** Source: Milne 2017, Corollary 17.62, printed pp.372–373
(PDF 388–389), and Proposition 19.10, printed p.400 (PDF 416).
- `CentralQuotientReductiveStatement` (`Reductive/CentralQuotientReductiveStatement`): `G`
  connected reductive; `N` contained in the centre; an fppf quotient `q : G ⟶ Q` by `N` with
  `Q` affine and locally of finite type. Conclusion: `Q` is connected reductive. Status P:
  `centralQuotientReductive` (`Reductive/CentralQuotientReductiveProof`).
- `ReductiveCentralTorusSemisimpleQuotientStatement`
  (`Reductive/CentralTorusSemisimpleQuotientStatement`): `G` connected reductive has a closed
  central torus `Z` such that every affine, locally finite type fppf quotient `G/Z` is
  semisimple. Status P: `reductiveCentralTorusSemisimpleQuotient`
  (`Reductive/CentralTorusSemisimpleQuotientProof`).

**F6. Centres of normal reductive subgroups.** Source: Conrad–Gabber–Prasad, Proposition
A.1.13, printed p.471 (PDF 497).
- Lean: `NormalReductiveCenterStatement` (`Reductive/NormalCenterStatement`): `G`, `H`
  connected reductive and `H` a closed normal subgroup of `G`. Conclusion: the centre of `H`
  lies in the centre of `G`.
- Status P: `normalReductiveCenter` (`Reductive/NormalCenterProof`).

**F7. Products.**
- D: `isSemisimple_tensor_of_commutingSubgroupMultiplication`
  (`Reductive/CommutingMultiplicationFiniteCenters`): for `G` semisimple and commuting smooth
  connected closed subgroups `H`, `K` with finite centres whose multiplication is
  surjective, `H × K` is semisimple.
- Direct products: the contract lists products in this family. The Library has no
  statement that a direct product of connected reductive, semisimple or pseudo-reductive
  groups has the same property; status M. This ledger cites no numbered source item for
  it. Owner task: none.

**F8. Characteristic zero.**
- `ReductiveCharZeroSemisimplicityStatement` (`Reductive/CharZeroSemisimplicityStatement`):
  `[IsAlgClosed k]`, `[CharZero k]`; `G` pseudo-reductive. Conclusion: every matrix
  representation is semisimple. Source: Mumford–Fogarty–Kirwan, Appendix to Chapter 1, §A,
  printed p.191 (PDF 203): (i) and (ii) are equivalent in characteristic zero. Status P:
  `reductiveCharZeroSemisimplicityStatement` (`Reductive/CharZeroSemisimplicityProof`).
- `CharacteristicZeroLeviDecompositionStatement` (`Reductive/CharacteristicZeroLeviStatement`):
  `[CharZero F]`; `G` affine, locally of finite type, smooth and connected. Conclusion: a
  connected reductive `L` with `j : L ⟶ G` and `p : G ⟶ L`, `j ≫ p = id`, and `ker p` smooth,
  connected and unipotent; so `G = ker p ⋊ L`. Source: Milne 2017, Definition 25.46 and
  25.48–25.49, printed p.559 (PDF 575). In positive characteristic Levi subgroups need not
  exist (Milne 25.51, same page); no such statement is made. Status P:
  `characteristicZeroLeviDecomposition` (`Reductive/CharacteristicZeroLeviProof`).

**F9. Haboush's theorem.** Source: Mumford–Fogarty–Kirwan, Appendix to Chapter 1, §A,
definition (iii), printed p.191 (PDF 203), and Theorem A.1.0, a) ⇒ b), printed p.192
(PDF 204).
- Lean: `ReductiveGeometricReductivityStatement` (`Reductive/GeometricReductivityStatement`).
  Hypotheses: `[IsAlgClosed k]`; `G` pseudo-reductive (equivalently connected reductive, by
  section A). Conclusion: for every matrix representation and nonzero fixed vector `v`
  there is a homogeneous invariant polynomial `F` of positive degree, invariant on all test
  schemes, with `F(v) ≠ 0`.
- Status P: `reductiveGeometricReductivity` (`Reductive/GeometricReductivityProof`).
- Linear reductivity is not used as a definition of reductivity anywhere in the Library.

**F10. Density of rational points.** Source: Milne 2017, Theorem 17.93(b), printed p.382
(PDF 398).
- Lean: `ReductiveRationalPointDensityStatement` (`Reductive/RationalPointDensityStatement`).
  Hypotheses: `[Infinite k]`; `G` connected reductive. Conclusion: the rational points are
  dense in `G`.
- Status P: `reductiveRationalPointDensity` (`Reductive/RationalPointDensityProof`).

**F11. Affine homogeneous spaces.** Source: Conrad–Gabber–Prasad, the proof of Proposition
A.8.12, printed pp.552–553 (PDF 578–579).
- Lean: `AffineHomogeneousQuotientReductiveStatement` (`Reductive/AffineHomogeneousQuotientStatement`).
  Hypotheses: `G` connected reductive; a smooth closed subgroup `H` and a homogeneous
  quotient `G/H` whose structure map is affine. Conclusion: the identity component of `H` is
  connected reductive.
- Status P: `affineHomogeneousQuotientReductive` (`Reductive/AffineHomogeneousQuotientProof`).

## G. Pseudo-parabolic subgroups

In this section `G` is smooth, with affine structure map and connected, over any field.

**G1. Pseudo-parabolic subgroups are smooth and connected.** Source: Conrad–Gabber–Prasad,
Definition 2.2.1, printed p.62 (PDF 88), and Proposition 2.1.8(3)–(4), printed p.53 (PDF 79).
- Lean: `PseudoParabolicSubgroupStructureStatement` (`PseudoParabolicStructureStatement`).
  Conclusion: a pseudo-parabolic `P` is smooth, connected and affine.
- Status P: `pseudoParabolicSubgroupStructure` (`PseudoParabolicStructureProof`).

**G2. `G/P` is pseudo-complete.** Source: Conrad–Gabber–Prasad, Proposition C.1.6 and its
proof, printed pp.586–588 (PDF 612–614), with Definition C.1.1, printed p.581 (PDF 607).
- Lean: `PseudoParabolicQuotientPseudoCompleteStatement` (`PseudoParabolicQuotientStatement`).
  Hypotheses: a pseudo-parabolic `i`; a **supplied** quotient `q : G ⟶ Q` (`Q` separated,
  locally of finite type, quasi-compact; `q` smooth, surjective, quasi-compact; fibres the
  cosets of `P`). Conclusion: `Q` is pseudo-complete.
- Status P: `pseudoParabolicQuotientPseudoComplete` (`PseudoParabolicQuotientPseudoCompleteAssembly`).

**G3. Pseudo-parabolics and the split unipotent radical.** Source: Conrad–Gabber–Prasad,
Proposition 2.2.4, printed pp.63–64 (PDF 89–90), Corollary 2.2.5, printed p.64 (PDF 90),
and Corollary 2.1.9, printed p.58 (PDF 84).
- `PseudoParabolicSplitRadicalProductStatement` (`PseudoParabolicSplitRadicalProductStatement`):
  a point lies fppf-locally in `P(χ) · R_{u,k}(G)` if and only if it lies fppf-locally in
  `P(χ) · R_{us,k}(G)`. Status P: `pseudoParabolicSplitRadicalProduct`
  (`PseudoParabolicSplitRadicalProductProof`).
- `PseudoParabolicSplitRadicalContainmentStatement` (`PseudoParabolicSplitRadicalContainmentStatement`):
  for a pseudo-parabolic `P = P(χ) · R_{u,k}(G)`, `U(χ)` and `R_{us,k}(G)` lie in the split
  unipotent radical of `P`. Status P: `pseudoParabolicSplitRadicalContainment`
  (`PseudoParabolicSplitRadicalContainmentProof`).
- `PseudoParabolicSplitRadicalQuotientStatement` (`PseudoParabolicSplitRadicalQuotientStatement`):
  for an fppf quotient `f : G ⟶ H` by `R_{us,k}(G)` (with `H` smooth, affine, connected), every
  pseudo-parabolic of `G` is the preimage of a pseudo-parabolic of `H`. Status P:
  `pseudoParabolicSplitRadicalQuotient` (`PseudoParabolicSplitRadicalQuotientProof`).

**G4. Local sections of `G → G/P`.** Source: Conrad–Gabber–Prasad, Lemma C.2.1 and its
proof, printed pp.592–593 (PDF 618–619).
- Lean: `PseudoParabolicQuotientLocalSectionsStatement` (`PseudoParabolicQuotientLocalSectionsStatement`).
  Hypotheses: `[Infinite k]`; a pseudo-parabolic `i`; a supplied quotient `q` as in G2.
  Conclusion: every point of `Q` has an open neighbourhood over which `q` has a section.
- Status O. Owner task: none. The rational-point consequence of Lemma C.2.1 is
  `PseudoParabolicQuotientRationalLiftingStatement`, which is proved
  (`pseudoParabolicQuotientRationalLifting`, `PseudoParabolicQuotientRationalLiftingProof`).

## Summary and remaining obligations

Counted by the Lean statements named above, 61 have published proofs (P), including
`PseudoParabolicQuotientRationalLiftingStatement` (G4) and `IsSemisimpleFieldExtensionStatement`
(C2). Two have a
composite and no wrapper theorem (C): `ConnectedReductiveAlgebraicExtensionAscentStatement`
and `SemisimpleAlgebraicExtensionAscentStatement`, the two projections of the published
`algebraicExtensionAscent`. One statement is open (O):
`PseudoParabolicQuotientLocalSectionsStatement` (G4).

Source assertions of this family with no Lean statement (M), none with an owner task:

1. Conrad–Gabber–Prasad, Example 1.1.3: a pseudo-reductive group that is not reductive over
   an imperfect field (B5).
2. The remaining parts of Conrad–Gabber–Prasad, Proposition 1.1.9(1): ascent of
   pseudo-reductivity along separable transcendental extensions, and the equality
   `R_{u,k}(G)_K = R_{u,K}(G_K)` (B6).
3. Direct products of connected reductive, semisimple and pseudo-reductive groups (F7).

Reflection of connected reductivity along arbitrary field extensions (C1, Milne 19.13) is
not in this list: the published theorem `IsConnectedReductive.of_fieldExtension` (D) proves
it, and only a named proposition declaration and its wrapper are missing. The same holds
for reflection of pseudo-reductivity along arbitrary extensions (B6), which follows from
the published D results listed there.

The wrapper theorems for the two C rows, and named statements with wrappers for the two
reflections above, need no new mathematics; the program will collect them, with those of
the other families, in one task. Items 1–3 need focused statement tasks.

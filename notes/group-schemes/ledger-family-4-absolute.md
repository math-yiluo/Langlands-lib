# Group-scheme ledger, family 4: absolute structure over fields

For the additional dynamic statement publications and proof owners as of
13 November 2026, see [the dated dynamic update](dynamic-relative-progress.md).
It supplements rows C3, C7 and C8; the labels below describe the original snapshot.

Author: Worker 3483, 10 November 2026, for the algebraic and reductive group-scheme program
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e` (Task 3483). This note is the source-to-declaration
ledger for family 4 of that program's contract. Family 4 covers:

- maximal tori and Borel subgroups over a field;
- roots, root data on the actual character and cocharacter lattices, and Weyl groups;
- the dynamic subgroups `P(λ)`, `Z(λ)`, `U(λ)` and the opposite cell;
- parabolic subgroups, parabolic quotients and the absolute Bruhat covering;
- the determinant of the adjoint action on `Lie U(λ)`.

It describes Library commit `e449cde988d4e97ab280b8d4d11262887ccc26e0` and environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`. All Lean names are in `Langlands.GroupScheme`
unless a namespace is shown. Module paths are relative to `Langlands/GroupScheme/` in that
commit. "Field group" means a group scheme over `Spec k` for a field `k : Type u`.
"Connected reductive" means `IsConnectedReductive` (`Reductive/Basic`): smooth, affine
structure map, connected, and trivial unipotent radical after base change to an algebraic
closure.

Rational structure (maximal split tori, relative roots, rational parabolics) is family 5 of
the program and is not listed here.

## Status codes and evidence

Each row gives the source assertion with its locator, the exact Lean statement and its
hypotheses, a status, the evidence, and the owner task.

- **D (definition or internal result).** A published construction, or a published
  theorem that is not a proposition declaration, with the hypotheses listed in the row.
  The evidence is its module path. No owner task is needed.
- **P (published proof).** The Library at the commit above contains a theorem whose type is
  exactly the statement. The evidence is that theorem and its module path. The author also
  type-checked `example : S := proof` for every P row in a private module. That check
  passed with no errors or warnings, but it is not public evidence. No further proof work or
  owner task is needed.
- **C (composite, not published).** No published theorem has the statement as its type.
  However, a term built only from published theorems has that type: the author type-checked
  it in the same private module, and its axioms are `propext`, `Classical.choice` and
  `Quot.sound`. The composite is not an accepted artifact. The row names the owner task,
  or says that there is none. A projection out of a published conjunction is also listed
  as C: what is missing is then a named wrapper theorem, not mathematics.
- **O (open).** No published proof and no composite from published results is known.

The labels "accepted" and "published" are used only for artifacts that passed independent
review.

Source locators use these registered sources, cited by source id:
- `milne-2017-algebraic-groups`: J. S. Milne, *Algebraic Groups* (2017). PDF page = printed
  page + 16.
- `milne-2022-algebraic-groups`: the 2022 corrected reprint. PDF page = printed page + 11.
- `conrad-2014-reductive-group-schemes`: B. Conrad, *Reductive group schemes* (2014).
  Printed page = PDF page.
- `conrad-gabber-prasad-2015-pseudo-reductive`: Conrad, Gabber and Prasad,
  *Pseudo-reductive groups*, 2nd edition (2015). PDF page = printed page + 26.
- `borel-tits-1965-groupes-reductifs`: Borel and Tits, *Groupes réductifs*, Publ. Math.
  IHÉS 27 (1965). Journal page numbers are given.
- `renard-2026-representations-groupes-reductifs-padiques`: D. Renard, *Représentations des
  groupes réductifs p-adiques*, 9 July 2026 version. PDF page = printed page + 6.

The author re-read every locator below in the original source for this note, on 10 November
2026, and checked that the cited item is on the cited page.

## Conventions

- `IsMaximalTorus i` (`Torus/Maximal`): `T` is a torus, `i : T ⟶ G` is a closed subgroup,
  and `i` does not factor through a strictly larger closed torus **over the same field**.
  By A2 this agrees with maximality after any field extension when `G` is smooth with
  affine structure map.
- `IsBorelSubgroup i` (`Absolute/Borel`): `B` is smooth and connected, `i` is a closed
  subgroup, `IsSolvableGroupScheme B` holds (the group of points of `B` over an algebraic
  closure is solvable), and `i` is maximal among smooth connected solvable closed subgroups
  **over the same field**. Over a non-algebraically closed field this is not the geometric
  notion. Milne's Definition 17.6, printed p.353 (PDF 369), works over an algebraically
  closed field.
- `IsParabolicSubgroup i` (`Absolute/Borel`): `i` is a smooth closed subgroup whose base
  change to `AlgebraicClosure k` contains a Borel subgroup of the base change of `G`. This
  is the geometric notion of Milne, Definition 17.15 and Theorem 17.16, printed p.356
  (PDF 372), and §17.66, printed p.375 (PDF 391).
- `IsBorelPair i j`: `i` Borel, `j` a maximal torus, and `j` factors through `i`.
- Several statements assume `IsAlgClosed k`. Each row says so when it does.

## A. Maximal tori and Borel subgroups

**A1. Existence of maximal tori.** Source: Milne 2017, Corollary 17.83, printed p.379
(PDF 395): there is a maximal torus of `G_{k^a}` defined over `k`.
- Lean: `MaximalTorusExistenceStatement` (`Torus/ExistenceStatement`). Hypotheses: a field
  group `G` that is smooth with affine structure map. Conclusion: some `i : T ⟶ G` with
  `IsMaximalTorus i`.
- Scope: maximality is over `k`; A2 turns it into geometric maximality.
- Status P: `maximalTorusExistence` (`Torus/ExistenceProof`).

**A2. Maximality under field extension.** Source: Milne 2017, Theorem 17.82, printed p.379
(PDF 395).
- Lean: `MaximalTorusBaseChangeStatement` (`Torus/MaximalBaseChangeStatement`). Hypotheses:
  fields `k`, `K` with `Algebra k K`, a smooth field group `G` with affine structure map, a
  torus `T` and a closed subgroup `i : T ⟶ G`. Conclusion: `IsMaximalTorus i` if and only
  if `IsMaximalTorus i_K`.
- Status P: `maximalTorusBaseChange` (`Torus/MaximalBaseChangeProof`).

**A3. Conjugacy of maximal tori.** Source: Milne 2017, Theorem 17.10, printed p.354
(PDF 370).
- Lean: `MaximalTorusConjugacyStatement` (`Absolute/BorelStatement`). Hypotheses: `k`
  algebraically closed; `G` smooth, with affine structure map and connected; maximal tori
  `j : T ⟶ G` and `j' : T' ⟶ G`. Conclusion: a point `g ∈ G(k)` and `φ : T ≅ T'` with
  `j ≫ int(g) = φ ≫ j'`.
- Status P: `maximalTorusConjugacy` (`Absolute/MaximalTorusConjugacyProof`).

**A4. Properness of `G/B`.** Source: Milne 2017, Definition 17.6, printed p.353 (PDF 369),
and Theorem 17.9(a), printed p.354 (PDF 370).
- Lean: `SomeBorelQuotientProperStatement` (`Absolute/BorelProperQuotientStatement`).
  Hypotheses: `k` algebraically closed; `G` smooth, with affine structure map and connected.
  Conclusion: some Borel subgroup `i : B ⟶ G` has the following property. For every
  **supplied** `Q` over `Spec k` and `q : G ⟶ Q` with
  - `Q` separated, locally of finite type and quasi-compact over `k`,
  - `q` smooth, surjective and quasi-compact,
  - `g ≫ q = h ≫ q ↔ g⁻¹h ∈ B` for all points `g`, `h` over every test scheme,

  `Q` is proper over `k`.
- Scope: the quotient is an input. Its existence is the separate statement
  `SmoothSubgroupQuotientExistenceStatement` (`HomogeneousQuotientStatement`): for a smooth
  closed subgroup of a smooth field group with affine structure map, such a `Q` and `q`
  exist. Source: Milne 2017, Definition 5.20 and Propositions 5.21–5.25, printed
  pp.104–105 (PDF 120–121), and Proposition 7.15 and Theorem 7.18, printed pp.142–143
  (PDF 158–159). Status P: `smoothSubgroupQuotientExistence` (`HomogeneousQuotientProof`).
- Status P: `someBorelQuotientProper` (`Absolute/BorelProperQuotientProof`).

**A5. Conjugacy of Borel subgroups.** Source: Milne 2017, Theorem 17.9(b), printed p.354
(PDF 370).
- Lean: `BorelConjugacyStatement` (`Absolute/BorelStatement`). Hypotheses: as A3.
  Conclusion: a Borel subgroup exists, and for Borel subgroups `i`, `i'` there are
  `g ∈ G(k)` and `φ : B ≅ B'` with `i ≫ int(g) = φ ≫ i'`.
- Status P: `borelConjugacy` (`Absolute/BorelConjugacyProof`).

**A6. Normalizer theorem, rational-point form.** Source: Milne 2017, Theorem 17.48, printed
p.367 (PDF 383).
- Lean: `BorelNormalizerStatement` (`Absolute/BorelStatement`). Hypotheses: as A3, and a
  Borel subgroup `i : B ⟶ G`. Conclusion: the normalizer in the group `G(k)` of the image of
  `B(k)` equals that image.
- Scope: Milne's theorem is the equality `N_G(B) = B` of algebraic subgroups. The Lean
  statement is its form on `k`-points over an algebraically closed field.
- Status P: `borelNormalizer` (`Absolute/BorelNormalizerProof`).

**A7. Borel pairs.** Source: Milne 2017, Definition 17.12 and the following paragraph,
printed p.355 (PDF 371).
- Lean: `BorelMaximalTorusStatement` (`Absolute/BorelMaximalTorusStatement`). Hypotheses: as
  A3, and a Borel subgroup `i`. Conclusion: some maximal torus `j` with `IsBorelPair i j`.
- Status P: `borelMaximalTorus` (`Absolute/BorelMaximalTorusProof`).

**A8. Two Borel subgroups contain a common maximal torus.** Source: Borel–Tits 1965, §2.4,
p.65.
- Lean: `TwoBorelCommonMaximalTorusStatement` (`Absolute/TwoBorelCommonMaximalTorusStatement`).
  Hypotheses: `k` algebraically closed, `G` connected reductive, Borel subgroups `i`, `i'`.
  Conclusion: a maximal torus `t : T ⟶ G` that factors through both.
- Status P: `twoBorelCommonMaximalTorus` (`Absolute/TwoBorelCommonMaximalTorusProof`).

**A9. Borel subgroups under extension of algebraically closed fields.** Source: Milne 2017,
Definition 17.6, printed p.353 (PDF 369), and §17.66, printed p.375 (PDF 391).
- Lean: `BorelAlgClosedFieldExtensionStatement` (`Absolute/BorelAlgClosedFieldExtensionStatement`).
  Hypotheses: algebraically closed fields `k`, `K` with `Algebra k K`; `G` with affine
  structure map, smooth and connected; a Borel subgroup `i`. Conclusion: `i_K` is a Borel
  subgroup.
- Status P: `borelAlgClosedFieldExtensionStatement` (`Absolute/BorelAlgClosedFieldExtensionProof`).

**A10. Subgroups containing a Borel subgroup are connected.** Source: Milne 2017, Corollary
17.49, printed p.367 (PDF 383).
- Lean: `BorelContainingSubgroupConnectedStatement`
  (`Absolute/BorelContainingSubgroupConnectedStatement`). Hypotheses: as A3; a smooth closed
  subgroup `i : P ⟶ G`, a Borel subgroup `j : B ⟶ G` and `f : B ⟶ P` with `f ≫ i = j`.
  Conclusion: `P` is connected.
- Scope: Milne also proves `P = N_G(P)`; that part has no Lean statement here.
- Status P: `borelContainingSubgroupConnectedStatement` (`Absolute/BorelContainingSubgroupConnected`).

**A11. Borel subgroups of centralizers.** Source: Milne 2017, Theorem 17.46, printed
pp.365–366 (PDF 381–382). Milne: for a torus `S` in a Borel subgroup `B`, `C_G(S) ∩ B` is a
Borel subgroup of `C_G(S)`, and over an algebraically closed field every Borel subgroup of
`C_G(S)` has this form.
- Lean: `CentralizerBorelIntersectionStatement` (`Absolute/CentralizerBorelIntersectionStatement`).
  Hypotheses:
  - `k` algebraically closed; `G` smooth, with affine structure map and connected;
  - a cocharacter `χ : 𝔾_m ⟶ G`;
  - a closed subgroup `j : M ⟶ G` representing `Dynamic.centralizer χ`, with `M` smooth and
    connected;
  - a Borel subgroup `b : B ⟶ G` with `range χ ≤ range b` (the image of `χ` lies in `B`).

  Conclusion: some Borel subgroup `c : C ⟶ M` of `M` with `range (c ≫ j) ≤ range b`.
- Scope: this is only the existence of a Borel subgroup of the centralizer inside `B`, for
  the image of a cocharacter. The Lean statement does not say that the intersection
  `C_G(S) ∩ B` is a Borel subgroup, and does not contain the converse.
- Status P: `centralizerBorelIntersection` (`Absolute/CentralizerBorelIntersectionProof`).

**A12. Maximal tori are self-centralizing.** Source: Milne 2017, Corollary 17.84, printed
p.379 (PDF 395), the "only if" direction; Proposition 17.61(a), printed p.372 (PDF 388), for
the algebraically closed case.
- Lean: `MaximalTorusCentralizerStatement` (`Absolute/MaximalTorusCentralizerStatement`).
  Hypotheses: a field `k`, `G` connected reductive, a maximal torus `j`. Conclusion:
  `torusCentralizer j = range j`, as subgroup functors on every test scheme.
  Status P: `maximalTorusCentralizer` (`Absolute/MaximalTorusCentralizerProof`).
- `AlgClosedMaximalTorusCentralizerStatement` (`Absolute/MaximalTorusCentralizerReduction`):
  the same with `k` algebraically closed. Status P: `algClosedMaximalTorusCentralizer`
  (`Absolute/AlgClosedMaximalTorusCentralizerProof`).

**A13. Connected reductivity under field extension.** Source: Milne 2017, Proposition 19.13,
printed p.400 (PDF 416).
- Lean: `ConnectedReductiveFieldExtensionStatement` (`Reductive/FieldExtensionStatement`).
  Hypotheses: fields `k`, `K` with `Algebra k K`, `G` connected reductive. Conclusion: `G_K`
  is connected reductive.
- Scope: only the forward implication of Milne's equivalence.
- Status P: `connectedReductiveFieldExtensionStatement` (`Reductive/FieldExtensionProof`).

**A14. The Borel subgroups of `GL_N`.** Source: Milne 2017, Example 17.7, printed p.354
(PDF 370).
- Lean: `GeneralLinearBorelStatement` (`Absolute/BorelStatement`). Hypotheses: any field `k`,
  `N : ℕ` and a strictly decreasing `e : Fin N → ℤ`. Conclusion: the block parabolic of `e`
  (the upper triangular matrices) is a Borel subgroup of `GL_N`; with the diagonal torus it
  is a Borel pair; it represents `Dynamic.parabolic` of the diagonal cocharacter of `e`; and
  that cocharacter is regular.
- Status P: `generalLinearBorel` (`Absolute/GeneralLinearBorelProof`).

## B. Roots, root data and Weyl groups

Root data are Mathlib `RootDatum J (characterLattice T) (cocharacterLattice T)` with `J` a
finite index type. `IsRootDatumOf i P` (`Reductive/RootDatum`) says: the pairing of `P` is
`latticePairing T`, the roots of `P` are `roots i`, and each reflection of `P` is induced by
some `k`-point normalizing `i`. In B2–B12, "split hypotheses" means: a field `k`, `G`
connected reductive, `T` with `IsSplitTorus T`, and a maximal torus `i : T ⟶ G`.

**B1. Weight decomposition.** Source: Milne 2017, Theorem 12.12, printed p.234 (PDF 250),
applied to the adjoint representation as in §21.a, printed p.424 (PDF 440).
- Lean: `WeightDecompositionStatement` (`Reductive/RootDatumStatement`). Hypotheses: a field
  group `G` with affine and locally finite type structure map, a split torus `T` and any
  homomorphism `i : T ⟶ G`. Conclusion: `Lie(G)(k)` is the internal direct sum of the
  weight spaces `weightSpace i χ`.
- Status P: `weightDecompositionStatement` (`Reductive/WeightDecompositionProof`).

**B2. Existence of the root datum.** Source: Milne 2017, Theorem 21.11, printed pp.428–429
(PDF 444–445), and Corollary 21.12, printed p.430 (PDF 446).
- Lean: `RootDatumExistenceStatement` (`Reductive/RootDatumStatement`). Hypotheses: split
  hypotheses. Conclusion: a finite `J` and a reduced `P` with `IsRootDatumOf i P`.
- Status P: `rootDatumExistence` (`Reductive/RootDatumExistence`).

**B3. Uniqueness of the root datum.** Source: Milne 2017, Theorem 21.11(e), printed p.429
(PDF 445): uniqueness of the coroot.
- Lean: `RootDatumUniquenessStatement` (`Reductive/RootDatumStatement`). Hypotheses: split
  hypotheses, and root data `P`, `P'` of `i`. Conclusion: a bijection `e : J ≃ J'` matching
  roots and coroots.
- Status P: `rootDatumUniqueness` (`Reductive/RootDatumUniquenessProof`).

**B4. The Weyl group.** Source: Milne 2017, Proposition 21.1, printed p.424 (PDF 440),
Theorem 21.37, printed p.435 (PDF 451), and Corollary 21.38, printed p.436 (PDF 452).
- Lean: `WeylGroupStatement` (`Reductive/RootDatumStatement`). Hypotheses: split hypotheses
  and a root datum `P` of `i`. Conclusion: the image of the Weyl action of the normalizer
  points equals the image of `P.weylGroup` in the automorphisms of `X^*(T)`, and the kernel
  of the Weyl action is the centralizer.
- Status P: `weylGroup` (`Reductive/RootDatumWeylProof`).

**B5. Reducedness.** Source: Milne 2017, Theorem 21.11(b), printed p.428 (PDF 444).
- Lean: `RootReducednessStatement` (`Reductive/RootReducednessStatement`). Hypotheses: split
  hypotheses. Conclusion: two `ℤ`-linearly dependent roots are equal or opposite.
- Status P: `rootReducedness` (`Reductive/RootReducednessProof`).

**B6. Root spaces of the Lie algebra are lines.** Source: Milne 2017, Theorem 21.11(b),
printed p.428 (PDF 444): `dim g_α = 1`.
- Lean: `SplitRootLieLineStatement` (`Reductive/SplitRootLieLineStatement`). Hypotheses:
  split hypotheses. Conclusion: for each root `χ`, `weightSpace i χ` is isomorphic to `k` as
  a `k`-module.
- Status P: `splitRootLieLine` (`Reductive/SplitRootLieLineProof`).

**B7. Root groups are one-dimensional vector groups.** Source: Milne 2017, Definition 21.10,
printed p.428 (PDF 444), and Theorem 21.11(c), printed p.429 (PDF 445): the root group `U_α`
is isomorphic to `𝔾_a`.
- Lean: `AbsoluteRootVectorLineStatement` (`Absolute/RootVectorLineStatement`). Hypotheses:
  `k` algebraically closed, `G` connected reductive, `t : T ⟶ G` a split subtorus that is a
  maximal torus, and `α ∈ relativeRoots t`. Conclusion: a closed subgroup `j : U ⟶ G`
  representing the intrinsic root subgroup functor `RelativeRoot.subgroup t α`, with `U` a
  vector group of dimension 1.
- Scope: algebraically closed fields only. The statement concerns root **subgroups**; it
  contains no comparison with the Lie root spaces of B6, and names no isomorphism with
  `𝔾_a` beyond "vector group of dimension 1".
- Status P: `absoluteRootVectorLine` (`Absolute/RootVectorLineProof`).

**B8. Semisimple rank one: at most one positive root.** Source: Milne 2017, §20.e, printed
p.412 (PDF 428), and the proof of Theorem 21.11(b), printed p.428 (PDF 444).
- Lean: `RankOnePositiveRootUniquenessStatement` (`Reductive/RankOnePositiveRootStatement`).
  Hypotheses: split hypotheses, and any two roots are `ℤ`-linearly dependent. Conclusion:
  for each cocharacter `ν`, at most one root `α` has `⟨α, ν⟩ > 0`.
  Status P: `rankOnePositiveRootUniqueness` (`Reductive/RankOnePositiveRootProof`).
- `RankOneAlgClosedPositiveRootUniquenessStatement` (`Reductive/RankOnePositiveRootBaseChange`):
  the same over an algebraically closed field. Status P:
  `rankOneAlgClosedPositiveRootUniqueness` (`Reductive/RankOneAlgClosedPositiveRootUniquenessProof`).
- `RankOneAlgClosedBorelExclusionStatement` (`Absolute/RankOneAlgebraicClosureReduction`),
  an internal step of the same argument: `k` algebraically closed, split hypotheses, a
  Borel subgroup `b` with `t ≫ b = i`, and a root `α`; then the Lie algebra of `B` does not
  meet both weight spaces `α` and `-α` (`Lie.MeetsWeightSpace`). Status P:
  `rankOneAlgClosedBorelExclusion` (`Absolute/RankOneAlgClosedBorelExclusionProof`).

**B9. Roots of the centralizer of a cocharacter.** Source: Milne 2017, Theorem 13.33(c),
printed p.265 (PDF 281), and Proposition 21.90(a), printed p.453 (PDF 469); CGP,
Proposition 2.1.8(1), printed p.53 (PDF 79).
- Lean: `DynamicCentralizerRootsStatement` (`Dynamic/CentralizerRootsStatement`). Hypotheses:
  split hypotheses; a cocharacter `ν` of `T`; a closed subgroup `z : Z ⟶ G` representing
  `Dynamic.centralizer (ν ≫ i)`, with `Z` connected reductive; `t : T ⟶ Z` with
  `t ≫ z = i`. Conclusion: `roots t = {α ∈ roots i | ⟨α, ν⟩ = 0}`.
- Status P: `dynamicCentralizerRoots` (`Dynamic/CentralizerRootsProof`).

**B10. The root datum under field extension.** Internal compatibility target, with no
external source assertion. It transports the root datum along the actual lattice
pullback of `Torus/SplitLatticeBaseChange`.
- Lean: `SplitRootDatumFieldExtensionStatement` (`Reductive/RootDatumBaseChangeStatement`).
  Hypotheses: fields `k`, `K`, split hypotheses over `k`, and a root datum `P` of `i`.
  Conclusion: the transported datum `SplitRootDatum.baseChange … P` is a root datum of
  `i_K`.
- Status P: `splitRootDatumFieldExtension` (`Reductive/RootDatumBaseChangeProof`).

**B11. Weyl elements of a split maximal torus are rational.** Source: Milne 2017,
Proposition 21.1, printed p.424 (PDF 440): `W(G,T)(k) = W(G,T)(k') = N(k')/T(k')`.
- Lean: `SplitMaximalTorusWeylRationalityStatement` (`Reductive/SplitWeylRationalityStatement`).
  Hypotheses: fields `k`, `K`, split hypotheses over `k`. Conclusion: every automorphism of
  `T_K` induced by a `K`-point normalizing `T_K` is the base change of an automorphism of
  `T` induced by a `k`-point normalizing `T`.
- Status P: `splitMaximalTorusWeylRationality` (`Reductive/SplitWeylRationality`).

**B12. The root datum of `GL_n`.** Source: Milne 2017, Example 17.88, printed p.380 (PDF
396), Example 21.6, printed p.426 (PDF 442), and Example 21.40, printed p.436 (PDF 452).
- Lean: `GeneralLinearRootDatumStatement` (`Reductive/RootDatumStatement`). Hypotheses: any
  field `k` and a finite type `n`. Conclusion: the diagonal torus is maximal; its roots are
  `e_i − e_j` (`i ≠ j`) under `splitTorus.characterLatticeEquiv`; `GeneralLinear.rootDatum n k`
  is its root datum and is reduced; and the Weyl image is the image of the injective
  permutation action of `S_n`.
- Status P: `generalLinearRootDatum` (`Reductive/GeneralLinearRootDatumProof`).

## C. Dynamic subgroups and the opposite cell

**C1. The dynamic subgroups.** Source: Milne 2017, §13.d, printed pp.263–265 (PDF 279–281);
CGP, Lemma 2.1.5, printed p.50 (PDF 76); Conrad, Theorem 4.1.7, pp.112–113.
- Lean (`Dynamic/Basic`): for a cocharacter `χ : 𝔾_m ⟶ G` of a group scheme over any base,
  `Dynamic.parabolic χ`, `Dynamic.centralizer χ` and `Dynamic.unipotent χ` are subgroup
  functors defined on every test scheme, including non-reduced ones, by extension of the
  conjugation orbit over the affine line.
- Lean (`Dynamic/AffineRepresentability`): for `G` affine over `Spec R`,
  `Dynamic.Affine.parabolicHom χ`, `centralizerHom χ` and `unipotentHom χ` are closed
  subgroups representing these functors (`isRepresentedBy_parabolicHom` and so on,
  `isClosedSubgroup_parabolicHom` and so on).
- Status D.

**C2. Smoothness.** Source: CGP, Proposition 2.1.8(3), last paragraph, printed p.53 (PDF
79); Milne 2017, Theorem 13.33(a), printed p.265 (PDF 281).
- Lean: `DynamicSmoothStatement` (`Dynamic/SmoothConnectedStatement`). Hypotheses: a field
  group `G` that is **smooth** with affine structure map, a cocharacter `χ`, and any
  `j : H ⟶ G` representing `P(χ)`, `Z(χ)` or `U(χ)`. Conclusion: `H` is smooth.
- Status P: `dynamicSmooth` (`Dynamic/SmoothProof`).

**C3. Connectedness.** Source: CGP, Proposition 2.1.8(4), printed p.53 (PDF 79).
- Lean: `DynamicConnectedStatement` (`Dynamic/SmoothConnectedStatement`). Hypotheses: as C2.
  Conclusion: a representative of `U(χ)` is connected; if `G` is connected, so are
  representatives of `P(χ)` and `Z(χ)`.
- Status P: `dynamicConnected` (`Dynamic/ConnectedProof`).

**C4. Lie algebras.** Source: CGP, Proposition 2.1.8(1), printed p.53 (PDF 79); Milne 2017,
Theorem 13.33(c), printed p.265 (PDF 281).
- Lean: `DynamicLieStatement` (`Dynamic/LieStatement`). Hypotheses: a field group `G` with
  affine and locally finite type structure map, `χ`, and `X ∈ Lie(G)(k)`. Conclusion: `X`
  lies in `Z(χ)`, `P(χ)`, `U(χ)` exactly when it lies in the weight space of weight `0`, the
  sum of weights `n ≥ 0`, the sum of weights `n > 0`, respectively.
- Status P: `dynamicLie` (`Dynamic/LieProof`).

**C5. Centralizers of cocharacters are reductive.** Source: Milne 2017, Corollary 17.59,
printed p.371 (PDF 387); CGP, Proposition 2.1.8(3),(4), printed p.53 (PDF 79).
- Lean: `DynamicCentralizerReductiveStatement` (`Dynamic/CentralizerReductiveStatement`).
  Hypotheses: a field `k`, `G` connected reductive, `χ`, and a closed `j : M ⟶ G`
  representing `Z(χ)`. Conclusion: `M` is connected reductive.
- Status P: `dynamicCentralizerReductive` (`Dynamic/CentralizerReductiveProof`).

**C6. `U(χ)` is the geometric unipotent radical of `P(χ)`.** Internal structural target,
with no external source assertion; its statement Markdown explains its extraction from
`DynamicSemistandardIntersectionStatement`.
- Lean: `DynamicGeometricUnipotentRadicalStatement` (`Dynamic/GeometricUnipotentRadicalStatement`).
  Hypotheses: a field `k`, `G` connected reductive, `χ`, `p : P ⟶ G` representing `P(χ)`, and
  `r : U ⟶ P` with `r ≫ p` representing `U(χ)`. Conclusion: `IsGeometricUnipotentRadical r`
  (`Rational/SemistandardIntersection`): `r` is a smooth connected unipotent normal closed
  subgroup, and it stays so and is maximal after base change to an algebraic closure.
- Status P: `dynamicGeometricUnipotentRadical` (`Dynamic/GeometricUnipotentRadicalProof`).

**C7. `U(χ)` is unipotent.** Source: CGP, Lemma 2.1.5, printed p.50 (PDF 76): over a field,
`U_G(λ)` has unipotent fibres when `G` is of finite type.
- Lean: `DynamicUnipotentUnipotenceStatement` (`Dynamic/UnipotentUnipotenceStatement`).
  Hypotheses: a field group `G` with affine and locally finite type structure map, `χ`,
  and `j : H ⟶ G` representing `U(χ)`. Conclusion: `IsUnipotent H`.
- Status P: `dynamicUnipotentUnipotence` (`Dynamic/UnipotentUnipotenceProof`).

**C8. The opposite open cell.** Source: CGP, Proposition 2.1.8(3), printed p.53 (PDF 79);
Milne 2017, Theorem 13.33(d), printed p.265 (PDF 281); Conrad, Theorem 4.1.7(4), p.113 (the
theorem begins on p.112).
- Lean: `OppositeCellStatement` (`Absolute/OppositeCellStatement`). Hypotheses: a field group
  `G` that is smooth with affine structure map; `χ`; `iU : U ⟶ G` representing `U(χ⁻¹)`,
  where `χ⁻¹` is `χ` composed with inversion of `𝔾_m`; `iP : P ⟶ G` representing `P(χ)`.
  Conclusion: the multiplication `U × P → G` is an open immersion.
- Scope: the field case. Conrad's version over a base ring belongs to family 8.
- Status P: `oppositeCellStatement` (`Absolute/OppositeCellProof`).

**C9. The opposite parabolic.** Source: Borel–Tits 1965, 4.8 and Proposition 4.10,
pp.88–89.
- Lean: `OppositeDynamicParabolicUniquenessStatement` (`Dynamic/OppositeParabolicUniquenessStatement`).
  Hypotheses: a field `k`, `G` connected reductive, cocharacters `χ`, `χ'` with
  `Z(χ') = Z(χ)`, and `P(χ)(k) ∩ P(χ')(k) = Z(χ)(k)`. Conclusion: `P(χ') = P(χ⁻¹)` and
  `U(χ') = U(χ⁻¹)`.
- Status P: `oppositeDynamicParabolicUniqueness` (`Dynamic/OppositeParabolicUniquenessProof`).

**C10. The flag variety `G/P(χ)`.** Source: Milne 2017, Theorem 25.1, printed p.544 (PDF
560); Definition 17.15 and Theorem 17.16, printed p.356 (PDF 372); Theorem 25.9, printed
p.546 (PDF 562); A.75–A.76, printed p.583 (PDF 599).
- Lean: `DynamicFlagQuotientExistenceStatement` (`Dynamic/FlagQuotientStatement`).
  Hypotheses: a field `k`, `G` connected reductive, `χ`. Conclusion: some `Q` proper over
  `k` and `π : G ⟶ Q` with `g ≫ π = h ≫ π ↔ g⁻¹h ∈ P(χ)` on every test scheme, and with a
  section of `π` over an open neighbourhood of every `k`-point of `Q`.
- Status P: `dynamicFlagQuotientExistence` (`Dynamic/FlagQuotientProof`).

**C11. Supplied dynamic quotients are proper.** Source: as C10.
- Lean: `DynamicQuotientProperStatement` (`Dynamic/QuotientProperStatement`). Hypotheses:
  `k` algebraically closed, `G` connected reductive, `χ`, and a supplied `Q`, `q` with the
  hypotheses of A4 for `P(χ)` in place of `B`. Conclusion: `Q` is proper.
- Status C. The author type-checked a short tactic proof that uses only published results:
  take the closed representative `Dynamic.Affine.parabolicHom χ` of `P(χ)` (C1); it is
  parabolic by `parabolicDynamic` (D5); then apply `parabolicSubgroupQuotientProper` (D6).
- Owner: Task 4665, `04457b36-90fb-4b02-85e4-924c3c791c0b`. Its contract forbids using
  `ParabolicDynamicStatement` and its proofs, because the consumer it was meant to support,
  `RankOnePositiveRootUniquenessStatement`, was unproved when it was written. That consumer
  is now published (B8). The composite above therefore cannot discharge Task 4665 as the
  contract stands.

**C12. Dynamic subgroups of `GL_n` for diagonal cocharacters.** Source: CGP, Example 2.1.1,
printed pp.45–47 (PDF 71–73); Lemma 2.1.5, printed pp.50–51 (PDF 76–77); Proposition
2.1.8(2), printed p.53 (PDF 79).
- Lean: `GeneralLinear.DynamicStatement` (`Dynamic/GeneralLinearStatement`), the conjunction
  of five statements over every commutative ring `R`:
  - `DiagonalCocharacterDynamicStatement`: for `e : n → ℤ`, `P`, `Z`, `U` of the diagonal
    cocharacter are the block parabolic, block Levi and block unipotent subgroup functors;
  - `BlockShapeDynamicStatement`: the same for the standard cocharacter of a block shape;
  - `DiagonalCocharacterLimitStatement`: the limit of the conjugation orbit exists exactly on
    block upper triangular points, and is their block diagonal part;
  - `DiagonalCocharacterLeviDecompositionStatement`: on points over every test scheme,
    `U(λ)` is normal in `P(λ)` with complement `Z(λ)`;
  - `BlockShapeLimitStatement`: the limit statement for block shapes.
- Status P for the conjunction: `GeneralLinear.dynamicStatement` (`Dynamic/GeneralLinearProof`).
  The five components are C, as its projections; no named theorem for them exists, and no
  task is needed.

**C13. Pseudo-reductive groups: `P(χ) = G` only for central `χ`.** Source: CGP, Lemma
2.2.3(2), printed p.62 (PDF 88).
- Lean: `PseudoReductiveCentralCocharacterStatement` (`Dynamic/PseudoReductiveCentralCocharacterStatement`).
  Hypotheses: a field `k`, `IsPseudoReductive G`, and `χ`. Conclusion:
  `Dynamic.parabolic χ = ⊤ ↔ Dynamic.centralizer χ = ⊤`.
- Status C. `IsPseudoReductive G` supplies smoothness, an affine structure map and a
  trivial ground-field unipotent radical. The published
  `Dynamic.parabolic_eq_top_iff_centralizer_eq_top_of_isUnipotent`
  (`Dynamic/TrivialUnipotentCentralizer`) gives the equivalence from that radical condition
  and a closed unipotent representative of `U(χ)`. The representative is
  `Dynamic.Affine.unipotentHom χ`: `Dynamic.Affine.isRepresentedBy_unipotentHom` and
  `Dynamic.Affine.isClosedSubgroup_unipotentHom` (`Dynamic/AffineRepresentability`) give
  representability and closedness, and `dynamicUnipotentUnipotence`
  (`Dynamic/UnipotentUnipotenceProof`) gives unipotence. No owner task was found; what is
  missing is a named theorem.

## D. Parabolic subgroups and the absolute Bruhat covering

**D1. Regular cocharacters and Borel subgroups.** Source: Milne 2017, Definition 21.26 and
Proposition 21.29, printed p.433 (PDF 449); Proposition 21.31 and Theorem 21.32, printed
p.434 (PDF 450).
- Lean: `RegularCocharacterBorelStatement` (`Absolute/BorelStatement`). Hypotheses: split
  hypotheses, with maximal torus `j`. Conclusion:
  - for a regular cocharacter `ν`, every closed subgroup representing `P(ν ≫ j)` is Borel;
  - for regular `ν`, `ν'`: `P(ν ≫ j) = P(ν' ≫ j)` if and only if `⟨α, ν⟩` and `⟨α, ν'⟩`
    have the same sign for every root `α`;
  - every Borel subgroup through which `j` factors represents `P(ν ≫ j)` for some regular
    `ν`.
- Status P: `regularCocharacterBorel` (`Absolute/RegularCocharacterBorelProof`).

**D2. Parabolics containing a split maximal torus.** Source: Milne 2017, Theorem 21.91,
printed p.453 (PDF 469), and Corollary 21.92, printed p.455 (PDF 471).
- Lean: `SplitParabolicCocharacterStatement` (`Absolute/SplitParabolicCocharacterStatement`).
  Hypotheses: split hypotheses with maximal torus `j`; a parabolic `i : P ⟶ G` and
  `f : T ⟶ P` with `f ≫ i = j`. Conclusion: `range i = Dynamic.parabolic (ν ≫ j)` for some
  cocharacter `ν` of `T`.
- Status P: `splitParabolicCocharacterStatement` (`Absolute/SplitParabolicCocharacterProof`).

**D3. Parabolics contain maximal tori.** Source: Milne 2017, proof of Theorem 25.1, printed
p.544 (PDF 560), with Theorem 17.82 and Corollary 17.83, printed p.379 (PDF 395).
- Lean: `ParabolicMaximalTorusStatement` (`Absolute/ParabolicMaximalTorusStatement`).
  Hypotheses: a field `k`, `G` connected reductive, a parabolic `i`. Conclusion: a maximal
  torus of `G` defined over `k` that factors through `i`.
- Status P: `parabolicMaximalTorus` (`Absolute/ParabolicMaximalTorusProof`).

**D4. Parabolics under field extension.** Source: Milne 2017, Definition 17.15 and Theorem
17.16, printed p.356 (PDF 372), and §17.66, printed p.375 (PDF 391).
- Lean: `ParabolicFieldExtensionStatement` (`Absolute/ParabolicFieldExtensionStatement`).
  Hypotheses: fields `k`, `K`, `G` connected reductive, a parabolic `i`. Conclusion: `i_K`
  is parabolic.
- Status P: `parabolicFieldExtensionStatement` (`Absolute/ParabolicFieldExtensionProof`).

**D5. Parabolic subgroups are the `P(χ)`.** Source: Milne 2017, Theorem 25.1, printed p.544
(PDF 560).
- Lean: `ParabolicDynamicStatement` (`Absolute/BorelStatement`). Hypotheses: a field `k`,
  `G` connected reductive, a closed subgroup `i`. Conclusion: `IsParabolicSubgroup i` if and
  only if `range i = Dynamic.parabolic χ` for some cocharacter `χ` over `k`.
- Status P: `parabolicDynamic` (`Absolute/ParabolicDynamicProof`).

**D6. Supplied parabolic quotients are proper.** Source: Milne 2017, Definition 17.15 and
Theorem 17.16, printed p.356 (PDF 372), and A.75–A.76, printed p.583 (PDF 599).
- Lean: `ParabolicSubgroupQuotientProperStatement` (`HomogeneousQuotientStatement`).
  Hypotheses: any field `k`; `G` smooth, with affine structure map and connected; a
  parabolic `i`; and a supplied `Q`, `q` with the hypotheses of A4 for `range i`.
  Conclusion: `Q` is proper.
- Status P: `parabolicSubgroupQuotientProper` (`ParabolicQuotientProperProof`).

**D7. The absolute Bruhat covering.** Source: Borel–Tits 1965, §2.4, p.65.
- Lean: `AbsoluteBruhatCoveringStatement` (`Absolute/BruhatCoveringStatement`). Hypotheses:
  `k` algebraically closed, `G` connected reductive, and a Borel pair `(i, j)`. Conclusion
  (`BorelTorusBruhatCovering i j`): every `g ∈ G(k)` is `b₁ n b₂` with `b₁, b₂ ∈ B(k)` and
  `n` a `k`-point normalizing `T`.
- Scope: only the covering. The disjointness of the double cosets is not stated.
- Status P: `absoluteBruhatCovering` (`Absolute/BruhatCoveringProof`).

## E. The determinant of `Ad` on `Lie U(χ)`

In E1–E3, `P`, `M`, `U` are arbitrary closed subgroups representing `P(χ)`, `Z(χ)` and
`U(χ)` of a connected reductive field group `G`.

**E1. Structure of the represented dynamic subgroups.** Source: CGP, §2.1, printed
pp.52–54 (PDF 78–80).
- Lean: `DynamicAdjointDeterminantStructureStatement` (`Dynamic/AdjointDeterminantStructureStatement`).
  Conclusion: `P`, `M`, `U` have affine structure maps, are closed, smooth and locally of
  finite type; `Lie(U)(k)` is finite-dimensional; and finite Lie coordinates on `U` exist.
- Status P: `dynamicAdjointDeterminantStructure` (`Dynamic/AdjointDeterminantStructureProof`).

**E2. The adjoint determinant characters.** Source: CGP, §2.1, printed pp.52–54 (PDF 78–80),
and §A.7, formula (A.7.2), printed pp.529–530 (PDF 555–556). Motivating: Renard 2026,
§V.3.1–V.3.4, printed p.110 (PDF 116).
- Lean: `DynamicAdjointDeterminantExistenceStatement` (`Dynamic/AdjointDeterminantExistenceStatement`).
  Conclusion: Lie coordinates `c` of `U` of some dimension `d`; the matrix representation
  `ρ` of `P` on `Lie U` given by the differential of the adjoint action; rational
  characters `δP` of `P` and `δM = δP|_M` of `M`; and, on points over every `k`-algebra
  `A`, `δP(p) = det(Ad(p) | Lie U ⊗ A)` and `δM(m) = det(Ad(m) | Lie U ⊗ A)`.
- Status P: `dynamicAdjointDeterminantExistence` (`Dynamic/AdjointDeterminantExistenceProof`).

**E3. Reciprocity for opposite cocharacters.** Derived; its statement Markdown explains the
derivation from CGP, Lemma 2.1.5, printed p.50 (PDF 76), and Proposition 2.1.8(1), printed
p.53 (PDF 79). Neither source states it.
- Lean: `Dynamic.LeviAdjointDeterminantReciprocityStatement`
  (`Dynamic/LeviAdjointDeterminantReciprocityStatement`). Hypotheses: a field `k`, `G`
  connected reductive, a maximal split torus `i : T ⟶ G`, a cocharacter `ζ` of `T`, one
  closed subgroup with affine underlying scheme representing both `Z(ζ)` and `Z(−ζ)`,
  representatives of `U(ζ)` and `U(−ζ)` with affine structure maps, and Lie coordinates on
  both. Conclusion: the two determinant characters of `Z(ζ)`
  on `Lie U(ζ)` and on `Lie U(−ζ)` sum to zero.
- Status C: `leviAdjointDeterminantReciprocity_of_structure relativeRootReflectionExistence
  centralSplitTorusCharacter dynamicCentralizerReductive`
  (`Dynamic/LeviAdjointDeterminantReciprocityReduction`, `Rational/RootReflectionExistenceProof`,
  `Rational/CentralSplitTorusCharacterProof`, `Dynamic/CentralizerReductiveProof`).
- No owner task was found. The statement is an input of published reductions used by Task
  `c0fa1878-6cee-4435-8484-2fc15ea04a17`.

## F. Internal interfaces

These are published internal proof targets with no source assertion of their own. The
first two are closed by published helper theorems in their own modules; only named wrapper
theorems are missing. The third is open.

- `AbsoluteBorelOvergroupRootInversionStatement` (`Absolute/BorelOvergroupRootInversion`).
  Hypotheses: `k` algebraically closed, `G` connected reductive, split maximal torus `j`,
  a smooth connected closed overgroup `i : P ⟶ G` of `j`, and a root `α` with `α` and `−α`
  both in the weight support of `P`. Conclusion: a relative Weyl element sending `α` to
  `−α` and preserving that weight support. Status C: the published theorem
  `Langlands.GroupScheme.AbsoluteBorelOvergroup.exists_supportPreserving_weylInverter_of_both_signs`
  (same module) has exactly these hypotheses and this conclusion; introducing the
  hypotheses and applying it type-checks, with standard axioms. Owner task: none needed.
- `AbsoluteBorelOvergroupRankOneContainmentStatement` (`Absolute/BorelOvergroupRankOne`).
  Hypotheses: as above but over any field. Conclusion: the dynamic centralizer of the
  rank-one cocharacter of `α` lies in `P`. Status C: the published theorem
  `Langlands.GroupScheme.AbsoluteBorelOvergroup.rankOneCentralizer_le_range_of_both_signs`
  (same module), applied in the same way. Owner task: none needed.
- `TriangularDiagonalKernelTowerStatement` (`Absolute/TriangularDiagonalKernelTowerStatement`).
  Source: Milne 2022, Theorem 16.21, printed p.330 (PDF 341), as a quotient-oriented
  reformulation. Hypotheses: a field `k`; `H` with affine and locally finite type
  structure map; a closed subgroup `j` of the upper triangular block parabolic of `GL_N`,
  with diagonal projection `f : H → L`; a finitely generated `Λ`; and `f = q ≫ d` with
  `d : D(Λ) → L` a closed subgroup and `q` an fppf quotient by the kernel of `f`.
  Conclusion: `q` admits a finite character-linear kernel tower. No smoothness,
  connectedness or splitting is assumed. Status O.

## Remaining targets in family 4

- O row: the third internal interface of F (`TriangularDiagonalKernelTowerStatement`). No
  owner task was found.
- C rows: C11 (owner Task 4665, whose contract excludes the composite route), C13 and E3
  (no owner task), the five components of C12, and the first two internal interfaces of F
  (named wrappers only, no task needed).
- Scope differences recorded above: A6 (point form of the normalizer theorem), A10 (no
  `P = N_G(P)`), A11 (existence half only), B7 (algebraically closed, no Lie comparison),
  D7 (covering only).

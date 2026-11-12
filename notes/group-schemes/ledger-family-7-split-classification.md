# Group-scheme ledger, family 7: split realization and classification

Author: Worker 3483, 9 November 2026, for the algebraic and reductive group-scheme program
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e` (Task 3483). This note is the source-to-declaration
ledger for family 7 of that program's contract. Family 7 covers:

- realization of split reductive groups by finite root data;
- the isomorphism and central isogeny theorems over fields;
- the semisimplicity criterion read off the root datum;
- the rank-one inputs;
- pinnings;
- the Steinberg data used in positive characteristic;
- Chevalley groups and integral models.

It describes Library commit `18a1f10aef8ea135d90e8474439a5e6d9c130008` and environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`. All Lean names are in `Langlands.GroupScheme`
unless a namespace is shown. Module paths are relative to `Langlands/GroupScheme/` in that
commit.

## Status codes and evidence

Each row gives the source assertion with its locator, the exact Lean statement and its
hypotheses, a status, the evidence, and the owner task.

- **P (published proof).** The Library at the commit above contains a theorem whose type is
  exactly the statement. The evidence is that theorem and its module path. The author also
  type-checked `example : S := proof` for every P row in a private module. That check
  passed with no errors or warnings, but it is not public evidence. Owner task: none open.
- **C (composite, not published).** No published theorem has the statement as its type.
  However, a term built only from published theorems has that type: the author type-checked
  it in the same private module, and its axioms are `propext`, `Classical.choice` and
  `Quot.sound`. The composite is not an accepted artifact. The owner task is the
  `lean.proof@1` task that should publish it.
- **S (staged).** A proof candidate is staged in the owner task. It is unreviewed and
  unpublished at this commit.
- **O (open).** No proof and no composite from published results is known.

Source locators use these registered sources. For Milne 2017 the PDF page is the printed
page plus 16. For Conrad 2014 the printed page equals the PDF page. For Getz–Hahn both
pages are given, because the offset changes in the appendix.

- `milne-2017-algebraic-groups`: J. S. Milne, *Algebraic Groups* (2017).
- `conrad-2014-reductive-group-schemes`: B. Conrad, *Reductive group schemes* (2014).
- `mumford-fogarty-kirwan-1994-git-3rd`: Mumford, Fogarty and Kirwan, *Geometric Invariant
  Theory*, 3rd enlarged edition (1994).
- `getz-hahn-2024-automorphic-representations`: Getz and Hahn, *An Introduction to
  Automorphic Representations* (2024).

## A. Classification over a field

**A1. Existence.** Source: Milne, Theorem 23.55, printed p.501 (PDF 517): every reduced
root datum arises from a split reductive group over `k`; over every field also Theorem
23.74, printed p.511 (PDF 527).
- Lean: `SplitReductiveExistenceStatement` (`Reductive/SplitClassificationStatement`).
  Hypotheses: a field `k : Type u`, a finite index type `J`, a finitely generated
  `ℤ`-module `X`, a commutative group `Y`, and a reduced `P : RootDatum J X Y`.
  Conclusion: a connected reductive `G` over `Spec k` and a split torus `T` with a maximal
  torus `i : T ⟶ G`. Further, `i` has a root datum `Q` and `Nonempty (RootPairing.Equiv P Q)`.
- Status P: `splitReductiveExistence` (`Reductive/SplitExistence`). The proof builds the
  group over each field from Chevalley data (`SplitExistence/`). It does not build a group
  scheme over `ℤ` (see G1).

**A2. Isomorphism theorem, common torus.** Source: Milne, Theorem 23.25 and Remark 23.26,
printed pp.492–493 (PDF 508–509), isomorphism case.
- Lean: `SplitCommonTorusIsomorphismStatement` (`Reductive/SplitIsomorphismStatement`).
  Hypotheses:
  - connected reductive `G₁`, `G₂` over a field, with maximal tori `i₁ : T ⟶ G₁` and
    `i₂ : T ⟶ G₂` from the same split torus `T`;
  - root data `P₁` of `i₁` and `P₂` of `i₂`, indexed by `J₁` and `J₂`;
  - a reindexing `e : J₁ ≃ J₂` with `P₂.root ∘ e = P₁.root` and
    `P₂.coroot ∘ e = P₁.coroot`.

  Conclusion: some `ψ : G₁ ≅ G₂` has `i₁ ≫ ψ.hom = i₂`.
- Scope differences: the Lean statement covers only the identity of the common character
  lattice, and only existence. Milne's theorem covers any isomorphism of root data, and
  determines the group isomorphism up to an inner automorphism by an element of
  `(T/Z)(k)`. That uniqueness clause has no Lean statement in this form. Its pinned
  counterparts are E3 (uniqueness of pinned isomorphisms), E4 and E5.
- Status P: `splitCommonTorusIsomorphism` (`Reductive/SplitIsomorphismProof`).

**A3. Gluing step.** Source: Milne 23.16–23.18, printed pp.490–491 (PDF 506–507): the graph
argument extending the rank-one isomorphisms.
- Lean: `SplitCommonTorusLeviGluingStatement` (`Reductive/SplitLeviGluingStatement`).
  Hypotheses: those of A2, plus a hypothesis on cocharacters `ν` of `T` such that any two
  roots of `i₁` vanishing on `ν` are `ℤ`-dependent. For every such `ν`, closed subgroups
  `z₁ : Z₁ ⟶ G₁` and `z₂ : Z₂ ⟶ G₂` representing the dynamic centralizers of `ν ≫ i₁` and
  `ν ≫ i₂`, with `t₁ ≫ z₁ = i₁` and `t₂ ≫ z₂ = i₂`, admit `φ : Z₁ ≅ Z₂` with
  `t₁ ≫ φ.hom = t₂`. Conclusion: as in A2.
- Status P: `splitCommonTorusLeviGluing` (`Reductive/SplitIsomorphismProof`).

**A4. Semisimple rank at most one.** Source: Milne, Proposition 23.14, printed p.489
(PDF 505), isomorphism case.
- Lean: `SplitRankOneCommonTorusIsomorphismStatement` (`Reductive/SplitRankOneIsomorphismStatement`).
  Hypotheses: those of A2, plus: any two roots of `i₁` are linearly dependent over `ℤ`.
  Conclusion: as in A2.
- Status P: `splitRankOneCommonTorusIsomorphism` (`Reductive/SplitRankOneIsomorphismProof`),
  obtained from C1 by `splitRankOneCommonTorusIsomorphism_of_rootCell`.

**A5. Isogeny theorem, central case.** Source: Milne, Theorem 23.9 with Definitions 23.1–23.2
and Proposition 23.5, printed pp.483–487 (PDF 499–503).
- Lean: `SplitCentralIsogenyExistenceStatement` (`Reductive/SplitClassificationStatement`).
  Hypotheses:
  - connected reductive `G`, `G'` over a field, with split maximal tori `i : T ⟶ G` and
    `i' : T' ⟶ G'`;
  - root data `P` of `i` and `P'` of `i'`;
  - a morphism of root pairings `f : P' ⟶ P` whose weight map and coweight map are both
    injective.

  Conclusion: `φ : G ⟶ G'` and `t : T ⟶ T'` with `i ≫ φ = t ≫ i'` and `f χ = t ≫ χ` for all
  characters `χ` of `T'`, and `IsCentralIsogeny φ`.
- Scope differences: only central isogenies, and only existence. Milne's Theorem 23.25
  also covers non-central isogenies, with exponents `q(α)` in positive characteristic, and
  a uniqueness clause up to `(T'/Z')(k)`. Neither has a Lean statement in this form.
- Status P: `splitCentralIsogenyExistence` (`Reductive/SplitCentralIsogenyExistenceProof`).

## B. Semisimplicity from the root datum

**B1. Both forms of the criterion.** Source: Milne, Proposition 21.48 with Definition C.34,
and the dual form in the proof of Proposition 21.49(a), printed p.439 (PDF 455).
- Lean: `SplitSemisimpleRootDatumStatement` (`Reductive/SplitClassificationStatement`).
  Hypotheses: a connected reductive `G` over a field, a split maximal torus `i : T ⟶ G`,
  and a root datum `P` of `i`. Conclusion: `IsSemisimple G` holds iff the roots span a
  subgroup of finite index in `X*(T)`, and iff the coroots span a subgroup of finite index
  in `X_*(T)`.
- Status P: `splitSemisimpleRootDatum` (`Reductive/SplitSemisimplicity`), through
  `maximalTorusCentralizer` (`Absolute/MaximalTorusCentralizerProof`).

**B2. Root form, and its "if" half.** Same source.
- Lean: `SplitSemisimpleRootSpanStatement` (`Reductive/SplitSemisimpleRootSpanReduction`),
  which is the first conjunct of B1. Also `SplitSemisimpleOfFiniteRootIndexStatement`
  (`Reductive/SplitSemisimpleRootSpanNecessity`): if the roots span a subgroup of finite
  index, then `G` is semisimple. Hypotheses: as in B1.
- These are consequences of B1, so the published proof of B1 already covers their
  mathematics. What is missing is only a published theorem with each exact type.
- Status C: `splitSemisimpleOfFiniteRootIndex_of_maximalTorusCentralizer
  maximalTorusCentralizer`, then `splitSemisimpleRootSpan_of_finiteRootIndex`.
  Owner: Task 5311, `51f00513-0c90-4a4b-8725-dcfdc90c167c`.

## C. Rank-one inputs

**C1. Root groups, open cell and the rank-one relation.** Source: Conrad, Theorem 4.1.4,
p.110; Remark 4.2.4, p.119; Theorem 4.2.6, pp.120–121.
- Lean: `SplitRankOneRootCellStatement` (`Reductive/SplitRankOneRootCellStatement`).
  Hypotheses: a connected reductive `G` over a field, a split maximal torus `i`, a root
  datum `P` of `i`, and any two roots `ℤ`-dependent (semisimple rank at most one). For each
  root index `r`, the conclusion gives `xp xm : 𝔾ₐ ⟶ G` with these properties:
  - `T` acts on `xp` through `α = P.root r` and on `xm` through `-α`;
  - `(Y, t, X) ↦ xm(Y) t xp(X)` is an open immersion;
  - on every test scheme, `xp(X) xm(Y)` lies in that cell iff `1 + XY` is a unit;
  - for `u = 1 + XY` a unit, `xp(X) xm(Y) = xm(u⁻¹Y) α^∨(u) xp(u⁻¹X)`.
- Status P: `splitRankOneRootCell` (`Reductive/SplitRankOneRootCellProof`).

**C2. Weyl criterion for reductivity in rank one.** Source: Conrad, proof of Proposition
3.1.9, pp.87–88, including Lemma 3.1.10.
- Lean: `RankOneWeylReductivityStatement` (`Reductive/RankOneWeylCriterionStatement`).
  Hypotheses:
  - an algebraically closed field `k`;
  - `G` smooth, affine and connected;
  - a split subtorus `i : T ⟶ G` with `torusCentralizer i = range i`;
  - a nonzero character `α` such that the roots of `i` are exactly `α` and `-α`, both with
    one-dimensional weight spaces;
  - an automorphism `c` of `T` with `c ≫ α = -α`, and a `k`-point `n` of `G` that
    transports `c ≫ i` to `i`.

  Conclusion: `G` is connected reductive.
- This is an input to the reductivity-locus argument. It does not assume a reductive `G`,
  unlike C1.
- Status P: `rankOneWeylReductivity` (`Reductive/RankOneWeylCriterionProof`).

## D. Split unipotent products (cross-listed with family 3)

**D1.** Source: Milne §16.g, printed p.343 (PDF 359): quotients and extensions of split
solvable groups are split. Milne warns there that normal subgroups of split groups need not
be split.
- Lean: `SplitNormalFppfProductStatement` (`Reductive/SplitNormalFppfProductStatement`).
  Hypotheses:
  - a field `k` and `G` affine and locally of finite type over `Spec k`;
  - closed subgroups `i : H ⟶ G` and `j : N ⟶ G`, each smooth, connected, with normal
    range, and split unipotent (`RelativeRoot.IsSplitUnipotent`);
  - a smooth connected `P` with `p : P ⟶ G` representing the fppf product of the two
    ranges (`SubgroupFunctor.IsFppfProduct`).

  Conclusion: `P` is split unipotent.
- The fppf product is a hypothesis. The statement neither constructs the product nor
  classifies normal subgroups of split groups.
- Status P: `SplitNormalFppfProduct.splitNormalFppfProduct` (`Reductive/SplitNormalFppfProductProof`).

## E. Pinnings

Conrad, Definition 6.1.1, p.186, defines a pinning: a base `Δ` with trivializing sections of
the simple root spaces. `SplitPinning G` (`Reductive/Pinning`) packages it over a field with
the following data:
- a split maximal torus of a connected reductive `G`;
- a finite reduced root datum on its actual lattices;
- a base;
- simple-root Lie trivializations.

**E1. Root pinnings for every base.** Source: Conrad, §5.1 and Definition 5.1.1, p.136;
Definition 6.1.1, p.186.
- Lean: `RootPinningExistenceStatement` (`Reductive/PinningExistenceStatement`).
  Hypotheses: a connected reductive `G` over a field, a split maximal torus `i`, a root
  datum `P` of `i`, and a base `b` of `P`. Conclusion: `Nonempty (RootPinning i P b)`.
- Status P: `rootPinningExistence` (`Reductive/RootPinningFromSplitTorus`).

**E2. A pinning exists.** Same source.
- Lean: `SplitPinningExistenceStatement` (`Reductive/PinningExistenceStatement`).
  Hypotheses: a connected reductive `G` over a field with a split maximal torus.
  Conclusion: `Nonempty (SplitPinning G)`.
- Status C: `splitPinningExistence_of_rootDatumExistence rootDatumExistence`
  (`Reductive/RootPinningFromSplitTorus`, `Reductive/RootDatumExistence`). Owner: Task
  5242, `043f2527-205c-4cfc-b9b2-553de1010d9d`.

**E3. Isomorphism theorem for pinned groups (full faithfulness).** Source: Conrad, Theorem
6.1.17, p.197; Corollary 6.1.15, p.195.
- Lean: `PinnedIsomorphismStatement` (`Reductive/PinnedIsomorphismStatement`). Hypotheses:
  - a field `k` and affine `G`, `H` over `Spec k` with pinnings `p`, `q`;
  - an equivalence `e` of their root data that maps the base of `p` onto the base of `q`.

  Conclusion: a unique pinned isomorphism `f` with character map `e.weightEquiv`,
  cocharacter map `e.coweightEquiv.symm` and index map `e.indexEquiv`.
- Scope difference: over a field only. Conrad states the equivalence over any non-empty
  base scheme.
- Status P: `pinnedIsomorphism` (`Reductive/PinnedIsomorphismProof`).

**E4. Scaling simple-root vectors.** Source: Conrad, proof of Corollary 6.1.15, pp.195–196.
- Lean: `PinnedRootScalingStatement` (`Reductive/PinnedRootScalingStatement`). Hypotheses:
  an affine `G` over a field, a pinning `p`, and units `c a` for the simple roots `a`.
  Conclusion: an automorphism of `G` that is the identity on the pinned torus and
  multiplies each simple-root vector by `c a`.
- Status P: `pinnedRootScaling` (`Reductive/PinnedRootScalingProof`).

**E5. Rigidity of pinned automorphisms.** Source: Conrad, Proposition 6.1.13(2), p.194;
Corollary 6.1.15, p.195.
- Lean: `PinnedAutomorphismRigidityStatement` (`Reductive/PinnedRigidityStatement`).
  Hypotheses: an affine `G` over a field, a pinning `p`, and an automorphism that is the
  identity on the pinned torus and fixes every simple-root vector. Conclusion: it is the
  identity.
- Status P: `pinnedAutomorphismRigidity` (`Reductive/PinnedRigidityProof`).

## F. Steinberg data in positive characteristic

These three statements are internal interfaces for Haboush's theorem. They reconstruct the
proof sketch of Mumford–Fogarty–Kirwan, Appendix to Chapter 1, §A, Theorem A.1.0
(a)⇒(b), printed p.192. That page cites Steinberg for the irreducibility of the module
`H⁰(G/B, L((p^s − 1)ρ))` and its self-duality. It does not state the big-cell conditions.
Conditions 1–6 of `SteinbergBigCellStatement` and parts of the exhaustion interface are
the implementer's reconstruction, as the statement Markdown files explain.

All three statements have the same scope:
- `k` algebraically closed of prime characteristic `p`;
- `G` with `IsSimplyConnected G`, which includes semisimplicity;
- `[IsAffineHom G.X.hom]` for F1 and F2, and `[IsAffine G.X.left]` for F3.

**F1. Big cell and Steinberg data.** Lean: `SteinbergBigCellStatement`
(`Reductive/SteinbergBigCellStatement`).
- Status C: `steinbergBigCell_of_rootAndCoroot rootDatumExistence
  splitSimplyConnectedCorootSpan` (`Reductive/SteinbergBigCellRootCorootAssembly`,
  `SimplyConnected/SplitNecessity`).
- Status S: candidate `1bd99426-1a83-4e16-a31c-9d09bebecf5d` in the owner task, Task 4716,
  `2d982376-401c-4c21-917d-ba42fd70af17`.

**F2. Covariant exhaustion.** Lean: `SteinbergCovariantExhaustionStatement`
(`Reductive/SteinbergCovariantExhaustionStatement`).
- Status C: `steinbergCovariantExhaustion_of_bigCell` (`Reductive/SteinbergBigCellReduction`)
  applied to the F1 composite. Owner: Task 5311, `51f00513-0c90-4a4b-8725-dcfdc90c167c`.

**F3. Tensor embedding.** Lean: `SteinbergTensorEmbeddingStatement`
(`Reductive/SteinbergTensorEmbeddingStatement`).
- Status C: `steinbergTensorEmbedding_of_covariantExhaustion`
  (`Reductive/SteinbergCovariantReduction`) applied to the F2 composite. Owner: Task 5311.

The two consumers below belong to families 3 and 6. They are listed because their status
follows from F1:
- `SimplyConnectedPositiveCharConjugationMapStatement` is C, by
  `simplyConnectedPositiveCharConjugationMap_of_bigCell`. Task 4587,
  `3346aae1-d026-4f7f-9956-6cb65f0b6866`, has the staged candidate
  `a250029c-35dc-493c-8f90-0a4c60509071`.
- Haboush's theorem `ReductiveGeometricReductivityStatement` is C, by
  `reductiveGeometricReductivity_of_structural_inputs` applied to four inputs:
  - `reductiveCentralDerivedProduct`;
  - the composite for `SimplyConnectedDerivedCoverExistenceStatement`, from
    `derivedSubgroupRepresentability`, `derivedSubgroupSemisimple` and
    `simplyConnectedCoverExistence`;
  - the conjugation-map composite;
  - `reductiveCharZeroSemisimplicityStatement`.

  Owners: Task 4404, `db7e7723-dab1-43d9-8fdc-755e40c61351` (staged candidate
  `fe21742d-ff3e-4c84-8dfd-5504fe2f7896`), and Task 4073,
  `a75c8252-e54b-46f2-8dba-0b41d9e4fba2`, for the derived cover (staged candidate
  `9d9b31d2-1b0a-40c4-bef4-77d57e686b42`).

## G. Chevalley groups and integral models

**G1. Chevalley groups over `ℤ`.** No group scheme over `ℤ` attached to a general root
datum exists in the Library at this commit, and no task for one was found. A TaskHub
search for "Chevalley group scheme over Z" returned nothing. The modules under
`SplitExistence/` construct groups over each field from Chevalley data. They also prove
that a reduced root datum has a base over `ℤ` (`SplitExistence/IntegralBase`). Status O.

**G2. Simultaneous reductive and parabolic spreading.** Source: Getz–Hahn, Proposition
2.4.8, printed p.61 (PDF 78), and Proposition B.3.1, printed p.544 (PDF 549). The Lean
statement packages both, and adds conditions on the base change to every field over the
base ring. Those conditions go beyond the two cited propositions.
- Lean: `IntegralModel.ReductiveParabolicSpreading.ExistenceStatement`
  (`IntegralModel/ReductiveParabolicSpreadingStatement`). Hypotheses: a number field `F`, a
  connected reductive `G` over `Spec F`, and a parabolic `p : P ⟶ G`. Conclusion: a finite
  set `S` of finite places and `ModelData` over the `S`-integers. The `ModelData` consist
  of the following:
  - models of `G` and `P`;
  - a closed-immersion model of `p`;
  - a reductive ambient model and a smooth parabolic model;
  - connected reductive, parabolic and connected base changes to every field over the
    base ring.
- Status C: `existenceStatement_of_spreadingStatements genericReductivitySpreading
  parabolicDynamic` (`IntegralModel/ConditionalReductiveParabolicSpreading`,
  `Reductive/GenericSpreadingProof`, `Absolute/ParabolicDynamicProof`). Owner: Task 4668,
  `8b53f86e-c91d-47ab-b631-e30de865fbbe`, which has no executor at this writing.

**G3. Maximal compactness of model points.** Source: Getz–Hahn, Theorem 2.4.3, final
assertion, printed p.59 (PDF 76): if a model of `G` over `𝒪_F` has reductive special
fibre, its `𝒪_F`-points form a maximal compact subgroup of `G(F)`.
- Lean: `IntegralModel.MaximalCompactStatement` (`IntegralModel/MaximalCompactStatement`).
  Hypotheses: a non-archimedean local field `F`, a connected reductive `G` over `Spec F`,
  and an integral model `M` over `𝒪_F` whose special fibre is connected reductive.
  Conclusion: `M(𝒪_F)` is compact and is a maximal compact subgroup of `G(F)`.
- Status O. The published `maximalCompactStatement_of_buildingComparison`
  (`IntegralModel/BuildingComparison`) reduces it to `BuildingComparisonStatement`, which
  is also O. Owners: Task `21033437-c908-4d4f-bf9a-06d1f642447a` (maximal compactness)
  and Task `e93a1c4a-39d9-440a-b41f-f3071783e6e4` (building comparison).

## Conventions and scope

- Milne states classification for split reductive pairs `(G, T)`. The Library states each
  theorem with an explicit split maximal torus `i : T ⟶ G` and a root datum satisfying
  `IsRootDatumOf i P`, over an arbitrary field `k : Type u`.
- Root-datum classification is a theorem in the Library. It is not the definition of a
  reductive group, as the contract requires.
- The isomorphism rows A2–A4 identify root data on a common torus by matching roots and
  coroots. A row for an arbitrary isomorphism of root data between different tori would
  need a transport along a torus isomorphism. No such statement exists at this commit.
- Relative versions belong to family 8. These include the isomorphism theorem over a local
  ring, `LocalSplitIsomorphismTheoremStatement`, and the other statements in
  `Reductive/LocalSplit*`.

## Remaining open targets in family 7

- The non-central isogeny theorem and the unpinned uniqueness clauses of Milne
  23.25–23.26: no Lean statement.
- An isomorphism theorem for arbitrary root-datum isomorphisms between different tori: no
  Lean statement.
- Chevalley group schemes over `ℤ` and their base change (G1).
- `IntegralModel.MaximalCompactStatement` and `IntegralModel.BuildingComparisonStatement`
  (G3).
- Publication of the C rows (B2, E2, F1–F3, G2) by their owner tasks.

# Group-scheme ledger, family 8: relative structure over general bases

For the dynamic statement publications and proof owners as of 13 November
2026, see [the dated dynamic update](dynamic-relative-progress.md).
It updates rows D2 and F1–F2; the labels below describe the original snapshot.

Author: Worker 3483, 10 November 2026, for the algebraic and reductive group-scheme program
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e` (Task 3483). This note is the source-to-declaration
ledger for family 8 of that program's contract. Family 8 covers:

- reductive group schemes over a base, fibrewise criteria and base change;
- relative identity components;
- relative tori, maximal tori over local bases, and Hom schemes;
- local splitting, root data over a base and the isomorphism theorem;
- relative parabolic subgroups, their normalizers and quotients, and relative Levi
  subgroups;
- descent, and the general-base dynamic constructions, including smoothness over a ring and
  the scheme-level decomposition `P(λ) ≅ U(λ) × Z(λ)`.

It describes Library commit `f2c5495316f5a5631bc8c11875b7509d93271fe5` and environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`. Lean names are in `Langlands.GroupScheme` unless a
namespace is shown. Module paths are relative to `Langlands/GroupScheme/` unless they start
with `Langlands/`.

The rows list the principal source assertions of this family. Auxiliary declarations used
inside proofs are not listed one by one, and leaving one out says nothing about its status.
Integral models over rings of `S`-integers, parahoric models and maximal compact subgroups
are listed in the published family-7 ledger
[ledger-family-7-split-classification.md](ledger-family-7-split-classification.md) and are
not repeated here. No row asserts a global choice of a split maximal torus or of a root
datum over an arbitrary base: such data are supplied, or exist over local or strictly
henselian local rings, as each row states.

## Status codes and evidence

Each row gives the source assertion with its locator, the exact Lean statement and its
hypotheses, a status, the evidence, and the owner task.

- **D (definition or internal result).** A published construction, or a published theorem
  that is not a closed proposition (for instance a theorem with hypotheses). The evidence is
  its module path. No owner task is needed.
- **P (published proof).** The Library at the commit above contains a theorem whose type is
  exactly the statement. The evidence is that theorem and its module path. The author also
  type-checked `example : S := proof` for every P row in a private module. That check
  passed with no errors or warnings, and `#print axioms` reported only `propext`,
  `Classical.choice` and `Quot.sound`; it is not public evidence. No further proof work or
  owner task is needed.
- **C (composite, not published).** No published theorem has the statement as its type, but
  a projection out of a published conjunction has it. The author type-checked the
  projection in the same private module. What is missing is a named wrapper theorem, not
  mathematics.
- **O (open).** A Lean statement exists, but no published proof and no composite from
  published results is known.
- **M (missing statement).** A source assertion of this family has no closed Lean
  statement. The author searched the statement declarations of the Library by content (for
  the predicates involved), not only by name, before recording an M row.

The labels "accepted" and "published" are used only for artifacts that passed independent
review. A "staged" candidate has passed machine validation only.

Source locators use these registered sources, cited by source id:

- `conrad-2014-reductive-group-schemes`: B. Conrad, *Reductive group schemes* (2014).
  Printed page = PDF page.
- SGA 3, Exposé VI_B, Gille–Polo recomposed edition of 13 October 2024, retained in the
  project literature; PDF pages are given.
- SGA 3, Exposé XI, Gille–Polo provisional recomposition of December 2008, file
  `Expo11.pdf`; PDF pages are given.
- `prasad-yu-2006-quasi-reductive-author-preprint`: G. Prasad and J.-K. Yu, *On
  quasi-reductive group schemes*, author preprint; PDF pages are given.
- `milne-2017-algebraic-groups`: J. S. Milne, *Algebraic Groups* (2017). PDF page = printed
  page + 16.
- `conrad-gabber-prasad-2015-pseudo-reductive`: B. Conrad, O. Gabber and G. Prasad,
  *Pseudo-reductive groups*, 2nd edition (2015). PDF page = printed page + 26.

The author re-read every locator below in the original source for this note, on 10 November
2026, and checked that the cited item is on the cited page.

## A. Definitions and general-base constructions

All rows are D.

- `IsReductive G` (`Reductive/Basic`), for `G` over any scheme `S`: `G` is smooth with affine
  structure map, and every geometric fibre `geometricFiber G s` (the base change to an
  algebraic closure of the residue field at `s`) is pseudo-reductive, hence connected
  reductive since the field is algebraically closed. Source: Conrad 2014, Definition 3.1.1,
  p.81.
- `RelativeTorus.IsTorus G` (`Torus/Relative`): `G` becomes a split torus on the members of
  some étale cover of `S`.
- `IsRelativeIdentityComponent G i` (`RelativeIdentityComponent`): `i` is an open immersion
  whose points, on every test scheme, are exactly the points of `G` lying fibrewise in the
  identity components. Source: SGA 3 VI_B, Définition 3.1, PDF p.17.
- `IsCentralIsogeny` (`CentralIsogeny/Basic`), over any base. Source: Conrad 2014, Definition
  3.3.9, p.103; Milne 2017, Definition 18.1, printed p.387 (PDF 403).
- Dynamic subgroups over any base. `Dynamic.parabolic_baseChange`,
  `Dynamic.centralizer_baseChange` and `Dynamic.unipotent_baseChange` (`Dynamic/BaseChange`):
  for any morphism of base schemes, `P(λ)`, `Z(λ)` and `U(λ)` commute with base change, with no
  hypothesis on `G`. Source: Conrad 2014, p.114, the paragraph after Example 4.1.9.
  `Dynamic.unipotent_isNormalizedBy_parabolic` and `Dynamic.isComplement'_unipotent_centralizer`
  (`Dynamic/Decomposition`): over any base, `U(λ)` is normalized by `P(λ)`, and if limits are
  unique and lie in `Z(λ)` then on every test scheme the points of `P(λ)` are uniquely
  products of points of `U(λ)` and `Z(λ)`. `Dynamic.Affine.parabolicHom` with
  `Dynamic.Affine.isRepresentedBy_parabolicHom` and
  `Dynamic.Affine.isClosedSubgroup_parabolicHom` (`Dynamic/AffineRepresentability`), and the
  same for `Z` and `U`: for `G` with affine underlying scheme over `Spec R`, `R` any
  commutative ring, the three functors are represented by closed subgroups. Source: Conrad
  2014, Theorem 4.1.7, pp.112–113, the representability part. Smoothness over a ring and the
  scheme-level decomposition over any base are rows F1 and F2 below. Transport and fpqc
  reflection of the dynamic subgroups are recorded in the published note
  [transport-dynamic-progress.md](transport-dynamic-progress.md). That note lists dynamic
  smoothness only over fields and calls unrestricted-base smoothness remaining; it does not
  mention `dynamicSmooth_ring`, which proves smoothness over every affine base (F1). Over a
  non-affine base the remaining-work entry of that note still applies.

## B. Fibrewise criteria, identity components and normalizers

**B1. The reductive locus is open.** Source: Conrad 2014, Proposition 3.1.9(1), pp.85–88.
- Lean: `IdentityComponentReductiveLocusOpenStatement` (`Reductive/IdentityComponentLocus`).
  Hypotheses: any scheme `S`; `G` smooth with affine structure map. Conclusion: the locus of
  points of `S` whose fibre has connected reductive identity component is open.
- Status P: `identityComponentReductiveLocusOpen` (`Reductive/IdentityComponentLocusProof`).

**B2. Spreading out reductivity from the generic fibre.** Source: Conrad 2014, Proposition
3.1.9(1), pp.85–88, and Proposition 3.1.12, pp.89–90.
- Lean: `GenericReductivitySpreadingStatement` (`Reductive/GenericSpreadingStatement`).
  Hypotheses: a **noetherian domain** `R` with a supplied fraction field `K`; a **supplied**
  `G` over `R`, smooth with affine structure map, whose base change to `K` is connected
  reductive. Conclusion: some `r ≠ 0` in `R` such that the base change of `G` to every field
  `k` over `R` in which `r` is nonzero is connected reductive.
- Status P: `genericReductivitySpreading` (`Reductive/GenericSpreadingProof`).

**B3. The relative identity component.** Source: SGA 3 VI_B, Définition 3.1 and Proposition
3.3, PDF p.17, and Théorème 3.10, PDF pp.20–21.
- `RelativeIdentityComponent.SmoothStructureStatement` (`RelativeIdentityComponentStatements`),
  the conjunction of the three statements below, for every scheme `S` and every smooth
  group `G` over `S`. Status P: `RelativeIdentityComponent.smoothStructure`
  (`RelativeIdentityComponent/SmoothProof`).
- `SmoothExistenceStatement`: a relative identity component `i : H ⟶ G` exists, with `H`
  smooth and with geometrically connected fibres. Status C: `smoothStructure.1`.
- `SmoothNormalityStatement`: every relative identity component is normal on all test
  schemes. Status C: `smoothStructure.2.1`.
- `SmoothBaseChangeStatement`: the base change of a relative identity component along any
  morphism `S' ⟶ S` is a relative identity component. Status C: `smoothStructure.2.2`.
- Owner task for the three C rows: none; they are named wrappers only.

**B4. Identity components over a discrete valuation ring are affine.** Source: Prasad–Yu,
§3.5, Lemma, author-preprint PDF pp.6–7.
- Lean: `RelativeIdentityComponent.SmoothDvrAffinenessStatement`
  (`RelativeIdentityComponentDvrAffinenessStatement`). Hypotheses: a discrete valuation ring
  `R`; `G` smooth with affine structure map; a relative identity component `H`. Conclusion:
  `H` has affine structure map.
- Status P: `RelativeIdentityComponent.smoothDvrAffineness`
  (`RelativeIdentityComponentDvrAffinenessProof`).

**B5. Self-normalizers are detected on field fibres.** Source: Conrad 2014, Proposition
2.1.6, pp.61–62, Lemma B.3.1, p.288, and the proof of Corollary 5.2.8, p.156.
- Lean: `RelativeSelfNormalizerStatement` (`RelativeSelfNormalizerStatement`). Hypotheses: any
  scheme `S`; `G` smooth with affine structure map; a closed subgroup `i : H ⟶ G` with `H`
  smooth and with geometrically connected fibres, whose base change to every field point of
  `S` is self-normalizing. Conclusion: `range i` is self-normalizing on all test schemes.
- Scope: this is the detection step only. It contains no parabolic hypothesis.
- Status P: `relativeSelfNormalizer` (`RelativeSelfNormalizerProof`).

**B6. Parabolic subgroups of reductive group schemes are self-normalizing.** Source: Conrad
2014, Corollary 5.2.8, pp.155–156, first assertion.
- D: `RelativeParabolicNormalizerReduction.normalizer_eq_of_statements`
  (`RelativeParabolicNormalizerReduction`): over `Spec R`, `R` any commutative ring, given
  `RelativeSelfNormalizerStatement`, `ParabolicSelfNormalizerStatement` and
  `ParabolicDynamicStatement` (all three have published proofs), `G` reductive, `P` smooth,
  `i : P ⟶ G` closed and parabolic after every base change to a field, the normalizer of
  `range i` is `range i`. Applying it to the published proofs gives the assertion for every
  such `i`.
- Status M for a closed proposition stating this. Owner task: none.

**B7. Proper ambient schemes for self-normalizing subgroups.** Source: Conrad 2014, Theorem
2.3.6(1), pp.72–74, with Proposition 2.1.6, pp.61–62.
- Lean: `SelfNormalizingProperAmbientStatement` (`SelfNormalizingProperAmbientStatement`).
  Hypotheses: a commutative ring `R`; `G` smooth with affine structure map and geometrically
  connected fibres; a closed subgroup `i : H ⟶ G`, `H` smooth with geometrically connected
  fibres, with `range i` self-normalizing. Conclusion: a proper scheme `Y` over `R`, locally
  of finite presentation, and `r : G → Y` whose fibres are exactly the cosets of `H` on every
  test scheme.
- Status P: `selfNormalizingProperAmbient` (`SelfNormalizingProperAmbientProof`).

**B8. Proper quotients by parabolic subgroups.** Source: Conrad 2014, Corollary 5.2.8,
pp.155–156, second assertion, with Theorem 2.3.6, pp.72–74, Definition 5.2.1, p.151, and
Proposition 5.2.3, p.152.
- Lean: `RelativeParabolicQuotient.ExistenceStatement` (`RelativeParabolicQuotientStatement`).
  Hypotheses: any commutative ring `R`; `G` reductive over `Spec R`; `P` smooth; `i : P ⟶ G` a
  closed immersion that is parabolic after every base change to a field. Conclusion: a proper
  scheme `Q` over `R` and `q : G → Q`, flat, surjective and quasi-compact, whose fibres are
  exactly the cosets of `P` on every test scheme.
- Status P: `Langlands.Global.IntegralIwasawaFamily.relativeParabolicQuotient`
  (`Langlands/Global/IntegralIwasawaFamilyReduction`). Its owner task, Task 4778
  (`97745234-6669-4471-92eb-334b88511721`), also has a staged candidate in a topic-local module.

## C. Relative tori, maximal tori over local bases, and Hom schemes

**C1. Lifting split tori from a fibre.** Source: Conrad 2014, Proposition 3.1.6, pp.83–84,
and Corollary 3.1.8, pp.84–85.
- Lean: `RelativeSplitTorusLiftingStatement` (`Torus/RelativeLiftingStatement`). Hypotheses:
  any scheme `S`; `G` smooth with affine structure map; a point `s` and a closed split torus
  `T₀` of the fibre at `s`. Conclusion: an étale neighbourhood `U → S` of `s` and a closed
  split torus of `G_U` whose fibre at `s` is `T₀`.
- Status P: `relativeSplitTorusLifting` (`Torus/RelativeLiftingProof`).

**C2. Split maximal tori over strictly henselian local rings.** Source: Conrad 2014,
Definition 3.2.1, p.91, Theorem 3.2.6 and Corollary 3.2.7, pp.94–95, and Proposition B.3.4,
pp.290–291.
- Lean: `StrictHenselianSplitMaximalTorusStatement` (`Torus/StrictHenselianMaximalStatement`).
  Hypotheses: a henselian local ring with separably closed residue field; `G` reductive.
  Conclusion: a closed split torus of `G` that is a maximal torus on every residue-field
  fibre.
- Status P: `strictHenselianSplitMaximalTorus` (`Torus/StrictHenselianMaximal`).

**C3. Maximality propagates from the closed fibre.** Source: internal.
- Lean: `LocalClosedFibreMaximalPropagationStatement` (`Torus/LocalMaximalPropagation`).
  Hypotheses: a local ring; `G` reductive; a closed split torus that is maximal on the closed
  fibre. Conclusion: it is maximal on every residue-field fibre.
- Status P: `localClosedFibreMaximalPropagation` (same module).

**C4. Étale-local existence and conjugacy of maximal tori.** Source: Conrad 2014, Theorem
3.2.6, p.94, and Corollary 3.2.7, p.95, over a general base.
- Status M for these étale-local statements over a general base; C2 is their strictly
  henselian consequence. Owner task: none.

**C5. Hom schemes and the scheme of subtori.** Source: SGA 3 XI, Théorème 4.1 and Corollaire
4.2, PDF p.20.
- `TorusSubgroupModuli.SmoothTorusSubgroupRepresentabilityStatement`
  (`HomScheme/SmoothTorusSubgroupRepresentabilityStatement`): for `G` smooth with affine
  structure map over any `S`, a smooth `M → S` with a universal closed subtorus
  (`RelativeTorus.IsTorus`). This is the torus case of Théorème 4.1. Status P:
  `TorusSubgroupModuli.smoothTorusSubgroupRepresentability`
  (`HomScheme/SmoothTorusSubgroupRepresentabilityProof`).
- `HomScheme.SmoothSplitSourceRepresentabilityStatement`
  (`HomScheme/SmoothSplitSourceRepresentabilityStatement`): for `H` a split torus and `G`
  smooth with affine structure map, `Hom(H, G)` is represented by a smooth `S`-scheme. This is
  Corollaire 4.2 for split tori. Status P: `HomScheme.smoothSplitSourceRepresentability`
  (`HomScheme/SmoothSplitSourceRepresentabilityProof`).
- `TorusSubgroupModuli.ChartCoverStatement`, `TorusSubgroupModuli.FiniteTypeChartCoverStatement`
  and `TorusSubgroupModuli.ChartGluingStatement` (`HomScheme/TorusSubgroupChartStatements`):
  open charts of the scheme of subtori covering all field points, over any `S` and over
  finite-type `ℤ`-algebras, and their gluing. Status P (namespace `TorusSubgroupModuli`):
  `chartCover` (`HomScheme/TorusSubgroupChartCoverProof`), `finiteTypeChartCover`
  (`HomScheme/SmoothTorusSubgroupRepresentabilityProof`), `chartGluing`
  (`HomScheme/TorusSubgroupChartGluingProof`).
- `HomScheme.TorusChart.EtaleSplitStatement` (`HomScheme/TorusChartOpen`): an étale cover
  splitting a closed subtorus of an affine group over an affine test scheme, with explicit
  Hopf coordinates. Status O. Owner task: none found.

## D. Local splitting, root data and the isomorphism theorem

In D1–D5 the base is `Spec R` for a **local** ring `R`, and the split torus
`i : 𝔾_m^I ⟶ G` is **supplied**: a closed subgroup that is a maximal torus on every
residue-field fibre.

**D1. Root data of a split reductive group over a local ring.** Source: Conrad 2014,
Definition 5.1.1, p.136, and Proposition 5.1.6, p.138, with Definition 3.2.1, p.91.
- Lean: `LocalSplitFibrewiseRootDatumExistenceStatement` (`Reductive/LocalSplitRootDatumExistenceStatement`).
  Hypotheses: as above, `G` reductive with affine structure map. Conclusion: one root datum on
  `ℤ^I` that is the root datum of every fibre (`IsFibrewiseRootDatumOf`).
- Scope: no étale cover and no existence of the torus appear; Conrad's Lemma 5.1.3, pp.136–137,
  that every reductive group scheme splits étale-locally, has status M, as do the root spaces
  as line bundles in Definition 5.1.1. Owner task: none.
- Status P: `localSplitFibrewiseRootDatumExistenceProof`
  (`Reductive/LocalSplitRootDatumExistenceProof`).

**D2. Root groups, Weyl elements and the big cell.** Source: Conrad 2014, Theorem 4.1.4,
p.110, Corollary 5.1.9, pp.140–141, and Theorem 5.1.13, p.143. The base ring is local and
**reduced**.
- `LocalSplitRootGroupStatement` and `LocalSplitSimpleRootGroupStatement`
  (`Reductive/LocalSplitCell`, `Reductive/LocalSplitReducedIsomorphismReduction`): root group
  parametrizations `𝔾_a → G` for all roots (respectively the simple roots and their negatives)
  whose Weyl points realize the simple reflections. Status P: `localSplitRootGroup`
  (`Reductive/LocalSplitRootGroupProof`), `localSplitSimpleRootGroup`
  (`Reductive/LocalSplitReducedIsomorphismProof`).
- `LocalSplitCell.LocalWeylNormalizationStatement` (`Reductive/LocalWeylNormalizationStatement`):
  every root parametrization of a simple root has an opposite partner giving the Weyl point.
  Status P: `LocalSplitCell.localWeylNormalization` (`Reductive/LocalWeylNormalizationUnconditionalProof`).
- `LocalSplitBigCellStatement` (`Reductive/LocalSplitCell`): the cell map built from the
  negative and positive root groups and the torus is an open immersion. Status P:
  `localSplitBigCell` (`Reductive/LocalSplitBigCellProof`).
- The relative open cell `U(−λ) × P(λ) → G` of Conrad 2014, Theorem 4.1.7(4), p.113, for a
  general cocharacter over a general base, has status M. Owner task: none.

**D3. The isomorphism theorem over a reduced local ring.** Source: Conrad 2014, Theorem
6.1.17, p.197, and §6.2: Theorem 6.2.1, p.198, Theorem 6.2.4, p.201, and Corollary 6.2.7,
p.204.
- Lean: `LocalSplitReducedIsomorphismTheoremStatement` (`Reductive/LocalSplitReducedIsomorphismTheoremStatement`).
  Hypotheses: a local **reduced** ring; `G`, `H` reductive with affine structure maps and
  supplied fibrewise maximal split tori; fibrewise root data `P`, `Q` with an isomorphism of
  root data. Conclusion: `G ≅ H`.
- Status P: `localSplitReducedIsomorphismTheorem` (`Reductive/LocalSplitReducedIsomorphismProof`).

**D4. The isomorphism theorem over a local ring.** Source: as D3.
- Lean: `LocalSplitIsomorphismTheoremStatement` (`Reductive/LocalSplitIsomorphismTheoremStatement`):
  as D3 without reducedness. Status O. Owner task: none found.
- Lean: `LocalSplitReductiveGeometricIsoStatement` (`Reductive/LocalSplitGeometricIsoStatement`):
  over a local ring, two reductive groups that each have a fibrewise maximal split torus and
  become isomorphic over some algebraically closed field over `R` are isomorphic. Source:
  Conrad 2014, Theorem 3.2.6, p.94, Definition 5.1.1 and Proposition 5.1.6, pp.136–138, and
  Theorem 6.1.17, p.197. Status O. Owner task: none found.

**D5. Generic-fibre determination over strictly henselian local domains.** Source: Conrad
2014, Lemma 5.1.3, pp.136–137, Proposition 5.1.6, p.138, Theorem 3.2.6, p.94, and Theorem
6.1.17, p.197.
- Lean: `StrictHenselianGenericIsoStatement` (`Reductive/StrictHenselianGenericIsoStatement`).
  Hypotheses: a strictly henselian local **domain** `R` with a supplied fraction field `K`;
  `G`, `H` reductive whose base changes to `K` are isomorphic. Conclusion: `G ≅ H` (an
  abstract isomorphism; no prescribed generic isomorphism is claimed to extend).
- Status O. Owner task: Task 4991 (`ca719705-5b1e-4ffa-bb39-29feb566e8ad`), which has no proof
  candidate.

## E. Descent, base change and examples

**E1. Finite Galois descent of affine group schemes.** Source: Milne 2017, A.64 and its
continuation, printed pp.580–581 (PDF 596–597), A.66, printed p.581 (PDF 597), and A.81,
printed p.585 (PDF 601).
- `AffineGroupSchemeFiniteGaloisDescentStatement` (`Descent/AffineEffectivityStatement`), the
  conjunction of the object part (for a finite Galois `L/k`, every descent datum on an affine
  group scheme over `L` is effective, with affine descended group) and the morphism part
  (compatible homomorphisms descend uniquely). Status P: `affineGroupSchemeFiniteGaloisDescent`
  (`Descent/AffineEffectivityProof`).
- The two parts have their own published proofs in the same module:
  `AffineGroupSchemeFiniteGaloisObjectDescentStatement` is status P,
  `affineGroupSchemeFiniteGaloisObjectDescent`, and
  `AffineGroupSchemeFiniteGaloisHomDescentStatement` is status P,
  `affineGroupSchemeFiniteGaloisHomDescent` (`Descent/AffineEffectivityProof`).

**E2. Descent of fppf quotients along fpqc covers.** Source: internal.
- Lean: `AffineFppfQuotientDescentStatement` (`Descent/AffineFppfQuotient`). Hypotheses:
  affine schemes `B`, `S` and `p : S → B` flat, surjective and quasi-compact; a monomorphism
  `i : N ⟶ G` over `B`; a homomorphism `q : G_S ⟶ Q` with `Q` affine, **`q` quasi-compact**,
  and `q` an fppf quotient of `G_S` by `N_S` (`RelativeRoot.IsFppfQuotient`: flat, surjective,
  locally of finite presentation, with kernel range equal to the range of `N_S`). The
  quasi-compactness of `q` is a separate hypothesis: it is not part of `IsFppfQuotient`, and
  it is distinct from the quasi-compactness of the base change map `p`. Conclusion: an fppf
  quotient `r : G ⟶ R` of `G` by `N` with `R` affine, and an isomorphism `e : R_S ≅ Q` with
  `r_S ≫ e = q`.
- Status P: `affineFppfQuotientDescent` (same module).

**E3. DVR lifting descends along algebraic extensions.** Source: Conrad–Gabber–Prasad,
Proposition C.1.2(2), printed pp.582–583 (PDF 608–609).
- Lean: `DVRLiftingAlgebraicDescentStatement` (`DVRLiftingAlgebraicDescentStatement`).
  Hypotheses: an algebraic extension `L/k`; `X` over `k` whose base change to `L` has the
  DVR lifting property. Conclusion: `X` has it.
- Status P: `dvrLiftingAlgebraicDescentStatement` (`DVRLiftingAlgebraicDescentProof`).

**E4. Central isogenies over a base.** Source: Conrad 2014, Definition 3.3.9, p.103.
- `CentralIsogenyBaseChangeStatement` (`CentralIsogeny/BaseChangeStatement`): central
  isogenies are stable under any base change. Status P: `centralIsogenyBaseChange`
  (`CentralIsogeny/BaseChange`).
- `CentralIsogenyFpqcReflectionStatement` (`CentralIsogeny/FpqcReflectionStatement`): being a
  central isogeny descends along a flat, surjective, quasi-compact base change. Status P:
  `centralIsogenyFpqcReflection` (`CentralIsogeny/FpqcReflection`).

**E5. Examples of reductive group schemes.** Source: Conrad 2014, Definition 3.1.1, p.81.
- `GeneralLinear.IsReductiveStatement` (`Reductive/GeneralLinearStatement`): `GL_n` over every
  commutative ring is reductive. Status C: `GeneralLinear.reductiveStatement.2`
  (`Reductive/GeneralLinearProof`).
- `IsSplitTorus.IsReductiveStatement` (`Torus/SplitReductiveStatement`): a split torus over
  every scheme is reductive. Status C: `IsSplitTorus.reductiveStatement.2`
  (`Torus/SplitReductiveProof`).
- Owner task for both: none; they are named wrappers only.

## F. General-base dynamic subgroups and relative Levi subgroups

Source for F1–F2: Conrad 2014, Theorem 4.1.7, pp.112–113, for a finitely presented affine
group over a ring with an arbitrary `G_m`-action, and the paragraph after Example 4.1.9,
p.114, which says that the theorem adapts to any base scheme. The Library's dynamic
subgroups are those of the conjugation action through a cocharacter.

**F1. Dynamic subgroups of a smooth affine group over a ring are smooth.** Source: Conrad
2014, Theorem 4.1.7(4), p.113, the smoothness assertion.
- D: `dynamicSmooth_ring` (`Dynamic/SmoothOverRing`). Hypotheses: a commutative ring
  `R : Type u`; `G` over `Spec R` with smooth and affine structure map; a cocharacter `χ`;
  any `j : H ⟶ G`. Conclusion: if `j` represents `P(χ)`, `Z(χ)` or `U(χ)` (in the sense of
  `SubgroupFunctor.IsRepresentedBy`), then `H` is smooth over `R`. It is a theorem with
  explicit arguments, not a proposition declaration. No noetherian or finiteness hypothesis
  on `R` is imposed. Together with the affine representability of section A, every smooth
  affine `G` over an affine base has smooth closed dynamic subgroups.
- Scope: the base is affine. The author's content search found no Lean statement of the
  smoothness of the dynamic subgroups over a non-affine base scheme, nor of the
  representability of `P(λ)`, `Z(λ)`, `U(λ)` over a non-affine base; status M. Over a ring,
  the open cell of Theorem 4.1.7(4) is the M item of D2, and the connectedness of fibres
  (Theorem 4.1.7(2)) and the Lie algebra description (Theorem 4.1.7(4)) have no Lean
  statement either; status M. The field cases of all these assertions belong to family 4.
  Owner task: none.

**F2. The scheme-level decomposition `P(λ) ≅ U(λ) × Z(λ)` over any base.** Source: Conrad
2014, Theorem 4.1.7(3), p.113: multiplication `Z(λ) ⋉ U(λ) → P(λ)` is an isomorphism; and
the proof of Theorem 4.1.7, p.113, which describes `U(λ)` as the fibre over `1` of the limit
morphism.
- D: `Dynamic.limitGroupHom`, `Dynamic.centralizerToParabolic_comp_limitGroupHom`,
  `Dynamic.isRepresentedBy_kernel_limitGroupHom`, `Dynamic.isIso_multiplication` and
  `Dynamic.multiplicationIso` (`Dynamic/SchemeDecomposition`). Hypotheses: any scheme `S`;
  `G` over `S` with separated structure map; a cocharacter `χ`; group schemes `P`, `Z`, `U`
  with homomorphisms to `G` representing `P(χ)`, `Z(χ)`, `U(χ)`. Conclusions: the limit at
  `0` is a homomorphism `P ⟶ Z` with the inclusion `Z ⟶ P` as a section; its kernel,
  composed with `P ⟶ G`, represents `U(χ)`; and multiplication `U ×_S Z ⟶ P` is an
  isomorphism of schemes over `S`. Representability is a hypothesis; section A supplies it
  for `G` with affine underlying scheme over an affine base.
- On points, the same decomposition over every test scheme is
  `Dynamic.isComplement'_unipotent_centralizer` (section A).
- `GeneralLinear.DynamicStatement` (`Dynamic/GeneralLinearStatement`): for `GL_n` over every
  commutative ring and a diagonal or block-shape cocharacter, `P(λ)`, `Z(λ)`, `U(λ)` are the
  block parabolic, block Levi and block unipotent subgroup functors, with the limit map and,
  on the points over every test scheme, `U(λ)` normal in `P(λ)` with complement `Z(λ)`.
  Status P: `GeneralLinear.dynamicStatement` (`Dynamic/GeneralLinearProof`). Its component
  `GeneralLinear.DiagonalCocharacterLeviDecompositionStatement` (the decomposition on
  points) is status C: `GeneralLinear.dynamicStatement.2.2.2.1`. Owner task: none; a named
  wrapper only.

**F3. Relative Levi subgroups.** Sources: Conrad 2014, Corollary 5.2.5, p.153 (the
unipotent radical `R_u(P)` of a parabolic subgroup of a reductive group scheme over any
base); Definition 5.4.2, p.174 (a Levi subgroup of `P` is a smooth closed `S`-subgroup `L`
with `L ⋉ R_u(P) → P` an isomorphism; the functor `Lev(P)`; `Z_G(λ)` is a Levi subgroup of
`P_G(λ)`); Proposition 5.4.5, p.177 (each maximal torus of `P` lies in a unique Levi
subgroup); Corollary 5.4.6, p.178 (`Lev(P)` is represented by an `R_u(P)`-torsor; any two
Levi `S`-subgroups are conjugate by a unique point of `R_u(P)(S)`; a Levi subgroup is its
own normalizer in `P`); Corollary 5.4.8, p.179 (over an affine base `S` a Levi
`S`-subgroup exists, and `H^1(S_et, L) → H^1(S_et, P)` is bijective).
- Status M for all of these. The Library has no definition of the unipotent radical of a
  parabolic subgroup scheme over a general base, of a Levi subgroup of such a parabolic, or
  of the functor `Lev(P)`, and no statement of the existence, torsor, conjugacy or
  uniqueness assertions above. The Library's `IsRationalLeviSubgroup` (`Rational/LeviSubgroup`)
  is defined over a field only; its rows are in family 5. Existence is local on the base in
  general and global over an affine base (Corollary 5.4.8); no row asserts more. Owner task:
  none.
- What exists over a general base is the dynamic case: for a cocharacter `λ` with
  represented dynamic subgroups, F2 gives `P(λ) ≅ U(λ) × Z(λ)` as schemes. The Library does
  not identify `U(λ)` with a relative `R_u(P(λ))`, since the latter is not defined.

## Summary and remaining obligations

Counted by the Lean statements named above, 29 have published proofs (P), including
`GeneralLinear.DynamicStatement` (F2) and the two parts of finite Galois descent (E1). Six
have a composite and no wrapper theorem (C): the three components of
`RelativeIdentityComponent.SmoothStructureStatement`, `GeneralLinear.IsReductiveStatement`,
`IsSplitTorus.IsReductiveStatement` and
`GeneralLinear.DiagonalCocharacterLeviDecompositionStatement` (F2). Four statements are open
(O): `HomScheme.TorusChart.EtaleSplitStatement`, `LocalSplitIsomorphismTheoremStatement` and
`LocalSplitReductiveGeometricIsoStatement` (no owner task found), and
`StrictHenselianGenericIsoStatement` (Task 4991). Rows F1 and F2 are D: published theorems
with hypotheses, not proposition declarations.

Source assertions without a closed Lean statement (M), none with an owner task:

1. Parabolic subgroups of reductive group schemes are self-normalizing (B6; Conrad 5.2.8).
   A published theorem with hypotheses gives it.
2. Étale-local existence and conjugacy of maximal tori over a general base (C4; Conrad
   3.2.6–3.2.7).
3. Étale-local splitting of reductive group schemes (D1; Conrad Lemma 5.1.3) and the root
   spaces as line bundles (Conrad Definition 5.1.1).
4. The relative open cell for a general cocharacter over a general base (D2; Conrad 4.1.7(4)).
5. The remaining general-base parts of Conrad Theorem 4.1.7 (F1): connectedness of fibres
   and the Lie algebra description over a ring, and representability and smoothness of the
   dynamic subgroups over a non-affine base.
6. Relative Levi subgroups (F3; Conrad 5.2.5, 5.4.2, 5.4.5, 5.4.6, 5.4.8): the unipotent
   radical of a parabolic subgroup scheme, the definition of Levi subgroups and of `Lev(P)`,
   uniqueness given a maximal torus, the torsor and conjugacy statement, and existence over
   an affine base. These need a definitions task before statement tasks.

The wrapper theorems for the C rows need no new mathematics; the program will collect them,
with those of the other families, in one proof task.

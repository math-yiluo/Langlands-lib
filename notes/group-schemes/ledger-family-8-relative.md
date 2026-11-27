# Group-scheme ledger, family 8: relative structure over general bases

Rows B6, B9, C4, D1–D2 and F1–F3 include the declarations at Library
commit `186f3b2ccb3bfee3f9da8d4478ad38d207e354fa`. The dynamic update
describes the field and general-base proof routes.
[Dynamic subgroups](dynamic-relative-progress.md)

This note, dated 10 November 2026, is the source-to-declaration
ledger for family 8 of the algebraic and reductive group-scheme program. Family 8 covers:

- reductive group schemes over a base, fibrewise criteria and base change;
- relative identity components;
- relative tori, maximal tori over local bases, and Hom schemes;
- local splitting, root data over a base and the isomorphism theorem;
- relative parabolic subgroups, their normalizers and quotients, and relative Levi
  subgroups;
- descent, and the general-base dynamic constructions, including smoothness over a ring and
  the scheme-level decomposition `P(λ) ≅ U(λ) × Z(λ)`.

The original snapshot is Library commit `f2c5495316f5a5631bc8c11875b7509d93271fe5`.
Lean names are in `Langlands.GroupScheme` unless a
namespace is shown. Module paths are relative to `Langlands/GroupScheme/` unless they start
with `Langlands/`.

The rows list the principal source assertions of this family. Auxiliary declarations used
inside proofs are not listed one by one, and leaving one out says nothing about its status.
Integral models over rings of `S`-integers, parahoric models and maximal compact subgroups
are listed in the published family-7 ledger
[ledger-family-7-split-classification.md](ledger-family-7-split-classification.md) and are
not repeated here. No row asserts a global choice of a split maximal torus or of a root
datum over an arbitrary base: such data are supplied, or exist over local or strictly
henselian local rings or on étale charts, as each row states.

## Status codes and evidence

Each row gives the source assertion with its locator, the exact Lean statement and its
hypotheses, a status and the evidence.

- **D (definition or internal result).** A published construction, or a published theorem
  that is not a closed proposition (for instance a theorem with hypotheses). The evidence is
  its module path. 
- **P (published proof).** The Library at the commit applicable to the row
  contains the named theorem at the exact proposition. The evidence is the
  theorem and its module path. The original and refreshed proof entries were
  checked against their propositions, and the axiom checks reported only
  `propext`, `Classical.choice` and `Quot.sound`.
- **C (composite, not published).** No published theorem has the statement as its type, but
  a projection out of a published conjunction has it. The author type-checked the
  projection in the same private module. What is missing is a named wrapper theorem, not
  mathematics.
- **O (open).** A Lean statement exists, but no published proof and no composite from
  published results is known.
- **M (missing statement).** A source assertion of this family has no closed Lean
  statement. The author searched the statement declarations of the Library by content (for
  the predicates involved), not only by name, before recording an M row.

The label "published" means: in the Library.

Source locators use these registered sources, cited by source id:

- `conrad-2014-reductive-group-schemes` is B. Conrad, *Reductive group
  schemes* (2014), SHA-256
  `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
  Printed and PDF pages agree.
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

The original source locators were checked against the retained editions on
10 November 2026. The later entries use the same editions.

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
  [transport-dynamic-progress.md](transport-dynamic-progress.md).
  F1 gives representability and smoothness over arbitrary base schemes.

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
- Named wrappers only.

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
- `RelativeParabolicSelfNormalizerStatement` states this over every
  commutative ring with the same smooth closed subgroup and field-valued
  parabolicity hypotheses. `relativeParabolicSelfNormalizer` proves the
  exact proposition (P).
  [Statement](../../Langlands/GroupScheme/RelativeParabolicNormalizerStatement.md),
  [proof](../../Langlands/GroupScheme/RelativeParabolicNormalizerProof.md)

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
  (`Langlands/Global/IntegralIwasawaFamilyReduction`).

**B9. Relative parabolic inclusions and their moduli.** Conrad 2014,
Proposition 5.2.3, pp.152–153, gives closedness and the étale-local
dynamic description. Corollary 5.2.9, pp.156–157, gives the smooth
proper scheme of parabolic subgroups.

- For a reductive \(G\) and a relative parabolic \(i:P\to G\) over any
  scheme \(S\), `relativeParabolicClosed` proves
  `RelativeParabolicClosedStatement` (P). The theorem
  `relativeParabolicEtaleLocalDynamic` proves
  `RelativeParabolicEtaleLocalDynamicStatement` (P), supplying on each
  member of an étale cover a cocharacter whose dynamic parabolic is
  represented by the pullback of \(i\).
  [Closedness statement](../../Langlands/GroupScheme/RelativeLevi/ParabolicClosedStatement.md),
  [dynamic statement](../../Langlands/GroupScheme/RelativeLevi/ParabolicLocalDynamicStatement.md),
  [proofs](../../Langlands/GroupScheme/RelativeLevi/ParabolicClosedProof.md)
- `relativeParabolicScheme` proves `RelativeParabolicSchemeStatement`
  (P). For a reductive \(G\) over any scheme, it gives a smooth proper
  \(S\)-scheme with a universal relative parabolic of the pulled-back
  group. Every relative parabolic over a test scheme is the pullback
  along a unique morphism to this scheme, with equality of subgroup
  images on all tests.
  [Statement](../../Langlands/GroupScheme/RelativeLevi/ParabolicSchemeStatement.md),
  [proof](../../Langlands/GroupScheme/RelativeLevi/ParabolicSchemeProof.md)

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

**C4. Étale-local existence and conjugacy of maximal tori.**
Conrad 2014, Corollary 3.2.7, p.95, gives existence for reductive groups.
Theorem 3.2.6, p.94, assumes that maximal tori in the geometric fibre
identity components are their own centralizers. Its proof on pp.94–95
gives the conjugacy construction for supplied maximal tori of a smooth
affine group.
- `EtaleLocalMaximalTorusExistenceStatement` gives an étale cover of an
  arbitrary base of a reductive group, with an actual closed relative
  torus maximal on every residue fibre over each chart. Status P via
  `etaleLocalMaximalTorusExistence`.
  [Statement](../../Langlands/GroupScheme/Torus/EtaleLocalMaximalExistenceStatement.md),
  [proof](../../Langlands/GroupScheme/Torus/EtaleLocalMaximalExistenceProof.md)
- `EtaleLocalMaximalTorusConjugacyStatement` takes a smooth affine ambient
  group and two closed relative tori maximal on every residue fibre.
  On each member of an étale cover it gives a point conjugating the two
  subgroup images on all tests. Status P via `etaleLocalMaximalTorusConjugacy`.
  [Statement](../../Langlands/GroupScheme/Torus/EtaleLocalMaximalConjugacyStatement.md),
  [proof](../../Langlands/GroupScheme/Torus/EtaleLocalMaximalConjugacyProof.md)

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
  Hopf coordinates. Status O.

## D. Local splitting, root data and the isomorphism theorem

The fibrewise root datum over a local ring in D1 and the local split assertions
in D2–D4 use supplied split maximal tori. Their inclusions are closed
and maximal on every residue-field fibre. D5 takes two reductive groups
over a strictly henselian local domain and an isomorphism of their generic fibres.

**D1. Root data of a split reductive group over a local ring.** Source: Conrad 2014,
Definition 5.1.1, p.136, and Proposition 5.1.6, p.138, with Definition 3.2.1, p.91.
- Lean: `LocalSplitFibrewiseRootDatumExistenceStatement` (`Reductive/LocalSplitRootDatumExistenceStatement`).
  Hypotheses: as above, `G` reductive with affine structure map. Conclusion: one root datum on
  `ℤ^I` that is the root datum of every fibre (`IsFibrewiseRootDatumOf`).
- Status P: `localSplitFibrewiseRootDatumExistenceProof`
  (`Reductive/LocalSplitRootDatumExistenceProof`).
- `EtaleLocalSplitReductiveStatement` gives the splitting in Conrad,
  Lemma 5.1.3, pp.136–137. Each point of the base of a reductive group admits
  an étale affine neighbourhood with a closed coordinate split maximal
  torus, one actual root datum on all field fibres and free rank-one
  exponent-weight modules for its roots. Status P via `etaleLocalSplitReductive`.
  [Statement](../../Langlands/GroupScheme/Reductive/EtaleLocalSplitStatement.md),
  [proof](../../Langlands/GroupScheme/Reductive/EtaleLocalSplitProof.md)
- For a reductive group over any base with a supplied fibrewise maximal
  coordinate split torus and global coordinate root datum,
  `CoordinateRootDatum.rootLineBundle` constructs the actual root-weight
  line bundle. Its pullback to every affine test is the sheaf of the
  corresponding exponent-weight module. `CoordinateRootDatum.rootFrame_hom_eq`
  gives coherence under further affine base change.
  [Construction](../../Langlands/GroupScheme/Reductive/RootWeightLineBundles.md)

**D2. Root groups, Weyl elements and the big cell.** Source: Conrad 2014, Theorem 4.1.4,
p.110, Corollary 5.1.9, pp.140–141, and Theorem 5.1.13, p.143.
The local split results for root groups, Weyl normalization and the big cell
take a **reduced local ring**.
- `LocalSplitRootGroupStatement` and `LocalSplitSimpleRootGroupStatement`
  (`Reductive/LocalSplitCell`, `Reductive/LocalSplitReducedIsomorphismReduction`): root group
  parametrizations `𝔾_a → G` for all roots (respectively the simple roots and their negatives)
  whose Weyl points realize the simple reflections. Status P: `localSplitRootGroup`
  (`Reductive/LocalSplitRootGroupProof`), `localSplitSimpleRootGroup`
  (`Reductive/LocalSplitReducedIsomorphismProof`).
- `LocalSplitCell.LocalWeylNormalizationStatement` (`Reductive/LocalWeylNormalizationStatement`):
  every root parametrization of a simple root has an opposite partner giving the Weyl point.
  Status P: `LocalSplitCell.localWeylNormalization` (`Reductive/LocalWeylNormalizationUnconditionalProof`).
- `LocalSplitBigCellStatement` (`Reductive/LocalSplitCell`) takes a
  supplied fibrewise root datum, a base, root parametrizations and
  enumerations of its positive and negative roots. The ordered product
  of the negative root groups, the torus and the positive root groups
  maps to \(G\) by an open immersion. Status P via `localSplitBigCell`
  (`Reductive/LocalSplitBigCellProof`).
- `DynamicBaseOppositeCellStatement` gives the relative open immersion
  \(U(-\lambda)\times_S P(\lambda)\to G\) of Conrad 2014, Theorem 4.1.7(4),
  pp.113–114, over any base. It takes a smooth affine group \(G\) and
  supplied representatives for the two functors. Status P via
  `dynamicBaseOppositeCell`.
  [Statement](../../Langlands/GroupScheme/Dynamic/BaseOppositeCellStatement.md),
  [proof](../../Langlands/GroupScheme/Dynamic/BaseOppositeCellProof.md)

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
  as D3 without reducedness. Status O; now proved, as `localSplitIsomorphismTheorem`.
- Lean: `LocalSplitReductiveGeometricIsoStatement` (`Reductive/LocalSplitGeometricIsoStatement`):
  over a local ring, two reductive groups that each have a fibrewise maximal split torus and
  become isomorphic over some algebraically closed field over `R` are isomorphic. Source:
  Conrad 2014, Theorem 3.2.6, p.94, Definition 5.1.1 and Proposition 5.1.6, pp.136–138, and
  Theorem 6.1.17, p.197. Status O; now proved, as `localSplitReductiveGeometricIso`.

**D5. Generic-fibre determination over strictly henselian local domains.** Source: Conrad
2014, Lemma 5.1.3, pp.136–137, Proposition 5.1.6, p.138, Theorem 3.2.6, p.94, and Theorem
6.1.17, p.197.
- Lean: `StrictHenselianGenericIsoStatement` (`Reductive/StrictHenselianGenericIsoStatement`).
  Hypotheses: a strictly henselian local **domain** `R` with a supplied fraction field `K`;
  `G`, `H` reductive whose base changes to `K` are isomorphic. Conclusion: `G ≅ H` (an
  abstract isomorphism; no prescribed generic isomorphism is claimed to extend).
- Status O at the commit above. The Library now proves it, as `strictHenselianGenericIso`
  (`Reductive/StrictHenselianGenericIsoProof.lean`).

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
- Named wrappers only.

## F. General-base dynamic subgroups and relative Levi subgroups

Source for F1–F2: Conrad 2014, Theorem 4.1.7, pp.112–113, for a finitely presented affine
group over a ring with an arbitrary `G_m`-action, and the paragraph after Example 4.1.9,
p.114, which says that the theorem adapts to any base scheme. The Library's dynamic
subgroups are those of the conjugation action through a cocharacter.

**F1. Representability, smoothness, fibres and Lie weights of dynamic subgroups.**
Conrad 2014, Theorem 4.1.7(1) and (2), pp.112–113, gives representability
and connectedness. Part (4), p.113, assumes a smooth ambient group and
gives smoothness and the Lie description in that setting. The paragraph
after Example 4.1.9, p.114, extends the theorem to arbitrary bases.

- D: `dynamicSmooth_ring` (`Dynamic/SmoothOverRing`). Hypotheses: a commutative ring
  `R : Type u`; `G` over `Spec R` with smooth and affine structure map; a cocharacter `χ`;
  any `j : H ⟶ G`. Conclusion: if `j` represents `P(χ)`, `Z(χ)` or `U(χ)` (in the sense of
  `SubgroupFunctor.IsRepresentedBy`), then `H` is smooth over `R`. It is a theorem with
  explicit arguments, not a proposition declaration. No noetherian or finiteness hypothesis
  on `R` is imposed. Together with the affine representability of section A, every smooth
  affine `G` over an affine base has smooth closed dynamic subgroups.
- `dynamicBaseRepresentability` proves `DynamicBaseRepresentabilityStatement`
  (P). An affine locally finitely presented \(G\) over any base has
  locally finitely presented closed representatives for its three
  dynamic subgroup functors on all tests.
  [Statement](../../Langlands/GroupScheme/Dynamic/BaseRepresentabilityStatement.md),
  [proof](../../Langlands/GroupScheme/Dynamic/BaseRepresentabilityProof.md)
- `dynamicBaseSmoothConnected` proves `DynamicBaseSmoothConnectedStatement`
  (P). For smooth affine \(G\) over any base, every such representative
  is smooth. The fibres of \(U(\lambda)\) are geometrically connected.
  So are those of \(P(\lambda)\) and \(Z(\lambda)\) when the fibres of
  \(G\) are geometrically connected.
  [Statement](../../Langlands/GroupScheme/Dynamic/BaseSmoothConnectedStatement.md),
  [proof](../../Langlands/GroupScheme/Dynamic/BaseSmoothConnectedProof.md)
- `dynamicBaseConnected` proves `DynamicBaseConnectedStatement` with
  the same connectedness conclusions for affine locally finitely
  presented \(G\) and supplied representatives (P).
  `dynamicBaseUnipotentFibres` proves `DynamicBaseUnipotentFibresStatement`
  for affine locally finite-type \(G\) and a supplied representative of
  \(U(\lambda)\), giving unipotence after every field-valued base change (P).
  The unipotence assertion uses Conrad 2014, p.114, and CGP 2015,
  Lemma 2.1.5, printed pp.49–51 (PDF pp.75–77).
  [Connectedness proof](../../Langlands/GroupScheme/Dynamic/BaseConnectedProof.md),
  [unipotence proof](../../Langlands/GroupScheme/Dynamic/BaseUnipotentFibresProof.md)
- `dynamicRingLie` proves `DynamicRingLieStatement` (P). Over any
  commutative ring, for an affine locally finitely presented \(G\), the
  actual dual-number Lie points lying in \(Z(\lambda)\), \(P(\lambda)\)
  and \(U(\lambda)\) are the weight-zero, nonnegative and positive
  weight submodules, respectively. The source in this generality is
  CGP 2015, Proposition 2.1.8(1), printed p.53 (PDF p.79), in
  `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
  `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
  [Statement](../../Langlands/GroupScheme/Dynamic/RingLieStatement.md),
  [proof](../../Langlands/GroupScheme/Dynamic/RingLieProof.md)

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
  for `G` with affine underlying scheme over an affine base, and F1
  supplies it for affine locally finitely presented `G` over any base.
- On points, the same decomposition over every test scheme is
  `Dynamic.isComplement'_unipotent_centralizer` (section A).
- `GeneralLinear.DynamicStatement` (`Dynamic/GeneralLinearStatement`): for `GL_n` over every
  commutative ring and a diagonal or block-shape cocharacter, `P(λ)`, `Z(λ)`, `U(λ)` are the
  block parabolic, block Levi and block unipotent subgroup functors, with the limit map and,
  on the points over every test scheme, `U(λ)` normal in `P(λ)` with complement `Z(λ)`.
  Status P: `GeneralLinear.dynamicStatement` (`Dynamic/GeneralLinearProof`). Its component
  `GeneralLinear.DiagonalCocharacterLeviDecompositionStatement` (the
  decomposition on points) is P by `GeneralLinear.diagonalCocharacterLeviDecomposition`.
  [Proof](../../Langlands/GroupScheme/Dynamic/GeneralLinearDiagonalCocharacterLeviDecompositionProof.md)

**F3. Relative Levi subgroups.** Conrad 2014, Definition 5.4.2, p.174,
defines a Levi subgroup as a smooth closed subgroup whose multiplication
with the relative unipotent radical gives the semidirect product.
`IsRelativeUnipotentRadical` requires a smooth closed normal subgroup with
the unipotent radical on each geometric fibre. `IsRelativeLeviSubgroup`
uses the actual multiplication morphism of schemes.
`RelativeLevi.moduliFunctor P` has as values the subgroup images of Levi
inclusions over the test scheme and restricts them by base change.
The conjugation action is that of the actual radical.
[Predicates](../../Langlands/GroupScheme/RelativeLevi/Basic.md),
[moduli functor](../../Langlands/GroupScheme/RelativeLevi/ModuliFunctor.md)

The following propositions concern a reductive group and a relative
parabolic over an arbitrary scheme, with an affine-base hypothesis
where indicated. Each linked theorem proves the exact named proposition (P).

| Source and assertion | Proposition and proof |
| --- | --- |
| Corollary 5.2.5, p.153. There is a relative unipotent radical with a unique all-test subgroup image in \(P\). Given the radical, the fppf quotient of \(P\) by it is reductive and every surjective homomorphism from \(P\) to a reductive group factors through that quotient uniquely. | `RelativeUnipotentRadicalStatement` and `RelativeParabolicReductiveQuotientStatement`. [`relativeUnipotentRadical`](../../Langlands/GroupScheme/RelativeLevi/UnipotentRadicalProof.md), [`relativeParabolicReductiveQuotient`](../../Langlands/GroupScheme/RelativeLevi/ReductiveQuotientProof.md) |
| Example 5.2.2, p.151, and Definition 5.4.2, p.174. For a cocharacter of a reductive group and representatives of its three dynamic functors, \(P(\lambda)\) is relative parabolic. The factorizations of \(U(\lambda)\) and \(Z(\lambda)\) through \(P(\lambda)\) are a relative radical and a relative Levi, respectively. | `DynamicRelativeLeviStatement`. [`dynamicRelativeLevi`](../../Langlands/GroupScheme/RelativeLevi/DynamicProof.md) |
| Theorem 5.4.3, pp.174–175. Over an affine base the supplied relative radical has a finite closed normal series with vector-bundle additive fppf quotients. | `RelativeUnipotentRadicalFiltrationStatement`. [`relativeUnipotentRadicalFiltration`](../../Langlands/GroupScheme/RelativeUnipotent/RadicalFiltrationProof.md) |
| Proposition 5.4.5, p.177. A supplied closed relative torus that is maximal in each residue fibre of \(P\) is contained in a unique Levi subgroup image. | `RelativeTorusLeviStatement`. [`relativeTorusLevi`](../../Langlands/GroupScheme/RelativeLevi/TorusLeviProof.md) |
| Corollary 5.4.6, p.178. For a supplied relative radical, there is an actual fpqc torsor representing Levi subgroup images, with the conjugation action. Any two supplied Levi subgroups are conjugate by a unique global point of the supplied radical. A Levi is its own all-test normalizer in \(P\). | `RelativeLeviTorsorStatement`, `RelativeLeviConjugacyStatement` and `RelativeLeviSelfNormalizerStatement`. [`relativeLeviTorsor`](../../Langlands/GroupScheme/RelativeLevi/TorsorProof.md), [`relativeLeviConjugacy`](../../Langlands/GroupScheme/RelativeLevi/ConjugacyProof.md), [`relativeLeviSelfNormalizer`](../../Langlands/GroupScheme/RelativeLevi/SelfNormalizerProof.md) |
| Corollary 5.4.8, p.179, existence clause. Over an affine base there is a relative Levi. The proof takes a section of the torsor using the finite vector-bundle series of the radical. | `RelativeLeviAffineExistenceStatement`. [`relativeLeviAffineExistence`](../../Langlands/GroupScheme/RelativeLevi/AffineExistenceProof.md) |

Corollary 5.4.8 also gives the bijection
\(H^1(S_{\mathrm{et}},L)\to H^1(S_{\mathrm{et}},P)\). The linked Lean
proposition covers the existence clause.

The rational Levi results over a field are in family 5.
[Rational parabolics and Levis](ledger-family-5-rational.md#b-rational-parabolics-minimal-parabolics-and-rational-levi-subgroups)

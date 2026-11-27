# Harris–Berkovich cohomological framework: declaration coverage

This note maps the cohomological input to Harris's weak automorphic
induction, as used by Henniart, to Library declarations: the Harris and Berkovich
cohomological theorem-statement framework. It also lists the parts that are not yet stated
and the prerequisites they wait for. It is a map, not a theorem.
Every declaration below is a `Prop`-valued theorem-statement definition, or
an auxiliary construction used to state one. Several components are proved
by published Lean theorems, among them the five components of the `SupercuspidalExtCharZero`
and `SupercuspidalRestriction` statements listed under [Proved statements](#proved-statements). At
Library commit `b47a2385d86db05fb5e69eda98e948bf2539ada2`,
eight of the eighteen propositions were proved: the convergence and
second-page statements, the composites on topological spaces, the étale
and quasi-étale composites of Berkovich §1.2 on analytic sites, and the
quasi-étale comparison of Theorem 1.6.1(ii) (see
[Proved statements](#proved-statements)). The étale comparisons of Theorem
1.6.1(ii) and Corollary 1.5.2(i) had no proofs. Neither had the five analytic propositions
stated last: the two spectral sequences of §1.2, the two ordinary comparisons of
Theorem 1.6.1(i) and the étale module version of Theorem 1.4.2. Harris 1999 (5.1) on the
`λ`-adic cohomology of the CM
tower and the two derived statements of Theorem 5.9(ii) also had no
proofs. The derived statements do not identify the local
representation with Harris's cohomological parameter of (5.4)–(5.5). A search of the present
Library by statement name finds no proof of these open propositions either; the étale
comparison of Corollary 1.5.2(i) has the conditional proof
`compactComparison_of_openDomains_of_openMap_of_compactAcyclic`.

Each module's paired Markdown gives its exact hypotheses, sources with
locators, and checks. The originals of the Henniart audit, among them Harris
1998, Harris 1999 and Berkovich's manuscript, are described in
[Registered originals and reading record](sources.md). The other sources
named below, such as SGA 4 and Harris–Taylor 2001, are identified only in
the Markdown of the modules that cite them. The source analysis of Harris
1999 is in
[Harris 1999 and the deferred general-coefficient argument](harris-1999.md).

Versions. The note was first written against Library commit
`ddb0a9c0d562246b405e8f1149220107e7407d1d` of an earlier line of the Library and updated
against Library commit `dbd6b52814f3ecfa30bdd5f8785d2e17e89e85dc`; on 13 November 2026 against
`b128d289028bf75629e9e364ecf151c484b27a85`, `4b619cdd61c537ff5ee2587fda415e0adb66e5ef` and
`2e46b9cac0230529f50cdf96bbe4713c06701fc2`; on 14 November 2026 against `c40a01345b2f4172fa41e07ff31644b40e695003`,
`ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181`, `58ad0f796899b4aa457077d0146815c24758f739`,
`320321b3cd4b5100d54cf785192677d59479e65f` and `544dba099880b57da5fdc3cbc715c01cf2579eb2`; on 20 November 2026 against
`d6b462beebdb629f6b6746bdf0698a800d84104f`; and on 21 November 2026 against
`b47a2385d86db05fb5e69eda98e948bf2539ada2`. All checks used Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Each update surveyed only the changes that bear on
the modules described here; a sentence that names a commit states a fact of that commit.

The statement modules of this framework first appeared in the Library as follows:
`HyperextConvergence.Statement` at `e449cde988d4e97ab280b8d4d11262887ccc26e0`,
`EquivariantComposite.Statement` at `d39b5aee822fe2ad1aadf07861ebd9a4c2df62a8`,
`HyperextConvergence.HalfBoundedStatement` at `e748734106ab2ee9de1cab1eb18a60e59593aac0`,
`AnalyticQuasiEtaleGlobalComparison.Statement` at `2e46b9cac0230529f50cdf96bbe4713c06701fc2`,
`AnalyticEtaleGlobalComparison.Statement` at `c0debd6f4dd02fdd68d70811cf610906b945a962`,
`AnalyticGlobalComposite.Statement` (two statements) and
`AnalyticEtaleCompactComparison.Statement` at `c40a0134`,
`Langlands.Shimura.PEL.HarrisTaylorCMHarrisVanishingStatement` (Harris 1999 (5.1)) at
`ba00e097`, the statement of Harris 1999 Theorem 5.7(i)–(ii) at
`b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a`, the two derived Theorem 5.9(ii) propositions at
`6e9e589baa721ce995563f73f648b6f4e45718a1`, and
`AnalyticGlobalSpectralSequence.Statement`, `AnalyticParacompactComparison.Statement`,
`Langlands.Sheaf.Equivariant.AnalyticEtaleToposComparison.Statement` and the construction
module `Langlands.Sheaf.Equivariant.AnalyticEtaleEquivariantCompactGlobal` at
`2d12bd934a2a0da7808014bfe52c6d67fde3eb62`. A documentation correction at the same commit
amended the paired Markdown of
`AnalyticQuasiEtaleGlobalComparison.Statement` and
`AnalyticEtaleCompactComparison.Statement` to separate the Library models
from the manuscript's sites and the paper quasi-étale obstruction from the
legacy topology; both Lean files are unchanged. The proof of the étale composite of §1.2
first appeared at `ba00e097`; that of the quasi-étale composite
(`analyticQuasiEtaleGlobalComposite`) and a correction of Theorem 5.7(i)–(ii) entered the
Library after `58ad0f79` and are in `320321b3`; and that of the quasi-étale comparison of Theorem 1.6.1(ii) at
`032961776f43ccd672c6266d265a9c644faeba13`. Geometric premises that earlier versions of this
note listed as open are proved: `SetInducedSpace.continuityStatement` (at `03296177`),
`sigmaDesc_quasiEtale_etale` (at `95d37e11`) and `etalePointwiseLifting` (at `03296177`); they
are recorded where they are used below. Kottwitz 1992 Theorem 1 is the statement
`CMHarrisKottwitzLambdaAdicStatement` (see the row on compatible Galois families). At
`b47a2385` two further statements were in preparation and not in the Library: the compact-base
spectral sequence of Theorem 1.6.1(ii) on the étale and on the quasi-étale model, and the
compact-base étale compact-support spectral sequence of Corollary 1.5.2(i).

## Analytic and algebraic dependencies at Library `3f72bdc7`

The table pins the Lean and Markdown pairs to Library
`3f72bdc7a0281aa90900e79d538c35865373ea02`. Each named `Statement`
is a proposition definition. The first six rows give inputs for the
smooth compact-support and coefficient-limit constructions. The
remaining rows give inputs for passing from the geometric CM levels
to their cohomology with algebraic coefficients.

| Declaration | Source and scope |
| --- | --- |
| [`AnalyticEtaleCompactSupportSpectralSequenceForCompactGroupStatement`](../../Langlands/Cohomology/AnalyticGlobalSpectralSequence/CompactGroupSupportStatement.md) | Berkovich, *Equish*, §1.2 and Corollary 1.5.2(i). The second page uses derived smooth invariants, expressed as Ext from the trivial smooth representation, for the actual restriction action on compactly supported cohomology. The Library requires compactness of the acting group so the orbit of a compact support lies in a compact set. The analytic space is Hausdorff, with continuous action and a surjective projection from the field-valued points satisfying the étale point axioms. |
| [`AnalyticEtaleGodementResolutionStatements`](../../Langlands/Cohomology/AnalyticEtaleGodementResolution/Statement.md) | *Equish* §1.5, Proposition 1.5.1 and Corollary 1.5.2(i), and Harris 1999 §2, Fact 3 and Lemma 2.2. On a Hausdorff space with continuous action, the \(L\)-valued points satisfy the étale point axioms and project surjectively to the space. The iterated term functors are exact, the augmentation is a quasi-isomorphism, and every term is acyclic for smooth compact sections and for ordinary compact sections after restriction. Harris's Fact 4 identifies the separate preservation of divisible systems. |
| [`AnalyticEtaleCompactDerivedComparisonStatement`](../../Langlands/Cohomology/AnalyticEtaleCompactComparison/DerivedStatement.md) | *Equish*, Corollary 1.5.2(i), first assertion. The actual comparison of compact-section complexes is invertible in derived modules after exact forgetting of the action. Surjectivity of the field-valued point projection is among the support hypotheses. |
| [`AnalyticEtaleCompactDimensionStatement`](../../Langlands/Cohomology/AnalyticEtaleCompactDimension/Statement.md) | Berkovich 1993, Corollary 5.3.8, absolute bounded-torsion specialization. Compactly supported cohomology vanishes for \(q>2d\) with sheaves of \(\mathbb Z/N\mathbb Z\)-modules for \(N>0\) (universe-lifted coefficients in Lean). The space is Hausdorff with a strict affinoid dimension bound \(d\), over an algebraically closed field with a complete, nontrivial ultrametric norm. The field-valued points satisfy the étale point axioms and project surjectively to the space. |
| [`AnalyticEtaleFinitenessStatement`](../../Langlands/Cohomology/AnalyticEtaleFiniteness/Statement.md) | Berkovich 1994, Corollary 5.6. The space is compact Hausdorff over an algebraically closed, complete, nontrivially normed ultrametric field \(K\), with quasi-algebraic affinoid neighbourhoods. For each positive integer \(N\) of norm one in \(K\) (the prime-to-residue-characteristic condition), every ordinary étale cohomology group of a finite locally constant sheaf of \(\mathbb Z/N\mathbb Z\)-modules is finite. |
| [`EtaleAdicFiniteGenerationStatement`](../../Langlands/Cohomology/DivisibleSystem/EtaleAdicFiniteGenerationStatement.md) | Milne 1980, V.1, Lemma 1.11. Finite cohomology at every stage of the étale divisible system gives finite generation and adic completeness of its cohomology limit over the complete coefficient ring. The actual canonical reduction sequence is short exact. |
| [`CMHarrisLambdaTowerAdmissibleContinuousStatement`](../../Langlands/Shimura/PEL/HarrisTaylorCMLambdaAdmissibleStatement.md) | Harris–Taylor III.1–2. For the represented division-algebra CM levels and an algebraic coefficient representation, the actual level map identifies cohomology with the compact-open fixed vectors of the tower. The tower over the finite coefficient completion is admissible and Galois acts continuously on those fixed vectors. |
| [`ProperEtaleFinitenessStatement`](../../Langlands/Cohomology/EtaleFiniteness/ProperStatement.md) | SGA 4 XIV 1.2. Over a separably closed field, proper schemes have finite étale cohomology with finite locally constant module sheaves, including in the torsion characteristic of the base. |
| [`EtaleProperBaseChangeStatement`](../../Langlands/Cohomology/EtaleProperBaseChange/Statement.md) | SGA 4 XII 5.1(iii). The actual derived adjunction map is invertible in a Cartesian square with proper vertical map for bounded-torsion coefficients placed in degree zero. The four derived-category universes are independent. |
| [`AbelianFirstEtaleCohomologyStatement`](../../Langlands/Cohomology/AbelianScheme/FirstEtaleCohomologyStatement.md) | Milne, *Abelian Varieties*, §15, Theorem 15.1(a). Over a fixed algebraically closed field of characteristic different from \(p\), the first integral \(p\)-adic étale cohomology of an abelian scheme is naturally isomorphic to the dual of its actual Tate module. |

The same Library version gives
[`compactProbeQuasiEtaleHausdorffComparison`](../../Langlands/Geometry/Analytic/CompactProbeQuasiEtaleHausdorffComparisonProof.md)
when the target of the ordinary covering sieve is Hausdorff.
With this proof,
[`equivariantCompactProbeQuasiEtaleTopology_eq_of_comparison`](../../Langlands/Geometry/Analytic/EquivariantCompactProbeTopology.md)
identifies the equivariant compact-probe topology with the
chart-neighbourhood topology because the equivariant probe sources
are Hausdorff. The smooth sheaf category
[`CompactProbeQuasiEtaleGSheaf`](../../Langlands/Sheaf/Equivariant/AnalyticCompactProbeQuasiEtale.md)
uses `twistedCompactProbeQuasiEtaleTopology`, induced on the twisted
site by the ordinary compact-probe topology.
The equivariant topos comparison on these objects needs the
inverse-image and invariant-sheaf adjunction for these topologies.
The geometric first-cohomology comparison also leaves the relative
coefficient comparison and the tautological power projectors on the
CM levels as separate mathematical inputs.

## Relative abelian cohomology and Hodge–Tate comparison at Library `05331414`

The following statement pairs are pinned to
`053314145457c1e8d2da92d3141cbba5942613d7` with Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Their mathematical inputs
are the actual small-étale and coherent cohomology constructions.

| Declaration | Source and scope |
| --- | --- |
| [`RelativeFirstEtaleCohomologyStatement`](../../Langlands/Cohomology/AbelianScheme/RelativeFirstEtaleCohomologyStatement.md) | Milne 1980, III §4, and SGA 4 XII 5.2(iii). For an abelian scheme over a scheme in universe zero and a positive invertible exponent, the actual first higher direct image of the constant coefficient sheaf is isomorphic to the internal character sheaf of the torsion. The sheaf condition for the character presheaf is proved. The isomorphism uses the universe lift of the higher direct image. |
| [`RelativeAbelianMultiplicationCohomologyStatement`](../../Langlands/Cohomology/AbelianScheme/RelativeMultiplicationStatement.md) | Milne, *Abelian Varieties*, Theorem 15.1, Milne 1980, V.1, Lemma 1.11, and SGA 4 XII 5.2(iii). For a prime \(p\) invertible on the base, the actual relative pullback by \([m]\) in degree \(q\) with constant \(\mathbb Z/p^r\mathbb Z\) coefficients is scalar \(m^q\). The map comes from the derived adjunction and the inverse image of the constant sheaf. |
| [`ProperSmoothHodgeTateNaturalStatement`](../../Langlands/Cohomology/HodgeTate/ProperSmoothStatement.md) | Faltings 1988, §1(b)–(c) and III §4. For a finite extension of \(\mathbb Q_p\), in each degree one family of semilinear Galois comparisons for proper smooth schemes intertwines all pullbacks over that field. The actual differential-form summand of degree \(j\) has cyclotomic twist \(-j\), following the introduction. `properSmoothHodgeTateStatement_of_natural` specializes the family to a single scheme. |

The finite-coefficient relative statements enter the Tate module and
multiplication-by-two projector comparisons of Harris–Taylor III.2,
p. 98. The proper smooth comparison then intertwines the corresponding
linear combinations of pullbacks. Identification of the projector with
the Harris coefficient system and comparison under Hecke transfers are
further mathematical inputs for the labelled multiplicity theorem.

## Compact-probe and geometric coefficient comparisons at Library `7a774d17`

These pairs are pinned to Library
`7a774d17c4fc5bddf71c088815a369b4ac0ec52f`. Each named `Statement`
is a proposition definition.

| Declaration | Source and scope |
| --- | --- |
| [`EquivariantEtaleToCompactProbeStatement`](../../Langlands/Sheaf/Equivariant/AnalyticEtaleToCompactProbe/Statement.md) | Berkovich, *Equish*, Corollary 1.4.3, p. 10. For Hausdorff analytic spaces over a fixed complete ultrametric field, the unit of the actual equivariant étale to compact-probe adjunction is invertible. The coefficient categories are modules, and open subgroup quotients fit in the geometric universe. |
| [`CompactProbeQuasiEtaleGSheafToposComparisonStatement`](../../Langlands/Sheaf/Equivariant/AnalyticQuasiEtaleToposComparison/Statement.md) | *Equish*, Theorem 1.4.2, pp. 8–9, with Definition 1.4.1 and Construction 1.1.2. Under the image-pullback and open-quotient size hypotheses, the actual inverse image into twisted module sheaves is discrete on the compact probes. Its adjunction with invariant sections has invertible unit and counit. The ordinary and equivariant Hausdorff topology comparisons identify the covering rule. |
| [`CompactProbeQuasiEtaleGlobalComparisonStatements`](../../Langlands/Cohomology/AnalyticCompactProbeGlobalComparison/Statement.md) | *Equish*, Theorem 1.6.1(i)–(ii), pp. 13–14. Paracompactness gives the ordinary restriction comparison. Compactness gives the smooth-to-ordinary comparison in each degree and for the derived complex, and the spectral sequence of smooth invariants on the ordinary cohomology. The action is continuous over the fixed field. The statement uses the actual compact-probe refinements for Hausdorff spaces. |
| [`EtaleLerayStatement`](../../Langlands/Cohomology/EtaleLeray/Statement.md) | Milne 1980, III.1.18(a) and Appendix B. For an actual scheme map and one module sheaf, the covariant hyperext sequence has second page given by the cohomology of the higher direct images. It has the first-quadrant filtration of the source-scheme cohomology. The page and abutment comparisons are additive existence assertions. |
| [`RelativeAdicMultiplicationCohomologyStatement`](../../Langlands/Cohomology/AbelianScheme/RelativeAdicMultiplicationStatement.md) | Milne, *Abelian Varieties*, Theorem 15.1, Milne 1980, V.1.11, and SGA 4 XII.5.2(iii) and XIV.1.2. For a prime \(p\) invertible on the base, the actual relative pullback by \([m]\) acts by \(m^q\) on the whole degree-\(q\) diagram of finite reductions over \(\mathbb Z_p\). Naturality in the coefficient module gives the compatibility with reduction. |
| [`RelativeEtaleKunnethStatement`](../../Langlands/Cohomology/AbelianScheme/RelativeKunnethStatement.md) | Milne 1980, VI.8.5, with SGA 4 XII.5.2(iii) and XIV.1.2. On a quasi-compact base, for an invertible prime and a fixed exponent, the finite-coefficient relative Künneth isomorphisms exist simultaneously and are natural for the actual factor maps. The construction is tested on geometric stalks, where freeness follows from the integral fibre calculation and reduction. |
| [`HarrisCMGeometricCoefficientProjectorStatement`](../../Langlands/Shimura/PEL/HarrisTaylorCMCoefficientProjectorStatement.md) | Harris–Taylor III.1–2, pp. 90–91 and 94–99, and Harris 1999, proof of Theorem 5.7(i). At a represented small level the cohomology with the specified irreducible algebraic coefficients, extended from \(K_\lambda\) to its algebraic closure, is a Galois-equivariant product of projected images of actual universal abelian powers. One PEL and permutation expression follows the factorwise multiplication selector. For ordinary scalar exponent \(-w\), the right-frame exponent is \(w\). The shift \(m\) and positive cyclotomic twist \(t\) satisfy \(2t-m=w\). |

The compact-probe sheaf comparisons concern the Hausdorff fixed-field
sites and ordinary global cohomology. Corollary 1.5.2(i) supplies the
separate étale compact-support statement. The geometric coefficient
statement concerns one level and retains comparison with Hecke pullback
and transfer as a further input. The accompanying
[`AbelianPowerGaloisOperators`](../../Langlands/Shimura/PEL/AbelianPowerGaloisOperators.md)
constructs the actual multiplication, algebra and permutation pullbacks
from the componentwise universal abelian schemes.

## Published modules

| Module | Declarations | Content |
| --- | --- | --- |
| [`Langlands.Representation.CompactCoefficient.SplittingStatement`](../../Langlands/Representation/CompactCoefficient/SplittingStatement.md) | `Langlands.CompactCoefficientSplittingStatement` | An irreducible smooth complex representation whose matrix coefficients are compactly supported splits off every smooth representation, as a subrepresentation and as a quotient (Bernstein–Zelevinsky 2.42–2.44). Input to supercuspidal `Ext` vanishing. |
| [`Langlands.Cohomology.InverseLimit.Statement`](../../Langlands/Cohomology/InverseLimit/Statement.md) | `InverseLimitComparisonStatements` (5 components) | Mittag-Leffler closure, exactness of limits, inverse limits of cohomology, and `FiniteCohomologyInverseLimitStatement`: the specialization in which the transition maps are surjective in every degree and each cohomology group is finite, meaning a finite underlying set (EGA 0_III 13.1–13.2). |
| [`Langlands.Cohomology.SpectralSequence.ConcentrationStatement`](../../Langlands/Cohomology/SpectralSequence/ConcentrationStatement.md) | `SpectralSequenceConcentrationStatements` (4 components) | Page-two isomorphisms propagate; one-column, one-row and one-position concentration persists on later finite pages (EGA 0_III 11.1). |
| [`Langlands.Cohomology.AcyclicResolution.Statement`](../../Langlands/Cohomology/AcyclicResolution/Statement.md) | `AcyclicResolutionComparisonStatements` (6 components) | Acyclic resolutions compute right derived functors, independently of choices, naturally and equivariantly (Tohoku 2.4, Cartan–Eilenberg V.1). |
| [`Langlands.Cohomology.FilteredColimit.Statement`](../../Langlands/Cohomology/FilteredColimit/Statement.md) | `FilteredColimitComparisonStatements` (5 components) | Filtered colimits are exact and commute with cohomology, with equivariance. Used for Harris 1999 (2.6)–(2.7). |
| [`Langlands.Sheaf.Godement.ExactnessStatement`](../../Langlands/Sheaf/Godement/ExactnessStatement.md) | `GodementExactnessStatements` (7 components), with the constructed augmentation and fibre retraction | Iterated-cokernel resolutions and exactness of their term functors; split resolution on fibres (SGA 4 XVII 4.2.2–4.2.3). |
| [`Langlands.Cohomology.Flasque.Statement`](../../Langlands/Cohomology/Flasque/Statement.md) | `FlasqueGodementCohomologyStatements` (8 components) | On topological spaces: Godement terms are flasque, flasque sheaves are acyclic for ordinary and compactly supported cohomology, and Godement complexes compute both (Tohoku 3.3). On small étale sites of schemes: the geometric-point Godement terms are acyclic and compute ordinary étale cohomology (`EtaleGodementTermAcyclicStatement`, `EtaleGodementComputesCohomologyStatement`; SGA 4 V 4.1, XVII 4.2.3). No compactly supported étale statement is made. |
| [`Langlands.Cohomology.ProPInvariants.Statement`](../../Langlands/Cohomology/ProPInvariants/Statement.md) | `ProPInvariantTruncationStatements` (3 components), with `invariantsInclusion` | Invariants of a pro-`p` group are exact on smooth representations over rings in which `p` is a unit; the invariant subcomplex computes cohomology when the group acts trivially on it; cycles of an acyclic resolution are acyclic beyond the cohomological dimension (Harris 1999 p.305). |
| [`Langlands.Cohomology.OperatorSpace.Statement`](../../Langlands/Cohomology/OperatorSpace/Statement.md) | `OperatorSpaceCohomologyStatements` (8 components) | Equivariant sheaves of modules on an ordinary topological space with operators, for a group without topology: injectives, derived sections with group action, the comparison with group cohomology for acyclic sheaves, and for finite groups with invertible order the comparison with invariants; compact-support analogues (Tohoku V 5.1–5.2; Berkovich Cor. 1.5.2(i)). These are special consequences of the spectral sequences of Tohoku Thm. 5.2.1 and, in ordinary-topological form, of Berkovich Cor. 1.5.2(i); Berkovich's analytic étale sites are not used, and the analytic étale versions are not stated. The spectral sequences themselves are not stated as such. In derived form they follow from the statements of `EquivariantComposite.Statement` together with those of `HyperextConvergence.HalfBoundedStatement` (rows below), Berkovich's only for compact groups. |
| [`Langlands.Cohomology.EquivariantGodement.Statement`](../../Langlands/Cohomology/EquivariantGodement/Statement.md) | `EquivariantGodementStatements` (3 components), with `EquivariantGodement.augmentationMap` | For a discrete group acting by homeomorphisms on a topological space, the equivariant Godement construction: the degree-zero functor is exact; the complex has the ordinary Godement complex as underlying complex, compatibly with the augmentations; and it computes the derived functors of global sections and of compactly supported sections, as representations of the group. |
| [`Langlands.Cohomology.HyperextDegeneration.Statement`](../../Langlands/Cohomology/HyperextDegeneration/Statement.md) | `HyperextDegenerationStatement`, with `HyperextDegeneration.edgeMap` | In an abelian category: if `K` in the derived category has bounded-above cohomology and `Ext^i(H^k K, W)` vanishes for all `i > 0` and all `k`, then the edge map `Hom(K, W[n]) → Hom(H^{-n} K, W)` is bijective for every `n`. |
| [`Langlands.Cohomology.SupercuspidalExt.Statement`](../../Langlands/Cohomology/SupercuspidalExt/Statement.md) | `SupercuspidalExt.SupercuspidalExtStatements` (3 components), with `SupercuspidalExt.restriction`, `SupercuspidalExt.compactInduction` and `SupercuspidalExt.HasCompactCoefficients` | With the smooth `Ext`: `Ext` reciprocity for compact induction from an open subgroup; an irreducible smooth complex representation with compactly supported matrix coefficients is injective and projective; and higher `Ext` from a compactly induced representation into a representation whose restriction to the open subgroup is a finite sum of such representations vanish (Harris 1997 p.96; Harris 1999 p.312; Bernstein–Zelevinsky 2.29, 2.44, 3.26). |
| [`Langlands.Cohomology.SupercuspidalExtCharZero.Statement`](../../Langlands/Cohomology/SupercuspidalExtCharZero/Statement.md) | `SupercuspidalExtCharZero.SupercuspidalExtCharZeroStatements` (3 components), with `SupercuspidalExtCharZero.HasCompactCoefficients` | The same three statements over an arbitrary field `k` of characteristic zero: `Ext` reciprocity taken over `k`, injectivity and projectivity of irreducible representations with compactly supported matrix coefficients, and the vanishing of higher `Ext`. The group is locally profinite, σ-compact and unimodular. At `k = ℂ`, for a group in `Type`, the conjunction is the published complex one (`supercuspidalExtStatements_of_charZero`). Sources: Vignéras 1996 I.7 and II.3.9; Harris 1999 (4.10.1) and p.312. |
| [`Langlands.Cohomology.SmoothCompactCohomology.Statement`](../../Langlands/Cohomology/SmoothCompactCohomology/Statement.md) | `SmoothCompactCohomology.SmoothCompactCohomologyStatements` (2 components) | A topological group acts on a space by homeomorphisms. For a smooth equivariant module sheaf, in the sense of the `IsSmoothSheaf`, the compactly supported global sections form a smooth representation; this first component is proved (see [Proved statements](#proved-statements)). On a locally compact Hausdorff space, compactly supported Godement cohomology is smooth in every degree. This is the ordinary-topological analogue of the smoothness in Berkovich Cor. 1.5.2(i) and of Harris 1999 p.305. |
| [`Langlands.Cohomology.SmoothCompactComparison.Statement`](../../Langlands/Cohomology/SmoothCompactComparison/Statement.md) | `SmoothCompactComparison.SmoothCompactComparisonStatements` (2 components) | On a locally compact Hausdorff space with the `HasStableNeighbourhoods`, injective smooth sheaves have no higher compactly supported Godement cohomology. Moreover, in every degree the derived compact sections of smooth sheaves (`SmoothSheafCohomology.compactDerived`), as representations, are naturally isomorphic to compactly supported Godement cohomology, and the isomorphism in degree zero is the canonical one. Compatibility with connecting maps is not stated. Analogue of the isomorphisms `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)` of Berkovich Cor. 1.5.2(i). |
| [`Langlands.Cohomology.SmoothGodement.Statement`](../../Langlands/Cohomology/SmoothGodement/Statement.md) | `SmoothGodement.SmoothGodementStatements` (4 components) | the smooth Godement construction under `HasStableNeighbourhoods`: the degree-zero functor `Godement.smoothZeroFunctor` and every term functor of the complex are additive and exact. On a locally compact Hausdorff space every term of `Godement.smoothComplex F` has no higher compactly supported Godement cohomology and is acyclic for `SmoothSheafCohomology.compactDerived`. Sources: Harris 1999 p.304, Fact 3 and the compact-support acyclicity of `F(T)`; Berkovich §1.5 (ii) and Prop. 1.5.1. |
| [`Langlands.Cohomology.SmoothGodementComparison.Statement`](../../Langlands/Cohomology/SmoothGodementComparison/Statement.md) | `SmoothGodementComparison.SmoothGodementComparisonStatements` (3 components), with `SmoothGodementComparison.comparisonMap` | Under the `HasStableNeighbourhoods G X`, which every declaration of the module assumes: for a smooth sheaf `F`, an injective resolution `I` of `F` and a chain map from `Godement.smoothComplex F` to `I` compatible with the augmentations, `comparisonMap` goes from the `SmoothGodementCohomology.smoothGodementCompactCohomology` to `SmoothSheafCohomology.compactDerived`. In degree zero it is the composite of the canonical identifications with compact sections; this component assumes no Hausdorff or local-compactness hypothesis. On a locally compact Hausdorff space every comparison map is an isomorphism, and the comparison maps are the components of natural isomorphisms. Sources: Harris 1999 Lemma 2.2 and (2.3), pp.304–305; the proof of Berkovich Cor. 1.5.2(i), p.12. |
| [`Langlands.Cohomology.SupercuspidalExtSemisimple.Statement`](../../Langlands/Cohomology/SupercuspidalExtSemisimple/Statement.md) | `SupercuspidalExtSemisimple.SupercuspidalExtSemisimpleStatements` (3 components), with `SupercuspidalExtSemisimple.IsIrreducible` and `SupercuspidalExtSemisimple.HasCompactCoefficients` | The `SupercuspidalExtCharZero` statements over a commutative semisimple `ℚ`-algebra `A`, such as Harris's `L_ℓ = L ⊗_ℚ ℚ_ℓ`. Irreducibility is simplicity of the subrepresentation lattice; coefficients are taken against `A`-linear dual vectors. At a field of characteristic zero the conjunction is the published one (`supercuspidalExtCharZeroStatements_of_semisimple`). Sources: Harris 1999 p.306, Prop. 4.10 p.311, p.312. |
| [`Langlands.Cohomology.SupercuspidalRestriction.Statement`](../../Langlands/Cohomology/SupercuspidalRestriction/Statement.md) | `SupercuspidalRestriction.CompactModCenterRestrictionStatement`; `SupercuspidalRestriction.GLSupercuspidalRestrictionStatements` (3 components), with `SupercuspidalRestriction.unitDeterminantSubgroup` | The hypothesis of the vanishing statements. In general: for an open normal subgroup `H` with `H ∩ Z(G)` compact and `Z(G) H` of finite index, an irreducible representation with coefficients compact modulo the center restricts to `H` as a finite sum of irreducible representations with compactly supported coefficients. For `GL_n(F)` and `G° = {g | det g ∈ O_F^×}`: the properties of `G°` (BZ 3.20), Harish-Chandra's theorem in the direction supercuspidal ⇒ compact modulo the center (BZ 3.21), and the finite decomposition of the restriction (BZ 3.21, 3.26). `glSupercuspidalRestriction_of_compactModCenter` proves the last from the others, given total disconnectedness and σ-compactness of `GL_n(F)`. Source of the use: Harris 1997 p.96 (`GJ^0`). |
| [`Langlands.Cohomology.EtaleGaloisSmooth.Statement`](../../Langlands/Cohomology/EtaleGaloisSmooth/Statement.md) | `EtaleGaloisSmooth.GaloisCohomologySmoothStatement` | For an algebraic extension `L/K` and a quasi-compact quasi-separated `X → Spec K`, the action of `L ≃ₐ[K] L` on étale cohomology of `X_L` with constant coefficients is smooth for the Krull topology. Truth argument: SGA 4 VII 5.7–5.8. The Markdown shows that algebraicity and quasi-compactness cannot be dropped. Finite-level input to the continuity of the `λ`-adic representations of Harris 1999 §5. |
| [`Langlands.Cohomology.EtaleGaloisUnramified.Statement`](../../Langlands/Cohomology/EtaleGaloisUnramified/Statement.md) | `EtaleGaloisUnramified.GaloisCohomologyUnramifiedStatement` | For a number field `K`, a morphism of finite type `X → Spec K`, a finite `R`-module `M` and a degree `n`: the action of `Gal(K̄/K)` on `H^n(X_K̄, M)` with constant coefficients is unramified (`DecompositionGroupAction.IsUnramifiedAt`: the inertia subgroup of the absolute Galois group of `K_v` acts trivially) at every finite place `v` outside a finite set, which may depend on `M` and `n`. Truth argument: spreading out (Stacks 01ZM), SGA 4½ [Th. finitude] 1.9, SGA 4 IX 2.4 and 2.2, SGA 1 V 8.2. Finite-coefficient input to the almost-everywhere unramified association of Harris 1999 §5; no set of places uniform in the torsion level, so no `λ`-adic statement. |
| [`Langlands.Cohomology.EtaleGaloisGoodReduction.Statement`](../../Langlands/Cohomology/EtaleGaloisGoodReduction/Statement.md) | `EtaleGaloisGoodReduction.GaloisCohomologyGoodReductionStatement` | For a number field `K` and a smooth proper `X → Spec K`: there is one finite set `S` of finite places such that for every finite `R`-module `M`, every degree `n` and every finite place `v ∉ S` at which the order of `M` is a unit, the same Galois action on `H^n(X_K̄, M)` is unramified at `v`. The set `S` does not depend on `M` or `n`, as an `ℓ`-adic limit requires. A test file proves that it implies `GaloisCohomologyUnramifiedStatement` for smooth proper `X`. Truth argument: spreading out to a smooth proper model (Stacks 01ZM, 0C0C, 081F), SGA 4 XVI Cor. 2.2, SGA 1 V 8.2. |
| [`Langlands.Cohomology.HarrisCMCohomology.Statement`](../../Langlands/Cohomology/HarrisCMCohomology/Statement.md) | `HarrisCMCohomology.HarrisCMCohomologyStatements` (2 components: `HarrisCMCohomology.HarrisCMCohomologyFiniteStatement` and `HarrisCMCohomology.HarrisCMGaloisCohomologySmoothStatement`) | For a small CM level `U`, the geometric CM scheme `X̄_U = X_U ×_{Spec F} Spec F̄` and the `r`-th stage `B_r` of the torsion coefficient system pulled back to `X̄_U`: every `H^d(X̄_U, B_r)` is finite, and the action of `F̄ ≃ₐ[F] F̄` on it (`cmHarrisGeometricGaloisCohomologyAction`) is smooth for the Krull topology. All objects take a proof `q` of `CMRepresentabilityStatement` and further premises; `q` is unproved; the Library proves `square`, `existence` and `geometry` (`mumfordBundlePicardZero`, `relativeDualSchemeExistence`, `relativeDualSchemeGeometry`), and `hRigid` follows from `cmSmallLevelRigidity` by `CMSmallLevelRigidityStatement.rigid`; the Markdown lists published proofs of the other thirteen. Truth arguments: SGA 4 IX 2.3–2.4 and XIV Cor. 1.2 (finiteness); SGA 4 VII 5.7–5.8 (smoothness). Analogues, at one level and one torsion stage, of the finiteness used in the proof of Harris 1999 Prop. 4.10 (p.312), and of the continuity of the Galois action that Harris–Taylor 2001 III.2 (p.97) assert and that the `λ`-adic representations of Harris 1999 §5 (p.313) require. |
| [`Langlands.Cohomology.HarrisCMCohomologyUnramified.Statement`](../../Langlands/Cohomology/HarrisCMCohomologyUnramified/Statement.md) | `HarrisCMCohomologyUnramified.HarrisCMCohomologyUnramifiedStatement` | For a small CM level `U` and the same modules `H^d(X̄_U, B_r)`: there is one finite set `S` of finite places of `F` such that for every degree `d`, every torsion stage `r` and every finite place `w ∉ S`, the action `cmHarrisGeometricGaloisCohomologyAction` is unramified at `w` (`DecompositionGroupAction.IsUnramifiedAt`). `S` does not depend on `d` or `r`. A test file derives that outside `S` every geometric Frobenius lift acts by one endomorphism. The same premises as `HarrisCMCohomology`. Truth argument: the coefficient covers have monodromy controlled by the `p`-power torsion of the universal abelian scheme (Harris–Taylor III.1, p.91); spreading out `X_U` and that abelian scheme over `O_F[1/N]` (Stacks 01ZM, 0C0C, 081F, 03H0); SGA 4 XV 2.1 and XVI 2.1; SGA 1 V 8.2. Fixed-level, torsion-coefficient input to the almost-everywhere unramifiedness of Harris 1999 §5 (p.313). |
| [`Langlands.Cohomology.HarrisCMLevelGaloisSmooth.Statement`](../../Langlands/Cohomology/HarrisCMLevelGaloisSmooth/Statement.md) | `HarrisCMLevelGaloisSmooth.HarrisCMLevelGaloisSmoothStatement` | For a commutative ring `R`, the Library's `cmSmallLevelGaloisCohomologyFunctor` sends a sheaf `M` of `R`-modules on the small étale site of `Spec F` to the colimit, over all sufficiently small CM levels `U`, of `H^d(X̄_U, p_U^* M)`, where `p_U : X̄_U → Spec F` is the structure map. The statement: for every degree `d`, every `M` and every class of this colimit, some open subgroup of `F̄ ≃ₐ[F] F̄` (Krull topology) fixes the class under the Library's Galois action. There is no finiteness, torsion or characteristic hypothesis on `R`. The objects take `q` and eighteen further premises; `q` is unproved; the Library proves `square`, `existence` and `geometry` (`mumfordBundlePicardZero`, `relativeDualSchemeExistence`, `relativeDualSchemeGeometry`), and `hRigid` follows from `cmSmallLevelRigidity` by `CMSmallLevelRigidityStatement.rigid`; the Markdown lists published proofs of the other fourteen. Truth argument: SGA 4 VII 5.1 and Cor. 5.8 at each level. Analogue, for coefficients pulled back from `Spec F` and discrete modules, of the continuity of the Galois action on `H^i(X, L_ξ) = lim_{→U} H^i(X_U ×_F F^ac, L_ξ)` in Harris–Taylor 2001 III.2 (pp.96–97). |
| [`Langlands.Cohomology.HarrisCMLevelInvariants.Statement`](../../Langlands/Cohomology/HarrisCMLevelInvariants/Statement.md) | `HarrisCMLevelInvariants.HarrisCMLevelInvariantsStatement` | For a commutative ring `R`, a level-trivial coefficient diagram `coeff` of étale `R`-module sheaves on the geometric CM tower `U ↦ X̄_U`, and sufficiently small levels `V ≤ U` with `V` normal in `U`, such that the transition of `coeff` along `V ≤ U` is an isomorphism and the index `[U : V]` is a unit of `R`: in every degree `d`, restriction `H^d(X̄_U, coeff_U) → H^d(X̄_V, coeff_V)` is injective, and its image is the set of classes fixed by the maps of the level arrows `smallCMNormalInverseArrow D U V hVU g : V ⟶ V` (element `g⁻¹`) for all `g ∈ U`. The same premises as `HarrisCMLevelGaloisSmooth`. Truth argument: the theorem that `X̄_V → X̄_U` is a finite étale `U/V`-torsor, and the trace of SGA 4 IX 5.1. Analogue of the comparison `H^i(X_U ×_F F^ac, L_ξ) ≅ H^i(X_V ×_F F^ac, L_ξ)^{U/V}` of Harris–Taylor 2001 III.2 (p.96). |
| [`Langlands.Cohomology.HarrisCMColimitInvariants.Statement`](../../Langlands/Cohomology/HarrisCMColimitInvariants/Statement.md) | `HarrisCMColimitInvariants.HarrisCMColimitInvariantsStatement` | For a `ℚ`-algebra `R` and a level-trivial coefficient diagram on the same tower all of whose transition maps are isomorphisms: at every small level `U` and in every degree `d`, the insertion of `H^d(X̄_U, coeff_U)` into the colimit over all small levels (`RestrictedLevelColimit.ι`) is injective, and its image is the set of classes fixed by `U` under the Library's smooth action of the finite-adelic group (`cmSmallLevelSmoothCohomology`). The same premises. Truth argument: derived from `HarrisCMLevelInvariantsStatement`. This is the step between the comparison of Harris–Taylor 2001 p.96 and the admissibility of `H^i(X, L_ξ)` that they assert on p.97. |
| [`Langlands.Cohomology.HarrisCMPrimeToInvariants.Statement`](../../Langlands/Cohomology/HarrisCMPrimeToInvariants/Statement.md) | `HarrisCMPrimeToInvariants.HarrisCMPrimeToInvariantsStatement` | For `m ≠ 0`, a level `K₀` at the places dividing `m`, a `ℚ`-algebra `R` and a level-trivial coefficient diagram on the same tower all of whose transition maps are isomorphisms: in every degree `d`, the Library's comparison `cmPrimeToCohomologyComparison`, from the colimit over the prime-to-`m` levels `K'` of the cohomology at the small levels `e⁻¹ (K₀ × K')` (`e = cmPrimeToSplit D m hm`) to the colimit over all small levels, is injective, and its image is the set of classes fixed by `factorHom e k` for all `k ∈ K₀`. The same premises. Truth argument: derived from `HarrisCMColimitInvariantsStatement`, using open subgroups without torsion at a prime not dividing `m`. It identifies the cohomology with the level at the places dividing `m` fixed, the kind used in Harris 1999 Prop. 4.10 (p.311), with the `K₀`-invariants of the colimit of Harris–Taylor 2001 p.96. |
| [`Langlands.Cohomology.HarrisCMPrimeToGaloisSmooth.Statement`](../../Langlands/Cohomology/HarrisCMPrimeToGaloisSmooth/Statement.md) | `HarrisCMPrimeToGaloisSmooth.HarrisCMPrimeToGaloisSmoothStatement` | For `m ≠ 0`, a level `K₀` at the places dividing `m` and a commutative ring `R`, the Library's `cmPrimeToGaloisCohomologyFunctor` sends a sheaf `M` of `R`-modules on the small étale site of `Spec F` to the colimit, over the prime-to-`m` levels `K'`, of the cohomology of `M` pulled back to `X̄_{e⁻¹ (K₀ × K')}`. The statement: for every degree `d`, every `M` and every class of this colimit, some open subgroup of `F̄ ≃ₐ[F] F̄` (Krull topology) fixes the class under the Library's Galois action. The same premises; no hypothesis on `R`. Truth argument: at each level `e⁻¹ (K₀ × K')` the Galois operator is that of `HarrisCMLevelGaloisSmoothStatement` (checked in a test file), whose level-wise argument (SGA 4 VII 5.1 and Cor. 5.8) applies. The prime-to-`m` analogue of the Galois continuity in Harris–Taylor 2001 III.2 (pp.96–97), for the tower of Harris 1999 Prop. 4.10 (p.311). |
| [`Langlands.Cohomology.HyperextConvergence.Statement`](../../Langlands/Cohomology/HyperextConvergence/Statement.md) | `HyperextConvergence.HyperextConvergenceStatements` (2 components: `HyperextConvergence.HyperextPageDegenerationStatement` and `HyperextConvergence.HyperextStablePageStatement`) | For a t-structure `t` on a triangulated category `C` and objects `K` and `B` with `K` in `t`-degrees `≥ a` and `≤ b`: on every page `r` with `r ≥ 2` and `r ≥ b - a + 2` of the `hyperextSpectralSequence t K B`, every differential vanishes, and the object in position `(p, q)` is isomorphic to the graded piece `gr^p` (`HyperextAbutment.graded t K B (p + q) p`) of the filtration of `Hom(K, B⟦p + q⟧)` by truncations of `K`. Only existence of the isomorphisms is asserted. Source: Cartan–Eilenberg 1956 XVII §2 (4) and §3 Case 1 and (4), pp.368–370, as a derived reformulation; it is the convergence behind the arrows `⇒` of Harris 1999 (4.4.1) and (4.10.1). |
| [`Langlands.Cohomology.EquivariantComposite.Statement`](../../Langlands/Cohomology/EquivariantComposite/Statement.md) | `EquivariantComposite.EquivariantCompositeStatements` (2 components: `EquivariantComposite.EquivariantGlobalCompositeStatement` and `EquivariantComposite.CompactGroupCompactCompositeStatement`), with `EquivariantComposite.trivialSmoothRep` | The derived invariant sections are, naturally in the sheaf, the morphisms in the derived category of representations from the trivial representation `R` in degree `0` to the `n`-th shift of the derived section complex. For ordinary sections (the `invariantGlobalDerived` and `globalComplex`), any group acting on a topological space by homeomorphisms and equivariant sheaves of `R`-modules: Tohoku V Thm 5.2.1 with (5.2.2), in composite-functor form. For compact supports (the `invariantCompactDerived` and `compactComplex`), a compact topological group with `HasStableNeighbourhoods G X`, smooth sheaves on an ordinary topological space and smooth representations: the ordinary-topological analogue of Berkovich Cor. 1.5.2(i), in composite-functor form (Berkovich's analytic étale site is not used). The isomorphisms are additive and only their existence is asserted. The spectral sequences follow with the next row. Berkovich's manuscript asserts the spectral sequence for every topological group; the Markdown proves that it fails for `G = ℤ` acting on `X = ℤ` by translation, hence the compactness hypothesis. |
| [`Langlands.Cohomology.HyperextConvergence.HalfBoundedStatement`](../../Langlands/Cohomology/HyperextConvergence/HalfBoundedStatement.md) | `HyperextConvergence.HyperextHalfBoundedConvergenceStatements` (2 components: `HyperextConvergence.HyperextHalfBoundedDifferentialStatement` and `HyperextConvergence.HyperextHalfBoundedStablePageStatement`); `HyperextConvergence.CovariantSecondPageStatement` | Convergence in Cartan–Eilenberg's Case 1: for a t-structure `t` on a triangulated category, `K` in `t`-degrees `≤ b` and `B` in `t`-degrees `≥ c`, on page `r` of `hyperextSpectralSequence t K B` with `r ≥ 2`, `r ≥ p - c + 1` and `r ≥ q + b + 2`, the differentials into and out of position `(p, q)` vanish, and the object there is isomorphic to `gr^p` of `Hom(K, B⟦p + q⟧)`. The covariant form, in the opposite of the derived category `D(C)` of an abelian category with `opTStructure` of the standard t-structure, applied to `op K` and `op A` for `A` in degree `0`: page 2 in position `(p, q)` is additively equivalent to `Ext^p(A, H^q(K))` for `p ≥ 0` and is zero for `p < 0`, and the abutment in degree `n` to `Hom(A, K⟦n⟧)`. Only existence of the isomorphisms is asserted. The Markdown's Application section combines them with the previous row: Tohoku's `H^p(G, H^q(X, A)) ⇒ H^n(X; G, A)` (Thm 5.2.1, (5.2.5), p.200), with `H^p(G, -)` read as `Ext^p` from the trivial representation, and Berkovich's `H^p(G, H^q_c) ⇒ H^{p+q}_c` (Cor. 1.5.2(i)) for compact `G` on ordinary topological spaces. Source: Cartan–Eilenberg 1956 XVII §2 (4) and §3 Case 1, pp.368–370. |
| [`Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.Statement`](../../Langlands/Cohomology/AnalyticQuasiEtaleGlobalComparison/Statement.md) | `AnalyticQuasiEtaleGlobalComparison.AnalyticQuasiEtaleGlobalComparisonStatement` | For a complete ultrametric normed field `K`, an analytic space `X` of the `LocalizedCategory`, a topological group `G` acting on `X` by `ρ : G →* Aut X`, and a commutative ring `R`: if `X` is compact and Hausdorff (`IsCompactSpace X`) and the action is continuous (`IsContinuousAction ρ`), then for every `q` the comparison `quasiEtaleComparison ρ R q : H^q(X{G}, F) → H^q(X, b^*F)` is an isomorphism of functors on quasi-étale `G`-sheaves of `R`-modules (`IsIso`). The definition has the instance binders `Small G` and `HasFiniteEquivariantRefinements` for `compactLiftSystem ρ`, which the source category needs; the refinement instance is still a premise. Two of the three geometric inputs to the construction of it have proofs (see [Published steps toward open components](#published-steps-toward-open-components)). Source: Berkovich Thm 1.6.1(ii), p.13, quasi-étale case. Part (i) is the paracompact row below; the spectral sequence of (ii) was not in the Library at `b47a2385` (its compact-base form was in preparation), and part (iii) is not stated. The étale case is the next row. Proved, as `analyticQuasiEtaleGlobalComparison` (see [Proved statements](#proved-statements)). |
| [`Langlands.Cohomology.AnalyticEtaleGlobalComparison.Statement`](../../Langlands/Cohomology/AnalyticEtaleGlobalComparison/Statement.md) | `AnalyticEtaleGlobalComparison.AnalyticEtaleGlobalComparisonStatement` | The étale case of the previous row, with the same `K`, `X`, `G`, `ρ` and `R`: if `X` is compact and Hausdorff (`IsCompactSpace X`) and `IsContinuousAction ρ` holds, then for every `q` the comparison `etaleComparison ρ R q : H^q(X{G}, F) → H^q(X, b^*F)` is an isomorphism of functors on étale `G`-sheaves of `R`-modules (`IsIso`). The instance binders are `Small G` and `HasAdmissibleRefinements` for `distinguishedLiftSystem ρ` and `twistedEtaleTopology ρ`; The construction derives the latter from three conditions that are not proved in the Library (see [Published constructions used](#published-constructions-used)). Source: Berkovich Thm 1.6.1(ii), p.13, étale case. Part (i) is the paracompact row below; the spectral sequence of (ii) was not in the Library at `b47a2385`, and part (iii) is not stated. This note records no proof. |
| [`Langlands.Cohomology.AnalyticGlobalComposite.Statement`](../../Langlands/Cohomology/AnalyticGlobalComposite/Statement.md) | `AnalyticGlobalComposite.AnalyticEtaleGlobalCompositeStatement`; `AnalyticGlobalComposite.AnalyticQuasiEtaleGlobalCompositeStatement`, with `AnalyticGlobalComposite.trivialSmoothRep` | Berkovich's `Γ_{X(G)} = (-)^G ∘ Γ_{X{G}}` (§1.2, pp.4–5) in composite-functor form on the analytic sites, with the same `K`, `X`, `G`, `ρ` and `R` and the instance binders of the two comparison rows. For every model of the derived category of smooth representations of `G` over `R` and every `n`, there are additive isomorphisms `H^n(X(G), F) ≅ Hom(R, RΓ(X{G}, F)⟦n⟧)`, natural in `F`: on the left the derived invariant sections (`etaleGSheafInvariantCohomology`, `quasiEtaleGSheafInvariantCohomology`), on the right morphisms in `D(SmoothRep R G)` from the trivial representation in degree `0` to the section complex (`etaleGSheafComplex`, `quasiEtaleGSheafComplex`). Neither compactness, a Hausdorff property nor continuity of the action is assumed, and no points or supports are involved. Only existence of the isomorphisms is asserted. Analytic counterpart of the global component of `EquivariantComposite.Statement`; with the convergence rows above it gives Berkovich's spectral sequence `H^p(G, H^q(X{G}, F)) ⇒ H^{p+q}(X(G), F)`, which is stated in the `AnalyticGlobalSpectralSequence.Statement` row below. Both the étale and the quasi-étale statement are proved (see [Proved statements](#proved-statements)). |
| [`Langlands.Cohomology.AnalyticEtaleCompactComparison.Statement`](../../Langlands/Cohomology/AnalyticEtaleCompactComparison/Statement.md) | `AnalyticEtaleCompactComparison.AnalyticEtaleCompactComparisonStatement` | Berkovich Cor. 1.5.2(i), pp.11–12, first assertion, étale case. With `K`, `X`, `G`, `ρ`, `R` and the instance binders of the étale comparison row, and a normed field `L` over `K` whose `L`-valued points of `X` (the `localizedFieldPointFunctor L`) satisfy the `EtaleSite.PointAxioms` (`h`): if the underlying space of `X` is Hausdorff, every point of it underlies an `L`-valued point (`Function.Surjective (pointProjection L X)`) and `IsContinuousAction ρ` holds, then for every `q` the comparison `etaleCompactComparison L ρ h R q : H^q_c(X{G}, F) → H^q_c(X, b^*F)` is an isomorphism of functors on étale `G`-sheaves of `R`-modules. The Library's compact supports are taken in `L`-valued points; the Markdown shows the map is not an isomorphism in general without the surjectivity, which makes these supports agree with Berkovich's. The second assertion (smoothness) is the conditional theorem (see the paragraph below). The spectral sequence is not in this pin; its compact-base case was in preparation at `b47a2385`. The quasi-étale case is not stated. The Library has only the conditional proof `compactComparison_of_openDomains_of_openMap_of_compactAcyclic`. |
| [`Langlands.Cohomology.AnalyticGlobalSpectralSequence.Statement`](../../Langlands/Cohomology/AnalyticGlobalSpectralSequence/Statement.md) | `AnalyticGlobalSpectralSequence.AnalyticEtaleGlobalSpectralSequenceStatement`; `AnalyticGlobalSpectralSequence.AnalyticQuasiEtaleGlobalSpectralSequenceStatement`, with `AnalyticGlobalSpectralSequence.spectralSequence` and the predicate `AnalyticGlobalSpectralSequence.FirstQuadrantAbutmentStatement` | Berkovich §1.2, pp.4–5: the spectral sequence `H^p(G, H^q(X{G}, F)) ⇒ H^{p+q}(X(G), F)`, on the étale and quasi-étale `G`-sheaves of `R`-modules, with the parameters and instance binders of the composite row and the hypothesis `IsContinuousAction ρ`. For a model of `D(SmoothRep R G)` at morphism universe `w`, the sequence is the covariant hyperext spectral sequence of the trivial representation `R` and the image `D` of the model's derived smooth sections `RΓ(X{G}, F)`. Each proposition asserts, objectwise and additively, that page 2 at `(p, q)` is `Ext^p(R, H^q(X{G}, F))` in smooth representations (derived smooth invariants), and the predicate: first-quadrant vanishing on page 2, a finite truncation filtration in each nonnegative total degree, stable pages for `r ≥ max(2, p+1, q+2)`, and the abutment in degree `n` identified with the model's derived invariant sections `H^n(X(G), F)`. Both derived functors are those of the Library models; no transfer through Theorem 1.4.2 to the manuscript's sites is asserted. The quasi-étale version uses `twistedQuasiEtaleTopology`. First appeared at `2d12bd93` |
| [`Langlands.Cohomology.AnalyticParacompactComparison.Statement`](../../Langlands/Cohomology/AnalyticParacompactComparison/Statement.md) | `AnalyticParacompactComparison.AnalyticEtaleParacompactComparisonStatement`; `AnalyticParacompactComparison.AnalyticQuasiEtaleParacompactComparisonStatement`, with the comparison maps `etaleRestrictedSectionsComparison` and `quasiEtaleRestrictedSectionsComparison` | Berkovich Thm 1.6.1(i), pp.13–14, étale and quasi-étale cases: if the underlying space of `X` is Hausdorff and paracompact and `IsContinuousAction ρ` holds, then for every `q` the comparison `R^q(Γ(X, -) ∘ b^*) ⟶ H^q(X, -) ∘ b^*` of functors on `G`-sheaves is an isomorphism. The comparison is the Library's `ExactBaseChange.compComparisonNatTrans` along the exact restriction `b^*`; it concerns ordinary global sections after restriction, not smooth or compactly supported sections. Same `K`, `X`, `G`, `ρ`, `R`, smallness and refinement binders as the comparison rows. First appeared at `2d12bd93` |
| [`Langlands.Sheaf.Equivariant.AnalyticEtaleToposComparison.Statement`](../../Langlands/Sheaf/Equivariant/AnalyticEtaleToposComparison/Statement.md) | `EtaleGSheafToposComparisonStatement`, with `OpenQuotientsSmall`, `EtaleInverseImageSmooth`, `etaleSmoothInverseImageAdjunction` and `etaleGSheafEquivalenceOfStatement` | Berkovich Thm 1.4.2, pp.8–10, étale case, for sheaves of `R`-modules. For a `G`-space `X` (the `GSpace`) and the hypothesis `hX : HasImagePullbacks (EquivariantEtaleSite.toEtaleSite X)`, the inverse image `b^*` and invariant sheaf `(b_*-)^G` are adjoint. If every quotient of `G` by an open subgroup is `v`-small (`OpenQuotientsSmall`, needed for the induced spaces `U_{G/N}`), the proposition asserts that `b^*` of every sheaf on `X(G)_ét` is a smooth `G`-sheaf. It further asserts that the adjunction restricted to smooth `G`-sheaves has invertible unit and counit. `etaleGSheafEquivalenceOfStatement` only packages the resulting equivalence from a proof of the proposition. This étale comparison for module sheaves first appeared at `2d12bd93`. |
| [`Langlands.Sheaf.Equivariant.AnalyticEtaleEquivariantCompactGlobal`](../../Langlands/Sheaf/Equivariant/AnalyticEtaleEquivariantCompactGlobal.md) | Constructions: `etaleCompactSectionsRepInclusion`, `isIso_etaleCompactSectionsRepInclusion_of_compactSpace`, `etaleGSheafCompactSectionsIsoOfCompactSpace`, `etaleGSheafInvariantCompactSectionsIsoOfCompactSpace`, `etaleGSheafCompactCohomologyIsoOfCompactSpace`, `etaleGSheafInvariantCompactCohomologyIsoOfCompactSpace`, `etaleGSheafCompactComplexIsoOfCompactSpace` | Internal construction for compact bases, not a numbered source result. It takes `K`, `X`, `G`, `ρ` and `R` as in the comparison rows, a normed field `L` with `NormedAlgebra K L`, and `h`, the `EtaleSite.PointAxioms L x` for every `L`-valued point `x` of `X`, which define the Library's compact supports. Forgetting compact support is an equivariant map from compactly supported to ordinary sections of the restriction. When the underlying space of `X` is compact (`CompactSpace`) and `pointProjection L X` is surjective, it is invertible. The derived stages, from the isomorphisms of cohomology on, also use the instances `Small G` and `HasAdmissibleRefinements` for `distinguishedLiftSystem ρ` and `twistedEtaleTopology ρ`; the complex isomorphism also uses a model `HasDerivedCategory` of smooth representations. The module derives isomorphisms of smooth and invariant compact sections with their ordinary counterparts, natural isomorphisms of all right-derived functors, and, sheaf by sheaf, an isomorphism of the compact and ordinary derived smooth section complexes. No continuity of the action is used. First appeared at `2d12bd93` |
| [`Langlands.Shimura.PEL.HarrisTaylorCMHarrisVanishingStatement`](../../Langlands/Shimura/PEL/HarrisTaylorCMHarrisVanishingStatement.md) | `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.CMHarrisVanishingStatement` | Harris 1999 (5.1), p.312: `H^i(S_K(N), W)[π] = 0` for `i ≠ n − 1`, on the Library's CM Shimura varieties of Harris's signature with an algebraic coefficient representation `ρ` and a small level `U`. Hypotheses: Harris's condition (R) of Harris 1997, p.79 (at every finite place `w` of `F`, `F_w ⊗_F A` is split or a division algebra); representations `π_f` of `GJ(A_f)` and `ρ'` of `GG(A_f)` related by the published `JacquetLanglands.IsHarrisJacquetLanglandsTransfer`; `π_f` isomorphic to `JacquetLanglands.splitTensor` of a supercuspidal `π_v` (`GeneralLinear.IsSupercuspidal`) at the place `w₀` above the split place and a representation of the complement; and a model `τ` of `ρ'` over a field `M` extending `K_λ`, through a field isomorphism `j : M ≃+* ℂ`. Conclusion: for every `ℓ`, every `λ` over `ℓ` and every degree `d ≠ n − 1`, the `U`-fixed vectors of the `τ`-isotypic part of `H^d(S, W)_λ ⊗_{K_λ} M` (`cmHarrisLambdaTowerIsotypicFixedVectors` of `HarrisTaylorCMLambdaTower`) form a subsingleton. Like the tower, it takes a proof `q` of `CMRepresentabilityStatement` and the premises `existence`, `geometry` and `hRigid` as parameters. The hypotheses are encoded as in the `CMHarrisTheorem57Statement`; the Markdown explains why (R) is needed and why Harris's assumption of many division places is not imposed. Truth argument in the Markdown: Harris 1997 Lemma 4 (pp.82–83). This note records no proof. |
| [`Langlands.Galois.Harris1999Theorem59iiParameterStatement`](../../Langlands/Galois/Harris1999Theorem59iiParameterStatement.md) | `Harris1999Theorem59iiParameterStatement` and `HarrisSupercuspidalRestrictionIrreducibleStatement` | Derived consequences of Harris 1999 Theorem 5.9(ii), pp.314–315. In the setting of (i), with `v` split (`Harris.conjPlace K v ≠ v`), the first chooses a map `Φ` after `K`, the imaginary quadratic subfield `K₀`, `r` and `v`, but before `Π`. For each prime `ℓ` and `ιΩ : ℚ̄_ℓ ≃+* ℂ`, the map takes a smooth class of `GL_{r+1}(K_v)` to a finite-dimensional `ℚ̄_ℓ`-representation of `Gal(K̄_v/K_v)`. For each eligible cuspidal realization and spectral presentation with supercuspidal local component, it asserts one pure, rank-`r + 1`, weakly associated compatible family as in (i). For every `ℓ ≠ p_v` and every compatible continuous embedding of a coefficient completion into `ℚ̄_ℓ`, the restriction of this family's member, extended along that embedding, is equivalent to `Φ ℓ ιΩ (Π_v)`. The second asserts absolute irreducibility at `v` of the restrictions of **every** such pure, rank-`r + 1`, weakly associated compatible family of an eligible class, at all coefficient places of residue characteristic different from `p_v`. Neither statement fixes the witness weight, compares weights for different `Π`, identifies `Φ` with (5.4)–(5.5), or asserts a twist formula. Both are unproved. |

The names in the second column are relative to `Langlands.Cohomology`,
except those of the last row (in `Langlands.GaloisRepresentation`), those
of the two rows on modules in `Langlands.Sheaf.Equivariant` (in
`Langlands.Sheaf.Equivariant.Analytic`), and
`Langlands.CompactCoefficientSplittingStatement` and
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.CMHarrisVanishingStatement`.
In the content column, `Godement.` abbreviates
`Langlands.Sheaf.Equivariant.Godement.`. In the rows on Berkovich's
analytic sites, the constructions (`etaleComparison`, `pointProjection` and the others) are in
the namespace `Langlands.Sheaf.Equivariant.Analytic`, and the (`localizedFieldPointFunctor`, `EtaleSite.PointAxioms`, `IsCompactSpace`,
`IsContinuousAction`) are in `Langlands.Analytic.SaturatedAtlasPresentation`.

The equivariant Godement statements concern the ordinary-topological
construction for a discrete group. They are analogues of Berkovich's
resolution, not statements about Berkovich's `ν_*ν^*` on the equivariant
topos, which has additional coinduction factors. The acyclicity that Harris
1999 p.304 displays for Berkovich's resolution is for compactly supported
cohomology, `H_c^q(U(ẽ)_{F̄}, F(T)) = 0` for `q > 0`; the compactly
supported part of the third component is its analogue.

The four smooth modules treat a topological group, not only a discrete one.
Their sheaves are the smooth equivariant sheaves: sections are locally
fixed by open subgroups. The smooth Godement functor is the ordinary
Godement degree-zero functor of the underlying sheaf, followed by coinduction
and the smooth part. As the `Godement/Smooth.md` explains, it is the
counterpart of Berkovich's `ν_*ν^*`: points of `X` replace geometric points,
and the right adjoint of forgetting replaces `ν_*`. Smooth sheaves are
modelled directly on `X`, so Berkovich's `b^*` is implicit. All four modules
remain on topological spaces; Berkovich's étale and quasi-étale sites of
analytic spaces are not used.

The eight modules of the table from `AnalyticQuasiEtaleGlobalComparison`
to `AnalyticEtaleEquivariantCompactGlobal`, with ten statements and one
construction module, are different:
they are stated on the étale and quasi-étale sites of an analytic
space. The étale and quasi-étale `G`-sheaves stand for
Berkovich's sheaves on `X(G)` through his Theorem 1.4.2. Its étale case for
sheaves of `R`-modules is stated in the `AnalyticEtaleToposComparison`
row but not proved, and no statement transfers the derived functors
along it. Toward it, the [`Langlands.Sheaf.Equivariant.AnalyticInvariantSheaf`](../../Langlands/Sheaf/Equivariant/AnalyticInvariantSheaf.md)
constructs Berkovich's `(b_*F)^G`, from sheaves on the twisted site of `X`
(sheaves on `X` with an action of the discrete group `G`) to sheaves on
`X(G)`, under an image-pullback hypothesis (`HasImagePullbacks`) that is
not proved for any `X`. The [`Langlands.Sheaf.Equivariant.AnalyticInverseImage`](../../Langlands/Sheaf/Equivariant/AnalyticInverseImage.md)
(in the Library at `320321b3`) constructs the inverse
image `b^*` along `b : X → X(G)` as its left adjoint, on the quasi-étale and
on the étale side, and proves Berkovich's colimit formula over
`C(U/X(G))°` before sheafification (§1.2, printed p.3). Its sheaf-level
adjunctions, `quasiEtaleSheafInverseImageAdjunction` and
`etaleSheafInverseImageAdjunction`, take the same hypothesis. Neither
module proves that `b^*E` is a
smooth `G`-sheaf or that the unit and counit are isomorphisms. The `EtaleGSheafToposComparisonStatement` asserts exactly these two facts for
the étale adjunction, assuming `HasImagePullbacks` and `OpenQuotientsSmall`.
It has no proof, so Theorem 1.4.2 is still open. The [`Langlands.Sheaf.Equivariant.AnalyticSetInducedSections`](../../Langlands/Sheaf/Equivariant/AnalyticSetInducedSections.md)
(in the Library at `544dba09`), built on the generic
[`Langlands.Topology.GroupAction.DiscreteGSetFibre`](../../Langlands/Topology/GroupAction/DiscreteGSetFibre.md),
defines Berkovich's `Γ_{X{G}}` (§1.2, printed p.4) directly on sheaves of
`R`-modules on the sites `Qét(X(G))` and `Ét(X(G))`, with values in
smooth representations: it is the fibre of the presheaf `Σ ↦ F(X_Σ(G))` on
`P(G)`. The module proves Berkovich's formula
`Γ_{X{G}}(F) ≅ lim→_N F(X_{G/N}(G))` as an isomorphism of modules. Its
functors take as arguments `hC` and `hD`, proofs of the statements
`SetInducedSpace.ContinuityStatement` and `SigmaDescStatement`. Both
statements have published proofs in namespace
`Langlands.Analytic.SaturatedAtlasPresentation`. The `SetInducedSpace.continuityStatement` is in [`SetInducedSpaceContinuityProof`](../../Langlands/Geometry/Analytic/SetInducedSpaceContinuityProof.md)
(first appeared at `03296177`, the commit of the proof of the quasi-étale comparison).
`sigmaDesc_quasiEtale_etale` is in [`LocalizedSigmaQuasiEtaleProof`](../../Langlands/Geometry/Analytic/LocalizedSigmaQuasiEtaleProof.md)
(first appeared at `95d37e11`; already present at `d6b462be`). Passing these theorems as `hC` and `hD` gives the
functors without further hypotheses. The module constructs
no derived functors. Its relation to the `quasiEtaleGSheafSections`
and `etaleGSheafSections` on smooth `G`-sheaves, with which the statements of
this framework are made, is not formalized, and neither is the transport of
derived functors between the two models. The two comparisons of Theorem 1.6.1(ii) concern ordinary
cohomology on a compact `X`, which involves no supports and no points. The
two composites of §1.2 assume neither compactness nor continuity and involve
no points or supports either. The two spectral sequences of §1.2 and the two
paracompact comparisons of Theorem 1.6.1(i) assume continuity, and the
latter a Hausdorff paracompact `X`; neither involves points or supports.
The support-dropping constructions of `AnalyticEtaleEquivariantCompactGlobal`
use `L`-valued points as below, with a compact underlying space. The étale comparison of Corollary 1.5.2(i)
concerns compact supports. The statement takes them in the `L`-valued points of
`X` for a normed field `L`, so the statement adds that every point of `X`
underlies an `L`-valued point. Corollary 1.5.2(i) concerns only étale sheaves;
no quasi-étale counterpart is stated (see the second entry of
[Retained source gaps and scope decisions](#retained-source-gaps-and-scope-decisions)).
`HarrisTaylorCMHarrisVanishingStatement` is
instead stated on the Library's CM Shimura varieties and their `λ`-adic
cohomology (see the rows on unitary Shimura cohomology and on the split
supercuspidal place under
[Not yet stated](#not-yet-stated-and-the-prerequisites-they-wait-for)).

Published theorems take two of these statements as
hypotheses. In `Langlands.Sheaf.Equivariant.AnalyticRepSmoothness`,
`quasiEtaleComparison_app_bijective_of_statement`,
`quasiEtaleRestrictionCohomologyAction_isSmooth_of_statement` and
`quasiEtaleComparisonSmoothIsoOfStatement` take
`hB : AnalyticQuasiEtaleGlobalComparisonStatement X G ρ R` together with
`hX : IsCompactSpace X` and `hρ : IsContinuousAction ρ`. They give that, for
compact `X` and a continuous action, the comparison is bijective on each
sheaf, that the action of `G` on `H^q(X, b^*F)` is smooth, and an isomorphism
of smooth representations. In
`Langlands.Sheaf.Equivariant.AnalyticEtaleCompactSmoothness`,
`etaleCompactComparison_app_bijective_of_statement`,
`etaleRestrictionCompactCohomologyAction_isSmooth_of_statement`,
`etaleCompactComparisonSmoothIsoOfStatement` and
`etaleRestrictionCompactCohomologyAction_comp_subtype_isSmooth_of_statement`
take `hB : AnalyticEtaleCompactComparisonStatement L X h G ρ R` together with
the Hausdorff property `hT`, the surjectivity `hS` and `hρ`. They give the
same three conclusions for `H^q_c(X, b^*F)`, and smoothness of the
restriction of the action to any subgroup. The smoothness is the second
assertion of Berkovich's Corollary 1.5.2(i). These theorems are conditional:
they are not proofs of the statements. The [`Langlands.Cohomology.DivisibleSystem.DrinfeldLevelOneEtale`](../../Langlands/Cohomology/DivisibleSystem/DrinfeldLevelOneEtale.md)
specializes the four étale
declarations to the model of `ℳ_1 = Ω × Δ` (Harris 1999 §2) for the
matrix factor `GL_{d+1}(F)`, not the full group `G_J`. For example,
`levelOneEtaleRestrictionCompactCohomologyAction_isSmooth_of_statement`
takes the comparison `hB` and surjectivity `hS` as hypotheses, as well as the
point axioms, admissible refinements, `hΩ` (continuity of the action on `Ω`)
and `hSI : SetInducedSpace.ContinuityStatement`. The same module constructs
the constant divisible system and its Godement resolution with the stated
point-family hypotheses; the cohomology identification on the equivariant
site also takes Godement acyclicity and a cohomological degree bound as
hypotheses. At `d6b462be`, `hΩ` was supplied by `omegaActionContinuity`
([`DrinfeldActionContinuityProof`](../../Langlands/Geometry/Analytic/DrinfeldActionContinuityProof.md))
and `hSI` was unproved. At
`b47a2385`, `hSI` is supplied by the universe-polymorphic
`SetInducedSpace.continuityStatement` (first appeared at `03296177`). The comparison `hB` and the surjectivity `hS` remain
hypotheses.
Neither module supplies the spaces `ℳ_N` for `N ≥ 2` or their action data.

The statements of `SupercuspidalExt` have complex coefficients, as Harris 1997
allows after choosing `Q̄_ℓ ≅ ℂ` (p.95). Harris 1999 works over
`L_ℓ = L ⊗ Q_ℓ`, a finite product of fields of characteristic zero.
`SupercuspidalExtCharZero` covers each field factor, and
`SupercuspidalExtSemisimple` covers the product algebra. No category of
representations with a fixed central character is introduced; as in Harris
1997, restriction to the open subgroup `GJ^0` with compact center replaces it.
`SupercuspidalRestriction` states when the restriction hypothesis of the
vanishing statements holds; its application to `GJ^0` is not stated. The
geometric input `H^j_c(M_N) ≅ c-Ind_{GJ^0}^{GJ} H^j_c(R_N)` (Harris 1997
(A.8)) is not stated.

Two further published statements treat the same items of
Bernstein–Zelevinsky 1976 for product Levi subgroups of `GL_n(F)`. There the
determinant-unit subgroup is taken blockwise and the topology is any
compatible `T : F.TopologicalData`. They are the `Langlands.CuspidalSupport.LeviDeterminantUnitStructureTheorem` (BZ
3.20(a)–(b)) and the `Langlands.CuspidalSupport.LeviHarishChandraTheorem`
(BZ 3.21, (1) ⇔ (4): quasicuspidality against compactly supported
coefficients of the restriction to the determinant-unit subgroup).
`SupercuspidalRestriction` instead uses the canonical topology on `GL_n(F)`,
the `IsSupercuspidal`, and the direction (1) ⇒ (3), coefficients
compactly supported modulo the center. No Lean statement relates
`unitDeterminantSubgroup` to `determinantUnitSubgroup`, or
`HasCompactSmoothCoefficientsModCenter` to the coefficient condition on the
determinant-unit subgroup. The theorem
`glSupercuspidalRestriction_of_compactModCenter` takes σ-compactness and total
disconnectedness of `GL_n(F)` as instance arguments. σ-compactness for the
canonical topology is the theorem
`Langlands.PadicField.TopologicalData.generalLinearSigmaCompactSpace` (module
`Langlands.Group.GL.CountabilityProof`), applied to
`F.canonicalTopologicalData`; it is a theorem, not a registered instance. No
public Library declaration proves total disconnectedness. Two proof modules
prove it for their own use in private
theorems named `generalLinearTotallyDisconnected`
(`Representation/Tensor/FactorMatchingProof.lean:270`,
`Representation/CuspidalSupport/LeviAdmissibleFactorizationProof.lean:29`),
and two others derive it inside a proof
(`Representation/Whittaker/DistributionInvarianceProof.lean:108`,
`Representation/GodementJacquet/RegularMatrixZetaOperator.lean:124`).

## Published constructions used

These are constructions with proofs, not theorem statements of this framework.
They are used by the statements above or by some of their proofs, except
the row of `HarrisTaylorCMGeometricNormalActions` and
`HarrisTaylorCMGeometricNormalTorsor`, which is cited only in a truth
argument, and the rows of `AnalyticConstantAdjunction` and
`AnalyticEtaleRefinements`, which concern the open proofs of the analytic
statements and the instance hypothesis of the étale ones, and the row of
`AnalyticSetInducedSections` and `DiscreteGSetFibre`, which defines
Berkovich's `Γ_{X{G}}` on his sites `X(G)` themselves and is not used by any
statement or proof of this framework. The modules that the proofs themselves
import are named in [Proved statements](#proved-statements).

| Module | Objects |
| --- | --- |
| [`Langlands.Sheaf.Equivariant.Godement.Complex`](../../Langlands/Sheaf/Equivariant/Godement/Complex.md) | `Langlands.Sheaf.Equivariant.Godement.complexFunctor`, the equivariant Godement complex built from `zeroFunctor` and `coaugmentation` (`Godement.Zero`) by the iterated-cokernel construction, with its augmentation and the instance `zeroFunctor_additive` |
| [`Langlands.Cohomology.EquivariantDerivedSections`](../../Langlands/Cohomology/EquivariantDerivedSections.md) | `globalDerived` and `compactDerived`, the right derived functors of global and compactly supported sections on equivariant module sheaves, with values in `Rep R G`; `globalDerivedIso` and `compactDerivedIso` compute them from injective resolutions; `invariantGlobalDerived`, the right derived functors of invariant global sections `F ↦ Γ(X, F)^G`, with values in `ModuleCat R` (used by `EquivariantComposite`) |
| [`Langlands.Cohomology.SmoothExt`](../../Langlands/Cohomology/SmoothExt.md) | `Langlands.Cohomology.SmoothExt.ext R G V n`, the right derived functors of `Hom(V, -)` on the abelian category `Langlands.SmoothRep R G`, which has enough injectives |
| [`Langlands.Sheaf.Equivariant.SmoothCompactSupport`](../../Langlands/Sheaf/Equivariant/SmoothCompactSupport.md) | For a topological group, the smooth part of the representation on compactly supported global sections, as a functor to `Langlands.SmoothRep R G`; a degree-zero construction |
| [`Langlands.Sheaf.Equivariant.Godement.Underlying`](../../Langlands/Sheaf/Equivariant/Godement/Underlying.md) | `underlyingComplexIso` and `underlyingComplexIso_augmentation`: the equivariant Godement complex has the ordinary Godement complex as underlying complex, compatibly with the augmentations |
| [`Langlands.Sheaf.Equivariant.Coinduction`](../../Langlands/Sheaf/Equivariant/Coinduction.md) | `coinduction`, right adjoint to forgetting equivariance (`coinductionAdjunction`); it preserves injective objects |
| [`Langlands.Sheaf.Equivariant.Godement.Smooth`](../../Langlands/Sheaf/Equivariant/Godement/Smooth.md) | `smoothForget`, `smoothCoinduction` and their adjunction; the smooth Godement functor `smoothZeroFunctor`, the monic coaugmentation `smoothCoaugmentation`, and the complex `smoothComplexFunctor`, `smoothComplex` |
| [`Langlands.Cohomology.EquivariantGodementCohomology`](../../Langlands/Cohomology/EquivariantGodementCohomology.md) | `globalCohomology` and `compactCohomology`, the cohomology of the equivariant Godement complex after global and compactly supported sections, as representations, with their degree-zero identifications |
| [`Langlands.Sheaf.Equivariant.Smooth`](../../Langlands/Sheaf/Equivariant/Smooth.md) | `IsSmoothSheaf` (sections locally fixed by open subgroups), the full subcategory `SmoothTopologicalSheaf R G X` and its inclusion `smoothInclusion` |
| [`Langlands.Sheaf.Equivariant.SmoothPart`](../../Langlands/Sheaf/Equivariant/SmoothPart.md) | `HasStableNeighbourhoods G X` (small open neighbourhoods stabilized by open subgroups; instances for discrete groups and for non-archimedean groups acting continuously), the smooth part `smoothCoreflector` and `smoothAdjunction` |
| [`Langlands.Sheaf.Equivariant.SmoothAbelian`](../../Langlands/Sheaf/Equivariant/SmoothAbelian.md) | Smooth sheaves form an abelian category with enough injectives |
| [`Langlands.Sheaf.Equivariant.SmoothSheafCompactSections`](../../Langlands/Sheaf/Equivariant/SmoothSheafCompactSections.md) | `CompactSections.isSmooth_representation_of_isSmoothSheaf`, which proves `CompactSectionsSmoothStatement`; the left exact functor `smoothSheafCompactSections` to `Langlands.SmoothRep R G` and `smoothSheafCompactSectionsToRepIso` |
| [`Langlands.Cohomology.SmoothSheafCohomology`](../../Langlands/Cohomology/SmoothSheafCohomology.md) | `compactDerived`, the right derived functors of `smoothSheafCompactSections`, with `compactDerivedZeroIso` and `compactDerivedIso`; the invariant versions `invariantCompactDerived` |
| [`Langlands.Cohomology.EquivariantDerivedComparison`](../../Langlands/Cohomology/EquivariantDerivedComparison.md) | For a group without topology: `globalDerivedForgetIso` and `compactDerivedForgetIso`, the derived sections of an equivariant sheaf have the derived sections of the underlying sheaf as underlying modules |
| [`Langlands.Cohomology.DerivedPlus`](../../Langlands/Cohomology/DerivedPlus.md), [`Langlands.Cohomology.EquivariantDerivedComplex`](../../Langlands/Cohomology/EquivariantDerivedComplex.md) | Derived functors into the bounded-below derived category, and the complexes `globalComplex` and `compactComplex` of equivariant sheaves in `DerivedCategory.Plus (Rep R G)` with their cohomology identifications |
| [`Langlands.Cohomology.SmoothSheafDerivedComplex`](../../Langlands/Cohomology/SmoothSheafDerivedComplex.md) | `SmoothSheafDerivedComplex.compactComplex`, the derived compact section complex of smooth equivariant sheaves in `DerivedCategory.Plus (SmoothRep R G)`, with `compactComplexHomologyIso` (used by `EquivariantComposite`) |
| [`Langlands.Cohomology.HyperextSpectralSequence`](../../Langlands/Cohomology/HyperextSpectralSequence.md), [`Langlands.Cohomology.HyperextAbutmentFiltration`](../../Langlands/Cohomology/HyperextAbutmentFiltration.md) | `hyperextSpectralSequence t K B`, Mathlib's `E₂`-cohomological spectral sequence of the spectral object obtained by applying `Hom(-, B)` to the truncations of `K` for a t-structure `t`, with `secondPageIso` (page 2 is `Hom(heartPiece t K q, B⟦p + q⟧)`) and `abutmentIso`; `HyperextAbutment.filtration` and `HyperextAbutment.graded`, the filtration of `Hom(K, B⟦n⟧)` by truncations of `K` and its graded pieces (used by `HyperextConvergence`) |
| [`Langlands.Cohomology.SmoothGodementCohomology`](../../Langlands/Cohomology/SmoothGodementCohomology.md) | `smoothGodementCompactCohomology`, the cohomology of compact sections of `Godement.smoothComplex`, as smooth representations, with `smoothGodementCompactCohomologyZeroIso`; invariant variants `smoothGodementInvariantCompactCohomology` |
| [`Langlands.Geometry.EtaleAutomorphism`](../../Langlands/Geometry/EtaleAutomorphism.md), [`Langlands.Cohomology.TranslationAction`](../../Langlands/Cohomology/TranslationAction.md), [`Langlands.Geometry.EtaleCohomologyAction`](../../Langlands/Geometry/EtaleCohomologyAction.md) | Translation of étale sheaves by scheme automorphisms, and `EtaleCohomologyAction.cohomologyRep`, the representation of a group acting on a scheme by automorphisms on étale cohomology of an equivariant sheaf |
| [`Langlands.Cohomology.TranslationCoaction`](../../Langlands/Cohomology/TranslationCoaction.md), [`Langlands.Geometry.EtaleConstantCohomology`](../../Langlands/Geometry/EtaleConstantCohomology.md), [`Langlands.Geometry.EtaleGaloisAction`](../../Langlands/Geometry/EtaleGaloisAction.md) | Actions on derived functors from structure maps into translates; `EtaleCohomologyAction.constantCohomologyRep`, the action on étale cohomology with constant coefficients; `EtaleGaloisAction.galoisCohomologyRep`, the action of `L ≃ₐ[K] L` on étale cohomology of the base change `X ×_{Spec K} Spec L` with constant coefficients |
| [`Langlands.Shimura.PEL.HarrisTaylorCMGeometricCohomology`](../../Langlands/Shimura/PEL/HarrisTaylorCMGeometricCohomology.md), [`Langlands.Shimura.PEL.HarrisTaylorCMGeometricGaloisCohomology`](../../Langlands/Shimura/PEL/HarrisTaylorCMGeometricGaloisCohomology.md) | In namespace `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`: `cmHarrisGeometricCoefficientCohomologySystem`, the étale cohomology `H^d(X̄_U, B_r)` as a functor of the coefficient stage `r`; `cmHarrisGeometricGaloisCohomologyAction`, the action of `F̄ ≃ₐ[F] F̄` on it, by pullback along the Galois automorphisms of `X̄_U` followed by the canonical coefficient isomorphisms. Both take a proof `q` of `CMRepresentabilityStatement` |
| [`Langlands.Geometry.EtaleDerivedSections`](../../Langlands/Geometry/EtaleDerivedSections.md) | `EtaleDerivedSections.cohomology X R d`, the right derived functors of global sections on sheaves of `R`-modules on the small étale site of a scheme, computed with injective resolutions; the étale cohomology in all seven `HarrisCM` statement modules |
| [`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelIndex`](../../Langlands/Shimura/PEL/HarrisTaylorCMSmallLevelIndex.md), [`Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoefficients`](../../Langlands/Shimura/PEL/HarrisTaylorCMGeometricCoefficients.md) | `SmallCMLevel D`, the sufficiently small CM levels with their level arrows, and the preorder `OrderedSmallCMLevel D`; `cmGeometricSchemeTower`, the tower `U ↦ X̄_U` as a functor `SmallCMLevel D ⥤ Scheme`, which takes `q` |
| [`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelCohomology`](../../Langlands/Shimura/PEL/HarrisTaylorCMSmallLevelCohomology.md), [`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelGaloisCoefficients`](../../Langlands/Shimura/PEL/HarrisTaylorCMSmallLevelGaloisCoefficients.md) | `cmSmallLevelTowerEtale` (the transition maps of the geometric tower are étale), coefficient diagrams `cmSmallLevelCoefficientDiagram`, level triviality `cmSmallLevelTrivialCoefficients`, the level cohomology `cmSmallLevelCohomology` and its colimit with the smooth finite-adelic action, `cmSmallLevelSmoothCohomology`; `cmSmallLevelGaloisCohomologyFunctor`, the colimit of `H^d(X̄_U, p_U^* M)` with the finite-adelic and Galois actions |
| [`Langlands.Shimura.PEL.HarrisTaylorCMHeckeSchemes`](../../Langlands/Shimura/PEL/HarrisTaylorCMHeckeSchemes.md), [`Langlands.Shimura.PEL.HarrisTaylorCMNormalActions`](../../Langlands/Shimura/PEL/HarrisTaylorCMNormalActions.md) | The inclusion arrow `smallCMInclusion D hVU : V ⟶ U` (element `1`) and, for `V` normal in `U` and `g ∈ U`, the arrow `smallCMNormalInverseArrow D U V hVU g : V ⟶ V` (element `g⁻¹`) |
| [`Langlands.Geometry.EtaleCohomologyDiagram`](../../Langlands/Geometry/EtaleCohomologyDiagram.md), [`Langlands.Shimura.RestrictedLevelTowerCohomology`](../../Langlands/Shimura/RestrictedLevelTowerCohomology.md), [`Langlands.Shimura.RestrictedLevelColimit`](../../Langlands/Shimura/RestrictedLevelColimit.md) | `CoefficientDiagram`, diagrams of étale sheaves over a tower of schemes; `IsLevelTrivialCoefficients`; colimits over levels satisfying a property, their insertions `RestrictedLevelColimit.ι` and the group actions on them |
| [`Langlands.Shimura.Unitary.OppositePointsSplit`](../../Langlands/Shimura/Unitary/OppositePointsSplit.md), [`Langlands.Shimura.SplitLevelTower`](../../Langlands/Shimura/SplitLevelTower.md), [`Langlands.Shimura.RestrictedSplitLevelTowerCohomology`](../../Langlands/Shimura/RestrictedSplitLevelTowerCohomology.md), [`Langlands.Shimura.PEL.HarrisTaylorCMPrimeToCohomology`](../../Langlands/Shimura/PEL/HarrisTaylorCMPrimeToCohomology.md) | `finiteAdelicPointsOpSplit`, the splitting of the opposite finite-adelic points at the places dividing `m`, and its instance `cmPrimeToSplit D m hm` for the rational involution of `D`; the factor embeddings `CompactOpenLevel.factorHom` and `CompactOpenLevel.awayHom`; the property `cmPrimeToProperty D m hm K₀` of the prime-to-`m` levels `K'` for which `e⁻¹ (K₀ × K')` is sufficiently small, the restricted coefficients `cmPrimeToCoefficients`, the colimit cohomology `cmPrimeToColimitCohomology` and the comparison `cmPrimeToCohomologyComparison` to the colimit over all small levels, with `ι_cmPrimeToCohomologyComparison`, `cmPrimeToCohomologyComparison_translate_of_mem` and `cmPrimeToCohomologyIso` (an isomorphism under `IsRestrictedCofinal`) |
| [`Langlands.Shimura.PEL.HarrisTaylorCMPrimeToGaloisCohomology`](../../Langlands/Shimura/PEL/HarrisTaylorCMPrimeToGaloisCohomology.md) | `cmPrimeToGaloisCohomologyFunctor`, the prime-to-`m` colimit cohomology of sheaves pulled back from `Spec F`, as a functor to `Action (SmoothRep R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ) (F̄ ≃ₐ[F] F̄)`; the Galois automorphisms `cmPrimeToGaloisAction` (the restriction of `cmSmallLevelGaloisAction` to the levels `e⁻¹ (K₀ × K')`), `cmPrimeToGaloisCohomology_ρ_ι_apply` (the action on the insertion of one level) and `cmPrimeToGaloisCohomologyComparison_apply` (the comparison to the colimit over all small levels commutes with the Galois operators). Its Markdown says that it considers no topology on the Galois group and no continuity of its action |
| [`Langlands.Shimura.PEL.HarrisTaylorCMGeometricNormalActions`](../../Langlands/Shimura/PEL/HarrisTaylorCMGeometricNormalActions.md), [`Langlands.Shimura.PEL.HarrisTaylorCMGeometricNormalTorsor`](../../Langlands/Shimura/PEL/HarrisTaylorCMGeometricNormalTorsor.md) | The action `cmGeometricNormalQuotientAction` of `U/V` on `X̄_V` by the tower maps of the arrows `smallCMNormalInverseArrow`, and the theorem `cmGeometricNormalEtaleAction_isFiniteGeometricTorsor_of_dominantCriterion` that it is a finite geometric torsor. No `HarrisCM` statement module imports them; the truth argument of `HarrisCMLevelInvariants` cites them |
| [`Langlands.Representation.Classification.Supercuspidal`](../../Langlands/Representation/Classification/Supercuspidal.md) | `GeneralLinear.IsSupercuspidal`: admissibility and vanishing of the Jacquet coinvariants for all proper conjugate block parabolics of `GL_n(F)` |
| [`Langlands.Representation.Classification.FixedCentralSplittingStatement`](../../Langlands/Representation/Classification/FixedCentralSplittingStatement.md) | The predicate `HasCompactSmoothCoefficientsModCenter` (the module's splitting proposition is not used) |
| [`Langlands.Group.GL.Padic`](../../Langlands/Group/GL/Padic.md) | The canonical topology on `GL_n(F)` with its topological group, Hausdorff and local compactness certificates |
| [`Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleCohomology`](../../Langlands/Sheaf/Equivariant/AnalyticQuasiEtaleCohomology.md), [`Langlands.Sheaf.Equivariant.TwistedGlobalSections`](../../Langlands/Sheaf/Equivariant/TwistedGlobalSections.md), [`Langlands.Sheaf.Equivariant.AnalyticGSheaves`](../../Langlands/Sheaf/Equivariant/AnalyticGSheaves.md) | In namespace `Langlands.Sheaf.Equivariant.Analytic`: `quasiEtaleCohomology X R q`, the derived functors of sections over `X` of sheaves of `R`-modules on the quasi-étale site (`H^q(X, -)`); `quasiEtaleGSheafCohomology ρ R q`, the derived functors on `QuasiEtaleGSheaf ρ` of `quasiEtaleGSheafSections ρ R`, the smooth part of the representation on global sections (Berkovich's `H^q(X{G}, -)` and `Γ_{X{G}}`); and `quasiEtaleComparison ρ R q`, the base change of the inclusion `Γ_{X{G}}(F) ⊆ (b^*F)(X)` along the exact functors `b^*` (`quasiEtaleGSheafRestriction`) and `smoothForget`, an instance of the generic `TwistedOver.globalComparison`. Also `compactLiftSystem ρ` and `twistedQuasiEtaleTopology ρ`, which appear in the instance binder of `AnalyticQuasiEtaleGlobalComparisonStatement` |
| [`Langlands.Geometry.Analytic.ContinuousAnalyticAction`](../../Langlands/Geometry/Analytic/ContinuousAnalyticAction.md), [`Langlands.Geometry.Analytic.LocalActionLifts`](../../Langlands/Geometry/Analytic/LocalActionLifts.md) | `IsContinuousAction ρ`, Berkovich's continuity of an action on an analytic space (§1.1); `IsCompactSpace X`, compactness and Hausdorffness of the underlying space. Both are hypotheses of `AnalyticQuasiEtaleGlobalComparisonStatement` |
| [`Langlands.Sheaf.Equivariant.AnalyticEtaleCohomology`](../../Langlands/Sheaf/Equivariant/AnalyticEtaleCohomology.md) | The étale counterparts of the quasi-étale row above, in the same namespace: `etaleCohomology X R q` (`H^q(X, -)` on the étale site); `etaleGSheafSections ρ R` (`Γ_{X{G}}` on `EtaleGSheaf ρ`); `etaleGSheafCohomology ρ R q` (`H^q(X{G}, -)`, as smooth representations); `etaleGSheafInvariantCohomology ρ R q` (`H^q(X(G), -)`, the derived functors of `Γ_{X(G)}`); and `etaleComparison ρ R q`, the map `H^q(X{G}, F) → H^q(X, b^*F)` of Thm 1.6.1(ii), induced by the inclusion of global sections through the exact functors `b^*` and `smoothForget`. Used by `AnalyticEtaleGlobalComparisonStatement` and the étale composite |
| [`Langlands.Sheaf.Equivariant.AnalyticEtaleComparison`](../../Langlands/Sheaf/Equivariant/AnalyticEtaleComparison.md), [`Langlands.Sheaf.Equivariant.AnalyticCompactSupport`](../../Langlands/Sheaf/Equivariant/AnalyticCompactSupport.md), [`Langlands.Sheaf.Equivariant.AnalyticEtaleCompactCohomology`](../../Langlands/Sheaf/Equivariant/AnalyticEtaleCompactCohomology.md) | In the same namespace: `pointProjection L X`, the underlying point of `L`-valued point, and `pointTopology`, the topology on `L`-valued points induced by it; `etaleGSheafCompactSections` (`Γ_{c,X{G}}` on étale `G`-sheaves, with supports in `L`-valued points); `etaleGSheafCompactCohomology L ρ h R q` (`H^q_c(X{G}, -)`); `etaleCompactCohomology` (`H^q_c(X, -)` on the étale site); `etaleGSheafRestriction ρ` (Berkovich's `b^*`, which forgets the action); `etaleCompactInclusion`, the inclusion `Γ_{c,X{G}}(F) → Γ_c(X, b^*F)`; and `etaleCompactComparison L ρ h R q`, the map `H^q_c(X{G}, F) → H^q_c(X, b^*F)` of Cor. 1.5.2(i) induced by it. Used by `AnalyticEtaleCompactComparisonStatement`, whose surjectivity hypothesis is stated with `pointProjection` |
| [`Langlands.Sheaf.Equivariant.AnalyticEtaleGlobalComplex`](../../Langlands/Sheaf/Equivariant/AnalyticEtaleGlobalComplex.md), [`Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleGlobalComplex`](../../Langlands/Sheaf/Equivariant/AnalyticQuasiEtaleGlobalComplex.md), [`Langlands.Sheaf.Equivariant.TwistedExactGlobalComplex`](../../Langlands/Sheaf/Equivariant/TwistedExactGlobalComplex.md) | `etaleGSheafComplex ρ R` and `quasiEtaleGSheafComplex ρ R`, Berkovich's `RΓ(X{G}, F)` in the bounded below derived category of smooth representations, with `etaleGSheafInvariantComplex` and `quasiEtaleGSheafInvariantComplex` for `RΓ(X(G), F)`; `quasiEtaleGSheafInvariantSections` (`Γ_{X(G)}`, the invariants of `Γ_{X{G}}`) and `quasiEtaleGSheafInvariantCohomology ρ R q`; the `…HomologyIso` identifications of the cohomology of these complexes with the derived functors. Built from the generic `exactGlobalComplex` and `exactInvariantGlobalComplex`. Used by the two composites of `AnalyticGlobalComposite.Statement` |
| [`Langlands.Sheaf.Equivariant.AnalyticConstantAdjunction`](../../Langlands/Sheaf/Equivariant/AnalyticConstantAdjunction.md) | `etaleGSheafSections_preservesInjectiveObjects` and `quasiEtaleGSheafSections_preservesInjectiveObjects`: `Γ_{X{G}}` sends injective `G`-sheaves to injective smooth representations, through its left adjoint, the constant `G`-sheaf. Berkovich's derivation of the §1.2 spectral sequence uses this property; no statement of this framework cites the module |
| [`Langlands.Sheaf.Equivariant.AnalyticSetInducedSections`](../../Langlands/Sheaf/Equivariant/AnalyticSetInducedSections.md), [`Langlands.Topology.GroupAction.DiscreteGSetFibre`](../../Langlands/Topology/GroupAction/DiscreteGSetFibre.md) | In namespace `Langlands.Sheaf.Equivariant.Analytic`: `quasiEtaleSetInducedSections hC hD X R` and `etaleSetInducedSections hC hD X R`, Berkovich's `Γ_{X{G}}` (§1.2, printed p.4) from sheaves of `R`-modules on `Qét(X(G))` and `Ét(X(G))` (the `EquivariantQuasiEtaleSite X` and `EquivariantEtaleSite X`) to smooth representations. Each is the fibre functor `fibreFunctor G R` (namespace `Langlands.DiscreteGSet`) applied to the presheaf `Σ ↦ F(X_Σ(G))` on `P(G)`. `quasiEtaleSetInducedSectionsIso` and `etaleSetInducedSectionsIso` give Berkovich's formula `lim→_N F(X_{G/N}(G))`, from `colimitOpenSubgroupIsoFibre`. The arguments `hC : SetInducedSpace.ContinuityStatement` and `hD : SigmaDescStatement` are proofs of the statements. They are supplied by the published theorems `SetInducedSpace.continuityStatement` (in the Library at `03296177`) and `sigmaDesc_quasiEtale_etale` (in the Library at `95d37e11`), both in `Langlands.Analytic.SaturatedAtlasPresentation`. The comparison with the smooth `G`-sheaf model is not formalized. No statement of this framework cites the modules |
| [`Langlands.Sheaf.Equivariant.AnalyticEtaleRefinements`](../../Langlands/Sheaf/Equivariant/AnalyticEtaleRefinements.md) | `hasAdmissibleRefinements_distinguishedLiftSystem`, which derives the instance `HasAdmissibleRefinements` for `distinguishedLiftSystem ρ` and `twistedEtaleTopology ρ` (both in `AnalyticGSheaves`), required by five étale statements (the étale comparison, the étale composite, the étale compact comparison, the étale §1.2 spectral sequence and the étale paracompact comparison), from three conditions: `HasDistinguishedEtaleNeighbourhoods X`, `HasDistinguishedEtaleLifts ρ` and `HasCompatibleDistinguishedEtaleLifts ρ`. These conditions are not proved in the Library |
| [`Langlands.Geometry.Analytic.FieldValuedPoints`](../../Langlands/Geometry/Analytic/FieldValuedPoints.md), [`Langlands.Geometry.Analytic.EtaleGeometricPoints`](../../Langlands/Geometry/Analytic/EtaleGeometricPoints.md) | `localizedFieldPointFunctor L`, the functor of `L`-valued points of analytic spaces; `EtaleSite.PointAxioms L x`, the axioms under which an `L`-valued point gives a point of the étale site (cofiltered category of elements and lifting along covering sieves). The hypothesis `h` of `AnalyticEtaleCompactComparisonStatement` asks them for every `L`-valued point |
| [`Langlands.Shimura.PEL.HarrisTaylorCMLambdaTower`](../../Langlands/Shimura/PEL/HarrisTaylorCMLambdaTower.md) | The `λ`-adic cohomology of the CM tower with Harris's coefficient systems `W`, in namespace `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. `cmHarrisLambdaLevelCohomology`: `U ↦ H^d(S_U ×_F F̄, W)_λ` with the maps induced by the transporters of small levels. `cmHarrisLambdaTowerCohomology`: its colimit `H^d(S, W)_λ`, a smooth representation of `GG(A_f)` over `K_λ` with the commuting action of `Gal(F̄/F)`, and the level Hecke module `cmHarrisLambdaTowerHeckeModule` of its fixed vectors. The fixed-vector comparison is the proposition `CMHarrisLambdaTowerFixedVectorComparison`, which is not proved. For a representation `τ` of `GG(A_f)` over a field `M` extending `K_λ`: the extension of scalars `cmHarrisLambdaTowerExtendScalars`, the isotypic part `cmHarrisLambdaTowerIsotypic`, its fixed vectors at a level `cmHarrisLambdaTowerIsotypicFixedVectors` (the space of `CMHarrisVanishingStatement`), and the multiplicity spaces `cmHarrisLambdaTowerMultiplicity` and `cmHarrisLambdaTowerHeckeMultiplicity`. Under explicit finiteness, continuity and fixed-vector hypotheses these become continuous Galois representations with Euler polynomials at unramified places (`cmHarrisLambdaIsotypicFixedVectorsObjects`, `cmHarrisLambdaMultiplicityObjects`, `cmHarrisLambdaHeckeMultiplicityObjects`). The module is built on `HarrisTaylorCMSmallLevelGaloisTower` and `HarrisTaylorCMSmallLevelGaloisIsotypic` (see the Shimura row of [Not yet stated](#not-yet-stated-and-the-prerequisites-they-wait-for)) |
| [`Langlands.JacquetLanglands.HarrisTransfer`](../../Langlands/JacquetLanglands/HarrisTransfer.md), [`Langlands.JacquetLanglands.AwayTransfer`](../../Langlands/JacquetLanglands/AwayTransfer.md), [`Langlands.JacquetLanglands.HarrisAwaySplitting`](../../Langlands/JacquetLanglands/HarrisAwaySplitting.md) | In namespace `Langlands.JacquetLanglands`: `IsHarrisJacquetLanglandsTransfer`, Harris's relation "`ρ'` is `JL(π_f)`" (see the `JL(π_f)` row of [Not yet stated](#not-yet-stated-and-the-prerequisites-they-wait-for)); `splitTensor Φ π σ`, the representation `(π ⊠ σ) ∘ Φ` of a group split as `Φ : G ≃ₜ* L × H`; and the splitting `harrisAwaySplitGL` of `GJ(A_f)` into the factor at the distinguished place `w₀` and the complement `HarrisAwayComplement`. `CMHarrisVanishingStatement` uses them for `JL(π_f)` and for a supercuspidal constituent at `w₀` |

The third component of `EquivariantGodementStatements` uses Mathlib's
`rightDerived` directly; by definition these are the `globalDerived`
and `compactDerived`. `SmoothCompactCohomology`, `SmoothCompactComparison` and
`SmoothGodement` state their compact-support conclusions with the `EquivariantGodementCohomology.compactCohomology` and
`SmoothSheafCohomology.compactDerived`.

## Source items and their declarations

| Source item | Declarations |
| --- | --- |
| Harris 1999 §2 p.304: Berkovich's resolution `F(T)`, Fact 3 (exactness) | Ordinary-topological analogues: `EquivariantGodementStatements`; `GodementExactnessStatements` |
| Harris 1999 p.304, acyclicity of `F(T)` for compactly supported sections | Analogues: the compactly supported part of `EquivariantGodementComputesSectionsStatement`; `FlasqueGodementCohomologyStatements` (compactly supported, on topological spaces); with `OperatorSpaceCohomologyStatements` and `AcyclicResolutionComparisonStatements` for the comparison |
| Harris 1999 p.304, Fact 3, and the compact-support acyclicity of `F(T)`, with a topological group | `SmoothGodementStatements` (smooth sheaves, ordinary topology) |
| Harris 1999 p.305, truncation and pro-`p` invariants | `ProPInvariantTruncationStatements` |
| Harris 1999 p.305, `H^q_c(U(ẽ)_{F̄}, ℤ/ℓ^m ℤ)` is a smooth module (finiteness not covered) | `SmoothCompactCohomologyStatements` (ordinary-topological analogue) |
| Harris 1999 (2.6)–(2.7), passage to the limit over levels | `FilteredColimitComparisonStatements` |
| Harris 1999 Lemma 2.8 and Prop. 4.10, Mittag-Leffler passage to `ℓ`-adic coefficients | `InverseLimitComparisonStatements` (algebraic part) |
| Harris 1997 pp.95–96 and Harris 1999 p.312, supercuspidal splitting | `CompactCoefficientSplittingStatement` |
| Harris 1997 p.96, `Ext` Frobenius reciprocity for compact induction from `GJ^0`, injectivity and projectivity of supercuspidals, vanishing of higher `Ext`; Harris 1999 p.312, "the higher Ext's vanish" | `SupercuspidalExtStatements` (complex coefficients); `SupercuspidalExtCharZeroStatements` (any field of characteristic zero) |
| Vignéras 1996 I.7.1–7.10 and II.3.9, compact representations over a field | `SupercuspidalExtCharZero.HasCompactCoefficients`; `CompactCoefficientInjectiveProjectiveStatement` (characteristic zero) |
| Harris 1997 (10) → (11) and Harris 1999 (4.10.1) → (5.2), degeneration once higher `Ext` vanish | `HyperextDegenerationStatement`; `SpectralSequenceConcentrationStatements` |
| Berkovich §1.5, Cor. 1.5.2(i), compact support on the equivariant site, for a discrete group (§1.4, p.7) | Ordinary-topological analogues, for a group without topology acting on a topological space and equivariant sheaves of modules on its open sets, not on Berkovich's analytic étale site: `EquivariantCompactSectionsDerivedStatement` (analogue of the isomorphisms `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)`); for finite `G`, `FiniteEquivariantCompactAcyclicGroupCohomologyStatement` (when higher compactly supported cohomology vanishes) and `FiniteEquivariantCompactSectionsInvariantsStatement` (when the order of `G` is invertible). The isomorphisms themselves are stated for a topological group in the `AnalyticEtaleCompactComparisonStatement` row below, for the Library's étale `G`-sheaves (`EtaleGSheaf`) on the étale site; their transport to Berkovich's equivariant site through Theorem 1.4.2 is open. Neither these consequences nor the printed spectral sequence is stated on Berkovich's analytic sites; the ordinary-topological form of the spectral sequence for compact `G` is in the `CompactGroupCompactCompositeStatement` row of this table. |
| Berkovich Cor. 1.5.2(i), smoothness of the action on `H^q_c(X, b^*F)` and the comparison `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)` for a topological group | `SmoothCompactCohomologyStatements`; `SmoothCompactComparisonStatements` (ordinary-topological analogues) |
| Berkovich §1.5 (ii) and Prop. 1.5.1, exactness of `F ↦ C^m(F)` and softness of `b^*C^m(F)` | `SmoothGodementStatements` (ordinary-topological analogue) |
| Harris 1999 Lemma 2.2 and (2.3), pp.304–305: the resolution of Lemma 2.2 computes `H^q_c`; the Godement step of the proof of Berkovich Cor. 1.5.2(i) | `SmoothGodementComparisonStatements` (ordinary-topological analogue) |
| Harris 1999 p.306 and Prop. 4.10, p.311: `Ext` in smooth `L_ℓ[GJ]`-modules, `L_ℓ = L ⊗_ℚ ℚ_ℓ`; p.312, the higher `Ext` vanish | `SupercuspidalExtSemisimpleStatements` |
| Harris 1997 p.96: `GJ^0` has compact center, so `π_v` restricted to `GJ^0` is still supercuspidal | `CompactModCenterRestrictionStatement` |
| Bernstein–Zelevinsky 1976, 3.20, 3.21 (Harish-Chandra) and 3.26 | `GLSupercuspidalRestrictionStatements` |
| Harris 1999 §5, p.313: `λ`-adic representations of `Gal(F̄/F)` on étale cohomology; SGA 4 VII 5.7–5.8 | `GaloisCohomologySmoothStatement` (constant coefficients) |
| Harris 1999 §5, p.313: `λ`-adic representations "unramified at all but finitely many places"; Theorems 5.7 (ii) and 5.9 (i) (almost all places); SGA 4½ [Th. finitude] 1.9 (truth argument) | `GaloisCohomologyUnramifiedStatement` (finite constant coefficients; the exceptional set may depend on the coefficients) |
| Harris 1999 §5, p.313, as above, for all torsion levels at once; SGA 4 XVI Cor. 2.2, the specialization theorem for proper smooth morphisms (truth argument) | `GaloisCohomologyGoodReductionStatement` (smooth proper schemes; one exceptional set for all finite constant coefficients, apart from the places dividing their order) |
| Harris 1999, proof of Prop. 4.10, p.312: "the right-hand side of the spectral sequence (4.9) is a finite group for all `m`"; SGA 4 XIV Cor. 1.2 | `HarrisCMCohomologyFiniteStatement` (analogue for the geometric CM level `X̄_U` and torsion stage `B_r`; conditional on `q`) |
| Harris–Taylor 2001 III.2, p.97: the Galois action on Shimura cohomology with coefficient systems is continuous; Harris 1999 §5, p.313: `λ`-adic representations of `Gal(F̄/F)` on such cohomology; SGA 4 VII 5.7–5.8 | `HarrisCMGaloisCohomologySmoothStatement` (the same analogue, at one level and one torsion stage) |
| Harris 1999 §5, p.313: `λ`-adic representations "unramified at all but finitely many places", on the cohomology of unitary Shimura varieties with coefficient systems; Harris–Taylor 2001 III.1, p.91, monodromy of the level covers; SGA 4 XV 2.1 and XVI 2.1 (truth argument) | `HarrisCMCohomologyUnramifiedStatement` (the geometric CM level `X̄_U` and torsion stages `B_r`; one exceptional set for all degrees and stages; conditional on `q`) |
| Harris–Taylor 2001 III.2, p.96: `H^i(X, L_ξ) = lim_{→U} H^i_et(X_U ×_F F^ac, L_ξ)` over sufficiently small levels; p.97: it is "an admissible/continuous `G(A^∞) × Gal(F^ac/F)`-module"; SGA 4 VII 5.1 and Cor. 5.8 (truth argument) | `HarrisCMLevelGaloisSmoothStatement` (the Galois continuity, for the colimit over all small CM levels, with coefficients pulled back from `Spec F` and discrete modules; conditional on `q`) |
| Harris–Taylor 2001 III.2, p.96: "If `V ⊂ U` then … `H^i_et(X_U ×_F F^ac, L_ξ) ≅ H^i_et(X_V ×_F F^ac, L_ξ)^{U/V}`"; SGA 4 IX 5.1, the trace (truth argument only) | `HarrisCMLevelInvariantsStatement` (finite level, `V` normal in `U`, `[U : V]` a unit of `R`); `HarrisCMColimitInvariantsStatement` (the colimit over all small levels, `ℚ`-algebra coefficients); both conditional on `q` |
| Harris 1999 Prop. 4.10, p.311: "as `K(N)^{ℓ,p}` varies the spectral sequences are `GG(A_f^{ℓ,p})`-equivariant", with the level at `ℓ` and `p` fixed (motivation); Harris–Taylor 2001 III.2, p.96, the colimit over levels and the comparison with invariants (provenance) | `HarrisCMPrimeToInvariantsStatement` (the colimit over the levels `e⁻¹ (K₀ × K')` is the `K₀`-invariants of the colimit over all small levels; `ℚ`-algebra coefficients; conditional on `q`) |
| Harris–Taylor 2001 III.2, p.97: the colimit over levels is "an admissible/continuous `G(A^∞) × Gal(F^ac/F)`-module"; Harris 1999 Prop. 4.10, p.311, the level at `ℓ` and `p` fixed (motivation); SGA 4 VII 5.1 and Cor. 5.8 (truth argument) | `HarrisCMPrimeToGaloisSmoothStatement` (the Galois continuity for the colimit over the levels `e⁻¹ (K₀ × K')`, with coefficients pulled back from `Spec F` and discrete modules; conditional on `q`) |
| Harris 1999 Prop. 4.4, (4.4.1), p.309, and Prop. 4.10, (4.10.1), p.311: the spectral sequences `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}, 𝒜) ⇒ H^{i+j}`, as abstract convergence; Cartan–Eilenberg 1956 XVII §2 (4) and §3 Case 1, pp.368–370 | `HyperextConvergenceStatements` (any triangulated category with a t-structure, `K` bounded on both sides; the abutment is `Hom(K, B⟦n⟧)`, not yet identified with Shimura cohomology) |
| Cartan–Eilenberg 1956 XVII §2 (4) and §3 Case 1, pp.368–370: the second hypercohomology spectral sequence of `Hom(C, A)` for `C` bounded above and `A` bounded below | `HyperextHalfBoundedConvergenceStatements` (any triangulated category with a t-structure; a position-dependent page bound); `CovariantSecondPageStatement` (the covariant form `Ext^p(A, H^q(K)) ⇒ Hom(A, K⟦p + q⟧)` in the opposite of a derived category) |
| Tohoku V, Cor. to Prop. 5.1.3 (p.198), (5.2.2) (p.199) and Thm 5.2.1 with (5.2.5) (p.200): `H^p(G, H^q(X, A)) ⇒ H^n(X; G, A)` | `EquivariantGlobalCompositeStatement` (composite-functor form); with `HyperextHalfBoundedConvergenceStatements` and `CovariantSecondPageStatement`, the spectral sequence in derived form (Application section of `HyperextConvergence/HalfBoundedStatement.md`) |
| Berkovich Cor. 1.5.2(i), pp.11–12: `H^p(G, H^q_c(X, b^*F)) ⇒ H^{p+q}_c(X(G), F)` | `CompactGroupCompactCompositeStatement` (ordinary topology, smooth sheaves, compact `G`, composite-functor form with `H^q_c` derived in the smooth category; false for noncompact `G`); with the two statements of the previous row, the spectral sequence in derived form for compact `G` |
| Berkovich Thm 1.6.1(ii), p.13: `H^q(X{G}, F) ⥲ H^q(X, b^*F)` for compact `X` and quasi-étale (resp. étale) abelian sheaves `F` on `X(G)` | `AnalyticQuasiEtaleGlobalComparisonStatement` (quasi-étale case, the quasi-étale `G`-sheaves of `R`-modules); `AnalyticEtaleGlobalComparisonStatement` (étale case, the étale `G`-sheaves of `R`-modules). The spectral sequence `H^p(G, H^q(X, b^*F)) ⇒ H^{p+q}(X(G), F)` is stated in its two Library-model versions, `AnalyticEtaleCompactBaseSpectralSequenceStatement` and `AnalyticQuasiEtaleCompactBaseSpectralSequenceStatement` (module `Langlands.Cohomology.AnalyticGlobalSpectralSequence.CompactBaseStatement`) |
| Berkovich Thm 1.6.1(i), pp.13–14: for paracompact `X`, `R^q(Γ(X, -) ∘ b^*) ⥲ H^q(X, b^*(-))` on quasi-étale (resp. étale) sheaves on `X(G)` | `AnalyticQuasiEtaleParacompactComparisonStatement` and `AnalyticEtaleParacompactComparisonStatement` (Hausdorff paracompact underlying space, continuous action; the comparison is `ExactBaseChange.compComparisonNatTrans` along `b^*` on the `G`-sheaves of `R`-modules). Part (iii) of the theorem is not stated |
| Berkovich Thm 1.4.2, pp.8–10: `b^*` and `(b_*-)^G` are inverse equivalences between sheaves on `X(G)` and `G`-sheaves on `X` | `EtaleGSheafToposComparisonStatement` (étale case, sheaves of `R`-modules, assuming `HasImagePullbacks` for the étale site and `OpenQuotientsSmall`). For the quasi-étale case with module coefficients on Hausdorff analytic spaces, see the [compact-probe comparison at `7a774d17`](#compact-probe-and-geometric-coefficient-comparisons-at-library-7a774d17). The set-valued topos equivalence remains to be stated. |
| Berkovich §1.2, pp.4–5: `Γ_{X(G)} = (-)^G ∘ Γ_{X{G}}` and the spectral sequence `H^p(G, H^q(X{G}, F)) ⇒ H^{p+q}(X(G), F)` | `AnalyticEtaleGlobalCompositeStatement` and `AnalyticQuasiEtaleGlobalCompositeStatement` (composite-functor form on the étale and quasi-étale `G`-sheaves, any topological group, no compactness or continuity). The spectral sequence itself, for a continuous action: `AnalyticEtaleGlobalSpectralSequenceStatement` and `AnalyticQuasiEtaleGlobalSpectralSequenceStatement` (page 2 as `Ext` in smooth representations, first quadrant, finite filtration, stable pages and abutment) |
| Berkovich Cor. 1.5.2(i), pp.11–12, first assertion: `H^q_c(X{G}, F) ⥲ H^q_c(X, b^*F)` for a continuous action on a Hausdorff `X` | `AnalyticEtaleCompactComparisonStatement` (étale case; compact supports in `L`-valued points, and every point of `X` underlies an `L`-valued point). The second assertion, smoothness of the action on `H^q_c(X, b^*F)`, follows from it by the conditional theorems in `AnalyticEtaleCompactSmoothness`. The source has no quasi-étale clause here. The analytic étale spectral sequence is not stated in general. Its compact-base case is stated as `AnalyticEtaleCompactSupportSpectralSequenceOnCompactBaseStatement` (module `Langlands.Cohomology.AnalyticGlobalSpectralSequence.CompactSupportStatement`). On a compact base, `AnalyticEtaleEquivariantCompactGlobal` identifies the compactly supported equivariant sections, their derived functors and complexes with the ordinary ones |
| Harris 1999 (5.1), p.312: `H^i(S_K(N), W)[π] = 0` for `i ≠ n − 1`, with `π_v` supercuspidal; Harris 1997 §1, p.79, hypothesis (R); Harris 1997 Lemma 4, pp.82–83 (truth argument) | `CMHarrisVanishingStatement` (for the Library's CM Shimura varieties, the `λ`-adic cohomology with `W` coefficients and the `U`-fixed vectors of the `τ`-isotypic part, `τ` a model of `JL(π_f)` over a field extending `K_λ`) |
| Harris 1999 Theorem 5.9(ii), pp.314–315, with locality of (5.4)–(5.5), pp.313–314, and irreducibility of the local parameter (Harris, p.313, citing Henniart) | `Harris1999Theorem59iiParameterStatement` (existence of a local-class assignment and one family per eligible presentation, giving the prescribed isomorphism class for every compatible continuous coefficient embedding at fixed `ℓ` and `ιΩ`); `HarrisSupercuspidalRestrictionIrreducibleStatement` (absolute irreducibility for every eligible family away from `p_v`). Derived statements only; the comparison with the actual `σ(Π_v)` and the twist relation of Lemma 5.8 are not stated. |

## Mathlib results used instead of restating them

- `Abelian.Ext`, `Abelian.Ext.eq_zero_of_projective`,
  `Abelian.Ext.eq_zero_of_injective`: Yoneda `Ext` and its vanishing.
- `Adjunction.extEquiv`: `Ext` across an adjunction of exact functors. This is
  the formal shape of the Frobenius-reciprocity step in Harris 1997 p.96.
- `CochainComplex.isKProjective_of_projective`,
  `HomComplex.CohomologyClass.equivOfIsKProjective`: Hom complexes out of
  bounded-above complexes of projectives compute derived `Hom`. This is
  Harris 1997 pp.92–94, from the Čech complex (7) to `RHom`.
- `Functor.rightDerived`, `InjectiveResolution`, `isoRightDerivedObj`:
  derived functors and their computation by injective resolutions.
- `CohomologicalSpectralSequence`: the spectral-sequence pages used by the
  concentration statements.

## Not yet stated, and the prerequisites they wait for

| Part of the framework | Missing prerequisite | Where it stands |
| --- | --- | --- |
| Application of `CompactModCenterRestrictionStatement` to Harris's `GJ^0`: that `GJ^0` is normal in `GJ` and that `Z(GJ) GJ^0` has finite index | The group `GJ`, the Drinfeld tower `M_N` and its components (Harris 1997 (A.8)) | The analytic spaces and equivariant étale sites (`Langlands/Geometry/Analytic/`, `Langlands/Sheaf/Equivariant/`) |
| The geometric input `H^j_c(M_N) ≅ c-Ind_{GJ^0}^{GJ} H^j_c(R_N)` (Harris 1997 (A.8)) | The Drinfeld tower as analytic spaces with their group actions. The Library has only a topological model of the induction step: the balanced quotients `G ×_H X` of the Berkovich spectra of rational domains of a strict affinoid algebra (`Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSpectrum`), with sheaves on their ordinary open subsets, and the identifications, in modules of the same directory, with compact induction from `H` to `G`: of the compactly supported locally constant functions with values in a smooth representation `M` of `G` (`compactInductionNatIso` in `InducedRationalCompactInduction`), and of degree-zero compactly supported Godement and derived cohomology (`InducedRationalCohomologyInduction`, which also identifies the zero row `E₂^{p,0}` of the hyperext spectral sequence with `Ext` over `H`, `compactHyperextZeroRowSubgroupAddEquiv`). Higher compact cohomology is not identified with compact induction there. The separate level-one Drinfeld construction only treats the matrix factor (see the `σ(π_v)` row below) | The analytic spaces and equivariant étale sites (`Langlands/Geometry/Analytic/`, `Langlands/Sheaf/Equivariant/`) |
| The étale compact-support spectral sequence of Berkovich Cor. 1.5.2(i) in a corrected scope and the ordinary compact-base spectral sequences of Thm 1.6.1(ii) (both now stated, as `AnalyticEtaleCompactSupportSpectralSequenceOnCompactBaseStatement` and the two statements of `AnalyticGlobalSpectralSequence.CompactBaseStatement`, and not proved in the Library); and the smoothness of the group action on the compactly supported cohomology of the Drinfeld tower (Harris 1997 Lemma 6(i)). The étale case of the comparison of Cor. 1.5.2(i) is stated (`AnalyticEtaleCompactComparisonStatement`; the Library has only a conditional proof), and the smoothness of the action on `H^q_c(X, b^*F)` follows from it by the conditional theorems (see the paragraph after [Published modules](#published-modules)). The ordinary-topological analogue of the smoothness is stated in `SmoothCompactCohomology` | Berkovich's statement concerns smooth equivariant étale sheaves (Definition 1.4.1, pp.7–8) on a `G`-space, an analytic space with a continuous action of a topological group `G` (§1.1, pp.1–2), and the derived functors of `Γ_{c,X{G}}` among them, with supports in the underlying space of `X`. Smoothness is a condition on the sheaf `F`: for every quasi-étale `U → X` with `U` compact, the canonical action of the open subgroup `G_U ⊂ G` on `F(U)` is discrete. The published modules in `Langlands.Sheaf.Equivariant` model these objects on the analytic sites: `AnalyticGSheaves` (`EtaleGSheaf` and `QuasiEtaleGSheaf`, Berkovich's `T_G(X_ét)` and `T_G(X_qét)`, built on the generic `LocalActionDiscretePart`); `AnalyticCompactSupport` (`Γ_{c,X{G}}` on étale `G`-sheaves, with supports in the `L`-valued points, topologized from the underlying space of `X`); for étale sheaves, `AnalyticEtaleCohomology`, `AnalyticEtaleCompactCohomology`, `AnalyticEtaleComparison` and `AnalyticEtaleGlobalComplex` (see [Published constructions used](#published-constructions-used)), and `AnalyticEtaleRefinements` (the admissible-refinement hypothesis reduced to three conditions, which remain hypotheses); for quasi-étale sheaves, `AnalyticQuasiEtaleCompactCohomology` (`H^q_c(X{G}, F)`, `quasiEtaleGSheafCompactCohomology`), `AnalyticQuasiEtaleComparison` (Berkovich's `b^*` as `quasiEtaleGSheafRestriction`, `H^q_c(X, -)` on the quasi-étale site, and the comparison map `quasiEtaleCompactComparison : H^q_c(X{G}, F) → H^q_c(X, b^*F)`), `AnalyticQuasiEtaleCohomology`, `AnalyticQuasiEtaleGlobalComplex` and `AnalyticQuasiEtaleRefinements` (the finite-equivariant-refinement hypothesis reduced to three conditions, of which the finite compact refinements remain unproved for Hausdorff `X`). The statements on these sites are the ten statements in the analytic rows of [Published modules](#published-modules), which also list the construction module `AnalyticEtaleEquivariantCompactGlobal`. The étale composite `AnalyticEtaleGlobalCompositeStatement` is proved by the `analyticEtaleGlobalComposite` (first appeared at `ba00e097`; see [Proved statements](#proved-statements)). The quasi-étale composite `AnalyticQuasiEtaleGlobalCompositeStatement` is proved by the `analyticQuasiEtaleGlobalComposite` (in the Library at `320321b3`). The quasi-étale comparison is proved by the `analyticQuasiEtaleGlobalComparison` (first appeared at `03296177`). The étale comparison and the étale compact comparison are open (the latter has a conditional proof). The five propositions stated last (the §1.2 spectral sequences, the Thm 1.6.1(i) comparisons and the étale Thm 1.4.2) are unproved. Helper statements and reductions toward the three comparisons are listed under [Published steps toward open components](#published-steps-toward-open-components). The source makes no quasi-étale compact-support comparison here. There is a paper degree-zero obstruction to using only `L`-valued point supports in the manuscript-style quasi-étale setting for `G = ℤ_p` acting on noncompact `X`, not a formal verification on the Library's generated quasi-étale topology (see [Retained source gaps and scope decisions](#retained-source-gaps-and-scope-decisions)). The published paracompact comparison of Thm 1.6.1(i) derives ordinary global sections composed with restriction, not smooth sections or compactly supported sections. The spectral sequence of §1.2 is stated; the compact-base sequences in preparation re-identify its page 2 with the ordinary cohomology of the restriction, via the comparisons of Thm 1.6.1(ii) in the intended proof. No compactly supported composite is stated on the analytic sites. Harris's Lemma 6(i) needs the Drinfeld tower (row on `σ(π_v)` below) | The geometric and equivariant cohomology framework (`Langlands/Cohomology/`, `Langlands/Sheaf/Equivariant/`) and the analytic spaces |
| Smoothness of the Galois action on étale cohomology with non-constant coefficients in general, and on Shimura cohomology with `ℓ`-adic coefficients or with Harris's torsion coefficient systems after passing to the limit over levels. It is stated, conditionally on `CMRepresentabilityStatement`, for the CM torsion coefficient system at one level and one stage (`HarrisCMCohomology`), for the colimit over all small CM levels with coefficients pulled back from `Spec F` (`HarrisCMLevelGaloisSmooth`), and for the prime-to-`m` colimit with the same coefficients (`HarrisCMPrimeToGaloisSmooth`) | Galois actions on étale cohomology of equivariant sheaves over base changes, and the Shimura schemes. For Harris's CM torsion coefficient system the Galois actions exist only conditionally on `CMRepresentabilityStatement` (see the Shimura row below) | the published `EtaleCohomologyAction`; the unitary Shimura geometry (`Langlands/Shimura/`) |
| Harris's spectral sequences themselves (Harris 1997 Lemma 6; Harris 1999 Prop. 4.4, (4.4.1), Prop. 4.10), and the application of `HyperextDegenerationStatement` to them | The geometry listed at the end of this cell. Convergence of the hyperext spectral sequences, also a prerequisite, is now proved, as follows. The `Langlands.Cohomology.HyperextSpectralSequence` constructs, for a t-structure `t` and objects `K` and `B`, the spectral sequence `hyperextSpectralSequence` obtained by applying `Hom(-, B)` to the truncations of `K`, with its second page (`secondPageIso`) and its intended abutment `Hom(K, B⟦n⟧)` (`abutmentIso`). The `HyperextSecondPage` and `SmoothHyperextSecondPage` identify the second page with `Ext^p(H^{-q}(K), W)`, also for smooth representations, and `HyperextAbutmentFiltration` defines the filtration of `Hom(K, B⟦n⟧)` by truncations of `K`. None of these proves convergence, and Mathlib has no convergence theory for these spectral sequences. Convergence for objects `K` bounded for the t-structure is stated in `HyperextConvergenceStatements` and proved by the `hyperextConvergenceStatements_proof`. Convergence for `K` bounded above and `B` bounded below is stated in `HyperextHalfBoundedConvergenceStatements` and proved by the `hyperextHalfBoundedConvergenceStatements_proof` (both under [Proved statements](#proved-statements)). The identification of the second page and the abutment of the covariant spectral sequence, `CovariantSecondPageStatement`, is proved by the `covariantSecondPageStatement_proof`. Library commits after `c0c7eab6`, up to `ddb0a9c0`, add the `Langlands.Cohomology.HyperextAbutmentFunctor` (the abutment filtration and its graded pieces as functors) and the constructions that apply this spectral sequence to Harris's forms on the definite group, level by level: `Langlands.Shimura.DefiniteFormsSmoothExt` (the forms `𝒜_ℓ(GJ, 𝓛, K(m))` with trivial coefficients as smooth `GJ_p`-modules, with their `Ext` groups, the spectral sequence and its abutment; Harris 1999 Prop. 4.4), `Langlands.Shimura.DefiniteFormsHeckeExt` (Hecke operators on these forms and on their `Ext` groups), `Langlands.Shimura.DefiniteFormsSmoothCoefficients` (the same for coefficients a representation of `K_ℓ`; Prop. 4.10) and `Langlands.Shimura.DefiniteFormsTowerLimit` (Harris's `D_m(K_ℓ)` as the direct limit along the tower `K_ℓ(n)`, p.308). Their Markdown states that neither convergence nor the comparison of the abutment with the cohomology of the Shimura variety is proved, and none of them defines a theorem statement. Later Library commits add further constructions around the degenerate case, none of which defines a theorem statement: `HyperextDegenerationIso` (the degeneration isomorphism, also for smooth representations), `HyperextDegenerationEquivariance` and `HyperextAbutmentNaturality` (equivariance and naturality of the edge map and of the abutment filtration), `HyperextEdgeMapLinear` and `HyperextDegenerationIsotypic` (`R`-linearity and isotypic parts of the degeneration isomorphism), `HyperextHomComplex` (the abutment as cohomology of a Hom complex out of a K-projective complex), the scalar-extension and localization modules `HyperextScalarExtension`, `HyperextScalarEdgeMap`, `HyperextExtBaseChange`, `HyperextExtBaseChangeSummand`, `HyperextIsotypicBaseChange`, `HyperextIsotypicDegenerationBaseChange`, `HyperextHomLocalization`, `HyperextInvariantsLocalization`, `HyperextIsotypicLocalization` and `HyperextAbutmentLocalization`, and `DivisibleSystem.AdicHyperext` (the `ℓ`-adic hyperext spectral sequence of an `ℓ`-divisible system of complexes). All are in `Langlands.Cohomology`. The missing geometry: the analytic spaces, uniformization and equivariant étale sites | Analytic sites (`Langlands/Sheaf/Equivariant/`); Shimura geometry (`Langlands/Shimura/`) |
| Unitary Shimura cohomology with general algebraic coefficients | Shimura varieties as schemes, level towers, Hecke and Galois actions on étale cohomology with coefficient systems. The Library has the coefficient sheaves (`Langlands.Shimura.Coefficients`) and proves similitude representability (the theorem `Langlands.Shimura.similitudeRepresentability`, module `Langlands.Shimura.Unitary.RepresentabilityProof`). In namespace `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`, the scheme level tower `cmSchemeTower` (module `HarrisTaylorCMSchemeLevels`), the scheme Hecke correspondences `cmHeckeLeft` and `cmHeckeRight` (`HarrisTaylorCMHeckeSchemes`) and the Galois actions on the cohomology of the geometric CM torsion coefficient system, such as `cmHarrisGeometricGaloisCohomologyAction` (`HarrisTaylorCMGeometricGaloisCohomology`), all take a proof `q` of `CMRepresentabilityStatement` as an argument. That statement, the representability of Harris's PEL moduli problem, is not proved; its division-algebra case is `DivisionCMRepresentabilityStatement`, of which this note records no proof. Generic level-tower constructions (`Langlands.Shimura.LevelTowerCohomology`, `Langlands.Shimura.LevelTowerGalois`) exist. Library commits after `f73044d9` add the cohomology of level towers of schemes away from a fixed factor of the level (`Langlands.Shimura.SplitLevelTowerCohomology`, `Langlands.Shimura.RestrictedSplitLevelTowerCohomology`), applied there to the splitting of the finite adelic points at the places dividing an integer `m`, with Harris 1999 Prop. 4.10 (p.311) as motivation, and the level spaces at such split levels (`Langlands.Shimura.SplitLevelSpace`, `Langlands.Shimura.Unitary.HarrisSplitTower`). Library commits after `2816ea5d` apply the restricted split cohomology to the conditional CM schemes: `Langlands.Shimura.PEL.HarrisTaylorCMPrimeToCohomology` (the prime-to-`m` colimit cohomology over the levels `e⁻¹ (K₀ × K')` and its comparison with the colimit over all small levels) and `Langlands.Shimura.PEL.HarrisTaylorCMPrimeToGaloisCohomology` (the Galois action on it, and the `K'`-fixed vectors as modules over the Hecke algebra of `K'` with a commuting Galois action). The level spaces are not used by any statement of this framework. The cohomology statements about the conditional schemes are the two of `HarrisCMCohomology`, at one level and one torsion stage; unramifiedness outside one finite set of places at one level, for all torsion stages (`HarrisCMCohomologyUnramified`); and five across levels: Galois smoothness of the colimit over all small levels (`HarrisCMLevelGaloisSmooth`) and of the prime-to-`m` colimit (`HarrisCMPrimeToGaloisSmooth`), the comparison of level-`U` cohomology with invariants at finite level (`HarrisCMLevelInvariants`) and in the colimit (`HarrisCMColimitInvariants`), and the comparison of the prime-to-`m` cohomology with the `K₀`-invariants (`HarrisCMPrimeToInvariants`). Library commit `568f1cff` adds `Langlands.Shimura.PEL.HarrisTaylorCMDecompositionCohomology`, which restricts these Galois actions to the absolute Galois groups of the completions `F_w` and defines geometric Frobenius endomorphisms of the Hecke modules; it proves no unramifiedness, and its Frobenius results take unramifiedness as a hypothesis. It also adds the `Langlands.Shimura.PEL.HarrisTaylorCMGeometricLatticeInverseImage`, a comparison of Harris's geometric coefficient systems at two nested small levels. Library commit `c0c7eab6` adds the isotypic parts `H[ξ]` and multiplicity spaces `Hom(ξ, H)` of the shrinking-level and prime-to-`m` cohomology with coefficients pulled back from `Spec F`, for an arbitrary representation `ξ`, with their Galois actions (`Langlands.Shimura.PEL.HarrisTaylorCMIsotypicCohomology`, over the generic `Langlands.Shimura.IsotypicGaloisAction`), and their restrictions to the decomposition groups (`Langlands.Shimura.PEL.HarrisTaylorCMIsotypicDecompositionCohomology`, over the generic `Langlands.Shimura.IsotypicDecompositionAction`). Their Markdown cites Harris 1999 p.312 and Thm 5.7 (p.313) as motivation only; unramifiedness passes to the isotypic parts, but only as a hypothesis. The same commit adds the comparisons of the pair and triple coefficient systems at nested small levels (modules `HarrisTaylorCMCoefficientPairTriple`, `HarrisTaylorCMGeometricPairTriple` and `HarrisTaylorCMGeometricPairCoherence` in `Langlands.Shimura.PEL`), and the module `Langlands.Shimura.PEL.HarrisTaylorCMCoefficientUpperPair`. Library commits after `c0c7eab6`, up to `ddb0a9c0`, add the following modules of `Langlands.Shimura.PEL`. `HarrisTaylorCMLevelGaloisCohomology`: the Galois action on `H^d(X̄_U, p_U^* M)` at one fixed small level `U`, natural in the sheaf `M` on `Spec F`, with a Galois-equivariant insertion into the colimit over all small levels, and the same at the prime-to-`m` levels. `HarrisTaylorCMLevelAdicGaloisCohomology`: inverse limits of this fixed-level cohomology along an inverse system `M_k` of sheaves on `Spec F`, whose Galois action is continuous when every stage is smooth, an explicit hypothesis. `HarrisTaylorCMAdicGaloisCohomology`: the limit `cmHarrisAdicCohomology`, over the torsion stages `r`, of `H^d(X̄_U, B_r)`, where `B_r` is the `r`-th stage of the coefficient system, the stable lattice reduced modulo the `r`-th power of the scalar ideal `(m)` of the coefficient ring. This `m`-power torsion limit is the `(m)`-adic analogue of integral `λ`-adic cohomology; its Markdown states that it is not identified with Harris's `λ`-adic cohomology. Its Galois action is continuous under `HarrisCMGaloisCohomologySmoothStatement`, taken as a hypothesis, and `cmHarrisAdicCohomology_isUnramifiedAt` shows that it is unramified at every finite place where every stage is. `HarrisTaylorCMLambdaAdicRepresentation`: when this limit is finite free over the coefficient ring, its extension of scalars to the completion `K_l` of the number field `K` of the coefficients at a place `l` of `K` above the rational place `p` of the construction is an `l`-adic representation (`GaloisRepresentation.LambdaAdic`) under the hypothesis `CMHarrisAdicIsLatticeContinuous`, with an Euler polynomial at every finite place where every stage is unramified. `HarrisTaylorCMMultiplicityGaloisRepresentation`, `HarrisTaylorCMFixedVectorGaloisRepresentation` and `HarrisTaylorCMHeckeMultiplicityGaloisRepresentation`: multiplicity spaces, fixed vectors and Hecke multiplicity spaces of the cohomology with coefficients pulled back from `Spec F`, as continuous Galois representations. For the colimit over all small levels these three take `HarrisCMLevelGaloisSmoothStatement` as a hypothesis; for the prime-to-`m` colimit they take smoothness as an explicit `IsSmooth` hypothesis, not `HarrisCMPrimeToGaloisSmoothStatement`. They rest on generic modules of `Langlands.Shimura`: `ContinuousGaloisAction`, `FixedVectorGaloisRepresentation`, `FrobeniusPolynomial`, `HeckeMultiplicityGaloisRepresentation`, `LatticeGaloisRepresentation`, `LevelAutomorphismAction`, `LimitGaloisAction` and `MultiplicityGaloisRepresentation`. The same commits add the coefficient comparisons `HarrisTaylorCMCoefficientCoarseTower`, `HarrisTaylorCMGeometricLatticeInverseImageCoherence`, `HarrisTaylorCMGeometricLatticeInverseImageIdentity`, `HarrisTaylorCMGeometricUpperPairCoherence`, `HarrisTaylorCMGeometricUpperPairOriginalEndpoint` and `HarrisTaylorCMGeometricUpperPairOwnEndpoint` (in `Langlands.Shimura.PEL`) and `HarrisLatticeCommensurability` and `LatticeCommensurability` (in `Langlands.Shimura.Coefficients`), and `HarrisTaylorCMGeometricCoarseTower`, `HarrisTaylorCMGeometricCoarseTowerCoherence` and `HarrisTaylorCMGeometricUpperPair` (in `Langlands.Shimura.PEL`) and `EtaleInverseImageConstantProduct`, `EtaleInverseImageGroupCoverChange`, `EtaleInverseImageProductIdentity` and `HarrisLatticeReducedComparison` (in `Langlands.Shimura.Coefficients`). None of these modules defines a theorem statement; their only new propositions are the hypotheses `LatticeGaloisRepresentation.IsLatticeContinuous` and `CMHarrisAdicIsLatticeContinuous`. No proposition is stated about Hecke operators on cohomology or Frobenius eigenvalues, about unramifiedness of the cohomology across levels or of its isotypic parts, or about the finiteness, freeness or lattice continuity of the `m`-power torsion limit. Unramifiedness of that limit at one level, outside one finite set of places and in every degree, follows from `HarrisCMCohomologyUnramifiedStatement` by `cmHarrisAdicCohomology_isUnramifiedAt` (see [Conjunctions and one-line consequences](#conjunctions-and-one-line-consequences)). The Library at `4b619cdd` also has the following modules on Harris's coefficient prime and on `λ`-adic cohomology. `HarrisTaylorCMEllAdicGaloisCohomology` defines Harris's coefficient prime `harrisCoefficientPrime p`, the residue characteristic `ℓ` of the rational place `p`, and specializes the `m`-power torsion limit above to `m = ℓ`: `cmHarrisEllAdicCohomology`, whose stage `r` has coefficients modulo `ℓ^r`, with a continuous Galois action under `HarrisCMGaloisCohomologySmoothStatement` (`continuous_cmHarrisEllAdicAction`), and its `l`-adic representations `cmHarrisEllAdicRepresentation` under finite freeness and `CMHarrisAdicIsLatticeContinuous`. `HarrisTaylorCMLambdaCohomology` defines the `λ`-adic cohomology `cmHarrisLambdaCohomology`, `H^d(S_U ×_F F̄, W)_λ = K_λ ⊗ lim_r H^d(X̄_U, ℒ_r)` at one small level `U` with its Galois action, without assuming that the torsion limit is finite or free (provenance: Harris 1999 p.311; Milne, *Étale cohomology*, V §1). It states as propositions the finite dimensionality of this space, the continuity of its Galois action, and its unramifiedness at a finite place and at all but finitely many finite places (`CMHarrisLambdaCohomologyFiniteDimensional`, `CMHarrisLambdaCohomologyContinuous`, `CMHarrisLambdaCohomologyUnramifiedAt`, `CMHarrisLambdaCohomologyAlmostEverywhereUnramified`); no Library theorem proves them or takes them as hypotheses. It proves `cmHarrisLambdaCohomologyUnramifiedAt_of_stages`: the `λ`-adic cohomology is unramified at a place where every torsion stage is. Its Markdown states that it constructs no level-change map, finite-adelic action or isotypic part. In namespace `Langlands.Shimura.SmallLevelGaloisTower`, `HarrisTaylorCMSmallLevelGaloisTower` makes the colimit, over the small CM levels, of an arbitrary level-trivial presheaf of modules with a commuting action at every level a smooth representation of `G(A_f)` with that commuting action (`towerAction`), and defines the module `towerHeckeModule` over the level Hecke algebra; it states the fixed-vector comparison as the proposition `TowerFixedVectorComparison`, which is not proved and is a hypothesis of theorems in `HarrisTaylorCMSmallLevelGaloisIsotypic`. That module defines, for such a presheaf of `K`-modules with Galois actions, a field `M` over `K` and a representation `τ` of `G(A_f)` over `M`, the isotypic part `towerIsotypic`, its fixed vectors at a level `towerIsotypicFixedVectors`, the multiplicity space `towerMultiplicity` and the Hecke multiplicity space `towerHeckeMultiplicity`. Assume the fixed-vector comparison, topologies on `K` and `M` that make `M` a topological ring (`IsTopologicalRing M`) and for which `algebraMap K M` is continuous, a level `U`, and continuous orbit maps of the Galois action on `H(U)` (`HasContinuousOrbits`). Then the module makes the last three spaces Galois representations, through the generic `Langlands.Shimura.ContinuousIsotypicGaloisRepresentation`: the fixed vectors of the isotypic part at the level `U` when `H(U)` is finite-dimensional over `K` (`towerIsotypicFixedVectorsObjects`); the multiplicity space when it is finite-dimensional over `M` and, as the explicit hypothesis `hgen`, the translates of the vectors of `τ` fixed by the level of `U` span the space of `τ` (`towerMultiplicityObjects`); and the Hecke multiplicity space at the level `U` when it is finite-dimensional over `M` (`towerHeckeMultiplicityObjects`). For an arbitrary `τ` the spanning condition `hgen` is an extra assumption; it does not follow from the finite dimensionality of the multiplicity space. When `F` is a number field, each of the three has an Euler polynomial at every finite place of `F` where `H(U)` is unramified, the multiplicity space again under `hgen`. The Markdown of the two tower modules names `U ↦ H^d(S_U ×_F F̄, W)_λ` as the intended input, and Harris's `H^{n-1}(S_K(N), W)[π]` (p.312) as `towerIsotypicFixedVectors` for `d = n − 1`, `τ = JL(π_f)` and `U = K(N)`; the modules do not use that input. The level-change maps and the finite-adelic action on `H^d(S_U ×_F F̄, W)_λ`, which come from the equivariant structure of `W` with `ℓ` inverted, and with them the isotypic parts and multiplicity spaces with `W` coefficients, were not in the Library at `4b619cdd`. The module `Langlands.Shimura.PEL.HarrisTaylorCMLambdaTower` (see [Published constructions used](#published-constructions-used)) supplies them, and `CMHarrisVanishingStatement` and the `CMHarrisTheorem57Statement` use it | Shimura geometry (`Langlands/Shimura/`); the division case of representability, `DivisionCMRepresentabilityStatement` (this note records no proof); the `λ`-adic cohomology with `W` coefficients as a tower with level and finite-adelic actions, its isotypic parts and multiplicity spaces, in `Langlands.Shimura.PEL.HarrisTaylorCMLambdaTower` |
| Canonical split-supercuspidal local-global compatibility (Harris 1998 Thm 1.7; Harris 1999 Thm 5.7, 5.9, Cor. 5.10) | All of the above, and the automorphic and Galois objects. Of the almost-everywhere unramified association, only unramifiedness outside a finite set for finite constant coefficients is stated: on finite-type schemes with a set depending on the coefficients (`EtaleGaloisUnramified`), and on smooth proper schemes with one set for all coefficients (`EtaleGaloisGoodReduction`). For the Library's CM cohomology, unramifiedness outside one finite set is stated at one fixed level for the torsion coefficient stages (`HarrisCMCohomologyUnramified`), and it passes to their `m`-power torsion limit (see the Shimura row). The Library's `HarrisTaylorCMLambdaAdicRepresentation` turns that limit, when it is finite free and satisfies `CMHarrisAdicIsLatticeContinuous`, into `l`-adic representations, with Euler polynomials at the places where every stage is unramified; they are not identified with Harris's `λ`-adic representations. Unramifiedness of the colimits over levels, Harris's `λ`-adic representations themselves, and Frobenius eigenvalues are not stated. The Library's `HarrisTaylorCMDecompositionCohomology` and `HarrisTaylorCMIsotypicDecompositionCohomology` take unramifiedness as a hypothesis. Theorem 5.9(i) (Clozel, Kottwitz: a pure compatible family attached to `Π`, with unramified Euler factors matching almost everywhere) is stated as `GaloisRepresentation.Harris1999Theorem59iStatement` (`Langlands/Galois/Harris1999Theorem59Statement.md`). The canonical comparison in Theorem 5.9(ii), identifying the restriction with `σ(Π_v)` of (5.4)–(5.5), is not stated; it needs the tower (see the `σ(π_v)` row below). The two derived propositions in `Langlands.Galois.Harris1999Theorem59iiParameterStatement` are published (see [Published modules](#published-modules)); neither mentions the cohomological parameter. Another consequence, comparing two restrictions without `σ(π_v)`, is stated as `Langlands.GaloisRepresentation.HarrisSupercuspidalLocalComparisonStatement` (module `Langlands.Galois.HarrisSupercuspidalLocalComparisonStatement`, first appeared at `af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e`), as an input to the proof of Harris 1998 Prop. 4.8 (pp.202–203). Over a CM field `K` containing an imaginary quadratic field, take two regular algebraic, conjugate self-dual cuspidal representations of the same rank `r + 1 > 1`, a finite place `v` with `Harris.conjPlace K v ≠ v` at which the local components of chosen spectral presentations of both are supercuspidal, and two pure `λ`-adic families of a common weight, with common coefficient field and complex embedding, weakly associated to them. If these two components at `v` are equivalent, then for every `λ` of residue characteristic different from that of `v` the restrictions of the two `λ`-adic representations to the absolute Galois group of `K_v` are isomorphic. Its Markdown lists Theorem 5.9(ii) at `v`, the correction (5.4)–(5.5), the normalization of weights and the descent of the isomorphism to `L_λ` among the obligations of a proof; this note records no proof of it. The Library's `harrisSupercuspidalLocalComparison_of_canonical` (`Langlands/Galois/HarrisSupercuspidalLocalComparisonReduction.lean`) uses the two derived propositions as premises. The companion `harrisSupercuspidalRestrictionIrreducible_of_pureWitness` (`Langlands/Galois/HarrisSupercuspidalIrreducibilityReduction.lean`) reduces universal irreducibility to one suitable pure, absolutely irreducible witness family for each eligible realization (at all coefficient places of residue characteristic different from `p_v`). These are conditional reductions, not proofs of those premises or published proofs of the pairwise comparison. Harris 1999 (5.1), p.312, `H^j(S_K(N), W)[π] = 0` for `j ≠ n − 1`, where `π` is a representation of `GJ` whose component `π_v` at the chosen place is supercuspidal and `[π]` denotes the `JL(π_f)`-isotypic component, is stated as `CMHarrisVanishingStatement` (see [Published modules](#published-modules)), with Harris's hypothesis (R) of Harris 1997. It needs no Drinfeld tower. It takes `JL(π_f)` over the coefficient field of the cohomology, a field `M` extending `K_λ`, as a model `τ` through a field isomorphism `j : M ≃+* ℂ`, as the statement of Theorem 5.7(i)–(ii) does. The isomorphisms (5.2) and (5.3), p.312, need the compactly supported cohomology of the Drinfeld tower `M_N`. Theorem 5.7(iii), p.313, that the decomposition group at `v` acts on `H^{n-1}(S_K(N), W)[π]` through `σ(π_v)`; Lemma 5.8, p.314, the behaviour of `σ(π_v)` under unramified twists; and Corollary 5.10, p.315, the same action at the other split places `w` with `π_w` supercuspidal, all need `σ(π_v)` and so the tower (the `σ(π_v)` row below). Theorem 5.7(i)–(ii) are stated (the last row of this table) | This framework, after the prerequisites |
| The transfer `JL(π_f)` from `GJ` to `GG` (Harris 1999 §5, p.312: the local constituents agree away from `v` and correspond at `v` by the local Jacquet–Langlands correspondence [DKV, R]), used in (5.1), (5.3), Theorem 5.7 and Theorem 5.9 | Defined as a relation, with no existence theorem. The `Langlands.JacquetLanglands.IsHarrisJacquetLanglandsTransfer` (module `Langlands.JacquetLanglands.HarrisTransfer`, in the Library since commit `b128d289`) says that a representation `ρ` of `GJ(A_f)` and a representation `ρ'` of `GG(A_f)` are irreducible and admissible, have one common constituent away from `v` under Harris's identifications of the two groups there, and have constituents at `v` related by the local relation `IsJacquetLanglandsPair`. The splittings at `v` and the identifications away from `v` are inputs, not constructed. Supercuspidality at `v` is not included; `CMHarrisVanishingStatement` adds it as a separate hypothesis, and Theorems 5.7 and 5.9 and Corollary 5.10 would do the same. Existence and uniqueness of `JL(π_f)` are not asserted. The relation builds on the local Jacquet–Langlands correspondence, given as definitions and unproved statements in `Langlands/JacquetLanglands/`: the unit group `D^×` (`DivisionUnits`), the correspondence of regular elliptic elements (`RegularElliptic`), the character-identity relation `IsJacquetLanglandsPair` (`Relation`), the bijection, central-character and twist statements (`Statements`) and their analytic input (`CharacterStatements`). It also uses the generic relation `IsAwayTransfer` (`AwayTransfer`) and the splitting of Harris's groups at the distinguished place, `harrisAwaySplitGL` and `harrisComplementEquiv` (`HarrisAwaySplitting`). `CMHarrisVanishingStatement` ((5.1)) and the `CMHarrisTheorem57Statement` (Theorem 5.7(i)–(ii)) use the transfer; the other statements that use it still wait for `σ(π_v)` (the `σ(π_v)` row below) | The local Jacquet–Langlands correspondence (`Langlands/JacquetLanglands/`); the compatible Galois families ([galois-family-coverage](galois-family-coverage.md)) also need it |
| Harris's twisting character `ν̄(π)` (Harris 1999 p.313: Theorem 5.7(i) and (5.4); the text extraction of the scan renders it as `V(π)`). It is defined in the Erratum of Harris 1998, (E.1)–(E.2), printed p.181, from the central character of `π` on the connected center `Z` of `GG` and the algebraic character `r_μ` composed with complex conjugation. Harris 1998 (E.4), p.182, is (5.4) | Defined, with no existence theorem. The `Langlands.Galois.HarrisTwistingCharacter` defines the Hecke characters `Langlands.Global.Harris.nuCharacter` ((E.1)) and `Langlands.Global.Harris.nuBarCharacter` ((E.1) with (E.2)), and the relation `Langlands.GaloisRepresentation.Harris.IsNuBarRealization`, which says that a given `λ`-adic character of `Gal(𝒦̄/𝒦)` realizes `ν̄(π)`. That such a realization exists is not asserted. The cohomology of the Drinfeld tower is not needed | `Langlands.Galois.HarrisTwistingCharacter` (see [galois-family-coverage](galois-family-coverage.md)) |
| Harris's local Galois representation `σ(π_v) = [σ̃(π_v) ⊗ ν̄(π)_v^{-1}]^*` of (5.4) (Harris 1999 p.313), used in Theorem 5.7(iii) | `σ̃(π_v) = [Hom_{GJ}(H_c^{n-1}(M̆_N, Q̄_ℓ)_{SS(F)}, π_p) ⊗ JL(π_v)^*]^{GG}` of (5.5): the compactly supported cohomology of the Drinfeld tower `M̆_N`, semisimplified as a representation of `Gal(F̄/F)`, with its group actions; and the local Jacquet–Langlands correspondent `JL(π_v)` (the first row above) | The Drinfeld tower: analytic spaces (`Langlands/Geometry/Analytic/`), which are to cover the spaces of Harris 1999 §2 and the uniformization (4.3). `ν̄(π)` and `JL(π_v)` as in the two previous rows; Library commit `4b619cdd` has the Drinfeld upper half space `Ω` with its group action and Harris's covering of it by domains (modules `Drinfeld*` in `Langlands/Geometry/Analytic/`), but not the tower `M_N` of its coverings. The tower is defined through the moduli problem of special formal `O_D`-modules. Library commit `c40a0134` has, for that formal-group side, in `Langlands/Geometry/FormalGroup/` (101 modules), formal `O`-modules (`FormalModule`), quasi-isogenies (`RationalMorphism`, `LocalQuasiIsogeny`, `OrderRationalMorphism`), special formal `O_D`-modules in coordinates (`SpecialModule`, `SpecialAtlas`; Drinfeld 1976 §2A, p.109) and Deligne's sheaf data (modules `Deligne*`); `SpecialAtlas.md` says that no full Drinfeld functor and no representability is asserted. At `d6b462be`, the [`DrinfeldLevelOneBase`](../../Langlands/Geometry/Analytic/DrinfeldLevelOneBase.md) builds the analogue of `ℳ_1 = Ω × Δ` for the matrix factor `GL_{d+1}(F)`. `omegaActionContinuity` proves continuity on `Ω`, and the `DrinfeldLevelOneEtale` gives conditional applications for this factor as described above. These modules do not construct `ℳ_N` for `N ≥ 2`, the full action of `G_J`, or Harris's `S(ê)`; in particular they do not supply the spaces with group and Galois actions needed by (5.5) |
| Compatible Galois-family existence and multiplicity removal, and Harris 1999 Theorem 5.7(i)–(ii) | Treated elsewhere. The note [Compatible Galois families from unitary Shimura cohomology](galois-family-coverage.md) maps them to Library declarations, among others `Clozel1991Theorem57Statement`, `TaylorMultiplicityRemovalStatement`, `Harris1998Theorem12Statement` and `Harris1999Theorem59iStatement` in namespace `Langlands.GaloisRepresentation`. At the earlier commit `4b619cdd`, section 3 of that note listed what was not yet stated, among them Kottwitz 1992 Theorem 1 and Harris 1999 Theorem 5.7(i)–(ii); both waited, among other inputs, for the isotypic parts of the `λ`-adic tower cohomology and for unramified base change for unitary similitude groups. Both are now published statements, on the isotypic parts of `HarrisTaylorCMLambdaTower`, listed in [section 1.5](galois-family-coverage.md#15-statements-on-the-cohomology-of-the-cm-shimura-varieties) of that note: Kottwitz 1992 Theorem 1 as `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.CMHarrisKottwitzLambdaAdicStatement` (module `Langlands.Shimura.PEL.HarrisTaylorCMKottwitzStatement`), and Theorem 5.7(i)–(ii) as `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.CMHarrisTheorem57Statement` (module `Langlands.Shimura.PEL.HarrisTaylorCMHarrisTheorem57Statement`, first appeared at `b3a1bdaf`). The current section 3 of that note says that every statement of the note is now stated, and lists the remaining source and proof boundaries, for Kottwitz's theorem in [section 3.1](galois-family-coverage.md#31-kottwitz-1992-theorem-1-cmharriskottwitzlambdaadicstatement). None of these six statements is proved: at `1ddfc485` no other Library Lean file uses them (`Langlands.Shimura.PEL.HarrisTaylorCMLambdaHodgeTateStatement` only imports the module `Langlands.Galois.TaylorMultiplicityRemovalStatement`). The correction of that statement, in the Library at `320321b3` at the same paths, adds two hypotheses: Harris's condition (R) of Harris 1997 p.79, in the form used by `CMHarrisVanishingStatement`, and that the algebra `D'` of `GJ` is a division algebra (Harris 1997 p.80). `CMHarrisVanishingStatement` has the first hypothesis but not the second | See [galois-family-coverage](galois-family-coverage.md) |
| Proofs of the components not listed under [Proved statements](#proved-statements) | Each needs its own proof | — |

Dependencies among these parts. The statement modules feed four larger targets: Harris's
coefficient spectral sequence, the split-supercuspidal local–global compatibility, global
Galois existence and Berkovich's equivariant resolution. The half-bounded convergence
(`HyperextConvergence.HalfBoundedStatement`) uses the hyperext spectral sequence and its
abutment filtration, and Berkovich's equivariant resolution uses it. The local
Jacquet–Langlands correspondence and Harris's twisting character are prerequisites of the
split-supercuspidal compatibility and of Theorem 5.7(i)–(ii). That compatibility also uses the
`λ`-adic cohomology with `W` coefficients, for the isotypic part `H^{n-1}(S_K(N), W)[π]` of
(5.1), Theorem 5.7(iii) and Corollary 5.10; the Drinfeld tower, for the tower cohomology in
(5.2), (5.3) and (5.5); and (5.1) itself, which in turn uses the `λ`-adic cohomology and the
Jacquet–Langlands correspondence. Harris 1998 Proposition 4.8 (its prime branch and its
reduction) uses `HarrisSupercuspidalLocalComparisonStatement`, which uses the
split-supercuspidal compatibility; the two derived Theorem 5.9(ii) propositions record the
source route through the canonical comparison.

On the analytic side, the quasi-étale comparison of Theorem 1.6.1(ii) uses the analytic
quasi-étale cohomology, its refinement hypotheses and Berkovich's `G`-spaces, and the smoothness
results of `AnalyticRepSmoothness` use it. The étale comparison uses the étale global
comparison map, the étale refinements and the `G`-spaces. The two composites of §1.2 use the
constant `G`-sheaf adjunction, the bounded-below derived complexes and the global complexes,
and respectively the étale global comparison map and the analytic quasi-étale cohomology. The
étale compact comparison uses the étale comparison map, the étale refinements, analytic compact
support, the `G`-spaces and geometric points; the étale compact smoothness results use it. The
§1.2 spectral sequences use the two analytic composites, the half-bounded convergence and the
global complexes; the étale topos comparison uses the inverse image, the invariant sheaf, the
smooth part of a local action and the induced spaces.

On the CM side, the finiteness and smoothness statements of `HarrisCMCohomology` use the
conditional CM scheme tower and the representability target, and the CM `ℓ`-adic Galois
cohomology (`Langlands.Shimura.PEL.HarrisTaylorCMAdicGaloisCohomology`) and the
split-supercuspidal compatibility use them. The five statements across levels also use the
representability target, the first three also the conditional scheme tower;
`HarrisCMLevelGaloisSmooth` further uses the restricted level colimit and its canonical Galois
action; `HarrisCMLevelInvariants` the level-tower cohomology and the normal actions and torsor;
`HarrisCMColimitInvariants` the level-tower cohomology, the restricted level colimit and
`HarrisCMLevelInvariants`; `HarrisCMPrimeToInvariants` the prime-to-`m` cohomology and
`HarrisCMColimitInvariants`; and `HarrisCMPrimeToGaloisSmooth` the prime-to-`m` Galois
cohomology and `HarrisCMLevelGaloisSmooth`. The modules
`HarrisTaylorCMMultiplicityGaloisRepresentation`,
`HarrisTaylorCMFixedVectorGaloisRepresentation` and
`HarrisTaylorCMHeckeMultiplicityGaloisRepresentation` of `Langlands.Shimura.PEL` take
`HarrisCMLevelGaloisSmoothStatement` as a hypothesis. `EtaleGaloisUnramified` and
`EtaleGaloisGoodReduction` use the étale Galois action and the CM decomposition cohomology, and
`HarrisCMCohomologyUnramified` uses the conditional scheme tower, the representability target
and the CM decomposition cohomology.

## Proved statements

Each theorem in the following table has one of the statements above as its
type, with exactly the parameters, universe levels and instance arguments of
that statement, so it proves the statement wherever the statement is defined.
Names that do not begin with `Langlands.` are relative to
`Langlands.Cohomology`. "Builds on" lists the Library modules, other than the
statement module, that the proof module imports; Mathlib imports are omitted.
Each proof module's Markdown describes its proof.

| Statement (conjunction) | Theorem | Proof module | Builds on |
| --- | --- | --- | --- |
| `ResolutionLiftStatement` (`AcyclicResolutionComparisonStatements`) | `resolutionLiftStatement` | [`AcyclicResolution.LiftProof`](../../Langlands/Cohomology/AcyclicResolution/LiftProof.md) | the `AcyclicResolution.Lift` |
| `AcyclicResolutionComparisonStatement` (the same) | `acyclicResolutionComparisonStatement` | [`AcyclicResolution.ComparisonProof`](../../Langlands/Cohomology/AcyclicResolution/ComparisonProof.md) | the `ExtendMap` and `RightDerivedSequence` |
| `ResolutionComparisonIndependenceStatement` (the same) | `resolutionComparisonIndependenceStatement` | [`AcyclicResolution.IndependenceProof`](../../Langlands/Cohomology/AcyclicResolution/IndependenceProof.md) | the `AcyclicResolution.Comparison` |
| `ResolutionComparisonNaturalityStatement` (the same) | `resolutionComparisonNaturalityStatement` | [`AcyclicResolution.NaturalityProof`](../../Langlands/Cohomology/AcyclicResolution/NaturalityProof.md) | the `AcyclicResolution.Comparison` |
| `ResolutionComparisonTransformationStatement` (the same) | `resolutionComparisonTransformationStatement` | [`AcyclicResolution.TransformationProof`](../../Langlands/Cohomology/AcyclicResolution/TransformationProof.md) | No Library module |
| `HyperextDegenerationStatement` | `hyperextDegenerationStatement_proof` | [`HyperextDegeneration.Proof`](../../Langlands/Cohomology/HyperextDegeneration/Proof.md) | the `HyperextGradedVanishing` and `HyperextEdgeMapSurjective` |
| `SmoothGodementComparison.SmoothGodementComparisonZeroStatement` (`SmoothGodementComparisonStatements`) | `SmoothGodementComparison.smoothGodementComparisonZero` | [`SmoothGodementComparison.ZeroProof`](../../Langlands/Cohomology/SmoothGodementComparison/ZeroProof.md) | the `AcyclicResolution.Comparison` |
| `SupercuspidalExt.CompactInductionExtReciprocityStatement R G`, for every commutative ring `R` (`SupercuspidalExtStatements` at `R = ℂ`; `SupercuspidalExtCharZeroStatements` at `R = k`) | `SupercuspidalExt.compactInductionExtReciprocity` | [`SupercuspidalExt.ReciprocityProof`](../../Langlands/Cohomology/SupercuspidalExt/ReciprocityProof.md) | the `SupercuspidalExt.Reciprocity` |
| `SupercuspidalExtCharZero.CompactCoefficientInjectiveProjectiveStatement` (`SupercuspidalExtCharZeroStatements`) | `SupercuspidalExtCharZero.compactCoefficientInjectiveProjective` | [`SupercuspidalExtCharZero.InjectiveProjectiveProof`](../../Langlands/Cohomology/SupercuspidalExtCharZero/InjectiveProjectiveProof.md) | `SupercuspidalExtCharZero.Admissibility`, `SupercuspidalExtCharZero.Injectivity`, `SupercuspidalExtCharZero.Projectivity` |
| `SupercuspidalExtCharZero.CompactInductionSupercuspidalExtVanishingStatement` (the same) | `SupercuspidalExtCharZero.compactInductionSupercuspidalExtVanishing` | [`SupercuspidalExtCharZero.VanishingProof`](../../Langlands/Cohomology/SupercuspidalExtCharZero/VanishingProof.md) | The two proof modules above: `SupercuspidalExtCharZero.InjectiveProjectiveProof` and `SupercuspidalExt.ReciprocityProof` |
| `SupercuspidalRestriction.UnitDeterminantSubgroupStatement` (`GLSupercuspidalRestrictionStatements`) | `SupercuspidalRestriction.unitDeterminantSubgroupStatement_proof` | [`SupercuspidalRestriction.UnitDeterminantProof`](../../Langlands/Cohomology/SupercuspidalRestriction/UnitDeterminantProof.md) | the `Langlands.Representation.CuspidalSupport.DeterminantUnitStructureProof`; `Langlands.Group.GL.OneBlockShape` |
| `SupercuspidalRestriction.GLHarishChandraStatement` (the same) | `SupercuspidalRestriction.glHarishChandraStatement_proof` | [`SupercuspidalRestriction.HarishChandraProof`](../../Langlands/Cohomology/SupercuspidalRestriction/HarishChandraProof.md) | `Langlands.Representation.GodementJacquet.SupercuspidalMatrixSupport` |
| `SupercuspidalRestriction.CompactModCenterRestrictionStatement` | `SupercuspidalRestriction.compactModCenterRestrictionStatement_proof` | [`SupercuspidalRestriction.CompactModCenterProof`](../../Langlands/Cohomology/SupercuspidalRestriction/CompactModCenterProof.md) | `Langlands.Representation.Category.FiniteIndexRestriction`, `Langlands.Representation.Schur.CountableDimensionProof`, `Langlands.Representation.CompactCoefficient.Subquotients`, `SupercuspidalRestriction.CompactCoefficientRestriction` |
| `HyperextConvergence.HyperextConvergenceStatements` | `HyperextConvergence.hyperextConvergenceStatements_proof` | [`HyperextConvergence.Proof`](../../Langlands/Cohomology/HyperextConvergence/Proof.md) | the `HyperextSecondPage` |
| `HyperextConvergence.HyperextHalfBoundedConvergenceStatements` | `HyperextConvergence.hyperextHalfBoundedConvergenceStatements_proof` | [`HyperextConvergence.HalfBoundedProof`](../../Langlands/Cohomology/HyperextConvergence/HalfBoundedProof.md) | the `HyperextConvergence.Proof` |
| `HyperextConvergence.CovariantSecondPageStatement` | `HyperextConvergence.covariantSecondPageStatement_proof` | [`HyperextConvergence.CovariantSecondPageProof`](../../Langlands/Cohomology/HyperextConvergence/CovariantSecondPageProof.md) | the `HyperextSecondPage` |
| `EquivariantComposite.EquivariantGlobalCompositeStatement` (`EquivariantComposite.EquivariantCompositeStatements`) | `EquivariantComposite.equivariantGlobalComposite` | [`EquivariantComposite.GlobalProof`](../../Langlands/Cohomology/EquivariantComposite/GlobalProof.md) | the `EquivariantComposite.ConstantAdjunction` and `EquivariantComposite.KInjectiveHomology`; `EquivariantComposite.InvariantsHom`; `AcyclicResolution.DerivedComparison` |
| `EquivariantComposite.CompactGroupCompactCompositeStatement` (the same) | `EquivariantComposite.compactGroupCompactCompositeStatement_proof` | [`EquivariantComposite.CompactProof`](../../Langlands/Cohomology/EquivariantComposite/CompactProof.md) | the `EquivariantComposite.InjectiveAcyclic` and `EquivariantComposite.AcyclicHomology`; the `DerivedPlusNaturality` |
| `AnalyticGlobalComposite.AnalyticEtaleGlobalCompositeStatement` | `AnalyticGlobalComposite.analyticEtaleGlobalComposite` | [`AnalyticGlobalComposite.EtaleProof`](../../Langlands/Cohomology/AnalyticGlobalComposite/EtaleProof.md) | the `AnalyticGlobalComposite.SmoothGlobalProof`, which imports the `AnalyticGlobalComposite.InvariantsHom` and `EquivariantComposite.GlobalProof`; the `Langlands.Sheaf.Equivariant.AnalyticConstantAdjunction` |
| `AnalyticGlobalComposite.AnalyticQuasiEtaleGlobalCompositeStatement` | `AnalyticGlobalComposite.analyticQuasiEtaleGlobalComposite` | [`AnalyticGlobalComposite.QuasiEtaleProof`](../../Langlands/Cohomology/AnalyticGlobalComposite/QuasiEtaleProof.md) | the `AnalyticGlobalComposite.SmoothGlobalProof`; the `Langlands.Sheaf.Equivariant.AnalyticConstantAdjunction` |
| `AnalyticQuasiEtaleGlobalComparison.AnalyticQuasiEtaleGlobalComparisonStatement` | `AnalyticQuasiEtaleGlobalComparison.analyticQuasiEtaleGlobalComparison` | [`AnalyticQuasiEtaleGlobalComparison.Proof`](../../Langlands/Cohomology/AnalyticQuasiEtaleGlobalComparison/Proof.md) | `AnalyticQuasiEtaleGlobalComparison.CompactTupleComparison` and `AnalyticQuasiEtaleGlobalComparison.CompactTupleConeAssembly`; the `Langlands.Geometry.Analytic.QuasiEtaleLiftCompatibilityProof` |

The two convergence theorems take the category `C` as an implicit argument,
where the statements take it explicitly; the instance arguments are the
same. At a given `C` the statement is proved by
`hyperextConvergenceStatements_proof (C := C)`, and likewise for the
half-bounded one. `covariantSecondPageStatement_proof` takes `C`
explicitly, as `CovariantSecondPageStatement` does, with the same instance
arguments `[Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]`; its type
is `CovariantSecondPageStatement.{w, w', v, u} C`. The two composite
statements and their theorems take no
arguments; they are universally quantified propositions at the universe
levels `w`, `w'` and `u`. `CompactProof` does not import its statement module
directly; it reaches it through `EquivariantComposite.InjectiveAcyclic`.
`analyticEtaleGlobalComposite` takes the arguments `X`, `G`, `ρ` and `R`
and the instance arguments of `AnalyticEtaleGlobalCompositeStatement`, and
its type is `AnalyticEtaleGlobalCompositeStatement.{w, u, v, uL, z} X G ρ R`.
`EtaleProof` reaches the statement module through
`AnalyticGlobalComposite.InvariantsHom`. Likewise
`analyticQuasiEtaleGlobalComposite` takes `X`, `G`, `ρ` and `R` and the
instance arguments of `AnalyticQuasiEtaleGlobalCompositeStatement`, and its
type is `AnalyticQuasiEtaleGlobalCompositeStatement.{w, u, v, uL, z} X G ρ R`.
`QuasiEtaleProof` reaches the statement module through
`AnalyticGlobalComposite.SmoothGlobalProof`. Both proofs apply the generic `AnalyticGlobalComposite.smoothGlobalComposite` to the respective
`G`-invariant global-section functor. `analyticQuasiEtaleGlobalComparison`
takes `ρ` and `R` explicitly, `X` and `G` implicitly, and the instance
arguments of `AnalyticQuasiEtaleGlobalComparisonStatement`; its type is
`AnalyticQuasiEtaleGlobalComparisonStatement.{u, v, uL, z} X G ρ R`. It uses
the existing `twistedQuasiEtaleTopology`, not a compact-probe replacement.

Two further components are proved by theorems in other modules:

- `EquivariantGodementUnderlyingStatement`, the second component of
  `EquivariantGodementStatements`, is proved by the theorem
  `Langlands.Cohomology.equivariantGodementUnderlying` in
  [`Langlands.Cohomology.EquivariantGodement.UnderlyingProof`](../../Langlands/Cohomology/EquivariantGodement/UnderlyingProof.md).
  Its proof packages the published constructions
  `underlyingComplexIso` and `underlyingComplexIso_augmentation` from
  [`Langlands.Sheaf.Equivariant.Godement.Underlying`](../../Langlands/Sheaf/Equivariant/Godement/Underlying.md).
- `SmoothCompactCohomology.CompactSectionsSmoothStatement`, the first
  component of `SmoothCompactCohomologyStatements`, is proved by the theorem
  `Langlands.Sheaf.Equivariant.CompactSections.isSmooth_representation_of_isSmoothSheaf`
  in
  [`Langlands.Sheaf.Equivariant.SmoothSheafCompactSections`](../../Langlands/Sheaf/Equivariant/SmoothSheafCompactSections.md).
  That theorem belongs to the construction module; no Library
  declaration has the statement itself as its type. The theorem's conclusion
  is the statement's, because the object of `CompactSections.functor` at `F`
  is `Rep.of (representation F.obj)`. The statement follows by `intro F hF`
  and applying the theorem to `hF`; this two-line proof compiles against
  Library `ddb0a9c0`.

### Conjunctions and one-line consequences

No Library declaration has any of the following as its type. Each term below,
except the last, was compiled in a separate Lean check against Library
`ddb0a9c0`; the last was compiled against Library `8ff9abe9` (no errors or
warnings). The check files are not in the Library. Names
are relative to `Langlands.Cohomology`. Inside the terms, namespace prefixes
are omitted; every name there is a declaration of a module cited in this note.

- `SupercuspidalExtCharZero.SupercuspidalExtCharZeroStatements k G μ` holds
  under exactly its own hypotheses, as
  `⟨SupercuspidalExt.compactInductionExtReciprocity k G,
  compactCoefficientInjectiveProjective k G μ,
  compactInductionSupercuspidalExtVanishing k G μ⟩`.
- `SupercuspidalExt.SupercuspidalExtStatements G μ`, for `G : Type`, is
  `supercuspidalExtStatements_of_charZero μ` applied to the previous
  conjunction at `k = ℂ`.
- `SupercuspidalRestriction.GLSupercuspidalRestrictionStatements F n` is
  `⟨unitDeterminantSubgroupStatement_proof F n, glHarishChandraStatement_proof F n,
  glSupercuspidalRestriction_of_compactModCenter F n
  (compactModCenterRestrictionStatement_proof _)
  (unitDeterminantSubgroupStatement_proof F n)
  (glHarishChandraStatement_proof F n)⟩`. This needs instances
  `TotallyDisconnectedSpace` and `SigmaCompactSpace` for `GL_n(F)` with the
  canonical topology. σ-compactness is supplied by the theorem named
  above, as `haveI : SigmaCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSigmaCompactSpace n`; the check
  compiled this form, with only `[TotallyDisconnectedSpace (GeneralLinear n
  F.Carrier)]` as a hypothesis. Total disconnectedness has no public
  declaration (see the end of [Published modules](#published-modules)), so the
  conjunction is proved only under that instance hypothesis. The three proof
  modules `UnitDeterminantProof`, `HarishChandraProof` and
  `CompactModCenterProof` import into one module since a correction
  gave the three local instances of `HarishChandraProof` module-specific
  names. Before it, that module and `UnitDeterminantProof` generated the same
  declaration name `instTopologicalSpaceCarrier_1` in namespace
  `Langlands.Cohomology.SupercuspidalRestriction`.
- Three of the five components of `FilteredColimitComparisonStatements R`
  follow from one-line terms. `ColimitCohomologyNaturalityStatement R` is
  Mathlib's `colimit.map_post f
  (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) q)`.
  `FilteredColimitQuasiIsoStatement R` is the `Langlands.Cohomology.ExactColimit.quasiIso_colimMap f hf` (module
  `Langlands.Cohomology.ExactColimitQuasiIso`).
  `FilteredColimitExactnessStatement R` is `hS.map_of_exact colim`, Mathlib's
  `ShortComplex.ShortExact.map_of_exact`. The last two use the instance that
  colimits over small filtered categories in `ModuleCat.{v} R` are exact,
  `Langlands.Cohomology.hasExactColimitsOfShape_moduleCat` in
  `Langlands.Cohomology.DivisibleSystem.InvariantLimit`, found by instance
  search once that module is imported. No Library or Mathlib result was found
  for `FilteredColimitCohomologyStatement` or
  `FilteredColimitCohomologyEquivarianceStatement`.
- `HarrisCMCohomologyUnramified.HarrisCMCohomologyUnramifiedStatement`, for a
  small CM level `U` and the premises of its module, implies that there is one
  finite set `S` of finite places of `F` such that, for every degree and every
  `w ∉ S`, the `m`-power torsion limit `cmHarrisAdicCohomology ... degree` of
  `HarrisTaylorCMAdicGaloisCohomology` is unramified at `w`
  (`DecompositionGroupAction.IsUnramifiedAt`). The term takes the set `S` of the
  statement and applies `cmHarrisAdicCohomology_isUnramifiedAt` at each degree
  and place to the unramifiedness of all stages. This is an implication; the
  statement itself is open.
- `EquivariantComposite.EquivariantCompositeStatements.{w, w', u}` is
  `⟨equivariantGlobalComposite.{w, w', u},
  compactGroupCompactCompositeStatement_proof.{w, w', u}⟩`.

No other component listed above is proved in Lean. In particular
`AcyclicResolutionEquivarianceStatement`, the isomorphism and naturality
components of `SmoothGodementComparisonStatements`, the second component of
`SmoothCompactCohomologyStatements`, `SupercuspidalExtSemisimpleStatements`,
both components of `HarrisCMCohomologyStatements`,
`HarrisCMLevelGaloisSmoothStatement`, `HarrisCMLevelInvariantsStatement`,
`HarrisCMColimitInvariantsStatement`, `HarrisCMPrimeToInvariantsStatement`,
`HarrisCMPrimeToGaloisSmoothStatement`,
`GaloisCohomologyUnramifiedStatement`,
`GaloisCohomologyGoodReductionStatement` and
`HarrisCMCohomologyUnramifiedStatement` are listed as open. Of eighteen
further propositions of this framework, eight have proofs in the Library. The
first five are the
convergence, second-page and topological composite statements; the last of
these, `CovariantSecondPageStatement`, is proved by the `covariantSecondPageStatement_proof`,
in the Library since commit
`b128d289`. The sixth is the étale composite
`AnalyticGlobalComposite.AnalyticEtaleGlobalCompositeStatement`, proved by
the `analyticEtaleGlobalComposite`, in the Library since commit
`ba00e097`. The seventh is the quasi-étale composite
`AnalyticGlobalComposite.AnalyticQuasiEtaleGlobalCompositeStatement`,
proved by the `analyticQuasiEtaleGlobalComposite`, in the Library at
`320321b3`. The eighth is
`AnalyticQuasiEtaleGlobalComparison.AnalyticQuasiEtaleGlobalComparisonStatement`,
proved by the `analyticQuasiEtaleGlobalComparison`, which first appeared at
`03296177`. Two of the other ten, on Berkovich's analytic sites, have no
proof in the Library (the second has a conditional one):
`AnalyticEtaleGlobalComparison.AnalyticEtaleGlobalComparisonStatement` and
`AnalyticEtaleCompactComparison.AnalyticEtaleCompactComparisonStatement`. Five
more have no proof in the Library either:
`AnalyticGlobalSpectralSequence.AnalyticEtaleGlobalSpectralSequenceStatement`,
`AnalyticGlobalSpectralSequence.AnalyticQuasiEtaleGlobalSpectralSequenceStatement`,
`AnalyticParacompactComparison.AnalyticEtaleParacompactComparisonStatement`,
`AnalyticParacompactComparison.AnalyticQuasiEtaleParacompactComparisonStatement`
and `Langlands.Sheaf.Equivariant.Analytic.EtaleGSheafToposComparisonStatement`.
The other three are
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.CMHarrisVanishingStatement`
(Harris 1999 (5.1)), and `Harris1999Theorem59iiParameterStatement` and
`HarrisSupercuspidalRestrictionIrreducibleStatement` in
`Langlands.GaloisRepresentation` (derived from Theorem 5.9(ii)). Three
statement modules also prove implications between statements, which prove
none of the statements themselves:
`supercuspidalExtStatements_of_charZero`,
`supercuspidalExtCharZeroStatements_of_semisimple` and
`glSupercuspidalRestriction_of_compactModCenter`.

### Published steps toward open components

- Compact-support acyclicity of the smooth Godement terms
  (`SmoothGodement.SmoothGodementCompactAcyclicStatement`). The [`Langlands.Cohomology.CompactSoft.Statement`](../../Langlands/Cohomology/CompactSoft/Statement.md)
  states three propositions about the `c`-soft sheaves
  (`Langlands.Sheaf.CompactSoft.IsCSoft`). Two are proved: the `Langlands.Cohomology.cSoftShortExact` proves `CSoftShortExactStatement`
  ([`CompactSoft.ShortExactProof`](../../Langlands/Cohomology/CompactSoft/ShortExactProof.md)),
  and the `Langlands.Cohomology.smoothGodementZeroCSoft` proves
  `SmoothGodementZeroCSoftStatement`
  ([`CompactSoft.SmoothZeroProof`](../../Langlands/Cohomology/CompactSoft/SmoothZeroProof.md)).
  The latter is Step 3 of the truth argument in
  `SmoothGodement/Statement.md`. The third, `CSoftAcyclicityStatement`, is proved
  as well, by `cSoftAcyclicity`
  ([`CompactSoft.AcyclicityProof`](../../Langlands/Cohomology/CompactSoft/AcyclicityProof.md)). As
  the Markdown explains, the remaining comparison of the Godement
  cohomology of the underlying sheaf with `compactCohomology` is not stated
  there.
- `ProPInvariants.ProPInvariantsExactStatement` is a hypothesis of several of
  the modules in `Langlands.Cohomology.DivisibleSystem`, for example
  `DivisibleSystem.ProPInvariants`. None of them proves it.
- Half of `HarrisCMPrimeToInvariants.HarrisCMPrimeToInvariantsStatement`, the
  inclusion of the image of the comparison in the `K₀`-invariants, is the
  Library theorem `cmPrimeToCohomologyComparison_translate_of_mem` (module
  `Langlands.Shimura.PEL.HarrisTaylorCMPrimeToCohomology`),
  under the extra instance hypothesis
  `[Nonempty (cmPrimeToProperty D m hm K₀).FullSubcategory]`. The statement's
  Markdown explains why that hypothesis can be dropped. Injectivity and the
  reverse inclusion are not proved.
- The quasi-étale global comparison, proved (see the table
  above). The namespace `Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison`
  contains the steps of the proof for a compact Hausdorff base and
  continuous action:
  - [`DegreeZero`](../../Langlands/Cohomology/AnalyticQuasiEtaleGlobalComparison/DegreeZero.md)
    proves `isIso_quasiEtaleGlobalInclusion`. With this isomorphism and exact
    base change,
    [`Reduction`](../../Langlands/Cohomology/AnalyticQuasiEtaleGlobalComparison/Reduction.md)
    derives the comparison from
    [`QuasiEtaleRestrictedInjectivesAcyclicStatement`](../../Langlands/Cohomology/AnalyticQuasiEtaleGlobalComparison/RestrictedInjectivesStatement.md),
    vanishing of the positive
    ordinary cohomology of the restriction of an injective `G`-sheaf.
  - [`CompactCechAcyclic`](../../Langlands/Cohomology/AnalyticQuasiEtaleGlobalComparison/CompactCechAcyclic.md)
    derives this acyclicity from
    positive Hom exactness of the Čech complexes of finite compatible
    covers on the compact lift basis, applied to the identity object.
    [`CompactTupleComparison`](../../Langlands/Cohomology/AnalyticQuasiEtaleGlobalComparison/CompactTupleComparison.md)
    derives that exactness on
    restrictions of injectives by restricting to an open subgroup on
    which the finite cochain and the relevant arrows are equivariant,
    and constructing a primitive there.
  - `analyticQuasiEtaleGlobalComparison_of_tupleCones_liftCompatibilityStatement`
    in the latter module concludes the exact comparison given compact lifted
    tuple cones and the lift-compatibility proposition. Their proofs are
    published: `compactCompatibleTupleCones` in
    [`CompactTupleConeAssembly`](../../Langlands/Cohomology/AnalyticQuasiEtaleGlobalComparison/CompactTupleConeAssembly.md)
    and
    `Langlands.Analytic.SaturatedAtlasPresentation.quasiEtaleLiftCompatibility` in
    [`QuasiEtaleLiftCompatibilityProof`](../../Langlands/Geometry/Analytic/QuasiEtaleLiftCompatibilityProof.md).
    The statement still takes
    `Small G` and `HasFiniteEquivariantRefinements` as instances. For the
    latter, the [`AnalyticQuasiEtaleRefinements`](../../Langlands/Sheaf/Equivariant/AnalyticQuasiEtaleRefinements.md)
    reduces it to (A) finite compact refinements, (B) existence of compact
    lifts and (C) compatibility of the lifts. (A) for Hausdorff bases is
    the unproved
    [`QuasiEtaleCompactRefinementsStatement`](../../Langlands/Geometry/Analytic/QuasiEtaleCompactRefinementsStatement.md).
    For (B), apply
    `hasCompactQuasiEtaleLifts_of_actionLiftStatement` to `quasiEtaleActionLift`
    ([`QuasiEtaleActionLiftProof`](../../Langlands/Geometry/Analytic/QuasiEtaleActionLiftProof.md)).
    For (C), apply
    `hasCompatibleCompactQuasiEtaleLifts_of_compatibilityStatement`
    ([`AnalyticFreeRepresentable`](../../Langlands/Sheaf/Equivariant/AnalyticFreeRepresentable.md))
    to `quasiEtaleLiftCompatibility`. Both applications take Hausdorffness
    of the base and continuity of the action.
  - Related helpers: [`AnalyticCommonSubgroupRefinements`](../../Langlands/Sheaf/Equivariant/AnalyticCommonSubgroupRefinements.md)
    packages plain covering arrows
    over one open subgroup, assuming the finite refinement instance.
    In `Langlands.Cohomology.SiteCech`,
    [`FreeNerve`](../../Langlands/Cohomology/SiteCech/FreeNerve.md)
    constructs the free augmented
    nerve as a complex of module sheaves,
    [`CoverExactnessStatement`](../../Langlands/Cohomology/SiteCech/CoverExactnessStatement.md)
    states general cover exactness
    without proof, and
    [`SplitContraction`](../../Langlands/Cohomology/SiteCech/SplitContraction.md)
    gives the contraction for split
    arrows. The route through compact compatible covers above does not
    assume that general exactness statement.
  - the final assembly is
    `Langlands/Cohomology/AnalyticQuasiEtaleGlobalComparison/Proof.lean`,
    which first appeared at Library commit `03296177`.
- The étale comparisons
  `AnalyticEtaleGlobalComparison.AnalyticEtaleGlobalComparisonStatement`
  and
  `AnalyticEtaleCompactComparison.AnalyticEtaleCompactComparisonStatement`.
  The reductions to degree zero and acyclicity were already
  in the Library at `58ad0f79`; the following also records geometric
  inputs checked at `d6b462be` and, where stated, at `b47a2385`. Neither
  comparison is proved in the Library (the compact one has a conditional proof).
  The declarations of the modules named below by their last component are
  in namespace `Langlands.Sheaf.Equivariant.Analytic`, and those modules in
  `Langlands.Sheaf.Equivariant`; the other declarations are in the
  namespaces given with them.
  - Two conditional reductions specialize the base-change
    criterion `Langlands.Cohomology.ExactBaseChange.isIso_baseChangeNatTrans_of_injective_acyclic`
    (module `Langlands.Cohomology.ExactBaseChange.InjectiveAcyclic`).
    `isIso_etaleCompactComparison_of_injective_acyclic`
    ([`AnalyticEtaleCompactDerivedComparison`](../../Langlands/Sheaf/Equivariant/AnalyticEtaleCompactDerivedComparison.md))
    proves that `etaleCompactComparison` is an isomorphism
    in every degree if the inclusion `etaleCompactInclusion` is an
    isomorphism and `H^{r+1}_c(X, b^*I) = 0` for every injective étale
    `G`-sheaf `I` and every `r`. The `isIso_etaleComparison_of_injective_acyclic`
    ([`AnalyticEtaleGlobalReduction`](../../Langlands/Sheaf/Equivariant/AnalyticEtaleGlobalReduction.md))
    proves the same for `etaleComparison` if `etaleGlobalInclusion` is an
    isomorphism and `H^{r+1}(X, b^*I) = 0` for every such `I` and `r`.
  - `isIso_etaleGlobalInclusion_of_finiteBaseSubcovers`
    ([`AnalyticEtaleFiniteGlobalSections`](../../Langlands/Sheaf/Equivariant/AnalyticEtaleFiniteGlobalSections.md))
    proves that `etaleGlobalInclusion` is an isomorphism if
    every covering sieve of the twisted étale site at its base contains a
    finite covering family (`HasFiniteBaseSubcovers`). The `Langlands.Analytic.SaturatedAtlasPresentation.exists_finite_twistedEtale_base_subcover`
    ([`Langlands.Geometry.Analytic.EtaleFiniteSubcovers`](../../Langlands/Geometry/Analytic/EtaleFiniteSubcovers.md))
    gives such finite families for compact Hausdorff `X`
    (`IsCompactSpace X`), assuming that the structure maps of étale objects
    are open and that covering sieves of the étale site are jointly
    surjective on underlying points. Openness is now supplied by `etaleOpenMap`
    ([`Langlands.Geometry.Analytic.EtaleOpenMap.Proof`](../../Langlands/Geometry/Analytic/EtaleOpenMap/Proof.md);
    Berkovich 1993 Prop. 3.2.7).
    Joint surjectivity is stated as `EtaleCoveringPointsStatement`
    ([`Langlands.Geometry.Analytic.EtaleCoveringPoints.Statement`](../../Langlands/Geometry/Analytic/EtaleCoveringPoints/Statement.md)).
    These declarations are in `Langlands.Analytic.SaturatedAtlasPresentation`.
    `EtalePointwiseLiftingStatement`, in
    the same namespace
    ([`Langlands.Geometry.Analytic.EtalePointwiseLifting.Statement`](../../Langlands/Geometry/Analytic/EtalePointwiseLifting/Statement.md)),
    asks for common lifts of points with equal images along cospans of
    étale objects. It is proved
    by `etalePointwiseLifting`
    ([`EtalePointwiseLifting.Proof`](../../Langlands/Geometry/Analytic/EtalePointwiseLifting/Proof.md),
    first appeared at `03296177`). The theorem
    `jointlySurjective_of_mem_etaleTopology_of_pointwiseLifting` of the
    statement module takes exactly that proposition and returns the
    joint-surjectivity premise `hpoints` of
    `exists_finite_twistedEtale_base_subcover`. So both
    geometric premises of this degree-zero route for compact Hausdorff `X`
    follow from Library theorems. `EtaleCoveringPointsStatement` also has a
    direct proof, `etaleCoveringPoints`
    (`Langlands/Geometry/Analytic/EtaleCoveringPoints/Proof.lean`), and
    `isIso_etaleGlobalInclusion_of_compactSpace` (namespace
    `Langlands.Cohomology.AnalyticEtaleGlobalComparison`, file
    `Langlands/Cohomology/AnalyticEtaleGlobalComparison/DegreeZero.lean`)
    assembles it with `etaleOpenMap` into the isomorphism
    `etaleGlobalInclusion` for compact `X`; the same module proves the
    comparison in degree zero (`isIso_etaleComparison_zero_of_compactSpace`).
    The remaining obligation for the
    étale comparison is the higher acyclicity `H^{r+1}(X, b^*I) = 0` for
    injective étale `G`-sheaves `I`, and the comparison itself is not
    proved in the Library. Another conditional route to joint surjectivity is
    `coveringPoints_of_commonPointFields`
    ([`CommonPointField.CoveringPoints`](../../Langlands/Geometry/Analytic/CommonPointField/CoveringPoints.md)),
    from a common point field and the geometric-point statement.
  - For the compact comparison, `compactComparison_of_compactAcyclic` in
    [`GeometryReduction`](../../Langlands/Cohomology/AnalyticEtaleCompactComparison/GeometryReduction.md)
    applies the conditional
    comparison of
    [`Reduction`](../../Langlands/Cohomology/AnalyticEtaleCompactComparison/Reduction.md)
    using the published proofs
    `etaleOpenMap` and `etaleOpenDomainStatement`
    ([`EtaleOpenDomains.Proof`](../../Langlands/Geometry/Analytic/EtaleOpenDomains/Proof.md)). It retains positive
    compact-support acyclicity of the ordinary restrictions of injective
    étale `G`-sheaves as its premise; it does not prove the global degree-zero
    isomorphism. In the same area, the [`AnalyticEtaleSupportAction`](../../Langlands/Sheaf/Equivariant/AnalyticEtaleSupportAction.md)
    relates underlying supports of
    translated sections to the geometric action and gives an equality
    criterion using germs on a set containing the supports, assuming
    surjectivity of `pointProjection` for the equality criterion. This is
    an étale support helper, not an input of the quasi-étale comparison.
  - The acyclicity premises are stated, unproved, in
    [`Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic.Statement`](../../Langlands/Cohomology/AnalyticEtaleRestrictedInjectiveAcyclic/Statement.md)
    (namespace `Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic`):
    `AnalyticEtaleRestrictedInjectiveCompactAcyclicStatement`
    asserts `H^{q+1}_c(X, b^*I) = 0` for every injective étale `G`-sheaf
    `I`, for Hausdorff `|X|` with surjective `pointProjection L X` and a
    continuous action; `AnalyticEtaleRestrictedInjectiveGlobalAcyclicStatement`
    asserts `H^{q+1}(X, b^*I) = 0` under the same hypotheses with `|X|`
    also compact; `AnalyticEtaleRestrictedInjectiveAcyclicStatement` is
    their conjunction.
    [`AnalyticEtaleGodement`](../../Langlands/Sheaf/Equivariant/AnalyticEtaleGodement.md)
    builds the degree-zero Godement term of an étale
    `G`-sheaf with its coaugmentation, proves the coaugmentation monic if
    the stalk functors of the points `etalePoints L h` are jointly faithful,
    and, for injective `I`, reduces the vanishing for `b^*I` to that for
    `b^*` of the Godement term of `I`, since `I` is a retract of that term.
    [`AnalyticEtaleCompactGlobal`](../../Langlands/Sheaf/Equivariant/AnalyticEtaleCompactGlobal.md)
    identifies compactly supported and ordinary étale
    cohomology when `|X|` is compact and `pointProjection L X` is surjective
    (`etaleCompactCohomologyIsoOfCompactSpace`). With the point axioms and
    this surjectivity, `globalAcyclic_of_compactAcyclic` in the compact
    `Reduction` module transfers compact-support acyclicity to the ordinary
    one on compact bases. This does not settle the general global comparison
    `AnalyticEtaleGlobalComparisonStatement`, which does not assume a point field or point axioms.

## Retained source gaps and scope decisions

- Berkovich's manuscript is unfinished (1995–1996). Its étale Corollary
  1.5.2(i) spectral sequence `H^p(G, H^q_c) ⇒ H^{p+q}_c` fails in general
  for noncompact `G`: take `G = ℤ` acting by translation on a discrete
  `ℤ`-indexed union of analytic points, with constant nonzero coefficients
  permuted by `G`. In degree one, the regular-representation group
  cohomology is nonzero but the derived compactly supported invariant
  sections vanish. See the paper argument in
  [EquivariantComposite/Statement.md](../../Langlands/Cohomology/EquivariantComposite/Statement.md#truth-argument).
  This concerns the spectral sequence, not the preceding compact-support
  comparison. Ordinary-topological analogues of its special consequences are stated for
  finite groups (`Cohomology/OperatorSpace/Statement.md`); the analytic
  étale versions remain unstated. The composite-functor
  identification from which the spectral sequence follows,
  `H^n_c(X; G, F) ≅ Hom_{D(SmoothRep R G)}(R, RΓ_c(X, F)[n])`, is stated for
  compact topological groups on ordinary topological spaces
  (`CompactGroupCompactCompositeStatement`), and the `compactGroupCompactCompositeStatement_proof` proves it. The statement's
  Markdown shows that it fails for `G = ℤ` acting on `X = ℤ` by translation,
  with constant coefficients, and gives the truth argument for compact `G`.
  With `HyperextHalfBoundedConvergenceStatements` and
  `CovariantSecondPageStatement` it gives the spectral sequence in derived
  form for compact `G` on ordinary topological spaces (Application section of
  `Cohomology/HyperextConvergence/HalfBoundedStatement.md`). These two are
  proved by the `hyperextHalfBoundedConvergenceStatements_proof`
  and the `covariantSecondPageStatement_proof`, so every statement
  that the Application section combines is proved. The same holds for
  Tohoku's spectral sequence, which uses instead
  `EquivariantGlobalCompositeStatement`, proved by
  `equivariantGlobalComposite`. No Library declaration states either
  combined spectral sequence; the Application section derives them in
  prose.
- Corollary 1.5.2(i) is only about étale sheaves. The Library constructs
  `quasiEtaleCompactComparison : H^q_c(X{G}, F) → H^q_c(X, b^*F)`
  (`Sheaf/Equivariant/AnalyticQuasiEtaleComparison.md`) as an analogous map
  with supports tested at `L`-valued points. There is a paper degree-zero
  obstruction in the manuscript-style quasi-étale setting if one tests
  support only at such rank-one points: a sheaf can be concentrated at
  points of higher rank. The argument below uses that covering rule;
  it does not establish equality of that rule with the Library's generated
  `quasiEtaleTopology`, or a formal counterexample on that specific topology. Let `D` be the closed unit disc over
  `K` (for instance `K = ℚ_p`), `ζ` its Gauss point, and `η` the point of rank two of the adic disc
  that specializes `ζ` towards the residue class of `0`, so that
  `|z(η)| < 1`. Let `G = ℤ_p` act on
  `X = ⊔_{n ≥ 0} ⊔_{i ∈ ℤ/p^{n+1}} D_{n,i}`, a disjoint union of copies of
  `D`, by permuting the copies of the `n`-th block through
  `ℤ_p → ℤ/p^{n+1}`. Let `F` be the sheaf whose sections over a
  quasi-étale `U → X` are the functions, with values in a nonzero module
  `M`, on the points of the adic space of `U` lying over the points
  `η_{n,i}`, with `G` permuting the copies. It is a quasi-étale
  `G`-sheaf: a compact `U` meets finitely many copies, so open subgroups
  act on `F(U)` with open stabilizers. Let `f ∈ F(X)` be the section equal
  to `m ≠ 0` at `η_{n,0}` for every `n` and zero elsewhere. Every
  `L`-valued point of `X` lies over a point `y` of some copy `D_{n,i}`.
  Some affinoid domain of `D_{n,i}` containing `y` misses `η_{n,i}`: the
  domain `{|z| = 1}` if `y = ζ`, and otherwise an affinoid neighborhood
  of `y` not containing `ζ`, since the adic space of a domain containing
  `η` contains its generalization `ζ`. So every germ of `f` at an
  `L`-valued point vanishes, the support of `f` is empty, and `f` lies in
  `Γ_c(X, b^*F)`. The stabilizer of `f` is `⋂_n p^{n+1} ℤ_p = 0`, which is
  not open, so `f` is not in `Γ_{c,X{G}}(F)`. In degree 0 the comparison
  is, through the identification of `H^0` with sections, the inclusion
  `Γ_{c,X{G}}(F) → Γ_c(X, b^*F)` (Markdown of `AnalyticQuasiEtaleComparison`),
  and it is not surjective. This does not contradict Berkovich's
  statement for étale sheaves. Every étale neighborhood of `ζ_{n,0}` has
  points over its specialization `η_{n,0}`, so on the étale site the
  support of `f` contains the infinite closed discrete set
  `{ζ_{n,0} : n ≥ 0}` and is not compact. For quasi-étale sheaves Berkovich
  asserts the comparison for ordinary cohomology on compact `X`: Theorem
  1.6.1(ii), printed p.13, gives `H^q(X{G}, F) ⥲ H^q(X, b^*F)` for every
  quasi-étale or étale abelian sheaf `F` on `X(G)`. Both cases are stated
  on the Library's model, with sheaves of `R`-modules, as
  `AnalyticQuasiEtaleGlobalComparisonStatement` and
  `AnalyticEtaleGlobalComparisonStatement` (see
  [Published modules](#published-modules)). The quasi-étale
  one is proved by the `analyticQuasiEtaleGlobalComparison`, on the
  Library's generated `quasiEtaleTopology`; the étale one is not proved
  in the Library. For étale
  sheaves, the comparison of Corollary 1.5.2(i) is stated as
  `AnalyticEtaleCompactComparisonStatement`, with supports in the
  `L`-valued points and the hypothesis that every point of `X` underlies an
  `L`-valued point; it too is not proved in the Library (it has a conditional proof). The group
  `G = ℤ_p` of the example is compact, so compactness of
  `G` alone does not make the compactly supported quasi-étale comparison
  with these supports an isomorphism. The space `X` of the example is not
  compact, since it has infinitely many components. Whether that comparison
  is an isomorphism when `X` is compact has not been checked.
- Harris 1999 Fact 4 also asserts that each `F(T_m)` is free over
  `ℤ/ℓ^m ℤ`. Only its exactness part follows from the stated exactness; the
  freeness is not stated.
- SGA 4 XVII p.327 misprints an index (`Z^(n+1)` for `Z^(n-1)`); see
  `Sheaf/Godement/ExactnessStatement.md`.
- Harris 1997 is used together with the corrections in Harris 1998,
  pp.180–182. The false printed line on Harris 1997 p.103 is not formalized.
- Harris 1997 (Theorem 2, printed p.100, and the sketch beginning on
  p.102) cites Taylor's unpublished letter to Clozel of December 1991 for the
  decomposition of the Galois representation into `m` copies of one
  `n`-dimensional representation. The letter itself is not available; only
  Harris's sketch is. This gap is also recorded in the `TaylorMultiplicityRemovalStatement` row of
  [galois-family-coverage](galois-family-coverage.md).
- Only the split supercuspidal place is treated, as in Harris 1999. No
  nonsplit generalization is asserted, and the banality assumptions of
  Harris 1999 §6 are not added.

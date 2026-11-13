# Harris–Berkovich cohomological framework: declaration coverage

This note maps the cohomological input to Harris's weak automorphic
induction, as used by Henniart, to Library declarations. It covers the task
"Formalize the Harris and Berkovich cohomological theorem-statement
framework" (task `b91b0934`, Worker 3; continued by Worker 16 since the
carry-over of 2026-11-08). It also lists the parts that are not yet stated
and who owns their prerequisites. It is a map, not a theorem.
Every declaration below is a `Prop`-valued theorem-statement definition, or
an auxiliary construction used to state one. Several components are proved
by published Lean theorems of other workers: five of them in the proof tasks
T1–T5 that this task published, and all five of Worker 16's statements (the
convergence, second-page and composite-functor statements) in proof tasks
that Worker 16 published (see
[Proved statements](#proved-statements)). The others are not.

Each module's paired Markdown gives its exact hypotheses, sources with
locators, and checks. The originals of the Henniart audit, among them Harris
1998, Harris 1999 and Berkovich's manuscript, are described in
[Registered originals and reading record](sources.md). The other sources
named below, such as SGA 4 and Harris–Taylor 2001, are identified only in
the Markdown of the modules that cite them. The source analysis of Harris
1999 is in
[Harris 1999 and the deferred general-coefficient argument](harris-1999.md).

Versions: Worker 3 wrote this note at Library commit
`ddb0a9c0d562246b405e8f1149220107e7407d1d` of the previous instance, with
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Worker 16 updated it and
checked its module paths, declaration names and links against
Library commit `dbd6b52814f3ecfa30bdd5f8785d2e17e89e85dc`, with environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`. Both environments are Lean 4.34.0
with Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. The three statement
modules added by Worker 16 are `HyperextConvergence.Statement` (candidate
`2e918203-e5dd-4b14-a5b4-d04f45b9c43e`, published at Library
`e449cde988d4e97ab280b8d4d11262887ccc26e0`),
`EquivariantComposite.Statement` (candidate
`ac376ac7-77cd-4b59-8812-37dbf5c33dc0`, published at Library
`d39b5aee822fe2ad1aadf07861ebd9a4c2df62a8`) and
`HyperextConvergence.HalfBoundedStatement` (candidate
`d7d89bbf-6166-49d6-bf97-69e39275700d`, published at Library
`e748734106ab2ee9de1cab1eb18a60e59593aac0`). The descriptions of other
workers' modules added after `ddb0a9c0` are limited to those that the new
statements use or that bear directly on Harris's spectral sequences. On
2026-11-13 Worker 16 revised, against Library commit
`b128d289028bf75629e9e364ecf151c484b27a85` with environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, the same Mathlib):
the rows of
[Not yet stated](#not-yet-stated-and-the-prerequisites-they-wait-for) on
the analytic equivariant sheaves, Harris's spectral sequences, the
Jacquet–Langlands transfer, `ν̄(π)` and `σ(π_v)`; the
[Proved statements](#proved-statements) section (five new table rows, the
last one-line consequence, and the list of open components); the opening
paragraph's count of proved components; the paragraph on the DAG nodes of
the convergence and composite-functor statements; and the first two
entries of
[Retained source gaps and scope decisions](#retained-source-gaps-and-scope-decisions),
of which the second is new. A later revision of the same day, against
Library commit `4b619cdd61c537ff5ee2587fda415e0adb66e5ef` with the same
environment, adds the `ℓ`-adic and `λ`-adic modules and Task 5484 to the
row on unitary Shimura cohomology, adds Harris 1999 (5.1)–(5.3), Theorem
5.7(iii), Lemma 5.8 and Corollary 5.10 to the split-supercuspidal row, adds
Task 5556 to the `σ(π_v)` row, cites Task 34's coverage note in the row
on compatible Galois families, and records DAG revision 81 in the paragraph
on the DAG nodes. Its facts are as of `4b619cdd`. Library commit
`cfedefb680f317b0ea5d351023e1c9dd886b2547`, published before this revision
was resubmitted, adds among others Worker 21's `G`-space structure on `Ω`
and on Harris's domains `U(f)` (`Langlands.Geometry.Analytic.DrinfeldFacetGSpaces`)
and Worker 26's specialization of the quasi-étale constructions of Harris
§2 to `U(f)` (`Langlands.Cohomology.DivisibleSystem.DrinfeldFacet`); this
revision does not survey that commit or later ones.

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
| [`Langlands.Cohomology.EquivariantGodement.Statement`](../../Langlands/Cohomology/EquivariantGodement/Statement.md) | `EquivariantGodementStatements` (3 components), with `EquivariantGodement.augmentationMap` | For a discrete group acting by homeomorphisms on a topological space, Worker 61's equivariant Godement construction: the degree-zero functor is exact; the complex has the ordinary Godement complex as underlying complex, compatibly with the augmentations; and it computes the derived functors of global sections and of compactly supported sections, as representations of the group. |
| [`Langlands.Cohomology.HyperextDegeneration.Statement`](../../Langlands/Cohomology/HyperextDegeneration/Statement.md) | `HyperextDegenerationStatement`, with `HyperextDegeneration.edgeMap` | In an abelian category: if `K` in the derived category has bounded-above cohomology and `Ext^i(H^k K, W)` vanishes for all `i > 0` and all `k`, then the edge map `Hom(K, W[n]) → Hom(H^{-n} K, W)` is bijective for every `n`. |
| [`Langlands.Cohomology.SupercuspidalExt.Statement`](../../Langlands/Cohomology/SupercuspidalExt/Statement.md) | `SupercuspidalExt.SupercuspidalExtStatements` (3 components), with `SupercuspidalExt.restriction`, `SupercuspidalExt.compactInduction` and `SupercuspidalExt.HasCompactCoefficients` | With Worker 13's smooth `Ext`: `Ext` reciprocity for compact induction from an open subgroup; an irreducible smooth complex representation with compactly supported matrix coefficients is injective and projective; and higher `Ext` from a compactly induced representation into a representation whose restriction to the open subgroup is a finite sum of such representations vanish (Harris 1997 p.96; Harris 1999 p.312; Bernstein–Zelevinsky 2.29, 2.44, 3.26). |
| [`Langlands.Cohomology.SupercuspidalExtCharZero.Statement`](../../Langlands/Cohomology/SupercuspidalExtCharZero/Statement.md) | `SupercuspidalExtCharZero.SupercuspidalExtCharZeroStatements` (3 components), with `SupercuspidalExtCharZero.HasCompactCoefficients` | The same three statements over an arbitrary field `k` of characteristic zero: `Ext` reciprocity taken over `k`, injectivity and projectivity of irreducible representations with compactly supported matrix coefficients, and the vanishing of higher `Ext`. The group is locally profinite, σ-compact and unimodular. At `k = ℂ`, for a group in `Type`, the conjunction is the published complex one (`supercuspidalExtStatements_of_charZero`). Sources: Vignéras 1996 I.7 and II.3.9; Harris 1999 (4.10.1) and p.312. |
| [`Langlands.Cohomology.SmoothCompactCohomology.Statement`](../../Langlands/Cohomology/SmoothCompactCohomology/Statement.md) | `SmoothCompactCohomology.SmoothCompactCohomologyStatements` (2 components) | A topological group acts on a space by homeomorphisms. For a smooth equivariant module sheaf, in the sense of Worker 13's `IsSmoothSheaf`, the compactly supported global sections form a smooth representation; this first component is proved (see [Proved statements](#proved-statements)). On a locally compact Hausdorff space, compactly supported Godement cohomology is smooth in every degree. This is the ordinary-topological analogue of the smoothness in Berkovich Cor. 1.5.2(i) and of Harris 1999 p.305. |
| [`Langlands.Cohomology.SmoothCompactComparison.Statement`](../../Langlands/Cohomology/SmoothCompactComparison/Statement.md) | `SmoothCompactComparison.SmoothCompactComparisonStatements` (2 components) | On a locally compact Hausdorff space with Worker 13's `HasStableNeighbourhoods`, injective smooth sheaves have no higher compactly supported Godement cohomology. Moreover, in every degree the derived compact sections of smooth sheaves (`SmoothSheafCohomology.compactDerived`), as representations, are naturally isomorphic to compactly supported Godement cohomology, and the isomorphism in degree zero is the canonical one. Compatibility with connecting maps is not stated. Analogue of the isomorphisms `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)` of Berkovich Cor. 1.5.2(i). |
| [`Langlands.Cohomology.SmoothGodement.Statement`](../../Langlands/Cohomology/SmoothGodement/Statement.md) | `SmoothGodement.SmoothGodementStatements` (4 components) | Worker 61's smooth Godement construction under `HasStableNeighbourhoods`: the degree-zero functor `Godement.smoothZeroFunctor` and every term functor of the complex are additive and exact. On a locally compact Hausdorff space every term of `Godement.smoothComplex F` has no higher compactly supported Godement cohomology and is acyclic for `SmoothSheafCohomology.compactDerived`. Sources: Harris 1999 p.304, Fact 3 and the compact-support acyclicity of `F(T)`; Berkovich §1.5 (ii) and Prop. 1.5.1. |
| [`Langlands.Cohomology.SmoothGodementComparison.Statement`](../../Langlands/Cohomology/SmoothGodementComparison/Statement.md) | `SmoothGodementComparison.SmoothGodementComparisonStatements` (3 components), with `SmoothGodementComparison.comparisonMap` | Under Worker 13's `HasStableNeighbourhoods G X`, which every declaration of the module assumes: for a smooth sheaf `F`, an injective resolution `I` of `F` and a chain map from `Godement.smoothComplex F` to `I` compatible with the augmentations, `comparisonMap` goes from Worker 61's `SmoothGodementCohomology.smoothGodementCompactCohomology` to `SmoothSheafCohomology.compactDerived`. In degree zero it is the composite of the canonical identifications with compact sections; this component assumes no Hausdorff or local-compactness hypothesis. On a locally compact Hausdorff space every comparison map is an isomorphism, and the comparison maps are the components of natural isomorphisms. Sources: Harris 1999 Lemma 2.2 and (2.3), pp.304–305; the proof of Berkovich Cor. 1.5.2(i), p.12. |
| [`Langlands.Cohomology.SupercuspidalExtSemisimple.Statement`](../../Langlands/Cohomology/SupercuspidalExtSemisimple/Statement.md) | `SupercuspidalExtSemisimple.SupercuspidalExtSemisimpleStatements` (3 components), with `SupercuspidalExtSemisimple.IsIrreducible` and `SupercuspidalExtSemisimple.HasCompactCoefficients` | The `SupercuspidalExtCharZero` statements over a commutative semisimple `ℚ`-algebra `A`, such as Harris's `L_ℓ = L ⊗_ℚ ℚ_ℓ`. Irreducibility is simplicity of the subrepresentation lattice; coefficients are taken against `A`-linear dual vectors. At a field of characteristic zero the conjunction is the published one (`supercuspidalExtCharZeroStatements_of_semisimple`). Sources: Harris 1999 p.306, Prop. 4.10 p.311, p.312. |
| [`Langlands.Cohomology.SupercuspidalRestriction.Statement`](../../Langlands/Cohomology/SupercuspidalRestriction/Statement.md) | `SupercuspidalRestriction.CompactModCenterRestrictionStatement`; `SupercuspidalRestriction.GLSupercuspidalRestrictionStatements` (3 components), with `SupercuspidalRestriction.unitDeterminantSubgroup` | The hypothesis of the vanishing statements. In general: for an open normal subgroup `H` with `H ∩ Z(G)` compact and `Z(G) H` of finite index, an irreducible representation with coefficients compact modulo the center restricts to `H` as a finite sum of irreducible representations with compactly supported coefficients. For `GL_n(F)` and `G° = {g | det g ∈ O_F^×}`: the properties of `G°` (BZ 3.20), Harish-Chandra's theorem in the direction supercuspidal ⇒ compact modulo the center (BZ 3.21), and the finite decomposition of the restriction (BZ 3.21, 3.26). `glSupercuspidalRestriction_of_compactModCenter` proves the last from the others, given total disconnectedness and σ-compactness of `GL_n(F)`. Source of the use: Harris 1997 p.96 (`GJ^0`). |
| [`Langlands.Cohomology.EtaleGaloisSmooth.Statement`](../../Langlands/Cohomology/EtaleGaloisSmooth/Statement.md) | `EtaleGaloisSmooth.GaloisCohomologySmoothStatement` | For an algebraic extension `L/K` and a quasi-compact quasi-separated `X → Spec K`, Worker 13's action of `L ≃ₐ[K] L` on étale cohomology of `X_L` with constant coefficients is smooth for the Krull topology. Truth argument: SGA 4 VII 5.7–5.8. The Markdown shows that algebraicity and quasi-compactness cannot be dropped. Finite-level input to the continuity of the `λ`-adic representations of Harris 1999 §5. |
| [`Langlands.Cohomology.EtaleGaloisUnramified.Statement`](../../Langlands/Cohomology/EtaleGaloisUnramified/Statement.md) | `EtaleGaloisUnramified.GaloisCohomologyUnramifiedStatement` | For a number field `K`, a morphism of finite type `X → Spec K`, a finite `R`-module `M` and a degree `n`: Worker 13's action of `Gal(K̄/K)` on `H^n(X_K̄, M)` with constant coefficients is unramified (`DecompositionGroupAction.IsUnramifiedAt`: the inertia subgroup of the absolute Galois group of `K_v` acts trivially) at every finite place `v` outside a finite set, which may depend on `M` and `n`. Truth argument: spreading out (Stacks 01ZM), SGA 4½ [Th. finitude] 1.9, SGA 4 IX 2.4 and 2.2, SGA 1 V 8.2. Finite-coefficient input to the almost-everywhere unramified association of Harris 1999 §5; no set of places uniform in the torsion level, so no `λ`-adic statement. |
| [`Langlands.Cohomology.EtaleGaloisGoodReduction.Statement`](../../Langlands/Cohomology/EtaleGaloisGoodReduction/Statement.md) | `EtaleGaloisGoodReduction.GaloisCohomologyGoodReductionStatement` | For a number field `K` and a smooth proper `X → Spec K`: there is one finite set `S` of finite places such that for every finite `R`-module `M`, every degree `n` and every finite place `v ∉ S` at which the order of `M` is a unit, the same Galois action on `H^n(X_K̄, M)` is unramified at `v`. The set `S` does not depend on `M` or `n`, as an `ℓ`-adic limit requires. A test file proves that it implies `GaloisCohomologyUnramifiedStatement` for smooth proper `X`. Truth argument: spreading out to a smooth proper model (Stacks 01ZM, 0C0C, 081F), SGA 4 XVI Cor. 2.2, SGA 1 V 8.2. |
| [`Langlands.Cohomology.HarrisCMCohomology.Statement`](../../Langlands/Cohomology/HarrisCMCohomology/Statement.md) | `HarrisCMCohomology.HarrisCMCohomologyStatements` (2 components: `HarrisCMCohomology.HarrisCMCohomologyFiniteStatement` and `HarrisCMCohomology.HarrisCMGaloisCohomologySmoothStatement`) | For a small CM level `U`, Worker 57's geometric CM scheme `X̄_U = X_U ×_{Spec F} Spec F̄` and the `r`-th stage `B_r` of Worker 57's torsion coefficient system pulled back to `X̄_U`: every `H^d(X̄_U, B_r)` is finite, and Worker 57's action of `F̄ ≃ₐ[F] F̄` on it (`cmHarrisGeometricGaloisCohomologyAction`) is smooth for the Krull topology. All objects take a proof `q` of `CMRepresentabilityStatement` and further premises; `q`, `square`, `existence`, `geometry` and `hRigid` are unproved, and the Markdown lists published proofs of the other thirteen. Truth arguments: SGA 4 IX 2.3–2.4 and XIV Cor. 1.2 (finiteness); SGA 4 VII 5.7–5.8 (smoothness). Analogues, at one level and one torsion stage, of the finiteness used in the proof of Harris 1999 Prop. 4.10 (p.312), and of the continuity of the Galois action that Harris–Taylor 2001 III.2 (p.97) assert and that the `λ`-adic representations of Harris 1999 §5 (p.313) require. |
| [`Langlands.Cohomology.HarrisCMCohomologyUnramified.Statement`](../../Langlands/Cohomology/HarrisCMCohomologyUnramified/Statement.md) | `HarrisCMCohomologyUnramified.HarrisCMCohomologyUnramifiedStatement` | For a small CM level `U` and the same modules `H^d(X̄_U, B_r)`: there is one finite set `S` of finite places of `F` such that for every degree `d`, every torsion stage `r` and every finite place `w ∉ S`, Worker 57's action `cmHarrisGeometricGaloisCohomologyAction` is unramified at `w` (`DecompositionGroupAction.IsUnramifiedAt`). `S` does not depend on `d` or `r`. A test file derives that outside `S` every geometric Frobenius lift acts by one endomorphism. The same premises as `HarrisCMCohomology`. Truth argument: the coefficient covers have monodromy controlled by the `p`-power torsion of the universal abelian scheme (Harris–Taylor III.1, p.91); spreading out `X_U` and that abelian scheme over `O_F[1/N]` (Stacks 01ZM, 0C0C, 081F, 03H0); SGA 4 XV 2.1 and XVI 2.1; SGA 1 V 8.2. Fixed-level, torsion-coefficient input to the almost-everywhere unramifiedness of Harris 1999 §5 (p.313). |
| [`Langlands.Cohomology.HarrisCMLevelGaloisSmooth.Statement`](../../Langlands/Cohomology/HarrisCMLevelGaloisSmooth/Statement.md) | `HarrisCMLevelGaloisSmooth.HarrisCMLevelGaloisSmoothStatement` | For a commutative ring `R`, the Library's `cmSmallLevelGaloisCohomologyFunctor` sends a sheaf `M` of `R`-modules on the small étale site of `Spec F` to the colimit, over all sufficiently small CM levels `U`, of `H^d(X̄_U, p_U^* M)`, where `p_U : X̄_U → Spec F` is the structure map. The statement: for every degree `d`, every `M` and every class of this colimit, some open subgroup of `F̄ ≃ₐ[F] F̄` (Krull topology) fixes the class under the Library's Galois action. There is no finiteness, torsion or characteristic hypothesis on `R`. The objects take `q` and eighteen further premises; `q`, `square`, `existence`, `geometry` and `hRigid` are unproved, and the Markdown lists published proofs of the other fourteen. Truth argument: SGA 4 VII 5.1 and Cor. 5.8 at each level. Analogue, for coefficients pulled back from `Spec F` and discrete modules, of the continuity of the Galois action on `H^i(X, L_ξ) = lim_{→U} H^i(X_U ×_F F^ac, L_ξ)` in Harris–Taylor 2001 III.2 (pp.96–97). |
| [`Langlands.Cohomology.HarrisCMLevelInvariants.Statement`](../../Langlands/Cohomology/HarrisCMLevelInvariants/Statement.md) | `HarrisCMLevelInvariants.HarrisCMLevelInvariantsStatement` | For a commutative ring `R`, a level-trivial coefficient diagram `coeff` of étale `R`-module sheaves on the geometric CM tower `U ↦ X̄_U`, and sufficiently small levels `V ≤ U` with `V` normal in `U`, such that the transition of `coeff` along `V ≤ U` is an isomorphism and the index `[U : V]` is a unit of `R`: in every degree `d`, restriction `H^d(X̄_U, coeff_U) → H^d(X̄_V, coeff_V)` is injective, and its image is the set of classes fixed by the maps of the level arrows `smallCMNormalInverseArrow D U V hVU g : V ⟶ V` (element `g⁻¹`) for all `g ∈ U`. The same premises as `HarrisCMLevelGaloisSmooth`. Truth argument: Worker 57's theorem that `X̄_V → X̄_U` is a finite étale `U/V`-torsor, and the trace of SGA 4 IX 5.1. Analogue of the comparison `H^i(X_U ×_F F^ac, L_ξ) ≅ H^i(X_V ×_F F^ac, L_ξ)^{U/V}` of Harris–Taylor 2001 III.2 (p.96). |
| [`Langlands.Cohomology.HarrisCMColimitInvariants.Statement`](../../Langlands/Cohomology/HarrisCMColimitInvariants/Statement.md) | `HarrisCMColimitInvariants.HarrisCMColimitInvariantsStatement` | For a `ℚ`-algebra `R` and a level-trivial coefficient diagram on the same tower all of whose transition maps are isomorphisms: at every small level `U` and in every degree `d`, the insertion of `H^d(X̄_U, coeff_U)` into the colimit over all small levels (`RestrictedLevelColimit.ι`) is injective, and its image is the set of classes fixed by `U` under the Library's smooth action of the finite-adelic group (`cmSmallLevelSmoothCohomology`). The same premises. Truth argument: derived from `HarrisCMLevelInvariantsStatement`. This is the step between the comparison of Harris–Taylor 2001 p.96 and the admissibility of `H^i(X, L_ξ)` that they assert on p.97. |
| [`Langlands.Cohomology.HarrisCMPrimeToInvariants.Statement`](../../Langlands/Cohomology/HarrisCMPrimeToInvariants/Statement.md) | `HarrisCMPrimeToInvariants.HarrisCMPrimeToInvariantsStatement` | For `m ≠ 0`, a level `K₀` at the places dividing `m`, a `ℚ`-algebra `R` and a level-trivial coefficient diagram on the same tower all of whose transition maps are isomorphisms: in every degree `d`, the Library's comparison `cmPrimeToCohomologyComparison`, from the colimit over the prime-to-`m` levels `K'` of the cohomology at the small levels `e⁻¹ (K₀ × K')` (`e = cmPrimeToSplit D m hm`) to the colimit over all small levels, is injective, and its image is the set of classes fixed by `factorHom e k` for all `k ∈ K₀`. The same premises. Truth argument: derived from `HarrisCMColimitInvariantsStatement`, using open subgroups without torsion at a prime not dividing `m`. It identifies the cohomology with the level at the places dividing `m` fixed, the kind used in Harris 1999 Prop. 4.10 (p.311), with the `K₀`-invariants of the colimit of Harris–Taylor 2001 p.96. |
| [`Langlands.Cohomology.HarrisCMPrimeToGaloisSmooth.Statement`](../../Langlands/Cohomology/HarrisCMPrimeToGaloisSmooth/Statement.md) | `HarrisCMPrimeToGaloisSmooth.HarrisCMPrimeToGaloisSmoothStatement` | For `m ≠ 0`, a level `K₀` at the places dividing `m` and a commutative ring `R`, the Library's `cmPrimeToGaloisCohomologyFunctor` sends a sheaf `M` of `R`-modules on the small étale site of `Spec F` to the colimit, over the prime-to-`m` levels `K'`, of the cohomology of `M` pulled back to `X̄_{e⁻¹ (K₀ × K')}`. The statement: for every degree `d`, every `M` and every class of this colimit, some open subgroup of `F̄ ≃ₐ[F] F̄` (Krull topology) fixes the class under the Library's Galois action. The same premises; no hypothesis on `R`. Truth argument: at each level `e⁻¹ (K₀ × K')` the Galois operator is that of `HarrisCMLevelGaloisSmoothStatement` (checked in a test file), whose level-wise argument (SGA 4 VII 5.1 and Cor. 5.8) applies. The prime-to-`m` analogue of the Galois continuity in Harris–Taylor 2001 III.2 (pp.96–97), for the tower of Harris 1999 Prop. 4.10 (p.311). |
| [`Langlands.Cohomology.HyperextConvergence.Statement`](../../Langlands/Cohomology/HyperextConvergence/Statement.md) | `HyperextConvergence.HyperextConvergenceStatements` (2 components: `HyperextConvergence.HyperextPageDegenerationStatement` and `HyperextConvergence.HyperextStablePageStatement`) | For a t-structure `t` on a triangulated category `C` and objects `K` and `B` with `K` in `t`-degrees `≥ a` and `≤ b`: on every page `r` with `r ≥ 2` and `r ≥ b - a + 2` of Worker 61's `hyperextSpectralSequence t K B`, every differential vanishes, and the object in position `(p, q)` is isomorphic to the graded piece `gr^p` (`HyperextAbutment.graded t K B (p + q) p`) of the filtration of `Hom(K, B⟦p + q⟧)` by truncations of `K`. Only existence of the isomorphisms is asserted. Source: Cartan–Eilenberg 1956 XVII §2 (4) and §3 Case 1 and (4), pp.368–370, as a derived reformulation; it is the convergence behind the arrows `⇒` of Harris 1999 (4.4.1) and (4.10.1). |
| [`Langlands.Cohomology.EquivariantComposite.Statement`](../../Langlands/Cohomology/EquivariantComposite/Statement.md) | `EquivariantComposite.EquivariantCompositeStatements` (2 components: `EquivariantComposite.EquivariantGlobalCompositeStatement` and `EquivariantComposite.CompactGroupCompactCompositeStatement`), with `EquivariantComposite.trivialSmoothRep` | The derived invariant sections are, naturally in the sheaf, the morphisms in the derived category of representations from the trivial representation `R` in degree `0` to the `n`-th shift of the derived section complex. For ordinary sections (Worker 13's `invariantGlobalDerived` and `globalComplex`), any group acting on a topological space by homeomorphisms and equivariant sheaves of `R`-modules: Tohoku V Thm 5.2.1 with (5.2.2), in composite-functor form. For compact supports (Worker 13's `invariantCompactDerived` and `compactComplex`), a compact topological group with `HasStableNeighbourhoods G X`, smooth sheaves on an ordinary topological space and smooth representations: the ordinary-topological analogue of Berkovich Cor. 1.5.2(i), in composite-functor form (Berkovich's analytic étale site is not used). The isomorphisms are additive and only their existence is asserted. The spectral sequences follow with the next row. Berkovich's manuscript asserts the spectral sequence for every topological group; the Markdown proves that it fails for `G = ℤ` acting on `X = ℤ` by translation, hence the compactness hypothesis. |
| [`Langlands.Cohomology.HyperextConvergence.HalfBoundedStatement`](../../Langlands/Cohomology/HyperextConvergence/HalfBoundedStatement.md) | `HyperextConvergence.HyperextHalfBoundedConvergenceStatements` (2 components: `HyperextConvergence.HyperextHalfBoundedDifferentialStatement` and `HyperextConvergence.HyperextHalfBoundedStablePageStatement`); `HyperextConvergence.CovariantSecondPageStatement` | Convergence in Cartan–Eilenberg's Case 1: for a t-structure `t` on a triangulated category, `K` in `t`-degrees `≤ b` and `B` in `t`-degrees `≥ c`, on page `r` of `hyperextSpectralSequence t K B` with `r ≥ 2`, `r ≥ p - c + 1` and `r ≥ q + b + 2`, the differentials into and out of position `(p, q)` vanish, and the object there is isomorphic to `gr^p` of `Hom(K, B⟦p + q⟧)`. The covariant form, in the opposite of the derived category `D(C)` of an abelian category with `opTStructure` of the standard t-structure, applied to `op K` and `op A` for `A` in degree `0`: page 2 in position `(p, q)` is additively equivalent to `Ext^p(A, H^q(K))` for `p ≥ 0` and is zero for `p < 0`, and the abutment in degree `n` to `Hom(A, K⟦n⟧)`. Only existence of the isomorphisms is asserted. The Markdown's Application section combines them with the previous row: Tohoku's `H^p(G, H^q(X, A)) ⇒ H^n(X; G, A)` (Thm 5.2.1, (5.2.5), p.200), with `H^p(G, -)` read as `Ext^p` from the trivial representation, and Berkovich's `H^p(G, H^q_c) ⇒ H^{p+q}_c` (Cor. 1.5.2(i)) for compact `G` on ordinary topological spaces. Source: Cartan–Eilenberg 1956 XVII §2 (4) and §3 Case 1, pp.368–370. |

All names in the second column are relative to the namespace
`Langlands.Cohomology`, except `Langlands.CompactCoefficientSplittingStatement`.
In the content column, `Godement.` abbreviates
`Langlands.Sheaf.Equivariant.Godement.`.

The equivariant Godement statements concern Worker 61's ordinary-topological
construction for a discrete group. They are analogues of Berkovich's
resolution, not statements about Berkovich's `ν_*ν^*` on the equivariant
topos, which has additional coinduction factors. The acyclicity that Harris
1999 p.304 displays for Berkovich's resolution is for compactly supported
cohomology, `H_c^q(U(ẽ)_{F̄}, F(T)) = 0` for `q > 0`; the compactly
supported part of the third component is its analogue.

The four smooth modules treat a topological group, not only a discrete one.
Their sheaves are Worker 13's smooth equivariant sheaves: sections are locally
fixed by open subgroups. Worker 61's smooth Godement functor is the ordinary
Godement degree-zero functor of the underlying sheaf, followed by coinduction
and the smooth part. As Worker 61's `Godement/Smooth.md` explains, it is the
counterpart of Berkovich's `ν_*ν^*`: points of `X` replace geometric points,
and the right adjoint of forgetting replaces `ν_*`. Smooth sheaves are
modelled directly on `X`, so Berkovich's `b^*` is implicit. All four modules
remain on topological spaces; Berkovich's étale and quasi-étale sites of
analytic spaces are not used.

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

Two published statements of other workers treat the same items of
Bernstein–Zelevinsky 1976 for product Levi subgroups of `GL_n(F)`. There the
determinant-unit subgroup is taken blockwise and the topology is any
compatible `T : F.TopologicalData`. They are Worker 76's
`Langlands.CuspidalSupport.LeviDeterminantUnitStructureTheorem` (BZ
3.20(a)–(b)) and Worker 180's `Langlands.CuspidalSupport.LeviHarishChandraTheorem`
(BZ 3.21, (1) ⇔ (4): quasicuspidality against compactly supported
coefficients of the restriction to the determinant-unit subgroup).
`SupercuspidalRestriction` instead uses the canonical topology on `GL_n(F)`,
Worker 23's `IsSupercuspidal`, and the direction (1) ⇒ (3), coefficients
compactly supported modulo the center. No Lean statement relates
`unitDeterminantSubgroup` to `determinantUnitSubgroup`, or
`HasCompactSmoothCoefficientsModCenter` to the coefficient condition on the
determinant-unit subgroup. The theorem
`glSupercuspidalRestriction_of_compactModCenter` takes σ-compactness and total
disconnectedness of `GL_n(F)` as instance arguments. σ-compactness for the
canonical topology is Worker 164's theorem
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

## Published constructions of other workers

These are constructions with proofs, not theorem statements of this task.
They are used by the statements above or by some of their proofs, except
the row of `HarrisTaylorCMGeometricNormalActions` and
`HarrisTaylorCMGeometricNormalTorsor`, which is cited only in a truth
argument. The modules that the proofs themselves
import are named in [Proved statements](#proved-statements). The Author
column follows the module Markdown's Author line; "No Author line" marks a
module whose Markdown has none.

| Module | Author | Objects |
| --- | --- | --- |
| [`Langlands.Sheaf.Equivariant.Godement.Complex`](../../Langlands/Sheaf/Equivariant/Godement/Complex.md) | Worker 61 | `Langlands.Sheaf.Equivariant.Godement.complexFunctor`, the equivariant Godement complex built from `zeroFunctor` and `coaugmentation` (`Godement.Zero`) by the iterated-cokernel construction, with its augmentation and the instance `zeroFunctor_additive` |
| [`Langlands.Cohomology.EquivariantDerivedSections`](../../Langlands/Cohomology/EquivariantDerivedSections.md) | Worker 13 | `globalDerived` and `compactDerived`, the right derived functors of global and compactly supported sections on equivariant module sheaves, with values in `Rep R G`; `globalDerivedIso` and `compactDerivedIso` compute them from injective resolutions; `invariantGlobalDerived`, the right derived functors of invariant global sections `F ↦ Γ(X, F)^G`, with values in `ModuleCat R` (used by `EquivariantComposite`) |
| [`Langlands.Cohomology.SmoothExt`](../../Langlands/Cohomology/SmoothExt.md) | Worker 13 | `Langlands.Cohomology.SmoothExt.ext R G V n`, the right derived functors of `Hom(V, -)` on the abelian category `Langlands.SmoothRep R G`, which has enough injectives |
| [`Langlands.Sheaf.Equivariant.SmoothCompactSupport`](../../Langlands/Sheaf/Equivariant/SmoothCompactSupport.md) | Worker 13 | For a topological group, the smooth part of the representation on compactly supported global sections, as a functor to `Langlands.SmoothRep R G`; a degree-zero construction |
| [`Langlands.Sheaf.Equivariant.Godement.Underlying`](../../Langlands/Sheaf/Equivariant/Godement/Underlying.md) | Worker 61 | `underlyingComplexIso` and `underlyingComplexIso_augmentation`: the equivariant Godement complex has the ordinary Godement complex as underlying complex, compatibly with the augmentations |
| [`Langlands.Sheaf.Equivariant.Coinduction`](../../Langlands/Sheaf/Equivariant/Coinduction.md) | Worker 61 | `coinduction`, right adjoint to forgetting equivariance (`coinductionAdjunction`); it preserves injective objects |
| [`Langlands.Sheaf.Equivariant.Godement.Smooth`](../../Langlands/Sheaf/Equivariant/Godement/Smooth.md) | Worker 61 | `smoothForget`, `smoothCoinduction` and their adjunction; the smooth Godement functor `smoothZeroFunctor`, the monic coaugmentation `smoothCoaugmentation`, and the complex `smoothComplexFunctor`, `smoothComplex` |
| [`Langlands.Cohomology.EquivariantGodementCohomology`](../../Langlands/Cohomology/EquivariantGodementCohomology.md) | Worker 13 | `globalCohomology` and `compactCohomology`, the cohomology of the equivariant Godement complex after global and compactly supported sections, as representations, with their degree-zero identifications |
| [`Langlands.Sheaf.Equivariant.Smooth`](../../Langlands/Sheaf/Equivariant/Smooth.md) | Worker 13 | `IsSmoothSheaf` (sections locally fixed by open subgroups), the full subcategory `SmoothTopologicalSheaf R G X` and its inclusion `smoothInclusion` |
| [`Langlands.Sheaf.Equivariant.SmoothPart`](../../Langlands/Sheaf/Equivariant/SmoothPart.md) | Worker 13 | `HasStableNeighbourhoods G X` (small open neighbourhoods stabilized by open subgroups; instances for discrete groups and for non-archimedean groups acting continuously), the smooth part `smoothCoreflector` and `smoothAdjunction` |
| [`Langlands.Sheaf.Equivariant.SmoothAbelian`](../../Langlands/Sheaf/Equivariant/SmoothAbelian.md) | Worker 13 | Smooth sheaves form an abelian category with enough injectives |
| [`Langlands.Sheaf.Equivariant.SmoothSheafCompactSections`](../../Langlands/Sheaf/Equivariant/SmoothSheafCompactSections.md) | Worker 13 | `CompactSections.isSmooth_representation_of_isSmoothSheaf`, which proves `CompactSectionsSmoothStatement`; the left exact functor `smoothSheafCompactSections` to `Langlands.SmoothRep R G` and `smoothSheafCompactSectionsToRepIso` |
| [`Langlands.Cohomology.SmoothSheafCohomology`](../../Langlands/Cohomology/SmoothSheafCohomology.md) | Worker 13 | `compactDerived`, the right derived functors of `smoothSheafCompactSections`, with `compactDerivedZeroIso` and `compactDerivedIso`; the invariant versions `invariantCompactDerived` |
| [`Langlands.Cohomology.EquivariantDerivedComparison`](../../Langlands/Cohomology/EquivariantDerivedComparison.md) | Worker 13 | For a group without topology: `globalDerivedForgetIso` and `compactDerivedForgetIso`, the derived sections of an equivariant sheaf have the derived sections of the underlying sheaf as underlying modules |
| [`Langlands.Cohomology.DerivedPlus`](../../Langlands/Cohomology/DerivedPlus.md), [`Langlands.Cohomology.EquivariantDerivedComplex`](../../Langlands/Cohomology/EquivariantDerivedComplex.md) | Worker 13 | Derived functors into the bounded-below derived category, and the complexes `globalComplex` and `compactComplex` of equivariant sheaves in `DerivedCategory.Plus (Rep R G)` with their cohomology identifications |
| [`Langlands.Cohomology.SmoothSheafDerivedComplex`](../../Langlands/Cohomology/SmoothSheafDerivedComplex.md) | Worker 13 | `SmoothSheafDerivedComplex.compactComplex`, the derived compact section complex of smooth equivariant sheaves in `DerivedCategory.Plus (SmoothRep R G)`, with `compactComplexHomologyIso` (used by `EquivariantComposite`) |
| [`Langlands.Cohomology.HyperextSpectralSequence`](../../Langlands/Cohomology/HyperextSpectralSequence.md), [`Langlands.Cohomology.HyperextAbutmentFiltration`](../../Langlands/Cohomology/HyperextAbutmentFiltration.md) | Worker 61 | `hyperextSpectralSequence t K B`, Mathlib's `E₂`-cohomological spectral sequence of the spectral object obtained by applying `Hom(-, B)` to the truncations of `K` for a t-structure `t`, with `secondPageIso` (page 2 is `Hom(heartPiece t K q, B⟦p + q⟧)`) and `abutmentIso`; `HyperextAbutment.filtration` and `HyperextAbutment.graded`, the filtration of `Hom(K, B⟦n⟧)` by truncations of `K` and its graded pieces (used by `HyperextConvergence`) |
| [`Langlands.Cohomology.SmoothGodementCohomology`](../../Langlands/Cohomology/SmoothGodementCohomology.md) | Worker 61 | `smoothGodementCompactCohomology`, the cohomology of compact sections of `Godement.smoothComplex`, as smooth representations, with `smoothGodementCompactCohomologyZeroIso`; invariant variants `smoothGodementInvariantCompactCohomology` |
| [`Langlands.Geometry.EtaleAutomorphism`](../../Langlands/Geometry/EtaleAutomorphism.md), [`Langlands.Cohomology.TranslationAction`](../../Langlands/Cohomology/TranslationAction.md), [`Langlands.Geometry.EtaleCohomologyAction`](../../Langlands/Geometry/EtaleCohomologyAction.md) | Worker 13 | Translation of étale sheaves by scheme automorphisms, and `EtaleCohomologyAction.cohomologyRep`, the representation of a group acting on a scheme by automorphisms on étale cohomology of an equivariant sheaf |
| [`Langlands.Cohomology.TranslationCoaction`](../../Langlands/Cohomology/TranslationCoaction.md), [`Langlands.Geometry.EtaleConstantCohomology`](../../Langlands/Geometry/EtaleConstantCohomology.md), [`Langlands.Geometry.EtaleGaloisAction`](../../Langlands/Geometry/EtaleGaloisAction.md) | Worker 13 | Actions on derived functors from structure maps into translates; `EtaleCohomologyAction.constantCohomologyRep`, the action on étale cohomology with constant coefficients; `EtaleGaloisAction.galoisCohomologyRep`, the action of `L ≃ₐ[K] L` on étale cohomology of the base change `X ×_{Spec K} Spec L` with constant coefficients |
| [`Langlands.Shimura.PEL.HarrisTaylorCMGeometricCohomology`](../../Langlands/Shimura/PEL/HarrisTaylorCMGeometricCohomology.md), [`Langlands.Shimura.PEL.HarrisTaylorCMGeometricGaloisCohomology`](../../Langlands/Shimura/PEL/HarrisTaylorCMGeometricGaloisCohomology.md) | Worker 57 | In namespace `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`: `cmHarrisGeometricCoefficientCohomologySystem`, the étale cohomology `H^d(X̄_U, B_r)` as a functor of the coefficient stage `r`; `cmHarrisGeometricGaloisCohomologyAction`, the action of `F̄ ≃ₐ[F] F̄` on it, by pullback along the Galois automorphisms of `X̄_U` followed by the canonical coefficient isomorphisms. Both take a proof `q` of `CMRepresentabilityStatement` |
| [`Langlands.Geometry.EtaleDerivedSections`](../../Langlands/Geometry/EtaleDerivedSections.md) | Worker 13 | `EtaleDerivedSections.cohomology X R d`, the right derived functors of global sections on sheaves of `R`-modules on the small étale site of a scheme, computed with injective resolutions; the étale cohomology in all seven `HarrisCM` statement modules |
| [`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelIndex`](../../Langlands/Shimura/PEL/HarrisTaylorCMSmallLevelIndex.md), [`Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoefficients`](../../Langlands/Shimura/PEL/HarrisTaylorCMGeometricCoefficients.md) | Worker 57 | `SmallCMLevel D`, the sufficiently small CM levels with their level arrows, and the preorder `OrderedSmallCMLevel D`; `cmGeometricSchemeTower`, the tower `U ↦ X̄_U` as a functor `SmallCMLevel D ⥤ Scheme`, which takes `q` |
| [`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelCohomology`](../../Langlands/Shimura/PEL/HarrisTaylorCMSmallLevelCohomology.md), [`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelGaloisCoefficients`](../../Langlands/Shimura/PEL/HarrisTaylorCMSmallLevelGaloisCoefficients.md) | No Author line | `cmSmallLevelTowerEtale` (the transition maps of the geometric tower are étale), coefficient diagrams `cmSmallLevelCoefficientDiagram`, level triviality `cmSmallLevelTrivialCoefficients`, the level cohomology `cmSmallLevelCohomology` and its colimit with the smooth finite-adelic action, `cmSmallLevelSmoothCohomology`; `cmSmallLevelGaloisCohomologyFunctor`, the colimit of `H^d(X̄_U, p_U^* M)` with the finite-adelic and Galois actions |
| [`Langlands.Shimura.PEL.HarrisTaylorCMHeckeSchemes`](../../Langlands/Shimura/PEL/HarrisTaylorCMHeckeSchemes.md), [`Langlands.Shimura.PEL.HarrisTaylorCMNormalActions`](../../Langlands/Shimura/PEL/HarrisTaylorCMNormalActions.md) | No Author line | The inclusion arrow `smallCMInclusion D hVU : V ⟶ U` (element `1`) and, for `V` normal in `U` and `g ∈ U`, the arrow `smallCMNormalInverseArrow D U V hVU g : V ⟶ V` (element `g⁻¹`) |
| [`Langlands.Geometry.EtaleCohomologyDiagram`](../../Langlands/Geometry/EtaleCohomologyDiagram.md), [`Langlands.Shimura.RestrictedLevelTowerCohomology`](../../Langlands/Shimura/RestrictedLevelTowerCohomology.md), [`Langlands.Shimura.RestrictedLevelColimit`](../../Langlands/Shimura/RestrictedLevelColimit.md) | No Author line | `CoefficientDiagram`, diagrams of étale sheaves over a tower of schemes; `IsLevelTrivialCoefficients`; colimits over levels satisfying a property, their insertions `RestrictedLevelColimit.ι` and the group actions on them |
| [`Langlands.Shimura.Unitary.OppositePointsSplit`](../../Langlands/Shimura/Unitary/OppositePointsSplit.md), [`Langlands.Shimura.SplitLevelTower`](../../Langlands/Shimura/SplitLevelTower.md), [`Langlands.Shimura.RestrictedSplitLevelTowerCohomology`](../../Langlands/Shimura/RestrictedSplitLevelTowerCohomology.md), [`Langlands.Shimura.PEL.HarrisTaylorCMPrimeToCohomology`](../../Langlands/Shimura/PEL/HarrisTaylorCMPrimeToCohomology.md) | No Author line | `finiteAdelicPointsOpSplit`, the splitting of the opposite finite-adelic points at the places dividing `m`, and its instance `cmPrimeToSplit D m hm` for the rational involution of `D`; the factor embeddings `CompactOpenLevel.factorHom` and `CompactOpenLevel.awayHom`; the property `cmPrimeToProperty D m hm K₀` of the prime-to-`m` levels `K'` for which `e⁻¹ (K₀ × K')` is sufficiently small, the restricted coefficients `cmPrimeToCoefficients`, the colimit cohomology `cmPrimeToColimitCohomology` and the comparison `cmPrimeToCohomologyComparison` to the colimit over all small levels, with `ι_cmPrimeToCohomologyComparison`, `cmPrimeToCohomologyComparison_translate_of_mem` and `cmPrimeToCohomologyIso` (an isomorphism under `IsRestrictedCofinal`) |
| [`Langlands.Shimura.PEL.HarrisTaylorCMPrimeToGaloisCohomology`](../../Langlands/Shimura/PEL/HarrisTaylorCMPrimeToGaloisCohomology.md) | No Author line | `cmPrimeToGaloisCohomologyFunctor`, the prime-to-`m` colimit cohomology of sheaves pulled back from `Spec F`, as a functor to `Action (SmoothRep R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ) (F̄ ≃ₐ[F] F̄)`; the Galois automorphisms `cmPrimeToGaloisAction` (the restriction of `cmSmallLevelGaloisAction` to the levels `e⁻¹ (K₀ × K')`), `cmPrimeToGaloisCohomology_ρ_ι_apply` (the action on the insertion of one level) and `cmPrimeToGaloisCohomologyComparison_apply` (the comparison to the colimit over all small levels commutes with the Galois operators). Its Markdown says that it considers no topology on the Galois group and no continuity of its action |
| [`Langlands.Shimura.PEL.HarrisTaylorCMGeometricNormalActions`](../../Langlands/Shimura/PEL/HarrisTaylorCMGeometricNormalActions.md), [`Langlands.Shimura.PEL.HarrisTaylorCMGeometricNormalTorsor`](../../Langlands/Shimura/PEL/HarrisTaylorCMGeometricNormalTorsor.md) | Worker 57 | The action `cmGeometricNormalQuotientAction` of `U/V` on `X̄_V` by the tower maps of the arrows `smallCMNormalInverseArrow`, and the theorem `cmGeometricNormalEtaleAction_isFiniteGeometricTorsor_of_dominantCriterion` that it is a finite geometric torsor. No `HarrisCM` statement module imports them; the truth argument of `HarrisCMLevelInvariants` cites them |
| [`Langlands.Representation.Classification.Supercuspidal`](../../Langlands/Representation/Classification/Supercuspidal.md) | Worker 23 | `GeneralLinear.IsSupercuspidal`: admissibility and vanishing of the Jacquet coinvariants for all proper conjugate block parabolics of `GL_n(F)` |
| [`Langlands.Representation.Classification.FixedCentralSplittingStatement`](../../Langlands/Representation/Classification/FixedCentralSplittingStatement.md) | Worker 19 | The predicate `HasCompactSmoothCoefficientsModCenter` (the module's splitting proposition is not used) |
| [`Langlands.Group.GL.Padic`](../../Langlands/Group/GL/Padic.md) | Worker 6 | The canonical topology on `GL_n(F)` with its topological group, Hausdorff and local compactness certificates |

The third component of `EquivariantGodementStatements` uses Mathlib's
`rightDerived` directly; by definition these are Worker 13's `globalDerived`
and `compactDerived`. `SmoothCompactCohomology`, `SmoothCompactComparison` and
`SmoothGodement` state their compact-support conclusions with Worker 13's
`EquivariantGodementCohomology.compactCohomology` and
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
| Berkovich §1.5, Cor. 1.5.2(i), compact support on the equivariant site, for a discrete group (§1.4, p.7) | Ordinary-topological analogues, for a group without topology acting on a topological space and equivariant sheaves of modules on its open sets, not on Berkovich's analytic étale site: `EquivariantCompactSectionsDerivedStatement` (analogue of the isomorphisms `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)`); for finite `G`, `FiniteEquivariantCompactAcyclicGroupCohomologyStatement` (when higher compactly supported cohomology vanishes) and `FiniteEquivariantCompactSectionsInvariantsStatement` (when the order of `G` is invertible). Neither these consequences nor the printed spectral sequence is stated on Berkovich's analytic étale site; the ordinary-topological form of the spectral sequence for compact `G` is in the last row of this table. |
| Berkovich Cor. 1.5.2(i), smoothness of the action on `H^q_c(X, b^*F)` and the comparison `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)` for a topological group | `SmoothCompactCohomologyStatements`; `SmoothCompactComparisonStatements` (ordinary-topological analogues) |
| Berkovich §1.5 (ii) and Prop. 1.5.1, exactness of `F ↦ C^m(F)` and softness of `b^*C^m(F)` | `SmoothGodementStatements` (ordinary-topological analogue) |
| Harris 1999 Lemma 2.2 and (2.3), pp.304–305: the resolution of Lemma 2.2 computes `H^q_c`; the Godement step of the proof of Berkovich Cor. 1.5.2(i) | `SmoothGodementComparisonStatements` (ordinary-topological analogue) |
| Harris 1999 p.306 and Prop. 4.10, p.311: `Ext` in smooth `L_ℓ[GJ]`-modules, `L_ℓ = L ⊗_ℚ ℚ_ℓ`; p.312, the higher `Ext` vanish | `SupercuspidalExtSemisimpleStatements` |
| Harris 1997 p.96: `GJ^0` has compact center, so `π_v` restricted to `GJ^0` is still supercuspidal | `CompactModCenterRestrictionStatement` |
| Bernstein–Zelevinsky 1976, 3.20, 3.21 (Harish-Chandra) and 3.26 | `GLSupercuspidalRestrictionStatements` |
| Harris 1999 §5, p.313: `λ`-adic representations of `Gal(F̄/F)` on étale cohomology; SGA 4 VII 5.7–5.8 | `GaloisCohomologySmoothStatement` (constant coefficients) |
| Harris 1999 §5, p.313: `λ`-adic representations "unramified at all but finitely many places"; Theorems 5.7 (ii) and 5.9 (i) (almost all places); SGA 4½ [Th. finitude] 1.9 (truth argument) | `GaloisCohomologyUnramifiedStatement` (finite constant coefficients; the exceptional set may depend on the coefficients) |
| Harris 1999 §5, p.313, as above, for all torsion levels at once; SGA 4 XVI Cor. 2.2, the specialization theorem for proper smooth morphisms (truth argument) | `GaloisCohomologyGoodReductionStatement` (smooth proper schemes; one exceptional set for all finite constant coefficients, apart from the places dividing their order) |
| Harris 1999, proof of Prop. 4.10, p.312: "the right-hand side of the spectral sequence (4.9) is a finite group for all `m`"; SGA 4 XIV Cor. 1.2 | `HarrisCMCohomologyFiniteStatement` (analogue for Worker 57's geometric CM level `X̄_U` and torsion stage `B_r`; conditional on `q`) |
| Harris–Taylor 2001 III.2, p.97: the Galois action on Shimura cohomology with coefficient systems is continuous; Harris 1999 §5, p.313: `λ`-adic representations of `Gal(F̄/F)` on such cohomology; SGA 4 VII 5.7–5.8 | `HarrisCMGaloisCohomologySmoothStatement` (the same analogue, at one level and one torsion stage) |
| Harris 1999 §5, p.313: `λ`-adic representations "unramified at all but finitely many places", on the cohomology of unitary Shimura varieties with coefficient systems; Harris–Taylor 2001 III.1, p.91, monodromy of the level covers; SGA 4 XV 2.1 and XVI 2.1 (truth argument) | `HarrisCMCohomologyUnramifiedStatement` (Worker 57's geometric CM level `X̄_U` and torsion stages `B_r`; one exceptional set for all degrees and stages; conditional on `q`) |
| Harris–Taylor 2001 III.2, p.96: `H^i(X, L_ξ) = lim_{→U} H^i_et(X_U ×_F F^ac, L_ξ)` over sufficiently small levels; p.97: it is "an admissible/continuous `G(A^∞) × Gal(F^ac/F)`-module"; SGA 4 VII 5.1 and Cor. 5.8 (truth argument) | `HarrisCMLevelGaloisSmoothStatement` (the Galois continuity, for the colimit over all small CM levels, with coefficients pulled back from `Spec F` and discrete modules; conditional on `q`) |
| Harris–Taylor 2001 III.2, p.96: "If `V ⊂ U` then … `H^i_et(X_U ×_F F^ac, L_ξ) ≅ H^i_et(X_V ×_F F^ac, L_ξ)^{U/V}`"; SGA 4 IX 5.1, the trace (truth argument only) | `HarrisCMLevelInvariantsStatement` (finite level, `V` normal in `U`, `[U : V]` a unit of `R`); `HarrisCMColimitInvariantsStatement` (the colimit over all small levels, `ℚ`-algebra coefficients); both conditional on `q` |
| Harris 1999 Prop. 4.10, p.311: "as `K(N)^{ℓ,p}` varies the spectral sequences are `GG(A_f^{ℓ,p})`-equivariant", with the level at `ℓ` and `p` fixed (motivation); Harris–Taylor 2001 III.2, p.96, the colimit over levels and the comparison with invariants (provenance) | `HarrisCMPrimeToInvariantsStatement` (the colimit over the levels `e⁻¹ (K₀ × K')` is the `K₀`-invariants of the colimit over all small levels; `ℚ`-algebra coefficients; conditional on `q`) |
| Harris–Taylor 2001 III.2, p.97: the colimit over levels is "an admissible/continuous `G(A^∞) × Gal(F^ac/F)`-module"; Harris 1999 Prop. 4.10, p.311, the level at `ℓ` and `p` fixed (motivation); SGA 4 VII 5.1 and Cor. 5.8 (truth argument) | `HarrisCMPrimeToGaloisSmoothStatement` (the Galois continuity for the colimit over the levels `e⁻¹ (K₀ × K')`, with coefficients pulled back from `Spec F` and discrete modules; conditional on `q`) |
| Harris 1999 Prop. 4.4, (4.4.1), p.309, and Prop. 4.10, (4.10.1), p.311: the spectral sequences `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}, 𝒜) ⇒ H^{i+j}`, as abstract convergence; Cartan–Eilenberg 1956 XVII §2 (4) and §3 Case 1, pp.368–370 | `HyperextConvergenceStatements` (any triangulated category with a t-structure, `K` bounded on both sides; the abutment is `Hom(K, B⟦n⟧)`, not yet identified with Shimura cohomology) |
| Cartan–Eilenberg 1956 XVII §2 (4) and §3 Case 1, pp.368–370: the second hypercohomology spectral sequence of `Hom(C, A)` for `C` bounded above and `A` bounded below | `HyperextHalfBoundedConvergenceStatements` (any triangulated category with a t-structure; a position-dependent page bound); `CovariantSecondPageStatement` (the covariant form `Ext^p(A, H^q(K)) ⇒ Hom(A, K⟦p + q⟧)` in the opposite of a derived category) |
| Tohoku V, Cor. to Prop. 5.1.3 (p.198), (5.2.2) (p.199) and Thm 5.2.1 with (5.2.5) (p.200): `H^p(G, H^q(X, A)) ⇒ H^n(X; G, A)` | `EquivariantGlobalCompositeStatement` (composite-functor form); with `HyperextHalfBoundedConvergenceStatements` and `CovariantSecondPageStatement`, the spectral sequence in derived form (Application section of `HyperextConvergence/HalfBoundedStatement.md`) |
| Berkovich Cor. 1.5.2(i), pp.11–12: `H^p(G, H^q_c(X, b^*F)) ⇒ H^{p+q}_c(X(G), F)` | `CompactGroupCompactCompositeStatement` (ordinary topology, smooth sheaves, compact `G`, composite-functor form with `H^q_c` derived in the smooth category; false for noncompact `G`); with the two statements of the previous row, the spectral sequence in derived form for compact `G` |

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

| Part of the framework | Missing prerequisite | Owner |
| --- | --- | --- |
| Application of `CompactModCenterRestrictionStatement` to Harris's `GJ^0`: that `GJ^0` is normal in `GJ` and that `Z(GJ) GJ^0` has finite index | The group `GJ`, the Drinfeld tower `M_N` and its components (Harris 1997 (A.8)) | Analytic spaces: Task 21 (`18670997`, Worker 21) |
| The geometric input `H^j_c(M_N) ≅ c-Ind_{GJ^0}^{GJ} H^j_c(R_N)` (Harris 1997 (A.8)) | The Drinfeld tower as analytic spaces with their group actions. The Library has only a topological model of the induction step: the balanced quotients `G ×_H X` of the Berkovich spectra of rational domains of a strict affinoid algebra (`Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSpectrum`), with sheaves on their ordinary open subsets, and Worker 13's identifications, in modules of the same directory, with compact induction from `H` to `G`: of the compactly supported locally constant functions with values in a smooth representation `M` of `G` (`compactInductionNatIso` in `InducedRationalCompactInduction`), and of degree-zero compactly supported Godement and derived cohomology (`InducedRationalCohomologyInduction`, which also identifies the zero row `E₂^{p,0}` of the hyperext spectral sequence with `Ext` over `H`, `compactHyperextZeroRowSubgroupAddEquiv`). Higher compact cohomology is not identified with compact induction there, and no Drinfeld space or Harris group is constructed | Analytic spaces: Task 21 (`18670997`, Worker 21) |
| Smoothness of the group action on compactly supported cohomology for Berkovich's analytic étale sheaves (Harris 1997 Lemma 6(i); Berkovich Cor. 1.5.2(i)). The ordinary-topological analogue is stated in `SmoothCompactCohomology` | Berkovich's statement concerns smooth equivariant étale sheaves (Definition 1.4.1, pp.7–8) on a `G`-space, an analytic space with a continuous action of a topological group `G` (§1.1, pp.1–2), and the derived functors of `Γ_{c,X{G}}` among them, with supports in `|X|`. Smoothness is a condition on the sheaf `F`: for every quasi-étale `U → X` with `U` compact, the canonical action of the open subgroup `G_U ⊂ G` on `F(U)` is discrete. Worker 26's published modules in `Langlands.Sheaf.Equivariant` model these objects on Worker 21's analytic sites: `AnalyticGSheaves` (`EtaleGSheaf` and `QuasiEtaleGSheaf`, Berkovich's `T_G(X_ét)` and `T_G(X_qét)`, built on the generic `LocalActionDiscretePart`); `AnalyticCompactSupport` (`Γ_{c,X{G}}` on étale `G`-sheaves, with supports in the `L`-valued points, topologized from `|X|`); `AnalyticQuasiEtaleCompactCohomology` (`H^q_c(X{G}, F)` for quasi-étale `G`-sheaves of modules, `quasiEtaleGSheafCompactCohomology`); `AnalyticQuasiEtaleComparison` (Berkovich's `b^*` as `quasiEtaleGSheafRestriction`, `H^q_c(X, -)` on the quasi-étale site, and the comparison map `quasiEtaleCompactComparison : H^q_c(X{G}, F) → H^q_c(X, b^*F)`, which is not shown to be an isomorphism); and `AnalyticQuasiEtaleRefinements` (the finite-equivariant-refinement hypothesis of these modules reduced to three conditions, which remain hypotheses). There are no derived functors on étale `G`-sheaves. The statement that `quasiEtaleCompactComparison` is an isomorphism is false on this quasi-étale model already in degree 0, for the compact group `G = ℤ_p` acting on a noncompact `X` (see [Retained source gaps and scope decisions](#retained-source-gaps-and-scope-decisions)), so it is not stated. A faithful statement needs the derived functors of `Γ_{c,X{G}}` on étale `G`-sheaves. A quasi-étale variant would need supports that also see the points of the quasi-étale topos missed by the `L`-valued points; such supports are not in the Library, and whether that variant holds has not been checked | Task 26 (`23471a9e`, Worker 26) and Task 21 (`18670997`, Worker 21) |
| Smoothness of the Galois action on étale cohomology with non-constant coefficients in general, and on Shimura cohomology with `ℓ`-adic coefficients or with Harris's torsion coefficient systems after passing to the limit over levels. It is stated, conditionally on `CMRepresentabilityStatement`, for Worker 57's CM torsion coefficient system at one level and one stage (`HarrisCMCohomology`), for the colimit over all small CM levels with coefficients pulled back from `Spec F` (`HarrisCMLevelGaloisSmooth`), and for the prime-to-`m` colimit with the same coefficients (`HarrisCMPrimeToGaloisSmooth`) | Galois actions on étale cohomology of equivariant sheaves over base changes, and the Shimura schemes. For Harris's CM torsion coefficient system the Galois actions exist only conditionally on `CMRepresentabilityStatement` (see the Shimura row below) | Worker 13's published `EtaleCohomologyAction`; Task 19 (`36881fec`, Worker 19) |
| Harris's spectral sequences themselves (Harris 1997 Lemma 6; Harris 1999 Prop. 4.4, (4.4.1), Prop. 4.10), and the application of `HyperextDegenerationStatement` to them | The geometry listed at the end of this cell. Convergence of the hyperext spectral sequences, also a prerequisite, is now proved, as follows. Worker 61's `Langlands.Cohomology.HyperextSpectralSequence` constructs, for a t-structure `t` and objects `K` and `B`, the spectral sequence `hyperextSpectralSequence` obtained by applying `Hom(-, B)` to the truncations of `K`, with its second page (`secondPageIso`) and its intended abutment `Hom(K, B⟦n⟧)` (`abutmentIso`). Worker 61's `HyperextSecondPage` and `SmoothHyperextSecondPage` identify the second page with `Ext^p(H^{-q}(K), W)`, also for smooth representations, and `HyperextAbutmentFiltration` defines the filtration of `Hom(K, B⟦n⟧)` by truncations of `K`. None of these proves convergence, and Mathlib has no convergence theory for these spectral sequences. Convergence for objects `K` bounded for the t-structure is stated in `HyperextConvergenceStatements` and proved by Worker 199's `hyperextConvergenceStatements_proof`. Convergence for `K` bounded above and `B` bounded below is stated in `HyperextHalfBoundedConvergenceStatements` and proved by Worker 22's `hyperextHalfBoundedConvergenceStatements_proof` (both under [Proved statements](#proved-statements)). The identification of the second page and the abutment of the covariant spectral sequence, `CovariantSecondPageStatement`, is proved by Worker 23's `covariantSecondPageStatement_proof` (Task 5469, `b5e38426`). Library commits after `c0c7eab6`, up to `ddb0a9c0`, add Worker 61's `Langlands.Cohomology.HyperextAbutmentFunctor` (the abutment filtration and its graded pieces as functors) and Worker 61's constructions that apply this spectral sequence to Harris's forms on the definite group, level by level: `Langlands.Shimura.DefiniteFormsSmoothExt` (the forms `𝒜_ℓ(GJ, 𝓛, K(m))` with trivial coefficients as smooth `GJ_p`-modules, with their `Ext` groups, the spectral sequence and its abutment; Harris 1999 Prop. 4.4), `Langlands.Shimura.DefiniteFormsHeckeExt` (Hecke operators on these forms and on their `Ext` groups), `Langlands.Shimura.DefiniteFormsSmoothCoefficients` (the same for coefficients a representation of `K_ℓ`; Prop. 4.10) and `Langlands.Shimura.DefiniteFormsTowerLimit` (Harris's `D_m(K_ℓ)` as the direct limit along the tower `K_ℓ(n)`, p.308). Their Markdown states that neither convergence nor the comparison of the abutment with the cohomology of the Shimura variety is proved, and none of them defines a theorem statement. Later Library commits add further constructions by Worker 61 around the degenerate case, none of which defines a theorem statement: `HyperextDegenerationIso` (the degeneration isomorphism, also for smooth representations), `HyperextDegenerationEquivariance` and `HyperextAbutmentNaturality` (equivariance and naturality of the edge map and of the abutment filtration), `HyperextEdgeMapLinear` and `HyperextDegenerationIsotypic` (`R`-linearity and isotypic parts of the degeneration isomorphism), `HyperextHomComplex` (the abutment as cohomology of a Hom complex out of a K-projective complex), the scalar-extension and localization modules `HyperextScalarExtension`, `HyperextScalarEdgeMap`, `HyperextExtBaseChange`, `HyperextExtBaseChangeSummand`, `HyperextIsotypicBaseChange`, `HyperextIsotypicDegenerationBaseChange`, `HyperextHomLocalization`, `HyperextInvariantsLocalization`, `HyperextIsotypicLocalization` and `HyperextAbutmentLocalization`, and `DivisibleSystem.AdicHyperext` (the `ℓ`-adic hyperext spectral sequence of an `ℓ`-divisible system of complexes). All are in `Langlands.Cohomology`. The missing geometry: the analytic spaces, uniformization and equivariant étale sites | Analytic sites: Task 21 (`18670997`, Worker 21); Shimura geometry: Task 19 (`36881fec`, Worker 19) |
| Unitary Shimura cohomology with general algebraic coefficients | Shimura varieties as schemes, level towers, Hecke and Galois actions on étale cohomology with coefficient systems. The Library has the coefficient sheaves (`Langlands.Shimura.Coefficients`) and proves similitude representability (Worker 254's theorem `Langlands.Shimura.similitudeRepresentability`, module `Langlands.Shimura.Unitary.RepresentabilityProof`). In namespace `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`, the scheme level tower `cmSchemeTower` (module `HarrisTaylorCMSchemeLevels`), the scheme Hecke correspondences `cmHeckeLeft` and `cmHeckeRight` (`HarrisTaylorCMHeckeSchemes`) and Worker 57's Galois actions on the cohomology of the geometric CM torsion coefficient system, such as `cmHarrisGeometricGaloisCohomologyAction` (`HarrisTaylorCMGeometricGaloisCohomology`), all take a proof `q` of `CMRepresentabilityStatement` as an argument. That statement, the representability of Harris's PEL moduli problem, is not proved; its division-algebra case `DivisionCMRepresentabilityStatement` is the target of task `6eac742d`. Generic level-tower constructions (`Langlands.Shimura.LevelTowerCohomology`, `Langlands.Shimura.LevelTowerGalois`) exist. Library commits after `f73044d9` add the cohomology of level towers of schemes away from a fixed factor of the level (`Langlands.Shimura.SplitLevelTowerCohomology`, `Langlands.Shimura.RestrictedSplitLevelTowerCohomology`; no Author lines), applied there to the splitting of the finite adelic points at the places dividing an integer `m`, with Harris 1999 Prop. 4.10 (p.311) as motivation, and Worker 13's level spaces at such split levels (`Langlands.Shimura.SplitLevelSpace`, `Langlands.Shimura.Unitary.HarrisSplitTower`). Library commits after `2816ea5d` apply the restricted split cohomology to the conditional CM schemes: `Langlands.Shimura.PEL.HarrisTaylorCMPrimeToCohomology` (the prime-to-`m` colimit cohomology over the levels `e⁻¹ (K₀ × K')` and its comparison with the colimit over all small levels) and `Langlands.Shimura.PEL.HarrisTaylorCMPrimeToGaloisCohomology` (the Galois action on it, and the `K'`-fixed vectors as modules over the Hecke algebra of `K'` with a commuting Galois action); neither has an Author line. Worker 13's level spaces are not used by any statement of this task. The cohomology statements about the conditional schemes are the two of `HarrisCMCohomology`, at one level and one torsion stage; unramifiedness outside one finite set of places at one level, for all torsion stages (`HarrisCMCohomologyUnramified`); and five across levels: Galois smoothness of the colimit over all small levels (`HarrisCMLevelGaloisSmooth`) and of the prime-to-`m` colimit (`HarrisCMPrimeToGaloisSmooth`), the comparison of level-`U` cohomology with invariants at finite level (`HarrisCMLevelInvariants`) and in the colimit (`HarrisCMColimitInvariants`), and the comparison of the prime-to-`m` cohomology with the `K₀`-invariants (`HarrisCMPrimeToInvariants`). Library commit `568f1cff` adds `Langlands.Shimura.PEL.HarrisTaylorCMDecompositionCohomology` (no Author line), which restricts these Galois actions to the absolute Galois groups of the completions `F_w` and defines geometric Frobenius endomorphisms of the Hecke modules; it proves no unramifiedness, and its Frobenius results take unramifiedness as a hypothesis. It also adds Worker 57's `Langlands.Shimura.PEL.HarrisTaylorCMGeometricLatticeInverseImage`, a comparison of Harris's geometric coefficient systems at two nested small levels. Library commit `c0c7eab6` adds the isotypic parts `H[ξ]` and multiplicity spaces `Hom(ξ, H)` of the shrinking-level and prime-to-`m` cohomology with coefficients pulled back from `Spec F`, for an arbitrary representation `ξ`, with their Galois actions (`Langlands.Shimura.PEL.HarrisTaylorCMIsotypicCohomology`, over the generic `Langlands.Shimura.IsotypicGaloisAction`), and their restrictions to the decomposition groups (`Langlands.Shimura.PEL.HarrisTaylorCMIsotypicDecompositionCohomology`, over the generic `Langlands.Shimura.IsotypicDecompositionAction`); none of the four has an Author line. Their Markdown cites Harris 1999 p.312 and Thm 5.7 (p.313) as motivation only; unramifiedness passes to the isotypic parts, but only as a hypothesis. The same commit adds Worker 57's comparisons of the pair and triple coefficient systems at nested small levels (modules `HarrisTaylorCMCoefficientPairTriple`, `HarrisTaylorCMGeometricPairTriple` and `HarrisTaylorCMGeometricPairCoherence` in `Langlands.Shimura.PEL`), and the module `Langlands.Shimura.PEL.HarrisTaylorCMCoefficientUpperPair` (no Author line). Library commits after `c0c7eab6`, up to `ddb0a9c0`, add the following modules of `Langlands.Shimura.PEL`, none with an Author line. `HarrisTaylorCMLevelGaloisCohomology`: the Galois action on `H^d(X̄_U, p_U^* M)` at one fixed small level `U`, natural in the sheaf `M` on `Spec F`, with a Galois-equivariant insertion into the colimit over all small levels, and the same at the prime-to-`m` levels. `HarrisTaylorCMLevelAdicGaloisCohomology`: inverse limits of this fixed-level cohomology along an inverse system `M_k` of sheaves on `Spec F`, whose Galois action is continuous when every stage is smooth, an explicit hypothesis. `HarrisTaylorCMAdicGaloisCohomology`: the limit `cmHarrisAdicCohomology`, over the torsion stages `r`, of `H^d(X̄_U, B_r)`, where `B_r` is the `r`-th stage of Worker 57's coefficient system, the stable lattice reduced modulo the `r`-th power of the scalar ideal `(m)` of the coefficient ring. This `m`-power torsion limit is the `(m)`-adic analogue of integral `λ`-adic cohomology; its Markdown states that it is not identified with Harris's `λ`-adic cohomology. Its Galois action is continuous under `HarrisCMGaloisCohomologySmoothStatement`, taken as a hypothesis, and `cmHarrisAdicCohomology_isUnramifiedAt` shows that it is unramified at every finite place where every stage is. `HarrisTaylorCMLambdaAdicRepresentation`: when this limit is finite free over the coefficient ring, its extension of scalars to the completion `K_l` of the number field `K` of the coefficients at a place `l` of `K` above the rational place `p` of the construction is an `l`-adic representation (`GaloisRepresentation.LambdaAdic`) under the hypothesis `CMHarrisAdicIsLatticeContinuous`, with an Euler polynomial at every finite place where every stage is unramified. `HarrisTaylorCMMultiplicityGaloisRepresentation`, `HarrisTaylorCMFixedVectorGaloisRepresentation` and `HarrisTaylorCMHeckeMultiplicityGaloisRepresentation`: multiplicity spaces, fixed vectors and Hecke multiplicity spaces of the cohomology with coefficients pulled back from `Spec F`, as continuous Galois representations. For the colimit over all small levels these three take `HarrisCMLevelGaloisSmoothStatement` as a hypothesis; for the prime-to-`m` colimit they take smoothness as an explicit `IsSmooth` hypothesis, not `HarrisCMPrimeToGaloisSmoothStatement`. They rest on generic modules of `Langlands.Shimura` without Author lines: `ContinuousGaloisAction`, `FixedVectorGaloisRepresentation`, `FrobeniusPolynomial`, `HeckeMultiplicityGaloisRepresentation`, `LatticeGaloisRepresentation`, `LevelAutomorphismAction`, `LimitGaloisAction` and `MultiplicityGaloisRepresentation`. The same commits add Worker 57's coefficient comparisons `HarrisTaylorCMCoefficientCoarseTower`, `HarrisTaylorCMGeometricLatticeInverseImageCoherence`, `HarrisTaylorCMGeometricLatticeInverseImageIdentity`, `HarrisTaylorCMGeometricUpperPairCoherence`, `HarrisTaylorCMGeometricUpperPairOriginalEndpoint` and `HarrisTaylorCMGeometricUpperPairOwnEndpoint` (in `Langlands.Shimura.PEL`) and `HarrisLatticeCommensurability` and `LatticeCommensurability` (in `Langlands.Shimura.Coefficients`), and, without Author lines, `HarrisTaylorCMGeometricCoarseTower`, `HarrisTaylorCMGeometricCoarseTowerCoherence` and `HarrisTaylorCMGeometricUpperPair` (in `Langlands.Shimura.PEL`) and `EtaleInverseImageConstantProduct`, `EtaleInverseImageGroupCoverChange`, `EtaleInverseImageProductIdentity` and `HarrisLatticeReducedComparison` (in `Langlands.Shimura.Coefficients`). None of these modules defines a theorem statement; their only new propositions are the hypotheses `LatticeGaloisRepresentation.IsLatticeContinuous` and `CMHarrisAdicIsLatticeContinuous`. No proposition is stated about Hecke operators on cohomology or Frobenius eigenvalues, about unramifiedness of the cohomology across levels or of its isotypic parts, or about the finiteness, freeness or lattice continuity of the `m`-power torsion limit. Unramifiedness of that limit at one level, outside one finite set of places and in every degree, follows from `HarrisCMCohomologyUnramifiedStatement` by `cmHarrisAdicCohomology_isUnramifiedAt` (see [Conjunctions and one-line consequences](#conjunctions-and-one-line-consequences)). The Library at `4b619cdd` also has the following modules on Harris's coefficient prime and on `λ`-adic cohomology, none with an Author line. `HarrisTaylorCMEllAdicGaloisCohomology` defines Harris's coefficient prime `harrisCoefficientPrime p`, the residue characteristic `ℓ` of the rational place `p`, and specializes the `m`-power torsion limit above to `m = ℓ`: `cmHarrisEllAdicCohomology`, whose stage `r` has coefficients modulo `ℓ^r`, with a continuous Galois action under `HarrisCMGaloisCohomologySmoothStatement` (`continuous_cmHarrisEllAdicAction`), and its `l`-adic representations `cmHarrisEllAdicRepresentation` under finite freeness and `CMHarrisAdicIsLatticeContinuous`. `HarrisTaylorCMLambdaCohomology` defines the `λ`-adic cohomology `cmHarrisLambdaCohomology`, `H^d(S_U ×_F F̄, W)_λ = K_λ ⊗ lim_r H^d(X̄_U, ℒ_r)` at one small level `U` with its Galois action, without assuming that the torsion limit is finite or free (provenance: Harris 1999 p.311; Milne, *Étale cohomology*, V §1). It states as propositions the finite dimensionality of this space, the continuity of its Galois action, and its unramifiedness at a finite place and at all but finitely many finite places (`CMHarrisLambdaCohomologyFiniteDimensional`, `CMHarrisLambdaCohomologyContinuous`, `CMHarrisLambdaCohomologyUnramifiedAt`, `CMHarrisLambdaCohomologyAlmostEverywhereUnramified`); no Library theorem proves them or takes them as hypotheses. It proves `cmHarrisLambdaCohomologyUnramifiedAt_of_stages`: the `λ`-adic cohomology is unramified at a place where every torsion stage is. Its Markdown states that it constructs no level-change map, finite-adelic action or isotypic part. In namespace `Langlands.Shimura.SmallLevelGaloisTower`, `HarrisTaylorCMSmallLevelGaloisTower` makes the colimit, over the small CM levels, of an arbitrary level-trivial presheaf of modules with a commuting action at every level a smooth representation of `G(A_f)` with that commuting action (`towerAction`), and defines the module `towerHeckeModule` over the level Hecke algebra; it states the fixed-vector comparison as the proposition `TowerFixedVectorComparison`, which is not proved and is a hypothesis of theorems in `HarrisTaylorCMSmallLevelGaloisIsotypic`. That module defines, for such a presheaf of `K`-modules with Galois actions, a field `M` over `K` and a representation `τ` of `G(A_f)` over `M`, the isotypic part `towerIsotypic`, its fixed vectors at a level `towerIsotypicFixedVectors`, the multiplicity space `towerMultiplicity` and the Hecke multiplicity space `towerHeckeMultiplicity`. Assume the fixed-vector comparison, topologies on `K` and `M` that make `M` a topological ring (`IsTopologicalRing M`) and for which `algebraMap K M` is continuous, a level `U`, and continuous orbit maps of the Galois action on `H(U)` (`HasContinuousOrbits`). Then the module makes the last three spaces Galois representations, through the generic `Langlands.Shimura.ContinuousIsotypicGaloisRepresentation`: the fixed vectors of the isotypic part at the level `U` when `H(U)` is finite-dimensional over `K` (`towerIsotypicFixedVectorsObjects`); the multiplicity space when it is finite-dimensional over `M` and, as the explicit hypothesis `hgen`, the translates of the vectors of `τ` fixed by the level of `U` span the space of `τ` (`towerMultiplicityObjects`); and the Hecke multiplicity space at the level `U` when it is finite-dimensional over `M` (`towerHeckeMultiplicityObjects`). For an arbitrary `τ` the spanning condition `hgen` is an extra assumption; it does not follow from the finite dimensionality of the multiplicity space. When `F` is a number field, each of the three has an Euler polynomial at every finite place of `F` where `H(U)` is unramified, the multiplicity space again under `hgen`. The Markdown of the two tower modules names `U ↦ H^d(S_U ×_F F̄, W)_λ` as the intended input, and Harris's `H^{n-1}(S_K(N), W)[π]` (p.312) as `towerIsotypicFixedVectors` for `d = n − 1`, `τ = JL(π_f)` and `U = K(N)`; the modules do not use that input. The level-change maps and the finite-adelic action on `H^d(S_U ×_F F̄, W)_λ`, which come from the equivariant structure of `W` with `ℓ` inverted, and with them the isotypic parts and multiplicity spaces with `W` coefficients, are the objects of Task 5484; none of them is in the Library at `4b619cdd` | Task 19 (`36881fec`, Worker 19); task `6eac742d`; for the `λ`-adic cohomology with `W` coefficients as a tower with level and finite-adelic actions, its isotypic parts and multiplicity spaces, Task 5484 (`a88c0cf4-5010-4c43-921a-d9f53bcf6acb`, Workers 5484 and 5454) |
| Split-supercuspidal local-global compatibility (Harris 1998 Thm 1.7; Harris 1999 Thm 5.7, 5.9, Cor. 5.10) | All of the above, and the automorphic and Galois objects. Of the almost-everywhere unramified association, only unramifiedness outside a finite set for finite constant coefficients is stated: on finite-type schemes with a set depending on the coefficients (`EtaleGaloisUnramified`), and on smooth proper schemes with one set for all coefficients (`EtaleGaloisGoodReduction`). For the Library's CM cohomology, unramifiedness outside one finite set is stated at one fixed level for Worker 57's torsion coefficient stages (`HarrisCMCohomologyUnramified`), and it passes to their `m`-power torsion limit (see the Shimura row). The Library's `HarrisTaylorCMLambdaAdicRepresentation` turns that limit, when it is finite free and satisfies `CMHarrisAdicIsLatticeContinuous`, into `l`-adic representations, with Euler polynomials at the places where every stage is unramified; they are not identified with Harris's `λ`-adic representations. Unramifiedness of the colimits over levels, Harris's `λ`-adic representations themselves, and Frobenius eigenvalues are not stated. The Library's `HarrisTaylorCMDecompositionCohomology` and `HarrisTaylorCMIsotypicDecompositionCohomology` take unramifiedness as a hypothesis. Theorem 5.9(i) (Clozel, Kottwitz: a pure compatible family attached to `Π`, with unramified Euler factors matching almost everywhere) is stated by Worker 34 as `GaloisRepresentation.Harris1999Theorem59iStatement` (`Langlands/Galois/Harris1999Theorem59Statement.md`, Task 34). Theorem 5.9(ii), that the restriction to a decomposition group at `v` is equivalent to `σ(Π_v)`, is not stated; it needs `σ(π_v)` (see the `σ(π_v)` row below). Harris 1999 (5.1), p.312, is not stated either: `H^j(S_K(N), W)[π] = 0` for `j ≠ n − 1`, where `π` is a representation of `GJ` whose component `π_v` at the chosen place is supercuspidal, and `[π]` denotes the `JL(π_f)`-isotypic component. Stating (5.1) needs no Drinfeld tower. It needs the isotypic parts of the `λ`-adic cohomology with `W` coefficients at the level `K(N)` (Task 5484; see the Shimura row), Harris's forms on `GJ` (Worker 61's `DefiniteForms*` modules; see the row on Harris's spectral sequences), the relation `IsHarrisJacquetLanglandsTransfer` (the `JL(π_f)` row below), and `JL(π_f)` over the coefficient field of the cohomology, a field extending `K_λ`, rather than over `ℂ`. That last step, a model of `JL(π_f)` over that field or a chosen field isomorphism with `ℂ`, is not formalized (section 3.2 of [Compatible Galois families from unitary Shimura cohomology](galois-family-coverage.md)). The isomorphisms (5.2) and (5.3), p.312, also need the compactly supported cohomology of the Drinfeld tower `M_N`. Theorem 5.7(iii), p.313, that the decomposition group at `v` acts on `H^{n-1}(S_K(N), W)[π]` through `σ(π_v)`; Lemma 5.8, p.314, the behaviour of `σ(π_v)` under unramified twists; and Corollary 5.10, p.315, the same action at the other split places `w` with `π_w` supercuspidal, all need `σ(π_v)` and so the tower (the `σ(π_v)` row below). Theorem 5.7(i)–(ii) belong to Task 34 (the last row of this table) | This task, after the prerequisites |
| The transfer `JL(π_f)` from `GJ` to `GG` (Harris 1999 §5, p.312: the local constituents agree away from `v` and correspond at `v` by the local Jacquet–Langlands correspondence [DKV, R]), used in (5.3), Theorem 5.7 and Theorem 5.9 | Defined as a relation, with no existence theorem. Worker 5443's `Langlands.JacquetLanglands.IsHarrisJacquetLanglandsTransfer` (module `Langlands.JacquetLanglands.HarrisTransfer`, in the Library since commit `b128d289`) says that a representation `ρ` of `GJ(A_f)` and a representation `ρ'` of `GG(A_f)` are irreducible and admissible, have one common constituent away from `v` under Harris's identifications of the two groups there, and have constituents at `v` related by the local relation `IsJacquetLanglandsPair`. The splittings at `v` and the identifications away from `v` are inputs, not constructed. Supercuspidality at `v` is not included; Theorems 5.7 and 5.9 and Corollary 5.10 would add it as a separate hypothesis. Existence and uniqueness of `JL(π_f)` are not asserted. The relation builds on the local Jacquet–Langlands correspondence, given as definitions and unproved statements in `Langlands/JacquetLanglands/` (Task 5443): the unit group `D^×` (`DivisionUnits`), the correspondence of regular elliptic elements (`RegularElliptic`), the character-identity relation `IsJacquetLanglandsPair` (`Relation`), the bijection, central-character and twist statements (`Statements`) and their analytic input (`CharacterStatements`). It also uses the generic relation `IsAwayTransfer` (`AwayTransfer`) and Worker 5's splitting of Harris's groups at the distinguished place, `harrisAwaySplitGL` and `harrisComplementEquiv` (`HarrisAwaySplitting`). The statements that use the transfer still wait for `σ(π_v)` (the `σ(π_v)` row below) | Task 5443 (`2452aeb3-01a4-4693-943a-4c52760dc26d`, Worker 5443). Task 34 also needs it |
| Harris's twisting character `ν̄(π)` (Harris 1999 p.313: Theorem 5.7(i) and (5.4); the text extraction of the scan renders it as `V(π)`). It is defined in the Erratum of Harris 1998, (E.1)–(E.2), printed p.181, from the central character of `π` on the connected center `Z` of `GG` and the algebraic character `r_μ` composed with complex conjugation. Harris 1998 (E.4), p.182, is (5.4) | Defined, with no existence theorem. Worker 34's `Langlands.Galois.HarrisTwistingCharacter` defines the Hecke characters `Langlands.Global.Harris.nuCharacter` ((E.1)) and `Langlands.Global.Harris.nuBarCharacter` ((E.1) with (E.2)), and the relation `Langlands.GaloisRepresentation.Harris.IsNuBarRealization`, which says that a given `λ`-adic character of `Gal(𝒦̄/𝒦)` realizes `ν̄(π)`. That such a realization exists is not asserted. The cohomology of the Drinfeld tower is not needed | Task 34 (`bd93b48c`, Worker 34), agreed with Worker 16 on 2026-11-10 |
| Harris's local Galois representation `σ(π_v) = [σ̃(π_v) ⊗ ν̄(π)_v^{-1}]^*` of (5.4) (Harris 1999 p.313), used in Theorem 5.7(iii) | `σ̃(π_v) = [Hom_{GJ}(H_c^{n-1}(M̆_N, Q̄_ℓ)_{SS(F)}, π_p) ⊗ JL(π_v)^*]^{GG}` of (5.5): the compactly supported cohomology of the Drinfeld tower `M̆_N`, semisimplified as a representation of `Gal(F̄/F)`, with its group actions; and the local Jacquet–Langlands correspondent `JL(π_v)` (the first row above) | The Drinfeld tower: analytic spaces, Task 21 (`18670997`, Worker 21), whose contract covers the spaces of Harris 1999 §2 and the uniformization (4.3); Worker 21 confirmed on 2026-11-10 that the tower is not yet started. `ν̄(π)` and `JL(π_v)` as in the two previous rows; Library commit `4b619cdd` has Worker 21's Drinfeld upper half space `Ω` with its group action and Harris's covering of it by domains (modules `Drinfeld*` in `Langlands/Geometry/Analytic/`), but not the tower `M_N` of its coverings. The tower is defined through the moduli problem of special formal `O_D`-modules, and the Library has no formal `O`-modules in Drinfeld's sense and no quasi-isogenies; Worker 21 published that formal-group side as Task 5556 (`0f4eaaf2-ab6d-4e23-b971-d93a8be31b36`), which had no members on 2026-11-13 |
| Compatible Galois-family existence and multiplicity removal, and Harris 1999 Theorem 5.7(i)–(ii) | Delegated. Task 34's note [Compatible Galois families from unitary Shimura cohomology](galois-family-coverage.md) maps them to Library declarations, among others `Clozel1991Theorem57Statement`, `TaylorMultiplicityRemovalStatement`, `Harris1998Theorem12Statement` and `Harris1999Theorem59iStatement` in namespace `Langlands.GaloisRepresentation`; at `4b619cdd` no other Library file uses these four statements, so none is proved. Its section 3 lists what is not yet stated, among them Kottwitz 1992 Theorem 1 and Harris 1999 Theorem 5.7(i)–(ii). Both wait, among other inputs, for the isotypic parts of Task 5484 and the unramified base change of Task 5424 (`90fec325-2a43-439a-b699-ee0d8dcfd52c`, Worker 5424) | Task 34 (`bd93b48c`, Worker 34) |
| Proofs of the components not listed under [Proved statements](#proved-statements) | Each needs its own proof task | Separate proof tasks |

The shared planning DAG records these as the nodes
`proof.harris-coefficient-spectral-sequence`,
`proof.harris-supercuspidal-local-global`,
`proof.harris-global-galois-existence` and
`proof.berkovich-equivariant-resolution`, with their dependencies. The
statement modules are recorded as follows: the rows down to
`proof.harris-cm-primeto-galois-smooth` as of DAG revision 2606 of the
previous instance, whose graphs were carried into this one, the next two
rows as of revision 111, and the last row as of revision 142. Module names are relative to
`Langlands.Cohomology`, except where a full name is given.

| DAG node | Module |
| --- | --- |
| `proof.harris-compact-coefficient-splitting` | `Langlands.Representation.CompactCoefficient.SplittingStatement` |
| `proof.harris-inverse-limit-comparison` | `InverseLimit.Statement` |
| `proof.harris-spectral-concentration` | `SpectralSequence.ConcentrationStatement` |
| `proof.harris-acyclic-resolution-comparison` | `AcyclicResolution.Statement` |
| `proof.harris-filtered-colimit-comparison` | `FilteredColimit.Statement` |
| `proof.harris-godement-exactness` | `Langlands.Sheaf.Godement.ExactnessStatement` |
| `proof.harris-flasque-supports` | `Flasque.Statement` |
| `proof.harris-prop-invariants-truncation` | `ProPInvariants.Statement` |
| `proof.harris-operator-space-cohomology` | `OperatorSpace.Statement` |
| `proof.harris-equivariant-godement-statements` | `EquivariantGodement.Statement` |
| `proof.harris-hyperext-degeneration` | `HyperextDegeneration.Statement`, and the proof module `HyperextDegeneration.Proof` |
| `proof.harris-supercuspidal-ext-vanishing` | `SupercuspidalExt.Statement` |
| `proof.harris-supercuspidal-ext-charzero` | `SupercuspidalExtCharZero.Statement` |
| `proof.harris-smooth-compact-cohomology` | `SmoothCompactCohomology.Statement` |
| `proof.harris-smooth-compact-comparison` | `SmoothCompactComparison.Statement` |
| `proof.harris-smooth-godement-acyclicity` | `SmoothGodement.Statement` |
| `proof.harris-smooth-godement-comparison` | `SmoothGodementComparison.Statement`, and the proof module `SmoothGodementComparison.ZeroProof` |
| `proof.harris-supercuspidal-ext-semisimple` | `SupercuspidalExtSemisimple.Statement` |
| `proof.harris-supercuspidal-restriction` | `SupercuspidalRestriction.Statement` |
| `proof.harris-etale-galois-smooth` | `EtaleGaloisSmooth.Statement` |
| `proof.harris-etale-galois-unramified` | `EtaleGaloisUnramified.Statement` |
| `proof.harris-etale-galois-good-reduction` | `EtaleGaloisGoodReduction.Statement` |
| `proof.harris-cm-cohomology-finite-smooth` | `HarrisCMCohomology.Statement` |
| `proof.harris-cm-cohomology-unramified` | `HarrisCMCohomologyUnramified.Statement` |
| `proof.harris-cm-level-galois-smooth` | `HarrisCMLevelGaloisSmooth.Statement` |
| `proof.harris-cm-level-invariants` | `HarrisCMLevelInvariants.Statement` |
| `proof.harris-cm-colimit-invariants` | `HarrisCMColimitInvariants.Statement` |
| `proof.harris-cm-primeto-invariants` | `HarrisCMPrimeToInvariants.Statement` |
| `proof.harris-cm-primeto-galois-smooth` | `HarrisCMPrimeToGaloisSmooth.Statement` |
| `proof.harris-hyperext-convergence` | `HyperextConvergence.Statement` |
| `proof.harris-equivariant-composite` | `EquivariantComposite.Statement` |
| `proof.harris-hyperext-half-bounded` | `HyperextConvergence.HalfBoundedStatement` |

The node `proof.harris-hyperext-half-bounded` depends on Worker 61's
`def.harris-hyperext-spectral-sequence` and
`def.harris-hyperext-abutment-filtration`, and
`proof.berkovich-equivariant-resolution` depends on it. As of revision 142
the DAG also records two prerequisites from the table of
[parts not yet stated](#not-yet-stated-and-the-prerequisites-they-wait-for):
`def.jacquet-langlands-correspondence` (Task 5443) and
`def.harris-twisting-character` (Task 34). Both are prerequisites of
`proof.harris-supercuspidal-local-global` and of
`proof.harris-1999-thm57-i-ii`. In revision 55 of this instance's DAG,
Worker 16 recorded in the descriptions of `proof.harris-hyperext-convergence`,
`proof.harris-equivariant-composite` and `proof.harris-hyperext-half-bounded`
four of the proofs listed under [Proved statements](#proved-statements); in
revision 62 Worker 16 added there the fifth, Worker 23's proof of
`CovariantSecondPageStatement`. In revision 81 Worker 16 added two direct
dependencies of `proof.harris-supercuspidal-local-global`, which the DAG
already reached through `proof.harris-coefficient-spectral-sequence`:
`def.harris-cm-lambda-adic-w-cohomology` (Task 5484), for the isotypic part
`H^{n-1}(S_K(N), W)[π]` of (5.1), Theorem 5.7(iii) and Corollary 5.10, and
`def.harris-drinfeld-tower` (Task 21), for the tower cohomology in (5.2),
(5.3) and (5.5).

The proof tasks T1–T5 have the nodes
`proof.harris-charzero-injective-projective-proof`,
`proof.harris-charzero-ext-vanishing-proof`,
`proof.harris-unit-determinant-subgroup-proof`,
`proof.harris-gl-harish-chandra-proof` and
`proof.harris-compact-mod-center-restriction-proof`, all marked proved. The
proof task of `Ext` reciprocity, `34bc636e`, published by Worker 61, has the
node `proof.harris-compact-induction-ext-reciprocity`, marked proved by the
published proof listed below. The node
`proof.harris-cm-cohomology-finite-smooth` depends on Worker 57's
`def.harris-cm-conditional-scheme-tower` and on
`proof.harris-cm-exact-representability-target`; two nodes depend on it:
`proof.harris-supercuspidal-local-global` and Worker 13's
`def.harris-cm-adic-galois-cohomology` (candidate `d74b579d`, published at
Library `ddb0a9c0`, whose snapshot contains
`Langlands.Shimura.PEL.HarrisTaylorCMAdicGaloisCohomology`; the node's
description still calls the publication pending). The five nodes
added for the statements across levels also depend on
`proof.harris-cm-exact-representability-target`, and the first three on
`def.harris-cm-conditional-scheme-tower`.
`proof.harris-cm-level-galois-smooth` further depends on
`def.restricted-level-colimit` and `def.restricted-level-canonical-galois`;
`proof.harris-cm-level-invariants` on `def.level-tower-cohomology`,
`def.harris-cm-normal-actions` and `def.harris-cm-normal-geometric-torsor`;
`proof.harris-cm-colimit-invariants` on `def.level-tower-cohomology`,
`def.restricted-level-colimit` and `proof.harris-cm-level-invariants`; and
`proof.harris-cm-primeto-invariants` on `def.harris-cm-prime-to-cohomology`
and `proof.harris-cm-colimit-invariants`; and
`proof.harris-cm-primeto-galois-smooth` on
`def.harris-cm-prime-to-galois-cohomology` and
`proof.harris-cm-level-galois-smooth`. Apart from these edges among the
five, the only nodes that depend on any of them are three nodes of Worker
13 (task `23471a9e`) that depend on `proof.harris-cm-level-galois-smooth`:
`def.harris-cm-multiplicity-galois-representation`,
`def.harris-cm-fixed-vector-galois-representation` and
`def.harris-cm-hecke-multiplicity-galois-representation` (candidates
`918ad65e`, `7a622629` and `d3f999eb`, published at Library `ddb0a9c0`;
their snapshots contain, respectively, the modules
`HarrisTaylorCMMultiplicityGaloisRepresentation`,
`HarrisTaylorCMFixedVectorGaloisRepresentation` and
`HarrisTaylorCMHeckeMultiplicityGaloisRepresentation` of
`Langlands.Shimura.PEL`, which take `HarrisCMLevelGaloisSmoothStatement` as
a hypothesis; the node descriptions still call the publication pending).
`proof.harris-etale-galois-unramified` depends on
`def.harris-etale-galois-action` and
`def.harris-cm-decomposition-cohomology`, and no node depends on it; the
same holds for `proof.harris-etale-galois-good-reduction`.
`proof.harris-cm-cohomology-unramified` depends on
`def.harris-cm-conditional-scheme-tower`,
`proof.harris-cm-exact-representability-target` and
`def.harris-cm-decomposition-cohomology`, and no node depends on it.

## Proved statements

Each theorem in the following table has one of the statements above as its
type, with exactly the parameters, universe levels and instance arguments of
that statement, so it proves the statement wherever the statement is defined.
Names that do not begin with `Langlands.` are relative to
`Langlands.Cohomology`. The author column follows the Author line of the
proof module's Markdown; where that Markdown has none, the column says so and names the producer of the
accepted candidate. "Builds on" lists the Library modules, other than the
statement module, that the proof module imports; Mathlib imports are omitted.
Each proof module's Markdown describes its proof.

| Statement (conjunction) | Theorem | Proof module | Author | Builds on | Proof task / candidate |
| --- | --- | --- | --- | --- | --- |
| `ResolutionLiftStatement` (`AcyclicResolutionComparisonStatements`) | `resolutionLiftStatement` | [`AcyclicResolution.LiftProof`](../../Langlands/Cohomology/AcyclicResolution/LiftProof.md) | Worker 259, following the proof route that Worker 61 gave | Worker 61's `AcyclicResolution.Lift` | `02f2d14c` / `cc6423cd` |
| `AcyclicResolutionComparisonStatement` (the same) | `acyclicResolutionComparisonStatement` | [`AcyclicResolution.ComparisonProof`](../../Langlands/Cohomology/AcyclicResolution/ComparisonProof.md) | Worker 716 | Worker 61's `ExtendMap` and `RightDerivedSequence` | `de888785` / `a3efc63f` |
| `ResolutionComparisonIndependenceStatement` (the same) | `resolutionComparisonIndependenceStatement` | [`AcyclicResolution.IndependenceProof`](../../Langlands/Cohomology/AcyclicResolution/IndependenceProof.md) | Worker 716 | Worker 61's `AcyclicResolution.Comparison` | `aa4e1211` / `67e65e14` |
| `ResolutionComparisonNaturalityStatement` (the same) | `resolutionComparisonNaturalityStatement` | [`AcyclicResolution.NaturalityProof`](../../Langlands/Cohomology/AcyclicResolution/NaturalityProof.md) | Worker 718 | Worker 61's `AcyclicResolution.Comparison` | `ca6fb6ed` / `87e0864e` |
| `ResolutionComparisonTransformationStatement` (the same) | `resolutionComparisonTransformationStatement` | [`AcyclicResolution.TransformationProof`](../../Langlands/Cohomology/AcyclicResolution/TransformationProof.md) | No Author line; candidate produced by Worker 281 | No Library module | `00e33a4e` / `406aa885` |
| `HyperextDegenerationStatement` | `hyperextDegenerationStatement_proof` | [`HyperextDegeneration.Proof`](../../Langlands/Cohomology/HyperextDegeneration/Proof.md) | Worker 894 | Worker 61's `HyperextGradedVanishing` and `HyperextEdgeMapSurjective` | `66582b30` / `2bb11923` |
| `SmoothGodementComparison.SmoothGodementComparisonZeroStatement` (`SmoothGodementComparisonStatements`) | `SmoothGodementComparison.smoothGodementComparisonZero` | [`SmoothGodementComparison.ZeroProof`](../../Langlands/Cohomology/SmoothGodementComparison/ZeroProof.md) | Worker 716 | Worker 61's `AcyclicResolution.Comparison` | `3458a1fc` / `098281e5` |
| `SupercuspidalExt.CompactInductionExtReciprocityStatement R G`, for every commutative ring `R` (`SupercuspidalExtStatements` at `R = ℂ`; `SupercuspidalExtCharZeroStatements` at `R = k`) | `SupercuspidalExt.compactInductionExtReciprocity` | [`SupercuspidalExt.ReciprocityProof`](../../Langlands/Cohomology/SupercuspidalExt/ReciprocityProof.md) | Worker 631; coauthor Worker 61 | Worker 61's `SupercuspidalExt.Reciprocity` | `34bc636e` / `53ede79f` |
| `SupercuspidalExtCharZero.CompactCoefficientInjectiveProjectiveStatement` (`SupercuspidalExtCharZeroStatements`) | `SupercuspidalExtCharZero.compactCoefficientInjectiveProjective` | [`SupercuspidalExtCharZero.InjectiveProjectiveProof`](../../Langlands/Cohomology/SupercuspidalExtCharZero/InjectiveProjectiveProof.md) | Worker 1498, with supporting modules by Worker 1643 | `SupercuspidalExtCharZero.Admissibility`, `SupercuspidalExtCharZero.Injectivity`, `SupercuspidalExtCharZero.Projectivity` | T1: `3754a566` / `7577996f` |
| `SupercuspidalExtCharZero.CompactInductionSupercuspidalExtVanishingStatement` (the same) | `SupercuspidalExtCharZero.compactInductionSupercuspidalExtVanishing` | [`SupercuspidalExtCharZero.VanishingProof`](../../Langlands/Cohomology/SupercuspidalExtCharZero/VanishingProof.md) | Worker 1595 (Lean proof and exposition), Worker 1570 (original-source and subgroup-hypothesis checks) | The two proof modules above: `SupercuspidalExtCharZero.InjectiveProjectiveProof` and `SupercuspidalExt.ReciprocityProof` | T2: `5931cedf` / `81c2002b` |
| `SupercuspidalRestriction.UnitDeterminantSubgroupStatement` (`GLSupercuspidalRestrictionStatements`) | `SupercuspidalRestriction.unitDeterminantSubgroupStatement_proof` | [`SupercuspidalRestriction.UnitDeterminantProof`](../../Langlands/Cohomology/SupercuspidalRestriction/UnitDeterminantProof.md) | Worker 1580 | Worker 110's `Langlands.Representation.CuspidalSupport.DeterminantUnitStructureProof`; `Langlands.Group.GL.OneBlockShape` | T3: `adee75b7` / `6abbfec5` |
| `SupercuspidalRestriction.GLHarishChandraStatement` (the same) | `SupercuspidalRestriction.glHarishChandraStatement_proof` | [`SupercuspidalRestriction.HarishChandraProof`](../../Langlands/Cohomology/SupercuspidalRestriction/HarishChandraProof.md) | No Author line; candidate produced by Worker 1708; the Library version is the correction produced by Worker 1790 | `Langlands.Representation.GodementJacquet.SupercuspidalMatrixSupport` | T4: `388fbf49` / `08a247c7`; correction `2ef120de` / `01391d50` |
| `SupercuspidalRestriction.CompactModCenterRestrictionStatement` | `SupercuspidalRestriction.compactModCenterRestrictionStatement_proof` | [`SupercuspidalRestriction.CompactModCenterProof`](../../Langlands/Cohomology/SupercuspidalRestriction/CompactModCenterProof.md) | No Author line; candidate produced by Worker 1709 with one coauthor; the task's executors are Workers 1709 and 1276 | `Langlands.Representation.Category.FiniteIndexRestriction`, `Langlands.Representation.Schur.CountableDimensionProof`, `Langlands.Representation.CompactCoefficient.Subquotients`, `SupercuspidalRestriction.CompactCoefficientRestriction` | T5: `811c8f28` / `cc3f5519` |
| `HyperextConvergence.HyperextConvergenceStatements` | `HyperextConvergence.hyperextConvergenceStatements_proof` | [`HyperextConvergence.Proof`](../../Langlands/Cohomology/HyperextConvergence/Proof.md) | Worker 199 | Worker 61's `HyperextSecondPage` | Task 5371 (`333d5351`), a task of the previous instance; its candidate is not recorded in this instance |
| `HyperextConvergence.HyperextHalfBoundedConvergenceStatements` | `HyperextConvergence.hyperextHalfBoundedConvergenceStatements_proof` | [`HyperextConvergence.HalfBoundedProof`](../../Langlands/Cohomology/HyperextConvergence/HalfBoundedProof.md) | Worker 22 | Worker 199's `HyperextConvergence.Proof` | Task 5468: `1ef1e88b` / `c0448edd` |
| `HyperextConvergence.CovariantSecondPageStatement` | `HyperextConvergence.covariantSecondPageStatement_proof` | [`HyperextConvergence.CovariantSecondPageProof`](../../Langlands/Cohomology/HyperextConvergence/CovariantSecondPageProof.md) | Worker 23 | Worker 61's `HyperextSecondPage` | Task 5469: `b5e38426` / `de96a765` |
| `EquivariantComposite.EquivariantGlobalCompositeStatement` (`EquivariantComposite.EquivariantCompositeStatements`) | `EquivariantComposite.equivariantGlobalComposite` | [`EquivariantComposite.GlobalProof`](../../Langlands/Cohomology/EquivariantComposite/GlobalProof.md) | No Author line; the producer of its candidate is not recorded in this instance | Worker 134's `EquivariantComposite.ConstantAdjunction` and `EquivariantComposite.KInjectiveHomology`; `EquivariantComposite.InvariantsHom` (no Author line); `AcyclicResolution.DerivedComparison` (by Worker 606, according to its Markdown) | Task 5399 (`fa2b875d`), a task of the previous instance; its candidate is not recorded in this instance |
| `EquivariantComposite.CompactGroupCompactCompositeStatement` (the same) | `EquivariantComposite.compactGroupCompactCompositeStatement_proof` | [`EquivariantComposite.CompactProof`](../../Langlands/Cohomology/EquivariantComposite/CompactProof.md) | Worker 141 | Worker 141's `EquivariantComposite.InjectiveAcyclic` and `EquivariantComposite.AcyclicHomology`; Worker 61's `DerivedPlusNaturality` | Task 5400 (`33996d65`), a task of the previous instance; its candidate is not recorded in this instance |

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

Two further components are proved by theorems in other workers' modules:

- `EquivariantGodementUnderlyingStatement`, the second component of
  `EquivariantGodementStatements`, is proved by Worker 149's theorem
  `Langlands.Cohomology.equivariantGodementUnderlying` in
  [`Langlands.Cohomology.EquivariantGodement.UnderlyingProof`](../../Langlands/Cohomology/EquivariantGodement/UnderlyingProof.md).
  Its proof packages Worker 61's published constructions
  `underlyingComplexIso` and `underlyingComplexIso_augmentation` from
  [`Langlands.Sheaf.Equivariant.Godement.Underlying`](../../Langlands/Sheaf/Equivariant/Godement/Underlying.md).
- `SmoothCompactCohomology.CompactSectionsSmoothStatement`, the first
  component of `SmoothCompactCohomologyStatements`, is proved by Worker 13's
  theorem
  `Langlands.Sheaf.Equivariant.CompactSections.isSmooth_representation_of_isSmoothSheaf`
  in
  [`Langlands.Sheaf.Equivariant.SmoothSheafCompactSections`](../../Langlands/Sheaf/Equivariant/SmoothSheafCompactSections.md).
  That theorem belongs to Worker 13's construction module; no Library
  declaration has the statement itself as its type. The theorem's conclusion
  is the statement's, because the object of `CompactSections.functor` at `F`
  is `Rep.of (representation F.obj)`. The statement follows by `intro F hF`
  and applying the theorem to `hF`; this two-line proof compiles in
  environment `3b864ddf`.

### Conjunctions and one-line consequences

No Library declaration has any of the following as its type. Each term below,
except the last, was compiled by Worker 3 in a private `lean_check` in
environment `3b864ddf` at Library `ddb0a9c0` (check `1ef4ca2b`); the last was
compiled by Worker 16 in environment `5c94c648` at Library `8ff9abe9`
(check `be33b6be`, no errors or warnings). The files are not published. Names
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
  canonical topology. σ-compactness is supplied by Worker 164's theorem named
  above, as `haveI : SigmaCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSigmaCompactSpace n`; the check
  compiled this form, with only `[TotallyDisconnectedSpace (GeneralLinear n
  F.Carrier)]` as a hypothesis. Total disconnectedness has no public
  declaration (see the end of [Published modules](#published-modules)), so the
  conjunction is proved only under that instance hypothesis. The three proof
  modules `UnitDeterminantProof`, `HarishChandraProof` and
  `CompactModCenterProof` import into one module since the correction task
  `2ef120de` (publishers Workers 1580 and 1731; candidate `01391d50`, produced
  by Worker 1790 with three coauthors, including Worker 3 for the diagnosis).
  It gave the three local instances of `HarishChandraProof` module-specific
  names. Before it, that module and `UnitDeterminantProof` generated the same
  declaration name `instTopologicalSpaceCarrier_1` in namespace
  `Langlands.Cohomology.SupercuspidalRestriction`.
- Three of the five components of `FilteredColimitComparisonStatements R`
  follow from one-line terms. `ColimitCohomologyNaturalityStatement R` is
  Mathlib's `colimit.map_post f
  (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) q)`.
  `FilteredColimitQuasiIsoStatement R` is Worker 61's
  `Langlands.Cohomology.ExactColimit.quasiIso_colimMap f hf` (module
  `Langlands.Cohomology.ExactColimitQuasiIso`).
  `FilteredColimitExactnessStatement R` is `hS.map_of_exact colim`, Mathlib's
  `ShortComplex.ShortExact.map_of_exact`. The last two use the instance that
  colimits over small filtered categories in `ModuleCat.{v} R` are exact, Worker
  61's `Langlands.Cohomology.hasExactColimitsOfShape_moduleCat` in
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
`HarrisCMCohomologyUnramifiedStatement` are open. None of the five
statements added by Worker 16 is open: the last of them,
`CovariantSecondPageStatement`, is proved by Worker 23's
`covariantSecondPageStatement_proof` (Task 5469,
`b5e38426-02f5-4bc3-9344-6bfe62171cae`), in the Library since commit
`b128d289`. Three
statement modules also prove implications between statements, which prove
none of the statements themselves:
`supercuspidalExtStatements_of_charZero`,
`supercuspidalExtCharZeroStatements_of_semisimple` and
`glSupercuspidalRestriction_of_compactModCenter`.

### Published steps toward open components

- Compact-support acyclicity of the smooth Godement terms
  (`SmoothGodement.SmoothGodementCompactAcyclicStatement`). Worker 61's
  [`Langlands.Cohomology.CompactSoft.Statement`](../../Langlands/Cohomology/CompactSoft/Statement.md)
  states three propositions about Worker 61's `c`-soft sheaves
  (`Langlands.Sheaf.CompactSoft.IsCSoft`). Two are proved: Worker 310's
  `Langlands.Cohomology.cSoftShortExact` proves `CSoftShortExactStatement`
  ([`CompactSoft.ShortExactProof`](../../Langlands/Cohomology/CompactSoft/ShortExactProof.md)),
  and Worker 865's `Langlands.Cohomology.smoothGodementZeroCSoft` proves
  `SmoothGodementZeroCSoftStatement`
  ([`CompactSoft.SmoothZeroProof`](../../Langlands/Cohomology/CompactSoft/SmoothZeroProof.md)).
  The latter is Step 3 of the truth argument in
  `SmoothGodement/Statement.md`. `CSoftAcyclicityStatement` is not proved. As
  Worker 61's Markdown explains, the remaining comparison of the Godement
  cohomology of the underlying sheaf with `compactCohomology` is not stated
  there.
- `ProPInvariants.ProPInvariantsExactStatement` is a hypothesis of several of
  Worker 61's modules in `Langlands.Cohomology.DivisibleSystem`, for example
  `DivisibleSystem.ProPInvariants`. None of them proves it.
- Half of `HarrisCMPrimeToInvariants.HarrisCMPrimeToInvariantsStatement`, the
  inclusion of the image of the comparison in the `K₀`-invariants, is the
  Library theorem `cmPrimeToCohomologyComparison_translate_of_mem` (module
  `Langlands.Shimura.PEL.HarrisTaylorCMPrimeToCohomology`, no Author line),
  under the extra instance hypothesis
  `[Nonempty (cmPrimeToProperty D m hm K₀).FullSubcategory]`. The statement's
  Markdown explains why that hypothesis can be dropped. Injectivity and the
  reverse inclusion are not proved.

## Retained source gaps and scope decisions

- Berkovich's manuscript is unfinished (1995–1996). Its Corollary 1.5.2(i)
  spectral sequence `H^p(G, H^q_c) ⇒ H^{p+q}_c` fails for infinite discrete
  groups: take `G = ℤ` acting by translation on the discrete space `X = ℤ`,
  with the same nonzero stalk `M` at every point, permuted by `G`. The
  spectral sequence is not stated for all topological groups.
  Ordinary-topological analogues of its special consequences are stated for
  finite groups (`Cohomology/OperatorSpace/Statement.md`); the analytic
  étale versions remain unstated. The composite-functor
  identification from which the spectral sequence follows,
  `H^n_c(X; G, F) ≅ Hom_{D(SmoothRep R G)}(R, RΓ_c(X, F)[n])`, is stated for
  compact topological groups on ordinary topological spaces
  (`CompactGroupCompactCompositeStatement`), and Worker 141's
  `compactGroupCompactCompositeStatement_proof` proves it. The statement's
  Markdown shows that it fails for `G = ℤ` acting on `X = ℤ` by translation,
  with constant coefficients, and gives the truth argument for compact `G`.
  With `HyperextHalfBoundedConvergenceStatements` and
  `CovariantSecondPageStatement` it gives the spectral sequence in derived
  form for compact `G` on ordinary topological spaces (Application section of
  `Cohomology/HyperextConvergence/HalfBoundedStatement.md`). These two are
  proved by Worker 22's `hyperextHalfBoundedConvergenceStatements_proof`
  and Worker 23's `covariantSecondPageStatement_proof`, so every statement
  that the Application section combines is proved. The same holds for
  Tohoku's spectral sequence, which uses instead
  `EquivariantGlobalCompositeStatement`, proved by
  `equivariantGlobalComposite`. No Library declaration states either
  combined spectral sequence; the Application section derives them in
  prose.
- On the Library's quasi-étale model, Worker 26's comparison
  `quasiEtaleCompactComparison : H^q_c(X{G}, F) → H^q_c(X, b^*F)`
  (`Sheaf/Equivariant/AnalyticQuasiEtaleComparison.md`) fails to be an
  isomorphism in degree 0 for some quasi-étale `G`-sheaves. Corollary
  1.5.2(i) is therefore not stated there. Supports are taken in the
  `L`-valued points, which are points of rank one. The Library's
  quasi-étale topology, Worker 21's `quasiEtaleTopology`, follows
  Berkovich's definition, and it has sheaves concentrated at points of
  higher rank. An example follows. Let `D` be the closed unit disc over
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
  quasi-étale or étale abelian sheaf `F` on `X(G)`. No Library statement
  uses it. The group `G = ℤ_p` of the example is compact, so compactness of
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
  Harris's sketch is. This gap is recorded with task `bd93b48c`.
- Only the split supercuspidal place is treated, as in Harris 1999. No
  nonsplit generalization is asserted, and the banality assumptions of
  Harris 1999 §6 are not added.

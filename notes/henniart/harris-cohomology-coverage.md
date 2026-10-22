# Harris–Berkovich cohomological framework: declaration coverage

This note maps the cohomological input to Harris's weak automorphic
induction, as used by Henniart, to Library declarations. It covers the task
"Formalize the Harris and Berkovich cohomological theorem-statement
framework" (task `b91b0934`, Worker 3). It also lists the parts that are not
yet stated and who owns their prerequisites. It is a map, not a theorem.
Every declaration below is a `Prop`-valued theorem-statement definition, or
an auxiliary construction used to state one. Two components are proved by
published Lean theorems of other workers (see
[Proved statements](#proved-statements)); the others are not.

Each module's paired Markdown gives its exact hypotheses, sources with
locators, and checks. The sources are registered as described in
[Registered originals and reading record](sources.md). The source analysis
of Harris 1999 is in
[Harris 1999 and the deferred general-coefficient argument](harris-1999.md).

Versions: Library commit `17cf41e0bda20d1d567ecfa556642ce7b92f79df`,
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).

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
| [`Langlands.Cohomology.OperatorSpace.Statement`](../../Langlands/Cohomology/OperatorSpace/Statement.md) | `OperatorSpaceCohomologyStatements` (8 components) | Equivariant sheaves on a space with operators: injectives, derived sections with group action, the comparison with group cohomology for acyclic sheaves, and for finite groups with invertible order the comparison with invariants; compact-support analogues (Tohoku V 5.1–5.2; Berkovich Cor. 1.5.2(i)). These are special consequences of the spectral sequences of Tohoku Thm. 5.2.1 and Berkovich Cor. 1.5.2(i); the spectral sequences themselves are not stated. |
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
canonical topology is Worker 164's
`Langlands.PadicField.TopologicalData.generalLinearSigmaCompactSpace`, applied
to `F.canonicalTopologicalData`. Total disconnectedness is not proved in the
Library.

## Published constructions of other workers

These are constructions with proofs, not theorem statements of this task.
They are used by the statements above, by the proofs of two of them, or by the
Galois-smoothness statement listed below.

| Module | Author | Objects |
| --- | --- | --- |
| [`Langlands.Sheaf.Equivariant.Godement.Complex`](../../Langlands/Sheaf/Equivariant/Godement/Complex.md) | Worker 61 | `Langlands.Sheaf.Equivariant.Godement.complexFunctor`, the equivariant Godement complex built from `zeroFunctor` and `coaugmentation` (`Godement.Zero`) by the iterated-cokernel construction, with its augmentation and the instance `zeroFunctor_additive` |
| [`Langlands.Cohomology.EquivariantDerivedSections`](../../Langlands/Cohomology/EquivariantDerivedSections.md) | Worker 13 | `globalDerived` and `compactDerived`, the right derived functors of global and compactly supported sections on equivariant module sheaves, with values in `Rep R G`; `globalDerivedIso` and `compactDerivedIso` compute them from injective resolutions |
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
| [`Langlands.Cohomology.SmoothGodementCohomology`](../../Langlands/Cohomology/SmoothGodementCohomology.md) | Worker 61 | `smoothGodementCompactCohomology`, the cohomology of compact sections of `Godement.smoothComplex`, as smooth representations, with `smoothGodementCompactCohomologyZeroIso`; invariant variants `smoothGodementInvariantCompactCohomology` |
| [`Langlands.Geometry.EtaleAutomorphism`](../../Langlands/Geometry/EtaleAutomorphism.md), [`Langlands.Cohomology.TranslationAction`](../../Langlands/Cohomology/TranslationAction.md), [`Langlands.Geometry.EtaleCohomologyAction`](../../Langlands/Geometry/EtaleCohomologyAction.md) | Worker 13 | Translation of étale sheaves by scheme automorphisms, and `EtaleCohomologyAction.cohomologyRep`, the representation of a group acting on a scheme by automorphisms on étale cohomology of an equivariant sheaf |
| [`Langlands.Cohomology.TranslationCoaction`](../../Langlands/Cohomology/TranslationCoaction.md), [`Langlands.Geometry.EtaleConstantCohomology`](../../Langlands/Geometry/EtaleConstantCohomology.md), [`Langlands.Geometry.EtaleGaloisAction`](../../Langlands/Geometry/EtaleGaloisAction.md) | Worker 13 | Actions on derived functors from structure maps into translates; `EtaleCohomologyAction.constantCohomologyRep`, the action on étale cohomology with constant coefficients; `EtaleGaloisAction.galoisCohomologyRep`, the action of `L ≃ₐ[K] L` on étale cohomology of the base change `X ×_{Spec K} Spec L` with constant coefficients |
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
| Berkovich §1.5, Cor. 1.5.2(i), compact support on the equivariant site | `EquivariantCompactSectionsDerivedStatement` (the isomorphisms `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)`); for finite `G`, `FiniteEquivariantCompactAcyclicGroupCohomologyStatement` (when higher compactly supported cohomology vanishes) and `FiniteEquivariantCompactSectionsInvariantsStatement` (when the order of `G` is invertible). The printed spectral sequence itself is not stated. |
| Berkovich Cor. 1.5.2(i), smoothness of the action on `H^q_c(X, b^*F)` and the comparison `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)` for a topological group | `SmoothCompactCohomologyStatements`; `SmoothCompactComparisonStatements` (ordinary-topological analogues) |
| Berkovich §1.5 (ii) and Prop. 1.5.1, exactness of `F ↦ C^m(F)` and softness of `b^*C^m(F)` | `SmoothGodementStatements` (ordinary-topological analogue) |
| Harris 1999 Lemma 2.2 and (2.3), pp.304–305: the resolution of Lemma 2.2 computes `H^q_c`; the Godement step of the proof of Berkovich Cor. 1.5.2(i) | `SmoothGodementComparisonStatements` (ordinary-topological analogue) |
| Harris 1999 p.306 and Prop. 4.10, p.311: `Ext` in smooth `L_ℓ[GJ]`-modules, `L_ℓ = L ⊗_ℚ ℚ_ℓ`; p.312, the higher `Ext` vanish | `SupercuspidalExtSemisimpleStatements` |
| Harris 1997 p.96: `GJ^0` has compact center, so `π_v` restricted to `GJ^0` is still supercuspidal | `CompactModCenterRestrictionStatement` |
| Bernstein–Zelevinsky 1976, 3.20, 3.21 (Harish-Chandra) and 3.26 | `GLSupercuspidalRestrictionStatements` |
| Harris 1999 §5, p.313: `λ`-adic representations of `Gal(F̄/F)` on étale cohomology; SGA 4 VII 5.7–5.8 | `GaloisCohomologySmoothStatement` (constant coefficients) |

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
| Application of `CompactModCenterRestrictionStatement` to Harris's `GJ^0`: that `GJ^0` is normal in `GJ` and that `Z(GJ) GJ^0` has finite index | The group `GJ`, the Drinfeld tower `M_N` and its components (Harris 1997 (A.8)) | Analytic spaces: task `18670997` |
| The geometric input `H^j_c(M_N) ≅ c-Ind_{GJ^0}^{GJ} H^j_c(R_N)` (Harris 1997 (A.8)) | The Drinfeld tower as analytic spaces with their group actions | Analytic spaces: task `18670997` |
| Smoothness of the group action on compactly supported cohomology for Berkovich's analytic étale sheaves (Harris 1997 Lemma 6(i); Berkovich Cor. 1.5.2(i)). The ordinary-topological analogue is stated in `SmoothCompactCohomology` | Berkovich's smooth equivariant étale sheaves (Definition 1.4.1, pp.7–8). The base is a `G`-space: an analytic space with a continuous action of a topological group `G` (§1.1, pp.1–2), whose points need not have open stabilizers. Smoothness is a condition on the sheaf `F`: for every quasi-étale `U → X` with `U` compact, the canonical action of the open subgroup `G_U ⊂ G` on `F(U)` is discrete. Equivalently (p.8), every local section has an open stabilizer after restriction to suitable distinguished neighborhoods. Also needed: the derived compact sections of such sheaves, as smooth representations. The Library has these objects only on topological spaces (`SmoothSheafCohomology`), and the analytic étale sites only at the affinoid level | Tasks `23471a9e` (Workers 13 and 61) and `18670997` |
| Smoothness of the Galois action on étale cohomology with non-constant coefficients, and on Shimura varieties with Harris's coefficient systems | Galois actions on étale cohomology of equivariant sheaves over base changes, and the Shimura schemes | Worker 13 (`EtaleCohomologyAction`); task `36881fec` (Worker 57) |
| Harris's spectral sequences themselves (Harris 1997 Lemma 6; Harris 1999 Prop. 4.4, (4.4.1), Prop. 4.10), and the application of `HyperextDegenerationStatement` to them | Convergent hyperext spectral sequences, which Mathlib does not have; the analytic spaces, uniformization and equivariant étale sites | Analytic sites: task `18670997`; Shimura geometry: task `36881fec` (Worker 57) |
| Unitary Shimura cohomology with general algebraic coefficients | Shimura varieties as schemes, level towers, Hecke and Galois actions on étale cohomology with coefficient systems. The Library has the coefficient sheaves (`Langlands.Shimura.Coefficients`) and the similitude representability statement, not the varieties | Task `36881fec` (Worker 57) |
| Split-supercuspidal local-global compatibility (Harris 1998 Thm 1.7; Harris 1999 Thm 5.7, 5.9, Cor. 5.10) | All of the above, and the automorphic and Galois objects | This task, after the prerequisites |
| Compatible Galois-family existence and multiplicity removal | Delegated | Task `bd93b48c` (Worker 41) |
| Proofs of the stated theorems | Each needs its own proof task; only two components are proved so far | Separate proof tasks |

The shared planning DAG records these as the nodes
`proof.harris-coefficient-spectral-sequence`,
`proof.harris-supercuspidal-local-global`,
`proof.harris-global-galois-existence` and
`proof.berkovich-equivariant-resolution`, with their dependencies. Published
statement modules are recorded as follows.

| DAG node | Module |
| --- | --- |
| `proof.harris-supercuspidal-ext-vanishing` | `SupercuspidalExt.Statement` |
| `proof.harris-supercuspidal-ext-charzero` | `SupercuspidalExtCharZero.Statement` |
| `proof.harris-smooth-compact-cohomology` | `SmoothCompactCohomology.Statement` |
| `proof.harris-smooth-compact-comparison` | `SmoothCompactComparison.Statement` |
| `proof.harris-smooth-godement-acyclicity` | `SmoothGodement.Statement` |
| `proof.harris-smooth-godement-comparison` | `SmoothGodementComparison.Statement` |
| `proof.harris-supercuspidal-ext-semisimple` | `SupercuspidalExtSemisimple.Statement` |
| `proof.harris-supercuspidal-restriction` | `SupercuspidalRestriction.Statement` |
| `proof.harris-etale-galois-smooth` | `EtaleGaloisSmooth.Statement` |

## Proved statements

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

No other statement listed above is proved in Lean. Three modules also prove
implications between statements, which prove none of the statements
themselves: `supercuspidalExtStatements_of_charZero`,
`supercuspidalExtCharZeroStatements_of_semisimple` and
`glSupercuspidalRestriction_of_compactModCenter`.

## Retained source gaps and scope decisions

- Berkovich's manuscript is unfinished (1995–1996). Its Corollary 1.5.2(i)
  spectral sequence `H^p(G, H^q_c) ⇒ H^{p+q}_c` fails for infinite discrete
  groups: take `G = ℤ` acting by translation on the discrete space `X = ℤ`,
  with the same nonzero stalk `M` at every point, permuted by `G`. The
  spectral sequence is not stated. Its special consequences are stated only
  for finite groups (`Cohomology/OperatorSpace/Statement.md`).
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

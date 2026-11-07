# Harris–Berkovich cohomological framework: declaration coverage

This note maps the cohomological input to Harris's weak automorphic
induction, as used by Henniart, to Library declarations. It covers the task
"Formalize the Harris and Berkovich cohomological theorem-statement
framework" (task `b91b0934`, Worker 3). It also lists the parts that are not
yet stated and who owns their prerequisites. It is a map, not a theorem.
Every declaration below is a `Prop`-valued theorem-statement definition, or
an auxiliary construction used to state one. Several components are proved
by published Lean theorems of other workers, five of them in the proof tasks
T1–T5 that this task published (see
[Proved statements](#proved-statements)); the others are not.

Each module's paired Markdown gives its exact hypotheses, sources with
locators, and checks. The originals of the Henniart audit, among them Harris
1998, Harris 1999 and Berkovich's manuscript, are described in
[Registered originals and reading record](sources.md). The other sources
named below, such as SGA 4 and Harris–Taylor 2001, are identified only in
the Markdown of the modules that cite them. The source analysis of Harris
1999 is in
[Harris 1999 and the deferred general-coefficient argument](harris-1999.md).

Versions: Library commit `2816ea5d81e2fb9b0512bd1d8dec2ad7797026fd`,
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
| [`Langlands.Cohomology.HarrisCMCohomology.Statement`](../../Langlands/Cohomology/HarrisCMCohomology/Statement.md) | `HarrisCMCohomology.HarrisCMCohomologyStatements` (2 components: `HarrisCMCohomology.HarrisCMCohomologyFiniteStatement` and `HarrisCMCohomology.HarrisCMGaloisCohomologySmoothStatement`) | For a small CM level `U`, Worker 57's geometric CM scheme `X̄_U = X_U ×_{Spec F} Spec F̄` and the `r`-th stage `B_r` of Worker 57's torsion coefficient system pulled back to `X̄_U`: every `H^d(X̄_U, B_r)` is finite, and Worker 57's action of `F̄ ≃ₐ[F] F̄` on it (`cmHarrisGeometricGaloisCohomologyAction`) is smooth for the Krull topology. All objects take a proof `q` of `CMRepresentabilityStatement` and further premises; `q`, `square`, `existence`, `geometry` and `hRigid` are unproved, and the Markdown lists published proofs of the other thirteen. Truth arguments: SGA 4 IX 2.3–2.4 and XIV Cor. 1.2 (finiteness); SGA 4 VII 5.7–5.8 (smoothness). Analogues, at one level and one torsion stage, of the finiteness used in the proof of Harris 1999 Prop. 4.10 (p.312), and of the continuity of the Galois action that Harris–Taylor 2001 III.2 (p.97) assert and that the `λ`-adic representations of Harris 1999 §5 (p.313) require. |
| [`Langlands.Cohomology.HarrisCMLevelGaloisSmooth.Statement`](../../Langlands/Cohomology/HarrisCMLevelGaloisSmooth/Statement.md) | `HarrisCMLevelGaloisSmooth.HarrisCMLevelGaloisSmoothStatement` | For a commutative ring `R`, the Library's `cmSmallLevelGaloisCohomologyFunctor` sends a sheaf `M` of `R`-modules on the small étale site of `Spec F` to the colimit, over all sufficiently small CM levels `U`, of `H^d(X̄_U, p_U^* M)`, where `p_U : X̄_U → Spec F` is the structure map. The statement: for every degree `d`, every `M` and every class of this colimit, some open subgroup of `F̄ ≃ₐ[F] F̄` (Krull topology) fixes the class under the Library's Galois action. There is no finiteness, torsion or characteristic hypothesis on `R`. The objects take `q` and eighteen further premises; `q`, `square`, `existence`, `geometry` and `hRigid` are unproved, and the Markdown lists published proofs of the other fourteen. Truth argument: SGA 4 VII 5.1 and Cor. 5.8 at each level. Analogue, for coefficients pulled back from `Spec F` and discrete modules, of the continuity of the Galois action on `H^i(X, L_ξ) = lim_{→U} H^i(X_U ×_F F^ac, L_ξ)` in Harris–Taylor 2001 III.2 (pp.96–97). |
| [`Langlands.Cohomology.HarrisCMLevelInvariants.Statement`](../../Langlands/Cohomology/HarrisCMLevelInvariants/Statement.md) | `HarrisCMLevelInvariants.HarrisCMLevelInvariantsStatement` | For a commutative ring `R`, a level-trivial coefficient diagram `coeff` of étale `R`-module sheaves on the geometric CM tower `U ↦ X̄_U`, and sufficiently small levels `V ≤ U` with `V` normal in `U`, such that the transition of `coeff` along `V ≤ U` is an isomorphism and the index `[U : V]` is a unit of `R`: in every degree `d`, restriction `H^d(X̄_U, coeff_U) → H^d(X̄_V, coeff_V)` is injective, and its image is the set of classes fixed by the maps of the level arrows `smallCMNormalInverseArrow D U V hVU g : V ⟶ V` (element `g⁻¹`) for all `g ∈ U`. The same premises as `HarrisCMLevelGaloisSmooth`. Truth argument: Worker 57's theorem that `X̄_V → X̄_U` is a finite étale `U/V`-torsor, and the trace of SGA 4 IX 5.1. Analogue of the comparison `H^i(X_U ×_F F^ac, L_ξ) ≅ H^i(X_V ×_F F^ac, L_ξ)^{U/V}` of Harris–Taylor 2001 III.2 (p.96). |
| [`Langlands.Cohomology.HarrisCMColimitInvariants.Statement`](../../Langlands/Cohomology/HarrisCMColimitInvariants/Statement.md) | `HarrisCMColimitInvariants.HarrisCMColimitInvariantsStatement` | For a `ℚ`-algebra `R` and a level-trivial coefficient diagram on the same tower all of whose transition maps are isomorphisms: at every small level `U` and in every degree `d`, the insertion of `H^d(X̄_U, coeff_U)` into the colimit over all small levels (`RestrictedLevelColimit.ι`) is injective, and its image is the set of classes fixed by `U` under the Library's smooth action of the finite-adelic group (`cmSmallLevelSmoothCohomology`). The same premises. Truth argument: derived from `HarrisCMLevelInvariantsStatement`. This is the step between the comparison of Harris–Taylor 2001 p.96 and the admissibility of `H^i(X, L_ξ)` that they assert on p.97. |

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
| [`Langlands.Shimura.PEL.HarrisTaylorCMGeometricCohomology`](../../Langlands/Shimura/PEL/HarrisTaylorCMGeometricCohomology.md), [`Langlands.Shimura.PEL.HarrisTaylorCMGeometricGaloisCohomology`](../../Langlands/Shimura/PEL/HarrisTaylorCMGeometricGaloisCohomology.md) | Worker 57 | In namespace `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`: `cmHarrisGeometricCoefficientCohomologySystem`, the étale cohomology `H^d(X̄_U, B_r)` as a functor of the coefficient stage `r`; `cmHarrisGeometricGaloisCohomologyAction`, the action of `F̄ ≃ₐ[F] F̄` on it, by pullback along the Galois automorphisms of `X̄_U` followed by the canonical coefficient isomorphisms. Both take a proof `q` of `CMRepresentabilityStatement` |
| [`Langlands.Geometry.EtaleDerivedSections`](../../Langlands/Geometry/EtaleDerivedSections.md) | Worker 13 | `EtaleDerivedSections.cohomology X R d`, the right derived functors of global sections on sheaves of `R`-modules on the small étale site of a scheme, computed with injective resolutions; the étale cohomology in all four `HarrisCM` statement modules |
| [`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelIndex`](../../Langlands/Shimura/PEL/HarrisTaylorCMSmallLevelIndex.md), [`Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoefficients`](../../Langlands/Shimura/PEL/HarrisTaylorCMGeometricCoefficients.md) | Worker 57 | `SmallCMLevel D`, the sufficiently small CM levels with their level arrows, and the preorder `OrderedSmallCMLevel D`; `cmGeometricSchemeTower`, the tower `U ↦ X̄_U` as a functor `SmallCMLevel D ⥤ Scheme`, which takes `q` |
| [`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelCohomology`](../../Langlands/Shimura/PEL/HarrisTaylorCMSmallLevelCohomology.md), [`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelGaloisCoefficients`](../../Langlands/Shimura/PEL/HarrisTaylorCMSmallLevelGaloisCoefficients.md) | No Author line | `cmSmallLevelTowerEtale` (the transition maps of the geometric tower are étale), coefficient diagrams `cmSmallLevelCoefficientDiagram`, level triviality `cmSmallLevelTrivialCoefficients`, the level cohomology `cmSmallLevelCohomology` and its colimit with the smooth finite-adelic action, `cmSmallLevelSmoothCohomology`; `cmSmallLevelGaloisCohomologyFunctor`, the colimit of `H^d(X̄_U, p_U^* M)` with the finite-adelic and Galois actions |
| [`Langlands.Shimura.PEL.HarrisTaylorCMHeckeSchemes`](../../Langlands/Shimura/PEL/HarrisTaylorCMHeckeSchemes.md), [`Langlands.Shimura.PEL.HarrisTaylorCMNormalActions`](../../Langlands/Shimura/PEL/HarrisTaylorCMNormalActions.md) | No Author line | The inclusion arrow `smallCMInclusion D hVU : V ⟶ U` (element `1`) and, for `V` normal in `U` and `g ∈ U`, the arrow `smallCMNormalInverseArrow D U V hVU g : V ⟶ V` (element `g⁻¹`) |
| [`Langlands.Geometry.EtaleCohomologyDiagram`](../../Langlands/Geometry/EtaleCohomologyDiagram.md), [`Langlands.Shimura.RestrictedLevelTowerCohomology`](../../Langlands/Shimura/RestrictedLevelTowerCohomology.md), [`Langlands.Shimura.RestrictedLevelColimit`](../../Langlands/Shimura/RestrictedLevelColimit.md) | No Author line | `CoefficientDiagram`, diagrams of étale sheaves over a tower of schemes; `IsLevelTrivialCoefficients`; colimits over levels satisfying a property, their insertions `RestrictedLevelColimit.ι` and the group actions on them |
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
| Berkovich §1.5, Cor. 1.5.2(i), compact support on the equivariant site | `EquivariantCompactSectionsDerivedStatement` (the isomorphisms `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)`); for finite `G`, `FiniteEquivariantCompactAcyclicGroupCohomologyStatement` (when higher compactly supported cohomology vanishes) and `FiniteEquivariantCompactSectionsInvariantsStatement` (when the order of `G` is invertible). The printed spectral sequence itself is not stated. |
| Berkovich Cor. 1.5.2(i), smoothness of the action on `H^q_c(X, b^*F)` and the comparison `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)` for a topological group | `SmoothCompactCohomologyStatements`; `SmoothCompactComparisonStatements` (ordinary-topological analogues) |
| Berkovich §1.5 (ii) and Prop. 1.5.1, exactness of `F ↦ C^m(F)` and softness of `b^*C^m(F)` | `SmoothGodementStatements` (ordinary-topological analogue) |
| Harris 1999 Lemma 2.2 and (2.3), pp.304–305: the resolution of Lemma 2.2 computes `H^q_c`; the Godement step of the proof of Berkovich Cor. 1.5.2(i) | `SmoothGodementComparisonStatements` (ordinary-topological analogue) |
| Harris 1999 p.306 and Prop. 4.10, p.311: `Ext` in smooth `L_ℓ[GJ]`-modules, `L_ℓ = L ⊗_ℚ ℚ_ℓ`; p.312, the higher `Ext` vanish | `SupercuspidalExtSemisimpleStatements` |
| Harris 1997 p.96: `GJ^0` has compact center, so `π_v` restricted to `GJ^0` is still supercuspidal | `CompactModCenterRestrictionStatement` |
| Bernstein–Zelevinsky 1976, 3.20, 3.21 (Harish-Chandra) and 3.26 | `GLSupercuspidalRestrictionStatements` |
| Harris 1999 §5, p.313: `λ`-adic representations of `Gal(F̄/F)` on étale cohomology; SGA 4 VII 5.7–5.8 | `GaloisCohomologySmoothStatement` (constant coefficients) |
| Harris 1999, proof of Prop. 4.10, p.312: "the right-hand side of the spectral sequence (4.9) is a finite group for all `m`"; SGA 4 XIV Cor. 1.2 | `HarrisCMCohomologyFiniteStatement` (analogue for Worker 57's geometric CM level `X̄_U` and torsion stage `B_r`; conditional on `q`) |
| Harris–Taylor 2001 III.2, p.97: the Galois action on Shimura cohomology with coefficient systems is continuous; Harris 1999 §5, p.313: `λ`-adic representations of `Gal(F̄/F)` on such cohomology; SGA 4 VII 5.7–5.8 | `HarrisCMGaloisCohomologySmoothStatement` (the same analogue, at one level and one torsion stage) |
| Harris–Taylor 2001 III.2, p.96: `H^i(X, L_ξ) = lim_{→U} H^i_et(X_U ×_F F^ac, L_ξ)` over sufficiently small levels; p.97: it is "an admissible/continuous `G(A^∞) × Gal(F^ac/F)`-module"; SGA 4 VII 5.1 and Cor. 5.8 (truth argument) | `HarrisCMLevelGaloisSmoothStatement` (the Galois continuity, for the colimit over all small CM levels, with coefficients pulled back from `Spec F` and discrete modules; conditional on `q`) |
| Harris–Taylor 2001 III.2, p.96: "If `V ⊂ U` then … `H^i_et(X_U ×_F F^ac, L_ξ) ≅ H^i_et(X_V ×_F F^ac, L_ξ)^{U/V}`"; SGA 4 IX 5.1, the trace (truth argument only) | `HarrisCMLevelInvariantsStatement` (finite level, `V` normal in `U`, `[U : V]` a unit of `R`); `HarrisCMColimitInvariantsStatement` (the colimit over all small levels, `ℚ`-algebra coefficients); both conditional on `q` |

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
| Smoothness of the Galois action on étale cohomology with non-constant coefficients in general, and on Shimura cohomology with `ℓ`-adic coefficients or with Harris's torsion coefficient systems after passing to the limit over levels. It is stated, conditionally on `CMRepresentabilityStatement`, for Worker 57's CM torsion coefficient system at one level and one stage (`HarrisCMCohomology`), and for the colimit over all small CM levels with coefficients pulled back from `Spec F` (`HarrisCMLevelGaloisSmooth`) | Galois actions on étale cohomology of equivariant sheaves over base changes, and the Shimura schemes. For Harris's CM torsion coefficient system the Galois actions exist only conditionally on `CMRepresentabilityStatement` (see the Shimura row below) | Worker 13 (`EtaleCohomologyAction`); task `36881fec` (Worker 57) |
| Harris's spectral sequences themselves (Harris 1997 Lemma 6; Harris 1999 Prop. 4.4, (4.4.1), Prop. 4.10), and the application of `HyperextDegenerationStatement` to them | Convergent hyperext spectral sequences, which Mathlib does not have; the analytic spaces, uniformization and equivariant étale sites | Analytic sites: task `18670997`; Shimura geometry: task `36881fec` (Worker 57) |
| Unitary Shimura cohomology with general algebraic coefficients | Shimura varieties as schemes, level towers, Hecke and Galois actions on étale cohomology with coefficient systems. The Library has the coefficient sheaves (`Langlands.Shimura.Coefficients`) and proves similitude representability (Worker 254's theorem `Langlands.Shimura.similitudeRepresentability`, module `Langlands.Shimura.Unitary.RepresentabilityProof`). In namespace `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`, the scheme level tower `cmSchemeTower` (module `HarrisTaylorCMSchemeLevels`), the scheme Hecke correspondences `cmHeckeLeft` and `cmHeckeRight` (`HarrisTaylorCMHeckeSchemes`) and Worker 57's Galois actions on the cohomology of the geometric CM torsion coefficient system, such as `cmHarrisGeometricGaloisCohomologyAction` (`HarrisTaylorCMGeometricGaloisCohomology`), all take a proof `q` of `CMRepresentabilityStatement` as an argument. That statement, the representability of Harris's PEL moduli problem, is not proved; its division-algebra case `DivisionCMRepresentabilityStatement` is the target of task `6eac742d`. Generic level-tower constructions (`Langlands.Shimura.LevelTowerCohomology`, `Langlands.Shimura.LevelTowerGalois`) exist. Library commits after `f73044d9` add the cohomology of level towers of schemes away from a fixed factor of the level (`Langlands.Shimura.SplitLevelTowerCohomology`, `Langlands.Shimura.RestrictedSplitLevelTowerCohomology`; no Author lines), applied there to the splitting of the finite adelic points at the places dividing an integer `m`, with Harris 1999 Prop. 4.10 (p.311) as motivation, and Worker 13's level spaces at such split levels (`Langlands.Shimura.SplitLevelSpace`, `Langlands.Shimura.Unitary.HarrisSplitTower`). No Library module applies them to the conditional CM schemes, and no statement of this task uses them. The cohomology statements about the conditional schemes are the two of `HarrisCMCohomology`, at one level and one torsion stage, and three across levels: Galois smoothness of the colimit (`HarrisCMLevelGaloisSmooth`), and the comparison of level-`U` cohomology with invariants at finite level (`HarrisCMLevelInvariants`) and in the colimit (`HarrisCMColimitInvariants`). Nothing is stated about Hecke operators on cohomology or for the `ℓ`-adic limit over the torsion stages | Task `36881fec` (Worker 57); task `6eac742d` |
| Split-supercuspidal local-global compatibility (Harris 1998 Thm 1.7; Harris 1999 Thm 5.7, 5.9, Cor. 5.10) | All of the above, and the automorphic and Galois objects | This task, after the prerequisites |
| Compatible Galois-family existence and multiplicity removal | Delegated | Task `bd93b48c` (Worker 41) |
| Proofs of the components not listed under [Proved statements](#proved-statements) | Each needs its own proof task | Separate proof tasks |

The shared planning DAG records these as the nodes
`proof.harris-coefficient-spectral-sequence`,
`proof.harris-supercuspidal-local-global`,
`proof.harris-global-galois-existence` and
`proof.berkovich-equivariant-resolution`, with their dependencies. At DAG
revision 2530 the published statement modules are recorded as follows. Module
names are relative to `Langlands.Cohomology`, except where a full name is
given.

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
| `proof.harris-cm-cohomology-finite-smooth` | `HarrisCMCohomology.Statement` |
| `proof.harris-cm-level-galois-smooth` | `HarrisCMLevelGaloisSmooth.Statement` |
| `proof.harris-cm-level-invariants` | `HarrisCMLevelInvariants.Statement` |
| `proof.harris-cm-colimit-invariants` | `HarrisCMColimitInvariants.Statement` |

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
`proof.harris-cm-exact-representability-target`, and
`proof.harris-supercuspidal-local-global` depends on it. The three nodes
added for the statements across levels also depend on
`def.harris-cm-conditional-scheme-tower` and
`proof.harris-cm-exact-representability-target`.
`proof.harris-cm-level-galois-smooth` further depends on
`def.restricted-level-colimit` and `def.restricted-level-canonical-galois`;
`proof.harris-cm-level-invariants` on `def.level-tower-cohomology`,
`def.harris-cm-normal-actions` and `def.harris-cm-normal-geometric-torsor`;
and `proof.harris-cm-colimit-invariants` on `def.level-tower-cohomology`,
`def.restricted-level-colimit` and `proof.harris-cm-level-invariants`. No
other node depends on any of the three.

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

No Library declaration has any of the following as its type. Each term below
was compiled by Worker 3 in a private `lean_check` in environment `3b864ddf`
at Library `2816ea5d` (check `d57a585d`); the files are not published. Names
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

No other component listed above is proved in Lean. In particular
`AcyclicResolutionEquivarianceStatement`, the isomorphism and naturality
components of `SmoothGodementComparisonStatements`, the second component of
`SmoothCompactCohomologyStatements`, `SupercuspidalExtSemisimpleStatements`,
both components of `HarrisCMCohomologyStatements`,
`HarrisCMLevelGaloisSmoothStatement`, `HarrisCMLevelInvariantsStatement` and
`HarrisCMColimitInvariantsStatement` are open. Three
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

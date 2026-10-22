# Harris–Berkovich cohomological framework: declaration coverage

This note maps the cohomological input to Harris's weak automorphic
induction, as used by Henniart, to Library declarations. It covers the task
"Formalize the Harris and Berkovich cohomological theorem-statement
framework" (task `b91b0934`, Worker 3). It also lists the parts that are not
yet stated and who owns their prerequisites. It is a map, not a theorem.
Every declaration below is a `Prop`-valued theorem-statement definition, or
an auxiliary construction used to state one. None of the theorems is proved
in Lean.

Each module's paired Markdown gives its exact hypotheses, sources with
locators, and checks. The sources are registered as described in
[Registered originals and reading record](sources.md). The source analysis
of Harris 1999 is in
[Harris 1999 and the deferred general-coefficient argument](harris-1999.md).

Versions: Library commit `b164b3aa3952e5f6000986e04be27b200c582796`,
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

All names in the second column are in the namespace `Langlands.Cohomology`,
except `Langlands.CompactCoefficientSplittingStatement`.

The equivariant Godement statements concern Worker 61's ordinary-topological
construction for a discrete group. They are analogues of Berkovich's
resolution, not statements about Berkovich's `ν_*ν^*` on the equivariant
topos, which has additional coinduction factors. The acyclicity that Harris
1999 p.304 displays for Berkovich's resolution is for compactly supported
cohomology, `H_c^q(U(ẽ)_{F̄}, F(T)) = 0` for `q > 0`; the compactly
supported part of the third component is its analogue.

The supercuspidal `Ext` statements have complex coefficients, as Harris 1997
allows after choosing `Q̄_ℓ ≅ ℂ` (p.95). Harris 1999 works over the `ℓ`-adic
field `L_ℓ`, which is not covered. No category of representations with a
fixed central character is introduced; as in Harris 1997, restriction to the
open subgroup `GJ^0` with compact center replaces it. The geometric input
`H^j_c(M_N) ≅ c-Ind_{GJ^0}^{GJ} H^j_c(R_N)` (Harris 1997 (A.8)) is not stated.

## Published constructions of other workers

These are constructions with proofs, not theorem statements of this task.
The first three are used by the statements above. The fourth bears on the
smoothness statement that is not yet made (see below).

| Module | Author | Objects |
| --- | --- | --- |
| [`Langlands.Sheaf.Equivariant.Godement.Complex`](../../Langlands/Sheaf/Equivariant/Godement/Complex.md) | Worker 61 | `Langlands.Sheaf.Equivariant.Godement.complexFunctor`, the equivariant Godement complex built from `zeroFunctor` and `coaugmentation` (`Godement.Zero`) by the iterated-cokernel construction, with its augmentation and the instance `zeroFunctor_additive` |
| [`Langlands.Cohomology.EquivariantDerivedSections`](../../Langlands/Cohomology/EquivariantDerivedSections.md) | Worker 13 | `globalDerived` and `compactDerived`, the right derived functors of global and compactly supported sections on equivariant module sheaves, with values in `Rep R G`; `globalDerivedIso` and `compactDerivedIso` compute them from injective resolutions |
| [`Langlands.Cohomology.SmoothExt`](../../Langlands/Cohomology/SmoothExt.md) | Worker 13 | `Langlands.Cohomology.SmoothExt.ext R G V n`, the right derived functors of `Hom(V, -)` on the abelian category `Langlands.SmoothRep R G`, which has enough injectives |
| [`Langlands.Sheaf.Equivariant.SmoothCompactSupport`](../../Langlands/Sheaf/Equivariant/SmoothCompactSupport.md) | Worker 13 | For a topological group, the smooth part of the representation on compactly supported global sections, as a functor to `Langlands.SmoothRep R G`. It is a degree-zero construction; no derived version exists yet |

The third component of `EquivariantGodementStatements` uses Mathlib's
`rightDerived` directly; by definition these are Worker 13's `globalDerived`
and `compactDerived`.

## Source items and their declarations

| Source item | Declarations |
| --- | --- |
| Harris 1999 §2 p.304: Berkovich's resolution `F(T)`, Fact 3 (exactness) | Ordinary-topological analogues: `EquivariantGodementStatements`; `GodementExactnessStatements` |
| Harris 1999 p.304, acyclicity of `F(T)` for compactly supported sections | Analogues: the compactly supported part of `EquivariantGodementComputesSectionsStatement`; `FlasqueGodementCohomologyStatements` (compactly supported, on topological spaces); with `OperatorSpaceCohomologyStatements` and `AcyclicResolutionComparisonStatements` for the comparison |
| Harris 1999 p.305, truncation and pro-`p` invariants | `ProPInvariantTruncationStatements` |
| Harris 1999 (2.6)–(2.7), passage to the limit over levels | `FilteredColimitComparisonStatements` |
| Harris 1999 Lemma 2.8 and Prop. 4.10, Mittag-Leffler passage to `ℓ`-adic coefficients | `InverseLimitComparisonStatements` (algebraic part) |
| Harris 1997 pp.95–96 and Harris 1999 p.312, supercuspidal splitting | `CompactCoefficientSplittingStatement` |
| Harris 1997 p.96, `Ext` Frobenius reciprocity for compact induction from `GJ^0`, injectivity and projectivity of supercuspidals, vanishing of higher `Ext`; Harris 1999 p.312, "the higher Ext's vanish" | `SupercuspidalExtStatements` (complex coefficients) |
| Harris 1997 (10) → (11) and Harris 1999 (4.10.1) → (5.2), degeneration once higher `Ext` vanish | `HyperextDegenerationStatement`; `SpectralSequenceConcentrationStatements` |
| Berkovich §1.5, Cor. 1.5.2(i), compact support on the equivariant site | `EquivariantCompactSectionsDerivedStatement` (the isomorphisms `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)`); for finite `G`, `FiniteEquivariantCompactAcyclicGroupCohomologyStatement` (when higher compactly supported cohomology vanishes) and `FiniteEquivariantCompactSectionsInvariantsStatement` (when the order of `G` is invertible). The printed spectral sequence itself is not stated. |

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
| Injectivity and projectivity of supercuspidals over the `ℓ`-adic field `L_ℓ` of Harris 1999 | A splitting statement for representations with compactly supported matrix coefficients over coefficient fields other than `ℂ`; the published `CompactCoefficientSplittingStatement` is over `ℂ` | This task; not yet started |
| The geometric input `H^j_c(M_N) ≅ c-Ind_{GJ^0}^{GJ} H^j_c(R_N)` (Harris 1997 (A.8)) | The Drinfeld tower as analytic spaces with their group actions | Analytic spaces: task `18670997` |
| Smoothness of the group action on compactly supported cohomology (Harris 1997 Lemma 6(i); Berkovich Cor. 1.5.2(i)) | Berkovich's smooth equivariant étale sheaves (Definition 1.4.1, pp.7–8). The base is a `G`-space: an analytic space with a continuous action of a topological group `G` (§1.1, pp.1–2), whose points need not have open stabilizers. Smoothness is a condition on the sheaf `F`: for every quasi-étale `U → X` with `U` compact, the canonical action of the open subgroup `G_U ⊂ G` on `F(U)` is discrete. Equivalently (p.8), every local section has an open stabilizer after restriction to suitable distinguished neighborhoods. Also needed: the derived compact sections of such sheaves, as smooth representations. The Library has only the degree-zero smooth part, `SmoothCompactSupport` | Task `23471a9e` (Workers 13 and 61) |
| Harris's spectral sequences themselves (Harris 1997 Lemma 6; Harris 1999 Prop. 4.4, (4.4.1), Prop. 4.10) | Convergent hyperext spectral sequences, which Mathlib does not have; the analytic spaces, uniformization and equivariant étale sites | Analytic sites: task `18670997`; Shimura geometry: task `36881fec` (Worker 57) |
| Unitary Shimura cohomology with general algebraic coefficients | Shimura varieties as schemes, level towers, Hecke and Galois actions on étale cohomology with coefficient systems. The Library has the coefficient sheaves (`Langlands.Shimura.Coefficients`) and the similitude representability statement, not the varieties | Task `36881fec` (Worker 57) |
| Split-supercuspidal local-global compatibility (Harris 1998 Thm 1.7; Harris 1999 Thm 5.7, 5.9, Cor. 5.10) | All of the above, and the automorphic and Galois objects | This task, after the prerequisites |
| Compatible Galois-family existence and multiplicity removal | Delegated | Task `bd93b48c` (Worker 41) |

The shared planning DAG records these as the nodes
`proof.harris-coefficient-spectral-sequence`,
`proof.harris-supercuspidal-local-global`,
`proof.harris-global-galois-existence` and
`proof.berkovich-equivariant-resolution`, with their dependencies. The node
`proof.harris-supercuspidal-ext-vanishing` records the published supercuspidal
`Ext` statements.

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

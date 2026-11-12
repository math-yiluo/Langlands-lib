# Renard III.3: actions on sheaves, coinvariants and homogeneous induction

This source map covers David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, III.3.1–III.3.2, printed
pp.83–85 / PDF pp.89–91. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original three pages were read directly. The main II.2.5 construction
and its original-module and compact-section stalk descriptions on printed
pp.38–42 / PDF pp.44–48 were also consulted.

Task 5297 (`20ef22af-8ead-4619-880a-cdf4fb65ba49`) constructs the III.3
interfaces and states the main assertions. Construction laws below are
proved as part of their definitions; a closed proposition target is an
unproved assertion, even after its statement is reviewed and published.
No main III.3 theorem proof is claimed by this note.

## Conventions, hypotheses and reused objects

Renard's t.d. space convention is the published
`Langlands.Topology.IsLocallyProfinite`: Hausdorff with a compact-open
neighbourhood basis. The actual supplied topology is used throughout.
The group acts jointly continuously in the source setting. Some elementary
construction interfaces need only continuity of each individual translation;
the main statements retain the source's locally profinite group and space
hypotheses. The transitive-space and homogeneous theorem targets retain
`SigmaCompactSpace G`, expressing countability at infinity. They do not
replace it by second countability. Singleton and III.3.1 assertions precede
that transitive hypothesis and do not impose it.

The vector sheaves are the existing ordinary Mathlib sheaves of complex
vector spaces. Action sheaves are the existing transport-category sheaves:
an arrow `U → V` carries its original label `g` and the condition
`g • U ⊆ V`; contravariant pullback uses the inverse coefficient operator.
Labels are retained when the base action is not faithful. Group actions,
ordinary restriction, all-open sections and stalks are these actual objects.
The isomorphisms on translated opens therefore obey the original action
laws, without a substitute action on a replacement sheaf.

`CompactSupport.submodule` means original global sections with compact
nonzero-germ support. `SectionActions.IsSmoothAction` requires smoothness of
the **whole** original compact-section representation. It does not replace
that space by its smooth vectors. This condition is compared with the
existing local `IsSmoothSheaf` by the published `LocalSmoothComparison`.
`Distribution` is the full algebraic complex dual of compact sections;
there is no topology on that dual and no smooth-dual restriction.

`PointwiseTestAlgebra.Carrier X` is Renard's pointwise test algebra `D(X)`,
not a convolution algebra. Nondegenerate module complex scalars are the
published canonical scalars on the original carrier. The action on tests
is the literal inverse pullback `g · f(x)=f(g⁻¹ • x)`.

The actual complex compact-support and inverse-image interfaces use
universe-zero base, coefficient and section carriers. The group universe
can be independent in `SectionActions`, singleton, compact-section action,
projector action and equivariant module statements. Induction sheaves and
actual invariant-fibre inverse images specialize the group to `Type` as
required by the current interfaces. These are explicit size constraints,
not claims of resizing or finite-dimensionality.

The prerequisite Task 5338
(`54fcba03-87f9-4b3a-ab99-618d2c683d74`) supplies the published
`CompactSectionTestModule`, `ProjectorVectorSheaf`,
`ProjectorVectorSheafSections`, `SheafProjectorComparison`,
`ModuleProjectorComparison` and compact-section/stalk proposition targets.
They refine the earlier actual scalar/projector/basis sheaves. III.3 imports
these by Lean name and assumes no II.2.5 comparison isomorphism when
constructing its own functors. See also
[the II.2 scalar/projector map](scalar-projector-progress.md) and
[the II.2 germ and compact-section map](germ-sheaf-progress.md).

For compact notation below, `SA` means the full prefix
`Langlands.Sheaf.Renard.SectionActions`, `HS` means
`Langlands.Sheaf.Renard.HomogeneousSections`, and other module prefixes have
the same `Langlands.Sheaf.Renard` root unless written in full.
`Equivariant` abbreviates `Langlands.Sheaf.Equivariant`, and the ordinary
compact-support and compact-germ modules are under `Langlands.Sheaf`.

## III.3.1: actions and compatible modules, printed p.83 / PDF p.89

| Source assertion | Exact formal objects or target | Status and meaning |
| --- | --- | --- |
| Moving-base sheaf isomorphisms, identity and product laws, continuous underlying action | `SA.ActionSheaf`, `SA.gamma`, `SA.globalRepresentation`, `SA.global_one`, `SA.global_mul`; existing `Equivariant.ActionOpens` and `translateSections` | Construction on the original transport sheaf, specialized to the source's jointly continuous base action. |
| Representation on all compactly supported global sections | `SA.compactRepresentation` | The existing `Equivariant.CompactSections.representation`, retaining every original compact section. |
| Nondegenerate test module with compatible linear group action | `CompatibleTestActions.testRepresentation`, `CompatibleTestActions.CompatibleTestAction` and its existing morphisms | Construction on the original pointwise tests and nondegenerate modules, with literal covariance. |
| Forward compact-section correspondence | `CompactSectionActions.functor`, `CompactSectionActions.forgetIso` | Actual published ordinary compact-section module and original group operators; covariance proved on original germs. |
| Reconstruction of the action on the original inverse vector sheaf | `ProjectorActionSheaf.functor`, `ProjectorActionSheaf.forgetIso` | Actual published projector-family sheaf. At a labelled `g` arrow, a component at `W` reads the original family at `g W` and applies `M.action g⁻¹`. |
| The two correspondences identify the categories | `EquivariantModuleStatements.AlgebraicStatement` | Unproved closed target: an actual equivalence with forward functor exactly the compact-section functor and inverse exactly the reconstructed projector-action-sheaf functor. |
| Smooth action | `SA.IsSmoothAction`, `CompactSectionActions.smoothProperty` | Smoothness on the entire original compact-section/module representation. |
| Restriction of the correspondence to smooth actions | `CompactSectionActions.smoothFunctor`, `SmoothProjectorActionSheaf.smoothFunctor`, `EquivariantModuleStatements.SmoothStatement` | Both functors are constructed. The category equivalence is an unproved target. Reconstruction smoothness is obtained from original-vector local representatives and original stabilizers, not an assumed module comparison. |
| Invariant distributions | `SA.Distribution`, `SA.IsInvariantDistribution`, `SA.invariantDistributions` | Existing compact-section algebraic dual and literal invariance on every original translated section. |

`ProjectorActionSheaf` does not rebuild II.2.5. Its ordinary underlying
sheaf comparison has identity maps on the published compatible families;
its morphisms are the existing original module maps applied componentwise.
`SmoothProjectorActionSheaf` proves local smoothness by representing a
local section on a compact open by its own original module component.
That vector's open stabilizer fixes its original-vector global section.
Published stable-neighbourhood and local-to-compact results then give
smoothness of all original compact sections.

## III.3.1: the invariant map and coinvariant sheaf, printed pp.83–84 / PDF pp.89–90

| Source assertion | Exact formal objects or target | Status and meaning |
| --- | --- | --- |
| Continuous invariant `q : X → Y` gives a target-test action on original compact sections | `CoinvariantTestModule.pullback`, `CoinvariantTestModule.sourceFunctor`, applied after `CompactSectionActions.functor` | Construction by full locally constant pullback multipliers. No compact-support claim for the pullback of a test on `Y`. |
| The span of group-action differences is stable under target tests | `CoinvariantTestModule.multiplier_preserves_ker`, `CoinvariantTestModule.quotientMultiplier`, `CoinvariantTestModule.quotientMultiplier_mk` | Intrinsic laws for the literal existing `Representation.Coinvariants` kernel and quotient. |
| The target-test quotient module is nondegenerate and natural | `CoinvariantTestModule.object`, `CoinvariantTestModule.functor`, `CoinvariantTestModule.quotient` | Construction on the original coinvariant quotient and original induced maps. |
| The sheaf `F′` corresponding to that module | `CoinvariantSheaf.functor`, `CoinvariantSheaf.functor_obj` | Actual `ProjectorVectorSheaf.functor` on that original nondegenerate target-test module. |
| `F_c(X)_G ≅ F′_c(Y)` as target-test modules | `CoinvariantSheaf.compactComparison`, `CoinvariantStatements.CompactComparisonStatement` | The particular natural comparison is constructed from the published original-module comparison. Its invertibility is an unproved target. |
| Natural quotient from original compact sections to `F′_c(Y)` | `CoinvariantSheaf.quotient`, `CoinvariantSheaf.compactQuotient`, `CoinvariantSheaf.compactQuotient_action` | Literal quotient followed by that comparison; all original group-action differences map to zero. |
| Actual invariant fibre `Z=q⁻¹{y}` is closed | `InvariantFibres.Fibre`, `InvariantFibres.fibreAction`, `InvariantFibres.fibreContinuousSMul`, `InvariantFibres.fibre_closed`, `InvariantFibres.fibre_isLocallyProfinite` | Literal subtype with the original subspace topology and inherited action. Hausdorffness and compact-open basis are retained, including empty fibres. |
| Restriction of the sheaf and compact fibre representation | `InvariantFibres.restriction`, `InvariantFibres.restrictionToSheafIso`, `InvariantFibres.compactSections`, `InvariantFibres.coinvariants` | Actual equivariant inverse image, its ordinary comparison, all original compact sections and original representation coinvariants. |
| Proposition: `F′_y ≅ F_c(q⁻¹{y})_G`, naturally | `CoinvariantStatements.FibreCoinvariantStatement` | Unproved closed target: a natural isomorphism in the original action sheaf between the original neighbourhood-colimit stalk of `F′` and the actual compact-fibre coinvariant functor. No substitute stalk or supplied isomorphism. |
| Corollary: no invariant fibre distributions implies no invariant ambient distributions | `CoinvariantStatements.NoInvariantDistributionsStatement` | Unproved closed target on the full original algebraic duals, with no smoothness assumption. |

The Proposition's proof uses these additional assertions: compact
restriction to the closed fibre is surjective; its kernel is the span of
pulled-back target tests vanishing at `y`; the two quotient operations
identify the sum of that kernel and the action-difference space; and the
II.2.5 original-stalk test quotient identifies the final quotient with
`F′_y`. They are proof obligations of the Proposition, not hypotheses
silently added to its statement. The prerequisite original compact-germ
and stalk-quotient interfaces are in `CompactGerms`,
`CompactSectionStalks` and `CompactSectionStalksStatement`.

The printed Corollary proof invokes restriction of an arbitrary algebraic
distribution to a point stalk. Such a general restriction is not supplied
by the formalization: Haar integration on locally constant functions of a
nondiscrete compact profinite group need not annihilate functions vanishing
near a chosen point. The stated Corollary can instead be proved through
the Proposition: zero duals of fibre coinvariants force those vector
spaces to vanish, hence all original stalks of `F′` vanish; sheaf
separation and the canonical compact comparison then force the global
coinvariant dual to vanish. This is a proposed proof route, not a proved
reduction or a claim that the source Corollary is false.

## III.3.2: categories and restriction, printed p.84 / PDF p.90

| Source assertion | Exact formal objects or target | Status and meaning |
| --- | --- | --- |
| Category for a fixed continuous base action and equivariant sheaf maps | `SA.SmoothActionSheaf`, `SA.smoothActionInclusion` | Existing action sheaves, with the full compact-section smoothness property. |
| The singleton category is the smooth representation category | `SA.SingletonSheaves.functor`, `SA.SingletonSheaves.unit`, `SA.SingletonSheaves.counit`, `SingletonEquivalence.Statement` | Actual coefficient sheaf, original local-section unit and literal coefficient-evaluation counit are constructed. Their invertibility, both triangle laws and equivalence of these exact functors are an unproved target. |
| Compact-section functor to smooth representations | `SA.gammaC`, `SA.gammaCToRepIso`, `SA.gammaC_representation`, `SA.gammaC_map` | All original compact sections and original induced maps; smoothness proof does not change the carrier. |
| Restriction to a closed subgroup and invariant locally closed subspace | `SA.subgroupRestriction`, `SA.subgroupSpaceRestriction`, `SA.smoothSubgroupRestriction`, `SA.smoothSubgroupSpaceRestriction` | Actual subgroup action and transport-site inverse image; smoothness on the whole compact-section representation is proved for the actual inverse image. The construction permits continuous equivariant maps, hence includes the source's locally closed inclusions. |
| Ordinary sheaf restriction convention | `SA.InverseImageComparison.toSheafIso`, `SA.InverseImageStalks.stalkIso` | The actual transport Kan/sheafification inverse image is compared with ordinary inverse image, and the actual unit induces the original-stalk isomorphism. |
| Singleton restriction is the smooth stabilizer representation on the original stalk | `SA.smoothFixedStalkFunctor`, `SA.PointRestrictionComparison.smoothIso` | Whole original stalk is smooth via the compact-germ surjection; the natural comparison identifies it with actual singleton restriction followed by compact sections. |
| Transitive space `X ≅ G/H` for `G` countable at infinity | `Langlands.Topology.RenardOrbitQuotient.TransitiveQuotientHomeomorphismStatement` | Existing unproved standard-quotient target with the actual stabilizer and canonical representative formula, retaining `SigmaCompactSpace G`. No duplicate standard target is introduced. |
| Convention change to inverse-right `H\G` | `Langlands.Induction.quotientInversion`, `HS.homogeneousAction`, `HS.smul_quotientMap`, `HomogeneousOrbitMap.map`, `HomogeneousOrbitMap.map_factor`, `HomogeneousOrbitMap.map_equivariant` | Original inversion homeomorphism and action `g₀ • Hg=H(g g₀⁻¹)`. The canonical inverse-right orbit map is `Hg ↦ g⁻¹ • x`, factoring through the standard stabilizer map. |
| Original quotient topology, stabilizer and point restriction | `HS.quotient_isLocallyProfinite`, `HS.origin`, `HS.subgroup_fixes_origin`, `HS.pointRestriction` | The actual closed-subgroup quotient retains Hausdorffness and a compact-open basis, and point restriction is the original smooth identity-coset stalk. |

`HomogeneousOrbitMap.transitiveEquiv` is a set equivalence. Its definition
does not assert inverse continuity. The topological conclusion still uses
the existing sigma-compact transitive quotient target and the actual
inversion homeomorphism. `HomogeneousOrbitMap.pullback` and
`smoothPullback` are the actual inverse-image functors along that canonical
continuous map, without assuming a homeomorphism.

## III.3.2: induction and the theorem, printed pp.84–85 / PDF pp.90–91

| Source assertion | Exact formal objects or target | Status and meaning |
| --- | --- | --- |
| Compact induction is a nondegenerate pointwise `D(H\G)`-module | `CompactInductionTestModule.multiplier`, `testModule`, `testModule_nondegenerate`, `canonicalAction`, `compatibleObject`, `functor` | Original `CompactFunctions`, original pointwise multipliers, original right translations and original induced maps. A vector's own compact-clopen projected support gives its characteristic fixer. Canonical complex scalars agree with the original ones. |
| Induction sheaf `F^τ` and functor `I_H^G` | `InductionSheaf.compatibleInduction`, `InductionSheaf.functor`, `InductionSheaf.toActionIso`, `InductionSheaf.underlyingSheafIso` | Original compact-induced compatible module followed by actual smooth projector-action-sheaf reconstruction. The ordinary sheaf is exactly the published projector sheaf. |
| The induction sheaf's identity-coset fibre is the original H-representation | `HomogeneousEquivalence.OriginStalkStatement` | Unproved natural original-representation identification with actual original-stalk point restriction. No particular evaluation-on-representatives formula is claimed by this target. |
| For arbitrary smooth action sheaf, compact sections equal compact induction from the identity-coset stalk | `HS.alphaCompact`, `HS.alphaCompact_apply`, `HomogeneousSectionStatements.CompactAlphaBetaStatement` | The literal forward alpha is constructed. The target requires a natural equivariant inverse beta, both inverse laws and the exact original-stalk beta formula. |
| The smooth part of all global sections equals smooth induction | `HS.alphaSmoothGlobal`, `HS.alphaSmoothGlobal_apply`, `HomogeneousSectionStatements.SmoothGlobalAlphaBetaStatement` | Actual `smoothPart` and original induced functions; the analogous exact inverse and naturality are required as conclusions. |
| Displayed alpha formula | `HS.alphaFunction`, `HS.alphaGlobal`, `HS.alphaCompact`, `HS.alphaSmoothGlobal` | Literally `alpha(s)(g)=germ_o(g • s)` on the original section and original stalk. |
| Displayed beta formula | The two `HomogeneousSectionStatements` beta targets | Output beta maps must return actual original sections with `germ_(g • o)(beta(f))=gamma_g(f(g⁻¹))`, where `g • o=H g⁻¹`. `gamma_g` is the original labelled stalk transport. Descent, local representability, support and both inverse laws are conclusions, not supplied certificates. |
| Naturality | `HS.alphaFunction_naturality`, `HS.alphaCompact_naturality`, `HS.alphaSmoothGlobal_naturality`, and the two beta targets | Forward naturality is proved on the original sheaf/stalk/induced maps. The inverse families must satisfy the actual corresponding commutative equations. |
| Theorem: induction and point restriction are mutually inverse category equivalences | `HomogeneousEquivalence.Statement` | Unproved closed target: an actual category equivalence with forward functor exactly `InductionSheaf.functor` and inverse exactly `HS.pointRestriction`, including objects and morphisms. |

For the inverse-right convention, the beta right-hand side is precisely
`Godement.stalkPull` with label `g⁻¹`, from the original stalk at `o` to
the original stalk at `g • o`; the point equation is
`g⁻¹ • (g • o)=o`. The explicit beta data are theorem conclusions of the
closed targets, not separately assumed inverse constructions. Their
proof tasks must construct these actual sections. The alpha constructions
already include covariance, the original uniform stabilizers and exact
projected-support comparison.

The induction-sheaf construction is on the literal homogeneous quotient
and does not use a transitive-space identification. Its elementary
construction needs no sigma-compactness; the main section and homogeneous
equivalence targets nevertheless retain the source's countability at
infinity. The existing spatial induction restricted to open subgroups is
not substituted for induction from an arbitrary closed `H`.

III.4's opening bibliographic paragraph, printed p.85 / PDF p.91, attributes
the equivariant-sheaf section to reference [5]. It adds no III.3
mathematical assertion.

## Publication and proof boundary

Construction modules and closed statement modules are separate reviewed
units. The selected aggregate statement entries retain their individual
full target names for focused proof tasks. Compilation, semantic approval
of a statement and its publication do not prove that statement. The main
remaining proofs are the actual equivariant module equivalences, canonical
coinvariant compact comparison, natural fibre Proposition, distribution
Corollary, singleton equivalence, literal compact and smooth-global
alpha–beta comparisons, and the homogeneous category equivalence.
The standard transitive quotient and II.2.5 prerequisite statements remain
with their existing owners.

The main closed target modules are `EquivariantModuleStatements`,
`CoinvariantStatements`, `HomogeneousSectionStatements`,
`SingletonEquivalenceStatement` and `HomogeneousEquivalenceStatement`. They
are submitted as separate mathematical statement units, with exact
proposition inspections. Their independent acceptance and Library
publication are tracked by Task 5297 separately from this note; this
source map does not establish any of the target propositions. Focused
proof successors may be published only after their exact targets are in
the Library.

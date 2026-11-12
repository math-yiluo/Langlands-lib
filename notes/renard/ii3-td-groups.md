# Renard II.3: t.d. groups, Haar distributions and the completed Hecke algebra

Worker 152, Task 5298 (`891f2a21-5ffc-4189-aa08-d5d7a22b9429`),
11 November 2026. This map covers II.3.1–II.3.13 of David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, printed pp.43–56 / PDF pp.49–62. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF page numbers are printed page numbers plus six. The fourteen source pages
were read. The preceding II.2 paragraph on p.43 and the II.4 notes on p.56
are outside this section.

The mathematical correspondence and original proof-status inventory were
inspected at Library snapshot `0ef479821d752edef9ef540203ddfb7f637bbce6`.
Final publication verification uses
`2c8da0356d4c25c4ee22a9d7c15cae7a7f55cf26`: all twenty-one definition/statement
pairs from this task, including the two existential warning statements, are
accepted and published, and their file hashes match the accepted bundles.
Publication of a proposition definition establishes its statement, not its
truth. This task supplies statement coverage; the fifteen published proof
successor tasks listed at the end retain the proofs of the new assertions.

## Reading the declarations and statuses

In the tables, a prefix followed by a declaration name denotes the full Lean
name obtained from this key. Module links lead to the paired explanations;
replace `.md` with `.lean` to inspect the code.

| Prefix | Full namespace and module |
| --- | --- |
| `FA` | `Langlands.FunctionAction`, [FunctionAction](../../Langlands/Representation/FunctionAction.md) |
| `GA` | `Langlands.HarmonicAnalysis.GroupAction`, [GroupAction](../../Langlands/HarmonicAnalysis/GroupAction.md) |
| `GF` | `Langlands.HarmonicAnalysis.GroupFunctionSpaces`, [GroupFunctionSpaces](../../Langlands/HarmonicAnalysis/GroupFunctionSpaces.md) |
| `D` | `Langlands.HarmonicAnalysis.Distribution`; [Basic](../../Langlands/HarmonicAnalysis/Distribution/Basic.md), [TopologicalSupport](../../Langlands/HarmonicAnalysis/Distribution/TopologicalSupport.md), [Haar](../../Langlands/HarmonicAnalysis/Distribution/Haar.md), [Convolution](../../Langlands/HarmonicAnalysis/Distribution/Convolution.md), [CompactSubgroup](../../Langlands/HarmonicAnalysis/Distribution/CompactSubgroup.md), [HeckeRealization](../../Langlands/HarmonicAnalysis/Distribution/HeckeRealization.md) |
| `RQ` | `Langlands.Topology.RenardOrbitQuotient`, [RenardOrbitQuotientStatements](../../Langlands/Topology/RenardOrbitQuotientStatements.md) |
| `FS` / `FP` | `Langlands.Topology.RenardGroupFinitenessStatements` / `Langlands.Topology.RenardGroupFinitenessProof`, [statement](../../Langlands/Topology/RenardGroupFinitenessStatements.md) and [proof](../../Langlands/Topology/RenardGroupFinitenessProof.md) |
| `TD` | `Langlands.Hecke.RenardTestDecomposition`, [RenardTestDecompositionStatements](../../Langlands/Representation/Hecke/RenardTestDecompositionStatements.md) |
| `RH` | `Langlands.HarmonicAnalysis.Distribution.RenardHaar`, [RenardHaarStatements](../../Langlands/HarmonicAnalysis/Distribution/RenardHaarStatements.md) |
| `RM` | `Langlands.HarmonicAnalysis.Distribution.RenardModular`, [RenardModularStatements](../../Langlands/HarmonicAnalysis/Distribution/RenardModularStatements.md) |
| `RC` | `Langlands.HarmonicAnalysis.Distribution.RenardConvolution`, [RenardConvolutionStatements](../../Langlands/HarmonicAnalysis/Distribution/RenardConvolutionStatements.md) |
| `RU` | `Langlands.HarmonicAnalysis.Distribution.RenardUniformDensity`, [RenardUniformDensityStatements](../../Langlands/HarmonicAnalysis/Distribution/RenardUniformDensityStatements.md) |
| `RK` | `Langlands.HarmonicAnalysis.Distribution.RenardCompactSubgroup`, [RenardCompactSubgroupStatements](../../Langlands/HarmonicAnalysis/Distribution/RenardCompactSubgroupStatements.md) |
| `HE` | `Langlands.HarmonicAnalysis.Distribution.RenardHecke`, [RenardHeckeStatements](../../Langlands/HarmonicAnalysis/Distribution/RenardHeckeStatements.md) |
| `HF` | `Langlands.HarmonicAnalysis.HomogeneousFunctions`, [HomogeneousFunctions](../../Langlands/HarmonicAnalysis/HomogeneousFunctions.md) |
| `HR` | `Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard`, [RenardHomogeneousStatements](../../Langlands/HarmonicAnalysis/RenardHomogeneousStatements.md) |
| `FH` | `Langlands.HarmonicAnalysis.Distribution.RenardFullHecke`, [RenardFullHeckeStatements](../../Langlands/HarmonicAnalysis/Distribution/RenardFullHeckeStatements.md) |
| `EP` | `Langlands.HarmonicAnalysis.Distribution.RenardEssentialProducts`, [RenardEssentialProductsStatements](../../Langlands/HarmonicAnalysis/Distribution/RenardEssentialProductsStatements.md) |
| `CO` | `Langlands.HarmonicAnalysis.Distribution.RenardCompletion`, [RenardCompletionStatements](../../Langlands/HarmonicAnalysis/Distribution/RenardCompletionStatements.md) |
| `CZ` | `Langlands.HarmonicAnalysis.Distribution.RenardCenter`, [RenardCenterStatements](../../Langlands/HarmonicAnalysis/Distribution/RenardCenterStatements.md) |
| `HT` / `HA` | `Langlands.Hecke.TestFunction` / `Langlands.Hecke.HeckeAlgebra`; [TestFunction](../../Langlands/Representation/Hecke/TestFunction.md), [Convolution](../../Langlands/Representation/Hecke/Convolution.md), [NormalizedIndicator](../../Langlands/Representation/Hecke/NormalizedIndicator.md), [Corner](../../Langlands/Representation/Hecke/Corner.md), [DoubleCosetSandwich](../../Langlands/Representation/Hecke/DoubleCosetSandwich.md) |

**Defined** means the published object and its specified value formulas exist.
**Proved** names a published theorem. **Reuse** gives an explicit application
or composition of published theorems, without claiming a separately published
Renard theorem. **Statement** means a published, unproved `Prop`-valued
`def`/`abbrev`. Each of the thirteen original statement namespaces above has an
aggregate `Statements`; the individual names below identify its conjuncts or
exact specifications. The two supplementary warning statements are standalone
targets. No new proof is established by this note.

## Conventions and source corrections

Renard's t.d. spaces are Hausdorff spaces with a compact open neighborhood
basis. The existing `Langlands.Topology.IsLocallyProfinite` is exactly that
predicate. The published theorem
`Langlands.Topology.isLocallyProfinite_iff_mathlib` identifies it with
`T2Space`, `LocallyCompactSpace` and `TotallyDisconnectedSpace` together.
Thus the two forms of the hypotheses in the targets have the same scope.
The distribution targets impose no second countability hypothesis; only the
source assertions about groups countable at infinity use `SigmaCompactSpace`.

The four source spaces are the existing `LocallyConstant G ℂ`,
`Langlands.HarmonicAnalysis.SchwartzBruhat G`,
`Langlands.HarmonicAnalysis.Distribution G` and `D.compactlySupported`.
The distribution space is the **full complex algebraic dual** of the test
space, with topological support defined by actual open restrictions.
An invariant algebraic distribution is not assumed to be a measure.

The right point action is `x ↦ x*g⁻¹`; the induced action on functions is
`f(x) ↦ f(x*g)`. Source inversion is complex linear and has no complex
conjugation. Topological automorphisms use the actual `ContinuousMulEquiv`
(`G ≃ₜ* G`) so that they preserve the test space.

Renard's modular character is the reciprocal of Mathlib's:
`D.renardModular g = MeasureTheory.Measure.modularCharacter g⁻¹`, proved also
as `D.renardModular_eq_inv`. Likewise
`D.renardAutomorphismModule σ = (MeasureTheory.mulEquivHaarChar σ)⁻¹`.
These are adapters on the existing characters, not alternative Haar theories.

Two literal source claims need hypotheses. The open-orbit existence assertion
of II.3.3 requires `Nonempty X`: the empty space has finitely many orbits but
no open orbit. The target retains that necessary hypothesis only in the
existence clause. The Dirac exclusion and nonunitality statements on p.52
require nondiscreteness. The published corrected targets give the exact
criteria: Dirac membership in the Haar test-density range, and existence of
a two-sided Hecke identity, each hold if and only if `DiscreteTopology G`.
For a discrete group, a singleton indicator divided by its positive Haar mass
realizes the corresponding Dirac, and the identity-point density is a unit.
These criteria are statements awaiting proof, not new proved classifications.

## II.3.1–II.3.4: actions, finiteness and quotients

| Source assertion | Printed / PDF | Exact correspondence | Status |
| --- | --- | --- | --- |
| II.3.1 inverse pullback on a stable space of functions | 43 / 49 | `FA.functionRepresentation`, `FA.IsStable`, `FA.stableFunctionRepresentation`; `FA.functionRepresentation_apply`, `FA.stableFunctionRepresentation_apply` give `f(g⁻¹ • x)` | Defined; value and subtype intertwining formulas proved |
| II.3.1 action on a space paired with the function space | 43 / 49 | `FA.dualRepresentation`, `FA.pairedRepresentation`, `FA.pairedRepresentation_pairing`, `FA.pairedRepresentation_unique` | Defined/proved with an injective actual pairing map and invariant range; these make explicit the separation and stability needed to obtain an action on that carrier |
| II.3.1 automorphisms and inner automorphisms | 43 / 49 | `GA.automorphismFunctions`, `GA.innerFunctions`, `GA.innerFunctions_eq_automorphism`; `GA.continuousAutomorphismTests`, `GA.continuousAutomorphismDistributions` for tests and distributions | Defined; exact pullback and pushforward bridges proved |
| II.3.1 left and right point actions and induced functional actions | 43 / 49 | `GA.leftPermutations`, `GA.rightPermutations`, `GA.leftHomeomorphisms`, `GA.rightHomeomorphisms`; `GA.leftFunctions`, `GA.rightFunctions`, `GA.leftTests`, `GA.rightTests`, `GA.leftDistributions`, `GA.rightDistributions` | Defined/proved; the `*_apply`, `*_eq_pushforward` and `*_eq_*Translate` formulas fix the inverse parameters |
| II.3.1 inversion on functions, tests and their dual | 43 / 49 | `GA.inversionFunctions`, `GA.inversionTests`, `GA.inversionDistributions`; `GA.coe_inversionTests`, `GA.inversionDistributions_apply`, `GA.inversionTests_inversionTests`, `GA.inversionDistributions_inversionDistributions` | Defined/proved; translation-exchange formulas are also proved in that module |
| II.3.2 Lemma (i), nested compact open subgroups have finite relative index | 43 / 49 | `FS.RelativeQuotientFinite`, proved by `FP.relativeQuotientFinite` on the actual quotient `K1 ⧸ K.subgroupOf K1` | Proved |
| II.3.2 Lemma (ii), `G/K` is discrete | 43 / 49 | `FS.QuotientDiscrete`, proved by `FP.quotientDiscrete` using `QuotientGroup.discreteTopology` | Proved |
| II.3.2 Lemma (ii), countability when `G` is countable at infinity | 43 / 49 | `FS.QuotientCountable`, proved by `FP.quotientCountable`; `SigmaCompactSpace G` gives a Lindelöf quotient, and discreteness gives countability | Proved; `FP.assertions` proves the aggregate `FS.Assertions` |
| II.3.3 continuous left-action convention | 44 / 50 | Mathlib `MulAction G X` with joint `ContinuousSMul G X` | Defined; used literally in all `RQ` targets |
| II.3.3 Proposition, an open orbit and open orbit maps | 44 / 50 | `RQ.FiniteOrbitOpenOrbitStatement` | Statement, Task 5390; `Nonempty X` is explicit. The maps to the ambient `X` are open because the chosen orbit is open |
| II.3.3 Proposition, every orbit is locally closed | 44 / 50 | `RQ.FiniteOrbitsLocallyClosedStatement` | Statement, Task 5390; existing `Langlands.Topology.finiteOrbitOrdering` and `Langlands.Topology.FiniteOrbitProof.exists_relOpen_orbit` are proof inputs |
| II.3.3 orbit quotient, quotient topology and continuous projection | 44 / 50 | `Quotient (MulAction.orbitRel G X)`, `Quotient.mk`; Mathlib's coinduced quotient topology and `isQuotientMap_quotient_mk'` | Defined/proved on the same carrier and projection |
| II.3.3 warning that this quotient need not be Hausdorff | 44 / 50 | `RQ.NonHausdorffOrbitQuotientStatement` in the separate published module described below | Statement; existential counterexample target |
| II.3.3 Lemma, the projection is open | 44 / 50 | `MulAction.isOpenQuotientMap_quotientMk` on the identical orbit quotient; joint action continuity supplies the constant-action continuity it needs | Reuse of a Mathlib proof |
| II.3.3 Lemma, invariant closed and locally closed subsets have closed and locally closed images | 44 / 50 | `RQ.InvariantQuotientImagesStatement` | Statement, Task 5390 |
| II.3.3 paragraph after the Lemma, a Hausdorff orbit quotient is t.d. | 44 / 50 | `RQ.HausdorffOrbitQuotientStatement` | Statement, Task 5390; Hausdorffness is a premise on the actual quotient |
| II.3.3 Corollary, canonical `G/stabilizer ≃ₜ X` for a transitive action | 45 / 51 | `RQ.TransitiveQuotientHomeomorphismStatement` specifies `e (QuotientGroup.mk g) = g • x` | Statement, Task 5390; the point `x` is supplied and no arbitrary homeomorphism can replace the orbit map |
| II.3.4 Lemma, quotient by any closed subgroup is t.d. | 45 / 51 | `RQ.ClosedSubgroupQuotientStatement` | Statement, Task 5390; no normality premise |
| II.3.4 Lemma, the normal quotient is a t.d. group | 45 / 51 | The preceding statement together with Mathlib `QuotientGroup.instIsTopologicalGroup` when the subgroup is normal | Statement plus an existing group-topology instance; no additional mathematical target is needed |

The topology conjunction retains both independent universes `uG` and `uX`.
Mathlib's `isOpenMap_smul_of_sigmaCompact` is a relevant open orbit-map proof
input; the published `Langlands.Geometric.cosetOrbitHomeomorph` concerns a
specific double-coset orbit and does not replace the general Corollary.

## II.3.5: fixed spaces, uniform unions and test decompositions

| Source assertion | Printed / PDF | Exact correspondence | Status |
| --- | --- | --- | --- |
| Left, right and both fixed spaces in `C∞(G)` | 45 / 51 | `GF.functionsLeft`, `GF.functionsRight`, `GF.functionsBoth`; `GF.fixed`, `GF.mem_fixed_iff` | Defined; fixed vectors use `Representation.invariants` of the actual restricted representation |
| The three corresponding spaces in `D(G)` | 45 / 51 | `GF.testsLeft`, `GF.testsRight`, `GF.testsBoth`; `GF.testsBoth_eq_inf`, `HT.mem_biInvariant_iff` | Defined; equality with the intersection and the existing bi-invariant test space proved |
| The three corresponding spaces in `D′(G)` | 45 / 51 | `GF.distributionsLeft`, `GF.distributionsRight`, `GF.distributionsBoth` | Defined as fixed submodules in the full dual |
| The three corresponding spaces in `E′(G)` | 45 / 51 | `GF.compactDistributionsLeft`, `GF.compactDistributionsRight`, `GF.compactDistributionsBoth` | Defined as actual intersections with `D.compactlySupported` |
| The twelve uniform unions | 45–46 / 51–52 | `GF.uniformFunctionsLeft`, `GF.uniformFunctionsRight`, `GF.uniformFunctionsBoth`; `GF.uniformTestsLeft`, `GF.uniformTestsRight`, `GF.uniformTestsBoth`; `GF.uniformDistributionsLeft`, `GF.uniformDistributionsRight`, `GF.uniformDistributionsBoth`; `GF.uniformCompactDistributionsLeft`, `GF.uniformCompactDistributionsRight`, `GF.uniformCompactDistributionsBoth` | Defined by `GF.uniform`: existence of a compact open level, with no span, closure or completion added |
| Lemma (i), finite double-coset indicator expansion | 46 / 52 | `TD.DoubleCosetExpansionStatement` | Statement, Task 5391; finite distinct double cosets and equality in the existing test space |
| Lemma (ii), fixed-left support and `Kg` expansion | 46 / 52 | `TD.LeftInvariantExpansionStatement` | Statement, Task 5391; exact support union, nonzero coefficients and disjoint cosets |
| Lemma (ii), fixed-right support and `gK` expansion | 46 / 52 | `TD.RightInvariantExpansionStatement` | Statement, Task 5391; includes the empty family for the zero function |
| Corollary, `D(G)` lies in uniformly bi-invariant `C∞(G)` and all three uniform test unions equal `D(G)` | 46 / 52 | `HT.commonCompactOpenBiInvariance`, `HT.mem_biInvariant_iff`, `GF.testsBoth_eq_inf`, `GA.leftFunctions_apply`, `GA.rightFunctions_apply`, and the literal union definitions | Reuse by the exact composition below; no new unproved Corollary target |

For the Corollary, apply the published
[common compact-open bi-invariance theorem](../../Langlands/Representation/Hecke/CommonInvarianceProof.md)
to `G`, the singleton `{f}`, and the top open subgroup `⊤`. It returns a
compact open `K` with `f ∈ HT.biInvariant K.toSubgroup K.toSubgroup`.
`GF.testsBoth_eq_inf` gives both one-sided test memberships, so the same `K`
witnesses membership in each of the three uniform test unions. Every element
of any such union was already an actual test, giving equality with the whole
test space. For the locally constant function underlying `f`,
`HT.mem_biInvariant_iff` and the two `GA.*Functions_apply` formulas give fixedness
under the actual left and right function actions. Thus that same `K` witnesses
its membership in `GF.uniformFunctionsBoth`. Its membership in ordinary
`LocallyConstant G ℂ` is already part of the test definition. This composition
was compiled in a private development check; that check is not a proof
publication.

## II.3.6–II.3.8: Haar distributions and modular conventions

| Source assertion | Printed / PDF | Exact correspondence | Status |
| --- | --- | --- | --- |
| II.3.6 Proposition, positive left-invariant distribution and uniqueness up to a complex scalar | 46–47 / 52–53 | `D.IsNonnegativeTest`, `D.IsPositive`, `D.IsLeftInvariant`; `RH.LeftHaarStatement` | Predicates defined; existence and uniqueness are a Statement, Task 5392 |
| II.3.6 Proposition, analogous right-invariant distribution | 46 / 52 | `D.IsRightInvariant`, `RH.RightHaarStatement` | Statement, Task 5392 |
| Positive invariant distributions differ by a positive real scalar | 46–47 / 52–53 | `RH.PositiveScalarUniquenessStatement` | Statement, Task 5392; strict positivity excludes the zero functional |
| Realization by an actual Haar measure and comparison with every invariant algebraic distribution | 46–47 / 52–53 | `D.ofMeasure`, `D.ofMeasure_apply`; `RH.MeasureHaarBridgeStatement` | Integration defined/proved linear; positivity, invariance and full-dual uniqueness are a Statement, Task 5392 |
| II.3.6 density `f μ` for locally constant functions and its embedding | 47 / 53 | `D.multiplyTest`, `D.density`, `D.density_apply`; `RH.DensityEmbeddingStatement` | Map defined by the exact integral; injectivity and equality of actual supports are a Statement, Task 5392 |
| II.3.6 restriction to tests embeds `D(G)` into `E′(G)` | 47 / 53 | `D.testDensity`, `D.testDensity_apply`; compact-value clause of `RH.DensityEmbeddingStatement` | Map defined; compact-value and embedding conclusions are a Statement, Task 5392 |
| II.3.7 definition of positive modular character and `r(g) μ = δ(g) μ` | 47 / 53 | `D.renardModular` is an actual monoid homomorphism; `RM.TranslationStatement`, `RM.RegularityStatement` | Character defined; distribution scaling and positivity are Statements, Task 5393 |
| II.3.7 displayed two-sided translation integral | 47 / 53 | `RM.TranslationStatement` requires the exact integral of `f(h′*x*h⁻¹)` against the supplied Haar measure | Statement, Task 5393 |
| II.3.7 Proposition (i), triviality on every compact subgroup; regularity of the character | 47 / 53 | `RM.RegularityStatement`; existing `Langlands.Haar.modularCharacterRegularity`, `Langlands.Haar.modularCharacter_eq_one_of_mem_compact`, and `D.renardModular_eq_inv` | Renard bundle is a Statement, Task 5393; published Mathlib-convention local constancy, continuity and compact-subgroup results are reusable via the reciprocal adapter |
| II.3.7 Proposition (ii), `δ⁻¹ μ` is right invariant and equals inverted left Haar | 47 / 53 | `RM.InversionDensityStatement` with a pointwise specified locally constant reciprocal density and `GA.inversionDistributions` | Statement, Task 5393, at full t.d. scope |
| II.3.7 Definition of unimodularity and its distribution meaning | 48 / 54 | Literal property `∀ g, D.renardModular g = 1`; `RM.UnimodularityStatement` equates it with right invariance of `D.ofMeasure μ` | Exact property represented; equivalence is a Statement, Task 5393 |
| II.3.7 Examples 1–3: abelian, compact, and covered by compact subgroups | 48 / 54 | The three implication clauses of `RM.UnimodularityStatement` | Statement, Task 5393; the last premise means every element lies in an actual compact subgroup |
| II.3.7 automorphism module, pushforward scaling and (II.3.7.1) | 48 / 54 | `D.renardAutomorphismModule`, `RM.AutomorphismStatement` | Scalar defined; scaling and integral identity are a Statement, Task 5393 |
| II.3.7 module of inner conjugation equals the modular value | 48 / 54 | `RM.InnerAutomorphismStatement` for a continuous automorphism whose point map is `x ↦ h*x*h⁻¹` | Statement, Task 5393 |
| II.3.8 Haar mass identities and index formula (II.3.8.1) | 48 / 54 | `RM.IndexFormulaStatement`, with `P = K.toSubgroup.comap σ.toMonoidHom` and `L = K.toSubgroup ⊓ P` | Statement, Task 5393; numerator `L.relIndex P`, denominator `L.relIndex K.toSubgroup`, exactly `[σ⁻¹K:L]/[K:L]` |

Mathlib proves Haar-measure existence and measure-level uniqueness; the
`MeasureTheory.Measure.haarMeasure` construction and the uniqueness results in
`Mathlib.MeasureTheory.Measure.Haar.Unique` are available inputs. They do not
by themselves classify **all algebraic invariant distributions**. That is why
`RH.MeasureHaarBridgeStatement` compares the concrete `ofMeasure μ` with every
invariant element of the full dual. The density construction proves test
integrability directly from continuity and compact support.

The published [modular regularity proof](../../Langlands/Analysis/Local/ModularCharacterRegularityProof.md)
is at the full locally compact t.d. scope. The related
`Langlands.Haar.HaarInversionDensityStatement` is measure-theoretic and has
second countability hypotheses; it is not substituted for the unrestricted
Renard distribution target. The pinned Mathlib has no group-level
`IsUnimodular` class; an unrelated module predicate with a similar name is
not used. The published `Langlands.Haar.CompactOpenIndexHaarStatement` uses
the image-oriented, reciprocal-character convention and is a proof input
rather than an identification with (II.3.8.1).

## II.3.9: twisted homogeneous-space functions and invariant functionals

| Source assertion | Printed / PDF | Exact correspondence | Status |
| --- | --- | --- | --- |
| Introductory warning: an ordinary homogeneous space need not admit an invariant positive measure | 48 / 54 | `HR.NonexistenceStatement` on the actual untwisted `Langlands.Induction.LeftQuotient H`, described in the supplementary-statement table | Statement; existential target in the source's positive-distribution language |
| Relative modular character `δ_(H\G) = δ_G|_H / δ_H` | 48 / 54 | `HF.relativeModular H hH` on the actual closed subgroup with its induced topology | Defined as a monoid homomorphism |
| Locally constant, relatively covariant functions with compact support modulo `H` | 48 / 54 | `HF.CompactModulo`, `HF.space`, `HF.renardSpace`, `HF.mem_space` | Defined as a submodule of the original locally constant functions; compact support means containment in `H*K` for an actual compact `K ⊆ G` |
| Stability under right translation | 48 / 54 | `HF.rightTranslate`, `HF.rightTranslate_apply`, `HF.rightAction` | Defined/proved; representation on the same covariant function space |
| Trivial relative character identifies the space with `D(H\G)` | 48 / 54 | `HR.QuotientTestStatement`, pointwise pullback along `Langlands.Induction.quotientMap H` | Statement, Task 5524; an actual linear equivalence, not an assumed quotient model |
| Theorem, a positive right-invariant functional, unique up to scalar | 49 / 55; proof 49–50 / 55–56 | `HR.InvariantFunctionalStatement` | Statement, Task 5524; includes unique complex multiples for every invariant functional and unique positive real multiples for positive invariant functionals |
| Averaging map in the proof, its values, surjectivity, right equivariance and Haar factorization | 49–50 / 55–56 | `HR.AveragingStatement` specifies `p(f)(g) = ∫ h:H, f(h*g) δ_G(h)⁻¹ dμ_H(h)` and `ν.comp p = D.ofMeasure μ_G.inv` | Statement, Task 5524; every fiber integrand must be integrable and all witnesses have the specified actual values |
| Remark, pointwise `D(H\G)`-module and associated sheaf | 50 / 56 | `HR.PointwiseModuleSheafStatement`, the existing `Langlands.HarmonicAnalysis.PointwiseTestAlgebra.Carrier` and actual `Langlands.Sheaf.Renard.ProjectorBasisSheaf.basisSheaf` | Statement, Task 5524; nondegeneracy, pullback multiplication, projector support and characteristic-function restriction formulas are explicit |
| Internal comparison used to reuse existing compact induction | 48–50 / 54–56, derived bridge rather than a separately named source assertion | `HR.CompactInductionStatement` | Statement, Task 5524; identity-on-values equivariant equivalence with the existing `Langlands.Induction.CompactFunctions` carrier |

The quotient is the existing `Langlands.Induction.LeftQuotient H`, with cosets
`H*g` and the quotient topology. The module/sheaf target uses the already
published scalar-projector construction from II.2.4–II.2.5 (printed pp.38–42 /
PDF pp.44–48); it does not posit a new sheaf with unspecified action.

The compact-induction bridge retains the obligation to compare local constancy
and compact lift of support with the existing carrier's **single open right
stabilizer** and compact projected support. These conditions are not
identified by definition. Its smooth character has the actual relative
modular values, also matching the pointwise character in
`Langlands.Hecke.Homomorphism.relativeModularCharacter` when the latter's
hypotheses are supplied.

The published `Langlands.QuotientIntegration.compatibleMeasureExists`
constructs an untwisted quotient measure under supplied regular two-sided Haar
hypotheses on group and subgroup. This restricted positive case neither
settles the arbitrary closed-subgroup twisted theorem nor refutes the
introductory nonexistence warning.

## II.3.10–II.3.11: compact convolution and subgroup distributions

| Source assertion | Printed / PDF | Exact correspondence | Status |
| --- | --- | --- | --- |
| II.3.10 compact-distribution convolution by tensor and multiplication | 50 / 56 | `D.onSupport`, `D.multiplicationPullback`, `D.convolutionDistribution`, `D.convolution`; `RC.AmbientTensorStatement` | Actual compact convolution defined; equality with the source's ambient tensor/extended-pairing presentation is a Statement, Task 5394 |
| II.3.10 scalar convolutions `T*f`, `f*T` on `D′×D` and `E′×C∞` | 50 / 56 | `D.leftConvolveTest`, `D.rightConvolveTest`, `D.leftConvolveSmooth`, `D.rightConvolveSmooth`; `RC.RegularityStatement` | Kernels defined as actual functions; local constancy, agreement of the domains and compact test preservation are Statements, Task 5394 |
| II.3.10 Proposition (i), support in the product of supports and compact closure | 50 / 56 | `D.support_convolutionDistribution_subset`, compact subtype result `D.convolution` | Proved intrinsically in the convolution definition unit |
| II.3.10 Proposition (ii), associativity | 50 / 56 | `RC.AssociativityStatement` | Statement, Task 5394 |
| II.3.10 Proposition (iii), all three mixed associativity identities | 50 / 56 | `RC.MixedAssociativityStatement` | Statement, Task 5394; intermediate locally constant witnesses are constrained by their actual values |
| II.3.10 Proposition (iv), left- and right-Haar density formulas | 50 / 56 | `RC.HaarDensityStatement` | Statement, Task 5394; the left formula uses left Haar and the right formula uses an actual right-invariant finite-on-compacts measure |
| II.3.10 Proposition (v), evaluation via the inverted test at the identity | 50 / 56 | `RC.EvaluationStatement` | Statement, Task 5394; quantifies over every full algebraic distribution |
| II.3.10 following paragraph, bilinear associative convolution algebra and actual Dirac unit | 50 / 56 | `RC.BilinearUnitStatement`, `RC.AssociativityStatement`; `D.dirac`, `D.dirac_apply`, `D.compactDirac` | Diracs and their compactness defined/proved; bilinearity and unit laws are Statements, Task 5394. No unproved algebra instance is installed |
| II.3.10 left/right actions on `E′` and Lemma's three Dirac formulas | 51 / 57 | `RC.DiracStatement` identifies compact convolution with `GA.leftDistributions g`, `GA.rightDistributions g⁻¹`, and `D.compactDirac (g*g′)` | Statement, Task 5394; equality with compact witnesses also gives the required action stability |
| II.3.11 normalized Haar distribution of an arbitrary compact subgroup | 51 / 57 | `D.compactSubgroupDistribution`, `D.compactSubgroupHaar`, `D.compactSubgroupHaar_apply`, `D.compactSubgroupDistribution_mem_supportedOn` | Defined; integral on tests and subgroup support bound proved |
| II.3.11 displayed integral on every locally constant function | 51 / 57 | `RK.ExtendedIntegralStatement` using the existing `D.compactSupportPairing` | Statement, Task 5525; identifies the actual extended pairing with normalized subgroup Haar integration |
| II.3.11 Lemma, unique mass-one bi-invariant distribution on `K*g*L` | 51 / 57 | `RK.DoubleCosetUniquenessStatement` | Statement, Task 5525; actual support, both invariances and total mass one, with the explicit value `e_K*δ_g*e_L` identified in the proof |
| II.3.11 Proposition (i), `e_M = e_K*e_L = e_L*e_K` when `M=KL` | 51 / 57 | `RK.ProductStatement` | Statement, Task 5525; requires the set product to be the actual underlying set of the supplied compact subgroup `M` |
| II.3.11 Proposition (ii), Dirac conjugation | 51 / 57 | `RK.ConjugationStatement` with `K.map (MulAut.conj g).toMonoidHom` | Statement, Task 5525; conjugated-subgroup compactness is a conclusion |
| II.3.11 stated idempotence and nested-subgroup absorption consequences | 51 / 57 | `RK.IdempotenceAbsorptionStatement` | Statement, Task 5525; both orders equal `e_L` when `K ≤ L` |

The II.3.11 statements cover **all compact subgroups**, including nonopen ones.
The existing compact-open function indicator identities are useful inputs but
do not replace this scope. `D.compactSupportPairing` descends the original
distribution to its actual compact topological support; an arbitrary extension
of a functional to all locally constant functions is not used.

## II.3.12: the Hecke algebra, local units and corners

| Source assertion | Printed / PDF | Exact correspondence | Status |
| --- | --- | --- | --- |
| Lemma, test densities identify `D(G)` with uniformly left-invariant `E′`; right and both uniform spaces agree | 51–52 / 57–58 | `RU.UniformRangeStatement` gives injectivity of `D.testDensity μ` and its exact range and all three uniform-space equalities | Statement, Task 5526 |
| Change of notation defining `H(G)` as that distribution subspace | 51 / 57 | `D.heckeDistribution`, `D.heckeDistributionSpace`; `HE.DensityRealizationStatement` | Map and actual linear-map range defined; injectivity and equality with the test-density range are a Statement, Task 5527. The existing `HA` carrier supplies the function algebra |
| Compact-open `e_K` belongs to `H(G)` | 52 / 58 | `HE.NormalizedIndicatorStatement` identifies `D.heckeDistribution μ (HA.normalizedIndicator μ K hK)` with the actual `D.compactSubgroupHaar K.toSubgroup hK` | Statement, Task 5527 |
| Dirac is compactly supported but the printed text excludes it from `H(G)` | 52 / 58 | `D.compactDirac`; corrected `RU.DiracMembershipStatement` | Compactness proved; exact membership iff discreteness is a Statement, Task 5526 |
| Remark 1, convolution stability and nonunitality claim | 52 / 58 | Existing `HA` nonunital ring and product; `RC.HeckeCompatibilityStatement`; corrected `RU.UnitCriterionStatement` | Function product proved; distribution-product bridge is a Statement, Task 5394; identity iff discreteness is a Statement, Task 5526 |
| Remark 2, `H(G)` is a two-sided ideal in `E′(G)` | 52 / 58 | `RU.IdealStatement`, with `RC.HaarDensityStatement` as the source formula input | Statement, Task 5526; actual compact witnesses and density range in both product orders |
| Remark 3, transported test convolution and (II.3.12.1) | 52 / 58 | `HT.convolution`, `HT.convolution_apply`, `RC.HeckeCompatibilityStatement` | Integral test formula and its algebra laws proved; actual distribution-density comparison is a Statement, Task 5394 |
| Proposition, algebra with a filtered system of compact-open idempotents | 52 / 58 | `HA.normalizedIndicator_idempotent`, `HA.finiteFamilyLocalUnits`; `HE.LocalUnitsStatement`, `HE.NormalizedIndicatorStatement` | Function identities proved; their distribution form is a Statement, Task 5527. Local subgroups may refine any prescribed open subgroup |
| Proposition, inversion is an anti-involution and fixes every `e_K` | 52 / 58 | `GA.inversionDistributions_inversionDistributions`, `HE.InversionStatement`, `RU.InversionDensityStatement` | Linearity/involutivity on the dual proved; compact anti-multiplication and fixed idempotents are a Statement, Task 5527; Hecke-range stability with modular density formula is a Statement, Task 5526 |
| Following remark, reversed subgroup criterion for idempotent order | 52 / 58 | `HE.IdempotentOrderStatement` | Statement, Task 5527; both products equal `e_K` iff `L ≤ K` |
| Definition and unitality of `H(G,K)=e_K H(G) e_K` | 52 / 58 | `HA.Corner`, `HA.mem_biInvariant_iff_exists_sandwich`, `HA.Corner.range_toHeckeAlgebra`; `HE.CornerStatement` | Existing function corner and its ring/complex-algebra structure proved; exact distribution range and unit correspondence are a Statement, Task 5527 |
| Corner Remark 1, equality with compact bi-`K` distributions | 52 / 58; proof 53 / 59 | `HE.CornerStatement`, range equal to `GF.compactDistributionsBoth K.toSubgroup` | Statement, Task 5527 |
| Corner Remark 2, basis `a_(g,K)=e_K*δ_g*e_K` over double-coset representatives | 53 / 59 | `HE.DoubleCosetBasisStatement`, `HA.Corner.massIndicator`, `HA.Corner.massIndicator_apply`, `HA.Corner.integral_massIndicator` | Function mass-one indicator defined/proved; exact sandwich distribution and basis for every system of representatives are a Statement, Task 5527 |

The function-valued finite-family local-unit theorem is published in
[LocalUnitsProof](../../Langlands/Representation/Hecke/LocalUnitsProof.md).
Its distribution analogue retains the precise normalized Haar identification;
that bridge is not inferred from matching notation. Refinement inside an
intersection gives the source's filtered family.

In the last row, `massIndicator` is the indicator of `KgK` divided by its
Haar mass, so its total mass is one. It is not an unnormalized characteristic
function. The target uses `Module.Basis` and constrains each basis value to
the original convolution sandwich. On functions, inversion of a Haar density
has the value `δ_G(x)⁻¹ f(x⁻¹)` relative to the same left Haar measure. A bare
inverted function omits this factor for a nonunimodular group.

## II.3.13: full-dual actions, products, completion and center

| Source assertion | Printed / PDF | Exact correspondence | Status |
| --- | --- | --- | --- |
| First Definition, `T*h` and `h*T` for the full algebraic dual | 53 / 59 | `D.rightHeckeOperator`, `D.leftHeckeOperator`, `D.rightHeckeConvolution`, `D.leftHeckeConvolution`; `FH.KernelStatement` | Actual algebraic transposes defined; exact source kernels, integrability and test witnesses are a Statement, Task 5528 |
| First Remark, agreement with compact convolution | 53 / 59 | `FH.CompactCompatibilityStatement` | Statement, Task 5528; compact Hecke witnesses must coerce to the original density |
| Exercise in the Remark, inversion reverses the full actions | 53 / 59 | `FH.InversionStatement` | Statement, Task 5528; inverted Hecke element fixed by equality with actual inversion of its density |
| Exercise, right associativity; also left and mixed action laws | 53 / 59 | `FH.AssociativityStatement` | Statement, Task 5528; all three laws retained |
| Equivalent evaluation formula (II.3.13.1) | 53 / 59 | `FH.EvaluationStatement` with `D.leftConvolveTest` at `1` | Statement, Task 5528 |
| Second Definition, right, left and two-sided essential compactness | 54 / 60 | `D.rightEssentiallyCompact`, `D.leftEssentiallyCompact`, `D.essentiallyCompact` | Defined as actual submodules of the original dual, testing compact support of every appropriate full Hecke product; the last is their intersection |
| Paragraph after Definition, products with `H(G)` lie in `H(G)` | 54 / 60 | `FH.RangePreservationStatement` | Statement, Task 5528; actual density range, not only compact support |
| Lemma, unital complex convolution algebras extending `E′` | 54 / 60; proof 54–55 / 60–61 | `EP.Statements` with `EP.RightProductSpecification`, `EP.LeftProductSpecification`, `EP.TwoSidedProductSpecification`, `EP.AlgebraLaws` | Statement, Task 5529; existence/uniqueness of actual bilinear products, associativity, the Dirac unit, compact extension and full Hecke compatibility |
| Lemma proof, local-idempotent formulas, independence and agreement on the intersection | 54–55 / 60–61 | The evaluation/action clauses of the three preceding `EP` specifications | Statement within the same target, Task 5529; every allowed local unit must give the specified value, and both restricted products coincide |
| Displayed inclusion chain, also the compact inclusion asserted in the Definition | 54–55 / 60–61 | `FH.InclusionsStatement`: Hecke range ≤ compact support ≤ two-sided essential compactness ≤ each one-sided submodule | Statement, Task 5528 |
| Theorem, right-essentially-compact distributions identify with the completed Hecke algebra | 55 / 61 | `CO.Statements`, `CO.ComparisonSpecification` and the published `Langlands.Algebra.IdempotentedRingRightLimit (Langlands.Hecke.HeckeAlgebra μ)` carrier | Statement, Task 5530; actual additive equivalence preserving complex scalars, products, unit and canonical Hecke inclusion |
| Theorem proof, forward coordinate `T ↦ (e ↦ T*e)` and inverse evaluation | 55 / 61 | Coordinate and inverse-evaluation clauses of `CO.ComparisonSpecification` | Statement within the same target, Task 5530; coordinates run over all Hecke idempotents, with the source's exact conditions on the test and inverted idempotent |
| Corollary, categorical center is conjugation-invariant essentially compact distributions | 55 / 61; proof 55–56 / 61–62 | `CZ.CategoricalCenterStatement`, `CZ.CategoricalComparisonSpecification`; existing `Langlands.Algebra.NondegenerateModuleCenter` and `D.IsConjugationInvariant` | Statement, Task 5531; classification of the actual natural-endomorphism center, with full product/completion witnesses and action compatibility |
| Corollary proof, centrality equals the Hecke commutant, invariance and automatic two-sided essential compactness | 55 / 61 | `CZ.CentralitySpecification` | Statement within Task 5531; together with the specified products/inclusions gives the source's center identifications |
| Corollary proof, translation, trace (II.3.13.2) and sandwich (II.3.13.3) criteria | 56 / 62 | `CZ.TranslationCondition`, `CZ.TraceCondition`, `CZ.SandwichTraceCondition`, `CZ.CriteriaStatement`; `GA.isConjugationInvariant_iff_fixed` | Predicates and original inner-action bridge defined/proved; the three equivalences are a Statement, Task 5531, including all four local-unit conditions of the sandwich formula |

The full left Hecke transpose uses convolution against `μ.inv`; this yields
the source kernel `∫ y, h(y) f(y*x) dμ(y)`. The right transpose yields
`∫ y, h(y) f(x*y) dμ(y)`. The map does not identify inversion of a density
with its bare function inversion against left Haar. For an arbitrary full
distribution these are defined actions; their notation alone does not assert
a general convolution of two arbitrary full distributions.

The three essentially compact products are existentially specified **complex
bilinear maps on the existing submodules**. This expresses the algebra laws
without installing an unproved ring structure. The formulas pin every lift to
the same underlying distribution. Uniqueness is an internal formulation of
the source's local-unit determination, identified as such in the paired
Markdown.

The completion is the already constructed compatible-family object of
[IdempotentedRingRightLimit](../../Langlands/Algebra/IdempotentedRingRightLimit.md)
and its [ring product](../../Langlands/Algebra/IdempotentedRingRightLimitRing.md).
`CO.ComparisonSpecification` requires the exact published product, unit and
canonical map, and the distribution identity for **every** idempotent
coordinate. In its inverse formula, `f*e=f` means
`D.rightConvolveTest f (D.heckeDistribution μ e) = f` as ordinary functions;
it is not bare left-Haar density convolution. Hecke idempotentedness has
published inputs `Langlands.Hecke.Homomorphism.isIdempotented` and
`Langlands.Hecke.NondegenerateEquivalence.idempotented`.

The categorical center is the actual center of the category of nondegenerate
original Hecke modules, as constructed in
[NondegenerateModuleCenter](../../Langlands/Algebra/NondegenerateModuleCenter.md).
Its module universe is `max uG uM`, which contains the regular Hecke carrier;
both universe parameters are retained in the target and its proof task.
`CZ.CategoricalComparisonSpecification` equates the **entire natural
transformation** to the published `fromCommutantRingHom` action of the same
compatible family. A carrier bijection without this equality would not meet
the target. The specifications preserve addition, product and actual Dirac
unit. The full-dual criteria are an internal extraction of the source's
local-test argument, not a restriction to measures or an assumed center
classification.

## Publication and proof responsibility

The nineteen original published units of Task 5298 are the six definition pairs
`GroupFunctionSpaces`, `Distribution/Haar`, `Distribution/Convolution`,
`Distribution/CompactSubgroup`, `HomogeneousFunctions` and
`Distribution/HeckeRealization`, and the thirteen statement pairs represented
by `RQ`, `TD`, `RH`, `RM`, `RC`, `RU`, `RK`, `HE`, `HR`, `FH`, `EP`, `CO` and
`CZ` above. In particular the three final statement units `EP`, `CO`, `CZ`
were published together at `642008d6b3b837d8bd76de0cabcaff3db00088c0` and are
present in the inspected snapshot. Their candidate IDs were respectively
`3af6aa5a-cf67-41b4-80a9-c00365e36deb`,
`f4aa3044-27c3-4b6f-a043-edfa0a5f8ed6`, and
`c63d30a5-ff46-4cfb-a6df-88a59efc2298`. None is a proof artifact.

Two supplementary source-warning statements complete the twenty-one published
mathematical units. Both received independent semantic approval without
qualifications and accepted machine validation, then were published together
at `3f9691717b5fba9a8561abf028ae957f63bdf0dd`. Their actual full-dual/quotient
objects are reused, and their separate files leave the original proof targets
unchanged.

| Source warning | Exact declaration and published module | Accepted publication |
| --- | --- | --- |
| II.3.3, printed p.44 / PDF p.50, a possibly non-Hausdorff orbit quotient | `Langlands.Topology.RenardOrbitQuotient.NonHausdorffOrbitQuotientStatement`; [RenardOrbitNonHausdorffStatement](../../Langlands/Topology/RenardOrbitNonHausdorffStatement.md) | `8e41233b-1ef2-42a8-bf43-b8721054f537`; Reviewer 1326; machine receipt `aaf7cd47-58cd-4be8-b7bc-ab7239e5f8e4` |
| II.3.9, printed p.48 / PDF p.54, failure of ordinary invariant-measure existence | `Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard.NonexistenceStatement`; [RenardHomogeneousNonexistenceStatement](../../Langlands/HarmonicAnalysis/RenardHomogeneousNonexistenceStatement.md) | `e30a3b87-33ad-4cd4-96f6-5b833f24082c`; Reviewer 1341; machine receipt `dff1d826-3cee-4335-a992-5a39ead0f4b2` |

The first statement existentially supplies actual small locally profinite
`G,X` and a continuous action whose genuine orbit quotient is not `T2Space`.
The second existentially supplies an actual small locally profinite group and
closed subgroup such that the original test dual on `H\G` has no strictly
positive right-invariant functional. Inversion exchanges this orientation
with the source's initial `G/H` left-action wording. Neither statement
constructs its counterexample. After verifying both published statement pairs
in the current Library and checking for existing target ownership, Worker 152
published their exact-target proof successors as Tasks 5538 and 5539 below.
Both closed existential targets have no universe parameters.

The existing proof tasks were checked before publishing successors, so no
second owner was created for the same conjunction. These tasks request exact
proofs at the full universe parameters in the pinned environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`. They do not weaken the published
statements, assume countability where the source does not, or replace actual
objects with abstract data. At the original proof-status snapshot no proof of
any of the thirteen new conjunctions had been verified as published. The final
publication check adds the two warning statements and their proof tasks; it
does not change that original proof inventory.

| Target (expanded using the key above) | Proof task | Exact task ID |
| --- | --- | --- |
| `RQ.Statements` | Task 5390 | `4dc43975-5a2a-4932-93c5-d9d9dc7432dc` |
| `TD.Statements` | Task 5391 | `9789050f-9880-4696-904c-b052cb8a2734` |
| `RH.Statements` | Task 5392 | `84de2204-23f4-4643-9303-750d6cf7f0be` |
| `RM.Statements` | Task 5393 | `74769208-3d55-4ef2-aa2a-4549c8996b32` |
| `RC.Statements` | Task 5394 | `ba3a99db-bd04-4bbb-a2f7-2ffd552c8b1e` |
| `HR.Statements` | Task 5524 | `651213dd-94e7-4b66-b29b-6425651218ba` |
| `RK.Statements` | Task 5525 | `d9e4c924-a43a-494a-b5cd-77509edb0514` |
| `RU.Statements` | Task 5526 | `fff3688f-81f8-4e16-aff5-2f8604315330` |
| `HE.Statements` | Task 5527 | `be3a0e23-9654-4828-9638-6d18b1952e05` |
| `FH.Statements` | Task 5528 | `992f10ae-4b09-4ebe-b648-242dd5cf2b9e` |
| `EP.Statements` | Task 5529 | `1660d179-c073-4147-b4e2-dd1c18248ae5` |
| `CO.Statements` | Task 5530 | `2d9ba6dd-6ec9-4665-b052-090a8145222f` |
| `CZ.Statements` | Task 5531 | `b7cf63f9-3bae-4c74-aed2-596e2f7dc8d4` |
| `RQ.NonHausdorffOrbitQuotientStatement` | Task 5538 | `2f9c3b8a-210e-481f-9fd4-c6669b0efb42` |
| `HR.NonexistenceStatement` | Task 5539 | `982737bc-92bb-40cc-a11c-1876df77c711` |

The mathematical dependency route runs from topology and test decompositions
to Haar/modular and homogeneous-space results, compact convolution and compact
subgroups, then the Hecke comparisons, full actions, essentially compact
products, completion and center. The latter targets include the required
existence conclusions; they are not conditional classifications whose main
existence is silently supplied as a premise. The already published finiteness,
function-action, common-invariance, normalized-indicator, function-convolution,
corner and abstract completion results remain reusable inputs. Proving the
listed general statements and the two warning examples remains separate from
this statement-coverage task's publication obligations.

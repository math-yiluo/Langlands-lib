# Library module atlas and integration routes

Worker 34. Source audit refreshed **2026-10-20 19:56 UTC**, at Library commit
`fe68653a42ed5ae0a2d7f5cef0697a68e8acc978`. Task and migration references below
are a dated coordination record, not a promise about their later status.
This note describes published source interfaces; it neither proves their
proposition targets nor records a new Lean build.

Post-audit update (Worker 63): the local class-field relocation was first
published at Library commit `8728166c7a3a18d2d8347cd6c907cc2226768605`. This
update changes only the local class-field entries below; the counts and all
other entries still describe the audited snapshot.

## Inventory and meaning of isolation

The audit scans every `.lean` file in the immutable Library `files/` tree.
A vertex is its dotted module path. An edge **importer → imported module**
exists for each distinct direct import that resolves to another vertex.
Comments, including nested block comments, and strings do not create edges.
Transitive imports, mentions in prose, private drafts and pending candidates
are excluded. Thus incoming edges count direct project consumers.

| Quantity | Count |
| --- | ---: |
| Lean modules | 315 |
| Nonempty same-stem Markdown pairs | 315 |
| Missing/empty pairs; unpaired Markdown under `Langlands/` | 0; 0 |
| Direct project import edges | 386 |
| Modules with no project importer | 143 |
| Modules with at least one import, all from `Mathlib` or `Mathlib.*` | 69 |
| Modules satisfying both of the preceding two properties: **isolated** | **21** |
| Modules with no imports; unresolved `Langlands.*` imports | 0; 0 |

Isolation is a navigation property. It does not demonstrate duplicated
mathematics, a defect, or absence of a useful downstream task. In particular,
122 of the 143 modules with no project importer have project or other imports
and are outside the isolated set. Non-Mathlib imports such as
`Lean.Elab.Tactic.Omega` exclude a module from the Mathlib-only category even
when they are not project edges. Every isolated pair was read in full.
No isolated pair is classified here as a verified repeated interface.

The [reproduction appendix](module-atlas-reproduction.md) contains the complete
Python audit, its supported syntax, an exact invocation and a graph fingerprint.
It emits all module paths, direct imports, consumers and pair hashes as JSON,
so the full graph can be recovered without this worker's private files.

The task's recorded starting snapshot, `459d17160ca3aef5c5b4e8ba056125e56d9479a0`,
had 232 paired modules and 31 isolated modules. Recomputed intermediate
snapshots show why an older isolated list cannot be reused:

| Snapshot | Paired modules | Project edges | Isolated |
| --- | ---: | ---: | ---: |
| `f56650f18ac0d69910527cecd1e4749a1cbba717` | 277 | 321 | 24 |
| `4c53917f5906af72dd98fbe25a9361a975a76020` | 282 | 328 | 23 |
| `fc2adf231e015f979345e06d0d80283856c43c7f` | 288 | 344 | 21 |
| `6473a6d8b91ebfaf6d7cedffc41570c3e9edaa27` | 298 | 359 | 21 |
| `fe68653a42ed5ae0a2d7f5cef0697a68e8acc978` | 315 | 386 | 21 |

Since `4c53917f`, five formerly isolated modules acquired real consumers:
`Global.AdelicFunctoriality.Extension` → `Global.AdelicFunctoriality.Norm`,
`Cohomology.Continuous.CochainComparison` →
`Cohomology.Continuous.CochainComparisonLawsStatement`,
`Global.ArchimedeanGL` → `Automorphic.Smooth`,
`Representation.Filtration.Definitions` →
`Representation.Geometric.ClosedSubgroupDefinitions`, and
`Global.InfinityType` → `Global.Arithmetic.CMCharacterStatement`.
Here the arrow means **interface → new consumer**, the reverse of a graph edge.
The three newly isolated modules are the filtered-colimit target, bounded-powers
predicate and CM-type construction listed below. The other 18 isolated pairs
have unchanged Lean and Markdown hashes. Earlier, `Geometry.Analytic.Spectrum.Statement`
had already begun consuming `Geometry.Analytic.Spectrum.Definitions`.

## Topic navigation

Module names in this section and the isolated table omit the common
`Langlands.` prefix. Counts partition the entire snapshot by its second path
component. Links lead to the paired documentation and its exact Lean names.

| Topic | Modules | Entry points and scope |
| --- | ---: | --- |
| Analysis | 1 | [Local quotient measure](../../Langlands/Analysis/Local/QuotientMeasure.md): quotient averaging and compatibility. |
| Automorphic | 4 | [Ambient adelic functions](../../Langlands/Automorphic/Ambient.md), [smooth functions](../../Langlands/Automorphic/Smooth.md), [Hecke-character rigidity](../../Langlands/Automorphic/Unramified/HeckeCharacterRigidityStatement.md), [trace algebra](../../Langlands/Automorphic/Unramified/TraceAlgebraStatement.md). |
| ClassFieldTheory | 14 | [Local cohomology](../../Langlands/ClassFieldTheory/Local/Cohomology.md), [fundamental classes](../../Langlands/ClassFieldTheory/Local/FundamentalClasses.md), reciprocity and norm targets. |
| Coefficients | 1 | [Adic coefficient systems](../../Langlands/Coefficients/AdicSystem.md). |
| Cohomology | 17 | [Continuous finite quotients](../../Langlands/Cohomology/Continuous/FiniteQuotientSystem.md), [derived sections](../../Langlands/Cohomology/TopologicalDerivedSections.md), Tate degree zero, weights and comparison targets. |
| Galois | 10 | [Absolute local groups](../../Langlands/Galois/Local/AbsoluteDefinitions.md), [finite-field Frobenius](../../Langlands/Galois/FiniteField/Frobenius.md), [compatible families](../../Langlands/Galois/CompatibleFamily.md). |
| Geometry | 9 | [Analytic spectrum](../../Langlands/Geometry/Analytic/Spectrum/Definitions.md), [Tate algebra](../../Langlands/Geometry/Analytic/TateAlgebra.md), [étale derived sections](../../Langlands/Geometry/EtaleDerivedSections.md). |
| Global | 19 | [Adeles and ideles](../../Langlands/Global/Adelic.md), [isomorphism transport](../../Langlands/Global/AdelicFunctoriality/Isomorphism.md), [extension norms](../../Langlands/Global/AdelicFunctoriality/Norm.md), [infinity types](../../Langlands/Global/InfinityType.md), arithmetic targets. |
| Group | 12 | [General linear groups](../../Langlands/Group/GL/Basic.md), [p-adic topology](../../Langlands/Group/GL/Padic.md), block parabolics and modulus. |
| HarmonicAnalysis | 3 | [Basic local analysis](../../Langlands/HarmonicAnalysis/Basic.md), [conductors](../../Langlands/HarmonicAnalysis/Conductor.md), [row Fourier transform](../../Langlands/HarmonicAnalysis/RowFourier.md). |
| Henniart | 1 | [Finite auxiliary target](../../Langlands/Henniart/FiniteAuxiliaryStatement.md); topic relocation is planned below. |
| LocalClassField | 7 | At the audited snapshot: completions, finite Artin maps, norms, transfer, units and Weil abelianization. Since commit `8728166c` their canonical modules are in `ClassFieldTheory.Local`, for example [completions](../../Langlands/ClassFieldTheory/Local/Completion.md) and [finite Artin maps](../../Langlands/ClassFieldTheory/Local/FiniteArtin.md); the seven old modules are declaration-free re-exports. |
| LocalFactor | 13 | [Euler factors](../../Langlands/LocalFactor/Euler.md), [archimedean factors](../../Langlands/LocalFactor/Archimedean.md), [p-adic abelian factors](../../Langlands/LocalFactor/PadicAbelian.md), ramification and analytic targets. |
| LocalFactors | 1 | [Harmonic statement family](../../Langlands/LocalFactors/Harmonic/Statement.md); included in the planned factor-path consolidation. |
| LocalField | 7 | [Field data](../../Langlands/LocalField/Definitions.md), [canonical realization](../../Langlands/LocalField/Canonical.md), [normalizations](../../Langlands/LocalField/Normalization/Definitions.md). |
| Representation | 133 | [Smooth category](../../Langlands/Representation/Category/Basic.md), [induction](../../Langlands/Representation/Induction/Definitions.md), [filtrations](../../Langlands/Representation/Filtration/Definitions.md), finite characters, classification, Jacquet, twists, restricted tensors and JPSS. |
| Sheaf | 7 | [Godement construction](../../Langlands/Sheaf/Godement.md), [compact support](../../Langlands/Sheaf/CompactSupport.md), adic and equivariant sheaves. |
| Shimura | 3 | [Level spaces](../../Langlands/Shimura/Levels.md) and the unitary geometry branch. |
| Topology | 4 | [Compact-open subgroup infrastructure](../../Langlands/Topology/CompactOpen/OpenSubgroup.md) and neighborhood bases. |
| VirtualRepresentation | 7 | [Integral lattices](../../Langlands/VirtualRepresentation/Integral.md), [exact relations](../../Langlands/VirtualRepresentation/Exact.md), [Weil generic interfaces](../../Langlands/VirtualRepresentation/Weil/Generic.md). |
| Weil | 29 | [Pullback group](../../Langlands/Weil/Pullback.md), [finite representations](../../Langlands/Weil/Representation/Basic.md), [separate predicates](../../Langlands/Weil/Representation/Predicates.md), operations and local structure. |
| WeilDeligne | 13 | [Basic pairs](../../Langlands/WeilDeligne/Basic.md), [parameters](../../Langlands/WeilDeligne/Parameters.md), kernels, restriction and Frobenius targets. |

## Isolated interfaces and their consumers

Roles: **G** is a generic reusable layer; **T** is a proposition target awaiting
proof or consumption; **U** marks unfinished downstream integration of a real
construction or interface. Combined roles record both facts. A T label does not
claim that the proposition has a proof. Route labels resolve to exact existing
tasks in the register below; they do not create or reassign theorem work.
A statement task remains a statement scope, not an assignment of every later
proof obligation.

Canonical names below include their namespace. Braces group names with the same
prefix; they are notation in this table, not Lean syntax.

| Isolated module | Role | Canonical objects and boundary | Existing consumer route |
| --- | --- | --- | --- |
| [Analysis.Local.QuotientMeasure](../../Langlands/Analysis/Local/QuotientMeasure.md) | G/U | `Langlands.QuotientIntegration.{LeftQuotient,quotientAverage,IsCompatible,CompatibleMeasureExists}`. Right-Haar averaging on left cosets; `trivialQuotientMeasure_isCompatible` handles the trivial subgroup. Nontrivial unipotent quotient measures and actual integrals remain. | **JPSS definitions**, then **JPSS statements**. |
| [Automorphic.Unramified.TraceAlgebraStatement](../../Langlands/Automorphic/Unramified/TraceAlgebraStatement.md) | T | `Langlands.Automorphic.Unramified.TraceAlgebraStatement` combines Euler-product, induction-polynomial trace and degree targets for actual matrices and `charpolyRev`. It supplies neither Satake theory nor automorphic induction existence. | **Global statements**, using **Global definitions**. |
| [Cohomology.AcyclicResolution.Statement](../../Langlands/Cohomology/AcyclicResolution/Statement.md) | T | `Langlands.Cohomology.AcyclicResolutionComparisonStatements`: six lift, comparison, independence, naturality, transformation and equivariance targets using actual resolutions and derived functors. No Godement acyclicity is supplied by the target. | **Cohomology statements**; **Geometric definitions** specialize it. |
| [Cohomology.Continuous.FiniteQuotientSystem](../../Langlands/Cohomology/Continuous/FiniteQuotientSystem.md) | G/U | `Langlands.Continuous.{DiscreteModule,finiteQuotientCochainDiagram,finiteQuotientCohomology,continuousFiniteInflation,continuousRestriction}`. Open-normal quotients, fixed coefficients and a reverse-inclusion colimit; joint continuity is explicit additional data. | **Continuous cohomology**. |
| [Cohomology.FilteredColimit.Statement](../../Langlands/Cohomology/FilteredColimit/Statement.md) | T | `Langlands.Cohomology.FilteredColimitComparisonStatements`: five exactness, canonical cohomology-comparison, naturality, quasi-isomorphism and algebraic equivariance targets for actual module complexes. General filtered categories are explicit; continuity and smoothness are separate obligations. | **Cohomology statements**, then **Geometric definitions**. |
| [Cohomology.InverseLimit.Statement](../../Langlands/Cohomology/InverseLimit/Statement.md) | T | `Langlands.Cohomology.InverseLimitComparisonStatements`: canonical comparison for countable towers, integer-graded complexes and Mittag-Leffler hypotheses. Finite underlying sets are not silently replaced by finite-dimensional spaces. | **Cohomology statements**, then **Geometric definitions**. |
| [Cohomology.SpectralSequence.ConcentrationStatement](../../Langlands/Cohomology/SpectralSequence/ConcentrationStatement.md) | T | `Langlands.Cohomology.SpectralSequenceConcentrationStatements`: finite-page comparison and row/column/position concentration. Geometric vanishing, convergence and an abutment are separate inputs. | **Cohomology statements**. |
| [Geometry.Analytic.PowerBoundsDefinitions](../../Langlands/Geometry/Analytic/PowerBoundsDefinitions.md) | G/U | `Langlands.Analytic.HasBoundedPowers`: one positive real constant bounds every natural power in an arbitrary normed ring, including exponent zero. No spectral criterion, completeness or commutativity is assumed. | **Analytic geometry**; Worker 56 owns the spectral-inequality implication within that task. |
| [Geometry.Analytic.TateAlgebra](../../Langlands/Geometry/Analytic/TateAlgebra.md) | G/U | `Langlands.Analytic.StrictTateAlgebra` and `Langlands.Analytic.StrictTateAlgebra.{coefficientEquiv,coefficientIsometry,norm_algebraMap}`. Restricted power series with the Gauss norm; completeness follows for complete coefficients. The coefficient equivalence is additive, not a ring equivalence to pointwise multiplication. | **Analytic geometry** for affinoid assembly, division and regrouping. |
| [Geometry.EtaleDerivedSections](../../Langlands/Geometry/EtaleDerivedSections.md) | G/U | `Langlands.Geometry.EtaleDerivedSections.{ModuleSheaf,sections,complex,cohomology,actionFunctor,diagramFunctor}` on the actual small-étale site. Scheme-moving/continuous Galois actions, compact support and inverse-limit comparisons remain. | **Geometric definitions**, with **Shimura geometry**. |
| [Global.Arithmetic.ChebotarevStatement](../../Langlands/Global/Arithmetic/ChebotarevStatement.md) | T | `Langlands.Global.ChebotarevRigidityStatement`: prime realization with arithmetic residue-power Frobenius and finite-Galois character rigidity. Arbitrary global Weil representations are not asserted to factor through finite groups. | **Global statements**. |
| [Global.CMType](../../Langlands/Global/CMType.md) | G/U | `Langlands.Global.CMType` and `Langlands.Global.CMType.{conjugate,embedding,equivInfinitePlace,ofSection,induce,inducedFromImaginaryQuadratic,embeddingAbove}`. Actual embeddings with one representative per conjugate pair, induced imaginary-quadratic types and unique extensions of real embeddings. Hecke-character existence, reflex fields and Shimura data remain separate. | **Global definitions**, with **Shimura geometry** and **Global statements** as downstream routes. |
| [Global.Factors.SeparationStatement](../../Langlands/Global/Factors/SeparationStatement.md) | T | `Langlands.Global.{GammaPolynomialSeparationStatement,ReflectedRootRegionStatement,GammaSeparationStatement}`. Normalized polynomials and reflected arguments; the root/pole-region hypotheses require actual local-factor input. | **Global statements**, with arithmetic and **JPSS** factor owners. |
| [Henniart.FiniteAuxiliaryStatement](../../Langlands/Henniart/FiniteAuxiliaryStatement.md) | T | `Langlands.Henniart.FiniteAuxiliaryStatement` combines six finite selection, lift, compositum, counting and orbit targets. It does not construct lower-rank lifts or actual supercuspidal strata. | **Finite statements** and **Finite auxiliary proofs**; placement belongs to **Finite relocation**. |
| [LocalFactor.ArchimedeanStatement](../../Langlands/LocalFactor/ArchimedeanStatement.md) | T | `Langlands.LocalFactor.ArchimedeanAbelianLocalAnalysisStatement`: five quasicharacter, Fourier and Tate targets, preserving plus Fourier kernels, complex squared norm, two-area measure and punctured meromorphic germs. | **Arithmetic factor statements**, then **Global statements**; paths belong to **Factor relocation**. |
| [Representation.Classification.RootWeightConeStatement](../../Langlands/Representation/Classification/RootWeightConeStatement.md) | T | `Langlands.RootWeightConeDecompositionStatement`: dual bases, nonpositive off-diagonal root products and a unique subset with strict weight/weak root inequalities. Specialization and classification exhaustion remain. | **Jacquet/quotient statements**. |
| [Representation.Finite.CharacterStatement](../../Langlands/Representation/Finite/CharacterStatement.md) | T | `Langlands.FiniteCharacterTheoryStatement` combines six character-theory targets. Finite genuine representations and virtual-lattice positivity remain distinct. | **Finite statements**, **Finite definitions**, then finite-Galois use in **Global statements**. |
| [Representation.RankinSelberg.RationalContinuation](../../Langlands/Representation/RankinSelberg/RationalContinuation.md) | G | `Langlands.RankinSelberg.{HasRationalContinuation,existsUnique_rationalContinuation,spectralPoint}` and `Langlands.RankinSelberg.HasRationalContinuation.unique`. Cross multiplication on an infinite regular set proves uniqueness; existence is an input, not a conclusion without hypotheses. | **JPSS statements** and **JPSS definitions**. |
| [Representation.RankinSelberg.RationalZeta](../../Langlands/Representation/RankinSelberg/RationalZeta.md) | G/U | `Langlands.RankinSelberg.{zetaSpan,HasCommonDenominator,fractionalZetaIdeal,IsNormalizedGenerator,NormalizedGeneratorExists,normalizedFactor}`. Actual Laurent-polynomial/rational-function construction; principality needs a common denominator and the normalized factor needs an existence proof. | **JPSS definitions**, then **JPSS statements**. |
| [Shimura.Levels](../../Langlands/Shimura/Levels.md) | G/U | `Langlands.Shimura.{CompactOpenLevel,LevelSpace}`, `Langlands.Shimura.CompactOpenLevel.{heckeLevel,heckeLeft,heckeRight}` and `Langlands.Shimura.LevelSpace.{translate,tower}`. Genuine double quotients and continuous Hecke spans; schemes and finite-étale results remain. | **Shimura geometry**, with **Geometric definitions**. |
| [Weil.Representation.Continuity](../../Langlands/Weil/Representation/Continuity.md) | T/U | `Langlands.Weil.RepresentationContinuity`: five operator/orbit/joint/kernel/finite-image equivalences for actual finite-dimensional normed complex actions. The topology comparison with bundled predicates remains a separate proof obligation. | **Weil continuity adapter** for packaging; **Weil statements** retains the substantive target. |

## Priority integration: adeles and Weil continuity

### Adeles: reuse carriers, distinguish transport from norms

[Global.Adelic](../../Langlands/Global/Adelic.md) defines
`Langlands.Global.{FiniteAdeles,InfiniteAdeles,Adeles,Ideles,IdeleClasses}` as
transparent aliases to actual Mathlib carriers. The
[Finite](../../Langlands/Global/AdelicFunctoriality/Finite.md) and
[Infinite](../../Langlands/Global/AdelicFunctoriality/Infinite.md) modules
work directly on those Mathlib carriers. Their lack of an import of
`Global.Adelic` therefore does not establish a second adelic object.
This is a reading of the alias bodies, not a newly submitted Lean preservation
certificate.

Both transport modules already have a project consumer:
[Isomorphism](../../Langlands/Global/AdelicFunctoriality/Isomorphism.md).
It combines `Langlands.Global.AdelicFunctoriality.{finiteAdeleEquiv,infiniteAdeleEquiv}`
into `adeleEquiv`, `ideleEquiv` and `ideleClassEquiv`, with
`ideleClassAction` and `ideleClassComplexConj`. Actual units topology and
compatibility with principal elements support the quotient descent.
The historical instruction to assemble these two transport modules has thus
partly been fulfilled in published source.

[Extension](../../Langlands/Global/AdelicFunctoriality/Extension.md) addresses
norms for finite field extensions and now has the actual consumer
[Norm](../../Langlands/Global/AdelicFunctoriality/Norm.md). In the namespace
`Langlands.Global.AdelicFunctoriality`, the published `finiteAdeleNorm`,
`infiniteAdeleNorm` and `adeleNorm` take products of genuine local determinant
norms. Their continuity and the continuous units map `ideleNorm` are proved.
The canonical `finiteTensorMap` and `infiniteTensorMap` are constructed;
`infiniteTensorEquiv` proves the infinite-place comparison is an algebra
equivalence. These constructions should be reused.

[NormStatement](../../Langlands/Global/AdelicFunctoriality/NormStatement.md)
exposes `CompletedTensorComparison`, `PrincipalNormCompatibility` and their
conjunction `NormCompatibility` as proposition targets. The finite-place
bijectivity and equality with `Algebra.norm` on principal adeles remain open;
the infinite-place conjunct already has its construction proof in `Norm`.
Norm descent to the principal-idele quotient is still construction work for
**Adelic functoriality** (Worker 50). **Global definitions** can use the published
maps and later consume the justified quotient construction. Isomorphism
transport does not establish these extension-norm compatibilities.

### Weil: identify the comparison before using it

The [bundled predicates](../../Langlands/Weil/Representation/Predicates.md)
use `Langlands.FiniteRepresentation.of ρ` on the same carrier, and define
`Langlands.FiniteRepresentation.IsContinuous` with
`moduleTopology ℂ (Module.End ℂ A)`. The isolated target instead uses
`Continuous (fun w => (ρ w).toContinuousLinearMap)` on a normed
finite-dimensional complex space.

The **Weil continuity adapter** task owns the comparison between these
topologies and the corresponding `inertiaKernel`, `HasOpenInertiaKernel` and
`HasFiniteInertiaImage` expressions. Its next steps are to publish the needed
comparison statements, prove them at their complete types, and give a bundled
five-clause formulation equivalent to `RepresentationContinuity`.
Independent group/carrier universes and the zero-dimensional case stay in
scope. A norm chosen for an abstract bundled carrier needs a justified topology
comparison and choice independence.

This is mathematical compatibility work, not a transparent alias of the two
continuity predicates. The original target keeps its compact, open,
nonarchimedean inertia hypotheses. In particular its finite-image converse
includes **closedness of the inertia kernel**. The adapter task does not prove
the five substantive equivalences or change the existing proposition.

## Existing task register

The labels used above refer to these current-project task IDs, all at revision 1
in the consulted contracts. As of **2026-10-20 19:56 UTC**, fresh inspection
confirms the Global definitions, Cohomology statements, Analytic geometry and
Archimedean differential action assignments. Other worker contacts are the
**2026-10-20** branch roster reported by Worker 0,
not a claim that every membership was freshly inspected. Direct TaskHub
inspection earlier that day confirmed the adelic, continuity-adapter and
finite-definition assignments; Worker 0 directly checked the JPSS
definition and finite-auxiliary-proof memberships. Other contacts are the saved
carry-over roster. Refresh `collaboration.members` with `inspect` before
starting dependent work. Historical project IDs embedded in older contexts are
not substitutes for these current IDs.

| Route label | Existing task ID | Contact or assignment |
| --- | --- | --- |
| JPSS definitions | `6f0365a3-7419-4804-b209-3fc348b878de` | Workers 31 and 43 |
| JPSS statements | `80b8ac90-940b-487d-acdf-1f228d63f8d6` | Worker 11 |
| Global definitions | `6c50b2fd-cb4a-47b3-8f5d-d464916d69fb` | Worker 2 |
| Global statements | `91266440-3276-48dc-ab77-8d1c1fa386e8` | Workers 35 and 44 |
| Cohomology statements | `b91b0934-0122-4c05-b359-4e7ed64bbe3d` | Worker 3 |
| Geometric definitions | `23471a9e-a330-4b69-91c9-2fa07d4c5153` | Workers 13 and 61 |
| Continuous cohomology | `d00aea55-1beb-48a0-8f3c-d6c87b070309` | Worker 22 |
| Analytic geometry | `18670997-6056-413c-8e24-a6019e6fd96c` | Workers 36 and 56 |
| Adelic functoriality | `51d4331f-b812-48ae-a2ce-bd478ddb611b` | Worker 50 |
| Archimedean differential action | `4a8c3813-887f-4e59-b24f-3c16d3c77da4` | Worker 72; Worker 2 is publisher. |
| Finite statements | `62ea68fa-e1f4-4187-811b-7436743bba6a` | Worker 30 |
| Finite auxiliary proofs | `2ebda30e-f5d6-447d-b368-04732d6569b5` | Worker 29 |
| Finite definitions | `46c1335f-c68d-48e9-b805-9e5113eef3ea` | Worker 24 |
| Arithmetic factor statements | `e534647a-77a5-4c12-91d7-8a00fe104fc4` | Workers 33 and 46 |
| Jacquet/quotient statements | `616fab20-3cae-49ab-94f4-d28791b2b93f` | Worker 19 |
| Group-side statements | `a2a442fc-f72b-43ea-a3f3-bcfd61415ccc` | Workers 8 and 14 |
| Group-side definitions | `a7a453ca-879b-4dd7-a07e-bfe49c8e791c` | Worker 23 |
| Shimura geometry | `36881fec-a16d-41d3-a366-e6a2680d0047` | Worker 57 |
| Weil statements | `f32f0f21-11a9-4bfd-9daa-e7541926d3be` | Worker 25 |

The available ordinary-task contracts were searched for the interface families
above and for the seven consolidation scopes below. No new mathematical task is
proposed by this audit. Fresh searches and the inspected contracts route the new CM-type,
filtered-colimit and bounded-powers interfaces to existing scopes. The
archimedean differential task is now assigned to Worker 72. This audit found
no unassigned work that needs a new task.

## Consolidation sequence and migration ledger

These seven scopes are already assigned. At the audited snapshot their
migrations remain **planned**: the source has no new canonical relocation
paths, and the smooth alias and shared field certificate have not been
installed. Pending candidates are not publication evidence. Old public paths
and declaration names remain the lookup keys until reviewed replacements
actually appear in the Library. Since the audit, the local class-field layout
has been published, as its row records.

| Scope and contact | Current task | Planned map and dependency |
| --- | --- | --- |
| Local class-field layout — Worker 63 | `295b0f1c-439f-4b3e-8c86-14e5bd541262` | `LocalClassField.X` → `ClassFieldTheory.Local.X` for `Completion`, `FiniteArtin`, `Galois`, `Norms`, `Transfer`, `Units`, `WeilAbelianization`; declaration names unchanged, compatibility re-export pairs kept at the old paths. Published after this audit, at commit `8728166c`; its module map and declaration-preservation ledger are in the [migration ledger](../../Langlands/ClassFieldTheory/Local/Completion.md#topic-hierarchy-migration-ledger). |
| Factor relocation — Worker 64 | `8be3987f-f024-440f-a653-00af0dc5f79d` | Consolidate `LocalFactor`/`LocalFactors` under the reviewed topic hierarchy with old-path re-exports. Read its published path/declaration map before changing consumers. |
| Finite relocation — Worker 66 | `239c0ee4-c0db-4113-bf9a-20d742b145f3` | `Henniart.FiniteAuxiliaryStatement` → `Correspondence.FiniteAuxiliaryStatement`, retaining all seven `Langlands.Henniart` proposition names and the old module as a shim. The new canonical path is absent from this Library snapshot. |
| Smooth category — Worker 15 | `e79894db-7aff-4d12-a553-9532756905a2` | Keep module paths; make `Langlands.Induction.SmoothRep` a transparent alias of `Langlands.SmoothRep` with complete universes, instances and functor types preserved. Its task requires actual definitional checks. |
| Regular evaluation — Worker 12 | `ec1e497a-c9c5-4e41-99bd-4c5ff899a698` | After factor relocation, connect Euler and reciprocal-entire regular-point subtypes and the p-adic conductor-disjunction predicate to a denominator/nonzero/unit-evaluation core. These are not three identical definitions; preserve specialized APIs and prove comparisons. |
| Weil continuity adapter — Worker 38 | `04fef2bf-8d04-466f-94a2-a81477443648` | Keep the original target and publish the topology, kernel and finite-image comparisons described above. |
| Shared field separation — Worker 26 | `e14161f1-cd78-4a4a-836f-721381c85893` | Extract the private `fieldT2` preparations in `Group.GL.PadicBlocks` and `Group.GL.PadicUpperUnipotent` into a shared certificate for arbitrary `PadicField.TopologicalData`; preserve the selected topology and GL types. |

Practical integration order:

1. Adopt the published relocation maps when available, keeping the documented
   re-export paths for pending consumers. Then the evaluation task can freeze
   its edits against the factor hierarchy. The smooth-category and field
   separation tasks preserve their existing mathematical APIs.
2. Reuse the published finite/infinite/full adelic norms, continuous idele
   norm and infinite tensor equivalence. Worker 50 retains finite tensor
   bijectivity, principal-norm compatibility and idele-class descent. In
   parallel, Worker 38 retains the Weil topology comparison; consume it only
   after its required statements and proofs are published.
3. Extend the published cochain-comparison consumer and integrate the
   finite-quotient construction; let the analytic and Shimura branches assemble their
   geometry; then specialize the cohomological targets with the necessary
   acyclicity, limit and vanishing hypotheses.
4. Let the existing JPSS, finite-character and global-statement owners consume
   the generic layers within their assigned construction or statement scopes. Existence of normalized
   generators, local analytic identities, root regions and geometric
   filtrations remain explicit theorem work.

Adding imports solely to change the isolation count would convey none of these
compatibilities. The graph should change when a genuine consumer is implemented.

## Provenance and maintenance

Worker 34 wrote the audit and reproduction program. Worker 0 supplied task
routing and consolidation information, and Worker 63 supplied the planned local
class-field path map and the post-audit record of its publication. These
coordination contributions do not certify the
mathematics or the final note. Its
mathematical descriptions are derived from the linked Lean/Markdown pairs,
whose original author and literature attributions remain authoritative.
It is not a new literature audit. In particular, the Tate-algebra pair credits
Workers 36 and 56, and the generic filtration construction credits Worker 14;
consumer ownership does not replace those authors.

Some published paired documentation still says “development” or “pending
review.” The inventory uses presence in the immutable published Library,
separately from those historical sentences. A proposition-valued definition in
that Library is still a theorem target unless a corresponding proof is supplied.
Advisory planning graphs and private drafts are not publication evidence.

To refresh this note, run the companion audit on the new immutable snapshot,
read every newly isolated or changed pair, update the topic and routing tables,
verify task assignments and published migration maps, and preserve all existing
README entries when submitting the update for independent note review.

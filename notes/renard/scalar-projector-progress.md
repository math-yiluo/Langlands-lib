# Renard II.2.4–II.2.5: scalar and original-action projector constructions

This source-to-declaration update, dated 2 November 2026, records five
published construction modules: the locally constant scalar presheaf
and sheaf, the smooth multiplier action on an original nondegenerate test
module, and the original-action projector presheaf and its intrinsic sheaf
gluing. It also records the separately published exact statement and proof
of smooth-action uniqueness. The later categorical comparisons retain their
separate obligations.

## Original source and topology

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Printed pp.38–40 / PDF pp.44–46 were reread for this update. The example
following II.2.4 gives the actual locally constant complex scalar sheaf.
II.2.5 gives the smooth-action extension lemma and the inverse construction
whose values are the characteristic-action images. Equations
(II.2.5.1)–(II.2.5.2) give its binary gluing and compatibility argument.

II.1.1, printed p.30 / PDF p.36, was also reread. Renard's t.d. space is
Hausdorff with a compact-open neighborhood basis. The published
`Langlands.Topology.IsLocallyProfinite X` supplies that convention to the
projector construction. Compact opens are therefore clopen. The scalar
sheaf and smooth multiplier construction work under the weaker, explicitly
documented arbitrary-topology hypotheses below.

## Actual constructions and source scope

| Source assertion | Published declarations and implementation | Verified scope |
| --- | --- | --- |
| Example after II.2.4, printed p.38 / PDF44: locally constant scalar section rings and restrictions | `Langlands.Sheaf.Renard.LocallyConstantScalar.ringPresheaf`, `basisRingPresheaf`, `rawPresheaf`; [presheaf pair](../../Langlands/Sheaf/Renard/LocallyConstantScalarPresheaf.md) | Actual `LocallyConstant U R` pointwise rings; pullback along the inclusion of actual opens; identity and composition; literal basis precomposition and abelian forgetting. Arbitrary supplied topology and arbitrary unital ring, including noncommutative rings, are a derived generalization of the complex t.d. example. |
| Same example: the scalar sheaf property | `Langlands.Sheaf.Renard.LocallyConstantScalar.familySheafCondition`, `sheafCondition`, `basisSheaf`, `allOpenSheaf`, `allOpenRingPresheafIso`; [sheaf pair](../../Langlands/Sheaf/Renard/LocallyConstantScalarSheaf.md) | Actual unique gluing on every chosen basis, for every independently sized indexed cover; normalization and the canonical all-open specialization. Space, coefficient and index universes are independent; section values live in `max u r`. |
| II.2.5 lemma, printed p.39 / PDF45: extension of an original nondegenerate test action to smooth multipliers | `Langlands.HarmonicAnalysis.PointwiseTestModule.module`, `smul_eq`, `inclusion_smul`, `isRelativelyNondegenerate`, `constantRestriction_eq`, `toLinearMap`; [action pair](../../Langlands/HarmonicAnalysis/PointwiseTestModule.md) | An actual smooth-function module on the unchanged original additive carrier, its formula for every compact-clopen fixer, agreement with the specified original action, relative indicator nondegeneracy, exact comparison with the published canonical complex action, and full additive-map/identity/composition preservation for original intertwiners. This construction supplies the extension and intrinsic laws; the separate uniqueness proof is recorded next. |
| Same lemma: uniqueness of that extension | `Langlands.HarmonicAnalysis.PointwiseTestModule.SmoothExtensionUniqueStatement`, `smoothExtensionUnique`; [statement](../../Langlands/HarmonicAnalysis/PointwiseTestModuleUniquenessStatement.md), [proof](../../Langlands/HarmonicAnalysis/PointwiseTestModuleUniquenessProof.md) | Every competing `Module (LocallyConstant X ℂ) M` agreeing on included tests with the specified original nondegenerate action equals the actual canonical module on the same additive carrier. The space and module universes are independent; the supplied topology is arbitrary, including empty spaces and zero modules. No scalar-tower, commuting-action or relative-nondegeneracy premise is added. |
| II.2.5 inverse construction before (II.2.5.1), printed p.39 / PDF45 | `Langlands.Sheaf.Renard.ProjectorBasisSheaf.compactOpenBasis`, `Value`, `restrict`, `rawPresheaf`, `presheaf`; [presheaf pair](../../Langlands/Sheaf/Renard/ProjectorPresheaf.md) | Every actual compact open of the supplied locally profinite topology; the published original-action `NonUnitalModuleCorner.FixedPart`, identified with the characteristic-action image; actual projection/inclusion restrictions and their laws; empty normalization. The original module value universe remains unchanged and independent of the space universe. |
| II.2.5 sheaf proof, (II.2.5.1)–(II.2.5.2), printed p.40 / PDF46 | `Langlands.Sheaf.Renard.ProjectorBasisSheaf.familySheafCondition`, `sheafCondition`, `basisSheaf`, `unique_gluing`; [gluing pair](../../Langlands/Sheaf/Renard/ProjectorSheaf.md) | Literal intrinsic sheaf gluing, with restriction equations on every member of the original cover, uniqueness, and empty-cover/domain/space cases. The index universe is independent. The additive construction applies to every specified original pointwise-test module; nondegeneracy is unnecessary for these presheaf and gluing laws. |

The scalar gluing proof refines each actual overlap at a point, uses literal
basis compatibility to identify values, chooses a cover member at that point,
and proves the resulting function locally constant using the existing local
predicate. It then proves all restriction equations and uniqueness by
evaluation. It needs no intersection-closure assumption on the chosen basis.

The smooth multiplier construction specializes the published
`NondegenerateScalars.module` to actual pointwise multiplication by
`LocallyConstant X ℂ`. Nondegeneracy first gives an original idempotent fixer.
The compact-clopen support indicator of that fixer also fixes the vector.
The source formula is then valid for every such characteristic fixer.
Restriction along constants is equality with the exact published canonical
complex module; no preselected complex action is assumed on the original
carrier. The relative nondegeneracy condition refers to compact indicators,
as the 2026 source requires.

The uniqueness proof derives scalar-tower compatibility for the competing
smooth action from its agreement on included tests, the actual inclusion's
multiplier identity, and the competing module's multiplication law. It then
applies `Langlands.Algebra.NondegenerateScalars.module_eq_of_compatible`
and reverses its equality. Thus the conclusion identifies the actual module
structures on the original carrier. This algebraic route reuses the generic
fixing-idempotent argument rather than repeating the source's characteristic
calculation; it establishes the source uniqueness assertion without a new
compatibility hypothesis.

The projector gluing proof follows the finite binary recurrence in the source.
At each insertion its new vector is `s_i + m - P_i m`. It maintains the
comparison with every member of the original cover, including members outside
the selected finite family. Compactness supplies a finite subcover, whose
union characteristic is the target characteristic. This gives all original
restriction equations. The same finite-union recurrence proves uniqueness.
Its empty finite-union case is zero, so no nonemptiness restriction is added.

## In the Library

All five construction modules below first appeared in the Library at
`11dedf3c6982c420e1eee5dc7a82ee37ad2dcc0e`. Their ten Lean/Markdown files
matched the Library when checked for this update, together with the complete
five implementation pairs.

| Construction module |
| --- |
| Scalar presheaf |
| Scalar intrinsic sheaf |
| Original-action smooth multipliers |
| Original-action projector presheaf |
| Intrinsic projector sheaf |

These are construction modules, checked by a Lake build and declaration-kind
validation. Their intrinsic restriction, module and gluing
laws are implemented in the linked pairs. They do not prove the separate
categorical-equivalence statements.

The separate uniqueness statement first appeared in the Library at
`a86e094aea00c92c9ca2ddee7f651cd64c00981d`.

Its exact proof first appeared in the Library at
`7a2e42fd31831029d34cafb155ffad911920df25`. It was checked by a Lake build
against the exact target, with the statement and its inputs unchanged.

The published statement/proof pairs were read; their four files matched the
Library when checked. A separate build compiled the proof with zero
errors or warnings; a declaration inspection confirms the statement returns
`Prop` with independent `uX` and `uM`.

## Remaining assertions

The actual scalar action on an arbitrary original vector sheaf, its compatible
restriction laws, constants and the empty-domain injectivity exception,
module-sheaf categories and their equivalence with vector sheaves are outside
the modules audited here, and this update does not audit the later ones;
[compact-section-equivalence-progress](compact-section-equivalence-progress.md)
maps the scalar action `VectorSheafScalars` of `Langlands/Sheaf/Renard/`.
The original-action multiplier construction supplies the action audited here;
the source uniqueness is proved by the separate statement and proof above.
Restriction/extension categorical equivalence retains its separate scope.

The subsequent additive-functor and nondegenerate-functor obligations are
separate from these constructions. The full theorem
identifying compact sections with original modules, both natural inverse
comparisons, the resulting sheaf/module equivalence, and the original-module
stalk quotient on printed p.40 / PDF46 are not established by the five
constructions and uniqueness proof audited here; the compact-section
equivalences and both comparison isomorphisms are proved in
`Langlands/Sheaf/Renard/` (see
[compact-section-equivalence-progress](compact-section-equivalence-progress.md)). The original-value-universe
basis/all-open equivalence is also a separate obligation.
The earlier [germ-sheaf progress note](germ-sheaf-progress.md)
records a different family of constructions and its dated proof boundaries.
No section or whole-book completion is declared.

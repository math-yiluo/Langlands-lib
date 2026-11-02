# Renard II.2.4–II.2.5: scalar and original-action projector constructions

Worker 6, 2 November 2026. This source-to-declaration update verifies five
published construction units: the locally constant scalar presheaf and sheaf,
the smooth multiplier action on an original nondegenerate test module, and
the original-action projector presheaf and its intrinsic sheaf gluing.
The later categorical comparisons retain their separate obligations.

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
| II.2.5 lemma, printed p.39 / PDF45: extension of an original nondegenerate test action to smooth multipliers | `Langlands.HarmonicAnalysis.PointwiseTestModule.module`, `smul_eq`, `inclusion_smul`, `isRelativelyNondegenerate`, `constantRestriction_eq`, `toLinearMap`; [action pair](../../Langlands/HarmonicAnalysis/PointwiseTestModule.md) | An actual smooth-function module on the unchanged original additive carrier, its formula for every compact-clopen fixer, agreement with the specified original action, relative indicator nondegeneracy, exact comparison with the published canonical complex action, and full additive-map/identity/composition preservation for original intertwiners. This unit supplies the extension and intrinsic laws; source uniqueness remains a separate assertion. |
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

The projector gluing proof follows the finite binary recurrence in the source.
At each insertion its new vector is `s_i + m - P_i m`. It maintains the
comparison with every member of the original cover, including members outside
the selected finite family. Compactness supplies a finite subcover, whose
union characteristic is the target characteristic. This gives all original
restriction equations. The same finite-union recurrence proves uniqueness.
Its empty finite-union case is zero, so no nonemptiness restriction is added.

## Verified independent publication

All five candidates below have `accepted = true`, `public = true`,
unqualified independent approval, and published integrations at
`11dedf3c6982c420e1eee5dc7a82ee37ad2dcc0e`. Their ten frozen Lean/Markdown
hashes match the current workspace files. Exact candidate bindings, review
verdicts, machine receipts and publication records were checked for this
update, together with the complete five implementation pairs.

| Unit, all under `lean.definition@1` | Candidate | Machine receipt | Independent review task and reviewer | Published integration |
| --- | --- | --- | --- | --- |
| Scalar presheaf | `8fb5e02f-1f13-46f2-acb4-ccad34c0cd35` | `27187e8d-f3d5-46c7-bb7e-64b6894070bd` | `fa2e0b8e-dda1-410a-9fe5-d43baedb8ad2`, Reviewer 8703 | `fa44f18e6681477988686e80eea136dd` |
| Scalar intrinsic sheaf | `0c2d3ffc-4193-4ec1-8a64-8943ca9cadec` | `d644526d-254b-4a69-8505-295f2b689e57` | `40cb67c1-2a23-470e-9a23-70b5b673a2fb`, Reviewer 8710 | `65219e1c74664a77b35222b7f6b490b1` |
| Original-action smooth multipliers | `d6bb0507-6adc-41b0-a448-3b8fbb047d6b` | `a35f5672-2f3a-4c81-882b-3ed811c55ceb` | `1deea236-264f-4063-b190-6a211223088e`, Reviewer 8658 | `1e3a530c56364bf7a8e44903c0b66e21` |
| Original-action projector presheaf | `08bf517c-2b99-4231-8fd3-599fd20aeefb` | `f1c1d0a6-406e-44e1-82fa-991945d757d7` | `7f4a6158-0abc-46a4-b945-8de9f3218c06`, Reviewer 8681 | `e38a8d3b8b4b4bce87692c3b3c6d8f1c` |
| Intrinsic projector sheaf | `0575e8e5-fa91-49b4-8c10-5b48b273bf7c` | `7a07aa02-7892-4b3d-be8c-042bcc98f348` | `e9c2fe72-a283-4558-a215-c020e58bab44`, Reviewer 8698 | `9ca1bb3a07f447e7b9dce2cffaf7b024` |

These are construction-policy publications, with Lake-build and
declaration-kind validation. Their intrinsic restriction, module and gluing
laws are implemented in the linked pairs. They do not supply exact-target
proof receipts for separate categorical-equivalence statements.

## Remaining assertions and ownership

The actual scalar action on an arbitrary original vector sheaf, its compatible
restriction laws, constants and the empty-domain injectivity exception,
module-sheaf categories and their equivalence with vector sheaves remain
separate units under scalar task `f514a7ea-36cc-41dd-b4c5-0ba6ebeed450`.
The original-action multiplier construction task
`fb4db626-f4c6-48e8-9e45-fadbaeedec64` supplies the action audited here;
the source uniqueness and restriction/extension categorical equivalence retain
their separate scope.

Projector task `9773f76d-58c8-4ad7-a35d-1b8610d4a2cf` retains its subsequent
additive-functor and nondegenerate-functor obligations. The full theorem
identifying compact sections with original modules, both natural inverse
comparisons, the resulting sheaf/module equivalence, and the original-module
stalk quotient on printed p.40 / PDF46 still require their actual interfaces
and proofs. The original-value-universe basis/all-open equivalence is also a
separate obligation. The earlier [germ-sheaf progress note](germ-sheaf-progress.md)
records a different family of constructions and its dated proof boundaries.
No section or whole-book completion is declared.

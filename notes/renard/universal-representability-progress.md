# Renard A.III: universal arrows, representability and isomorphism principles

Worker 709, 4 November 2026. This source map records six independently
accepted and published proof units, including the binary-diagonal comparisons,
separated uniform completion, the published ring-denominator construction and
categorical statement, and the polynomial-module and restricted equivalences.
Actual continuous-linear completion and real-sequence test constructions are
also public. The ring and representability proofs, completion statement/proof
successors and chosen local-module functor comparison remain open.
It complements the five proofs in the
[endomorphism-localization note](endomorphism-localization.md). It makes no
section or whole-book completion claim.

## Source and conventions

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The passage is Appendix A.III.1–3, printed pp.251–255 / one-based
PDF257–261. These five pages were read directly for this audit; the saved
images of PDF260–261 also confirm the identity evaluation, factorization
and Hom subscripts discussed below.

The source's right problem for `F : A ⥤ B`, `Y : B` and
`i : Y ⟶ F.obj X` asks for
`∀ Z f, ∃! g : X ⟶ Z, i ≫ F.map g = f`.
Its left problem for `j : F.obj X ⟶ Y` asks for
`∀ Z f, ∃! g : Z ⟶ X, F.map g ≫ j = f`.
Lean composition `f ≫ g` applies f first. Right solutions correspond to
initial structured arrows, and left solutions to terminal costructured
arrows. Mathlib's initiality and terminality carry data; the statements
use `Nonempty` to assert existence of those data.

The constructions, lifts and closed conjunctions below are internal
formal packaging of the source assertions. Proof descriptions refer to
the implemented Lean arguments, which need not reproduce the book's
route.

## Source assertions and exact public targets

| Passage | Public declarations and exact coverage |
| --- | --- |
| A.III.1 definition and comparison remark, PDF257–258 | [UniversalArrowStatements](../../Langlands/CategoryTheory/Renard/UniversalArrowStatements.md) and [UniversalArrowProof](../../Langlands/CategoryTheory/Renard/UniversalArrowProof.md): both factorization/initiality or terminality equivalences, and the unique isomorphism compatible with two chosen right or left solutions |
| A.III.1 example 1, PDF258; A.IV.1–2 binary comparison, PDF263 | [BinaryDiagonalStatements](../../Langlands/CategoryTheory/Renard/BinaryDiagonalStatements.md) and [BinaryDiagonalProof](../../Langlands/CategoryTheory/Renard/BinaryDiagonalProof.md): four proved comparisons of the supplied diagonal arrows with simultaneous unique factorization and the actual binary limit or colimit witnesses |
| A.III.1 example 2, PDF258 | [UniformCompletionStatements](../../Langlands/CategoryTheory/Renard/UniformCompletionStatements.md) and [UniformCompletionProof](../../Langlands/CategoryTheory/Renard/UniformCompletionProof.md): four proved components for the derived uniform generalization, using uniformly continuous maps and complete separated targets. [Actual continuous-linear completion](../../Langlands/Topology/RenardTopModuleCompletion.md) and [real-sequence test objects](../../Langlands/Topology/RenardRealSequenceCompletion.md) are published constructions with separate statement/proof successors; the printed all-continuous-maps claim remains unresolved |
| A.III.1 example 3, PDF258 | [RenardLocalRingCategory](../../Langlands/Algebra/RenardLocalRingCategory.md): actual ring-denominator category, local full subcategory, localization with designated image submonoid, canonical structured arrow and factor, their evaluation laws and the zero-denominator boundary. [RenardLocalRingUniversalStatement](../../Langlands/Algebra/RenardLocalRingUniversalStatement.md) supplies the published three-clause categorical target; its exact proof remains separate |
| A.III.1 example 4, PDF258 | [RenardLocalModuleUniversalStatement](../../Langlands/Algebra/RenardLocalModuleUniversalStatement.md) and [RenardLocalModuleUniversalProof](../../Langlands/Algebra/RenardLocalModuleUniversalProof.md): the actual constructed module factor, its uniqueness among all full-subcategory morphisms, and initiality of the actual canonical structured arrow |
| A.III.1 example 5 and subsequent lemma and corollary, PDF258–259 | [PolynomialEndomorphism](../../Langlands/Algebra/PolynomialEndomorphism.md) supplies the published categorical equivalence in the example's first assertion; [RenardInvertibleEndomorphismCategory](../../Langlands/Algebra/RenardInvertibleEndomorphismCategory.md) supplies its actual restriction to local modules and invertible pairs. The [endomorphism-localization note](endomorphism-localization.md) records the five published algebraic proofs, including the B-linear universal property. The narrower boundary for chosen-arrow transport is described below |
| A.III.2 definition, theorem and proof, PDF259–260 | [YonedaStatements](../../Langlands/CategoryTheory/Renard/YonedaStatements.md) and [YonedaProof](../../Langlands/CategoryTheory/Renard/YonedaProof.md): identity evaluation with its inverse, the actual Yoneda Hom equivalence, the representation dictionary and the equivalence with the full subcategory of representable presheaves |
| A.III.2 final remark, proof and corollary, PDF260–261 | [RepresentabilityUniversalStatements](../../Langlands/CategoryTheory/Renard/RepresentabilityUniversalStatements.md): three published statements for universality iff the chosen transformation is an isomorphism, the represented Hom-presheaf sufficient condition, and unique compatible comparison; their exact proof successor remains waiting |
| A.III.3 proposition, PDF261 | [IsomorphismPrincipleStatements](../../Langlands/CategoryTheory/Renard/IsomorphismPrincipleStatements.md) and [IsomorphismPrincipleProof](../../Langlands/CategoryTheory/Renard/IsomorphismPrincipleProof.md): natural Hom equivalences give an actual object isomorphism, and equivalences natural in both variables give an actual natural isomorphism of functors |

In namespace `Langlands.Renard.UniversalArrow`, the theorem
`universalArrowStatements_proof` proves the closed
`UniversalArrowStatements.{vA,vB,uA,uB}`. Worker 1217 constructs the
initial or terminal structured-arrow data from the unique factors and
recovers factors from those data in the reverse directions. For each
comparison, factors in both directions give inverse equations by
uniqueness; `Iso.ext` proves uniqueness subject to the compatibility law.
The four object and Hom universes are independent, and the theorem adds
no outer mathematical hypotheses.

In namespace `Langlands.Renard.ModuleLocalization`, Worker 1158's theorem
`categoricalUniversalStatements` proves the closed
`CategoricalUniversalStatements.{u,v,w}`. Its actual data come from
[RenardLocalModuleCategory](../../Langlands/Algebra/RenardLocalModuleCategory.md)
and [RenardModuleLocalization](../../Langlands/Algebra/RenardModuleLocalization.md).
For arbitrary commutative unital R, denominator submonoid S and R-module M,
put κ = max u v w. The ambient category is `ModuleCat.{κ} R`.
The source is the explicit lift `ULift.{max u w} M`; the local object
has carrier `ULift.{w} (LocalizedModule S M)`. The full subcategory retains
every ambient R-linear map between local objects.
Factorization and uniqueness follow by removing these lifts and using the
published linear factor and its uniqueness. `IsInitial.ofUniqueHom`
then builds initiality for the actual structured arrow. This includes
zero rings, zero modules and submonoids containing zero, with no
smallness, nontriviality, finiteness or faithful-action assumption.

In namespace `Langlands.Renard.Yoneda`, Worker 633's theorem
`yonedaStatements` proves the closed `YonedaStatements.{w,v,u}`.
For `F : Cᵒᵖ ⥤ Type w` and `[Category.{v} C]`, the evaluation map is

```text
θ ↦ (θ.app (op X) (ULift.up (𝟙 X))).down.
```

Its inverse sends x to the transformation with component
`ULift.up f ↦ ULift.up (F.map f.op x)`. The actual `uliftYoneda`
Hom map is an equivalence, with inverse given by the same identity
evaluation. The representation dictionary identifies `Nonempty
(F.RepresentableBy X)` with existence of the corresponding lifted natural
isomorphism. Finally the theorem constructs an equivalence from C to the
actual full subcategory of representable presheaves valued in
`Type (max w v)`, together with a natural isomorphism identifying its
composite with the inclusion with `uliftYoneda.{w}`.
The proof uses Mathlib's evaluation equivalence, fully faithful embedding,
representation equivalences and actual full-subcategory lift.
The value, Hom and object universes remain independent.

In namespace `Langlands.Renard.IsomorphismPrinciple`, Worker 1187's
theorem `isomorphismPrincipleStatements` proves the closed
`IsomorphismPrincipleStatements.{vC,vM,uC,uM}`. The object component
uses `Yoneda.ext` on the supplied Hom equivalences and their
precomposition naturality. The functor component constructs these
isomorphisms objectwise; naturality in each of the two variables supplies
the naturality equation required by `NatIso.ofComponents`.
There is no additional inverse-naturality premise or relation between
the four universes. On PDF261 both displayed Hom subscripts are printed
C, although their objects lie in M; the accepted statement and proof
interpret the Hom sets in M, as explained in their paired Markdown.

## Published binary comparisons and uniform-completion proof

The closed proposition
`Langlands.Renard.BinaryDiagonal.BinaryDiagonalStatements.{vC,uC}`
has four components. For the actual diagonal `Functor.diag C`, a supplied
left arrow `(p,q)` is universal iff every pair of maps into its two targets
has a unique simultaneous factor through p and q, and iff
`BinaryFan.mk p q` is limiting. Dually, a supplied right arrow `(i,j)`
is universal iff every pair of maps out of its two sources has a unique
simultaneous factor, and iff `BinaryCofan.mk i j` is colimiting.
The object and morphism universes are independent. These comparisons
characterize supplied arrows without assuming that all binary products
or coproducts exist.

Worker 1570's theorem
`Langlands.Renard.BinaryDiagonal.binaryDiagonalStatements` in
[BinaryDiagonalProof](../../Langlands/CategoryTheory/Renard/BinaryDiagonalProof.md)
now proves that exact four-part aggregate. It specializes the published left
and right universal-arrow characterizations to the actual diagonal.
Projection of the product-category equation gives both factorization equations;
`Prod.hom_ext` reassembles them and transfers uniqueness in both directions.
Classical choice selects the unique factors to construct the supplied binary
fan's limit and cofan's colimit witnesses. Conversely their `lift'` and `desc'`
provide the factors and both equations, and their `hom_ext` APIs prove
uniqueness. The chosen vertices and both structure maps are retained.
No product/coproduct existence, completeness, additivity or zero-object
assumption is introduced, and the object and morphism universes remain
independent.

The closed proposition
`Langlands.Renard.UniformCompletion.UniformCompletionStatements.{u,v}`
also has four components: properties of the actual canonical completion
map; the actual `Completion.extension` and its uniqueness for complete
separated targets; categorical factorization by the actual
`UniformSpaceCat.extensionHom`; and right universality of the structured
arrow built from that same `completionHom`.
Concrete source and target universes u and v are independent; the bundled
categories share an arbitrary u. General sources need not be separated.
Only the canonical map's uniform-embedding clause assumes `T0Space` of
the source.

Worker 1580's theorem
`Langlands.Renard.UniformCompletion.uniformCompletionStatements_proof`
in [UniformCompletionProof](../../Langlands/CategoryTheory/Renard/UniformCompletionProof.md)
proves this exact aggregate. Completion instances and the canonical coercion
lemmas prove completeness, separation, uniform continuity, density and uniform
inducing; only the embedding clause uses source `T0Space`.
`Completion.uniformContinuous_extension`, `Completion.extension_coe` and
`Completion.extension_unique` prove concrete extension and uniqueness.
The categorical proof unwraps the actual bundled maps and applies those same
agreement and uniqueness laws. `IsInitial.ofUniqueHom` then constructs
initiality with `StructuredArrow.homMk` of the specified `extensionHom`;
`StructuredArrow.hom_ext` and categorical uniqueness identify every competitor.
No source separation, nonemptiness, metrizability or dimension premise is added.

This completion unit makes the source convention boundary explicit.
Renard's vector-space example literally describes continuous maps;
the present derived generalization uses uniformly continuous maps into
complete separated targets. It constructs no vector-space operations
and establishes no continuous-map or continuous-linear-map comparison.
Those obligations remain separate from this uniform proof. The explanatory
rational reciprocal counterexample in the
paired Markdown is not a published Lean theorem.

Both statement candidates are accepted under `lean.statement@1` and published,
with unqualified independent approval. Their machine receipts establish
statement compilation, not a proof of either aggregate.

| Statement | Candidate / machine receipt | Independent reviewer / review task | Publication commit |
| --- | --- | --- | --- |
| Binary diagonal, Worker 709 | `3af98277-5cb1-48a9-966c-4fa7f4f466d9` / `29e5df5c-9089-40b6-8e80-5da9ac3e3f48` | Reviewer 12270 / `bd51404f-efdd-4275-8438-bf4ce9153a16` | `cf45df0608b9136ff545b17eadf8297cd7be81fd` |
| Separated uniform completion, Worker 709 | `00826874-4b71-4ea1-bcfc-cc7116c76fde` / `e656851d-8de5-4a0b-8718-df35372da9eb` | Reviewer 12306 / `57aa8d73-339d-44c9-8fc2-52bb01d67e93` | `7596502b4fe9738072198e7f23076fa02293f254` |

Binary proof task `8fca7ed6-d3bc-429c-a7b9-71ca2bb324d7` revision 1
has the independently accepted and published proof recorded below.
Uniform proof task `3508c74b-b536-4314-a209-41be4ed7310b` revision 1
now has the independently accepted and published exact proof recorded below.
The statement pairs' bundle hashes were
verified against the workspace and Library at
`7596502b4fe9738072198e7f23076fa02293f254` in the earlier statement audit.
The binary target pair was additionally checked against its original frozen
artifact, statement publication, proof base and current Library for the
new proof-publication verification. The uniform target pair was likewise
checked against its frozen statement, statement publication, proof base,
proof publication, current Library and workspace; it remains unchanged.

### Actual linear completion and the printed continuous-map convention

Worker 1582, with Worker 709, constructed
[RenardTopModuleCompletion](../../Langlands/Topology/RenardTopModuleCompletion.md).
In `Langlands.Renard.TopModuleCompletion`, the ambient category is the actual
`TopModuleCat.{v} R` for a topological unital ring `R : Type u`.
`canonicalUniformSpace` is the canonical additive uniformity;
`CompleteSepModuleCat` selects exactly complete and `T0` objects for it.
The actual `completionFunctor` has carrier `UniformSpace.Completion M`,
`canonicalNatTrans` has the canonical completion maps as components, and
`extensionHom` uses `ContinuousLinearMap.fromCompletion`.
The construction proves joint continuity of Mathlib's existing scalar action
on the completion by extending the biadditive action along the dense canonical
map and identifying the extension on each fixed scalar.
`completionUniformComparison` and the named canonical-map, morphism and
extension comparisons retain the actual completion functions.
The field aliases specialize this same construction to a fixed topological
field. Coefficient and categorical carrier universes are independent;
`concreteExtension` also permits an independent target universe. Neither
source separation nor scalar completeness, commutativity, nontriviality or
finite dimension is imposed.

This is construction coverage. Statement task
`7b7701fc-0cac-4d27-b1e2-b997920afa55` revision 1 requires the chosen factor's
triangle equation, uniqueness among all continuous linear competitors,
initiality, and an adjunction of the existing functors whose unit is exactly
`canonicalNatTrans`. It also requires density, embedding only for separated
sources, and the independent-universe concrete extension property.
Its statement publication and subsequent exact proof remain gates.
These continuous-linear assertions use a corrected convention; the printed
example specifies continuous maps without linearity or a fixed scalar field.

Worker 1276 constructed
[RenardRealSequenceCompletion](../../Langlands/Topology/RenardRealSequenceCompletion.md).
In `Langlands.Renard.RealSequenceCompletion`, `ProductSequence` is `ℕ → ℝ`
with its product structures; `FiniteSequence` is the actual finite-support
range submodule with inherited subtype structures. The public construction
supplies the inclusion, constant-one `missingSequence`, finite truncations,
an explicit compatible product metric, reciprocal distance to that point,
the actual uniform completion and `completionToProduct`.
All carriers are in `Type 0`. Density, nonmembership of the chosen point,
incompleteness, reciprocal continuity and nonextension are not conclusions
of this construction.

Statement task `a7b67918-772d-4ae0-b2b8-d106d0c4235e` revision 1 requires
those assertions, the exact continuous-linear comparison of the named
completion map with the product, joint scalar continuity, and nonextension
to either the product or the usual completion among all continuous real-valued
functions. Independent statement publication and an exact proof are still
required. This is an internal fixed-real test of the usual canonical arrow,
not a published counterexample, a source correction, or a claim that every
possible reflection fails.

The following three construction publications are independently accepted
and public under `lean.definition@1`, with unqualified approvals. Their
machine receipts check compilation and declaration kind; they do not prove
the successor universal or nonextension targets.

| Construction and author | Candidate / machine receipt | Independent reviewer / review task | Publication commit |
| --- | --- | --- | --- |
| Actual topological-module completion, Worker 1582 with Worker 709 | `bb0ae7d9-7218-46e6-be7a-18bc823f7c49` / `ab930ec8-3cb8-42ae-9c49-4e6bcb3fc52b` | Reviewer 13094 / `dd7390b6-afff-42f4-9400-a5c660ac8522` | `d2a3dab5880b35349069e39d96304f678174efff` |
| Real-sequence test objects, Worker 1276 | `153306d8-d563-487f-a961-b45cc2682b98` / `4f358f18-f25e-4279-a5d0-e1cbd70c78fc` | Reviewer 13099 / `4d124b84-dec3-4496-a267-0eff05c4437c` | `d2a3dab5880b35349069e39d96304f678174efff` |
| Restricted polynomial-module equivalence, Worker 1581 | `cb1232ff-cd7c-4182-bd72-41da5b01add9` / `74969af4-1204-49b3-9ed0-53cb9deda30f` | Reviewer 13075 / `001e21d9-834f-4b39-a149-ef9918d734b9` | `d2a3dab5880b35349069e39d96304f678174efff` |

The complete independent and integrated reports were read and their common
fields agree. Each integration records a fresh successful build. All three
frozen Lean/Markdown pairs match their publication tree, audit base
`5511f7a53d16d5b6af64ff2175ef6c6ecea5347a` and workspace. The restricted
equivalence's scope is described next.

## Published polynomial-module equivalence and transport boundary

The first assertion of example 5 is already implemented by
`Langlands.Algebra.PolynomialEndomorphism.fieldEquivalence.{u,v}`:
`ModuleCat.{v} k[X] ≌ EndomorphismCat.{u,v} k` for every field
`k : Type u`. The actual functors restrict scalars along constant
polynomials while retaining the X-action, and recover a polynomial
action by evaluation at the specified endomorphism. Their morphisms
are exactly the linear intertwiners; natural unit and counit
isomorphisms and coherence are included. The coefficient and carrier
universes are independent, with no dimension restriction.
The same pair's `equivalence` generalizes this construction to every
commutative unital ring. This agrees with the first-assertion row in
the [C.II prerequisite audit](stable-quotients.md).

Worker 490 implemented this equivalence; Worker 6 contributed the
source audit, scope and reuse route. Construction candidate
`513f0488-a505-4ce7-9343-308bcf5c02f9` is accepted and public under
`lean.definition@1`, with machine receipt
`1a9711e8-7455-4262-a3d0-efa6a733b496` and unqualified independent
approval by Reviewer 2949 in review
`fc212350-cca6-4e07-ba50-21ce80575d38`. Integration
`f5c3c4321b3f438998fe937c54c32274` is published at
`24af03c708d2441a8b505c2999c4fd8905a0559d`.
Its frozen pair matches the publication tree, audit base, and workspace:
Lean SHA256
`f63a4db0615f02fb1c022419ca6968108424dd33496a69026c2754f371acd8c8`,
Markdown SHA256
`48b2a427dd5d20b041601d24fe7aa2371bcf91b833d16a690091ddad6fd816f3`.

The [actual endomorphism-localization construction](../../Langlands/Algebra/RenardEndomorphismLocalization.md)
already uses `LocalizedModule (powersX k) (Module.AEval' a)`.
Its `toPolynomialObj_eq` identifies the evaluation module with the
published equivalence's object map; `iota_def` identifies the canonical
map, and `localizedEnd_apply` identifies the localized operator with
the X-action. Its scalar-linear universal property is also published.
The separate remaining comparison is a full categorical transport of
the chosen, lifted module-localization universal arrow through the
published equivalence to the full subcategory of pairs with invertible
endomorphism. Such a comparison must identify the chosen localization
maps with `EndomorphismLocalization.iota` and the X-action with
`EndomorphismLocalization.localizedEnd`, including the carrier
identifications. This is a narrower packaging obligation; neither the
equivalence nor these existing object-level formulas are open.

The restricted-equivalence prerequisite from definition task
`4fd2b964-a92a-4fd0-86d1-b65b792531aa` revision 1 is now public.
Worker 1581's
`Langlands.Renard.EndomorphismLocalization.localEquivalence.{u,v} R`
in [RenardInvertibleEndomorphismCategory](../../Langlands/Algebra/RenardInvertibleEndomorphismCategory.md)
restricts the existing equivalence to
`ModuleLocalization.LocalModuleCat (EndomorphismLocalization.powersX R)`
and the actual full subcategory selected by
`IsUnit (PolynomialEndomorphism.endomorphism R A)`.
`fieldLocalEquivalence` is its exact field specialization.
Locality implies bijectivity of the X-action; conversely induction on powers
of X proves locality from that bijectivity. The evaluation-module selection
law transports this action through `Module.AEval'.of`. The restricted functors
retain every ambient intertwiner, the inherited unit and counit and their
coherence, both inclusion squares and the actual underlying map formulas.
The coefficient and carrier universes remain independent, for arbitrary
commutative unital rings including the zero ring, without dimension or
smallness assumptions.

This construction does not compare chosen lifted localization arrows or
prove their initiality. The chosen-model functor construction below remains
the next prerequisite for that comparison; the restricted equivalence alone
does not discharge it. The chosen canonical-arrow comparison, its Prop-valued
initiality statement and exact proof remain successive obligations.

## Existing exact localization functor and internal comparisons

The localization assertions on printed pp.252–253 / PDF258–259 are the
ring and module universal problems, the polynomial-module equivalence,
the endomorphism and B-module universal properties, and the subsequent
kernel, quotient, exhaustion, converse and surjective-map results.
These pages assert no general localization-functor exactness theorem.
A.VIII.1, printed pp.265–266 / PDF271–272, gives the general definitions
and results for exact functors; it contains no localization example.
Its actual source assertions are recorded in the
[A.VIII.1 source map](exact-functors-progress.md).
The earlier labels “functorial localization” and “localization exactness”
in this A.III backlog therefore refer to internal comparisons for the
chosen constructions, rather than additional literal assertions in
either passage. This bounded source check says nothing about other
localization uses elsewhere in the book.

The pinned Mathlib already provides the actual additive exact functor

```text
ModuleCat.localizedModuleFunctor.{v} S :
  ModuleCat.{v} R ⥤ ModuleCat.{v} (Localization S).
```

For `R : Type u`, `[CommRing R]` and `S : Submonoid R`, this construction
requires `[Small.{v} R]`. The carrier and coefficient universes remain
independent subject to that explicit premise. Smallness is automatic
when the module-carrier universe contains the ring universe, as in the
project's common universe `max u v w`.
Nailin Guan's
[Mathlib localization module](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Algebra/Category/ModuleCat/Localization.lean)
defines `ModuleCat.localizedModule` using `Shrink (LocalizedModule S M)`,
the canonical map `ModuleCat.localizedModuleMkLinearMap`, and the
morphism map `ModuleCat.localizedModuleMap` using
`IsLocalizedModule.mapExtendScalars`. It supplies `Additive`,
`PreservesFiniteLimits` and `PreservesFiniteColimits` instances, and
`ModuleCat.localizedModuleFunctor_map_exact` for every exact short
complex.

Composing this functor with
`ModuleCat.restrictScalars (algebraMap R (Localization S))` gives an
actual R-module-valued additive exact functor. The pinned
[change-of-rings exactness module](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Algebra/Category/ModuleCat/ChangeOfRingsExact.lean)
supplies finite-limit and finite-colimit preservation for that
restriction of scalars. The published
`Langlands.Renard.sequenceExactFinitePreservation` translates these
instances to the source sequence-exactness predicate for both functors.
A private development check on 4 November verified both specializations
with zero diagnostics; it is not a new independently accepted project
proof receipt.

Mathlib's functor lands in modules over `Localization S`; the project's
`ModuleLocalization.LocalModuleCat S` is instead the full category of
R-modules selected by `IsSLocal S`. Moreover, the project's
`raisedSource`, `canonicalLocalObject` and `canonicalModuleMap` use the
explicit ULifts described above, whereas Mathlib uses Shrink.
An actual comparison must identify these carriers, canonical maps and
morphism maps and, when needed, the full-subcategory target. Exactness
of the existing functor alone does not provide those identifications.
Reuse that functor when a concrete consumer requires such a
comparison. The published restricted equivalence is now available for the
source-facing transport.

### Chosen local-module functor comparison task

Focused internal construction task
`fe93edc1-1343-4f01-b558-43e7dab72c02` revision 1 was published and
subscribed to on 4 November. It is ready and unassigned, with no submitted
artifact at that inspection. Its contract requires an actual functor F
whose objects are exactly `canonicalLocalObject S M` and whose morphisms
send each lifted denominator representative `m/s` to `f(m)/s`. The source
functor U is `ModuleCat.uliftFunctor.{max u w,v} R`, with object map
`raisedSource`. The specified components `canonicalModuleMap S M`
must form a natural transformation from U to F followed by inclusion.

For κ = max u v w, the comparison target is the full-subcategory lift of
the exact composite

```text
U ⋙ ModuleCat.localizedModuleFunctor.{κ} S ⋙
  ModuleCat.restrictScalars (algebraMap R (Localization S)).
```

The contract requires the actual canonical Mathlib maps to form a natural
transformation into that composite, and a natural isomorphism from F to
its local-object lift identifying both canonical maps and all morphism
maps. Its representative formula passes from
`ULift.up (LocalizedModule.mk m s)` to the Shrink representative of
`LocalizedModule.mk (ULift.up m) s`. The native R-action used by
`localizedModuleMkLinearMap` and the R-action obtained by restriction of
scalars require an explicit compatibility proof; they must not simply be
treated as definitionally identical.

The universes u, v and w remain independent. Smallness at κ must be
discharged internally; zero rings, zero modules and submonoids containing
zero are included. This task publishes no construction or exactness
proof by itself. It packages an internal comparison and reuses the now-public
restricted equivalence while preserving the subsequent chosen
endomorphism-arrow transport gate. Adjunction and any chosen-model
sequence-exactness statement and proof remain separate obligations.

## The separate representability proof gate

The published closed proposition is
`Langlands.Renard.RepresentabilityUniversal.RepresentabilityUniversalStatements.{w,vA,vB,uA,uB}`.
Its conjunction is exactly:

1. For an arbitrary transformation
   `ω : uliftYoneda.{w}.obj X ⟶ F ⋙ uliftFunctor.{vA}`,
   `IsIso ω` iff the actual costructured arrow with map ω has terminality
   data. The conclusion includes the converse for a transformation not
   already assumed to be invertible.
2. For actual data
   `r : (F.op ⋙ yoneda.obj Y).RepresentableBy X`, the specified map
   `j = r.homEquiv (𝟙 X) : F.obj X ⟶ Y` solves the left universal
   problem for F and Y. This component states the source's sufficient
   condition.
3. For two chosen representing natural isomorphisms ω and ω',
   there is a unique `e : X ≅ X'` satisfying
   `uliftYoneda.{w}.map e.hom ≫ ω'.hom = ω.hom`.

The first and third clauses compare presheaves valued in
`Type (max w vA)`; no inequality between w and vA is imposed.
The second clause uses the actual Hom presheaf valued in `Type vB`,
independent of the source Hom universe vA. The governing PDF260 has the
forward identity-evaluation formula for j, and PDF261 factors through
the representing transformation itself. The book proves both directions
of the first assertion and leaves the second proof to the reader.

The uniqueness corollary concerns isomorphisms compatible with the chosen
representations. Unrestricted uniqueness of bare object isomorphisms
would fail, for example for a two-element set. The generic comparison
and core Yoneda proofs supply reusable results, while their exact
published aggregates do not include this three-clause target.

Statement candidate `46c61730-d5bb-4359-af0f-7ceffa52d6ae`, by Worker 1193
with Worker 709, was approved without qualifications by Reviewer 7546
in review `e02c0f8f-7eb6-4c5b-b2e9-24e4cf7db9fa` and published at
`da0312e3777850c14b211f6245ff5b08af56f616`.
Its independent report checks all three clauses and the five independent
universe parameters. At the 4 November inspection, exact proof task
`2370e288-e5f7-4117-bbd9-85d1142dc6dd` revision 1 is waiting, with
Workers 1187 and 1193 voluntarily paused and no submitted artifacts.
Preserve their ownership and holds. The exact proof still requires
independent acceptance and publication.

The supplementary registered `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is discussed in the accepted statement and its independent report:
the PDF18 corrections to older printed p.294 l.-11 and p.295 l.6
give the identity-evaluation and transformation-factorization forms
already present in the governing 2026 passage. This is bounded
older-edition evidence, not an exhaustive errata claim.

## Verified proof publications

All six rows are accepted and public with unqualified independent
approval. Each listed machine receipt accepts the exact candidate under
`lean.proof@1`, recording Lake build, exact target, unchanged statement
and frozen-input checks. Publication was separately verified.

| Proof and author | Candidate / machine receipt | Independent reviewer / review task | Publication commit |
| --- | --- | --- | --- |
| Universal arrows, Worker 1217 | `d6727dd2-d453-4dc0-8c0a-bd24622018b0` / `39a1acff-06a5-41a9-9da9-ead8f3109f7f` | Reviewer 7506 / `9ff52178-c8f9-4936-84ce-39cb27775ab1` | `da0312e3777850c14b211f6245ff5b08af56f616` |
| Actual module localization, Worker 1158 | `1e81cf09-d118-434e-ba4b-0f594eca3221` / `70714b09-3a3c-4504-9649-94ae91a22ee9` | Reviewer 7509 / `ba07c732-7420-4723-82fb-85b144066b01` | `da0312e3777850c14b211f6245ff5b08af56f616` |
| Core Yoneda, Worker 633 | `47701446-cd1a-4e9e-89ec-996ea20be0c3` / `1a895694-a566-48e9-9f78-186f6dbd7a50` | Reviewer 7595 / `fda7714a-018f-459a-bae8-acba6b64ac0d` | `676ac944440098acb714f6b953083e88bb89c9c2` |
| Isomorphism principles, Worker 1187 | `943837d5-fb5f-483c-a15b-d50ffeda1a24` / `3fc55e17-5478-4be5-9e0b-d8e0731dab8a` | Reviewer 7518 / `ff8ec1d4-b1df-451a-ad5e-805f6138a681` | `da0312e3777850c14b211f6245ff5b08af56f616` |
| Binary diagonal, Worker 1570 | `195cc426-9e99-4fb4-89b8-b048df85033f` / `76115644-7eed-4ecb-b462-b9f0adcc77d3` | Reviewer 13002 / `0030caaa-3ff8-4392-a7e5-7af1541fa988` | `442ff746325df5b6d721fee75d430a65c33d09f0` |
| Separated uniform completion, Worker 1580 | `ab87f47d-9cdd-4caa-b11f-5d6392984aba` / `688960c5-1091-4771-851c-8f9f44242b5e` | Reviewer 13064 / `e6592340-9bf7-4d57-826c-3a8f8854cfb5` | `d2a3dab5880b35349069e39d96304f678174efff` |

At audit base `b3c3e9d6d2583790775c36d7a1ac7db8baaf9e48`,
the four frozen proof pairs and the representability statement pair
match their bundle SHA256 values in the workspace, current Library
and their actual publication trees. All project statement/dependency
pairs imported by the four proofs also match their proof base,
publication tree, current Library and workspace. The complete independent
reports and exact machine receipts were read. This documentation audit
changes none of those mathematical files and supplies no new Lean result.

The new binary proof was published by integration
`e961bf11718f4efb9ee20057fcb52313` at
`442ff746325df5b6d721fee75d430a65c33d09f0`. Its complete independent
acceptance report is unqualified; every common field agrees with the integrated
report. Receipt `76115644-7eed-4ecb-b462-b9f0adcc77d3` passes Lake build,
exact-target, unchanged-statement and frozen-input checks. The published
integration also records a successful fresh integrated build. The frozen,
published and workspace proof pair matches SHA256
`4d2a7ac876073efe5d8810e62133bd28f0407d94cec0c99c8a86f30aafacf542`
for Lean and
`7db8f732216b3e3db51a4cde6472e0156eec3ee2d9bb3fb49637bdc4da727c72`
for Markdown. The target statement pair remains unchanged.

The uniform proof was published by integration
`cebf5ed0d21e45f9a9f6bc58bc357b80` at
`d2a3dab5880b35349069e39d96304f678174efff`.
Its complete independent acceptance report is unqualified and agrees with
the integrated report in every common field. Receipt
`688960c5-1091-4771-851c-8f9f44242b5e` passes all four proof checks listed
above, and the published integration records a fresh successful build.
The frozen proof pair matches its publication tree, current audit base and
workspace: Lean SHA256
`f7973315aeb53c100955636e69ab5669ddb7d53c50341e0f488759c74dc7f158`,
Markdown SHA256
`46a2dfd83063cd499c4de86713c670f646f3a7af304e361adc8cfec2405a94bc`.
The unchanged target pair has Lean SHA256
`8d7f1963aedaeb86d9e25f6ee26c1999bdf8df1efc6bf8f66aea66e3bf87402c`
and Markdown SHA256
`a7bf3f4081f9a74071c8911233f762071cbd852476b1471c308e0cec695ee366`.

## Published ring-denominator construction and its proof gate

Worker 1301, with Worker 709, constructed
[RenardLocalRingCategory](../../Langlands/Algebra/RenardLocalRingCategory.md).
`Langlands.Renard.RingLocalization.RingPair.{u}` stores an actual
commutative unital ring and its designated submonoid; maps are all unital
ring homomorphisms preserving that submonoid. `LocalRingCat` is the actual
full subcategory whose designated elements are units, with its fully
faithful inclusion. `canonicalLocalObject A` uses the actual
`Localization A.denominators` and designates precisely the image of the
original submonoid. The canonical map is the actual `algebraMap`.

The image choice permits a target to designate a proper submonoid of its
units. The actual `canonicalFactor` uses `IsLocalization.lift`; a witness
in the original submonoid and `lift_eq` show preservation into the target's
own designated submonoid. The construction proves the algebra-map evaluation
laws and, when zero is designated, subsingletonness of the actual localized
ring. The common carrier universe u is arbitrary and fixed. Zero rings and
zero denominators are included; no domain, nontriviality, finiteness,
smallness or shrinking assumption is present. Independent-target-universe
transport is not asserted.

Definition candidate `18584ab9-d26b-4e21-bb56-8595b8ae684a`, from task
`0cdbbc91-9d25-405b-99ae-8fb7bace38a4` revision 1, is independently
accepted and public under `lean.definition@1`. Reviewer 12974 approved it
without qualifications in `5eac7fd0-039d-4119-b244-b38cbfe46f98`.
Machine receipt `bb89150e-e443-442d-963f-f72d55d09356` accepts compilation
and declaration-kind checks; it is not a proof of categorical universality.
Integration `52ce5d95e098449a8a630c3269f919c6` published the pair at
`442ff746325df5b6d721fee75d430a65c33d09f0`, with a fresh successful
integrated build. The complete unqualified acceptance report was read and
its common fields agree with the integrated report.
The frozen, published and workspace pair matches SHA256
`a067de0e8559d9783c9ef153b987e01a2ac620217836a38141081f95b8c68bc8`
for Lean and
`19ccc2d16d0435cf2848cc7aefea9eebecc7dc611a4359f81e0dfa5c9a40b65e`
for Markdown. Recovery compilation and declaration inspection passed with
zero diagnostics; this is development evidence, not independent acceptance.

Worker 709, with Worker 1301, has the independently accepted and published
statement candidate `a72a1cf2-cfc7-43b3-ab17-ef4ab192eefe`, declaring
`Langlands.Renard.RingLocalization.CategoricalUniversalStatements` in
`Langlands.Algebra.RenardLocalRingUniversalStatement`. Its three closed
clauses assert the actual chosen-factor equation, uniqueness among all
local-category factors satisfying it, and initiality of the actual canonical
structured arrow. It retains the same image submonoid, arbitrary common u
and zero boundary. Reviewer 13155 approved it without qualifications in
`42438c41-aaf4-416e-b870-ac77444a9c5e`; machine receipt
`49bb3cdb-a54b-43bc-baf9-d00ee721ccbc` accepts statement compilation.
Integration `dcf15bebe94d4307a0dcd784effd9789` published it at
`50c05a5877c13ea23a52ea298c0ec2bd6fdb0817` with a fresh successful build.
The complete independent report and integrated report agree in their common
fields. The frozen pair matches its publication tree, current audit base and
workspace: Lean SHA256
`542fcc71d4d2beebef95e80d3c6ba0857d8d8c16d3eb4c8073718fa7360eeff5`,
Markdown SHA256
`08bec4b9b8c3009bff8c889b4df147e941520c5bd4763fcea5fba1f348a34c67`.

Exact proof task `dd07e94c-b543-487f-8120-e6037cb9c974` revision 1 is now
published and subscribed. It requires a theorem of that unchanged aggregate,
with the actual chosen factor and all local-category competitors.
The statement's publication and the clean recovery declaration inspection
establish no categorical proof.

## Remaining A.III obligations

The ring example's actual construction and categorical statement are published;
its exact proof task remains open. The binary example-1 comparisons and the
precise uniform generalization of example 2 are proved.
The actual continuous-linear completion and fixed-real test constructions
are published, with their distinct statement and exact-proof gates above.
The printed all-continuous-maps vector-space completion claim
remains unresolved; see the [limits and colimits source map](limits-colimits-progress.md)
for related public results. The module example uses invertibility of
each scalar endomorphism, with the stronger printed scalar-inverse
parenthesis corrected as in the [Appendix A discrepancy note](appendix-a-corrections.md).
For example 5, the remaining full categorical transport of the chosen
localization universal arrow is specified above, separately from the
published polynomial-module/endomorphism equivalence, its actual local
restriction and object-level localization formulas.
The chosen functor and natural model comparison
now have the focused construction task above; they remain unpublished
mathematics. Exactness comparisons with these chosen models are internal
backlog, with an existing exact Mathlib functor available for reuse.
Further compatible comparisons for the concrete constructions and their adjunctions retain
separate obligations. Existing adjunction results can be found in the
[A.V source map](adjunctions-progress.md).
Neither these remaining comparisons nor the waiting representability
proof may be counted as completed by the six proof publications above.

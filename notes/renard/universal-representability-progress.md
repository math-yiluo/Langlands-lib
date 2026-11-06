# Renard A.III: universal arrows, representability and isomorphism principles

Worker 709, 5 November 2026. This source map records eleven independently
accepted and published proof units, including the binary-diagonal comparisons,
separated uniform completion, actual continuous-linear completion, the
actual ring-localization categorical universal property, the fixed-real
completion test, the initiality of the chosen endomorphism canonical
arrows and the A.III.2 representability remark and corollary. It also
records the published ring-denominator construction
and statement, and the polynomial-module and restricted equivalences.
The chosen local-module functor and its natural Mathlib comparison are
public. So are the chosen endomorphism canonical-arrow construction, its
initiality statements and their exact proof. For the B-module sentence of
example 5, the category construction and its initiality statements are
public; their exact proof is open.
The fixed-real proof shows that the usual completion arrow does not solve
the printed continuous-map problem for one real space; this is an internal
diagnosis recorded below.
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
| A.III.1 example 2, PDF258 | [UniformCompletionStatements](../../Langlands/CategoryTheory/Renard/UniformCompletionStatements.md) and [UniformCompletionProof](../../Langlands/CategoryTheory/Renard/UniformCompletionProof.md): four proved components for the derived uniform generalization, using uniformly continuous maps and complete separated targets. [Actual continuous-linear completion](../../Langlands/Topology/RenardTopModuleCompletion.md), its [linear-universal statements](../../Langlands/Topology/RenardTopModuleCompletionStatements.md) and [exact proof](../../Langlands/Topology/RenardTopModuleCompletionProof.md) give actual extension uniqueness, canonical-arrow initiality and the specified adjunction. [Real-sequence test objects](../../Langlands/Topology/RenardRealSequenceCompletion.md), [concrete test statements](../../Langlands/Topology/RenardRealSequenceCompletionStatements.md) and their [exact proof](../../Langlands/Topology/RenardRealSequenceCompletionProof.md) give density, incompleteness, the product comparison and continuous nonextension along the usual completion arrow; the consequence for the printed continuous-map claim is the internal diagnosis below |
| A.III.1 example 3, PDF258 | [RenardLocalRingCategory](../../Langlands/Algebra/RenardLocalRingCategory.md): actual ring-denominator category, local full subcategory, localization with designated image submonoid, canonical structured arrow and factor, their evaluation laws and the zero-denominator boundary. [RenardLocalRingUniversalStatement](../../Langlands/Algebra/RenardLocalRingUniversalStatement.md) and [RenardLocalRingUniversalProof](../../Langlands/Algebra/RenardLocalRingUniversalProof.md): the chosen factor's triangle equation, uniqueness among all commuting local-category maps, and initiality of the actual canonical structured arrow are proved |
| A.III.1 example 4, PDF258 | [RenardLocalModuleUniversalStatement](../../Langlands/Algebra/RenardLocalModuleUniversalStatement.md) and [RenardLocalModuleUniversalProof](../../Langlands/Algebra/RenardLocalModuleUniversalProof.md): the actual constructed module factor, its uniqueness among all full-subcategory morphisms, and initiality of the actual canonical structured arrow. [RenardLocalModuleFunctor](../../Langlands/Algebra/RenardLocalModuleFunctor.md) supplies the published chosen functor, canonical natural transformation and comparison with the specified Mathlib model |
| A.III.1 example 5 and subsequent lemma and corollary, PDF258–259 | [PolynomialEndomorphism](../../Langlands/Algebra/PolynomialEndomorphism.md) supplies the published categorical equivalence in the example's first assertion; [RenardInvertibleEndomorphismCategory](../../Langlands/Algebra/RenardInvertibleEndomorphismCategory.md) supplies its actual restriction to local modules and invertible pairs. The [endomorphism-localization note](endomorphism-localization.md) records the five published algebraic proofs, including the B-linear universal property. [RenardEndomorphismLocalizationSource](../../Langlands/Algebra/RenardEndomorphismLocalizationSource.md) and [RenardEndomorphismLocalizationComparison](../../Langlands/Algebra/RenardEndomorphismLocalizationComparison.md) transport the chosen arrow and compare it with the explicit one; [RenardEndomorphismLocalizationInitialityStatements](../../Langlands/Algebra/RenardEndomorphismLocalizationInitialityStatements.md) states factorization, initiality and comparison uniqueness for both arrows, and [RenardEndomorphismLocalizationInitialityProof](../../Langlands/Algebra/RenardEndomorphismLocalizationInitialityProof.md) proves all six clauses. For the final B-module sentence, [RenardAlgebraActionLocalizationCategory](../../Langlands/Algebra/RenardAlgebraActionLocalizationCategory.md) builds the actual category of pairs, its invertible full subcategory and the canonical structured arrow, and [RenardAlgebraActionLocalizationInitialityStatements](../../Langlands/Algebra/RenardAlgebraActionLocalizationInitialityStatements.md) states factorization, initiality and the field specialization; their exact proof is open |
| A.III.2 definition, theorem and proof, PDF259–260 | [YonedaStatements](../../Langlands/CategoryTheory/Renard/YonedaStatements.md) and [YonedaProof](../../Langlands/CategoryTheory/Renard/YonedaProof.md): identity evaluation with its inverse, the actual Yoneda Hom equivalence, the representation dictionary and the equivalence with the full subcategory of representable presheaves |
| A.III.2 final remark, proof and corollary, PDF260–261 | [RepresentabilityUniversalStatements](../../Langlands/CategoryTheory/Renard/RepresentabilityUniversalStatements.md): three published statements for universality iff the chosen transformation is an isomorphism, the represented Hom-presheaf sufficient condition, and unique compatible comparison. [RepresentabilityUniversalProof](../../Langlands/CategoryTheory/Renard/RepresentabilityUniversalProof.md) proves all three |
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

Statement task `7b7701fc-0cac-4d27-b1e2-b997920afa55` revision 1 now has
the independently published pair
[RenardTopModuleCompletionStatements](../../Langlands/Topology/RenardTopModuleCompletionStatements.md).
Its closed aggregate
`Langlands.Renard.TopModuleCompletion.UniversalStatements.{u,v,w}`
conjoins six ring clauses and their exact field specialization:
the chosen extension's triangle equation; uniqueness among all actual
continuous linear competitors; initiality of the actual canonical structured
arrow; an adjunction of the existing functors; density and separated
embedding of the actual canonical map; and concrete chosen extension,
uniqueness and explicit existence-and-uniqueness with independent source
and target universes. The adjunction's unit is exactly `canonicalNatTrans`.
Its inverse Hom map is exactly `extensionHom`, and its forward Hom map
sends g to `canonicalMap R M ≫ (inclusion R).map g`.

These statements keep arbitrary topological unital rings, independent
coefficient/source/target universes u, v and w, and the canonical additive
uniformities. Only targets require completeness and `T0Space`; source
`T0Space` occurs solely in the embedding implication. Zero rings and zero
modules remain included. No adjunction or universal-property certificate
is a premise. Exact proof task
`ce7f40bb-e686-41b7-a4cd-1b249bc07b6d` revision 1 now has the independently
accepted and published
[RenardTopModuleCompletionProof](../../Langlands/Topology/RenardTopModuleCompletionProof.md).
Worker 1582's theorem
`Langlands.Renard.TopModuleCompletion.universalStatements_proof.{u,v,w}`
proves exactly that unchanged aggregate.

The implemented proof evaluates the chosen extension triangle with
`extensionHom_coe`. For every competing continuous linear factor, the
triangle gives agreement on all original points;
`ContinuousLinearMap.fromCompletion_unique` proves equality with the chosen
extension. `Limits.IsInitial.ofUniqueHom` packages these same factors and
their uniqueness as initiality of the actual canonical structured arrow.
The proof constructs `completionHomEquiv` with forward map
`g ↦ canonicalMap R M ≫ (inclusion R).map g` and inverse `extensionHom`.
Extension uniqueness proves naturality in the source, and pointwise
composition proves naturality in the target. `Adjunction.mkOfHomEquiv`
then constructs the adjunction of the existing functors and proves its
exact unit and both Hom formulas, without assuming adjunction data.
The concrete proof uses the same extension uniqueness across independent
source and target universes. Mathlib's canonical completion lemmas prove
density and the conditional uniform embedding; the field clause
specializes the same ring proof.

This proves the continuous-linear aggregate with no further outer
mathematical premises. Completeness and separation are imposed only on
targets, and source `T0Space` is used only for the embedding implication.
The corrected continuous-linear convention remains distinct from the printed
example's continuous maps without linearity or a fixed scalar field.

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

Statement task `a7b67918-772d-4ae0-b2b8-d106d0c4235e` revision 1 now has
the independently published pair
[RenardRealSequenceCompletionStatements](../../Langlands/Topology/RenardRealSequenceCompletionStatements.md).
Its closed aggregate
`Langlands.Renard.RealSequenceCompletion.CompletionCounterexampleStatements`
conjoins eleven conclusions over these unchanged `Type 0` objects:
truncation convergence, density, both missing-point assertions,
incompleteness, positive distance, reciprocal continuity, the exact
continuous-linear comparison with the product, joint scalar continuity of
the existing completion action, and both continuous nonextension assertions.
The comparison equivalence's underlying function is exactly
`completionToProduct`. Nonextension ranges over every continuous
real-valued function on the product or actual usual completion agreeing
with `reciprocalDistance` along the specified canonical arrow.
No linearity, boundedness or uniform-continuity condition restricts competitors.

Exact proof task `8e91f574-670c-4a1b-9971-5d9942489de6` revision 1 now has
the independently accepted and published
[RenardRealSequenceCompletionProof](../../Langlands/Topology/RenardRealSequenceCompletionProof.md).
Worker 1276, with Worker 709, proves the unchanged aggregate as
`Langlands.Renard.RealSequenceCompletion.completionCounterexampleStatements`,
with eleven named constituent theorems and no outer premises.
Eventual coordinate equality of the truncations and `tendsto_pi_nhds` give
convergence in the product topology, hence density. Finite support excludes
the constant-one sequence. If the finite subspace were complete, its uniform
embedding into the Hausdorff product would have closed range, contradicting
density. Positivity and continuity of the distance use a local instance of the
published metric, whose uniformity and topology are definitionally the original
ones; no structure is replaced globally. For the product comparison, a local
`AbstractCompletion` built from the product and the inclusion gives, via
`AbstractCompletion.compareEquiv`, a uniform equivalence whose forward function
is definitionally `completionToProduct`. The proof bundles it as a real
continuous linear equivalence e. Joint scalar continuity of the existing
completion action is read off from e.
For product nonextension, a continuous g agreeing with `reciprocalDistance`
on the inclusion makes `p ↦ sequenceDistance p missingSequence * g p` equal
to one on a dense range. `DenseRange.equalizer` makes it identically one,
which fails at the missing point, where the distance is zero.
A continuous extension along the completion arrow would give the forbidden
product extension `p ↦ g (e.symm p)`.

Internal diagnosis. PDF258 example 2 takes as morphisms “les applications
continues” between topological vector spaces and names the completion with
its continuous inclusion as the solution. Read literally, the proved
`NoCompletionContinuousExtension` contradicts this for the real space
`FiniteSequence`. The complete real space ℝ and the continuous map
`reciprocalDistance` have no continuous factor through the usual completion
arrow, so that arrow does not solve the printed continuous-map problem for
this space. The comparison is made in this note: Lean formalizes no
category of topological vector spaces with continuous maps. The result
concerns one space and the usual completion arrow. It says nothing about
whether some other reflection into complete spaces exists. The published
continuous-linear and uniformly continuous versions above are the proved
positive formulations.

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

Both new completion statement pairs are accepted and public under
`lean.statement@1`, with unqualified independent approval:

| Statement and author | Candidate / machine receipt | Independent reviewer / review task | Publication commit |
| --- | --- | --- | --- |
| Actual topological-module universal property, Worker 1582 with Worker 709 | `88d78a41-0f15-485d-a91e-fbd250875c9b` / `bae4e0dd-5094-4c23-b3d5-418a0097c023` | Reviewer 13424 / `9642262b-fcbf-4fb6-b9af-1773dd1bc31b` | `4dd5f7c45ce9b800a0caffa94e2e790953bf7c96` |
| Actual real-sequence completion test, Worker 1276 | `4677cf0e-fb45-4a7b-b1fc-6ece663fa96b` / `1d98bd43-34ef-4052-b97c-e3ee15e83253` | Reviewer 13421 / `45f9ccee-b6d4-4e17-860f-336d76e72016` | `4dd5f7c45ce9b800a0caffa94e2e790953bf7c96` |

Their integrations are respectively
`3fd0ecd496864e349ed62da4f6938853` and
`ba4f3c6113e045d992bf34a823143e31`, each with a fresh successful
integrated build. The full independent reports were read and agree with
the integrated reports in every common field. Both frozen pairs match
their publication trees, Library `18de63ed841e31dca10a26ef417aea7050cf443f`
and the workspace. The topological-module pair's Lean/Markdown SHA256 values
are respectively
`28413c45eebbdf6385c07c2574283fb6aa51ae47e635cae375a7ab7cda97b427` and
`79284a0ae20c351b98dc9784d1fdf2094e80f8cb13edf2772ad6944c40ddffde`;
the real-sequence pair's are
`31b89cce9e09ccecea2eb32fe1a6a55f0f61d67f734ff5d4118d2acceaeb230a` and
`8190c66dd18e8e80ac2b437106f3717b83f16153102dbec8a0b362317a4d6c85`.
Recovery check `e903355e-306b-43e0-9b83-e171c922e9f9` also compiles
the topological-module construction and statement with zero diagnostics
and inspects `UniversalStatements` as Prop with independent u, v and w.
These are statement and development receipts; neither proves an aggregate.

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
The separate comparison was a full categorical transport of
the chosen, lifted module-localization universal arrow through the
published equivalence to the full subcategory of pairs with invertible
endomorphism. It had to identify the chosen localization
maps with `EndomorphismLocalization.iota` and the X-action with
`EndomorphismLocalization.localizedEnd`, including the carrier
identifications. That narrower packaging is now published; see the
canonical-arrow section below.

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
prove their initiality. The chosen-model functor, the canonical-arrow
comparison, its Prop-valued initiality statements and their exact proof
are published as described below.

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
The published comparison below identifies these carriers, canonical maps,
morphism maps and full-subcategory target for the chosen functor.
Exactness of Mathlib's functor alone did not supply those identifications.
Chosen-model sequence exactness and its source-facing transport retain
separate statement/proof obligations for a concrete consumer.

### Published chosen local-module functor and natural comparison

Focused internal construction task
`fe93edc1-1343-4f01-b558-43e7dab72c02` revision 1 has two independently
accepted and published implementations. The current
[RenardLocalModuleFunctor](../../Langlands/Algebra/RenardLocalModuleFunctor.md)
pair is Worker 1570's construction in
`Langlands.Renard.ModuleLocalization`. Its actual `chosenLocalFunctor S`
has objects exactly `canonicalLocalObject S M`. Its `chosenLocalMap S f`
conjugates `IsLocalizedModule.map S` by the two ULift linear equivalences,
and `chosenLocalMap_up_mk` gives the formula
`ULift.up (LocalizedModule.mk m s) ↦ ULift.up (LocalizedModule.mk (f m) s)`.
Representative induction proves identity and composition.
`sourceRaisingFunctor` is exactly
`ModuleCat.uliftFunctor.{max u w,v} R`, with object map `raisedSource`.
`chosenLocalizationUnit` has exactly `canonicalModuleMap S M` as its
components; its naturality holds for every actual R-linear morphism.

For κ = max u v w, `mathlibLocalizationFunctor` is the exact composite

```text
U ⋙ ModuleCat.localizedModuleFunctor.{κ} S ⋙
  ModuleCat.restrictScalars (algebraMap R (Localization S)).
```

`mathlibActionEquiv` identifies the native R-action with the restricted
action by `IsScalarTower.algebraMap_smul`, using identity functions.
`mathlibCanonicalMap` and `mathlibLocalizationUnit` therefore land in the
actual restricted-action objects. Proved locality supplies the actual
full-subcategory lift `mathlibLocalFunctor`.

`chosenMathlibLinearEquiv` removes the chosen outer ULift, localizes the
source-raising linear equivalence, passes through the actual Shrink
equivalence and compares the scalar actions. `chosenMathlibIso` bundles
these equivalences naturally into the local full subcategory. Its
`chosenMathlibIso_hom_up_mk` formula sends
`ULift.up (LocalizedModule.mk m s)` to the Shrink representative of
`LocalizedModule.mk (ULift.up m) s`. The exact canonical-arrow law is

```text
canonicalModuleMap S M ≫
  (localModuleInclusion S).map ((chosenMathlibIso S).hom.app M) =
  (mathlibLocalizationUnit S).app M.
```

Naturality for every morphism and both component inverse laws are proved.
The comparison uses `IsLocalizedModule.ext` on the actual raised canonical
arrow, whose localization instance is established by the existing ULift
equivalences. It assumes no universal-property certificate.
Independent u, v and w are retained, with Smallness at κ discharged
internally. Zero rings, zero modules and submonoids containing zero are
included, without dimension, faithfulness or nontriviality restrictions.

Worker 1603's alternative is preserved in
[RenardLocalModuleFunctorUniversalComparison](../../Langlands/Algebra/RenardLocalModuleFunctorUniversalComparison.md),
namespace `Langlands.Renard.ModuleLocalization.UniversalComparison`.
It constructs the same specified chosen-object functor and comparison
through the universal properties of the two verified localization maps.
Its source and canonical transformations are named `sourceRaiseFunctor`,
`chosenLocalizationNatTrans` and `mathlibLocalizationNatTrans`.
Use Worker 1570's names for the successor composite below.

Both are accepted and public under `lean.definition@1`, with unqualified
independent reviews and fresh successful integrated builds:

| Construction | Candidate / machine receipt | Independent reviewer / review task | Integration / publication commit |
| --- | --- | --- | --- |
| Worker 1570, current main pair | `96d4c3a1-4c2b-4390-b521-6262dfe22174` / `882301a1-0d47-4ae3-a2b3-ac8ad6df1bb5` | Reviewer 13207 / `6f70ccbf-ea37-4d5e-b39c-15a2f01996f3` | `3e2f53aa038b4ecf9f17abecf9624ac7` / `50c05a5877c13ea23a52ea298c0ec2bd6fdb0817` |
| Worker 1603, relocated alternative | `442a17e3-6f93-49ff-a266-703d8935941b` / `f1f8e51c-332c-4821-b839-7fcedc1c792a` | Reviewer 13215 / `2bf89aa3-5938-4fe1-a45a-792146211c2d` | `dedb752c270b4956a7f2afd745c508cc` / `50c05a5877c13ea23a52ea298c0ec2bd6fdb0817` |

The full independent reports were read. Worker 1570's frozen pair equals
the main pair in the publication, audit Library and workspace.
Worker 1603's integration changes the Lean namespace and the companion's
title, namespace and alternative-construction link; its relocated pair
equals the published and local alternative. It is not a same-path
byte-identical copy of the frozen submission. The relocation preserves
its construction and intrinsic laws. Neither unit publishes an adjunction
or chosen-model sequence-exactness theorem.

### Published chosen endomorphism canonical-arrow comparison

Focused construction task `e340435d-c0ce-453f-9f1b-31629e02bc52`
revision 1 is done. With PE =
`Langlands.Algebra.PolynomialEndomorphism`, ML =
`Langlands.Renard.ModuleLocalization`, EL =
`Langlands.Renard.EndomorphismLocalization`, and κ = max u v w,
it required the actual composite

```text
F = PE.toPolynomial R ⋙ ML.chosenLocalFunctor.{u,v,w} (EL.powersX R) ⋙
      EL.localFromPolynomial.{u,κ} R.
```

Worker 1581 delivered it in two published units. All their declarations
are in `EL.ChosenComparison`. The source unit
[RenardEndomorphismLocalizationSource](../../Langlands/Algebra/RenardEndomorphismLocalizationSource.md)
defines F as `chosenFunctor` and the explicitly raised pair functor U as
`raisedFunctor`, sending A to `(ULift A.a, x ↦ ULift.up (A.str x.down))`.
Its natural isomorphism β = `sourceComparison` compares U with
`PE.toPolynomial ⋙ ML.sourceRaisingFunctor ⋙ PE.fromPolynomial`.
The component `sourceLinearEquiv` sends `ULift.up x` to
`ULift.up (Module.AEval'.of a x)`. Its proofs identify the restricted
action of r with the polynomial action of `C r`, and the recovered
X-action with the original operator. θ = `polynomialArrow` whiskers the
actual `ML.chosenLocalizationUnit`, and the chosen arrow
λ = `chosenArrow` is β followed by θ, with formula
`ULift.up x ↦ ULift.up (LocalizedModule.mk (Module.AEval'.of a x) 1)`.

The comparison unit
[RenardEndomorphismLocalizationComparison](../../Langlands/Algebra/RenardEndomorphismLocalizationComparison.md)
defines the explicit functor E = `explicitFunctor`. Its objects are
`ULift.{w} (EL.Localized a)` with the lifted `EL.localizedEnd a`, and it
sends every original intertwiner to its actual localized polynomial map.
The natural isomorphism α = `targetComparison` : F ≅ E has identity
underlying functions. Its scalar proof compares the restricted and native
R-actions with `EL.smul_eq_C_smul`, without assuming them definitionally
equal. Let J be `invertibleEndomorphismInclusion` and ι = `explicitArrow`,
with components `ULift.up x ↦ ULift.up (EL.iota a x)`. Then
`arrow_comparison` proves

```text
β_A.hom ≫ θ_A ≫ J.map (α.hom.app A) = ι.app A,
```

and `chosenArrow_comparison` restates it as
`λ.app A ≫ J.map (α.hom.app A) = ι.app A`. `structuredArrowComparison`
is the actual isomorphism from `chosenStructuredArrow` to
`explicitStructuredArrow` with target component α. It identifies the
two arrows together with their raised sources, not only their targets.
Both units retain arbitrary commutative rings and independent u, v and w.
They keep all intertwiners, zero rings and modules, and zero or nilpotent
source endomorphisms. The field specializations have no dimension
restriction. Neither unit asserts a universal property.

Worker 709's statement unit
[RenardEndomorphismLocalizationInitialityStatements](../../Langlands/Algebra/RenardEndomorphismLocalizationInitialityStatements.md)
declares the closed `EL.ChosenComparison.InitialityStatements.{u,v,w}`.
Its six Prop-valued clauses are:

1. for every invertible pair B and every map g out of the raised pair,
   `∃! h : E.obj A ⟶ B, ι.app A ≫ J.map h = g`;
2. the same factorization through the chosen arrow λ and F.obj A;
3. `Nonempty` initiality of the explicit structured arrow;
4. `Nonempty` initiality of the chosen structured arrow;
5. α.hom.app A and α.inv.app A are the only maps compatible with the two
   arrows in the respective directions;
6. the explicit factorization over an arbitrary field.

The field clause is the setting of example 5, and clause 5 is the PDF258
uniqueness remark for the two canonical arrows. The commutative-ring,
full-subcategory and lifted-carrier forms are internal formulations. A
noncommutative B is outside the statement.

| Unit and author | Candidate / machine receipt | Independent reviewer / review task | Integration / publication commit |
| --- | --- | --- | --- |
| Raised source and chosen arrow, Worker 1581 | `b61b979b-71fe-4633-b560-f99d4607d8d0` / `a56a1faa-9d8c-4049-b60b-b609a68b294d` | Reviewer 13654 / `f26821e5-ec3f-4654-8202-8ecbd8610e24` | `09003353ee2c4a63882ac112376512d5` / `476a152fd90d846bcb20b9897f53829a768b822c` |
| Explicit functor and arrow comparison, Worker 1581 | `c7dc4e38-c0f1-4ac0-9fd0-a0058f8fc554` / `4571f4ad-e175-4e53-8d02-ae766502866c` | Reviewer 13698 / `1d73d9b5-e522-4810-95be-02aa8bc50de0` | `3c34ede5a63b45d1a006dd64bf0b8aa8` / `409542525904dd50036abafdafb8ad1459eadade` |
| Initiality statements, Worker 709 | `dd7e51e2-d78a-47ca-9a2c-036589b7d2f5` / `3dd610f2-8805-40e0-8675-4ed045b80a31` | Reviewer 14035 / `f3ef27e0-7f94-4c0f-9190-bcff504f3658` | `120f1af1977f480e8688e279846f87a7` / `0bd5bf67c3464359bc8da3b3100163d6ee3da352` |

The two constructions are accepted and public under `lean.definition@1`,
and the statements under `lean.statement@1`, all with unqualified
approval. Their machine receipts check compilation and declaration kind;
none proves the initiality targets. Each integration records a fresh
successful integrated build. The full independent reports were read and
agree with the integrated reports in every common field. The frozen pairs
equal their publication trees, Library
`4253339ea6afa6e5df9f13373ec3aa96b434ace4` and the workspace. Their
Lean/Markdown SHA256 values are
`ad56e2ee46bad41d59742fd9687631895b60f697a717f5aa42b4e3a5fa181374` /
`5c44f064a67dcf073b9db780f97bd44e1c113fbe84f479d724e98ed3f09d4f9a`
for the source unit,
`249b65e7eec01300ed83bcdd473c7270c1c979100c2f548fe905e59e3194709d` /
`cddf6abd16ae99105992a6deeae5ad6cf4220ae5aa2e943777933045bb1bd052`
for the comparison and
`b7a3246af1356e5994d0cc549b1820e53ae2e17200d3b4a3467ffb496e128c60` /
`c95821e69d974c27d71535203ee8b8d113dd7ab2378013ed191d28b104328a70`
for the statements.

Exact proof task `348bf102-8242-47f7-b5b2-5ea4429d30da` revision 1 is
completed by proof `8c87e9d1-9e45-4a0c-bd57-6a3d7b25c5b3`, by Worker 1570
with Worker 709:
[RenardEndomorphismLocalizationInitialityProof](../../Langlands/Algebra/RenardEndomorphismLocalizationInitialityProof.md)
proves `EL.ChosenComparison.initialityStatements` at independent u, v and
w with no added hypothesis. Machine receipt
`b8e219cf-cb9b-441f-9e43-bf7c2b05a5da` accepts it under `lean.proof@1`
with Lake build, exact-target, unchanged-statement and frozen-input
checks. Reviewer 14249 approved it without qualifications in review
`7347835a-939c-4baf-9da4-8b1106296799`. Integration
`e825cc69801b4005a0add71ca1881290` published it at Library
`910675f18ad6c3d8b09c12c678a0243795a673b9` after a fresh successful
integrated build; the independent and integrated reports agree in every
common field. Its Lean/Markdown SHA256 values
`f9c6be9f25172cce9e618e46b6d3b9b7de03578a26d9e3d16175bed3837e7011` /
`63708fd7643008151676683e8b512e212fcd0704c1458181f897bb0282c198fc`
are equal in the frozen candidate, that publication, Library
`f931c96e65d20b436d2363a83d6971f9406ec738` and the workspace, and the
statement pair is unchanged.

The implemented route converts a map g out of the raised pair into an
R-linear intertwiner of the original carrier and bundles the published
`factor` as `explicitFactor`. The published `factor_comp_iota` gives the
triangle equation and `factor_unique` gives uniqueness among all
full-subcategory maps. `IsInitial.ofUniqueHom` turns these into initiality
data for the explicit structured arrow, and `IsInitial.ofIso` transports them
along the inverse of `structuredArrowComparison` to the chosen arrow. The
factorization and comparison clauses are `existsUnique` consequences of
these data, using `chosenArrow_comparison` and the inverse comparison
square. Neither initiality proof takes a universal-property certificate as
input. Chosen-model exactness and adjunctions retain separate obligations.
The categorical B-module variant is recorded in the next section.

## The B-module variant of example 5

The final sentence of example 5 on PDF258 says that the same construction
works with B-modules and B-module endomorphisms for a k-algebra B. The
published raw B-linear universal property is recorded in the
[endomorphism-localization note](endomorphism-localization.md). Two further
units by Worker 709 package it categorically.

[RenardAlgebraActionLocalizationCategory](../../Langlands/Algebra/RenardAlgebraActionLocalizationCategory.md)
is a definition unit in `Langlands.Renard.AlgebraActionLocalization`.
`ActionModuleCat.{u,v,w} k B` has as objects k-modules with an actual
nonunital action `B →ₙₐ[k] Module.End k M`, and as morphisms exactly the
actual linear intertwiners. `ActionEndomorphismCat` is the category of
pairs with a compatible endomorphism, using Mathlib's `Endofunctor.Algebra`.
`InvertibleActionEndomorphismCat` is the full subcategory of pairs whose
endomorphism is a unit, and `invertibleActionInclusion` is its inclusion.
`raisedFunctor` lifts carriers into `max u w x`, and
`canonicalStructuredArrow A` is the structured arrow of the lifted published
`iotaIntertwiner` into `localizedObject A`. The unit asserts no universal
property.

[RenardAlgebraActionLocalizationInitialityStatements](../../Langlands/Algebra/RenardAlgebraActionLocalizationInitialityStatements.md)
declares the closed `InitialityStatements.{u,v,w,x}`. Write J for
`invertibleActionInclusion`. Its three Prop-valued clauses are:

1. for every invertible pair T and every map g out of the raised pair,
   `∃! h : localizedObject A ⟶ T, canonicalArrow A ≫ J.map h = g`;
2. `Nonempty (StructuredArrow.IsUniversal (canonicalStructuredArrow A))`;
3. the factorization clause over an arbitrary field k, for a possibly
   nonunital k-algebra B.

The coefficient ring k is an arbitrary commutative ring and B needs only
`[NonUnitalRing B] [Module k B]`. No unit, commutativity or nondegeneracy is
assumed, and zero rings, modules, actions and endomorphisms are allowed.
The general coefficient ring, the categorical packaging and the universe
raising are internal derived formulations.

| Unit and author | Candidate / machine receipt | Independent reviewer / review task | Integration / publication commit |
| --- | --- | --- | --- |
| Category and canonical arrow, Worker 709 | `f36a1ffd-c8b4-4bf9-a99c-9a395cd216bd` / `336753c9-b3a0-40ea-ad00-b961bcc4f0b0` | Reviewer 14379 / `24d9243f-35d3-451b-b8f2-507d483278da` | `247cdc26cf9748f782ab8e602a871fea` / `1831431f93603e52c73600a2a900dd42d7f18deb` |
| Initiality statements, Worker 709 | `17343a78-2584-40db-aced-a124277decdb` / `f89f4adc-359e-4072-ac52-a80f47ae0501` | Reviewer 14616 / `1e6a5bee-b147-49e5-94da-c651677faf49` | `e27a3020da5249fe8bf251875d15f1a9` / `bc859155612cc8ca34e8e25175ce2f7775c217dc` |

The definition is public under `lean.definition@1` and the statements under
`lean.statement@1`, both with unqualified approval. Their machine receipts
check compilation and declaration kind; neither proves the initiality
targets. The pairs equal Library
`dd78edadc914cf56ca81c595cee581a3570d415c` and the workspace. Their
Lean/Markdown SHA256 values are
`d1c5b34dc1fd8332ecf8a4baa3f43285b4fbea8111b7bdd909021c24169fd9fa` /
`0a7c3f194633bec2ba64d13e24a2d71409ba89e627d5baf632b0f78e9fceb838`
for the category and
`6e1bbfc661b7da8ea2ab558da9b708b2306a91c7cebe2cd9b5b00260e99f047b` /
`270d98dcd0a8b968444939ee6fb65b0e4647d771e574610c6ff25be665a1b75a`
for the statements.

Exact proof task `7973e016-e501-4153-a0e5-6bec84b8598b` targets
`InitialityStatements` unchanged; at this audit it is claimed and has no
accepted proof. Until such a proof is published, the categorical B-module
universal property remains an open obligation.

## The representability proof

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
universe parameters.

Exact proof task `2370e288-e5f7-4117-bbd9-85d1142dc6dd` revision 1 now
has the accepted and published
[RepresentabilityUniversalProof](../../Langlands/CategoryTheory/Renard/RepresentabilityUniversalProof.md),
proof `5bf0b78b-2c07-478a-a37e-e8efb5664a0a`. Worker 1187 wrote the Lean
proof; Worker 1193 adapted Worker 709's documentation draft and prepared
the final documentation. The theorem
`Langlands.Renard.RepresentabilityUniversal.representabilityUniversalStatements`
proves the unchanged aggregate at independent w, vA, vB, uA and uB with
no added hypothesis.

The implemented route is as follows. For an invertible ω,
`IsTerminal.ofUniqueHom` uses the `uliftYoneda` preimage of
`c.hom ≫ inv ω`. Conversely, terminality data give bijectivity of each
component `ω.app (op Y)`: injectivity from `h.hom_ext`, surjectivity from
`h.lift`, both through `uliftYonedaEquiv`. Then
`NatIso.isIso_of_isIso_app` gives `IsIso ω`. This follows the book's
argument in elementwise form. For the Hom presheaf, `r.homEquiv_eq` gives
`r.homEquiv m = F.map m ≫ j`, and the factor of a costructured arrow c is
`r.homEquiv.symm c.hom`. The compatible isomorphism is
`uliftYoneda.preimageIso (ω ≪≫ ω'.symm)`, unique by faithfulness and
`Iso.ext`. The last two proofs are internal derivations; the book leaves
the second to the reader and does not prove the corollary.

Machine receipt `481c71f3-14b4-40b0-9c38-1a4d3a053af6` accepts the
proof under `lean.proof@1` with Lake build, exact-target,
unchanged-statement and frozen-input checks. Reviewer 14686 approved it
without qualifications or suggestions in review task
`845d8646-cd85-4148-9ed7-e9b5f369863d`. Integration
`fb0df6d8d06a48cd986a7b18ac6573ee` published it at
`542eaca02a9f2d14f175497b7bf6459436ac5c6d` after a fresh successful
integrated build. Its Lean/Markdown SHA256 values
`0c14c9e7cb209f44f4b08179b919910b00882fdd09b9bb2510d546483e56e403` /
`f5baebc3fab561d5d632b0d7f18d9b157c9c0858aaf57ba60beec42f6532b777`
are equal in the frozen candidate, that publication, Library
`dd78edadc914cf56ca81c595cee581a3570d415c` and the workspace. The
statement pair
`06ab1b345a8d60a5a2e00125aa763b70f53a716b3b7357a127b4966c015dd3bd` /
`dacaf272524eb79bc37f544828a0f843e1f8e8c27ede807dd853978b68bec791`
is unchanged. Worker 709 is a coauthor of this proof, so this audit is a
documentation record, not an independent review.

The supplementary registered `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is discussed in the accepted statement and its independent report:
the PDF18 corrections to older printed p.294 l.-11 and p.295 l.6
give the identity-evaluation and transformation-factorization forms
already present in the governing 2026 passage. This is bounded
older-edition evidence, not an exhaustive errata claim.

## Verified proof publications

All eleven rows are accepted and public with unqualified independent
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
| Actual ring localization, Worker 1301 with Worker 709 | `2e8ebe7c-2a86-4c78-b263-7e6a635fb705` / `14e12de7-0fa3-4ff4-bdab-c7493c4a26f4` | Reviewer 13467 / `59072e33-b9a6-4ba0-9b3d-277d3ba5a6da` | `a4a5fb7b2643f2b9b9a6ac9c41bde7cc387d4a1a` |
| Actual continuous-linear completion, Worker 1582 | `338f12b5-928a-47c5-870b-40bd70c019f1` / `8c887c95-9aa5-4d1a-ae57-7df2ce1b3b8f` | Reviewer 13656 / `f92c2ef4-d4e1-4dff-985b-3a7190d9e988` | `476a152fd90d846bcb20b9897f53829a768b822c` |
| Fixed-real completion test, Worker 1276 with Worker 709 | `e8ba1922-e212-4638-9ab2-412324dbac15` / `936207fb-7f4d-4436-b5d1-66d1ee4b8549` | Reviewer 13715 / `47f36e5b-f92a-48f0-8c87-d6c6cb5d85f7` | `409542525904dd50036abafdafb8ad1459eadade` |
| Endomorphism canonical-arrow initiality, Worker 1570 with Worker 709 | `8c87e9d1-9e45-4a0c-bd57-6a3d7b25c5b3` / `b8e219cf-cb9b-441f-9e43-bf7c2b05a5da` | Reviewer 14249 / `7347835a-939c-4baf-9da4-8b1106296799` | `910675f18ad6c3d8b09c12c678a0243795a673b9` |
| Representability remark and corollary, Worker 1187 with Workers 1193 and 709 | `5bf0b78b-2c07-478a-a37e-e8efb5664a0a` / `481c71f3-14b4-40b0-9c38-1a4d3a053af6` | Reviewer 14686 / `845d8646-cd85-4148-9ed7-e9b5f369863d` | `542eaca02a9f2d14f175497b7bf6459436ac5c6d` |

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

The continuous-linear completion proof was published by integration
`2e2cab1ef4564e2e9a8f60a79a8d7732` at
`476a152fd90d846bcb20b9897f53829a768b822c`.
The full unqualified independent report was read and agrees with the
integrated report in every common field. Its machine receipt in the table
passes Lake build, exact-target, unchanged-statement and frozen-input checks;
integration records a fresh successful build. The frozen proof pair equals
its publication tree, audit Library
`9caf47cacd8f25d9a56aa0737b4256267bf62d16` and workspace:
Lean SHA256
`dee60a4d1f418a56cf9e780ddcb51c49fff777419bd050275077a6b7d971c0e9`,
Markdown SHA256
`ba10fa0a66b344da3a677e4167b1199ce452007e711fe83ba1e67f14b328d783`.
The published statement remains unchanged, with the hashes recorded above.
Recovery check `b725f1ff-157c-4e97-8b1f-003a8f254626` also compiles the
proof with zero diagnostics; that development check is separate from the
independent proof acceptance.

The fixed-real proof was published by integration
`910dd67ea8cf44f9ab9d4b14dac78c13` at
`409542525904dd50036abafdafb8ad1459eadade`. The full unqualified
independent report was read and agrees with the integrated report in every
common field. Its machine receipt in the table passes all four proof checks,
and the integration records a fresh successful build. The frozen proof pair
equals its publication tree, Library
`4253339ea6afa6e5df9f13373ec3aa96b434ace4` and the workspace: Lean SHA256
`42587719a0f37fe314a9a49f7671e153888d540332b13a3d340f8c5af73c4e64`,
Markdown SHA256
`a8c5e0bbf2c6de2c316a019138ad940eab50376c004700edc091d7f8af40aaab`.
The target statement pair is unchanged, with the hashes recorded above.

## Published ring-denominator construction and categorical proof

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

Exact proof task `dd07e94c-b543-487f-8120-e6037cb9c974` revision 1 now has
the accepted and published
[RenardLocalRingUniversalProof](../../Langlands/Algebra/RenardLocalRingUniversalProof.md).
Worker 1301's theorem
`Langlands.Renard.RingLocalization.categoricalUniversalStatements`
proves exactly the unchanged closed `CategoricalUniversalStatements.{u}`,
with Worker 709's source correspondence, statement design and factorization
route.

Extensionality reduces the chosen factor's triangle equation to evaluation
on each original ring element, where `canonicalFactor_algebraMap` applies.
For every commuting local-category map, extensionality removes the
full-subcategory and denominator-preservation wrappers.
`IsLocalization.ringHom_ext` reduces equality of its underlying ring map
with the chosen factor to agreement after the algebra map. Evaluating the
assumed triangle gives that agreement; competitors need not be presented
as localization lifts. `Limits.IsInitial.ofUniqueHom` then uses
`StructuredArrow.homMk` of the chosen factor to construct initiality.
`StructuredArrow.w`, the proved factor uniqueness and
`StructuredArrow.hom_ext` identify every competing structured-arrow map.
The proof retains the designated image, arbitrary common u, zero rings
and zero denominators, without further mathematical premises.

The proof candidate and exact machine receipt appear in the table above.
Reviewer 13467's full unqualified independent report was read and agrees
with the integrated report in every common field. Integration
`fce23df03a7f464294913df1bc5fcff0` published the proof at
`a4a5fb7b2643f2b9b9a6ac9c41bde7cc387d4a1a`, with a fresh successful
integrated build. The frozen proof pair matches its publication tree,
Library `b01e426d540ff0d2edcc0480f6f0d03dd2f71e78` and the workspace:
Lean SHA256
`713604c936253dc02b615242cf8e4dbccc4124c8ec1622133eea2466bda931dd`,
Markdown SHA256
`9903008248140a079c87e063cf9b0602dab64f672bf43fa0ac7b5c229ec21d9c`.
The construction and statement pairs also match the proof base,
publication tree, checked Library and workspace, with the unchanged
hashes recorded above. The exact proof receipt passes Lake build,
exact-target, unchanged-statement and frozen-input checks.
This proves the three categorical assertions for example 3. Localization
functors, reflection and adjunctions, independent-target-universe transport
and further comparisons retain separate obligations.

## Remaining A.III obligations

The ring example's actual construction, categorical statement and exact
three-clause proof are published. The binary example-1 comparisons and the
precise uniform generalization of example 2 are proved.
The actual continuous-linear completion now has its published exact proof,
including extension uniqueness, initiality and the canonical adjunction.
The fixed-real test now has its published exact proof. As diagnosed above,
it shows that the usual completion arrow does not solve the printed
all-continuous-maps problem for one real space. Whether that problem has
some other solution is not addressed. See the
[limits and colimits source map](limits-colimits-progress.md)
for related public results. The module example uses invertibility of
each scalar endomorphism, with the stronger printed scalar-inverse
parenthesis corrected as in the [Appendix A discrepancy note](appendix-a-corrections.md).
For example 5, the chosen functor, its natural model comparison, the
endomorphism canonical-arrow transport, the initiality statements and their
exact proof are published.
Exactness comparisons with these chosen models are internal
backlog, with an existing exact Mathlib functor available for reuse.
For the final B-module sentence of example 5, the unique factorization among
actual B-linear intertwiners is public as
`Langlands.Renard.AlgebraActionLocalization.universalPropertyStatements`;
see the [endomorphism-localization note](endomorphism-localization.md).
Its categorical structured-arrow packaging and initiality statements are
public, as recorded [above](#the-b-module-variant-of-example-5). Their
exact proof, task `7973e016-e501-4153-a0e5-6bec84b8598b`, is open.
The A.III.2 representability remark and corollary are proved. Further
compatible comparisons for the concrete constructions and their adjunctions
retain separate obligations. Existing adjunction results can be found in the
[A.V source map](adjunctions-progress.md).
Neither these remaining comparisons nor the open B-module proof may be
counted as completed by the eleven proof publications above.

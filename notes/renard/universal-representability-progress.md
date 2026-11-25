# Renard A.III: universal arrows, representability and isomorphism principles

This source map, dated 5 November 2026, records twelve
proof modules of the Library, including the binary-diagonal comparisons,
separated uniform completion, actual continuous-linear completion, the
actual ring-localization categorical universal property, the fixed-real
completion test, the initiality of the chosen endomorphism canonical
arrows, the categorical B-module initiality of example 5 and the A.III.2
representability remark and corollary. It also
records the published ring-denominator construction
and statement, and the polynomial-module and restricted equivalences.
The chosen local-module functor and its natural Mathlib comparison are
public. So are the chosen endomorphism canonical-arrow construction, its
initiality statements and their exact proof. For the B-module sentence of
example 5, the category construction, its initiality statements and their
exact proof are public.
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
| A.III.1 example 5 and subsequent lemma and corollary, PDF258–259 | [PolynomialEndomorphism](../../Langlands/Algebra/PolynomialEndomorphism.md) supplies the published categorical equivalence in the example's first assertion; [RenardInvertibleEndomorphismCategory](../../Langlands/Algebra/RenardInvertibleEndomorphismCategory.md) supplies its actual restriction to local modules and invertible pairs. The [endomorphism-localization note](endomorphism-localization.md) records the five published algebraic proofs, including the B-linear universal property. [RenardEndomorphismLocalizationSource](../../Langlands/Algebra/RenardEndomorphismLocalizationSource.md) and [RenardEndomorphismLocalizationComparison](../../Langlands/Algebra/RenardEndomorphismLocalizationComparison.md) transport the chosen arrow and compare it with the explicit one; [RenardEndomorphismLocalizationInitialityStatements](../../Langlands/Algebra/RenardEndomorphismLocalizationInitialityStatements.md) states factorization, initiality and comparison uniqueness for both arrows, and [RenardEndomorphismLocalizationInitialityProof](../../Langlands/Algebra/RenardEndomorphismLocalizationInitialityProof.md) proves all six clauses. For the final B-module sentence, [RenardAlgebraActionLocalizationCategory](../../Langlands/Algebra/RenardAlgebraActionLocalizationCategory.md) builds the actual category of pairs, its invertible full subcategory and the canonical structured arrow; [RenardAlgebraActionLocalizationInitialityStatements](../../Langlands/Algebra/RenardAlgebraActionLocalizationInitialityStatements.md) states factorization, initiality and the field specialization, and [RenardAlgebraActionLocalizationInitialityProof](../../Langlands/Algebra/RenardAlgebraActionLocalizationInitialityProof.md) proves all three clauses |
| A.III.2 definition, theorem and proof, PDF259–260 | [YonedaStatements](../../Langlands/CategoryTheory/Renard/YonedaStatements.md) and [YonedaProof](../../Langlands/CategoryTheory/Renard/YonedaProof.md): identity evaluation with its inverse, the actual Yoneda Hom equivalence, the representation dictionary and the equivalence with the full subcategory of representable presheaves |
| A.III.2 final remark, proof and corollary, PDF260–261 | [RepresentabilityUniversalStatements](../../Langlands/CategoryTheory/Renard/RepresentabilityUniversalStatements.md): three published statements for universality iff the chosen transformation is an isomorphism, the represented Hom-presheaf sufficient condition, and unique compatible comparison. [RepresentabilityUniversalProof](../../Langlands/CategoryTheory/Renard/RepresentabilityUniversalProof.md) proves all three |
| A.III.3 proposition, PDF261 | [IsomorphismPrincipleStatements](../../Langlands/CategoryTheory/Renard/IsomorphismPrincipleStatements.md) and [IsomorphismPrincipleProof](../../Langlands/CategoryTheory/Renard/IsomorphismPrincipleProof.md): natural Hom equivalences give an actual object isomorphism, and equivalences natural in both variables give an actual natural isomorphism of functors |

In namespace `Langlands.Renard.UniversalArrow`, the theorem
`universalArrowStatements_proof` proves the closed
`UniversalArrowStatements.{vA,vB,uA,uB}`. The proof constructs the
initial or terminal structured-arrow data from the unique factors and
recovers factors from those data in the reverse directions. For each
comparison, factors in both directions give inverse equations by
uniqueness; `Iso.ext` proves uniqueness subject to the compatibility law.
The four object and Hom universes are independent, and the theorem adds
no outer mathematical hypotheses.

In namespace `Langlands.Renard.ModuleLocalization`, the theorem
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

In namespace `Langlands.Renard.Yoneda`, the theorem
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

In namespace `Langlands.Renard.IsomorphismPrinciple`, the theorem `isomorphismPrincipleStatements` proves the closed
`IsomorphismPrincipleStatements.{vC,vM,uC,uM}`. The object component
uses `Yoneda.ext` on the supplied Hom equivalences and their
precomposition naturality. The functor component constructs these
isomorphisms objectwise; naturality in each of the two variables supplies
the naturality equation required by `NatIso.ofComponents`.
There is no additional inverse-naturality premise or relation between
the four universes. On PDF261 both displayed Hom subscripts are printed
C, although their objects lie in M; the statement and proof in the Library
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

The theorem
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

The theorem
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

This completion module makes the source convention boundary explicit.
Renard's vector-space example literally describes continuous maps;
the present derived generalization uses uniformly continuous maps into
complete separated targets. It constructs no vector-space operations
and establishes no continuous-map or continuous-linear-map comparison.
Those obligations remain separate from this uniform proof. The explanatory
rational reciprocal counterexample in the
paired Markdown is not a published Lean theorem.

Both statements are in the Library; their statement checks
establish statement compilation, not a proof of either aggregate.

| Statement | First appeared at Library commit |
| --- | --- |
| Binary diagonal | `cf45df0608b9136ff545b17eadf8297cd7be81fd` |
| Separated uniform completion | `7596502b4fe9738072198e7f23076fa02293f254` |

Both statements have the exact proofs in the Library recorded below.
The statement pairs' hashes were
verified against Library
`7596502b4fe9738072198e7f23076fa02293f254` in the earlier statement audit.
The binary target pair was additionally checked, as first checked, at the
commit where it first appeared, at the base of its proof and in the Library
of the proof audit. The uniform target pair was likewise
checked at the same points and at the commit where its proof first
appeared; it remains unchanged.

### Actual linear completion and the printed continuous-map convention

The Library constructs
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

The statement pair
[RenardTopModuleCompletionStatements](../../Langlands/Topology/RenardTopModuleCompletionStatements.md)
is in the Library. Its closed aggregate
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
is a premise. The Library proves it in
[RenardTopModuleCompletionProof](../../Langlands/Topology/RenardTopModuleCompletionProof.md).
The theorem
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

The Library constructs
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

The statement pair
[RenardRealSequenceCompletionStatements](../../Langlands/Topology/RenardRealSequenceCompletionStatements.md)
is in the Library. Its closed aggregate
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

The Library proves it in
[RenardRealSequenceCompletionProof](../../Langlands/Topology/RenardRealSequenceCompletionProof.md),
as
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

The following three constructions are in the Library. Their
definition checks are of compilation and declaration kind; they do
not prove the universal or nonextension targets.

| Construction | First appeared at Library commit |
| --- | --- |
| Actual topological-module completion | `d2a3dab5880b35349069e39d96304f678174efff` |
| Real-sequence test objects | `d2a3dab5880b35349069e39d96304f678174efff` |
| Restricted polynomial-module equivalence | `d2a3dab5880b35349069e39d96304f678174efff` |

Each was added after a fresh build of the Library with it. All three
Lean/Markdown pairs, as checked, match that commit and the audit base
`5511f7a53d16d5b6af64ff2175ef6c6ecea5347a`. The restricted
equivalence's scope is described next.

Both new completion statement pairs are in the Library, checked as
statements:

| Statement | First appeared at Library commit |
| --- | --- |
| Actual topological-module universal property | `4dd5f7c45ce9b800a0caffa94e2e790953bf7c96` |
| Actual real-sequence completion test | `4dd5f7c45ce9b800a0caffa94e2e790953bf7c96` |

Each was added after a fresh build of the Library with it. Both pairs, as
checked, match that commit and Library `18de63ed841e31dca10a26ef417aea7050cf443f`. The topological-module pair's Lean/Markdown SHA256 values
are respectively
`28413c45eebbdf6385c07c2574283fb6aa51ae47e635cae375a7ab7cda97b427` and
`79284a0ae20c351b98dc9784d1fdf2094e80f8cb13edf2772ad6944c40ddffde`;
the real-sequence pair's are
`31b89cce9e09ccecea2eb32fe1a6a55f0f61d67f734ff5d4118d2acceaeb230a` and
`8190c66dd18e8e80ac2b437106f3717b83f16153102dbec8a0b362317a4d6c85`.
A separate check also compiles
the topological-module construction and statement with zero diagnostics
and inspects `UniversalStatements` as Prop with independent u, v and w.
These are statement and development checks; neither proves an aggregate.

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

The construction was checked as a definition and first appeared
in the Library at
`24af03c708d2441a8b505c2999c4fd8905a0559d`.
Its pair, as checked, matches that commit and the audit base:
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

The restricted-equivalence prerequisite is in the Library.
The `Langlands.Renard.EndomorphismLocalization.localEquivalence.{u,v} R`
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
A separate check on 4 November verified both specializations
with zero diagnostics; it is not a proof in the Library.

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

The Library has two implementations of this construction. The main
[RenardLocalModuleFunctor](../../Langlands/Algebra/RenardLocalModuleFunctor.md)
pair is the construction in
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

The alternative is preserved in
[RenardLocalModuleFunctorUniversalComparison](../../Langlands/Algebra/RenardLocalModuleFunctorUniversalComparison.md),
namespace `Langlands.Renard.ModuleLocalization.UniversalComparison`.
It constructs the same specified chosen-object functor and comparison
through the universal properties of the two verified localization maps.
Its source and canonical transformations are named `sourceRaiseFunctor`,
`chosenLocalizationNatTrans` and `mathlibLocalizationNatTrans`.
The composite below uses these names.

Both are in the Library, checked as definitions, each after a
fresh build of the Library with it:

| Construction | First appeared at Library commit |
| --- | --- |
| current main pair | `50c05a5877c13ea23a52ea298c0ec2bd6fdb0817` |
| relocated alternative | `50c05a5877c13ea23a52ea298c0ec2bd6fdb0817` |

The main pair, as checked, equals the pair at that commit and in the
audit Library. The alternative in the Library differs from the version
checked in the Lean namespace and the companion's
title, namespace and alternative-construction link; it is not a same-path
byte-identical copy of that version. The relocation preserves
its construction and intrinsic laws. Neither module gives an adjunction
or chosen-model sequence-exactness theorem.

### Published chosen endomorphism canonical-arrow comparison

With PE =
`Langlands.Algebra.PolynomialEndomorphism`, ML =
`Langlands.Renard.ModuleLocalization`, EL =
`Langlands.Renard.EndomorphismLocalization`, and κ = max u v w,
the construction is the actual composite

```text
F = PE.toPolynomial R ⋙ ML.chosenLocalFunctor.{u,v,w} (EL.powersX R) ⋙
      EL.localFromPolynomial.{u,κ} R.
```

It is in two published modules. All their declarations
are in `EL.ChosenComparison`. The source module
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

The comparison module
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
Both modules retain arbitrary commutative rings and independent u, v and w.
They keep all intertwiners, zero rings and modules, and zero or nilpotent
source endomorphisms. The field specializations have no dimension
restriction. Neither module asserts a universal property.

The statement module
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

| Module | First appeared at Library commit |
| --- | --- |
| Raised source and chosen arrow | `476a152fd90d846bcb20b9897f53829a768b822c` |
| Explicit functor and arrow comparison | `409542525904dd50036abafdafb8ad1459eadade` |
| Initiality statements | `0bd5bf67c3464359bc8da3b3100163d6ee3da352` |

The two constructions were checked as definitions,
and the statements as statements; these checks are of
compilation and declaration kind, and
none proves the initiality targets. Each was added after a fresh build of
the Library with it. The pairs, as checked, equal those at the commits
where they first appeared and in Library
`4253339ea6afa6e5df9f13373ec3aa96b434ace4`. Their
Lean/Markdown SHA256 values are
`ad56e2ee46bad41d59742fd9687631895b60f697a717f5aa42b4e3a5fa181374` /
`5c44f064a67dcf073b9db780f97bd44e1c113fbe84f479d724e98ed3f09d4f9a`
for the source module,
`249b65e7eec01300ed83bcdd473c7270c1c979100c2f548fe905e59e3194709d` /
`cddf6abd16ae99105992a6deeae5ad6cf4220ae5aa2e943777933045bb1bd052`
for the comparison and
`b7a3246af1356e5994d0cc549b1820e53ae2e17200d3b4a3467ffb496e128c60` /
`c95821e69d974c27d71535203ee8b8d113dd7ab2378013ed191d28b104328a70`
for the statements.

The exact proof is
[RenardEndomorphismLocalizationInitialityProof](../../Langlands/Algebra/RenardEndomorphismLocalizationInitialityProof.md)
proves `EL.ChosenComparison.initialityStatements` at independent u, v and
w with no added hypothesis. It was checked as a proof
by a Lake build against the exact target, with the statement and its inputs
unchanged, and first appeared in the Library at
`910675f18ad6c3d8b09c12c678a0243795a673b9`, after a fresh build of the
Library with it. Its Lean/Markdown SHA256 values
`f9c6be9f25172cce9e618e46b6d3b9b7de03578a26d9e3d16175bed3837e7011` /
`63708fd7643008151676683e8b512e212fcd0704c1458181f897bb0282c198fc`
are equal in the version checked, at that commit and in Library
`f931c96e65d20b436d2363a83d6971f9406ec738`, and the
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
modules package it categorically, and a third module proves the
packaged universal property.

[RenardAlgebraActionLocalizationCategory](../../Langlands/Algebra/RenardAlgebraActionLocalizationCategory.md)
is a definition module in `Langlands.Renard.AlgebraActionLocalization`.
`ActionModuleCat.{u,v,w} k B` has as objects k-modules with an actual
nonunital action `B →ₙₐ[k] Module.End k M`, and as morphisms exactly the
actual linear intertwiners. `ActionEndomorphismCat` is the category of
pairs with a compatible endomorphism, using Mathlib's `Endofunctor.Algebra`.
`InvertibleActionEndomorphismCat` is the full subcategory of pairs whose
endomorphism is a unit, and `invertibleActionInclusion` is its inclusion.
`raisedFunctor` lifts carriers into `max u w x`, and
`canonicalStructuredArrow A` is the structured arrow of the lifted published
`iotaIntertwiner` into `localizedObject A`. The module asserts no universal
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

| Module | First appeared at Library commit |
| --- | --- |
| Category and canonical arrow | `1831431f93603e52c73600a2a900dd42d7f18deb` |
| Initiality statements | `bc859155612cc8ca34e8e25175ce2f7775c217dc` |

The definition was checked as a definition and the statements as
statements; these checks are of compilation and declaration kind,
and neither proves the initiality
targets. The pairs equal those of Library
`dd78edadc914cf56ca81c595cee581a3570d415c`. Their
Lean/Markdown SHA256 values are
`d1c5b34dc1fd8332ecf8a4baa3f43285b4fbea8111b7bdd909021c24169fd9fa` /
`0a7c3f194633bec2ba64d13e24a2d71409ba89e627d5baf632b0f78e9fceb838`
for the category and
`6e1bbfc661b7da8ea2ab558da9b708b2306a91c7cebe2cd9b5b00260e99f047b` /
`270d98dcd0a8b968444939ee6fb65b0e4647d771e574610c6ff25be665a1b75a`
for the statements.

[RenardAlgebraActionLocalizationInitialityProof](../../Langlands/Algebra/RenardAlgebraActionLocalizationInitialityProof.md)
proves the closed theorem `initialityStatements` of the unchanged type
`InitialityStatements.{u,v,w,x}`, with the four universes independent.
The sources and the implemented proof were checked against each other. The proof turns a
map g out of the raised pair into an actual base intertwiner. It applies the
published `EndomorphismLocalization.factor`, which is B-linear by the
published `factor_map_localizedAction`, and packs the result as a morphism
of the full subcategory. The triangle equation comes from
`factor_comp_iota`. Uniqueness among every morphism of the full subcategory
comes from `factor_unique`. `IsInitial.ofUniqueHom` then builds initiality
data for the published `canonicalStructuredArrow A` itself. The theorem
has no outer premises. It uses no universal-property certificate and no
replacement arrow, and adds no hypothesis on k, B, the actions or the source
endomorphism. The field clause specializes the ring clause.

| Proof | First appeared at Library commit |
| --- | --- |
| B-module canonical-arrow initiality | `50126e1b2b20b62d408b52dc3552f01089dd1d11` |

The proof was checked as a proof by a Lake build against the
exact target, with the statement and its inputs unchanged, and was added
after a fresh build of the Library with it. The pair in the Library
equals the version checked, with Lean SHA256
`1596f87bc314a17fff84a4fc2256ee1e0f75c6649dc58bd42f78644286822137` and
Markdown SHA256
`e8b4387fd67cec7b074acdfe30e0f3b67cc60003eecf345e042cd85f841871e6`.
The category and statement pairs at Library
`50126e1b2b20b62d408b52dc3552f01089dd1d11` keep the hashes listed above.
So the categorical B-module universal property of the final sentence of
example 5 is proved in the derived formulation described above.

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

The statement first appeared in the Library at
`da0312e3777850c14b211f6245ff5b08af56f616`.
All three clauses and the five independent
universe parameters were checked.

The Library proves it in
[RepresentabilityUniversalProof](../../Langlands/CategoryTheory/Renard/RepresentabilityUniversalProof.md).
The theorem
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

The proof was checked as a proof by a Lake build against the
exact target, with the statement and its inputs unchanged, and first
appeared in the Library at
`542eaca02a9f2d14f175497b7bf6459436ac5c6d`, after a fresh build of the
Library with it. Its Lean/Markdown SHA256 values
`0c14c9e7cb209f44f4b08179b919910b00882fdd09b9bb2510d546483e56e403` /
`f5baebc3fab561d5d632b0d7f18d9b157c9c0858aaf57ba60beec42f6532b777`
are equal in the version checked, at that commit and in Library
`dd78edadc914cf56ca81c595cee581a3570d415c`. The
statement pair
`06ab1b345a8d60a5a2e00125aa763b70f53a716b3b7357a127b4966c015dd3bd` /
`dacaf272524eb79bc37f544828a0f843e1f8e8c27ede807dd853978b68bec791`
is unchanged.

The supplementary registered `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is discussed in the statement's documentation and its check:
the PDF18 corrections to older printed p.294 l.-11 and p.295 l.6
give the identity-evaluation and transformation-factorization forms
already present in the governing 2026 passage. This is bounded
older-edition evidence, not an exhaustive errata claim.

## Proofs in the Library

All twelve proofs below are in the Library. Each was checked
as a proof by a Lake build against the exact target, with the
statement and its inputs unchanged. Their presence in the Library was
verified separately.

| Proof | First appeared at Library commit |
| --- | --- |
| Universal arrows | `da0312e3777850c14b211f6245ff5b08af56f616` |
| Actual module localization | `da0312e3777850c14b211f6245ff5b08af56f616` |
| Core Yoneda | `676ac944440098acb714f6b953083e88bb89c9c2` |
| Isomorphism principles | `da0312e3777850c14b211f6245ff5b08af56f616` |
| Binary diagonal | `442ff746325df5b6d721fee75d430a65c33d09f0` |
| Separated uniform completion | `d2a3dab5880b35349069e39d96304f678174efff` |
| Actual ring localization | `a4a5fb7b2643f2b9b9a6ac9c41bde7cc387d4a1a` |
| Actual continuous-linear completion | `476a152fd90d846bcb20b9897f53829a768b822c` |
| Fixed-real completion test | `409542525904dd50036abafdafb8ad1459eadade` |
| Endomorphism canonical-arrow initiality | `910675f18ad6c3d8b09c12c678a0243795a673b9` |
| Representability remark and corollary | `542eaca02a9f2d14f175497b7bf6459436ac5c6d` |
| B-module canonical-arrow initiality | `50126e1b2b20b62d408b52dc3552f01089dd1d11` |

At audit base `b3c3e9d6d2583790775c36d7a1ac7db8baaf9e48`,
the first four proof pairs and the representability statement pair
match the SHA256 values of the versions checked in that Library
and at the commits where they first appeared. All project statement/dependency
pairs imported by the four proofs also match their proof base,
first-appearance commit and that Library. This documentation audit
changes none of those mathematical files and supplies no new Lean result.

The binary proof first appeared in the Library at
`442ff746325df5b6d721fee75d430a65c33d09f0`, after a fresh build of the
Library with it. The proof pair, as checked and at that commit, matches SHA256
`4d2a7ac876073efe5d8810e62133bd28f0407d94cec0c99c8a86f30aafacf542`
for Lean and
`7db8f732216b3e3db51a4cde6472e0156eec3ee2d9bb3fb49637bdc4da727c72`
for Markdown. The target statement pair remains unchanged.

The uniform proof first appeared in the Library at
`d2a3dab5880b35349069e39d96304f678174efff`, after a fresh build of the
Library with it.
The proof pair, as checked, matches that commit and the audit base:
Lean SHA256
`f7973315aeb53c100955636e69ab5669ddb7d53c50341e0f488759c74dc7f158`,
Markdown SHA256
`46a2dfd83063cd499c4de86713c670f646f3a7af304e361adc8cfec2405a94bc`.
The unchanged target pair has Lean SHA256
`8d7f1963aedaeb86d9e25f6ee26c1999bdf8df1efc6bf8f66aea66e3bf87402c`
and Markdown SHA256
`a7bf3f4081f9a74071c8911233f762071cbd852476b1471c308e0cec695ee366`.

The continuous-linear completion proof first appeared in the Library at
`476a152fd90d846bcb20b9897f53829a768b822c`, after a fresh build of the
Library with it. The proof pair, as checked, equals
that commit and audit Library
`9caf47cacd8f25d9a56aa0737b4256267bf62d16`:
Lean SHA256
`dee60a4d1f418a56cf9e780ddcb51c49fff777419bd050275077a6b7d971c0e9`,
Markdown SHA256
`ba10fa0a66b344da3a677e4167b1199ce452007e711fe83ba1e67f14b328d783`.
The published statement remains unchanged, with the hashes recorded above.
A separate check also compiles the
proof with zero diagnostics.

The fixed-real proof first appeared in the Library at
`409542525904dd50036abafdafb8ad1459eadade`, after a fresh build of the
Library with it. The proof pair, as checked,
equals that commit and Library
`4253339ea6afa6e5df9f13373ec3aa96b434ace4`: Lean SHA256
`42587719a0f37fe314a9a49f7671e153888d540332b13a3d340f8c5af73c4e64`,
Markdown SHA256
`a8c5e0bbf2c6de2c316a019138ad940eab50376c004700edc091d7f8af40aaab`.
The target statement pair is unchanged, with the hashes recorded above.

## Published ring-denominator construction and categorical proof

The Library constructs
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

The definition was checked as a definition for compilation
and declaration kind; this is not a proof of categorical universality.
It first appeared in the Library at
`442ff746325df5b6d721fee75d430a65c33d09f0`, after a fresh build of the
Library with it.
The pair, as checked and at that commit, matches SHA256
`a067de0e8559d9783c9ef153b987e01a2ac620217836a38141081f95b8c68bc8`
for Lean and
`19ccc2d16d0435cf2848cc7aefea9eebecc7dc611a4359f81e0dfa5c9a40b65e`
for Markdown. A separate compilation and declaration inspection passed with
zero diagnostics.

The statement module, in the Library, declares
`Langlands.Renard.RingLocalization.CategoricalUniversalStatements` in
`Langlands.Algebra.RenardLocalRingUniversalStatement`. Its three closed
clauses assert the actual chosen-factor equation, uniqueness among all
local-category factors satisfying it, and initiality of the actual canonical
structured arrow. It retains the same image submonoid, arbitrary common u
and zero boundary. Its compilation was checked. It first appeared in the
Library at
`50c05a5877c13ea23a52ea298c0ec2bd6fdb0817`, after a fresh build of the
Library with it. The pair, as checked, matches that commit and the audit
base: Lean SHA256
`542fcc71d4d2beebef95e80d3c6ba0857d8d8c16d3eb4c8073718fa7360eeff5`,
Markdown SHA256
`08bec4b9b8c3009bff8c889b4df147e941520c5bd4763fcea5fba1f348a34c67`.

The Library proves it in
[RenardLocalRingUniversalProof](../../Langlands/Algebra/RenardLocalRingUniversalProof.md).
The theorem
`Langlands.Renard.RingLocalization.categoricalUniversalStatements`
proves exactly the unchanged closed `CategoricalUniversalStatements.{u}`,
with the source correspondence, statement design and factorization
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

The proof first appeared in the Library at
`a4a5fb7b2643f2b9b9a6ac9c41bde7cc387d4a1a`, after a fresh build of the
Library with it. The proof pair, as checked, matches that commit and
Library `b01e426d540ff0d2edcc0480f6f0d03dd2f71e78`:
Lean SHA256
`713604c936253dc02b615242cf8e4dbccc4124c8ec1622133eea2466bda931dd`,
Markdown SHA256
`9903008248140a079c87e063cf9b0602dab64f672bf43fa0ac7b5c229ec21d9c`.
The construction and statement pairs also match the proof base,
first-appearance commit and checked Library, with the unchanged
hashes recorded above. The proof was checked by a Lake build against the
exact target, with the statement and its inputs unchanged.
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
This note records no exactness comparisons with these chosen models; an
existing exact Mathlib functor is available for reuse.
For the final B-module sentence of example 5, the unique factorization among
actual B-linear intertwiners is public as
`Langlands.Renard.AlgebraActionLocalization.universalPropertyStatements`;
see the [endomorphism-localization note](endomorphism-localization.md).
Its categorical structured-arrow packaging, initiality statements and their
exact proof are public, as recorded [above](#the-b-module-variant-of-example-5).
The A.III.2 representability remark and corollary are proved. Further
compatible comparisons for the concrete constructions and their adjunctions
retain separate obligations. Existing adjunction results can be found in the
[A.V source map](adjunctions-progress.md).
The twelve proofs above do not complete these remaining comparisons.

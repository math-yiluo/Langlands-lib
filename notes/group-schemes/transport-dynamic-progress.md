# Group schemes: published transport, dynamics and fpqc reflection

This focused progress ledger records eight transport construction units and three
exact-statement proofs for the algebraic and reductive group-scheme program
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e`, revision 2. Worker 1107 verified their
independent acceptance, publication and entry-file hashes on 3 November 2026.
The eight construction units contribute to several thematic families; they do
not constitute eight completed families. The standing program remains incomplete.
The [initial reuse ledger](../reuse/algebraic-groups-reuse-ledger.md) preserves
the earlier outside-source audit and port experiments.

All Lean names below are in `Langlands.GroupScheme` unless qualified otherwise.
Use the current Library modules by name. Artifact and receipt identifiers below
record publication evidence; they are not mathematical inputs to Lean imports.
Each module link leads to its implemented declarations, and its paired Markdown
explains provenance, conventions, hypotheses and the proof route.

## Transport conventions and shared inputs

The cross-torus modules start with acting commutative group schemes `T, T'`,
ambient group schemes `G, H`, maps `i : T.toGrp ⟶ G`, `j : T'.toGrp ⟶ H`,
actual isomorphisms `e : T ≅ T'`, `f : G ≅ H`, and the supplied equality

```lean
i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j
```

The character identification `characterLattice.congr e` sends `a` to
`e.inv ≫ a`. Forward point transport postcomposes with `f.hom`; inverse
transport postcomposes with `f.inv`. For `f = G.innerIso g`, these maps are
`x ↦ g_U * x * g_U⁻¹` and `y ↦ g_U⁻¹ * y * g_U`, using the same supplied
point `g` pulled back to each test scheme `U`.

These are derived internal constructions from the existing actual group-scheme,
subgroup-functor, kernel, Lie and lattice interfaces. They construct comparisons
from the supplied data. Torus existence and conjugacy, structural realizations
and representability existence remain separate assertions. All subgroup-functor
identities retain nonreduced tests; character kernels retain their full
scheme-theoretic structure.

## Eight published transport constructions

| Unit and implementation | Exported comparison | Exact scope and retained inputs |
| --- | --- | --- |
| [Restricted standard conjugation](../../Langlands/GroupScheme/Rational/StandardRestrictedConjugation.lean) ([Markdown](../../Langlands/GroupScheme/Rational/StandardRestrictedConjugation.md)) | `restrictedStandardSubgroups_eq_comap_of_character_images`, `restrictedStandardParabolicConjEquiv`, `restrictedStandardUnipotentConjEquiv` | Any field; affine ambient group; monomorphic underlying map `i`; finite `simpleRelativeRoots i ν`; `I₀ ⊆ J₀`, `I₁ ⊆ J₁`; standard cocharacters for both `J` sets; one normalizer point with both specified character-image equations. Gives all-test comparisons of `L_J ∩ P_I` and `L_J ∩ U_I`, including both ambient conjugation formulas. |
| [Associated standard conjugation](../../Langlands/GroupScheme/Rational/StandardAssociatedConjugation.lean) ([Markdown](../../Langlands/GroupScheme/Rational/StandardAssociatedConjugation.md)) | `associatedStandardSubgroups_eq_comap`, `associatedStandardParabolicConjEquiv`, `associatedStandardUnipotentConjEquiv` | Any field; affine ambient group; monomorphic underlying map `i`; finite enumerations of `SimpleRoot i ν` and `relativeWeylGroup i`; supplied Coxeter system and `IsRelativeWeylCoxeterRealization`; a normalizer point representing `longestRep cs J`. Specializes the preceding comparisons to every subset of `associatedSubset cs J`, including empty subsets. The realization remains an input. |
| [Transporter differences and range orbits](../../Langlands/GroupScheme/Rational/TorusTransporterOrbit.lean) ([Markdown](../../Langlands/GroupScheme/Rational/TorusTransporterOrbit.md)) | `isNormalizingPoint_inv_mul_of_transporters`, `torusRangeOrbitEquivQuotient` | Arbitrary base scheme. Two supplied transporters to the same embedded acting group have difference `h⁻¹g` in the source normalizer. With the underlying map `i` monomorphic, the orbit of the full range subgroup functor is equivalent to the set of left cosets `G(B)/N(B)`. No normality of `N(B)` or quotient-group structure is asserted. |
| [Root subgroup and character-kernel transport](../../Langlands/GroupScheme/Rational/CrossTorusRootTransport.lean) ([Markdown](../../Langlands/GroupScheme/Rational/CrossTorusRootTransport.md)) | `RelativeRoot.characterKernelCongr`, `RelativeRoot.subgroup_comap_of_transport`, `RelativeRoot.subgroupTransportEquiv` | Arbitrary base scheme and the supplied square. Identifies full character kernels and orbit-extension root subgroup functors; restricts the ambient isomorphism on every test. No root-membership, smoothness or monomorphism premise is needed. |
| [Lie weights and relative roots](../../Langlands/GroupScheme/Rational/CrossTorusLieTransport.lean) ([Markdown](../../Langlands/GroupScheme/Rational/CrossTorusLieTransport.md)) | `Lie.targetEquiv`, `weightSpaceTransportEquiv`, `rootsTransportEquiv`, `relativeRootsTransportEquiv` | Over `Spec R`, with `R` a commutative ring and both ambient structure maps affine, the supplied square gives linear equivalences of the actual dual-number Lie kernels and all-coefficient-algebra weight spaces. Over a field, simultaneous character/cocharacter transport preserves relative roots, positivity, simple roots and `IsGenericCocharacter`. The full possibly nonreduced root set is retained. |
| [Full kernel-centralizer transport](../../Langlands/GroupScheme/Rational/CrossTorusKernelCentralizer.lean) ([Markdown](../../Langlands/GroupScheme/Rational/CrossTorusKernelCentralizer.md)) | `RelativeRoot.kernelCentralizer_comap_of_transport`, `RelativeRoot.kernelCentralizerTransportEquiv` | Arbitrary base scheme and the supplied square. Preserves commutation with every point of the full character kernel after every refinement. Gives all-test multiplicative equivalences and restriction naturality, without a smoothness or representability assumption. |
| [Transport of supplied representatives](../../Langlands/GroupScheme/Rational/RepresentedCrossTorusTransport.lean) ([Markdown](../../Langlands/GroupScheme/Rational/RepresentedCrossTorusTransport.md)) | `RelativeRoot.subgroupTransportIso`, `RelativeRoot.kernelCentralizerTransportIso` | Arbitrary base scheme and the supplied square, with representing inclusions and their `IsRepresentedBy` proofs supplied on both sides. Constructs actual group-scheme isomorphisms, both inclusion squares and comparison with the existing point equivalences in both directions. Does not prove existence of representatives. |
| [Normalizer, centralizer and rational Weyl transport](../../Langlands/GroupScheme/Rational/CrossTorusWeylTransport.lean) ([Markdown](../../Langlands/GroupScheme/Rational/CrossTorusWeylTransport.md)) | `normalizerPointsTransportEquiv`, `centralizerPointsTransportEquiv`, `relativeWeylTransportEquiv`, `relativeWeylCharacterAction_transport` | Normalizer and centralizer point-group equivalences over any base, from the supplied square. Over a field, identifies the actual quotient groups `N(k)/Z(k)` and their representatives. Both character-action intertwining results require monomorphic underlying maps `i` and `j`; the group equivalences themselves do not. |

For the orbit and Weyl results, quotients of groups of points have exactly the
meanings stated above. No comparison with points of a sheaf quotient is supplied.
The standard-family units retain finite-root and standard-cocharacter or Coxeter
realization inputs. The cross-torus units retain the isomorphisms and their square.
None of these inputs is an unconditional reductive structure theorem.

Worker 1107 authored the eight units. Workers 76 and 165 contributed the
restricted/associated standard-family interfaces, and Worker 118 contributed
the transporter and cross-torus consumer interfaces; the immutable submissions
retain their coauthorship. These units provide algebraic comparisons for later
consumers; building, topology and valuation assertions are outside their scope.

## Published dynamic smoothness and connectedness proofs

The exact propositions are
[`DynamicSmoothStatement` and `DynamicConnectedStatement`](../../Langlands/GroupScheme/Dynamic/SmoothConnectedStatement.lean)
([Markdown](../../Langlands/GroupScheme/Dynamic/SmoothConnectedStatement.md)).
Both quantify over any field `k`, a group scheme `G` over `Spec k` with smooth
affine structural morphism, every cocharacter `χ`, and any homomorphism `j : H ⟶ G`
representing the indicated dynamic subgroup functor.

- [`dynamicSmooth`](../../Langlands/GroupScheme/Dynamic/SmoothProof.lean)
  ([proof description](../../Langlands/GroupScheme/Dynamic/SmoothProof.md)) proves
  smoothness of representatives of each of `Dynamic.parabolic χ`,
  `Dynamic.centralizer χ` and `Dynamic.unipotent χ`. Its graded-coordinate and
  retract route has noetherian-ring helper results; the exact final statement is
  over fields. It does not discharge the unrestricted-base smoothness theorem.
- [`dynamicConnected`](../../Langlands/GroupScheme/Dynamic/ConnectedProof.lean)
  ([proof description](../../Langlands/GroupScheme/Dynamic/ConnectedProof.md)) proves
  that a representative of `Dynamic.unipotent χ` is connected. If `G` is
  connected, representatives of `Dynamic.parabolic χ` and
  `Dynamic.centralizer χ` are connected as well. Ambient connectedness is not
  required for the unipotent assertion. The implementation uses the published
  unipotent contraction, opposite open cell and limit-map section.

The paired files document the relationship to CGP Proposition 2.1.8(3),(4).
These are exact proofs of the published propositions, with the hypotheses above;
the adjective “unipotent” in a dynamic functor name alone does not discharge all
geometric unipotent-radical comparisons required by the program.

## Published fpqc reflection of central isogenies

[`centralIsogenyFpqcReflection`](../../Langlands/GroupScheme/CentralIsogeny/FpqcReflection.lean)
([proof description](../../Langlands/GroupScheme/CentralIsogeny/FpqcReflection.md))
proves the exact
[`CentralIsogenyFpqcReflectionStatement`](../../Langlands/GroupScheme/CentralIsogeny/FpqcReflectionStatement.lean)
([Markdown](../../Langlands/GroupScheme/CentralIsogeny/FpqcReflectionStatement.md)).
For any schemes `S, S'`, a surjective flat quasi-compact map `b : S' ⟶ S`,
and any `f : G ⟶ H` of group schemes over `S`, the implication is

```lean
IsCentralIsogeny ((GroupScheme.baseChange b).map f) → IsCentralIsogeny f
```

This retains finiteness, flatness, surjectivity, local finite presentation and
centrality of the full scheme-theoretic kernel in `IsCentralIsogeny`. The proof
descends the four morphism properties and reflects all-test kernel commutation.
No smoothness of a centre or kernel and no representable-centre hypothesis is
added. This descent result does not construct a derived group, adjoint quotient
or simply connected cover.

## Independent acceptance and publication evidence

Every row below was fetched as accepted and public. The eight construction rows
carry `lean.definition@1` receipts with Lake-build and declaration-kind checks;
they include their intrinsic lemmas. The three proof rows carry `lean.proof@1`
receipts with Lake-build, exact-target, unchanged-statement and frozen-input
checks. Each also has independent semantic acceptance by the named reviewer.
All eleven entry Lean/Markdown pairs matched their frozen hashes and Library
commit `83afd4553e9b793a825b53a9504028c880852999` when checked. Publication
commits below identify the respective integration, rather than a new proof claim
made by this note.

| Module | Candidate | Accepted machine receipt | Independent reviewer | Publication commit |
| --- | --- | --- | --- | --- |
| `StandardRestrictedConjugation` | `6ce4961e-9d15-4cff-a3f8-4ab583c8f9d2` | `276cbe5a-9941-40c9-adb8-cbdbad40db2f` | Reviewer 10940 | `25b91125ea94e88d741b206d633e82eb0d87c3e5` |
| `StandardAssociatedConjugation` | `15727b4d-a1a1-439d-b163-d464a4cf1877` | `0648a199-1562-4401-a0a4-8f152a4f554e` | Reviewer 11016 | `25b91125ea94e88d741b206d633e82eb0d87c3e5` |
| `TorusTransporterOrbit` | `8a4f0462-9c26-43d1-a71a-bec849f74e9f` | `ac91dde0-746a-4976-a2c9-b357a727d40f` | Reviewer 11071 | `25b91125ea94e88d741b206d633e82eb0d87c3e5` |
| `CrossTorusRootTransport` | `df1718d4-80dc-46f5-af44-ee8473a5cf3c` | `c856e705-37ad-4e17-863f-4424595174fe` | Reviewer 11109 | `25b91125ea94e88d741b206d633e82eb0d87c3e5` |
| `CrossTorusLieTransport` | `39545723-a4eb-447d-9a7c-831da24fa822` | `b9cc27e3-ba2f-40c6-be9c-f2dab8fc4c02` | Reviewer 11165 | `25b91125ea94e88d741b206d633e82eb0d87c3e5` |
| `CrossTorusKernelCentralizer` | `c1b65ef8-4593-41e0-8608-ed40177c12b2` | `f83fa381-e8da-4f95-9906-ff068ab5e418` | Reviewer 11190 | `25b91125ea94e88d741b206d633e82eb0d87c3e5` |
| `RepresentedCrossTorusTransport` | `e5ea7da2-c72e-4cb5-967f-a5798f6c6b3a` | `821e1765-9ec9-4edf-8d1e-5dab678824b4` | Reviewer 11221 | `25b91125ea94e88d741b206d633e82eb0d87c3e5` |
| `CrossTorusWeylTransport` | `e344068c-f210-43b2-b74e-49bf9ccb5c67` | `f1965208-ca75-4cc6-8481-f439212d1861` | Reviewer 11262 | `25b91125ea94e88d741b206d633e82eb0d87c3e5` |
| `SmoothProof` | `e9a3c1f3-ca63-4651-b2ee-9a98900e265e` | `23858ee8-98d3-45b4-9093-0cb6c00c6708` | Reviewer 9948 | `405ff58c5df69766419c9941161444531c1979ae` |
| `ConnectedProof` | `54f1fc10-177b-4be0-a8b6-a1975ccaf646` | `b3c13199-4aab-4672-8236-1dc42b54726d` | Reviewer 10887 | `f799bd3b181a5ac1fb60bf3bb48f384b5be31d01` |
| `FpqcReflection` | `b4561344-76b4-4641-9e55-3e442184adbc` | `6c3822e0-d073-4ffc-b10f-6e07da5d4548` | Reviewer 11026 | `25b91125ea94e88d741b206d633e82eb0d87c3e5` |

## Contribution to the eight thematic families

This table locates only the results verified in this note. The remaining column
names obligations of the standing contract that these units do not discharge;
it is not an exhaustive assertion about every other published module.

| Contract family | Contribution recorded here | Obligations outside this note's evidence |
| --- | --- | --- |
| 1. Group-scheme and affine foundations | Actual full-kernel, subgroup-functor and represented-subgroup transport; Lie-kernel functorial comparisons. | General quotient existence, flatness and the other required affine/Hopf and Lie structure bridges. |
| 2. Tori and multiplicative type | Character transport, full character-kernel comparison and orbit indexing for supplied embeddings. | Torus/Galois-lattice classification, finite-separable restriction and norm comparisons, and the concrete non-split milestone. |
| 3. Unipotent structure and geometric reductivity | Smoothness of dynamic P/Z/U and connectedness in the precise field scope above. | Geometric unipotence and radical comparisons, reductivity theorems and imperfect-field distinctions. |
| 4. Absolute structure over fields | Transport of actual root functors and Lie weights, with scheme isomorphisms when representatives are supplied. | Existence of maximal tori/Borels, root datum and root subgroup realizations, structural conjugacy and Bruhat results. |
| 5. Rational structure | Standard-family conjugation with its explicit finite-root/realization inputs; transport of relative roots, positivity and `N(k)/Z(k)`. | Unconditional realization, maximal split torus existence/conjugacy, rational structural decompositions and the noncommutative non-split example. |
| 6. Galois and central structure | Full character-kernel transport and arbitrary-base fpqc reflection of central isogenies. | Finite-Galois effectivity, star-action comparisons, derived/adjoint and cover constructions and their root-data bridges. |
| 7. Split realization and classification | No realization or classification result is established by these units. | Actual split realization, pinning, classification and morphism/isogeny comparisons. |
| 8. Relative structure over general bases | Arbitrary-base transport, supplied-representative comparisons and fpqc reflection. | Unrestricted-base dynamic smoothness, relative existence/descent and locality-qualified structural comparisons. |

The GL and Deligne first milestone, the subsequent unitary example, and the full
source-to-declaration ledger require their own verified evidence. The present
note adds focused publication records and usable algebraic interfaces without
changing those obligations or existing task ownership.

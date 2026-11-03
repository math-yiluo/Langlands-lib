# Actual coordinate augmentation weights and remaining proof targets

This note inventories the constructions and precise proposition targets of task
`7a21605a-8f42-4554-8610-b8fdf28b233d`. The mathematical entries are separate
construction and statement submissions. A proposition declaration records an
obligation; it does not supply a proof. Each of the seven target groups below
has a published focused proof successor.

The source is Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition
(2015), §3.3, printed pp.107–108 / PDF pp.133–134, especially Example 3.3.2.
The registered source is `conrad-gabber-prasad-2015-pseudo-reductive`, with SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The explicit coordinate presentations, all-algebra formulas and functorial maps
are derived implementation interfaces. The extension to arbitrary pointed affine
schemes generalizes the source's stable pointed subvarieties; reducedness and
finite type are not needed for the decomposition target itself.

## Actual objects and constructed laws

All module names in this note have prefix `Langlands.GroupScheme.Rational`;
declaration names have prefix `Langlands.GroupScheme`.

| Module | Construction and proved laws |
| --- | --- |
| `CoordinateAction` | `CoordinateWeights.Coord` is the existing `Lie.coordinateAlgebra`. Universal-point evaluation constructs actual coordinate pullback and its identity and composition laws. The actual action gives algebra automorphisms after every coefficient extension, preserves evaluation at the identity, and defines coordinate and augmentation eigenspaces and nonzero augmentation support. Equivariant pullback preserves weights. The represented stable-subgroup inclusion is equivariant. |
| `CoordinateCotangent` | `CoordinateWeights.Cotangent` is the actual quotient `I/I²` of the identity augmentation ideal. The module constructs the quotient map, the augmentation and cotangent after coefficient extension, the induced action, and its all-algebra eigenspaces and support. |
| `PointedCoordinateAction` | `PointedCoordinateWeights.PointedAction` retains an actual scheme action and a fixed rational point, without requiring a group law on the affine scheme. All-test stability along a monomorphic inclusion constructs the restricted action. Actual coordinate and augmentation maps satisfy the analogous evaluation and transport laws. Pointed equivariant isomorphisms preserve support. Injective pullback and explicitly assumed same-weight lifts give the two support-containment directions. |
| `CoordinateCotangentPullbackStatement` | Besides its remaining proposition target, this module constructs `CoordinateWeights.cotangentPullback` using `Ideal.mapCotangent`, proves its class formula and identity and composition laws, and constructs the cotangent equivalence of an actual group-scheme isomorphism. |

The action convention is the source's positive pullback formula
`(s.f)(g) = f(b.act s g)`. The eigenconditions test every commutative coefficient
algebra and every pair of algebra-valued points. Neither rational-point density
nor an unrelated abstract grading replaces the specified scheme action.
The four `PointedCoordinateWeights.ofGroup_*` equalities identify group
specialization with the existing coordinate objects and character labels.

Support means that an augmentation eigenspace contains a nonzero function.
It may be empty. The zero character is allowed when it occurs and is never
inserted automatically. Coordinate support remains distinct from the original
`RelativeRoot.actionWeightSupport` on the actual Lie kernel.

## Exact outstanding propositions

Each successor uses policy `lean.proof@1`, pins environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, and requires publication of its exact
statement. All targets retain arbitrary universe `u` and all field
characteristics.

| Exact declaration after `Langlands.GroupScheme.` | Module | Remaining conclusion | Proof successor task |
| --- | --- | --- | --- |
| `CoordinateWeights.CoordinateWeightDecompositionStatement` | `CoordinateWeightDecompositionStatement` | For split-torus actions on affine groups, internal direct sums of coordinate, augmentation and cotangent eigenspaces, and same-character lifts from cotangent to augmentation. | `ccddf7a7-e580-4d6a-9009-75424a7e54c1` |
| `CoordinateWeights.CoordinateLieComparisonStatement` | `CoordinateLieComparisonStatement` | The three actual kernel-duality, action-pairing and support comparisons detailed below. | `e1a78681-725a-40f5-af98-93856cb7ac28` |
| `CoordinateWeights.CoordinateSemigroupComparisonStatement` | `CoordinateSemigroupStatement` | For smooth connected affine groups and split tori, the positive-semigroup equality and equivalent containment criterion detailed below. | `afd5b210-636d-4e7b-a143-0bc11df29d9b` |
| `CoordinateWeights.CotangentPullbackStatement` | `CoordinateCotangentPullbackStatement` | Actual equivariant group pullback preserves each cotangent weight space; actual equivariant group isomorphisms preserve cotangent support. | `f664e382-76db-4c65-bc03-4254ea82e431` |
| `PointedCoordinateWeights.PointedCoordinateDecompositionStatement` | `PointedCoordinateDecompositionStatement` | For actual split-torus actions on arbitrary pointed affine schemes, internal direct sums of the coordinate and fixed-point augmentation eigenspaces. | `4e087cc6-722e-47e9-a978-3f120cb386bc` |
| `PointedCoordinateWeights.DominantPullbackStatement` | `DominantPullbackStatement` | A dominant morphism of actual affine schemes with reduced target gives injectivity of the specified coordinate pullback. | `1f93b03c-7810-4fc3-a4e3-f213ae57e74b` |
| `PointedCoordinateWeights.ClosedImmersionPullbackStatement` | `ClosedImmersionPullbackStatement` | An actual pointed equivariant closed immersion for a split torus gives coordinate and augmentation surjectivity, images equal to the same-character weight spaces, augmentation weightwise lifts, and source support contained in target support. | `536e7301-29bf-425e-abdc-bbe53e5620d4` |

The Lie-comparison conjunction contains the exact declarations
`CoordinateWeights.KernelCotangentDualityStatement`,
`CoordinateWeights.CotangentActionPairingStatement`, and
`CoordinateWeights.CotangentLieSupportStatement`. The first specifies duality
through `Lie.kernelDerivationEquiv` over every coefficient algebra. The second
requires pairing with the actual action on dual-number kernel points and the
actual base-changed cotangent pullback. Both require affine groups but no
smoothness or finite-type assumption. The third retains local finite type and
splitness and asks for equality with the original intrinsic Lie support, using
the same character labels.

The semigroup conjunction contains
`CoordinateWeights.AugmentationLieSemigroupStatement` and
`CoordinateWeights.AugmentationLieContainmentStatement`. Their conclusions are
respectively

```text
CoordinateWeights.support b
  = AddSubsemigroup.closure (RelativeRoot.actionWeightSupport b ⊤)

CoordinateWeights.support b ⊆ M
  ↔ RelativeRoot.actionWeightSupport b ⊤ ⊆ M
```

where the first equality uses the underlying set of the closure and the second
holds for every additive subsemigroup `M`, including the empty one. These are
positive finite-sum closures, not submonoid closures with an inserted empty sum.
Smoothness and connectedness remain explicit hypotheses of these two targets.
The source's nonzero-product and local-filtration arguments remain proof work.

## Consumer boundaries

The separate pointed decomposition is needed because closures of commutator
images need not be subgroups. Its conclusion includes both spanning and
independence, without reducedness, finite type or a group law on the pointed
scheme. Closed-immersion weightwise lifting needs decomposition in addition to
ordinary quotient surjectivity. Dominant pullback retains reducedness because
topological dominance alone does not detect target nilpotents.

These interfaces serve `RelativeRoot.SemigroupCommutatorStatement` and
`RelativeRoot.SemigroupRealizationStatement` in `WeightSemigroupStatement`
without assuming either consumer conclusion. All-test stability of the concrete
commutator image and the support calculation for its finite products are
separate consumer obligations. Completing the construction and statement
publications does not discharge the seven proof successors above.

# Actual Tits indices: existence, anisotropic kernel and open targets

Author: Worker 47, 13 November 2026.

This note records the status of the Library's actual Tits-index interface for
semisimple groups over arbitrary fields: the two published proofs, the
statements that are still unproved with their proof tasks, how to use the
existence theorem, and its role in the local rank-one classification. It
describes Library commit `cfedefb680f317b0ea5d351023e1c9dd886b2547`. All
declarations are in the namespace `Langlands.GroupScheme`.

## Source and interface

The source is J. Tits, *Classification of algebraic semisimple groups*
(1966), §§2.1–2.3, printed pp.38–39 (proceedings PDF pp.43–44), registered as
`tits-1966-classification-algebraic-semisimple`. The interface module is
[`Reductive.TitsIndex`](../../Langlands/GroupScheme/Reductive/TitsIndex.md).
Its Markdown gives the exact source locators and explains the encoding.

For a field `k : Type u` and a group scheme `G` over `Spec k` with
`[IsAffineHom G.X.hom]` and `[LocallyOfFiniteType G.X.hom]`, a term of
`TitsIndexData G` has these fields:

- `isSemisimple : IsSemisimple G`;
- `pinning : GaloisPinningData k (SeparableClosure k) G`, with a `k`-torus,
  its inclusion into `G`, a reduced root datum on the actual lattices of the
  torus over the separable closure, a base and a pinning;
- `maximalTorus`: that inclusion is a maximal torus over `k`;
- `splitTorus`, `splitInclusion` and `maximalSplit`: an actual maximal split
  torus `S ⟶ G`;
- `torusMap` and `square`: a map `S ⟶ T` whose composite with the torus
  inclusion is the split inclusion;
- `positiveCocharacter` and `generic`: a cocharacter of `S` that pairs
  nonzero with every relative root (`IsGenericCocharacter`);
- `compatible`: every absolute root whose restriction to `S`
  (`absoluteRootRestriction`) is nonzero is positive for the chosen base if
  and only if its restriction pairs positively with the cocharacter.

The last two items encode Tits's compatible orders by finitely many signs.
Absolute roots with zero restriction are ordered by the chosen base alone.
The namespace `TitsIndexData` then defines `Vertex`, `cartan`,
`rootRestriction`, `zeroVertices` (`Δ₀`), `distinguishedVertices`, the star
action `star` with `star_one` and `star_mul`, and the quotient
`DistinguishedOrbit`. `TitsIndexEquiv d e` compares two indices over the same
field by a vertex bijection that preserves Cartan pairings, `Δ₀` and the
action of each Galois element.

## Status

| Statement | Module | Status at `cfedefb6` |
|---|---|---|
| `TitsIndexExistenceStatement` | `Reductive.TitsIndexChoiceStatement` | proved: `titsIndexExistence` |
| `TitsIndexIndependenceStatement` | `Reductive.TitsIndexChoiceStatement` | unproved; task `338330a2-05d3-4923-af79-cfb245116ae2` |
| `TitsIndexChoiceStatement` | `Reductive.TitsIndexChoiceStatement` | unproved; needs only independence |
| `TitsIndexStarInvariantStatement`, `TitsIndexRelativeSimpleRootsStatement` (bundled as `TitsIndexStarRelativeRootsStatement`) | `Reductive.TitsIndexRelativeStatement` | unproved; task `893d04c0-ec89-45ab-a1e1-46f4a0ad7ca0` |
| `TitsIndexSplitRankStatement` | `Reductive.TitsIndexRelativeStatement` | unproved; task `4280bc84-8750-4f37-ada6-2b41879fc4d6` |
| `TitsIndexRelativeStructureStatement` | `Reductive.TitsIndexRelativeStatement` | unproved; the conjunction of the two rows above |
| `TitsAnisotropicKernelStatement` | `Reductive.TitsIndexAnisotropicKernelStatement` | proved: `titsAnisotropicKernel` |
| `TitsAnisotropicKernelIndexStatement` | `Reductive.TitsIndexAnisotropicKernelStatement` | unproved; task `4073241d-236c-4ef4-9f74-ea19216c6ccd` |
| `TitsAnisotropicKernelStructureStatement` | `Reductive.TitsIndexAnisotropicKernelStatement` | unproved; needs only the index statement |

The two proofs are:

- `titsIndexExistence : TitsIndexExistenceStatement.{u}`, module
  [`Reductive.TitsIndexExistenceProof`](../../Langlands/GroupScheme/Reductive/TitsIndexExistenceProof.md),
  by Worker 148 in Task 5621 (`0559cf0c-3421-4cff-b257-2f60f9ef9c82`),
  artifact `8918509e-3ce9-4f74-a7d2-cf80732f00ac`, accepted by Reviewer 202.
- `titsAnisotropicKernel : TitsAnisotropicKernelStatement.{u}`, module
  [`Reductive.TitsIndexAnisotropicKernelProof`](../../Langlands/GroupScheme/Reductive/TitsIndexAnisotropicKernelProof.md),
  by Worker 145 in Task 5618 (`84825882-92e4-4cb1-aed1-e94d39bf9c39`),
  artifact `1ecfc00c-33f7-46d9-b23c-e06a851943b1`, accepted by Reviewer 206.
  For any index data `d`, it shows that every derived subgroup of every actual
  representative of the centralizer of `d.splitInclusion` is semisimple and
  anisotropic.

Neither proof assumes an unproved Library statement.

## Using the existence theorem

The statement is

```
def TitsIndexExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom],
    IsSemisimple G → Nonempty (TitsIndexData G)
```

so `titsIndexExistence k G hG : Nonempty (TitsIndexData G)` for
`hG : IsSemisimple G`. The field, its characteristic and the universe are
arbitrary. There is no perfectness, infinite-field, local-field or
positive-rank hypothesis, and characteristic two and rank zero are included.

The theorem gives some index data, not a canonical one. Every other statement
in the table, and `LocalRankOneTitsIndexStatement`, quantifies over all
`d : TitsIndexData G`, so it applies to the data obtained this way. A
conclusion that depends on which `d` was chosen still needs
`TitsIndexIndependenceStatement`. For `hind` of that type,
`⟨titsIndexExistence, hind⟩ : TitsIndexChoiceStatement.{u}`.

Worker 47 compile-checked the application `titsIndexExistence k G hG`, this
pair and the use in `localRankOneClassification_of_indexStatements` below with
`lean_check` against this Library.

## Route of the existence proof

The proof Markdown describes each step. In outline:

1. `exists_maximalSplitTorus G` gives the maximal split torus `j : S ⟶ G`.
2. `EnvelopeInfiniteReduction.exists_isMaximalTorus_factor` puts it inside a
   maximal `k`-torus `i : T ⟶ G`. Despite the module name
   (`Rational.TorusGeneratedEnvelopeAlgebraicClosureInfiniteReduction`), this
   theorem has no infinite-field hypothesis. It needs `Smooth` and
   `IsAffineHom` on `G` and a closed torus.
3. Over `K = SeparableClosure k`, `connectedReductiveFieldExtensionStatement`,
   `GaloisPinningData.isSplitTorus_separableClosure` and
   `maximalTorusBaseChange` provide the hypotheses of `rootDatumExistence`.
   It gives a reduced root datum `P` on the lattices of `T_K`.
4. The cocharacter `c₀` of `S` comes from `IsSplitTorus.exists_pairings_ne_zero`.
   It avoids a finite set: the relative roots of `j` and also every nonzero
   restriction of an absolute root. Avoiding the second part is what makes
   the `compatible` field provable.
5. `TitsIndexExistence.latticePairing_restriction` shows that the pairing of
   a restricted root with `c₀` equals the pairing over `K` of the root with
   the pushed-forward cocharacter `cK`.
6. `RootDatumCoweightFace.exists_regular_refinement` refines `cK` to a
   regular cocharacter with the same nonzero signs.
   `IsRootDatumOf.regularCocharacterBase` turns it into a base, and
   `RootPinning.ofSplitMaximalTorus` gives the pinning.

A Galois pinning alone does not give compatibility: a base chosen without
reference to `c₀` need not agree with its signs. Step 4 is the essential
choice.

## The local rank-one classification

Task 5621 required the proof to be independent of
`LocalRankOneClassificationStatement` and of every local Kneser–Tits
statement or result whose planned proof consumes them. The review of artifact
`8918509e-3ce9-4f74-a7d2-cf80732f00ac` records a recursive import audit: no
module the proof imports refers to Kneser–Tits, `LocalRankOneClassification`
or `LocalRankOneTitsIndex`. The review of the anisotropic-kernel proof
records a similar audit of its imports.

The opposite direction is in the Library. The theorem
`localRankOneClassification_of_indexStatements` (module
`SimplyConnected.LocalRankOneClassificationIndexReduction`) derives
`LocalRankOneClassificationStatement` from seven explicit hypotheses. The
first is `hexist : TitsIndexExistenceStatement.{u}`, and `titsIndexExistence`
can now be passed for it. The six remaining inputs are
`LocalRankOneTitsIndexStatement` (task
`c6b28e3e-647d-4a94-8988-75408718fdd4`), `InnerTypeANormOneStatement`,
`CentralSimpleUnits.MatrixNormOneSplitRankStatement`,
`OuterTypeARankOneHermitianStatement`, `TypeCRankOneQuaternionicStatement`
and `TypeDRankOneSpinStatement`. No published theorem yet removes the first
conjunct from the bundled `LocalRankOneClassificationIndexInputs`. The proof
task of the classification itself is Task 5442
(`56866550-3ce3-4065-86ef-babcf0251a5e`); see
[Local Kneser–Tits: published reductions and open inputs](local-kneser-tits-route.md).

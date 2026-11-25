# Renard VI.4.1–VI.4.5: the supercuspidal block and its center

This focused map, dated 7 November 2026, supplements the
[whole-book ledger](coverage.md) and the
[supercuspidal induction and finite-length map](supercuspidal-finite-length-progress.md).
It records twelve statements published for VI.4, the published proofs of
three of them and the published conditional reductions. None of the twelve
statement modules proves a proposition. At Library `eec7519b`, the other nine
statements had no proof; the Library now proves eight of the twelve (see
[Status in the Library](#status-in-the-library)). The map is not a complete inventory of VI.4,
and supplies no new Lean proof.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF page numbers are one-based and equal printed page numbers plus six.
The source passages and the paired Lean and Markdown files were read for the
claims below. By SHA256, all twenty-four primary files equal their first published
versions and the files at Library
`eec7519b852f9097606377425625fd5794c87f71`. A Lean check at that
Library of fifty modules, including these twelve, had zero diagnostics.

## Statements in the Library

Each statement below was checked by a Lake build and for declaration kind. A
statement does not prove its proposition. All declarations are in namespace
`Langlands.CuspidalSupport` under `Langlands/Representation/CuspidalSupport/`.

| Pair and exact declaration | First appeared at Library commit |
| --- | --- |
| [RationalSummandSmallProgeneratorStatement](../../Langlands/Representation/CuspidalSupport/RationalSummandSmallProgeneratorStatement.md) | `6f182f920309bbe9e9e43bd7181d7e25d5c02acd` |
| [RationalSummandHomEquivalenceStatement](../../Langlands/Representation/CuspidalSupport/RationalSummandHomEquivalenceStatement.md) | `6f182f920309bbe9e9e43bd7181d7e25d5c02acd` |
| [RationalNormKernelHeckeStatement](../../Langlands/Representation/CuspidalSupport/RationalNormKernelHeckeStatement.md) | `6f182f920309bbe9e9e43bd7181d7e25d5c02acd` |
| [RationalNormKernelEndSeparationStatement](../../Langlands/Representation/CuspidalSupport/RationalNormKernelEndSeparationStatement.md) | `6f182f920309bbe9e9e43bd7181d7e25d5c02acd` |
| [RationalNormKernelEndDomainStatement](../../Langlands/Representation/CuspidalSupport/RationalNormKernelEndDomainStatement.md) | `6f182f920309bbe9e9e43bd7181d7e25d5c02acd` |
| [RationalSummandEndCommutativeStatement](../../Langlands/Representation/CuspidalSupport/RationalSummandEndCommutativeStatement.md) | `6f182f920309bbe9e9e43bd7181d7e25d5c02acd` |
| [RationalSummandEndCenterStatement](../../Langlands/Representation/CuspidalSupport/RationalSummandEndCenterStatement.md) | `6f182f920309bbe9e9e43bd7181d7e25d5c02acd` |
| [RationalSummandEndNoetherianStatement](../../Langlands/Representation/CuspidalSupport/RationalSummandEndNoetherianStatement.md) | `6f182f920309bbe9e9e43bd7181d7e25d5c02acd` |
| [RationalSummandCenterGroupAlgebraStatement](../../Langlands/Representation/CuspidalSupport/RationalSummandCenterGroupAlgebraStatement.md) | `6f75b7b37e52f82517ed4cc6d73e4d3511317934` |
| [RationalSummandBlockCenterStatement](../../Langlands/Representation/CuspidalSupport/RationalSummandBlockCenterStatement.md) | `6813e35ad82cbbdded7064b624e6041b61e40b74` |
| [RationalInertiaBlockIndecomposableStatement](../../Langlands/Representation/CuspidalSupport/RationalInertiaBlockIndecomposableStatement.md) | `6813e35ad82cbbdded7064b624e6041b61e40b74` |
| [RationalInertiaBlockCenterEvaluationStatement](../../Langlands/Representation/CuspidalSupport/RationalInertiaBlockCenterEvaluationStatement.md) | `6813e35ad82cbbdded7064b624e6041b61e40b74` |

## Common setting

Every statement quantifies over an arbitrary nonarchimedean local field `F`
of any characteristic and an actual connected reductive group scheme `G`
over `Spec F`. Write `H = G(F)`, with its canonical rational-point
topology, and `H⁰ = Plancherel.rationalCommonNormKernel G`, the common
kernel of the norms of all rational characters. This is Renard's `⁰G`,
with the subspace topology.

- **Π.** Renard's `Π = ind_{⁰G}^G ρ` is the published
  `Induction.compactInductionFunctor (rationalCommonNormKernel G)` applied
  to `SmoothRep.toRep.obj ρ`. In the VI.4.1 module it is named
  `rationalNormKernelSummandInduction G ρ`.
- **The block.** Renard's `M(G)[π]` is the published full category
  `RationalInertiaBlock G (rationalInertiaBaseLift G π)`. Its objects are
  the actual smooth representations whose irreducible actual subquotients
  are all isomorphic to actual unramified twists of the universe lift of
  `π`. `π` and `ρ` have carriers in `Type uV`, and `Π` and the block are
  formed at carrier universe `max uF uV`.
- **Premises with `π`.** The statements with a representation `π` take a
  maximal split torus inclusion and a generic cocharacter, explicit
  `StandardCocharacterStatement`, relative-root-system and
  standard-unipotent-closedness premises, and local compactness, the
  nonarchimedean group property and Hausdorffness of `H`. `π` is
  irreducible and cuspidal in the sense of the published
  `Aubert.General.IsCuspidal`: every proper standard normalized Jacquet
  module vanishes. The
  `isCuspidal_of_all_represented_parabolics_of_standardCocharacter`
  (module `Langlands.Representation.Aubert.General.RepresentedStandardCuspidality`)
  derives this exact `IsCuspidal` from vanishing along all proper
  represented actual parabolics. It keeps `StandardCocharacterStatement`,
  the relative-root-system realization and closedness of the standard
  unipotent subgroups as premises. The converse comparison is a separate
  obligation.
- **Choice of ρ.** Renard's `ρ` is one irreducible summand of `Res π`
  (VI.3.2). The statements with `π` take every irreducible `ρ` with an
  injective `H⁰`-equivariant map into `Res π`. By VI.3.2 these are the
  summands up to isomorphism; this comparison is not used or asserted.
- **R and A.** The VI.4.3 and VI.4.4 statements and
  `RationalSummandBlockCenterStatement` are made for `R = End I` with
  `I = Π`, where Renard uses the convolution algebra `A = H(G, ρ)` or
  `H(N, ρ)`. The isomorphism `R ≅ A` is the separate VI.4.2 statement, and
  no statement uses it as a premise.

## VI.4.1: the progenerator and the equivalence

Source: VI.4.1, Proposition, printed p.149 / PDF p.155; (VI.4.1.3),
(VI.4.1.4) and Theorem, printed pp.150–151 / PDF pp.156–157; A.VIII.2,
printed pp.266–267 / PDF pp.272–273.

- `RationalSummandSmallProgeneratorStatement` (Proposition): `Π` satisfies
  `IsRationalInertiaSmallProgenerator`: it lies in the block, lifts along
  epimorphisms of the block, has a faithful integer Hom functor, the block
  has coproducts indexed by `Type (max uF uV)`, and the Hom functor
  preserves them. The predicate is the
  `IsRationalNormKernelSmallProgenerator` with `Π₁` replaced by an
  arbitrary object.
- `RationalSummandHomEquivalenceStatement` (Theorem): `Π` lies in the block,
  and `preadditiveCoyonedaObj` of the resulting object, from the block to
  right modules over `R`, is an equivalence. The identification of the
  quasi-inverse with `M ↦ M ⊗_R V_Π` (VI.4.1.4) is not stated. The block is
  neither assumed nor asserted to be abelian.

The alternative progenerator `Π₁ = ind_{⁰G}^G(Res π)` of the Remark after
the Proposition is the subject of the
`RationalUniversalSmallProgeneratorStatement` (not proved) and
`RationalUniversalProgeneratorComparisonStatement`, the isomorphism of
`Π₁` with the unramified group-algebra tensor. The
`rationalUniversalProgeneratorComparison` proves the comparison. Their entries in the Library are listed in the
[algebraic-families map](algebraic-families-progress.md) and the
prerequisite table of the
[uniform-compression map](uniform-compression-progress.md).

## VI.4.2 and VI.4.3: the convolution algebra

Source: (VI.4.1.2), printed p.149 / PDF p.155; (VI.4.2.1) and the
Proposition of VI.4.2 with its proof, printed pp.151–153 / PDF pp.157–159;
VI.4.3, Lemma and Corollary, printed pp.154–155 / PDF pp.160–161.

- `RationalNormKernelHeckeStatement` (VI.4.2, Proposition, derived): for
  every irreducible smooth `ρ` of `H⁰`, there is a `ℂ`-linear equivalence
  from `End I` onto `rationalNormKernelHecke G ρ` (Renard's `H(G, ρ)` as a
  vector space) given by `α ↦ (g ↦ (w ↦ α(f_w)(g)))`, with Renard's inverse
  formula, carrying composition to `rationalNormKernelConvolution`. No ring
  structure is put on `H(G, ρ)`. The convolution uses the representatives
  of `Quotient.out`; independence of this choice is not asserted. The right
  module structures of VI.4.2 are not formalized.
- `RationalNormKernelEndSeparationStatement` (VI.4.3, Lemma, derived): for
  every irreducible smooth `ρ` of `H⁰`, an element of `End I` that acts as
  zero on every simple right `R`-module is zero. The structure of the
  spaces `F_x(ρ)` and the units (VI.4.3.3) are not stated.
- `RationalNormKernelEndDomainStatement` (VI.4.3, Corollary (i), derived):
  `IsDomain (End I)` for every irreducible smooth `ρ` of `H⁰`.
- `RationalSummandEndCommutativeStatement` (VI.4.3, Corollary (ii)):
  `End I` is commutative if and only if, for every irreducible smooth `σ`
  of `H⁰`, the space of `H⁰`-maps `σ → Res π` has rank at most one.

The first three statements generalize Renard's `ρ`, a summand of `Res π`
for an irreducible supercuspidal `π`, to every irreducible smooth `ρ` of
`H⁰`, with no torus, root or topological premise. Their provenance is
recorded as derived.

## VI.4.4: the center and noetherianity

Source: VI.4.4, Theorem, Lemma, Corollary and Proposition, printed
pp.155–159 / PDF pp.161–165.

Write `T` for the infimum, over the unramified characters `ω` with
`π ⊗ ω ≅ π`, of `ker ω`. This is Renard's `⋂_{ω ∈ X(G)(π)} ker ω`.

- `RationalSummandEndCenterStatement` (Theorem): an element of `End I` is
  central exactly when `α(f_w)` vanishes off `T` for every `w`; and for
  `m` the rank of the space of `H⁰`-maps `ρ → Res π`, a natural number,
  `End I` has a basis indexed by `Fin (m ^ 2)` over its center.
- `RationalSummandEndNoetherianStatement` (Corollary): `End I` is left and
  right noetherian. The concluding remark that `M(G)[π]` is equivalent to
  modules over a noetherian algebra is not stated.
- `RationalSummandCenterGroupAlgebraStatement` (Proposition, derived): a
  `ℂ`-algebra isomorphism from `ℂ[T/⁰G]` onto the center of `End I`, with
  the support of the image of the class of `t` in `⁰G t⁻¹`, and with that
  image acting by `ω(t)` on every `Hom_G(Π, π ⊗ ω)`. This action replaces
  Renard's normalization `ψ_g(g⁻¹) = ρ_T(g⁻¹)`.

The VI.4.4 Lemma, the representation `ρ_T`, finiteness of `X(G)(π)` and
finite index of `T` are not stated, nor is the identification of the
center with the functions on the variety `Irr(G)[π]`.

## VI.4.5: the center of the block

Source: VI.4.5, Proposition, Corollary and proof, printed pp.159–160 /
PDF pp.165–166; A.IX and A.X, printed pp.268–269 / PDF pp.274–275.

- `RationalSummandBlockCenterStatement`: `Π` lies in the block, and the
  component at `Π` is a ring isomorphism from the published `CatCenter` of
  the block onto the center of `End I`.
- `RationalInertiaBlockCenterEvaluationStatement` (Proposition, derived):
  a ring isomorphism from `ℂ[T/⁰G]` onto `CatCenter` of the block, with
  scalars acting as scalars and the class of `t` acting by `ω(t)` on every
  unramified twist of `π` that lies in the block. The algebra of functions
  on `Irr(G)[π]` is replaced by `ℂ[T/⁰G]`, through the Remark of VI.4.4.
- `RationalInertiaBlockIndecomposableStatement` (Corollary): in every
  decomposition of the block into two full subcategories in the sense of
  A.IX (`Renard.IsCategoryDecomposition`), one factor has only zero
  objects.

## Status in the Library

| Statement | In the Library |
| --- | --- |
| `RationalNormKernelHeckeStatement` | proved, `rationalNormKernelHecke_equiv` (`RationalNormKernelHeckeProof.lean`) |
| `RationalNormKernelEndSeparationStatement` | proved, `rationalNormKernelEnd_separation` (`RationalNormKernelEndSeparationProof.lean`) |
| `RationalNormKernelEndDomainStatement` | proved, `rationalNormKernelEnd_isDomain` (`RationalNormKernelEndDomainProof.lean`) |
| `RationalSummandEndCommutativeStatement` | proved, `rationalSummandEnd_commutative` (`RationalSummandEndCommutativeProof.lean`) |
| `RationalSummandEndCenterStatement` | proved, `rationalSummandEndCenter` (`RationalSummandEndCenterProof.lean`) |
| `RationalSummandEndNoetherianStatement` | proved, `rationalSummandEndNoetherian` (`RationalSummandEndNoetherianProof.lean`) |
| `RationalSummandCenterGroupAlgebraStatement` | proved, `rationalSummandCenterGroupAlgebra` (`RationalSummandCenterGroupAlgebraProof.lean`) |
| `RationalInertiaBlockIndecomposableStatement` | proved, `rationalInertiaBlockIndecomposable` (`RationalInertiaBlockIndecomposableProof.lean`) |
| `RationalSummandSmallProgeneratorStatement` | conditional reductions only (below) |
| `RationalSummandHomEquivalenceStatement` | conditional reductions only (below) |
| `RationalSummandBlockCenterStatement` | conditional reduction only, `rationalSummandBlockCenter_of_homEquivalence` (`RationalBlockCenterReduction.lean`) |
| `RationalInertiaBlockCenterEvaluationStatement` | conditional reduction only, `rationalInertiaBlockCenterEvaluation_of_inputs` (`RationalInertiaBlockCenterEvaluationReduction.lean`) |

All files are in `Langlands/Representation/CuspidalSupport/`. The related
`RationalUniversalSmallProgeneratorStatement` also has only a conditional
reduction (`rationalUniversalSmallProgenerator_of_specialVertexInputs_of_restriction`).

## Published proofs

Three of the statements had published proofs at the date of this map. Each theorem
has the exact published statement as its type, with both universes
arbitrary. All three proofs are in namespace `Langlands.CuspidalSupport`.

| Statement | Theorem and proof module | First appeared at Library commit |
| --- | --- | --- |
| `RationalNormKernelHeckeStatement` (VI.4.2) | `rationalNormKernelHecke_equiv`, `RationalNormKernelHeckeProof` | `d82893a7de0b168873a15c6c7b0a731deb27aa23` |
| `RationalNormKernelEndDomainStatement` (VI.4.3, Corollary (i)) | `rationalNormKernelEnd_isDomain`, `RationalNormKernelEndDomainProof` | `d82893a7de0b168873a15c6c7b0a731deb27aa23` |
| `RationalNormKernelEndSeparationStatement` (VI.4.3, Lemma) | `rationalNormKernelEnd_separation`, `RationalNormKernelEndSeparationProof` | `93c6a3c332d9b4c0bdda5f4026a5865fb43cfa08` |

The three proofs were checked by a Lake build. They specialize the
supporting modules `NormalSubgroupHecke`, `NormalSubgroupHeckeDomain` and
`NormalSubgroupHeckeSeparation`. Those modules are written for an arbitrary
topological group, an open normal subgroup `H` and an irreducible smooth
representation `ρ` of `H`. The separation theorem also assumes that `G/H` is
countable with unique products and that `ρ` has countable dimension. The
proofs then take `H = H⁰`, with the published openness and normality of the
norm kernel.

- The VI.4.2 proof follows Renard's computation through the decomposition
  (VI.4.2.2), which uses only that `H⁰` is open and normal.
- The domain proof does not follow Renard's route through the Lemma of VI.4.3
  and the twisted Laurent structure over `⁰G\N`. It proves that
  `G(F)/⁰G` has unique products, by embedding it through the valuations of
  the rational characters into `ℤ`-valued functions. For nonzero `φ` and
  `ψ`, a unique product of their coset supports then isolates a single
  nonzero term of the convolution.
- The Lemma proof keeps Renard's use of B.III (`Langlands.Renard.unitalSeparation`,
  applied to `(End I)ᵐᵒᵖ`), which makes a kernel element nilpotent. It
  replaces Renard's argument through the units (VI.4.3.3) by the domain
  property, Corollary (i). B.III needs countable dimension of `End I`. The
  proof obtains it from second countability of `G(F)`, which makes `G(F)/⁰G`
  countable and bounds the dimension of `ρ` by the published
  `Whittaker.MirabolicRigidity.rank_le_aleph0`, and from the VI.4.2
  embedding of `End I` into finitely supported functions on `G(F)/⁰G`.

None of the three proofs assumes admissibility or finite dimensionality of
`ρ`, nor a supercuspidal `π`. At the date of this map no proof of
the other nine statements had been found (for the present status see
[Status in the Library](#status-in-the-library)). The supporting module
`NormalHeckeGrading` grades `End(ind_H^G ρ)` by a degree
on `G` with kernel `H`, toward the VI.4.4 proofs, using
the abstract module `Langlands.Algebra.RankOneGradedAlgebra`. It proves none
of the twelve statements.

## Published conditional reductions

Two modules for VI.4.1 give conditional reductions. Their theorems are
proved and keep the listed premises as hypotheses.

| Theorem and module | Premises | Conclusion |
| --- | --- | --- |
| `rationalSummandSmallProgenerator_of_specialVertexInputs`, `RationalSummandSmallProgeneratorReduction` | `RationalSpecialVertexCompactInputsStatement`, `RationalNormKernelFiniteRestrictionStatement` (VI.3.2 (ii)), `RationalNormKernelTwistEquivalenceStatement` (VI.3.2 (iii)) | `RationalSummandSmallProgeneratorStatement` |
| `rationalSummandSmallProgenerator_of_jointBasis`, same module | `JointSpecialCompactBasisExistenceStatement` and the two VI.3.2 premises | `RationalSummandSmallProgeneratorStatement` |
| `rationalSummandHomEquivalence_of_jointBasis`, same module | the premises of the previous row | `RationalSummandHomEquivalenceStatement` |
| `rationalSummandHomEquivalence_of_smallProgenerator`, `RationalSummandHomEquivalenceReduction` | `RationalSummandSmallProgeneratorStatement` | `RationalSummandHomEquivalenceStatement` |

At Library `eec7519b`, a search for theorems whose type is one of the named
premise statements found only conditional reductions, so none of these
premises is proved. The module `RationalSummandHomEquivalenceReduction` also
proves, without premises, `rationalSummandBlock_abelian`: the inertia block
has an abelian structure whose additive structure is the full-subcategory
one.

## Remaining obligations

1. Proofs of the four statements the Library does not prove (see
   [Status in the Library](#status-in-the-library)), and of the premises of
   the reductions above.
2. Statements of the VI.4.1.4 quasi-inverse, the right module structures
   of VI.4.2, the structure of `F_x(ρ)` and (VI.4.3.3), the VI.4.4 Lemma,
   finiteness of `X(G)(π)` and of the index of `T`, the variety
   `Irr(G)[π]` and its algebra of functions, and the comparison from
   standard to all-parabolic cuspidality.

General reductive scope and positive-characteristic local fields remain
unchanged.

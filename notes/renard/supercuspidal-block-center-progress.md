# Renard VI.4.1–VI.4.5: the supercuspidal block and its center

Worker 6, 7 November 2026. This focused map supplements the
[whole-book ledger](coverage.md) and the
[supercuspidal induction and finite-length map](supercuspidal-finite-length-progress.md).
It records twelve verified statement publications by Worker 6 for VI.4,
the proof tasks for them, the published proofs of three of them by Worker
1789 and the published conditional reductions by other workers. None of the
twelve publications proves a proposition. At Library `eec7519b`, the other
nine statements have no proof. The map is not a complete inventory of VI.4,
and supplies no new Lean proof.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF page numbers are one-based and equal printed page numbers plus six.
The source passages and the paired Lean and Markdown files were read for the
claims below. By SHA256, all twenty-four primary files equal their frozen
accepted files, Worker 6's workspace files and the files at Library
`eec7519b852f9097606377425625fd5794c87f71`. A fresh Lean check at that
Library of fifty modules, including these twelve (check
`6459f600-a711-4494-a5dc-27d2639384bc`), had zero diagnostics.

## Verified publications

Each receipt below has `accepted = true`, `public = true`, an accepted
`lean.statement@1` machine validation, an independent semantic approval with
no review qualification and a published integration. A statement receipt
does not prove its proposition. All declarations are in namespace
`Langlands.CuspidalSupport` under `Langlands/Representation/CuspidalSupport/`.

| Pair and exact declaration | Candidate, independent review and publication |
| --- | --- |
| [RationalSummandSmallProgeneratorStatement](../../Langlands/Representation/CuspidalSupport/RationalSummandSmallProgeneratorStatement.md) | Statement `b7460a21-0d96-40d1-ac54-0280318b052d`; Reviewer 16438, review `5212f319-f534-4f94-9e84-6d691d45f785`; machine `44311bfa-0dc9-4dd1-8039-45bab42dbb3e`; integration `1b8da722e53a445f9b1731ffe3b11bf7`, commit `6f182f920309bbe9e9e43bd7181d7e25d5c02acd`. |
| [RationalSummandHomEquivalenceStatement](../../Langlands/Representation/CuspidalSupport/RationalSummandHomEquivalenceStatement.md) | Statement `1ff070b2-41a0-4bed-a8f4-a5d45ec83cef`; Reviewer 16439, review `1ddad616-88ba-400b-977a-f5b9c24ad613`; machine `d473fb32-9018-4e56-a2f0-257c30174164`; integration `b7b38daf53aa438395b7716f63d115e0`, commit `6f182f920309bbe9e9e43bd7181d7e25d5c02acd`. |
| [RationalNormKernelHeckeStatement](../../Langlands/Representation/CuspidalSupport/RationalNormKernelHeckeStatement.md) | Statement `d02b789d-c795-4894-a239-5fa9c9a5332b`; Reviewer 16444, review `3a1f6432-9966-487c-8cac-49908ce798a2`; machine `94d5c26a-e289-48d6-9e47-66be341a3e81`; integration `18158e0343ef4769959ad9142722bcec`, commit `6f182f920309bbe9e9e43bd7181d7e25d5c02acd`. |
| [RationalNormKernelEndSeparationStatement](../../Langlands/Representation/CuspidalSupport/RationalNormKernelEndSeparationStatement.md) | Statement `bdd4f35e-f82b-403c-b91e-4b53087e2e70`; Reviewer 16446, review `8c8eddc3-d546-4e9f-8d09-3dfd9372d8c0`; machine `0aed16f6-7512-44b5-935b-92b9b9913d0b`; integration `10fef6ecf9f94b29a172cf42e6caef93`, commit `6f182f920309bbe9e9e43bd7181d7e25d5c02acd`. |
| [RationalNormKernelEndDomainStatement](../../Langlands/Representation/CuspidalSupport/RationalNormKernelEndDomainStatement.md) | Statement `4ac10ae2-0fd2-498a-9b23-7c36d464eadf`; Reviewer 16447, review `9c064310-fc70-4de0-b00d-4365915d16ea`; machine `734faad6-3c37-4650-9cd6-d9abdf2713dc`; integration `281de72ffbf64641a7d98d05a72e8312`, commit `6f182f920309bbe9e9e43bd7181d7e25d5c02acd`. |
| [RationalSummandEndCommutativeStatement](../../Langlands/Representation/CuspidalSupport/RationalSummandEndCommutativeStatement.md) | Statement `4f8cbd12-5159-4485-bf7d-b0904413515b`; Reviewer 16448, review `3d0d0f20-8530-4cc6-a5dd-c3507fcdd1c5`; machine `b34b20b8-9486-41f4-9313-58c00f8bef27`; integration `1db9d835dcd84e398adce6763c9a5d3c`, commit `6f182f920309bbe9e9e43bd7181d7e25d5c02acd`. |
| [RationalSummandEndCenterStatement](../../Langlands/Representation/CuspidalSupport/RationalSummandEndCenterStatement.md) | Statement `beb8c173-4491-47d8-9714-4f41130a4043`; Reviewer 16452, review `64a201e0-d84a-424a-9550-13a138962129`; machine `d46afc66-00c2-47e8-8f4e-140726cf5651`; integration `76c83d21183d4c5b86d0e022ea46879b`, commit `6f182f920309bbe9e9e43bd7181d7e25d5c02acd`. |
| [RationalSummandEndNoetherianStatement](../../Langlands/Representation/CuspidalSupport/RationalSummandEndNoetherianStatement.md) | Statement `a6cb06b3-1154-4c29-837f-cca72bca147e`; Reviewer 16497, review `cac1a762-600e-4ef3-a2a9-76b345ef3b5f`; machine `11462a10-848b-46f0-8102-59aa82115fc7`; integration `72bc6f080075476eb37442408e883275`, commit `6f182f920309bbe9e9e43bd7181d7e25d5c02acd`. |
| [RationalSummandCenterGroupAlgebraStatement](../../Langlands/Representation/CuspidalSupport/RationalSummandCenterGroupAlgebraStatement.md) | Statement `7f4e9425-8096-4b60-86e9-434f2f7ca2a0`; Reviewer 16528, review `83187ad0-c1c8-412b-9624-e8295ab36b8c`; machine `c87264aa-2779-45cb-9839-4919aca6b1e5`; integration `79548ab4256d4bdfb2baa75c52b7b7f4`, commit `6f75b7b37e52f82517ed4cc6d73e4d3511317934`. |
| [RationalSummandBlockCenterStatement](../../Langlands/Representation/CuspidalSupport/RationalSummandBlockCenterStatement.md) | Statement `59881e52-be22-4a0e-bc4e-46242ad7a9dc`; Reviewer 16621, review `ea7f8efc-f5fd-4181-b8c6-118b7c9a5c0b`; machine `b4e2db8e-e07c-4505-b401-1512c7f13e05`; integration `c5a1c0e2932348f1a8575da0f7f2e5c1`, commit `6813e35ad82cbbdded7064b624e6041b61e40b74`. |
| [RationalInertiaBlockIndecomposableStatement](../../Langlands/Representation/CuspidalSupport/RationalInertiaBlockIndecomposableStatement.md) | Statement `5582e3d7-daa9-4f80-a5a4-5c4b0a552c82`; Reviewer 16639, review `fcc82d65-77df-4f8d-b2d3-3c70ada02c12`; machine `cab52c00-2103-424f-a466-5f191d343af7`; integration `0dd7436100da436db8c3e4bd4962efc2`, commit `6813e35ad82cbbdded7064b624e6041b61e40b74`. |
| [RationalInertiaBlockCenterEvaluationStatement](../../Langlands/Representation/CuspidalSupport/RationalInertiaBlockCenterEvaluationStatement.md) | Statement `4f025e34-0609-4756-95c4-0d2246eb7d1a`; Reviewer 16695, review `a30f2cbc-454e-4c61-8fde-2f7c00975f7b`; machine `32bb591c-a52a-49e3-8181-7e48d1c3d271`; integration `808ee191e3a844638985029fd734ab1a`, commit `6813e35ad82cbbdded7064b624e6041b61e40b74`. |

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
  module vanishes. Worker 1276's
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
  preserves them. The predicate is Worker 1758's
  `IsRationalNormKernelSmallProgenerator` with `Π₁` replaced by an
  arbitrary object.
- `RationalSummandHomEquivalenceStatement` (Theorem): `Π` lies in the block,
  and `preadditiveCoyonedaObj` of the resulting object, from the block to
  right modules over `R`, is an equivalence. The identification of the
  quasi-inverse with `M ↦ M ⊗_R V_Π` (VI.4.1.4) is not stated. The block is
  neither assumed nor asserted to be abelian.

The alternative progenerator `Π₁ = ind_{⁰G}^G(Res π)` of the Remark after
the Proposition is the subject of Worker 1758's
`RationalUniversalSmallProgeneratorStatement` (not proved) and
`RationalUniversalProgeneratorComparisonStatement`, the isomorphism of
`Π₁` with the unramified group-algebra tensor. Worker 1595's
`rationalUniversalProgeneratorComparison` proves the comparison. The
receipts are in the
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

## Proof tasks

| Targets | Proof task |
| --- | --- |
| The two VI.4.1 statements | `ca5fea74-6ce4-457c-9947-4427cbfdbdd8` |
| The four VI.4.2 and VI.4.3 statements | `d1dd711e-784b-4280-aca6-84ebe3265618` |
| The three VI.4.4 statements | `3014a47e-e58f-44f8-94da-6e973d17a1f2` |
| The three VI.4.5 statements | `6b7a3e50-1d26-42c0-8246-ae6d1514d6e8` |

Worker 6 published these tasks. Related tasks of other workers: the
statement task `3e43c59a-2f05-433e-a739-54f50fcea0d3` of the VI.4.1
norm-kernel model and progenerator comparison; the proof tasks
`0bb65e53-06b7-4274-92ba-fee1666298eb` of the comparison and
`0ba788d6-b9d9-4a76-a017-972f8cad288f` of
`RationalUniversalSmallProgeneratorStatement`; and the VI.3.2 proof tasks
`04bc1186-999e-4a8b-8ee9-896710865f63` (i),
`5c063810-e264-4d0d-95b4-0da35bdfedf5` (ii) and
`9e053e00-35e1-4121-972e-e1653dc830c3` (iii). A task identifier locates
work; it is not a proof receipt or an ownership change.

## Published proofs

Worker 1789 proved three of the statements on task `d1dd711e`. Each theorem
has the exact published statement as its type, with both universes
arbitrary. All three proofs are in namespace `Langlands.CuspidalSupport`.

| Statement | Theorem and proof module | Proof candidate, independent review and publication |
| --- | --- | --- |
| `RationalNormKernelHeckeStatement` (VI.4.2) | `rationalNormKernelHecke_equiv`, `RationalNormKernelHeckeProof` | `e176e28c-c97d-48d7-8e3e-46d2918f11a3`; Reviewer 17311, review `ab8746b6-73da-4e07-a001-d3e7ba469bbf`; integration `903ef7e42a3e45be95d45ff09e6427e2`, commit `d82893a7de0b168873a15c6c7b0a731deb27aa23`. |
| `RationalNormKernelEndDomainStatement` (VI.4.3, Corollary (i)) | `rationalNormKernelEnd_isDomain`, `RationalNormKernelEndDomainProof` | `a25b96df-c3fc-43cd-b2f2-128e4b704a46`; Reviewer 17346, review `48ed33a9-e6ec-4f23-9b83-7d5efb71cf02`; integration `dda86aecedff433a93a79413ce8da707`, commit `d82893a7de0b168873a15c6c7b0a731deb27aa23`. |
| `RationalNormKernelEndSeparationStatement` (VI.4.3, Lemma) | `rationalNormKernelEnd_separation`, `RationalNormKernelEndSeparationProof` | `f5226a42-bb3c-4e93-a019-04d4e5419b27`; Reviewer 17438, review `9797c6b7-1b2e-4976-8fde-553951744fcc`; integration `4b34dea8b1354fea8a91120c23382ecb`, commit `93c6a3c332d9b4c0bdda5f4026a5865fb43cfa08`. |

The three proof receipts have an accepted `lean.proof@1` lake-build
validation and no qualification. The proofs specialize Worker 1789's
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
`ρ`, nor a supercuspidal `π`. A search of the staged and published proof
records found no proof candidate for any of the other nine statements.
Worker 1826's supporting module `NormalHeckeGrading` (artifact
`56500ee3-da11-4196-a7c4-9f497b7634a2`) grades `End(ind_H^G ρ)` by a degree
on `G` with kernel `H`, toward the VI.4.4 proofs of task `3014a47e`, using
the abstract module `Langlands.Algebra.RankOneGradedAlgebra`. It proves none
of the twelve statements.

## Published conditional reductions

Worker 1637 published two modules for VI.4.1. Their theorems are proved
and keep the listed premises as hypotheses.

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

1. Proofs of the nine statements that are not proved, through the listed
   tasks, and of the premises of the reductions above.
2. Statements of the VI.4.1.4 quasi-inverse, the right module structures
   of VI.4.2, the structure of `F_x(ρ)` and (VI.4.3.3), the VI.4.4 Lemma,
   finiteness of `X(G)(π)` and of the index of `T`, the variety
   `Irr(G)[π]` and its algebra of functions, and the comparison from
   standard to all-parabolic cuspidality.

General reductive scope, positive-characteristic local fields, existing
owners and user run controls remain unchanged.

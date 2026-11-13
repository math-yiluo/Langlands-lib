# Tate modules, Weil pairings and PEL invariant-orbit levels: Library map

This note locates, in the Library at commit `8ff9abe9`, the Lean
declarations that build the Tate modules, Weil pairings and invariant-orbit
level structures of Harris–Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties* (2001), p.18 and Section III.1, pp.90–92
(`harris-taylor-2001-geometry-cohomology-simple-shimura`), with Kottwitz
(1992), Section 5, pp.390–391, as the prime-to-p reference. The last
section lists the general theorems that these declarations take as explicit
parameters, with their proof status at this commit. The list was obtained by
searching the explicit binders of `AbelianScheme/Tate/`, of the finite Weil
and Cartier modules of `AlgebraicGeometry/Picard/`, and of the cited
`AlgebraicGeometry/FiniteEtale/` and `Shimura/PEL/` modules. That section
also lists the main propositions about the given abelian scheme, including
the two that no published theorem supplies. Side conditions of individual
lemmas, such as coprimality, injectivity or continuity, are not listed. It is meant
for the consumer of the PEL moduli functor, which needs these declarations by
name. Each declaration's own Markdown file is the authority on its exact
hypotheses. Paths are relative to `Langlands/`.

## 1. Tate modules from torsion points

- `Langlands.GroupScheme.Tate` in `AbelianScheme/Tate/Integral.lean`.
  `levelGroup G T n` is the kernel of multiplication by `n` on the
  `T`-points of a commutative group scheme `G`, and `Level` is its additive
  form. `transition (h : n ∣ m)` is `x ↦ x^(m/n)`. `Index P` is the set of
  positive `n` satisfying `P n`, `Integral G T P` is the subgroup of coherent
  families, and `Full` (all `n`) and `Away p` (`n` coprime to `p`) are its two
  instances. `FullAt` and `AwayAt` evaluate these at a field-valued point.
- `Langlands.AbelianScheme.Tate` in `AbelianScheme/Tate/AbelianScheme.lean`
  specializes these to bundled abelian schemes, with `transition_self`,
  `transition_comp`, `map_id`, `map_comp` and `map_add`.
- Prime-adic modules: `GroupScheme.Tate.PrimeAdic.Integral` and
  `PrimeAdic.Rational` (`PrimeAdic.lean`, specialized in `AbelianPrimeAdic.lean`).
- Profinite topology when the levels are finite: `GroupScheme.Tate.profinite`,
  with `fullProfinite` and `awayProfinite` (`Topology.lean`).
- Finite étaleness of torsion when `n` is invertible:
  `AbelianScheme.TorsionFiniteEtaleStatement`, proved by
  `AbelianScheme.torsionFiniteEtale` (`AbelianScheme/TorsionFiniteEtale.lean`).
  Geometric ranks are proved by `geometricTorsionRank`,
  `geometricPrimeAdicRank` and `AbelianScheme.Tate.geometricAdelicRank`
  (`GeometricTorsionRankProof.lean`, `GeometricPrimeAdicRankProof.lean`,
  `GeometricAdelicRankProof.lean`).

## 2. Rational and adelic structure; functoriality

- `Rational.lean`: `RationalFull` and `RationalAway` are `ℚ ⊗[ℤ]` of the
  integral limits, as in Harris–Taylor p.18. It also defines
  `rationalHomMap` on rational homomorphisms, `rationalEndAction` and
  `algebraAction`.
- `Scalars.lean`: continuous actions of the profinite integers
  (`fullModule`, `awayModule`), built from the finite-level actions.
- Full finite adeles, `RationalScalars.lean`: `finiteAdeleAction` of
  `Global.FiniteAdeles ℚ` and `finiteAdeleAlgebraAction` of
  `D ⊗[ℚ] Global.FiniteAdeles ℚ`, with `finiteAdeleHomMap`. They take
  `h : Global.RationalProfiniteIntegerAdeleComparison`, proved by
  `Global.rationalProfiniteIntegerAdeleComparison`
  (`Global/RationalProfiniteIntegerComparisonProof.lean`). The same file's
  `rationalAwayScalarAction` acts by the rationalized away profinite
  integers; it is not a prime-to finite-adele action.
- Prime-to-`m` finite adeles, `AwayRationalScalars.lean`:
  `primeToFiniteAdeleAction` of `Global.PrimeToFiniteAdeles m` and
  `primeToFiniteAdeleAlgebraAction` of `D ⊗[ℚ] Global.PrimeToFiniteAdeles m`,
  with `primeToFiniteAdeleHomMap`. They take, besides `h`,
  `hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m`, a
  comparison coupled to the witnesses chosen from `h`. Every instance is
  given by the proved
  `Global.primeToRationalProfiniteIntegerAdeleComparisons`
  (`Global/PrimeToRationalProfiniteIntegerComparisonProof.lean`).
- Restricted products of the `V_ℓ` relative to the `T_ℓ`
  (`RestrictedProduct.lean`): the comparison
  `RationalRestrictedProductComparisons` is proved by
  `GroupScheme.Tate.PrimeComparison.rationalRestrictedProductComparisons`
  (`RestrictedProductProof.lean`).

## 3. Geometric monodromy

- `Langlands.AlgebraicGeometry.FiniteEtale` (`AlgebraicGeometry/FiniteEtale/Definitions.lean`)
  defines the category of finite étale covers, the geometric fibre functor
  `fiberFunctor`, `FundamentalGroup` (its automorphism group) and its
  profinite topology (`fundamentalGroup_compact`, `fundamentalGroup_t2`,
  `fundamentalGroup_totallyDisconnected`,
  `fundamentalGroup_isTopologicalGroup`).
- The Galois-category theorem `geometricGaloisFiberFunctor`, path existence
  `geometricPathExists` and `geometricContinuousActionEquivalence` are proved
  in the same directory.
- Actions on torsion and Tate modules: `FiniteMonodromy.lean`
  (`finiteLevelMonodromy`), `IntegralMonodromy.lean` (`integralMonodromy`,
  `fullMonodromy`, `awayMonodromy`), and `GeometricMonodromy.lean`
  (namespace `AbelianScheme.Tate.Geometric`: `integralRepresentation`,
  `profiniteTateFunctor`, `profiniteTateMap_equivariant`).
  Pointed base change: `PointedMonodromyBaseChangeProof.lean`.

## 4. Weil pairings and the Tate twist

- Finite level, from Cartier duality of kernels
  (`AlgebraicGeometry/Picard`): `AbelianScheme.finiteWeilPairing`,
  `finiteWeilBilinearMap`, the pairing along a homomorphism
  `finiteWeilAlongHomPairing`, and Cartier perfectness `finiteWeilCartierIso`.
  The latter rests on `RelativeDualKernelCharacterBijectiveStatement`, proved
  by `relativeDualKernelCharacterBijective`. Transition, alternation and
  functoriality are proved by `relativeFiniteWeilTransition`,
  `relativeFiniteWeilAlternation` and `relativeFiniteWeilFunctoriality`.
- Tate twist: `Langlands.TateTwist` (`Twist.lean` and the `Twist*` modules) is
  the inverse limit of the roots-of-unity points, with its rational, adelic
  and prime-adic versions and its monodromy action.
- Limits: `integralWeilBilinearMap` and `awayWeilBilinearMap`
  (`WeilIntegral.lean`), `rationalWeilBilinearMap`, `adelicWeilBilinearMap`
  and `awayAdelicWeilBilinearMap` (`WeilRational.lean`), and the
  along-polarization forms (`WeilAlongHom.lean`, `WeilRationalAlongHom.lean`).
- Polarizations: rational alternation (`rationalPolarizationWeilAlternation`)
  and rational and adelic nondegeneracy
  (`AbelianScheme.rationalPolarizationWeilNondegeneracy`) are proved. No
  integral perfectness for nonprincipal polarizations is claimed.

## 5. PEL level structures as invariant orbits

- Similitude group: `Shimura.PEL.ScalarExtensionSimilitudes D V R ψ`
  (`Shimura/PEL/ScalarExtension.lean`) is the `D ⊗[ℚ] R`-linear similitude
  group of `ψ.baseChange R`. In `Shimura/PEL/ScalarExtensionTopology.lean`,
  `ScalarExtensionSimilitudePoints` gives it a topology, and
  `FiniteAdelicScalarExtensionLevel` and `PrimeToScalarExtensionLevel` are
  its compact open subgroups. `scalarExtensionRegularSimilitudesEquiv`
  (`Shimura/PEL/ScalarExtensionRegular.lean`) identifies it with the Harris
  regular-module similitude group.
- Frames: `AbelianScheme.Tate.WeilAdelicFrame` and `WeilPrimeToAdelicFrame`
  (`WeilFrame.lean`), with right actions `weilAdelicFrameRightAction`. The
  compatibility condition existentially quantifies a trivialization of the
  actual Tate twist. No trivialization is part of a frame.
- Monodromy-fixed orbit sets: `WeilAdelicLevel` and `WeilPrimeToAdelicLevel`
  (`WeilFrameMonodromy.lean`, `WeilPrimeToFrameMonodromy.lean`), packaged as
  `WeilAdelicCompactOpenLevel` and `WeilPrimeToAdelicCompactOpenLevel`
  (`WeilCompactOpenLevels.lean`). `HarrisWeilLevels.lean` specializes them to
  the Harris trace-form data.
- Geometric specialization: `GeometricWeilCompactOpenLevels.lean`
  (namespace `AbelianScheme.Tate.Geometric`) restates the towers, Hecke
  maps and canonical comparisons of Section 6 at geometric points with
  algebraically closed fields. It supplies the finite-fibre witness from the
  proved `geometricFiberFinite` (`AlgebraicGeometry/FiniteEtale/GeometricFiberFiniteProof.lean`)
  and the torsion and roots-of-unity finite-étale witnesses from
  `torsionFiniteEtale` and the finite étaleness of `mu S n`. Unit
  hypotheses on the selected orders and the duality, tensor and finite Weil
  transition inputs stay explicit.

## 6. Level change, Hecke maps, transport and base points

- Forgetting and translation: `weilAdelicLevelForget` and
  `weilAdelicLevelTranslate`, with composition laws, in
  `WeilAdelicLevelTransport.lean`. Compact-open towers and Hecke spans, in
  `WeilCompactOpenLevels.lean`: `weilAdelicCompactOpenLevelTower`,
  `weilAdelicCompactOpenHeckeLeft` and `weilAdelicCompactOpenHeckeRight`.
  The prime-to versions are parallel.
- Invertible rational homomorphisms: `weilAdelicLevelIsogeny`
  (`WeilLevelIsogeny.lean`), plus the `*Isogeny*Coherence` modules.
- Pointed base change: `WeilPathBaseChange.lean`,
  `WeilCompactOpenLevelPathBaseChange.lean` and `AdelicFrameBaseChange.lean`.
- Base points at a fixed level: path transport `weilAdelicLevelTransport`
  with `weilAdelicLevelTransport_path_independent`, `_refl`, `_trans`,
  `_symm`, `_translate` and `_forget` (`WeilAdelicLevelTransport.lean`). The
  prime-to analogue is `weilPrimeToAdelicLevelTransport`
  (`WeilPrimeToAdelicLevelTransport.lean`).
- Canonical base-point comparison of the actual Weil-compatible levels:
  `weilAdelicCompactOpenLevelGeometricTransport` and
  `weilPrimeToAdelicCompactOpenLevelGeometricTransport`
  (`WeilCompactOpenLevelTransport.lean`). They are natural isomorphisms
  between the compact-open level towers at two geometric points, for one
  abelian scheme with its fixed map to the dual and its algebra action.
  `_eq_path` shows that every path gives the same comparison, and `_refl`,
  `_trans` and `_symm` hold with no path in their statements. The
  hypotheses are those of the towers together with `[ConnectedSpace S]`,
  `[IsLocallyNoetherian S]`, algebraically closed fields at both points and
  the finite-fibre witnesses. A path is chosen from the proved
  `geometricPathExists` (`AlgebraicGeometry/FiniteEtale/GeometricPathProof.lean`). Pairing
  compatibility comes from the proved `rationalWeilGeometricTransport`
  (`WeilGeometricTransportProof.lean`). The geometric specialization of
  Section 5 has the same comparisons, with `_eq_path`, `_refl`, `_trans` and
  `_arrow`.
- Ambient frames, without the Weil condition:
  `adelicFrameOrbitCanonicalEquiv` and
  `primeToAdelicFrameOrbitCanonicalEquiv` (`CanonicalFrameOrbitTransport.lean`)
  compare the fixed orbit sets `AdelicFrameOrbit` (`AdelicFrameTransport.lean`)
  and its prime-to analogue of all tensor-algebra-linear frames. No
  polarization-pairing condition is imposed, so these are not comparisons
  of PEL levels. They take `GeometricPathExists`
  (`AlgebraicGeometry/FiniteEtale/GeometricPathStatement.lean`) as a parameter. For PEL levels
  use the declarations of the preceding item.

## Explicit parameters and their status

Three kinds of explicit inputs occur. General theorems taken as parameters
are proved, with two exceptions noted below. Propositions about the
particular abelian scheme or base form the second kind. Two of them, the
dual-scheme witness and its geometry, are instances of published general
statements that are unproved at this commit. The rest are data.

### General theorems taken as parameters

Each row is a published proposition quantified over all bases or schemes.
The proof is a closed theorem with no further hypotheses unless the row says
otherwise.

| Parameter type | Proof | File |
| --- | --- | --- |
| `pullbackTensorComparisonIsIsoStatement` | `pullbackTensorComparisonIsIso` | `AlgebraicGeometry/Modules/PullbackTensorProof.lean` |
| `PullbackTensorCompositionStatement`, `PullbackTensorSymmetryStatement` | `pullbackTensorComposition`, `pullbackTensorSymmetry` | `AlgebraicGeometry/Modules/PullbackTensorCompatibilityProofs.lean` |
| `PullbackTensorUnitCoherenceStatement` | `pullbackTensorUnitCoherence` | `AlgebraicGeometry/Modules/PullbackTensorUnitProofs.lean` |
| `ExplicitPullbackTensorAssociativityStatement` | `explicitPullbackTensorAssociativity` | `AlgebraicGeometry/Modules/ExplicitPullbackTensorAssociativityProofs.lean` |
| `TensorMonoidalLeftUnitorComparisonStatement` | `tensorMonoidalLeftUnitorComparison` | `AlgebraicGeometry/Modules/TensorMonoidalComparisonProofs.lean` |
| `PicardZeroPullbackStatement` | `picardZeroPullback` | `AlgebraicGeometry/Picard/PicardZeroPullbackProof.lean` |
| `PicardZeroUniversalBaseChangeStatement` | `picardZeroUniversalBaseChange` | `AlgebraicGeometry/Picard/PicardZeroUniversalBaseChangeProof.lean` |
| `MumfordBundlePicardZeroStatement` | `mumfordBundlePicardZero` | `AlgebraicGeometry/Picard/MumfordBundlePicardZeroProof.lean` |
| `DualAbelianBaseChangeStatement` | `dualAbelianBaseChange` | `AlgebraicGeometry/Picard/DualAbelianBaseChangeProof.lean` |
| `PolarizedFiniteFlatRankStatement` | `polarizedFiniteFlatRank` | `AlgebraicGeometry/Picard/PolarizedFiniteFlatRankProof.lean` |
| `FieldDualKernelCharacterBijectiveStatement` | `fieldDualKernelCharacterBijective` | `AlgebraicGeometry/Picard/FieldDualKernelCharacterBijectiveProof.lean` |
| `RelativeDualKernelCharacterBijectiveStatement` | `relativeDualKernelCharacterBijective` | `AlgebraicGeometry/Picard/RelativeDualKernelCharacterBijectiveProof.lean` |
| `RelativeFiniteWeilTransitionStatement` | `relativeFiniteWeilTransition` | `AlgebraicGeometry/Picard/FiniteWeilTransitionProof.lean` |
| `RelativeFiniteWeilAlternationStatement` | `relativeFiniteWeilAlternation` | `AlgebraicGeometry/Picard/FiniteWeilAlternationProof.lean` |
| `TorsionFiniteEtaleStatement` | `torsionFiniteEtale` | `AbelianScheme/TorsionFiniteEtale.lean` |
| `MultiplicationIsogenyStatement` | `GroupScheme.multiplicationIsogeny` | `AbelianScheme/MultiplicationIsogenyProof.lean` |
| `GroupScheme.FieldCubePullbackStatement`, `GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement`, `GroupScheme.FieldSymmetricMultiplicationPullbackStatement`, `GroupScheme.FieldSymmetricAmpleExistenceStatement` | `fieldCubePullback`, `algebraicallyClosedFieldAmpleExistence`, `fieldSymmetricMultiplicationPullback`, `fieldSymmetricAmpleExistence` | `AbelianScheme/` files of the same names with suffix `Proof` |
| `Global.RationalProfiniteIntegerAdeleComparison` | `Global.rationalProfiniteIntegerAdeleComparison` | `Global/RationalProfiniteIntegerComparisonProof.lean` |
| `Global.PrimeToRationalProfiniteIntegerAdeleComparison h m` | `Global.primeToRationalProfiniteIntegerAdeleComparisons h m` | `Global/PrimeToRationalProfiniteIntegerComparisonProof.lean` |
| `RationalWeilGeometricTransportStatement` | `rationalWeilGeometricTransport` | `AbelianScheme/Tate/WeilGeometricTransportProof.lean` |
| `RationalWeilFunctorialityStatement` | `rationalWeilFunctoriality` | `AbelianScheme/Tate/WeilRationalFunctorialityProof.lean` |
| `PrimeRationalPolarizationWeilNondegeneracyStatement` | `primeRationalPolarizationWeilNondegeneracy` | `AbelianScheme/Tate/WeilPrimeRationalPolarizationNondegeneracyProof.lean` |
| `FiniteEtaleCharacterSeparationStatement` | `finiteEtaleCharacterSeparation` | `AbelianScheme/Tate/WeilFiniteGeometricNondegeneracyFromField.lean` |
| `FieldRationalFaithfulnessStatement` | `fieldRationalFaithfulness` | `AbelianScheme/Tate/FieldRationalFaithfulnessProof.lean` |
| `FieldTwoPowerTorsionDensityStatement` | `fieldTwoPowerTorsionDensity` | `AbelianScheme/Tate/FieldTwoPowerTorsionDensityProof.lean` |
| `AbelianScheme.Tate.RationalMonodromyBaseChange` | third component of `pointedMonodromyBaseChange` | `AbelianScheme/Tate/PointedMonodromyBaseChangeProof.lean` |

The two exceptions are `FieldTorsionCardinalityStatement` and
`FieldTorsionRankStatement`, parameters of the reductions in
`GeometricTorsionReduction.lean`. Neither has a closed theorem. The published
`fieldTorsionCardinality_of_ample_and_cube` derives the first from proved
inputs, and `geometricTorsionRank` is proved along this route.
`FieldTwoPowerTorsionDetectionStatement` is unproved, and no declaration
above takes it.

### Propositions about the given abelian scheme, base and data

These are hypotheses about the particular `A`, `S`, geometric point or PEL
data. The caller must discharge them.

- `hA : HasDualScheme A` (`AlgebraicGeometry/Picard/DualScheme.lean`)
  asserts that a universal rigidified Picard-zero family exists. The dual
  scheme `dualScheme A hA` and the Poincaré family are chosen from it. Every
  Weil pairing of Sections 4–6 takes it. The general existence statement
  `RelativeDualSchemeExistenceStatement`
  (`AlgebraicGeometry/Picard/RelativeDualSchemeExistenceStatement.lean`) is
  published and **unproved** at this commit.
- `geometryA : DualSchemeGeometry A hA`
  (`AlgebraicGeometry/Picard/RelativeDualSchemeGeometryStatement.lean`)
  asserts that `dualScheme A hA` is smooth, proper and geometrically
  connected over `S`. It is needed only by the second of two layers:
  - *Intrinsic pairings, no geometry.* The finite pairings
    `finiteWeilPairing` and `finiteWeilBilinearMap`, Cartier perfectness
    `finiteWeilCartierIso`, the finite transition and functoriality results,
    and the limit pairings `integralWeilBilinearMap`, `awayWeilBilinearMap`,
    `rationalWeilBilinearMap`, `adelicWeilBilinearMap` and
    `awayAdelicWeilBilinearMap`, with their prime-adic and base-change forms
    (`WeilPrime.lean`, `WeilRationalPrime.lean`, `WeilBaseChange.lean`), pair
    `A` with the commutative group scheme `dualCommGroupSchemeFromEvaluation`.
    This group scheme is built from `hA`, the evaluation data below and the
    tensor and Picard statements of the table, without `geometryA`.
  - *Along a homomorphism to the dual, with geometry.* Together with the same
    inputs, `geometryA` builds the dual abelian scheme
    `dualAbelianSchemeFromEvaluation`, which `polarizationMap` targets. The
    constructions that use such a map all take `geometryA` as well:
    `finiteWeilAlongHomPairing` and the finite alternation and principal
    Cartier perfectness results, the along-homomorphism limit pairings
    (`WeilAlongHom.lean`, `WeilRationalAlongHom.lean`,
    `WeilRationalPrimeAlongHom.lean`), the polarization alternation and
    nondegeneracy results, `RationalWeilFunctorialityStatement` and
    `RationalWeilGeometricTransportStatement`, and all Weil frames, Weil levels,
    Hecke maps and Weil-level transports of Sections 5 and 6. The similitude
    groups and the ambient frame comparisons of
    `CanonicalFrameOrbitTransport.lean` and `AdelicFrameBaseChange.lean`
    take neither `hA` nor `geometryA`.

  The general statement `RelativeDualSchemeGeometryStatement` is
  **unproved** at this commit. The conditional theorem
  `RelativeDualSchemeGeometryStatement.of_flat_finitePresentation_proper`
  (`RelativeDualSchemeGeometryReduction.lean`) derives it from field
  geometry and from flatness, finite presentation and properness of the
  dual scheme. None of these four inputs has a closed proof at this commit.
  The representability boundary is described in
  [relative-picard-source-map.md](relative-picard-source-map.md).
- `DualSchemeMapAdditivity preservation stability A B hA hB` (isogeny and
  compact-open isogeny transport). Over a quasi-separated base, each
  instance follows from the proved `relativeDualSchemeMapAdditivity`
  (`AlgebraicGeometry/Picard/RelativeDualSchemeMapAdditivityProof.lean`).
- `GeometricPathExists s t hs ht` (`CanonicalFrameOrbitTransport.lean`). For connected, locally noetherian `S`,
  algebraically closed fields and the finite-fibre witnesses, it follows
  from the proved `geometricPathExists`.
- Invertibility of the selected torsion orders, as
  `hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤))`.
- Finite étaleness of the root-of-unity group schemes `mu S n` for selected
  `n`, as instance arguments. Given `0 < n` and invertibility of `n`, it
  follows from the proved `GroupScheme.muFiniteEtale`
  (`GroupScheme/MuFiniteEtaleProof.lean`).
- Finite-fibre witnesses `hs : ∀ Y : Cover S, Finite (Fiber s Y)`, and the
  instances `[QuasiSeparatedSpace S]`, and `[ConnectedSpace S]` and
  `[IsLocallyNoetherian S]` where monodromy or canonical comparison is used.
  At geometric points with algebraically closed fields, the proved
  `geometricFiberFinite` supplies `hs`; the geometric specialization of
  Section 5 uses it, together with the finite-étale witnesses above.
- Conditions on the PEL linear-algebra data where frames are compared with
  the source similitude group: `Shimura.PEL.RationalPELConditions σ ψ`
  (`Shimura/PEL/RationalInput.lean`, used in `WeilPELFrame.lean`) bundles
  finite dimensionality, faithfulness, alternation, nondegeneracy and
  compatibility of `ψ` with the involution.
- Polarization conditions, where a result needs them: for example
  `IsPolarization` in the polarization alternation and nondegeneracy
  results, and
  `IsRationalDualPullbackMultiple` in isogeny transport. The general
  frame and level interfaces impose no polarization predicate on
  `polarizationMap`.

### Data

- `MA`, a line bundle on the relative dual space, and `evaluationA`, an
  isomorphism from the tensor product of the Poincaré carrier with `MA` to
  the structure sheaf. Every construction accepts any such pair; this note
  records no canonical choice.
- The homomorphism `polarizationMap` from `A` to its dual abelian scheme,
  the rational algebra action `i : D →ₐ[ℚ] Rationalization.End A`, the
  `D`-module `V` with form `ψ`, the geometric point `s`, and the subgroups
  or levels `U` and `K`.

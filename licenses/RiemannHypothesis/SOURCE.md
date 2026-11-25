# Source note: the `riemann-hypothesis` repository

Parts of the Library contain text ported from a formalization published in November 2026 and
mirrored in the repository `leanprover-community/riemann-hypothesis`. This note names the source
and lists the Library files that contain text from it.

## The source

- The author's announcement: <https://alpo.ge/remark.pdf> (20 November 2026).
- Repository (a mirror of the published source): <https://github.com/leanprover-community/riemann-hypothesis>
- Commit the text was taken from: `f1f6d65`. The mirror's first commit, `40e56bab`, is the source as published.
- Lean `v4.33.1`; the Lean files are under `src/`.

What the repository's `README.md` says about the author and the origin of the text (quoted):

> A [Comparator](https://github.com/leanprover/comparator) setup and community build cache for
> the Lean formalization that claims a proof of the Riemann Hypothesis, and of GRH for Dirichlet
> L-functions, announced on 2026-11-20 at <https://alpo.ge/remark.pdf>.
>
> The first commit, `40e56bab`, is the submitted Lean source exactly as published.

and, under the heading "License":

> The submission belongs to its author and was published without a license. It is mirrored here
> for verification only: unmodified at commit `40e56bab`, and with the changes listed in the
> [notes](verification/NOTES.md#source) since.

The README does not name the author.

## Licence

The repository has no licence file. The text taken from it is used with attribution: this note
names the source, and the page of each Library file listed below names the source files and
lines it takes text from and what was changed.

## Library files containing text ported from the source

Each file's page (the `.md` beside it) has a section "Source and licence" that names the source
files and lines it takes from and what was changed.

Stone–von Neumann theorem (source
`src/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean`):

- `Langlands/Theta/Heisenberg/Basic.lean` (source lines 11–51, 543–554)
- `Langlands/Theta/Heisenberg/SelfDualSubgroup.lean` (lines 70–355)
- `Langlands/Theta/Heisenberg/SelfDual.lean` and `Langlands/Theta/Heisenberg/InducedModel.lean` (lines 357–541, 555–646, shared by the two files)
- `Langlands/Theta/Heisenberg/StoneVonNeumann.lean` (lines 652–678)
- `Langlands/HarmonicAnalysis/AdditiveCharacterExists.lean` (lines 684–715)

`Langlands/Theta/Heisenberg/Schrodinger.lean` contains no text of the source (its definitions are
new; its page names the source definitions they replace).

Real Weil representation; source files under
`src/Development/AbelianVarietyTheory/` and `src/Development/WeilBound/ThetaLifts/`:

- `Langlands/Theta/Real/Schrodinger.lean` (`PublishedTheorems/TwistedTraceFormula/RealMetaplecticRepresentation.lean`
  lines 1–119; `PublishedTheorems/TwistedTraceFormula/MetaplecticRepresentation.lean` lines 15–50;
  `Proofs/TwistedOperators/ExistsSchwartzTranslate.lean`; `Proofs/DivisorProofs/ContinuousRhoApply.lean`)
- `Langlands/Theta/Real/SchrodingerDeriv.lean` (`RealMetaplecticRepresentation.lean` lines 121–345)
- `Langlands/Theta/Real/WeylAlgebra.lean` (`Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean` lines 1–244)
- `Langlands/Theta/Real/Intertwiner.lean` (`IteratedLineDerivMemWeylAlg.lean` lines 246–292;
  `CartanFactorisation/EqOfInner.lean` lines 61–206)
- `Langlands/Analysis/OneParameterSubgroup.lean` (`EqOfInner.lean` lines 12–59)
- `Langlands/Theta/Real/BigCellOperator.lean` (`Reductions/IsoOfIntegral.lean`)
- `Langlands/Theta/Real/BigCellDerivative.lean` (`Reductions/HasDerivAtSchwartzToL2.lean`, `Reductions/NormExpSubLe.lean`)
- `Langlands/Theta/Real/LocalLift.lean` (`Reductions/MetaDef.lean`, `Reductions/LocalLift.lean`)
- `Langlands/Theta/Real/Metaplectic/Defs.lean` (`Reductions/MetaplecticDerivatives/ContinuousPair.lean` lines 1–125)
- `Langlands/Theta/Real/Metaplectic/Basic.lean` (`MetaplecticDerivatives/ContinuousTo.lean`)
- `Langlands/Theta/Real/Metaplectic/Unipotent.lean` (`MetaplecticDerivatives/MetaplecticUnipotentBlockSecondDiag.lean`)
- `Langlands/Theta/Real/Metaplectic/BigCell.lean` (`MetaplecticDerivatives/MapOfRealMul.lean`)
- `Langlands/Analysis/FDerivOfCurves.lean` (`MetaplecticDerivatives/HasFDerivAtOfCurves.lean` lines 10–57)
- `Langlands/Theta/Real/Metaplectic/Covering.lean` (`HasFDerivAtOfCurves.lean` lines 59–153;
  `MetaplecticDerivatives/MetaplecticGroupT2Space.lean`; `MetaplecticDerivatives/MpFOne.lean` lines 12–52)
- `Langlands/Theta/Real/Metaplectic/Smooth.lean` (`IteratedLineDerivMemWeylAlg.lean` lines 294–446;
  `EqOfInner.lean` lines 212–319; `MetaplecticDerivatives/HasFDerivAtOrb.lean`; `MpFOne.lean` lines 54–117;
  `Proofs/TwistedOperators/MemSymplecticLieAlgebraOfExpSmulMemSymplecticGro.lean`)

Real Weil representation, Gaussian normalization:

- `Langlands/LinearAlgebra/SiegelUpperHalfSpace.lean` (`Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean`
  lines 13–125, without the lemmas on `SiegelH`; `Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean`
  lines 14–115; `Proofs/DivisorProofs/SymplecticHolPartDetNeZeroAndIsSymm.lean`;
  `Proofs/DivisorProofs/IsSiegelUpperHalfSpaceNegMulInvSymplectic.lean`)
- `Langlands/Analysis/SiegelGaussianIntegral.lean` (`ExistsEqTransposeMulDiagonalMul.lean` lines 117–196;
  `Proofs/DivisorProofs/SiegelGaussianPairStandardGaussian.lean`)
- `Langlands/Theta/Real/Metaplectic/Gaussian.lean` (`Proofs/DivisorProofs/` files
  `MetaplecticGaussianNormalised`, `MetaplecticCoverWeilRepresentation`, `FderivEqMulVecOfSchrodingerAnnihilated`,
  `SchwartzEqGaussianOfFderivEqMulVec`, `OrthogonalSymplecticFixesSiegelPointI`, `VacuumMatrixCoefficientSq`,
  `ContinuousMetaplecticSchwartzActionProd`, `MetaplecticRepresentationHolds` lines 79–108;
  `PublishedTheorems/TwistedTraceFormula/MetaplecticRepresentation.lean` lines 87–88)


### The Dixmier–Malliavin block


Each file's page (the `.md` file beside it) has a section "Source and licence" naming the source
files and lines it takes text from and what was changed.

| Library file | Source files (under `src/`) |
|---|---|
| `Langlands/Analysis/DixmierMalliavin/ExponentialKernel.lean` | `GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean` |
| `Langlands/Analysis/DixmierMalliavin/KernelProduct.lean` | `GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean` |
| `Langlands/Analysis/DixmierMalliavin/KernelBounds.lean` | `GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean` |
| `Langlands/Analysis/DixmierMalliavin/SmoothWeakLimit.lean` | `GroundTheory/AutomorphicForms/DixmierMalliavinLineLimit.lean` |
| `Langlands/Analysis/DixmierMalliavin/Line.lean` | `GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean` |
| `Langlands/Geometry/Manifold/LinearLieGroup/Exponential.lean` | `GroundTheory/AutomorphicForms/RealGroupsLie.lean` |
| `Langlands/Geometry/Manifold/LinearLieGroup/Basic.lean` | `GroundTheory/AutomorphicForms/RealGroupsLie.lean`, `DixmierMalliavinBasic.lean`, `GKModules/SmoothVectors.lean`, `DixmierMalliavinHaarCoord.lean`, `GKModules/Garding.lean`, `HarishChandraInvariance/Compact.lean` (all in `GroundTheory/AutomorphicForms/`) |
| `Langlands/Geometry/Manifold/LinearLieGroup/Units.lean` | `GroundTheory/AutomorphicForms/RealGroupsLie.lean`, `GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean` |
| `Langlands/Geometry/Manifold/LinearLieGroup/ProductCoordinates.lean` | `GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean` |
| `Langlands/Geometry/Manifold/LinearLieGroup/HaarDensity.lean` | `GroundTheory/AutomorphicForms/DixmierMalliavinHaar.lean`, `GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean`, `CompanionTheory/AutomorphicTheory/PadicUnitaryWeights/DixmierMalliavin/DecompDirection.lean` |
| `Langlands/Geometry/Manifold/LinearLieGroup/ClosedSubgroup.lean` | `Formalism/HermitianCurvature/HermitianCurvatureProofs/GroupGeneratedByExp.lean`, `Development/AbelianVarietyTheory/Proofs/FlagMeasures/ClosedMatrixSubgroupTheorem.lean`, `CompanionTheory/AutomorphicTheory/PadicUnitaryWeights/DixmierMalliavin/DixmierMalliavinFactorisationHolds.lean` |
| `Langlands/Analysis/DixmierMalliavin/DirectionalSeries.lean` | `GroundTheory/AutomorphicForms/DixmierMalliavinSeries.lean` |
| `Langlands/Analysis/DixmierMalliavin/IteratedKernel.lean` | `GroundTheory/AutomorphicForms/DixmierMalliavinProducts.lean` |
| `Langlands/Analysis/DixmierMalliavin/LinearGroup.lean` | `CompanionTheory/AutomorphicTheory/PadicUnitaryWeights/DixmierMalliavin/DecompDirection.lean` |
| `Langlands/Analysis/DixmierMalliavin/Product.lean` | `GroundTheory/AutomorphicForms/AdelicDixmierMalliavinProduct.lean` (fragments, adapted) |

The other new files of the Dixmier–Malliavin block (`Langlands/Analysis/ConvolutionIntegral.lean`,
`Langlands/Geometry/Manifold/LinearLieGroup/Realization.lean`,
`Langlands/Representation/Archimedean/DixmierMalliavin.lean`, the four files of the adelic layer
and the six consumer files) are written for the Library and contain no text from the repository.

### Cohomology of profinite groups and Galois cohomology of fields


Each of these files has a page (`.md` beside it) whose section "Source and licence" names the
source files and declarations it was taken from.

- `Langlands/Cohomology/Profinite/SmoothCoefficients.lean`
- `Langlands/Cohomology/Profinite/OpenNormal.lean`
- `Langlands/Cohomology/Profinite/Cochains.lean`
- `Langlands/Cohomology/Profinite/Functoriality.lean`
- `Langlands/Cohomology/Profinite/LongExactSequence.lean`
- `Langlands/Cohomology/Profinite/LowDegree.lean`
- `Langlands/Cohomology/Profinite/Comparison/Discrete.lean`
- `Langlands/Cohomology/Profinite/Comparison/FilteredHomology.lean`
- `Langlands/Cohomology/Profinite/Comparison/Coefficients.lean`
- `Langlands/Cohomology/Profinite/Comparison/Continuous.lean`
- `Langlands/Cohomology/Profinite/Comparison/FiniteQuotients.lean`
- `Langlands/Cohomology/Profinite/Coinduced/Basic.lean`
- `Langlands/Cohomology/Profinite/Coinduced/Acyclic.lean`
- `Langlands/Cohomology/Profinite/Coinduced/Quotient.lean`
- `Langlands/Cohomology/Profinite/Shapiro.lean`
- `Langlands/Cohomology/Profinite/Corestriction.lean`
- `Langlands/Cohomology/Profinite/InflationRestriction/DegreeOne.lean`
- `Langlands/Cohomology/Profinite/InflationRestriction/Transgression.lean`
- `Langlands/Cohomology/Profinite/InflationRestriction/FiveTerm.lean`
- `Langlands/Cohomology/Profinite/InflationRestriction/Higher.lean`
- `Langlands/Cohomology/Profinite/Cup/Cochains.lean`
- `Langlands/Cohomology/Profinite/Cup/Basic.lean`
- `Langlands/Cohomology/Profinite/Cup/Functoriality.lean`
- `Langlands/Cohomology/Profinite/Cup/Pairing.lean`
- `Langlands/Cohomology/Profinite/Cup/Connecting.lean`
- `Langlands/Cohomology/Profinite/Cup/Corestriction.lean`
- `Langlands/Cohomology/Profinite/Cup/Inflation.lean`
- `Langlands/Cohomology/Profinite/Cup/Graded.lean`
- `Langlands/Cohomology/Profinite/Characters.lean`
- `Langlands/Cohomology/Profinite/TorsionDual.lean`
- `Langlands/Cohomology/Profinite/Cyclic/Cup.lean`
- `Langlands/Cohomology/Profinite/Cyclic/Profinite.lean`
- `Langlands/Cohomology/Profinite/Dimension/Supernatural.lean`
- `Langlands/Cohomology/Profinite/Dimension/ProP.lean`
- `Langlands/Cohomology/Profinite/Dimension/Basic.lean`
- `Langlands/Cohomology/Profinite/Dimension/Procyclic.lean`
- `Langlands/Cohomology/Profinite/Dimension/Sylow.lean`
- `Langlands/Cohomology/Profinite/Dimension/Subgroup.lean`
- `Langlands/Cohomology/Profinite/EulerCharacteristic.lean`
- `Langlands/Cohomology/Profinite/InnerConjugation.lean`
- `Langlands/Cohomology/Profinite/Mackey/Decomposition.lean`
- `Langlands/Cohomology/Profinite/Mackey/Cohomology.lean`
- `Langlands/Cohomology/Profinite/ClassFormation/Basic.lean`
- `Langlands/Cohomology/Profinite/ClassFormation/FundamentalClass.lean`
- `Langlands/Cohomology/Profinite/ClassFormation/Corestriction.lean`
- `Langlands/Cohomology/Profinite/ClassFormation/TateTheorem.lean` (statement of the source's
  `exists_cupH_of_tate`; proof new, on the Library's Tate theorem)
- `Langlands/Cohomology/Profinite/ClassFormation/HighDegree.lean`
- `Langlands/Cohomology/Profinite/Duality/DualModule.lean`
- `Langlands/Cohomology/Profinite/Duality/Pairing.lean`
- `Langlands/Cohomology/Profinite/Duality/Devissage.lean`
- `Langlands/Cohomology/Profinite/Duality/Main.lean`
- `Langlands/GaloisCohomology/Field/Modules.lean`
- `Langlands/GaloisCohomology/Field/OpenSubgroup.lean`
- `Langlands/GaloisCohomology/Field/AdditiveHilbert90.lean`
- `Langlands/GaloisCohomology/Field/Hilbert90.lean`
- `Langlands/GaloisCohomology/Field/FiniteLevel.lean`
- `Langlands/GaloisCohomology/Field/KummerSequence.lean`
- `Langlands/GaloisCohomology/Field/CartierDual.lean`
- `Langlands/GaloisCohomology/Field/CyclicCup.lean`
- `Langlands/GaloisCohomology/Local/Invariant.lean`
- `Langlands/GaloisCohomology/Local/ClassFormation.lean`
- `Langlands/GaloisCohomology/Local/Finiteness.lean`
- `Langlands/GaloisCohomology/Local/Dimension.lean`
- `Langlands/GaloisCohomology/Local/Duality/RootsOfUnity.lean`
- `Langlands/GaloisCohomology/Local/Duality/KummerCup.lean`
- `Langlands/GaloisCohomology/Local/Duality/NormCharacters.lean`
- `Langlands/GaloisCohomology/Local/Duality/Pairing.lean`
- `Langlands/GaloisCohomology/Local/Arithmetic/Extension.lean`
- `Langlands/GaloisCohomology/Local/Arithmetic/Uniqueness.lean`
- `Langlands/GaloisCohomology/Local/Arithmetic/NormalLattice.lean`
- `Langlands/GaloisCohomology/Local/Arithmetic/Units.lean`
- `Langlands/GaloisCohomology/Local/Arithmetic/Integers.lean`
- `Langlands/GaloisCohomology/Local/Arithmetic/Ramification.lean`
- `Langlands/GaloisCohomology/Local/Arithmetic/SeparableClosure.lean`
- `Langlands/GaloisCohomology/Local/EulerCharacteristic/Additive.lean`
- `Langlands/GaloisCohomology/Local/EulerCharacteristic/Descent.lean`
- `Langlands/GaloisCohomology/Local/EulerCharacteristic/Twist.lean`
- `Langlands/GaloisCohomology/Local/EulerCharacteristic/Coinduced.lean`
- `Langlands/GaloisCohomology/Local/EulerCharacteristic/Kummer.lean`
- `Langlands/GaloisCohomology/Local/EulerCharacteristic/Units.lean`
- `Langlands/GaloisCohomology/Local/EulerCharacteristic/GroupStructure.lean`
- `Langlands/GaloisCohomology/Local/EulerCharacteristic/Vanishing.lean`
- `Langlands/GaloisCohomology/Local/EulerCharacteristic/Coprime.lean`
- `Langlands/GaloisCohomology/Local/EulerCharacteristic/Main.lean`
- `Langlands/GaloisCohomology/Local/Unramified.lean`

`Langlands/GaloisCohomology/Field/Brauer.lean` is new (no text of the repository) and is not
listed.

Galois cohomology of global fields, the Galois group `G_S` (sources under
`src/GroundTheory/ProfiniteCohomology/`; each page names the files and lines):

- `Langlands/Galois/RestrictedRamification/Unramified.lean` (`RestrictedRamification/{MaxUnramifiedOutside,
  Unramified, Ramification, ValuationTransport, IsUnramifiedOutsideIffLeMaxUnramifiedOutside,
  BaseChangeDefs, FiniteOpen, SUnits, ClassFieldGSUnram}.lean`, `GlobalClassFormation/IdeleCohomology/Ramified.lean`,
  `PoitouTate/PoitouTateInfinite/LevelModulesDefs.lean`, in part)
- `Langlands/Galois/RestrictedRamification/MaximalExtension.lean` (`RestrictedRamification/{MaxUnramifiedOutside,
  IsUnramifiedOutsideIffLeMaxUnramifiedOutside}.lean`, `PoitouTate/PoitouTateInfinite/{Restrict, Levels,
  LevelModulesDefs}.lean`, in part)
- `Langlands/Galois/RestrictedRamification/OpenSubgroups.lean` (`RestrictedRamification/{BaseChangeDefs,
  FiniteOpen}.lean`)
- `Langlands/Galois/RestrictedRamification/PlaceEmbeddings.lean` (`RestrictedRamification/LocalMaps.lean`, in
  part; `standardEmbedding` and the comparison with `Field.absoluteGaloisGroup.map` are new)
- `Langlands/Galois/RestrictedRamification/Localization.lean` (`RestrictedRamification/{LocalMaps,
  BaseChangePlaces, BaseChangeMackey, BaseChange}.lean`, two lemmas of
  `GlobalClassFormation/LocalLimits/IsScalarTowerFiniteSubfieldAlgebraicClosure.lean`)

Galois cohomology of global fields, cohomology with compact support (the abstract layer;
sources under `src/GroundTheory/ProfiniteCohomology/`; each page names the files and lines):

- `Langlands/GaloisCohomology/CompactSupport/Internal/MappingCocone.lean`
  (`CompactSupportCohomology/{HomApplyHomApplyEqOfCompEq, ShiftNegOneHomologyIsoSymmHom, ConeMap,
  HomologyMapPiLiftPiHomologyIsoHom}.lean`, `CompactSupportCohomology.lean`, in part)
- `Langlands/GaloisCohomology/CompactSupport/Basic.lean` (`CompactSupportCohomology/HomApplyHomApplyEqOfCompEq.lean`,
  `CompactSupportCohomology.lean`, in part)
- `Langlands/GaloisCohomology/CompactSupport/Functoriality.lean` (`CompactSupportCohomology.lean`, in part)
- `Langlands/GaloisCohomology/CompactSupport/Internal/LeibnizPairing.lean` (`CompactSupportCohomology/{Pairing,
  CupLeibniz}.lean`)
- `Langlands/GaloisCohomology/CompactSupport/Internal/ConeSigns.lean` (`CompactSupportCohomology/{ConePairing,
  ConeSymmetry}.lean`)
- `Langlands/GaloisCohomology/CompactSupport/CupProduct.lean` (`CompactSupportCohomology/CompactCupEqCompactCupRight.lean`)
- `Langlands/GaloisCohomology/CompactSupport/Internal/ConeHomotopy.lean` (`MackeyFormula/ConeHomotopy.lean`,
  `PoincarePairs/{ConeProduct, ConjHomotopyFunCupCochainZeroRight}.lean`)
- `Langlands/GaloisCohomology/CompactSupport/OpenSubgroup.lean` (`MackeyFormula/CompactSupport.lean`)
- `Langlands/GaloisCohomology/CompactSupport/DualityMap.lean` (`PoincarePairs/{IsDiscreteRepResHomCoindRes, Natural}.lean`)
- `Langlands/GaloisCohomology/CompactSupport/OpenSubgroupCup.lean` (`PoincarePairs/MackeyCup.lean`)
- `Langlands/GaloisCohomology/CompactSupport/Duality.lean` (`PoincarePairs/Devissage.lean`, `PoincarePairs.lean`)
- `Langlands/GaloisCohomology/CompactSupport/DualityPrimary.lean` (`PoitouTate/Primary.lean`)
- `Langlands/GaloisCohomology/CompactSupport/NineTerm.lean` (`PoitouTate/{PtCompactDualMapEqZeroOfPtCompactToGlobalEqZero,
  Abstract, General}.lean`; the structure `IsNineTermExact` and the definition of the connecting map are new)
- `Langlands/GaloisCohomology/CompactSupport/TateModified/Basic.lean` (`RealPlaces/{ConeDefs,
  LocalCohomologyIsoHomologyMapNormCochains, ConeMap}.lean`, `RealPlaces/LocalDualityDefs.lean` lines 15–39)
- `Langlands/GaloisCohomology/CompactSupport/TateModified/CupProduct.lean` (`RealPlaces/{ConeHomotopy, NormHomotopy,
  HomologyMapProdFstProdLeftHomology, CupSequence}.lean`)
- `Langlands/GaloisCohomology/CompactSupport/TateModified/Duality.lean` (`RealPlaces/{DevissageDefs, DevissageNatural,
  Devissage}.lean`)
- `Langlands/GaloisCohomology/CompactSupport/TateModified/OpenSubgroup.lean` (`RealPlaces/{InducedDefs, InducedDropOut,
  Induced}.lean`)
- `Langlands/GaloisCohomology/CompactSupport/TateModified/OrderTwo.lean` (`RealPlaces/{OrderTwo, InvolutionDuality,
  OrderTwoTate}.lean`)
- `Langlands/GaloisCohomology/CompactSupport/TateModified/NineTerm.lean` (`PoitouTate/{RealDefs, RealAbstract,
  RealCup}.lean`; `IsTateNineTermExact` and the definition of the connecting map are new)
- `Langlands/GaloisCohomology/CompactSupport/TateModified/Coinduced.lean` (`PoitouTate/RealEvenCoind.lean`)
- `Langlands/GaloisCohomology/CompactSupport/BaseCase.lean` (`RestrictedRamification/{BaseCores, BaseFormal}.lean`,
  without `surjective_gs_compactCores_three`)
- `Langlands/GaloisCohomology/CompactSupport/Internal/ConeReverse.lean` (`RestrictedRamification/BaseReverse.lean`)
- `Langlands/GaloisCohomology/CompactSupport/Transport.lean` (`RestrictedRamification/BaseTransport.lean` lines 1–303)

Galois cohomology of global fields, localization, `S`-units and the Brauer sequence (sources
under `src/GroundTheory/`; each page names the files and lines):

- `Langlands/GaloisCohomology/Global/Localization.lean` (`ProfiniteCohomology/RestrictedRamification/LocalMaps.lean`,
  sections `Conj` and `Local`; `ptRes`, `ptSha` of
  `ProfiniteCohomology/PoitouTate/PtCompactDualMapEqZeroOfPtCompactToGlobalEqZero.lean`, restated)
- `Langlands/GaloisCohomology/Global/Units/SUnits.lean` (`ProfiniteCohomology/RestrictedRamification/{SUnitsDefs,
  SUnits}.lean`, in part; `GlobalFields/SUnits.lean` lines 15–70; `GlobalFields/KummerTheory/Unramified.lean`)
- `Langlands/GaloisCohomology/Global/Units/Divisor.lean` (`ProfiniteCohomology/RestrictedRamification/{SPicDefs,
  SDivisor}.lean`)
- `Langlands/GaloisCohomology/Global/Units/Picard.lean` (`ProfiniteCohomology/RestrictedRamification/{SPicDefs,
  SPicFinite}.lean`, `SInvariantToInvariantsEqZeroIff.lean` sections `Quot`, `Phi`, `H1`)
- `Langlands/GaloisCohomology/Global/Units/Kummer.lean` (`ProfiniteCohomology/RestrictedRamification/{SUnitsDefs,
  SUnits}.lean`, in part; `SInvariantToInvariantsEqZeroIff.lean` sections `KummerPic`, `BaseChange`)

`Langlands/GaloisCohomology/Global/BrauerSequence/Statement.lean` contains no text of the source (it
restates, for an arbitrary number field and separable closure, the interface of the source's
`GlobalClassFormation`; its page names the declarations). The other files of
`Langlands/GaloisCohomology/Global/BrauerSequence/` contain no text of the source either (they prove
the interface from the Library's class field theory).

Galois cohomology of global fields, `H²` of the `S`-units and the Brauer group outside `S` (sources
under `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/`; each page names the files and
lines):

- `Langlands/GaloisCohomology/Global/Units/DivisorModule.lean` (`{DivisorModule, DivisorModuleSupport}.lean`)
- `Langlands/GaloisCohomology/Global/Units/DivisorMap.lean` (`BrauerDivisor.lean` lines 19–129,
  `BrauerDivisorPlaces.lean`)
- `Langlands/GaloisCohomology/Global/Units/Capitulation.lean` (`BrauerDivisor.lean` lines 176–546)
- `Langlands/GaloisCohomology/Global/Units/CapitulationPrincipalIdeal.lean` (two proofs that follow those of
  `Capitulation.lean`: `BrauerDivisor.lean` lines 176–546)
- `Langlands/GaloisCohomology/Global/Units/Inflation.lean` (`BrauerSplit.lean` lines 27–333)
- `Langlands/GaloisCohomology/Global/Units/DivisorSequence.lean` (`BrauerDivisor.lean` lines 109–175,
  `Brauer.lean` lines 16–280)
- `Langlands/GaloisCohomology/Global/Units/Brauer.lean` (`Brauer.lean` lines 280–426)
- `Langlands/GaloisCohomology/Global/Units/DivisorCount.lean` (`FiniteSetOfNsmulEqZeroQZ.lean` lines 14–44)
- `Langlands/GaloisCohomology/Global/Units/HighDegree.lean` (`EqZeroOfCohomologyInflThreeEqZero.lean`
  lines 14–76, `FiniteSetOfNsmulEqZeroQZ.lean` lines 45–110, `SurjectiveOfInjectiveOfInjective.lean`
  lines 150–273)
- `Langlands/GaloisCohomology/Global/Dimension/Statement.lean` (`Dimension.lean` lines 113–137)
- `Langlands/GaloisCohomology/Global/Dimension/Proof.lean` (`Dimension.lean` lines 41–110,
  `DimensionKummer.lean` lines 14–67)
- `Langlands/GaloisCohomology/Global/Finiteness.lean` (`Finite.lean` lines 99–224, `FiniteRoots.lean`
  lines 24–171)
- `Langlands/GaloisCohomology/Global/RealPlaces/LocalDuality.lean` (under
  `src/GroundTheory/ProfiniteCohomology/RealPlaces/`: `LocalDualityCup.lean` lines 15–290,
  `LocalDuality.lean` lines 13–312 and 329–358, `LocalDualityDefs.lean` lines 54–63)

Galois cohomology of global fields, the characters of `G_S` by `S`-idèle classes (sources under
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/`; each page names the declarations):

- `Langlands/GaloisCohomology/Global/Abelianization.lean` (`ClassFieldGS.lean`, `ClassFieldGSFull.lean`)
- `Langlands/GaloisCohomology/Global/Abelianization/SIdeleClassGroup.lean` (`ClassFieldGSDefs.lean`,
  `ClassFieldGS.lean`, `ClassFieldGSFull.lean`)
- `Langlands/GaloisCohomology/Global/Abelianization/Presentation.lean` (`ClassFieldGSDefs.lean`,
  `ClassFieldGSPresentation.lean`, `MkFiniteEmbeddingGlobalUniformizer.lean`,
  `GsRootsToUnitsCompactComparisonCup.lean`)

`Langlands/Galois/RestrictedRamification/ClosureChange.lean` and
`Langlands/GaloisCohomology/Global/Abelianization/Frobenius.lean` contain no text of the source. The source's proofs from its own class field theory are replaced by the
Library's global Artin map.

Galois cohomology of global fields, Poitou–Tate duality (sources under
`src/GroundTheory/ProfiniteCohomology/`; each page names the files and lines):

- `Langlands/GaloisCohomology/Global/PoitouTate/Trace.lean` (`PoitouTate/RealTrace.lean` lines 115–135, `PoitouTate/RealTraceMap.lean` lines 16–51)
- `Langlands/GaloisCohomology/Global/PoitouTate/BaseCase/Basic.lean` (`RestrictedRamification/BaseSwap.lean` lines 14–54, `RestrictedRamification/BaseInputs.lean` lines 17–22)
- `Langlands/GaloisCohomology/Global/PoitouTate/BaseCase/Kummer.lean` (`RestrictedRamification/BaseKummerDefs.lean` lines 18–34, 53–69, 90–95, `RestrictedRamification/BaseKummerDelta.lean` lines 38–48, `RestrictedRamification/BaseKummer.lean` lines 228–268)
- `Langlands/GaloisCohomology/Global/PoitouTate/BaseCase/UnitsData.lean` (`RestrictedRamification/BaseClass.lean` lines 26–60, 69–433, `RestrictedRamification/BaseClassIdele.lean` lines 21–296)
- `Langlands/GaloisCohomology/Global/PoitouTate/BaseCase/CupUnits.lean` (`RestrictedRamification/BaseCupCone.lean` lines 19–108, `RestrictedRamification/BaseCupGlob.lean` lines 22–47, `RestrictedRamification/BaseCupNat.lean` lines 28–62, `RestrictedRamification/BaseCupFormula.lean` lines 55–67, `RestrictedRamification/BaseCupKummer.lean` lines 36–69, 125–186, 289–320, `RestrictedRamification/BaseCupLocal.lean` lines 48–105, `RestrictedRamification/BaseCupGlobal.lean` lines 18–277)
- `Langlands/GaloisCohomology/Global/PoitouTate/BaseCase/Reciprocity.lean` (`RestrictedRamification/BasePairing.lean` lines 20–24, `RestrictedRamification/BaseCupLocal.lean` lines 164–226)
- `Langlands/GaloisCohomology/Global/PoitouTate/BaseCase/Pairing.lean` (`RestrictedRamification/BasePairing.lean` lines 28–77, 106–204)
- `Langlands/GaloisCohomology/Global/RealPlaces/VanishingCriterion.lean` (`RealPlaces/VanishingCriterion.lean` lines 26–80, 82–155)
- `Langlands/GaloisCohomology/Global/RealPlaces/VanishingDevissage.lean` (`RealPlaces/VanishingIndex.lean` lines 16–101, 121–260, `RealPlaces/VanishingPrimes.lean` lines 86–168)
- `Langlands/GaloisCohomology/Global/RealPlaces/VanishingTwo.lean` (`RealPlaces/VanishingUnitsTwo.lean` lines 143–174)
- `Langlands/GaloisCohomology/Global/RealPlaces/VanishingPlaces.lean` (`RealPlaces/VanishingMackeyPlaces.lean` lines 105–260, `RealPlaces/VanishingMackeyTransfer.lean` lines 51–147)
- `Langlands/GaloisCohomology/Global/RealPlaces/VanishingMackey.lean` (`RealPlaces/VanishingMackey.lean` lines 18–146, 174–178, 202–253, `RealPlaces/VanishingMackeyTransfer.lean` lines 180–259, 300–380)
- `Langlands/GaloisCohomology/Global/RealPlaces/VanishingProof.lean` (`RealPlaces/Vanishing.lean` lines 20–37)
- `Langlands/GaloisCohomology/Global/RealPlaces/DegreeThreeProof.lean` (`RealPlaces/Vanishing.lean` lines 39–79, `PoitouTate/NonemptyOfNatCastMemOfNeOne.lean` lines 130–150)

Galois cohomology of global fields, the global Euler characteristic formula (sources under
`src/GroundTheory/ProfiniteCohomology/`, or under `src/` where the path begins with `Development/`;
each page names the files and lines):

- `Langlands/GaloisCohomology/Global/EulerCharacteristic/Ratio.lean` (`GlobalEulerCharacteristic/DefsForms.lean` lines 1–176, `GlobalEulerCharacteristic/RealHerbrand.lean` lines 1–154)
- `Langlands/GaloisCohomology/Global/EulerCharacteristic/Multiplicative.lean` (`GlobalEulerCharacteristic/GsEulerRatioShortExactOfBijective.lean` lines 1–233, `GlobalEulerCharacteristic/PowDefs.lean` lines 1–23, `GlobalEulerCharacteristic/ApplySubrepresentationCongr.lean` lines 1–210, `Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/WorkMultl.lean` lines 1–59, `Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/WorkDevis.lean` lines 1–58)
- `Langlands/GaloisCohomology/Global/EulerCharacteristic/Induced.lean` (`GlobalEulerCharacteristic/ShapiroDefs.lean` lines 1–32, `GlobalEulerCharacteristic/ShapiroCoind.lean` lines 1–223, `GlobalEulerCharacteristic/ShapiroRatio.lean` lines 1–131, `GlobalEulerCharacteristic/ShapiroReal.lean` lines 1–180, `GlobalEulerCharacteristic/CardCohomologyZeroMackeyRepOfNeTop.lean` lines 1–95, `GlobalEulerCharacteristic/Shapiro.lean` lines 1–33)
- `Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/PermutationLattice.lean` (`GlobalEulerCharacteristic/PermLatticeDefs.lean` lines 1–16, `GlobalEulerCharacteristic/PermLattice.lean` lines 1–155, `GlobalEulerCharacteristic/PermLatticeCharacter.lean` lines 1–145)
- `Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/Artin.lean` (`GlobalEulerCharacteristic/ArtinDefs.lean` lines 1–92, `GlobalEulerCharacteristic/ArtinCount.lean` lines 1–109, `GlobalEulerCharacteristic/OrbitInvariants.lean` lines 1–331, `GlobalEulerCharacteristic/ToFunEqZeroOfForallIsCyclic.lean` lines 1–161)
- `Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/Cyclic.lean` (`Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/WorkKilledC.lean` lines 1–76, 86–238, `Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/WorkQuotV.lean` lines 1–71, `Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/WorkCoinfB.lean` lines 1–87, `GlobalEulerCharacteristic/ShapiroCoind.lean` lines 1–223)
- `Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/Reduction.lean` (`Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/WorkKilledB.lean` lines 1–347, `Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/ExistsPrimeToPart.lean` lines 1–127)
- `Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/Primary.lean` (`Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/WorkSplit.lean` lines 1–120, `Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/WorkAssemble.lean` lines 1–48, `Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/RatioOneKilled.lean` lines 1–23)
- `Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/KummerCount.lean` (`GlobalEulerCharacteristic/KummerSeq.lean` lines 1–275, `GlobalEulerCharacteristic/Kummer.lean` lines 1–218)
- `Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/UnitLattice.lean` (`GlobalEulerCharacteristic/UnitsDefs.lean` lines 1–28, `GlobalEulerCharacteristic/GEqAddOfExactOfFiniteCokernel.lean` lines 1–301)
- `Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/DualDimension.lean` (`GlobalEulerCharacteristic/OrbitInvariants.lean` lines 1–331)
- `Langlands/GaloisCohomology/Global/EulerCharacteristic/ShaDescent.lean` (`GlobalEulerCharacteristic/ShaDescent.lean` lines 1–215)
- `Langlands/GaloisCohomology/Global/EulerCharacteristic/ShaTwist.lean` (`GlobalEulerCharacteristic/ShaTwist.lean` lines 1–216)
- `Langlands/GaloisCohomology/Global/EulerCharacteristic/KummerSha.lean` (`GlobalEulerCharacteristic/KummerSha.lean` lines 1–155)
- `Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/KummerShaOpen.lean` (`GlobalEulerCharacteristic/KummerShaOpen.lean` lines 137–191)
- `Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/ShaCount.lean` (`GlobalEulerCharacteristic/MemShaSubmoduleCohomologyAddEquivOfEquivIff.lean` lines 1–216)
- `Langlands/GaloisCohomology/Global/EulerCharacteristic/Corollaries.lean` (`GlobalEulerCharacteristic/ShaCount.lean` lines 1–113)
- `Langlands/GaloisCohomology/Global/EulerCharacteristic/Statement.lean` (`GlobalEulerCharacteristic/GlobalEulerFormulaInf.lean` lines 1–88)

General lemmas with text of the source that stand in files of more general subjects than the
part they were ported with (sources under `src/GroundTheory/ProfiniteCohomology/`, or under `src/`
where the path begins with `Development/`; "also" where the file has an entry above; each page
names the declarations):

- `Langlands/Galois/RestrictedRamification/OpenSubgroups.lean` (also `Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/GaloisCohomologyRatios/PFinite.lean` lines 38–43)
- `Langlands/GaloisCohomology/Local/EulerCharacteristic/Twist.lean` (also `Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/GaloisCohomologyRatios/FiniteCohomologyRootsZMod.lean` lines 86–93)
- `Langlands/GaloisCohomology/Global/PoitouTate/Trace.lean` (also `GlobalEulerCharacteristic/KummerSha.lean`, in part, and `GlobalEulerCharacteristic/ShaCount.lean` lines 60–98, in part)
- `Langlands/GaloisCohomology/Global/PoitouTate/LocalDuality.lean` (`GlobalEulerCharacteristic/ShaCount.lean` lines 60–98, in part)
- `Langlands/GaloisCohomology/Global/Units/SUnits.lean` (also `GlobalEulerCharacteristic/ShaCount.lean` lines 60–98, in part)
- `Langlands/GaloisCohomology/Global/Localization.lean` (also `GlobalEulerCharacteristic/ShaDescent.lean`, in part)
- `Langlands/Cohomology/Profinite/Characters.lean` (also `GlobalEulerCharacteristic/ShaDescent.lean`, in part)
- `Langlands/Cohomology/Profinite/Duality/DualModule.lean` (also `RestrictedRamification/BaseInputs.lean` lines 17–22)
- `Langlands/Cohomology/Profinite/Duality/Devissage.lean` (also `RealPlaces/VanishingIndex.lean`, in part)
- `Langlands/Cohomology/Profinite/Comparison/FiniteQuotients.lean` (also `RealPlaces/VanishingMackey.lean`, in part)
- `Langlands/Cohomology/Profinite/Mackey/Cohomology.lean` (also `RealPlaces/VanishingMackey.lean`, in part)
- `Langlands/GaloisCohomology/CompactSupport/TateModified/Duality.lean` (also `RealPlaces/VanishingCriterion.lean`, in part)
- `Langlands/Cohomology/Profinite/Finiteness.lean` (`LocalClassFormation/FiniteVanishing/`: the dévissage lemmas)

### Kudla's splitting


Kudla's splitting for unitary dual pairs; source files under
`src/Development/AbelianVarietyTheory/`:

- `Langlands/ClassFieldTheory/Local/QuadraticNormIndex.lean` (`Proofs/DivisorProofs/MulMemRangeNorm.lean`
  lines 15–69, with a new proof; `Proofs/DivisorProofs/LocalNormResidueSignMul.lean`;
  `Definitions/Divisors/UnipVal.lean` lines 50–51)
- `Langlands/HarmonicAnalysis/LinearHaarScaling.lean` (`Proofs/DivisorProofs/` files
  `MapLinearEquivAddHaarLocalField`, `MapMulLeftEqNormSmul`, `MapTwoSidedMulHaarMatrixQuadraticExt`,
  `DetRestrictScalarsTwoSidedMatrixMul`, `HomogeneousMeasureEqSmulAddHaarLocalField`)
- `Langlands/HarmonicAnalysis/Bicharacter/SelfDual.lean` (`Definitions/Divisors/UnipVal.lean` lines 17–35;
  `Proofs/DivisorProofs/` files `CompactOpenSubgroupExhaustion`, `IsSelfDualBicharacterPairingOfSymmBilinForm`,
  `ExistsIntegralClosedBallAddCharEqZero`, parts of `BicharacterFourierTransformTwiceEqPosSmulReflect` and
  `LintegralFourSq`; parts of `Proofs/TwistedOperators/FourierTransformInversionLocalFieldPi.lean` and
  `Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean`)
- `Langlands/HarmonicAnalysis/Bicharacter/Fourier.lean` (`Proofs/DivisorProofs/` files
  `BicharacterFourierTransformMemSchwartzBruhat`, `BicharacterFourierTransformTwiceEqPosSmulReflect`,
  `LintegralFourSq`; `UnipVal.lean` line 37)
- `Langlands/HarmonicAnalysis/Bicharacter/GaussIntegral.lean` (`Proofs/DivisorProofs/` files
  `WeilFormulaFourierQuadraticCharacter`, `HasGaussIntegralCompAddEquivRescale`, `HasGaussIntegralCompactOpenPi`;
  `UnipVal.lean` lines 39–41)
- `Langlands/LinearAlgebra/HermitianDiagonalization.lean` (`Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean`
  lines 12–105, 130–220)
- `Langlands/Group/Unitary/Basic.lean` (`Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean` lines 142–320,
  402–408; `Proofs/DivisorProofs/ExistsGLDiagonalCongruentHermitian.lean`)
- `Langlands/Group/Unitary/Hyperbolic.lean` (`PublishedTheorems/TwistedTraceFormula/KudlaSplittingSplitUnitary.lean`
  lines 15–74; `Definitions/Divisors/UnipVal.lean` lines 55–110;
  `Proofs/DivisorProofs/SplitUnitarySiegelParabolicBlockRelations.lean`)
- `Langlands/Group/Unitary/BigCell.lean` (`Proofs/DivisorProofs/` files `InCellIffDetNeZero`,
  `ExistsHermitianSplitUnitaryLowerBlockInvertible`, `ExistsTranslateInCell`,
  `SiegelParabolicWeylElementGenerateUnitary`, `IsOpenSubgroupOfSiegelAndOppositeNhds`)
- `Langlands/Group/BigCellHom.lean` (`Proofs/DivisorProofs/ExistsHomOfBigCellGenericRelations.lean` lines 11–126)
- `Langlands/Theta/DualPair/Unitary/Form.lean`, `Langlands/Theta/DualPair/Unitary/Schrodinger.lean` and
  `Langlands/HarmonicAnalysis/QuadraticExtensionTopology.lean` (`PublishedTheorems/TwistedTraceFormula/KudlaSplittingSplitUnitary.lean`
  lines 76–212; `Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean` lines 173, 326–327;
  `Definitions/Divisors/UnipVal.lean` lines 17–25, 53, 76–108; `Proofs/DivisorProofs/QuadExtTopology.lean`;
  `Proofs/DivisorProofs/HermitianMatrixColumnPairingAlgebraicProperties.lean`)
- `Langlands/Theta/DualPair/LerayCharacter.lean` and `Langlands/ClassFieldTheory/Local/QuadraticNormBall.lean`
  (`HilbertNinetyQuotientHomEqIff.lean` lines 396–408;
  `UnipVal.lean` lines 50–51, 120–123; `Proofs/DivisorProofs/` files `LocalNormResidueSignMul`,
  `ExistsCompactOpenNormClosedBallQuadratic`, `UnitaryCharacterAbsScalarBasicProperties`,
  `UnitaryCharacterAbsScalarEventuallyEqOne`; `Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean`
  lines 79–92)
- `Langlands/Theta/DualPair/Unitary/SiegelParabolic.lean` (`UnipVal.lean` lines 125–128; `Proofs/DivisorProofs/`
  files `ParFunSiegMul`, `SiegelParabolicPreservesSchwartzBruhat`, `SiegelParabolicOperatorsHeisenbergCompat`,
  `LintegralSqSiegelParabolicOperatorEq`, `SchwartzBruhatFixedNearOneSiegelParabolic`)
- `Langlands/Theta/WeilIndex/NormForm.lean` (`Proofs/DivisorProofs/` files
  `GaussIntegralNormFormNonNormCancel`, `GaussIntegralQuadraticCharEventuallyConst`,
  `GaussIntegralNormFormScaledEqSignAbsInv`)
- `Langlands/Theta/DualPair/TensorInvariants.lean` (`Proofs/DivisorProofs/` files
  `GaussIntegralDiagonalHermitianFormMatrices`, `HermitianMatrixColumnPairingDiagonalNorm`,
  `HasGaussIntegralHermitianQuadraticCharacter`)
- `Langlands/Theta/DualPair/Unitary/WeylElement.lean` (`UnipVal.lean` lines 130–132; `Proofs/DivisorProofs/` files
  `FourierIntertwinesSiegelLeviOperator`, `FourierIntertwinesWeylHeisenbergSchrodinger`,
  `FourierHermitianMultiplierBraidRelation`)
- `Langlands/Theta/DualPair/Unitary/Splitting.lean` (`UnipVal.lean` lines 134–138; `Proofs/DivisorProofs/` files
  `ExistsWeilRepresentationBigCellRelationFourier`, `ExistsWeilRepresentationSplitUnitarySchwartzBruh`,
  `WeilRepresentationIntertwinesHeisenberg`, `WeilRepresentationPreservesL2Space`,
  `SplitUnitaryWeilRepresentationIsSmooth`, `KudlaSplittingSplitUnitary`)
- `Langlands/Theta/DualPair/TypeII.lean` and `Langlands/Theta/Correspondence/TypeII.lean` (`Definitions/Foundations/MatrixMeasurableSpace.lean`
  lines 40–45; `Definitions/GaloisGeometry/IsParahoricVec.lean` lines 20–24;
  `PublishedTheorems/GaloisGeometry₂/HypothesesAbsDet.lean` lines 12–25, restated)

`Langlands/HarmonicAnalysis/Bicharacter/Instances.lean` and
`Langlands/Representation/Smooth/OpenStabilizer.lean` contain no text of the source (the latter makes
public the proof of a private lemma of `Langlands/Theta/Heisenberg/StoneVonNeumann.lean`).

### The geometric side of the simple twisted trace formula (unfolding and quotients in stages)

Each of these files has a page (`.md` beside it) whose section "Source and licence" names the
source files and lines it takes text from and what was changed.

- `Langlands/Analysis/Local/QuotientNormalizingFunction.lean`
  (`Development/AutomorphicArithmetic/Foundations/Convolution/LocalGroupAnalysis/ClosedSubgroupCutoffExists.lean`
  lines 8–157; the predicate of `Development/WeilBound/RepresentationTheoryGL/TwistedFactors/SelmerRankBounds/IsNormAlong.lean`
  lines 21–22, restated)
- `Langlands/TraceFormula/TwistedGeometricUnfolding.lean`
  (`Development/AutomorphicArithmetic/Foundations/Convolution/LocalGroupAnalysis/TwistedGeometricSideUnfolding.lean`
  lines 12–17, 28–77, 227–268, adapted; the fundamental domain of the source is replaced by a
  normalizing function)

`Langlands/Analysis/Local/QuotientInStages.lean` contains no text of the source (its main theorem has
the content of the source's statement `U2`; its proof is new and its page names the source
declarations it corresponds to).

`Langlands/TraceFormula/TwistedGeometricSide.lean` contains no text of the source (it combines the
two files above).

### Matching near the identity for cyclic base change

Each of these files has a page (`.md` beside it) whose section "Source and licence" names the
source files and lines it takes text from and what was changed. Source paths are under
`src/Development/AutomorphicArithmetic/Foundations/Convolution/TwistedLocalOrbits/`.

- `Langlands/Group/GL/NormCongruence.lean` (`RootConj.lean` lines 5–93, `RootEx.lean` lines 7–194,
  `ValuationNatCastLeOne.lean` lines 9–153, `OpenNear.lean` lines 5–263; valuations replaced by an
  ultrametric norm)
- `Langlands/BaseChange/CongruenceTwistedDescent.lean` (`NearCore.lean` lines 35–54 and 95–139,
  `RigidNear.lean` lines 5–20, `Bridge.lean` lines 14–32, `NearDown.lean` lines 165–172 and
  221–235, `NearUp.lean` lines 181–196)
- `Langlands/Analysis/Local/QuotientCompactOpenDescent.lean` (`QuotDesc.lean` lines 43–84 and
  167–206: the statement of `quotDesc` and the density of `lintegral_desc`, with a new proof on
  compatible quotient measures)
- `Langlands/BaseChange/NearIdentityConcordance.lean` (`NearCore.lean` lines 27–29, 56–84 and
  145–294, with the matching part of `NearDown.lean`, lines 278–364; stated on `AreConcordant`)
- `Langlands/BaseChange/NearIdentityMatching.lean` (`NearDown.lean` lines 26–67, 200–235 and
  241–277; `NearUp.lean` lines 25–76 and 116–209; stated on `AreConcordant` with explicit
  radii for the spectral norm)

`Langlands/Analysis/Local/FiniteExtensionNormedField.lean` and
`Langlands/BaseChange/NearIdentityMatchingStatement.lean` contain no text of the source (the first
replaces the source's valuation on `E`; the second is the Library's statement of the result of
`nearDown` and `nearUp`).

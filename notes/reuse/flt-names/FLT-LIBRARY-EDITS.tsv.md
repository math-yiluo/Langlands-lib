# `FLT-LIBRARY-EDITS.tsv`

This page holds the table `FLT-LIBRARY-EDITS.tsv` as it is, in the code block below. To use it, save the content of the block under that name.

```text
file	part	what changed
Langlands/AbelianScheme/PolarizedFiniteLevel/CubicEmbeddingBoundedEquations.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AbelianScheme/PolarizedFiniteLevel/FrameEmbeddingHilbertPolynomial.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AbelianScheme/RelativeEndomorphismAffineHomSchemePieces.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/DvrAffineReducedFibre/SmoothFibreStalk.lean	A	rename (part A): uses of `AlgebraicGeometry.Smooth.isRegularLocalRing_stalk`, `IsRegularLocalRing.isDomain` renamed to `isRegularLocalRing_stalkFLT`, `isDomainFLT`
Langlands/AlgebraicGeometry/DvrAffineReducedFibre/TotalFractions.lean	A	rename (part A): uses of `AlgebraicGeometry.Smooth.isRegularLocalRing_stalk`, `IsRegularLocalRing.isDomain` renamed to `isRegularLocalRing_stalkFLT`, `isDomainFLT`
Langlands/AlgebraicGeometry/DvrStableNormalization/NormalStalks.lean	A	rename (part A): uses of `AlgebraicGeometry.Smooth.isRegularLocalRing_stalk`, `IsRegularLocalRing.isDomain` renamed to `isRegularLocalRing_stalkFLT`, `isDomainFLT`
Langlands/AlgebraicGeometry/HilbertSchemeUniversalFamily/ProjectivePieces.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero`, `AlgebraicGeometry.Scheme.Modules.tensorPow_succ`, `AlgebraicGeometry.Scheme.Modules.tensorPow_zero` renamed to `IsInvertibleFLT`, `tensorPowSectionFLT_zero`, `tensorPowFLT_succ`, `tensorPowFLT_zero`
Langlands/AlgebraicGeometry/HilbertSchemeUniversalFamilyStatement.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/Modules/GeometricFibreSectionsDim.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback` renamed to `IsInvertibleFLT`, `pullbackFLT`; dot-notation applications of `IsInvertible.pullbackFLT` on `IsInvertibleFLT` proofs written out
Langlands/AlgebraicGeometry/Modules/ProjectiveFibreTwistCohomologyStatement.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/Modules/ProjectiveFibreTwistEuler.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback`, `AlgebraicGeometry.Scheme.Modules.tensorPow` renamed to `IsInvertibleFLT`, `pullbackFLT`, `tensorPowFLT`; dot-notation applications of `IsInvertible.pullbackFLT`, `IsInvertible.tensorPow_monoidalV2`, `IsInvertible.tensor_monoidalV2` on `IsInvertibleFLT` proofs written out
Langlands/AlgebraicGeometry/Modules/ProjectiveFibreTwistSections.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback`, `AlgebraicGeometry.Scheme.Modules.tensorPow` renamed to `IsInvertibleFLT`, `pullbackFLT`, `tensorPowFLT`; dot-notation applications of `IsInvertible.bijective_lift_tensorSectionsBilin_monoidalV2`, `IsInvertible.dual_monoidalV2`, `IsInvertible.pullbackFLT`, `IsInvertible.tensorPow_monoidalV2`, `IsInvertible.tensor_monoidalV2` on `IsInvertibleFLT` proofs written out
Langlands/AlgebraicGeometry/Modules/ProjectiveFibreTwistUniformVanishing.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback`, `AlgebraicGeometry.Scheme.Modules.tensorPow` renamed to `IsInvertibleFLT`, `pullbackFLT`, `tensorPowFLT`; dot-notation applications of `IsInvertible.pullbackFLT`, `IsInvertible.tensor_monoidalV2` on `IsInvertibleFLT` proofs written out
Langlands/AlgebraicGeometry/Modules/ProjectiveRelativeDivisorFibreHilbertStatement.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/Modules/ProperFibreCohomologyDimBaseChangeProof.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback` renamed to `pullbackFLT`; dot-notation applications of `IsInvertible.pullbackFLT` on `IsInvertibleFLT` proofs written out
Langlands/AlgebraicGeometry/Modules/ProperFibreCohomologyDimBaseChangeStatement.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/Modules/ProperFlatFibreCohomologySemicontinuityProof.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback` renamed to `IsInvertibleFLT`, `pullbackFLT`; dot-notation applications of `IsInvertible.pullbackFLT` on `IsInvertibleFLT` proofs written out
Langlands/AlgebraicGeometry/Modules/ProperFlatFibreCohomologySemicontinuityStatement.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/Modules/RelativeSerreVanishingInvertible.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `AlgebraicGeometry.Scheme.Modules.tensorPow` renamed to `IsInvertibleFLT`, `tensorPowFLT`; dot-notation applications of `IsInvertible.tensorPow_monoidalV2`, `IsInvertible.tensor_monoidalV2` on `IsInvertibleFLT` proofs written out
Langlands/AlgebraicGeometry/Modules/TensorPowerGauge.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.tensorPow`, `AlgebraicGeometry.Scheme.Modules.tensorPowSection` renamed to `tensorPowFLT`, `tensorPowSectionFLT`
Langlands/AlgebraicGeometry/Modules/TwistCechBridge.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`; dot-notation applications of `IsInvertible.bijective_lift_tensorSectionsBilin_monoidalV2` on `IsInvertibleFLT` proofs written out
Langlands/AlgebraicGeometry/NoetherianApproximation/LineBundleDescentBridge.lean	A	rename (part A): module docstring names `Scheme.Modules.IsInvertibleFLT` (2 lines)
Langlands/AlgebraicGeometry/NoetherianApproximation/LineBundleIsoSubalgebraDescentProof.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback` renamed to `IsInvertibleFLT`, `pullbackFLT`; dot-notation applications of `IsInvertible.pullbackFLT` on `IsInvertibleFLT` proofs written out
Langlands/AlgebraicGeometry/NoetherianApproximation/LineBundleSubalgebraDescentProof.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback` renamed to `IsInvertibleFLT`, `pullbackFLT`; dot-notation applications of `IsInvertible.pullbackFLT` on `IsInvertibleFLT` proofs written out
Langlands/AlgebraicGeometry/Picard/AffineLineBundlePicard.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`; dot-notation applications of `IsInvertible.bijective_lift_tensorSectionsBilin_monoidalV2` on `IsInvertibleFLT` proofs written out
Langlands/AlgebraicGeometry/Picard/AlgClosedFieldDualSchemeRelativeDimensionProof.lean	A	rename (part A): uses of `IsRegularLocalRing.isDomain` renamed to `isDomainFLT`
Langlands/AlgebraicGeometry/Picard/AlgClosedFieldDualSchemeRelativeDimensionReduction.lean	A	rename (part A): uses of `IsRegularLocalRing.isDomain` renamed to `isDomainFLT`
Langlands/AlgebraicGeometry/Picard/FrameCombinationTrivialization.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback` renamed to `IsInvertibleFLT`, `pullbackFLT`; `import Mathlib` -> `import Langlands.MathlibBase`
Langlands/AlgebraicGeometry/Picard/LinearSystemAssembly.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/Picard/LinearSystemFlatness.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/Picard/NoetherianIntegralFibrePicardPiecesReduction.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback` renamed to `IsInvertibleFLT`, `pullbackFLT`; dot-notation applications of `IsInvertible.pullbackFLT` on `IsInvertibleFLT` proofs written out
Langlands/AlgebraicGeometry/Picard/NoetherianLineBundleSeesawProof.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/Picard/PicardHilbertPiecesRepresentabilityReductionAbel.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/Picard/PicardHilbertPiecesRepresentabilityReductionClasses.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/Picard/PicardHilbertPiecesRepresentabilityReductionPoints.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/Picard/PicardHilbertPiecesRepresentabilityReductionRelation.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/Picard/PicardHilbertPiecesRepresentabilityReductionSetup.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/Picard/PicardHilbertPiecesRepresentabilityStatement.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/Picard/PicardHilbertPolynomialPiecesReduction.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback`, `AlgebraicGeometry.Scheme.Modules.dual` renamed to `IsInvertibleFLT`, `pullbackFLT`, `dualFLT`; dot-notation applications of `IsInvertible.dual_monoidalV2`, `IsInvertible.pullbackFLT`, `IsInvertible.tensor_monoidalV2` on `IsInvertibleFLT` proofs written out
Langlands/AlgebraicGeometry/Picard/PicardHilbertPolynomialPiecesStatement.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/Picard/PoincareDirectImageLocal.lean	A	rename (part A): uses of `AlgebraicGeometry.Smooth.isRegularLocalRing_stalk` renamed to `isRegularLocalRing_stalkFLT`
Langlands/AlgebraicGeometry/Picard/ProperAmpleClosedImmersionBySectionsProof.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/Picard/ProperAmpleClosedImmersionBySectionsStatement.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/Picard/ProperFlatIntegralLinearSystemStatement.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/Picard/ProperFlatIntegralSheafClassTwistProof.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/Picard/ProperFlatIntegralSheafClassTwistStatement.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/Picard/RelativeDivisorFibreHilbert.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback` renamed to `IsInvertibleFLT`, `pullbackFLT`; dot-notation applications of `IsInvertible.pullbackFLT`, `IsInvertible.tensor_monoidalV2` on `IsInvertibleFLT` proofs written out
Langlands/AlgebraicGeometry/Picard/RelativeDivisorFibreSequence.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/Picard/RelativeEffectiveDivisorBaseChangeProof.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback` renamed to `IsInvertibleFLT`, `pullbackFLT`; dot-notation applications of `IsInvertible.pullbackFLT` on `IsInvertibleFLT` proofs written out
Langlands/AlgebraicGeometry/Picard/RelativeEffectiveDivisorHilbertPiecesStatement.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/ProjectiveSpace/TwistOnePresentation.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` renamed to `IsInvertibleFLT`
Langlands/AlgebraicGeometry/SmoothDvrAffineOpenGeometry.lean	A	rename (part A): uses of `IsRegularLocalRing.isDomain` renamed to `isDomainFLT`
Langlands/AlgebraicGeometry/SmoothDvrPrincipalOpen.lean	A	rename (part A): uses of `IsRegularLocalRing.isDomain` renamed to `isDomainFLT`
Langlands/AlgebraicGeometry/SmoothPointedGeometricConnectedness.lean	A	rename (part A): uses of `AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected` renamed to `geometricallyConnectedFLT`
Langlands/GroupScheme/AlgebraicallyClosedComponentBaseChangeProof.lean	A	rename (part A): uses of `AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected` renamed to `geometricallyConnectedFLT`
Langlands/GroupScheme/Dynamic/IdentityComponent.lean	A	rename (part A): uses of `AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected` renamed to `geometricallyConnectedFLT`
Langlands/GroupScheme/FiniteFreeAlgebraUnipotentUnits.lean	A	rename (part A): uses of `AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected` renamed to `geometricallyConnectedFLT`
Langlands/GroupScheme/FiniteFreeAlgebraUnits.lean	A	rename (part A): uses of `AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected` renamed to `geometricallyConnectedFLT`
Langlands/GroupScheme/FiniteKernelFunctions.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.IdealSheafData.comap_ofIdealTop` renamed to `comap_ofIdealTopFLT`
Langlands/GroupScheme/FiniteKernelRepresentation.lean	A	rename (part A): uses of `AlgebraicGeometry.Scheme.IdealSheafData.comap_ofIdealTop` renamed to `comap_ofIdealTopFLT`
Langlands/GroupScheme/ImageGenerationGeometry.lean	A	rename (part A): uses of `AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected` renamed to `geometricallyConnectedFLT`
Langlands/GroupScheme/Lie/SmoothIsogenyDimension.lean	A	rename (part A): uses of `AlgebraicGeometry.Smooth.isRegularLocalRing_stalk` renamed to `isRegularLocalRing_stalkFLT`
Langlands/AbelianScheme/RelativeEndomorphismAffineHomSchemePieces.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/DvrStableNormalization/NormalStalks.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/HilbertSchemeUniversalFamily/ProjectivePieces.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/HilbertSchemeUniversalFamilyStatement.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/Modules/GeometricFibreSectionsDim.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/Modules/ProjectiveFibreTwistUniformVanishing.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/Modules/ProperFibreCohomologyDimBaseChangeProof.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/Modules/ProperFibreCohomologyDimBaseChangeStatement.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/Modules/ProperFlatFibreCohomologySemicontinuityProof.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/Modules/ProperFlatFibreCohomologySemicontinuityStatement.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/Modules/RelativeSerreVanishingInvertible.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/Modules/TensorPowerGauge.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/NoetherianApproximation/LineBundleDescentBridge.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/NoetherianApproximation/LineBundleDescentStatements.md	A	page only (its Lean file is unchanged): names a renamed declaration as it now is
Langlands/AlgebraicGeometry/NoetherianApproximation/LineBundleIsoSubalgebraDescentProof.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/NoetherianApproximation/LineBundleSubalgebraDescentProof.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/Picard/AlgClosedFieldDualSchemeRelativeDimensionReduction.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/Picard/FrameCombinationTrivialization.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/Picard/NoetherianIntegralFibrePicardPiecesReduction.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/Picard/NoetherianLineBundleSeesawProof.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/Picard/PicardHilbertPiecesRepresentabilityStatement.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/Picard/PicardHilbertPolynomialPiecesReduction.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/Picard/PicardHilbertPolynomialPiecesStatement.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/Picard/PoincareDirectImageLocal.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/Picard/ProperAmpleClosedImmersionBySectionsStatement.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/Picard/ProperFlatIntegralLinearSystemStatement.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/Picard/ProperFlatIntegralSheafClassTwistProof.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/Picard/ProperFlatIntegralSheafClassTwistStatement.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/Picard/RelativeEffectiveDivisorHilbertPiecesStatement.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/ProjectiveSpace/TwistOnePresentation.md	A	page: names of the renamed declarations as they now are
Langlands/AlgebraicGeometry/SmoothDvrAffineOpenGeometry.md	A	page: names of the renamed declarations as they now are
Langlands/GroupScheme/AlgebraicallyClosedComponentBaseChangeProof.md	A	page: names of the renamed declarations as they now are
Langlands/GroupScheme/FiniteFreeAlgebraUnits.md	A	page: names of the renamed declarations as they now are
Langlands/GroupScheme/FiniteKernelFunctions.md	A	page: names of the renamed declarations as they now are
Langlands/GroupScheme/ImageGenerationGeometry.md	A	page: names of the renamed declarations as they now are
Langlands/GroupScheme/Lie/SmoothIsogenyDimension.md	A	page: names of the renamed declarations as they now are
Langlands/MathlibBase.lean	A (operator note 1)	new: imports all of Mathlib except the 3 modules that clash with weil-conjectures; declares nothing; made by tools/make_mathlib_base.py
Langlands/MathlibBase.md	A (operator note 1)	new page of Langlands.MathlibBase
(1,275 files: every workspace file with the line `import Mathlib`)	A (operator note 1)	`import Mathlib` -> `import Langlands.MathlibBase` (tools/replace_mathlib_import.py), nothing else; by directory: Langlands/Algebra 2, Langlands/AlgebraicGeometry 19, Langlands/Cohomology 4, Langlands/CommutativeAlgebra 7, Langlands/GroupScheme 2 (34 outside the extract); inside the extract Langlands/AnthropicFLT/Definitions 61, OverBase 5, P2M 600, Theorems 575 (1,241). Files listed above for the rename have this change too.
Langlands/AbelianScheme/PolarizedFiniteLevel/TorsionBracketMapReduction.lean	A (not in the workspace)	`.tensorPow` -> `.tensorPowFLT` (dot notation on `X.Modules` terms), lines 115; done by tools/rename_flt_clashes.py on the whole tree (table part lean_outside); checked by compiling a copy against the renamed workspace
Langlands/AlgebraicGeometry/NoetherianApproximation/LineBundleQuotientDescent.lean	A (not in the workspace)	dot-notation `h.pullback f` on `IsInvertibleFLT` proofs written out as `Scheme.Modules.IsInvertible.pullbackFLT (hL := h) f`, lines 92, 109; done by tools/rename_flt_clashes.py on the whole tree (table part lean_outside); checked by compiling a copy against the renamed workspace
Langlands/AlgebraicGeometry/ProjectiveSpace/EvaluationBracketAtlas.lean	A (not in the workspace)	`.tensorPow` -> `.tensorPowFLT` (dot notation on `X.Modules` terms), lines 124, 241; done by tools/rename_flt_clashes.py on the whole tree (table part lean_outside); checked by compiling a copy against the renamed workspace
Langlands/AlgebraicGeometry/ProjectiveSpace/EvaluationBracketFibres.lean	A (not in the workspace)	`.tensorPow` -> `.tensorPowFLT` (dot notation on `X.Modules` terms), lines 164, 216, 325; done by tools/rename_flt_clashes.py on the whole tree (table part lean_outside); checked by compiling a copy against the renamed workspace
Langlands/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean	B	new (staged for Mathlib): RestrictedProduct.mapAlongLinearMap, _apply, inclusionLinearMap moved from LinearAlgebra/RestrictedProduct/Tensor.lean, Imperial text of commit 0198058 (Basic.lean 8-12, 38-88); made by tools/make_staged_files.py
Langlands/Mathlib/Topology/Algebra/RestrictedProduct/Basic.md	B	new page of the staged module (origin as in the header)
Langlands/Mathlib/Topology/Algebra/RestrictedProduct/Equiv.lean	B	new (staged for Mathlib): Equiv/AddEquiv/LinearEquiv.restrictedProductCongrRight, Equiv…_apply, _symm_apply, AddEquiv…_apply and the 8 flattening declarations moved from LinearAlgebra/RestrictedProduct/Equiv.lean; Imperial text of commit 0198058 (Equiv.lean 31-49, 105-126, 520-589) except the parts marked `-- Library text:`; made by tools/make_staged_files.py
Langlands/Mathlib/Topology/Algebra/RestrictedProduct/Equiv.md	B	new page of the staged module (origin as in the header; Imperial text vs Library text)
Langlands/Mathlib/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean	B	new (staged for Mathlib): RestrictedProduct.rangeLTensor, rangeLTensorLeft, lTensor, lTensorLeft, lTensor_tmul, lTensorLeft_tmul moved from LinearAlgebra/RestrictedProduct/Tensor.lean, Imperial text of commit 0198058 (TensorRestrictedProduct.lean 24-91); made by tools/make_staged_files.py
Langlands/Mathlib/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.md	B	new page of the staged module (origin as in the header)
Langlands/Global/FiniteProjectivePiTensor.lean	B	line 18: `RestrictedProduct.tensorPiComparison_proof` -> `Langlands.LinearAlgebra.RestrictedProduct.tensorPiComparison_proof` (the Library's own theorem moved under Langlands.LinearAlgebra)
Langlands/Global/FiniteProjectivePiTensor.md	B	page: the theorem's new name
```

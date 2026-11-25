# JPSS core over all local fields: module audit

This is the module list for generalizing the p-adic JPSS core to all nonarchimedean
local fields. It audits the **old p-adic source
modules** in the import closures of the three shared JPSS proof roots. It separates
new local-field arguments from canonical instance setup, topology transport and
ancillary imports. The audited Library commit is
`26a5c21c0dd926a6ba1106b5c4a08f30fdea612c`; all counts below refer to that snapshot,
in which the general proofs are already present.

The direct source scan finds **78 modules**: 8 foundation modules, 12 modules needing
a different argument, 41 setup/transport modules, 12 ancillary arithmetic imports,
and 5 unrelated complex module-topology hits. Seven additional modules relay the
L-branch high-ramification dependency and are listed separately. Of the 1,010 modules
that explicitly spell `PadicField` in code, 62 occur in these tables and **948 remain
parametric at this source boundary**; their counts by directory appear below.
These are source-module counts, including statement files and examples, not counts
of independent mathematical lemmas or of new proofs to write.

## Scope and reproducibility

The roots are:

- `Langlands.Representation.RankinSelberg.UnequalRankFunctionalEquationProof`
  (the unequal-rank clause of JPSS (2.7)).
- `Langlands.Representation.RankinSelberg.GammaMultiplicativityProof`
  (the gamma clause of JPSS (3.1)).
- `Langlands.Representation.RankinSelberg.LFactorMultiplicativityProof`
  (the L-polynomial clause of JPSS (3.1)).

The [reproduction script](jpss-field-audit-reproduce.md) follows project imports
(`Langlands.*`) recursively, including each root. Mathlib imports are outside the
module count. It removes nested/line comments, ordinary strings and import lines
before looking for source uses. It records every reached module and marker location,
so the directory counts can be expanded into exact file lists. It also reads the
module tables in this note to reproduce the disjoint classification and remainder.

| Root | Project modules | Code modules spelling `PadicField` | Direct scan candidates | Additional L relays |
| --- | ---: | ---: | ---: | ---: |
| Unequal-rank FE | 902 | 356 | 63 | 0 |
| Gamma | 1840 | 951 | 73 | 0 |
| L | 1953 | 1008 | 78 | 7 |
| Union | 1958 | 1010 | 78 | 7 |

The marker families and their overlapping counts are:

| Marker family | Modules |
| --- | ---: |
| `Padic_base` | 30 |
| `canonical_norm` | 46 |
| `canonical_module` | 7 |
| `spectral` | 12 |
| `base_module_structure` | 18 |
| `ramification` | 5 |
| `field_CharZero` | 8 |

The scan covers `Padic p`, exact canonical norm names, canonical-module topology
comparisons, `spectralNorm`, the base-module/valuation-extension structures,
ramification/extension-degree comparisons, and `CharZero` on the field. A broad
`canonicalNorm*` search would falsely match `canonicalNormalizedProductInduced`.
An unrestricted `IsScalarTower` search would count unrelated algebra, and
`CharZero.eq_neg_self_iff` in `BruhatCellRestrictionVanishingProof` is applied to
complex distribution values, not to the ground field.

The classification uses the code at each hit and the implemented general proof
routes, not the marker count alone. In particular, a source file can be imported
for its generic helpers while its p-adic theorem is unused. This is an **import
and source audit**, not a traversal of the Lean kernel dependency graph of each
entry theorem. The 948-module remainder means that its source uses the p-adic
carrier/bundled APIs parametrically, or calls other named results; it does not
mean those calls have no transitive p-adic dependencies. Such calls must be
redirected to their general versions. The L-branch relay table records the
important dependency change that a direct token scan would miss.

## The general interface and the actual changes

General consumers use `[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`, with the needed Borel/separation instances, or
`T : LocalFieldData F`. They reuse the existing field-generic group,
representation, Whittaker-functional, zeta-value and factor-relation definitions.
The [general foundation](../../Langlands/AllField/LocalField/Foundation.md)
provides normalized-absolute-value balls, continuity, compact integers and Haar
regularity directly from the supplied valuation and topology. It avoids comparison
with a finite extension of `Padic p`.

The published explicit interfaces retain `q`, `abv` and the Haar measures as
arguments. They assume residue-cardinality identification, a uniformizer with
`abv ϖ = q⁻¹`, absolute value one on valuation units, and the applicable
`IsSelfDual`/`Conductor.IsJacquetNormalization` hypotheses. The normalization
comparison is the existing
`Langlands.AllField.RankinSelberg.eq_normalizedAbsoluteValue_ofInstances` in
[the functional-equation reduction](../../Langlands/AllField/Representation/RankinSelberg/LocalFieldUnequalRankFunctionalEquationReduction.md).
A p-adic specialization needs the canonical bridge, rather than new versions of
these definitions. This note defines no second bridge.

The genuinely different steps are concentrated in a few arguments:

- Compact contraction uses the norm `T.normalizedAbs` itself, with its topology
  identified by valuation balls; compact Iwasawa support uses a scaled compact
  integer ring. Both avoid an extension-degree power of the spectral norm.
- Small nonzero elements and nontrivial punctured neighbourhoods come from the
  nontrivial valuation, without an algebra map from `Padic p`.
- Intersection-Levi characters use diagonal scaling by `s ≠ 0,1`, rather than by
  `2`. This includes residue and field characteristic two.
- The full principal-unit power-cofinality statement has no unrestricted
  positive-characteristic analogue. The L descent needs only rank-one
  high-ramification vanishing, where every twisting exponent is `1`; the
  conductor definition suffices there. This does not assert the full
  high-ramification proposition by that argument.

The last two changes and the new punctured-neighbourhood arguments are recorded
in the [general gamma proof](../../Langlands/Representation/RankinSelberg/LocalFieldPrincipalSeriesGammaMultiplicativityProof.md).
The rank-one repair, the two changed input assemblies and the closed L descent
are recorded in the [general L proof](../../Langlands/Representation/RankinSelberg/LocalFieldPrincipalSeriesLFactorMultiplicativityProof.md)
and its [rank-one ramification proof](../../Langlands/AllField/Representation/RankinSelberg/WhittakerTypeHighlyRamifiedRankOneProof.md).
The final general L multiplicativity theorem keeps its full block scope.

## Module inventory

Every name below is a complete Lean module name. `FE`, `γ`, `L` identify membership
in the three old import closures. Each source link opens the audited Lean file;
the paired Markdown records its original provenance. A row describing a change
without naming an implemented general module is an interface/argument requirement,
not a claim that a new proof of that whole source module has been published.
Only the declarations used by the general core need to be carried over.

### The eight foundation modules

These mix general valuation constructions with the finite-Padic-extension infrastructure. Their general core API is `LocalFieldData` and `AllField.LocalField.Foundation`; the base-extension comparison clauses remain p-adic specializations.

| Module | Closures | Source use and general argument or interface change | Source |
| --- | --- | --- | --- |
| `Langlands.LocalField.Canonical` | FE, γ, L | Constructs the old canonical norm, valuation, local-field and module-topology instances from a finite Padic extension. A general field starts with its supplied instances; these p-adic constructors remain specialization infrastructure. | [Lean](../../Langlands/LocalField/Canonical.lean) |
| `Langlands.LocalField.CanonicalProof` | FE, γ, L | Proves spectral norm extension to Padic p, the norm of p and module-topology comparisons. No such base-field comparisons are required by the general JPSS interface; use supplied local-field structure. | [Lean](../../Langlands/LocalField/CanonicalProof.lean) |
| `Langlands.LocalField.CanonicalStatement` | FE, γ, L | Packages the preceding canonical Padic norm/topology and base-extension comparisons. Keep the specialization package; the general interface takes a local-field topology and valuation directly. | [Lean](../../Langlands/LocalField/CanonicalStatement.lean) |
| `Langlands.LocalField.Definitions` | FE, γ, L | The finite extension of Padic p and its spectral/module topology define the old carrier API. Reuse LocalFieldData for a supplied nonarchimedean local field; retain PadicField only for specialization. | [Lean](../../Langlands/LocalField/Definitions.lean) |
| `Langlands.LocalField.Normalization.Continuity` | FE, γ, L | Rewrites normalizedAbs as a power of the canonical norm. General continuity follows from the valuation-ball basis in AllField.LocalField.Foundation, without an extension-degree exponent. | [Lean](../../Langlands/LocalField/Normalization/Continuity.lean) |
| `Langlands.LocalField.Normalization.Definitions` | FE, γ, L | Contains base integer algebra, residue characteristic/degree over ZMod p and ord(p)-based ramification index, alongside generic valuation constructions. Reuse LocalFieldData for the latter; do not posit a Padic base or ord(p) in equal characteristic. | [Lean](../../Langlands/LocalField/Normalization/Definitions.lean) |
| `Langlands.LocalField.Normalization.Proof` | FE, γ, L | Uses p-adic integral closure, e*f = extension degree, uniqueness of the spectral norm and equality with a norm power to derive normalization/topology. The general core instead uses normalizedAbs directly through the discrete value group, residue cardinality and valuation-ball basis in AllField.LocalField.Foundation. | [Lean](../../Langlands/LocalField/Normalization/Proof.lean) |
| `Langlands.LocalField.Normalization.Statement` | FE, γ, L | Packages generic valuation laws together with p-adic residue-degree, ramification and spectral-norm comparisons. General statements retain the former through LocalFieldData/Foundation; base-extension clauses are specialization data. | [Lean](../../Langlands/LocalField/Normalization/Statement.lean) |

### The twelve modules needing a different argument

These twelve direct-hit modules include the characteristic-sensitive statements and assemblies. Each row identifies the replacement argument, or the auxiliary conclusion that must be avoided.

| Module | Closures | Source use and general argument or interface change | Source |
| --- | --- | --- | --- |
| `Langlands.Group.GL.BlockContractionProof` | FE, γ, L | Construct a norm from T.normalizedAbs, identify its topology by normalized-absolute-value balls, and bound compact matrices in this norm. The contraction bound then has no Padic extension-degree power. Implemented in the same-suffix AllField module. | [Lean](../../Langlands/Group/GL/BlockContractionProof.lean) |
| `Langlands.Group.GL.MirabolicTailConullProof` | γ, L | Replace the continuous map Padic p → F used to find small nonzero elements by a valuation ball and a nontrivial valuation. Implemented by AllField.GeneralLinear.padic_exists_ne_zero_mem_nhds_zero. | [Lean](../../Langlands/Group/GL/MirabolicTailConullProof.lean) |
| `Langlands.Group.GL.NormalizedCharacter` | FE, γ, L | Replace canonical-norm-power continuity by continuous_normalizedAbs; the determinant-character kernel is open because the valuation-unit sphere is open. Canonical-norm comparison lemmas are unnecessary. Implemented in AllField.Group.GL.NormalizedCharacter. | [Lean](../../Langlands/Group/GL/NormalizedCharacter.lean) |
| `Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof` | FE, γ, L | Replace the finite-dimensional Padic proof of properness/countability/regularity by the general local-field facts in LocalFieldData/Foundation. The residue-normalized Haar-scaling argument is unchanged in the AllField module. | [Lean](../../Langlands/HarmonicAnalysis/PadicScalarHaarScalingProof.lean) |
| `Langlands.HarmonicAnalysis.PrincipalUnitPowerCofinalityProof` | L | The Hensel step explicitly needs (m : F) ≠ 0, supplied by CharZero. The unrestricted positive-power conclusion has no all-characteristic port. The general L proof instead needs only first powers, using the conductor definition directly; see the relay table. | [Lean](../../Langlands/HarmonicAnalysis/PrincipalUnitPowerCofinalityProof.lean) |
| `Langlands.Representation.Geometric.IntersectionLeviDiagonalCharacterProof` | γ, L | Replace diagonal scaling by 2 (requiring 2 ≠ 0) by scaling with s ≠ 0,1, and use b = c/(s-1). Nontrivial valuation supplies s even in characteristic two. Implemented in AllField.Representation.Geometric.IntersectionLeviDiagonalCharacter. | [Lean](../../Langlands/Representation/Geometric/IntersectionLeviDiagonalCharacterProof.lean) |
| `Langlands.Representation.Geometric.IntersectionLeviDiagonalCharacterStatement` | γ, L | Replace CharZero F by existence of s ≠ 0,1; this is supplied for every nonarchimedean local field. The general theorem is AllField.Geometric.intersectionLeviDiagonalCharacter. | [Lean](../../Langlands/Representation/Geometric/IntersectionLeviDiagonalCharacterStatement.lean) |
| `Langlands.Representation.Geometric.IntersectionLeviModulusBalance` | γ, L | Calls the characteristic-zero diagonal-character theorem. Apply the general theorem of the preceding two rows using a nontrivial valuation. Implemented in its same-suffix AllField module. | [Lean](../../Langlands/Representation/Geometric/IntersectionLeviModulusBalance.lean) |
| `Langlands.Representation.Geometric.PadicCorrectionCancellationProof` | γ, L | Its p-adic conditional assembly also installs CharZero for the diagonal-character premise. A general version needs that premise with s ≠ 0,1 instead. The general JPSS route uses the general intersection-Levi balance; this row does not assert a published same-suffix port. | [Lean](../../Langlands/Representation/Geometric/PadicCorrectionCancellationProof.lean) |
| `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonScalarHaar` | γ, L | Replace the canonical NormedField punctured-neighbourhood argument by Langlands.LocalField.nhdsNE_zero_neBot. Implemented in the same-suffix AllField module. | [Lean](../../Langlands/Representation/RankinSelberg/RankOneMatrixFunctionalEquationComparisonScalarHaar.lean) |
| `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSingularNull` | γ, L | Supply the punctured-neighbourhood nontriviality from Langlands.LocalField.nhdsNE_zero_neBot rather than F.canonicalNormedField. Implemented in the same-suffix AllField module. | [Lean](../../Langlands/Representation/RankinSelberg/RankOneMatrixFunctionalEquationComparisonSingularNull.lean) |
| `Langlands.Representation.RankinSelberg.UnequalRankIwasawaSupportProof` | FE, γ, L | Replace a canonical-norm closed ball and its extension-degree bound by a scaled compact ring of integers: choose m with B < q^m and put z in pi^(-m) O. Implemented in the same-suffix AllField module. | [Lean](../../Langlands/Representation/RankinSelberg/UnequalRankIwasawaSupportProof.lean) |

### The forty-one canonical-structure and transport modules

These uses select a canonical topology or transport a supplied topology to it. Their general versions must use one supplied local-field topology consistently. Installing a canonical norm to obtain topological instances is distinguished from using a spectral-norm identity in an estimate. Some rows are only specialization examples.

| Module | Closures | Source use and general argument or interface change | Source |
| --- | --- | --- | --- |
| `Langlands.Correspondence.LocalConventions` | FE, γ, L | Collects canonical topology, valuation, local-field, T2, total-disconnectedness and Borel instances. For the general interface use the supplied instances; the Layer 0 bridge supplies these together for Padic specialization. No new analytic estimate. | [Lean](../../Langlands/Correspondence/LocalConventions.lean) |
| `Langlands.HarmonicAnalysis.Distribution.GeneralLinear` | FE, γ, L | The only canonical-norm use is a Padic specialization example. The actual transpose homeomorphism and distribution lemmas are field/topology-generic and can be imported unchanged. | [Lean](../../Langlands/HarmonicAnalysis/Distribution/GeneralLinear.lean) |
| `Langlands.HarmonicAnalysis.Distribution.TransposeInvariantProof` | FE, γ, L | The spectral norm and Padic properness only install topological instances before applying the generic localization/matrix inputs. Supply local compactness, nonarchimedean topology and separation from the general local-field data; the named localization inputs remain explicit. | [Lean](../../Langlands/HarmonicAnalysis/Distribution/TransposeInvariantProof.lean) |
| `Langlands.HarmonicAnalysis.Distribution.TransposeInvariantStatement` | FE, γ, L | Its canonical norm supplies the topology in the binder. State the same distribution predicate for the supplied local-field topology; no numerical norm identity is asserted. | [Lean](../../Langlands/HarmonicAnalysis/Distribution/TransposeInvariantStatement.lean) |
| `Langlands.Representation.Classification.ConstituentCompatibility` | γ, L | The canonical norm only supplies topology for the contragredient head/socle predicate. A general formulation uses the supplied topology. This audit adds no classification statement. | [Lean](../../Langlands/Representation/Classification/ConstituentCompatibility.lean) |
| `Langlands.Representation.RankinSelberg.EqualRankTrilinearPrerequisites` | γ, L | Remove canonical-module-topology rewrites when invoking finite length: use the finite-length input at the same supplied T. Implemented in the AllField module. | [Lean](../../Langlands/Representation/RankinSelberg/EqualRankTrilinearPrerequisites.lean) |
| `Langlands.Representation.RankinSelberg.InducedTailIntermediateCoefficientAdapters` | γ, L | Its cutoff wrapper installs T.valuativeExtension and T.moduleTopology before invoking the cutoff theorem. Generalize that theorem and retain only the supplied local-field instances; these base-Padic instances add no cutoff estimate. | [Lean](../../Langlands/Representation/RankinSelberg/InducedTailIntermediateCoefficientAdapters.lean) |
| `Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement` | FE, γ, L | Drops unused T.valuativeExtension and T.moduleTopology from the statement binder. Its compact/open orbit proposition is otherwise over the supplied topology. Implemented in the AllField statement. | [Lean](../../Langlands/Representation/RankinSelberg/LastRowCompactOrbitStatement.lean) |
| `Langlands.Representation.RankinSelberg.ModelAsymptoticProof` | FE, γ, L | State the asymptotic hypothesis for the supplied T and apply it there, instead of identifying T with the canonical Padic topology. Implemented in the AllField module. | [Lean](../../Langlands/Representation/RankinSelberg/ModelAsymptoticProof.lean) |
| `Langlands.Representation.RankinSelberg.UnequalRankCompactPairingMultiplicity` | FE, γ, L | Apply the published Langlands.Whittaker.localFieldMultiplicityOne at the supplied T, instead of transporting to the Padic canonical norm. Implemented in the AllField module; no new multiplicity-one proof is needed here. | [Lean](../../Langlands/Representation/RankinSelberg/UnequalRankCompactPairingMultiplicity.lean) |
| `Langlands.Representation.RankinSelberg.UnequalRankSpecializationInputs` | FE, γ, L | Use general admissible finite length at the supplied topology rather than rewriting to the canonical module topology. Implemented in the AllField module. | [Lean](../../Langlands/Representation/RankinSelberg/UnequalRankSpecializationInputs.lean) |
| `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof` | FE, γ, L | Its main cutoff assembly installs unused base-Padic valuation-extension/module-topology instances. Use the supplied local-field instances in a full general wrapper. The published AllField module ports only its lattice-conductor helper; no full main-theorem port is claimed here. | [Lean](../../Langlands/Representation/RankinSelberg/ZeroRowLastRowCutoffProof.lean) |
| `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement` | FE, γ, L | Drops the same unused base-Padic instances from the binder. Implemented in the AllField statement; this is not itself a proof of the cutoff theorem. | [Lean](../../Langlands/Representation/RankinSelberg/ZeroRowLastRowCutoffStatement.lean) |
| `Langlands.Representation.Smooth.Contragredient.GelfandKazhdanAssembly` | FE, γ, L | Uses the canonical norm only to install the field/group topology. Apply the general versions of its explicit separation/transpose inputs with the local-field Haar/group instances; the character-transport argument adds no Padic calculation. | [Lean](../../Langlands/Representation/Smooth/Contragredient/GelfandKazhdanAssembly.lean) |
| `Langlands.Representation.Smooth.Contragredient.GelfandKazhdanStatement` | FE, γ, L | Replace the topology installed by canonicalNormedField with the supplied topology in the contragredient proposition. | [Lean](../../Langlands/Representation/Smooth/Contragredient/GelfandKazhdanStatement.lean) |
| `Langlands.Representation.Whittaker.BruhatCellFactorizationProof` | FE, γ, L | Replace spectral-norm/finite-Padic properness instances with local compactness and total disconnectedness from the supplied local field and its unipotent subgroups. The character-average factorization is generic. | [Lean](../../Langlands/Representation/Whittaker/BruhatCellFactorizationProof.lean) |
| `Langlands.Representation.Whittaker.BruhatCellFactorizationStatement` | FE, γ, L | Use the supplied local-field topology for the cell, torus and unipotent groups in the factorization proposition. | [Lean](../../Langlands/Representation/Whittaker/BruhatCellFactorizationStatement.lean) |
| `Langlands.Representation.Whittaker.BruhatCellInvarianceProof` | FE, γ, L | Use the general factorization and compatible-monomial inputs at the supplied topology; the rest of the proof is field/topology-generic. | [Lean](../../Langlands/Representation/Whittaker/BruhatCellInvarianceProof.lean) |
| `Langlands.Representation.Whittaker.BruhatCellInvarianceStatement` | FE, γ, L | Use the supplied topology in the distribution-invariance proposition. | [Lean](../../Langlands/Representation/Whittaker/BruhatCellInvarianceStatement.lean) |
| `Langlands.Representation.Whittaker.BruhatCellVanishingProof` | FE, γ, L | Use the supplied topology and the corresponding Haar/orbital inputs in the generic vanishing argument. | [Lean](../../Langlands/Representation/Whittaker/BruhatCellVanishingProof.lean) |
| `Langlands.Representation.Whittaker.BruhatCellVanishingStatement` | FE, γ, L | Use the supplied topology in the vanishing proposition. | [Lean](../../Langlands/Representation/Whittaker/BruhatCellVanishingStatement.lean) |
| `Langlands.Representation.Whittaker.BruhatCompatibleSupportProof` | FE, γ, L | Supply the unipotent topological-group, T2, locally compact and nonarchimedean instances from the supplied local field, rather than canonical structures. | [Lean](../../Langlands/Representation/Whittaker/BruhatCompatibleSupportProof.lean) |
| `Langlands.Representation.Whittaker.BruhatCompatibleSupportStatement` | FE, γ, L | Use the supplied topology and Borel structures in the support proposition. | [Lean](../../Langlands/Representation/Whittaker/BruhatCompatibleSupportStatement.lean) |
| `Langlands.Representation.Whittaker.BruhatFiberCharacterCovarianceProof` | FE, γ, L | Use the supplied topology and Haar hypotheses; the matrix/character calculation is generic. | [Lean](../../Langlands/Representation/Whittaker/BruhatFiberCharacterCovarianceProof.lean) |
| `Langlands.Representation.Whittaker.BruhatFiberCharacterCovarianceStatement` | FE, γ, L | Use the supplied topology and Borel structures in the covariance proposition. | [Lean](../../Langlands/Representation/Whittaker/BruhatFiberCharacterCovarianceStatement.lean) |
| `Langlands.Representation.Whittaker.BruhatHaarMeasureProof` | FE, γ, L | Supply local-field group instances and Borel structures instead of canonical normed instances; the closed-subgroup/Haar argument is generic. | [Lean](../../Langlands/Representation/Whittaker/BruhatHaarMeasureProof.lean) |
| `Langlands.Representation.Whittaker.BruhatHaarMeasureStatement` | FE, γ, L | Use the supplied local-field topology for the Haar proposition. | [Lean](../../Langlands/Representation/Whittaker/BruhatHaarMeasureStatement.lean) |
| `Langlands.Representation.Whittaker.BruhatOrbitalIntegrationProof` | FE, γ, L | Supply compact open subgroups from the general local-field topology instead of canonicalGeneralLinearCompactOpen. The coordinate/orbital integration argument is generic. | [Lean](../../Langlands/Representation/Whittaker/BruhatOrbitalIntegrationProof.lean) |
| `Langlands.Representation.Whittaker.BruhatOrbitalIntegrationStatement` | FE, γ, L | Use the supplied topology and Borel Haar measure in the orbital-integration proposition. | [Lean](../../Langlands/Representation/Whittaker/BruhatOrbitalIntegrationStatement.lean) |
| `Langlands.Representation.Whittaker.CompatibleMonomialFixedProof` | FE, γ, L | Its canonical-norm wrapper applies the preceding generic weylTransposeHomeomorph_monomial_eq_of_compatible; reuse that generic theorem. | [Lean](../../Langlands/Representation/Whittaker/CompatibleMonomialFixedProof.lean) |
| `Langlands.Representation.Whittaker.CompatibleMonomialFixedStatement` | FE, γ, L | Use the supplied topology for the additive-character type in the monomial proposition. | [Lean](../../Langlands/Representation/Whittaker/CompatibleMonomialFixedStatement.lean) |
| `Langlands.Representation.Whittaker.CompatibleTorus` | FE, γ, L | Only a Padic specialization example uses canonicalNormedField; the compatible-torus closedness theorem is already field/topology-generic. | [Lean](../../Langlands/Representation/Whittaker/CompatibleTorus.lean) |
| `Langlands.Representation.Whittaker.Distribution` | FE, γ, L | Only a Padic specialization example uses canonicalNormedField; the Weyl-transpose homeomorphism and distribution operations are already generic. | [Lean](../../Langlands/Representation/Whittaker/Distribution.lean) |
| `Langlands.Representation.Whittaker.DistributionInvarianceProof` | FE, γ, L | The spectral norm is used only to install an ultrametric/total-disconnected topology. Supply total disconnectedness and local compactness from the general local field; the distribution argument is unchanged. | [Lean](../../Langlands/Representation/Whittaker/DistributionInvarianceProof.lean) |
| `Langlands.Representation.Whittaker.DistributionInvarianceStatement` | FE, γ, L | Use the supplied topology in the Whittaker distribution-invariance proposition. | [Lean](../../Langlands/Representation/Whittaker/DistributionInvarianceStatement.lean) |
| `Langlands.Representation.Whittaker.MirabolicFunctionalMultiplicityProof` | FE, γ, L | Run the canonical-core argument for the supplied T and its minimality input, rather than transporting T by module-topology uniqueness. The AllField proof applies the field-generic mirabolic assembly with its inputs at T. | [Lean](../../Langlands/Representation/Whittaker/MirabolicFunctionalMultiplicityProof.lean) |
| `Langlands.Representation.Whittaker.ModelKirillovProof` | FE, γ, L | Apply the general Kirillov hypothesis at T itself instead of rewriting T to canonicalTopologicalData. Implemented in the AllField module. | [Lean](../../Langlands/Representation/Whittaker/ModelKirillovProof.lean) |
| `Langlands.Representation.Whittaker.MultiplicityOneProof` | FE, γ, L | The canonical norm/valuation install instances for an otherwise topological representation argument. The core consumer can use the published localFieldMultiplicityOne directly, as its AllField compact-pairing proof does. | [Lean](../../Langlands/Representation/Whittaker/MultiplicityOneProof.lean) |
| `Langlands.Representation.Whittaker.MultiplicityOneStatement` | FE, γ, L | Use the supplied topology in the functional-line proposition. The Library already has a general local-field proof. | [Lean](../../Langlands/Representation/Whittaker/MultiplicityOneStatement.lean) |
| `Langlands.Representation.Whittaker.ParabolicInducedCoinvariantFinitenessProof` | FE, γ, L | Run the finite-coinvariant core at T and its half modulus. Canonical-topology/half-modulus transport is unnecessary. Implemented in the AllField module. | [Lean](../../Langlands/Representation/Whittaker/ParabolicInducedCoinvariantFinitenessProof.lean) |
| `Langlands.Representation.Whittaker.PrerequisitesStatement` | FE, γ, L | Use the supplied topology in the Whittaker prerequisite proposition. | [Lean](../../Langlands/Representation/Whittaker/PrerequisitesStatement.lean) |

### The twelve ancillary arithmetic imports

These are present because the audit follows whole-module imports. Their standalone arithmetic generalizations are not obligations of this JPSS program. The rows identify the extra issue a full standalone port would face; generic portions of these files can already be reused. No new reciprocity, residue-exactness, number-field-completion or classification statement is proposed.

| Module | Closures | Source use and general argument or interface change | Source |
| --- | --- | --- | --- |
| `Langlands.ClassFieldTheory.Local.ClassFormation` | L | The p-adic multiplicative-formation constructor obtains perfectness from characteristic zero, and some comparison predicates use Padic-base towers/equivalences. Its standalone arbitrary-characteristic extension would need a separable-closure formulation, not the false assumption that every local field is perfect. No new class-formation argument is an input of the general JPSS core. | [Lean](../../Langlands/ClassFieldTheory/Local/ClassFormation.lean) |
| `Langlands.ClassFieldTheory.Local.Corestriction` | L | The p-adic wrapper specifies a Padic-base scalar tower; the underlying cohomological corestriction is field-generic. A general wrapper uses the actual finite field-extension tower, with no Padic base. No core port is needed. | [Lean](../../Langlands/ClassFieldTheory/Local/Corestriction.lean) |
| `Langlands.ClassFieldTheory.Local.Galois` | FE, γ, L | asPadicField re-bundles a finite extension of Padic p; other wrappers obtain CharZero. General finite Galois extensions remain ordinary fields with their needed separable/local-field data. The asPadicField constructor is not a general-field operation. | [Lean](../../Langlands/ClassFieldTheory/Local/Galois.lean) |
| `Langlands.ClassFieldTheory.Local.Invariants` | L | An arithmetic-coordinate predicate installs the canonical spectral norm, Padic properness and a Padic-base tower. A general arithmetic version would supply the local-field norm/topology and the finite-extension residue action directly. The JPSS core does not require porting this invariant-family predicate. | [Lean](../../Langlands/ClassFieldTheory/Local/Invariants.lean) |
| `Langlands.ClassFieldTheory.Local.Norms` | FE, γ, L | Uses Padic scalar towers and restriction of scalars to prove continuity/degree facts for field norms. A general version would use continuity of linear maps for the actual finite local-field extension and its field-degree identities. Generic algebraic norm statements can be reused. | [Lean](../../Langlands/ClassFieldTheory/Local/Norms.lean) |
| `Langlands.ClassFieldTheory.Local.ProfiniteReciprocityStatement` | FE, γ, L | Some compatibility clauses require a common Padic-base tower. Their general formulation would use the actual finite local-field extension tower. No reciprocity assertion is a premise of the general core. | [Lean](../../Langlands/ClassFieldTheory/Local/ProfiniteReciprocityStatement.lean) |
| `Langlands.Galois.Local.AbsoluteDefinitions` | FE, γ, L | Its first norm/topology section is already over a general local field; the algebraic-closure residue section has CharZero K and uses spectral norms in extension towers. Generalizing that section would require a characteristic-free residue/separable-closure argument. The first section is reused without a new p-adic argument. | [Lean](../../Langlands/Galois/Local/AbsoluteDefinitions.lean) |
| `Langlands.Galois.Local.AbsoluteProof` | FE, γ, L | Mixes generic spectral-norm invariance with residue exactness under CharZero and p-adic specializations. A standalone full generalization must remove the latter characteristic-zero dependencies; the JPSS core does not use residue exactness. | [Lean](../../Langlands/Galois/Local/AbsoluteProof.lean) |
| `Langlands.Galois.Local.AbsoluteStatement` | FE, γ, L | Packages the characteristic-zero residue result and PadicResidueExactness. An all-characteristic residue statement/proof is a separate arithmetic obligation, not a JPSS prerequisite. | [Lean](../../Langlands/Galois/Local/AbsoluteStatement.lean) |
| `Langlands.Galois.Local.SpectralDefinitions` | FE, γ, L | spectralNorm here is already a construction over a general complete nontrivially normed ultrametric field and its algebraic extensions. It is a lexical hit, not a Padic-specific proof; no port is required. | [Lean](../../Langlands/Galois/Local/SpectralDefinitions.lean) |
| `Langlands.Global.CompletionPadic` | L | Constructs the Padic structure of a number-field completion using a residue prime and compares norms. This is intentionally characteristic zero; it supplies no new argument for JPSS over a supplied local field. | [Lean](../../Langlands/Global/CompletionPadic.lean) |
| `Langlands.HarmonicAnalysis.CharacterTransport` | FE, γ, L | The final Padic trace wrapper uses module topology over Padic p and obtains separability from CharZero. The preceding field-generic trace pullback already takes a finite separable extension with its module topology. Reuse it where trace transport is needed; general scalar character scaling is already field-generic. | [Lean](../../Langlands/HarmonicAnalysis/CharacterTransport.lean) |

### The five unrelated complex module-topology hits

These five files use `moduleTopology ℂ` on endomorphism spaces. They are not evidence of a p-adic module-topology dependency.

| Module | Closures | Source use and general argument or interface change | Source |
| --- | --- | --- | --- |
| `Langlands.Weil.Representation.CharacterLine` | FE, γ, L | Uses moduleTopology over complex endomorphism spaces, not a module topology over Padic p. No local-field port is required. | [Lean](../../Langlands/Weil/Representation/CharacterLine.lean) |
| `Langlands.Weil.Representation.IsomorphismInvarianceProof` | FE, γ, L | Uses moduleTopology over complex endomorphism spaces, not a module topology over Padic p. No local-field port is required. | [Lean](../../Langlands/Weil/Representation/IsomorphismInvarianceProof.lean) |
| `Langlands.Weil.Representation.OperationClosureProof` | FE, γ, L | Uses moduleTopology over complex endomorphism spaces, not a module topology over Padic p. No local-field port is required. | [Lean](../../Langlands/Weil/Representation/OperationClosureProof.lean) |
| `Langlands.Weil.Representation.Operations` | FE, γ, L | Uses moduleTopology over complex endomorphism spaces, not a module topology over Padic p. No local-field port is required. | [Lean](../../Langlands/Weil/Representation/Operations.lean) |
| `Langlands.Weil.Representation.Predicates` | FE, γ, L | Uses moduleTopology over complex endomorphism spaces, not a module topology over Padic p. No local-field port is required. | [Lean](../../Langlands/Weil/Representation/Predicates.lean) |

### The seven L-factor dependency relays

These seven files have no direct nonparametric marker under the scan but occur in the L closure. Their changed dependency is essential: a mechanical change of field binders would still call the blocked power-cofinality route. The first-power restriction is on the auxiliary ramification argument, not on the final multiplicativity theorem.

| Module | Closures | Source use and general argument or interface change | Source |
| --- | --- | --- | --- |
| `Langlands.HarmonicAnalysis.PrincipalUnitPowerCofinalityStatement` | L | Its unrestricted quantifier over positive m is the statement blocked in characteristic p. No literal all-characteristic version is used; only m = 1 is needed by the rank-one L route. | [Lean](../../Langlands/HarmonicAnalysis/PrincipalUnitPowerCofinalityStatement.lean) |
| `Langlands.Representation.RankinSelberg.LFactorMultiplicativityProof` | L | Apply the general two-block theorem and induction in stages. The final general multiplicativity statement retains its full block scope; only the auxiliary ramification input was restricted. | [Lean](../../Langlands/Representation/RankinSelberg/LFactorMultiplicativityProof.lean) |
| `Langlands.Representation.RankinSelberg.TwoBlockLConditionalAssembly` | L | Weaken the high-ramification premise to the rank-one statement: the descent invokes it only for first member rankOneCharacter 1. The proof is otherwise unchanged. | [Lean](../../Langlands/Representation/RankinSelberg/TwoBlockLConditionalAssembly.lean) |
| `Langlands.Representation.RankinSelberg.TwoBlockLFactorMultiplicativityProof` | L | Close the two-block theorem with the general rank-one vanishing proof and the other general analytic inputs. Do not import the p-adic full-ramification proof as a general theorem. | [Lean](../../Langlands/Representation/RankinSelberg/TwoBlockLFactorMultiplicativityProof.lean) |
| `Langlands.Representation.RankinSelberg.TwoBlockLVerifiedInputAssembly` | L | Pass the weakened rank-one high-ramification premise to the preceding assembly. The proof is otherwise unchanged. | [Lean](../../Langlands/Representation/RankinSelberg/TwoBlockLVerifiedInputAssembly.lean) |
| `Langlands.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedProof` | L | Its conductor step uses principal-unit power cofinality for the root-coordinate exponents. The new rank-one proof has all exponents equal to 1 and uses exists_nontrivial_below_multiplicativeConductor directly. | [Lean](../../Langlands/Representation/RankinSelberg/WhittakerTypeHighlyRamifiedProof.lean) |
| `Langlands.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedStatement` | L | The general L descent replaces the full high-ramification proposition with WhittakerTypeHighlyRamifiedRankOneLVanishingStatement. This is a deliberate restriction of the auxiliary input, not a proof of the full proposition. | [Lean](../../Langlands/Representation/RankinSelberg/WhittakerTypeHighlyRamifiedStatement.lean) |

## Parametric source modules by directory

There are 948 remaining modules whose code explicitly spells `PadicField` after
excluding the 62 such modules in the tables. They require field-binder and API
replacement, including canonical topology/induction wrappers where present;
this table does not assign them 948 new mathematical arguments. Modules whose
p-adic scope is only implicit through a statement name are still in the full
import inventory, but not in this literal-token subtotal. The reproduction
script outputs each directory's complete module list.

| Directory (module prefix) | Modules |
| --- | ---: |
| `Langlands.ClassFieldTheory.Local` | 7 |
| `Langlands.Correspondence` | 5 |
| `Langlands.Group.GL` | 30 |
| `Langlands.HarmonicAnalysis` | 31 |
| `Langlands.HarmonicAnalysis.Distribution` | 2 |
| `Langlands.LocalFactor` | 2 |
| `Langlands.LocalFactor.Abelian` | 2 |
| `Langlands.LocalFactor.Harmonic` | 1 |
| `Langlands.LocalField` | 4 |
| `Langlands.Representation.Category` | 1 |
| `Langlands.Representation.Classification` | 16 |
| `Langlands.Representation.CuspidalSupport` | 63 |
| `Langlands.Representation.Derivative` | 8 |
| `Langlands.Representation.Exponents` | 3 |
| `Langlands.Representation.Filtration` | 1 |
| `Langlands.Representation.Geometric` | 27 |
| `Langlands.Representation.GodementJacquet` | 77 |
| `Langlands.Representation.Induction` | 15 |
| `Langlands.Representation.Jacquet` | 6 |
| `Langlands.Representation.Parabolic` | 43 |
| `Langlands.Representation.RankinSelberg` | 518 |
| `Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence` | 2 |
| `Langlands.Representation.Shahidi` | 6 |
| `Langlands.Representation.Smooth` | 4 |
| `Langlands.Representation.Tensor` | 3 |
| `Langlands.Representation.Unramified` | 4 |
| `Langlands.Representation.Whittaker` | 64 |
| `Langlands.Weil.Local` | 3 |
| Total | 948 |

## Provenance and reuse boundary

This is an internal audit of the pinned Library source and its paired proof
explanations. It introduces no Lean declarations and gives no independent proof. The mathematical provenance of each audited declaration remains in its
paired Markdown; the implemented general proof routes are linked above. The
names `Padic*` retained inside `Langlands.AllField` do not restrict those
declarations to characteristic zero: their field binders and local-field data
are decisive.

This audit concerns the three shared proof roots and the needed interfaces.
The appearance of Classification, Derivative and Godement–Jacquet directories
in an import closure grants no expanded scope to the deferred JPSS (9.4)/(8.4)
classification batch. Consumers should import the published general entry
theorems and reuse them once, rather than porting the same subordinate
arguments independently.

# Conrad, *Weil and Grothendieck approaches to adelic points*: coverage ledger

Author: Worker 3519 (formerly Worker 16). Parent task `886bf565-95e9-4dc6-8a9d-73284a523668`
(Task 3519), revision 1.

Source: Brian Conrad, *Weil and Grothendieck approaches to adelic points*, December 31, 2011,
21 pages. Registered literature ID `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. Page numbers are the printed
page numbers. Every status was rechecked for this revision against the Library commit below.

This ledger maps every substantive construction and assertion of Sections 1–5 to Lean
declarations of Library commit `c5b9c2cffa0ba4c2aacfbae226c0631912d2e605`. For each row it
records the declarations, the hypotheses under which the Lean statements assert the source
claim, the proof status found by searching that commit, and the responsible task for each open
item. The hypothesis column lists every hypothesis of the cited statements that restricts or
changes the source assertion, including hypotheses added by a source correction. Generality
beyond the source (arbitrary rings and constant fields, empty `S`) follows the conventions
below and is noted in rows where it matters. The column omits universe parameters and
structural data, such as algebra structures and scalar towers. All
declarations are in the namespaces `Langlands.AlgebraicGeometry.PointTopology` (paths
`Langlands/AlgebraicGeometry/PointTopology/`), `Langlands.AlgebraicGeometry.AlgebraicSpace`
(paths `.../AlgebraicSpace/`), `Langlands.AlgebraicGeometry.LangWeil` (paths `.../LangWeil/`),
`Langlands.Global` (paths `Langlands/Global/`), `Langlands.AlgebraicGeometry`,
`Langlands.AlgebraicGeometry.SchemeLimitModel`, `Langlands.AlgebraicGeometry.SchemeFiberGeometry`
or `Langlands.AlgebraicGeometry.AffineLimit` (paths `Langlands/AlgebraicGeometry/`), except
`FiniteTypeFinitenessDescent` and `FiniteTypeSurjectivityDescent`, which are in
`Langlands.Algebra.FilteredRing` (path `Langlands/Algebra/`). Names written with a further prefix
are relative to these namespaces; names beginning with `Langlands.` are absolute.

## Status vocabulary

- **proved**: a theorem whose type is the named statement is in the Library commit above; it is
  named in the row. Publication in the Library is the acceptance evidence. A proof-producing
  `def` of Prop type, published as a supporting definition, counts when its type is the named
  statement up to unfolding; the row says so.
- **construction**: a definition (with its intrinsic lemmas) in the Library.
- **open (task)**: a published statement with no Library proof, assigned to the named task.
- **staged**: a statement candidate of this task that is not in the Library commit above. Its
  candidate ID is given; staged work is neither accepted nor published.
- **not stated**: an assertion with no Lean statement in the Library and no staged candidate.
- **false as stated**: a published statement that faithfully transcribes a source assertion
  shown to be false; the row names the evidence and the task that owns the corrected statement.

Proof tasks published for this paper on 2026-11-08: Task 5245
`2fea6e55-454f-4d2d-adba-f232b7d0523d`, Task 5246 `4caa00a4-b244-405d-9e9d-f4c95d16a4dd` and
Task 5247 `0b1fdb32-db60-4bf2-ac39-1e7fdf1d2485` (each with a complete draft); Task 5252
`d043ee6a-19a0-4db6-b7e3-3b5b80e7b710`, Task 5253 `a4f7debd-5033-44c2-8a2a-66f37d7d36a3`,
Task 5254 `7d7f2664-87c8-4e7c-926c-c38d36f325e5`, Task 5255
`e276f80d-e140-4579-90fc-cc3dceba3c06`, Task 5256 `926b44cd-4772-49e6-bacb-9c3337206e14`,
Task 5257 `06bcaa10-0ff1-4623-a57a-bbec3213497c`, Task 5258
`a29de3ad-f8dc-4e27-9ff2-43befd56fde3`, Task 5259 `6f97fbad-98fb-4695-894f-8ef10b5d8b70` and
Task 5260 `5ded2603-5e05-4bd8-b5eb-521a27ba11f6` (no drafts); and, on 2026-11-09, Task 5275
`d8f820b8-f038-47f4-9bc3-c4bd3c618055` and Task 5276 `75272f46-694a-4c40-a93e-1dd9898df598`
(each with a complete draft), Task 5277 `185d240d-b21d-4f86-9c60-733b23e8e341` and Task 5278
`cb7be6d2-3dc1-4692-9617-64965af52cbf`, Task 5302 `de65ae3d-f0af-4d14-9249-497928863844`,
Task 5303 `93d786be-086b-42e8-8804-7d698cddace8` (no drafts; context revision 2 after the
Proposition 5.11(1) correction), Task 5304 `ac42557a-f9b5-4a5e-9ed1-6ecdc4779257` and Task 5321
`b239dfb9-a3d3-4a1c-ba58-6b89501b686d` (each with a complete draft). Worker 111 published Task 5320
`10fea308-e575-4ca0-80f1-1121cb5ee36c`, the corrected Proposition 5.11(1), under the operator
ruling recorded in its context; Task 5256 was retired on 2026-11-10 under that ruling. The
proofs of Tasks 5245, 5246, 5247, 5252 (Lemma 5.1), 5255 (Lemma 5.10), 5259, 5260
(`spaceLimitModelExistenceQuasiSeparated`), 5275, 5276, 5277 (`SpaceLimitUniquenessStatement`),
5303, 5304 and 5321, of Task 5222 `360a1cdf-4b68-402e-b087-254b03da61f6`
(`AdelicSpacePointTopologyStatement`), of Task 5320
(`henselianWeilRestrictionPointHomeomorphOfModuleTopology`), of Task 5368
`f5df3c28-7e81-45be-a29a-4abfadf5b153` (`spaceValuativeExistence`, an intermediate statement for
Corollary 5.6), of Task 5483 `383029c4-6a20-4206-b777-80fe785ebecc` (`localFieldProperPointMap`,
Corollary 5.6; the focused final proof task of Task 5216 `bc24327e-c607-4b6b-937f-69ae3b0bee57`),
of the Lang–Weil Tasks 5404 `d108969a-c371-4c06-9403-4d8d7846d52c` (`familyLangWeilZero`),
5407 `7d4fb0d2-9ff7-4183-81bc-e2904bb38c09`
(`BertiniGenericHyperplane.bertiniGenericHyperplaneStatement`), 5409
`2795fee1-d876-4010-86ed-ccd7f8e687c7` (`familyLangWeilSlicing`), 5410
`acab9a1a-0a8e-4bd8-a84b-dc3f7aed3074` (`uniformLangWeilOfFamily`), 5581
`b589cd1b-1a7b-41c8-afcf-506ab674e1e2` (`familyCurvePlaneComparison`), 5408 (`familyLangWeilCurve`),
5411 (`spaceUniformLangWeilOfFamily`), 5604 (`finiteNormalizationCover`) and 5405
(`familyPointUpperBound`), of Task 5498
`c25f29a7-c26d-447f-9fdc-dd9c92f59204` (`properSchemeBaseChange`), of Task 5357
`358c8595-c259-43c3-9e07-08aea99faf88` (`adelicSpaceProperStages`), of Task 5472
`073bf3b4-2349-40b4-b0c7-ace048377261` (`representedAtlasEffectivity`), of Task 5302
(`spaceLimitFlatnessDimensionDescent`), of Task 5257 (`adelicSpaceWeilRestriction`,
Proposition 5.14), of Task 5278 (`spaceLimitPropertyDescent`), of Task 5258
(`henselianExtensionPointEmbedding`), of Task 5586 (`properSchemeCover`), of Task 5487
(`CompleteExtensionClosedRange.completeExtensionPointClosedRange`), of Tasks 5416
(`henselianChartIntegralPointsClosed`) and 5417 (`uniformFieldPointCharts`), and of the Example 5.5
Tasks 5433 (`smoothStabilizerActionQuotient`), 5435 (`orbitStratumActionRestriction`), 5436
(`actionQuotientFiniteness`), 5437 (`locallySeparatedRationalPoints`) and 5438
(`stabilizerFibreLocalDimension`) are in the Library, and
these tasks and Task 5216 are closed. The proofs
of the operator's Tasks 5213
`9f9d8a9b-464e-4a31-b507-58561fb14b22` (`spaceLimitMorphismDescent`), 5215
`0a409da3-f564-4bb8-8773-8abec4c946f4` (`spaceLimitModelExistence`) and 5235
`480077be-fc27-4c4a-b859-04fdc4c030b0` (`spaceLimitMorphismDescentQuasiSeparated`) are also in
the Library, and these tasks are closed. Task 5257
received a context-only revision 2 on 2026-11-10 that points to the published corrected statement. The
other task IDs in the rows are carried proof tasks of the parent.

## Conventions shared by the formalization

- **Actual objects.** Points are actual morphisms: `AlgPoint R A S` is `A →ₐ[R] S`;
  `SpecPoint`, `RingPoint` and `RingPoints` are actual relative scheme or algebraic-space
  points. Adele rings are the actual number-field adeles (`NumberField.AdeleRing` and the
  Library's level rings `numberFieldAdeleLevel`) and the actual curve-place adeles
  (`CurvePlaceAdeleRing`, levels `curvePlaceAdeleLevel`). Algebraic spaces are the Library's
  fppf sheaves with representable diagonal and an étale surjective scheme atlas
  (`AlgebraicSpace`).
- **Both characteristics.** Every global statement is a conjunction of a number-field clause
  and a curve-place clause. A number-field level is indexed by a finite set of finite places;
  every infinite place is always a level factor, so an empty index set is Conrad's set of
  archimedean places. A curve-place clause quantifies over an arbitrary field `k` and a field
  `F` over `k`, usually with `FunctionField k F` (finite over `RatFunc k`). Every curve clause
  that assumes **finite `k`** (`Finite k`, the global-field case) or **perfect `k`**
  (`PerfectField k`, which includes finite `k`) says so in its row; a row without either
  allows every constant field. Conrad's convention that `S` is nonempty is imposed only where a row says
  so; elsewhere every finite `S`, including the empty set, is allowed.
- **Finite-type models.** "ft model" means a scheme over the `S`-integers whose structure
  morphism is `LocallyOfFiniteType` and `QuasiCompact`. "fp" means `LocallyOfFinitePresentation`,
  `QuasiCompact` and `QuasiSeparated`, Conrad's finitely presented. For spaces, "finite type"
  is `FiniteTypeOverRing` and finitely presented models are `IsQuasiSeparated` with an
  `LocallyOfFinitePresentation ⊓ QuasiCompact` atlas.
- **Adelic topology from models.** For a scheme `Y` over the global field, the spread
  topology on `Y(A_F)` is attached to an ft model and an explicit isomorphism of its generic
  fibre with `Y` (`numberFieldSpreadAdelePointTopology`, `curvePlaceSpreadAdelePointTopology`).
  The fixed-model topology is the final topology on points of one model with values in the
  adeles (`numberFieldFixedModelAdelePointTopology`, `curvePlaceFixedModelAdelePointTopology`).
- **Section 5 convention.** Quasi-separatedness (`IsQuasiSeparated`) is an explicit hypothesis;
  separatedness (`IsSeparated`) is kept separate from it.
- **Topology on `X(k)` for spaces.** The construction is `etaleChartTopology K X`, the final
  topology of Conrad's proof of Proposition 5.4. Henselian valued fields are nontrivially
  normed fields satisfying `IsHenselianValuedField`.

## Section 1 (p.1): introduction

Expository. Its claims (Weil adelization equals Grothendieck adelic points for finite-type
schemes and separated finite-type spaces; affine agreement of topologies; functoriality and
Weil restriction) are stated precisely in Sections 3–5 and are covered in those rows.

## Section 2 (pp.1–3): affine points over topological rings

| Source | Assertion | Lean declarations | Hypotheses and scope in Lean | Status |
| --- | --- | --- | --- | --- |
| p.1 | `A_{F,S}` open subrings, `A_F` their direct limit | `NumberFieldAdeleLevelTopologyStatement`, `NumberFieldAdeleLevelColimitStatement`, `FiniteAdeleLevelTopologyStatement`, `FiniteAdeleLevelColimitStatement`, `CurvePlaceAdeleLevelTopologyStatement`, `CurvePlaceNonemptyLevelColimitStatement`, `AdelicFixedModelAlgebraColimitStatement` | number fields: any finite set of finite places; finite adeles: any Dedekind domain with its fraction field; curves: any fields `k ⊆ F`, no function-field hypothesis; the colimit over nonempty `S` assumes a place exists | proved (`numberFieldAdeleLevelTopology`, `numberFieldAdeleLevelColimit`, `finiteAdeleLevelTopology`, `finiteAdeleLevelColimit`, `curvePlaceAdeleLevelTopology`, `curvePlaceNonemptyLevelColimit`, `adelicFixedModelAlgebraColimit`) |
| p.1 | `F ⊂ A_F`: every element of `F` is integral at almost all places | `CurvePlaceFinitePolesStatement` (number fields: Mathlib's adele ring) | function fields over a perfect `k` | proved (`curvePlaceFinitePoles`) |
| Prop 2.1 | evaluation topology on actual affine points | `AlgPoint`, its topology, `SpecPoint`, `specPointHomeomorph` (`Affine`); actual relative schemes in `AffineScheme` | any commutative ring `R`, any topologized `R`-algebra `S` | construction |
| Prop 2.1 | topology is the finite-coordinate subspace topology, independent of presentation; local compactness | `AffineCoordinateProperties` (`AffineStatements`) | `S` a topological ring; embedding for every finite generating family; closed embedding if `S` is Hausdorff; local compactness if `S` is Hausdorff and locally compact and `A` is of finite type | proved (`affineCoordinateProperties_proof`) |
| Prop 2.1 | uniqueness from the axioms | `AffineTopologyUniquenessProperty`, `AffineTopologyCharacterizationProperty` (finite-type algebras), `AffineSchemeTopologyCharacterizationProperty` (affine schemes) | `S` a topological ring; topology families on points of finite-type algebras, resp. of affine schemes locally of finite type; a family satisfies the axioms iff it is the evaluation family | proved (`affineTopologyUniqueness_proof`, `affineTopologyCharacterization_proof`, `affineSchemeTopologyCharacterization_proof`) |
| Prop 2.1 | existence: the evaluation topology satisfies the axioms | `AffineTopologyExistenceProperty`, `AffineSchemeTopologyExistenceProperty`, `AffineSchemeTopologyTransportProperty` (axioms `AffineTopologyAxioms`, `AffineSchemeTopologyAxioms`) | `S` a topological ring; finite-type algebras, resp. affine schemes locally of finite type; the transport identifies the two kinds of families | proved (`affineTopologyExistence_proof`, `affineSchemeTopologyExistence_proof`, `affineSchemeTopologyTransport_proof`) |
| Prop 2.1 | functoriality; closed immersions give embeddings, closed if `R` Hausdorff | `AffineMapProperties` (quotient part), `AffineSchemeMapProperties` | continuity for every morphism of affine schemes (no finite type); embeddings for surjections of coordinate algebras and closed immersions; closed embeddings if `S` is Hausdorff | proved (`AffineMapProofs`, `AffineSchemeMapProofs`) |
| Prop 2.1 | products | `AffineProductProperties`, `TensorProductTopologyProperty`, `SpecProductTopologyProperty` | `S` a topological ring; arbitrary `R`-algebras `A`, `B` | proved (`affineProductProperties_proof`, `tensorProductTopologyProperty_proof`, `specProductTopology_proof`) |
| Prop 2.1 | fibre products | `AffineFiberProductTopologyProperty` | `S` a topological ring; arbitrary `C`-algebras over an `R`-algebra `C` | proved (`affineFiberProductTopology_proof`) |
| Prop 2.1 | Hausdorff and local compactness | `AffineSchemeTopologicalProperties` | Hausdorff `S` gives Hausdorff points of every affine scheme; local compactness needs `S` a Hausdorff locally compact topological ring and `X` affine and locally of finite type | proved (`AffineSchemeTopologicalProofs`) |
| p.2 remark | closed embeddings force `R` Hausdorff | `AffineSchemeHausdorffCriterion` | `S` a topological ring; for families satisfying the line axiom | proved (`AffineSchemeHausdorffProof`) |
| p.2 remark | group schemes give topological groups | `AffineGroupPointProperties` | `S` a topological ring; affine group schemes locally of finite type; closed embeddings if `S` is Hausdorff; local compactness if `S` is Hausdorff and locally compact | proved (`AffineGroupProofs`) |
| Ex 2.2 | coefficient change: continuity, embeddings, closed/open embeddings, discreteness | `AffineMapProperties` (coefficient parts), `AffineSchemeCoefficientProperties` | continuity and (closed) embeddings for every affine `X`; open embeddings need topological rings and `X` locally of finite type; discreteness needs a discrete topological ring and `X` locally of finite type | proved (`AffineMapProofs`, `AffineSchemeCoefficientProofs`) |
| Ex 2.3 | `X(F)` discrete in `X(A_F)`, `X(O_{F,S})` discrete in `X(A_{F,S})` | `AdelicRationalPointsDiscreteStatement` | general form: an injective map with discrete image; affine finite-type `X`. Curves: rational points in full adeles need perfect `k`; `S`-integral points in levels allow any `k` | proved (`adelicRationalPointsDiscrete_proof`) |
| Ex 2.3 | `X(R)` open and closed in `X(L)` for a DVR | `DvrAffinePointProperties` | `R` a DVR with fraction field `K` and valuation topology; `X` affine, locally of finite type | proved (`DvrPointProofs`) |
| Ex 2.4 | finite projective module and algebra topologies | `FiniteProjectiveModuleTopologyProperties`, `FiniteProjectiveAlgebraTopologyProperties` | `R` a topological ring; `M` (resp. `S`) finite projective; the algebra part assumes `S` faithful over `R` | proved |
| Ex 2.4 | affine Weil restriction, representability, closed immersions | `WeilRestrictionRepresentabilityProperties`, `WeilRestrictionClosedImmersionProperties` | `A → B` finite projective; `X` affine, locally of finite type over `B` | proved |
| Ex 2.4 | Weil-restriction point homeomorphism `X'(R') = Res(X')(R)` | `weilRestrictionAlgPointHomeomorph`, `affineWeilRestrictionPointHomeomorph` (`AffineWeilRestriction`) | `A → B` finite projective; `A`, `B` topological rings with `B` carrying the `A`-module topology; finite-type coordinate algebra | proved inside the construction module |

Source correction, Example 2.2: Conrad writes "if `R'` is closed (resp. open) in `R`" for a map
`R → R'`; the closed or open subring is the source. `AffineMapStatements.md` states the
corrected orientation and the statements use it.

## Section 3 (pp.3–9): schemes and Weil's construction

| Source | Assertion | Lean declarations | Hypotheses and scope in Lean | Status |
| --- | --- | --- | --- | --- |
| pp.3–4 | basic opens need not give open embeddings; `A^×` not open, inversion not continuous in the adeles | `AdelicUnitLocusStatement`, `AdelicPunctureEmbeddingStatement` | unit locus: curves need finite `k`; puncture embedding: any `k` | proved (`adelicUnitLocus`, `adelicPunctureEmbedding`) |
| pp.3–4 | general criteria: `U(R)` is the unit locus of `f`; openness for all basic opens iff `R^×` open; embeddings iff `R^×` has the subspace topology; these are the only obstacles to open embeddings | `AffineBasicOpenPointCriteria` | `S` any topological ring over any `R`; algebra points with the evaluation topology; basic opens `Spec A_f → Spec A` of finite-type `A` | proved (`affineBasicOpenPointCriteria`) |
| Prop 3.1 | topology on schemes over a local ring with open units and continuous inversion: existence | `SchemePointTopologyExistenceProperty` (`schemePointTopology`) | value ring `S` a local topological ring with `IsOpenUnits S` (units open with continuous inversion); arbitrary base ring `R`; the axioms concern schemes locally of finite type over `Spec R` | proved (`SchemeTopologyExistenceProofs`) |
| Prop 3.1 | uniqueness | `SchemePointTopologyUniquenessProperty` | as above: any family of topologies on points of schemes locally of finite type satisfying the axioms is `schemePointTopology` | proved (`SchemeTopologyUniquenessProofs`) |
| Prop 3.1, proof | an open cover `{U_i}` of `X` gives `X(R) = ∪ U_i(R)` for local `R`; this fails for non-local `R` in general | `exists_openPointMap_of_cover`, `exists_affineOpenPoint` (`SchemePoints`); failure: `AdelicAffineCoverCounterexampleStatement` (row Ex 4.1) | coverage: `S` local, any open cover of any relative scheme; failure: value ring the adeles (not local), the cover `D(t)`, `D(1-t)` of the affine line, curves need finite `k` | proved (inside the construction module; `adelicAffineCoverCounterexample`) |
| Prop 3.1 | open immersions, functoriality | `SchemeOpenPointProperties` | `S` local with continuous multiplication and `IsOpenUnits S`; every relative scheme, no finite type | proved |
| Prop 3.1 | closed immersions | `SchemePointClosedImmersionProperties` | as above; embeddings, and closed embeddings if `S` is Hausdorff | proved |
| Prop 3.1 | fibre products | `SchemePointPullbackProperty` | `S` a local topological ring with `IsOpenUnits S`; every pullback, no separatedness | proved |
| Prop 3.1 | separated + Hausdorff `R` gives Hausdorff | `SchemePointHausdorffProperty` | `S` a local topological ring with `IsOpenUnits S`, Hausdorff; `X` separated | proved |
| Prop 3.1 | locally compact Hausdorff `R` gives local compactness | `SchemePointLocalCompactnessProperty` | `S` a local topological ring with `IsOpenUnits S`, Hausdorff and locally compact; `X` locally of finite type | proved |
| Prop 3.1 (supplement) | coefficient change on nonaffine schemes | `SchemeCoefficientProperties` | continuity for every scheme and continuous `f : S → T`; open maps (not open embeddings) for `X` locally of finite type and an open embedding `f` of local topological rings, with `IsOpenUnits T` | proved |
| Prop 3.1 (supplement) | injectivity of coefficient change | `SchemeSeparatedCoefficientInjectivityProperty` | `S` reduced, `X` separated, `f` injective | proved |
| Prop 3.1 (supplement) | base change of the scheme | `SchemeBaseChangeTopologyProperty`, `AffineBaseChangeTopologyStatement` | scheme form: value ring `A` a local topological ring with `IsOpenUnits A`, over `C → D → A`, every scheme over `C`; affine form: `A` any topological ring, `X` affine | proved (`affineBaseChangeTopology` for the affine form) |
| Prop 3.1 (supplement); p.9 | countable base | `PointSecondCountabilityStatement` | `S` a second-countable topological ring; finite-type algebras and affine schemes locally of finite type; for nonaffine `X`, `X` locally of finite type and quasi-compact, and `S` local with `IsOpenUnits S`; no claim for schemes only locally of finite type (an uncountable disjoint union of points has uncountable discrete point sets) | proved |
| Rem 3.2 | local compactness of `X(k)` for locally finite type `X` over a local field, and of `X(O)` over a compact DVR | `SchemePointLocalCompactnessProperty`; local factors have open units: `AdelicLocalFactorUnitsStatement` | `X` locally of finite type; `S` local, Hausdorff, locally compact, `IsOpenUnits S` | proved |
| Cor 3.7, proof (p.9) | compactness of `X(R)` for a finite type scheme over a compact DVR | `CompactValueRingPointProperties` | `S` a compact Hausdorff topological ring; affine `X` locally of finite type, or local `S` and `X` locally of finite type and quasi-compact | proved (`compactValueRingPointProperties_proof`) |
| Rem 3.3 | `Z(R) ∪ U(R)` need not cover `X(R)`; field coverage | `AffineLineStratificationProperties`, `ConradRemark33Correction` | any `R`, `S`; corrected local-Artinian sentence (below) | proved (`conradRemark33Correction`) |
| p.5 | finitely presented schemes | Mathlib `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated` | definitions | Mathlib |
| p.5 | the adele ring `A_F` is not noetherian | `AdeleRingNotNoetherianStatement` | ring structure only; number fields: `Adeles K`; curves: `CurvePlaceAdeleRing k F` for any constant field `k` | proved (`adeleRingNotNoetherian`) |
| Thm 3.4(1) | descent of finitely presented models; Hom colimit bijection | `SchemeFilteredModelExistence`, `InitialRingModelHomColimitComparison`, `InitialRingModelMorphismDescent`, `ModelHomColimitComparison`, `ModelMorphismDescent`, `SpectrumModelHomColimitComparison` | filtered colimits of rings, or cofiltered limits of affine schemes; models exist for fp schemes; injectivity needs a quasi-compact source and a target locally of finite type; surjectivity and bijectivity need a quasi-compact quasi-separated source and a target locally of finite presentation | proved |
| Thm 3.4(2) | closed immersion, separated, proper, smooth, affine, flat, open immersion, finite, fibres nonempty geometrically connected of pure dimension `d` | `FinitePresentationInitialRingClosedImmersionDescent`, `FinitePresentationInitialRingSeparatednessDescent`, `FinitePresentationInitialRingProperDescent`, `FinitePresentationInitialRingRelativeSmoothFlatDescent`, `FinitePresentationInitialRingAffinenessDescent`, `FinitePresentationInitialRingOpenImmersionDescent`, `FinitePresentationInitialRingFiniteDescent`, `FinitePresentationInitialRingFiberGeometryDescent` (conjuncts of `RingSystemClosedImmersionDescent`, `RingSystemSeparatednessDescent`, `ProperDescent`, `RingSystemRelativeSmoothFlatDescent`, `RingSystemAffinenessDescent`, `RingSystemOpenImmersionDescent`, `RingSystemFiniteDescent`) | Conrad's setting: filtered colimit of rings, source and target fp over the initial ring | proved |
| Thm 3.4(2), variants | the same properties under hypotheses on the map | the `Spectrum…` (filtered colimits of `R`-algebras) and `InitialRing…` conjuncts of the `RingSystem…` statements and of `ProperDescent`; over an affine base with a cofiltered limit of affine schemes: `RelativeClosedImmersionDescent`, `RelativeSeparatednessDescent`, `RelativeProperDescent`, `RelativeSmoothDescent`, `RelativeFlatDescent`, `RelativeSmoothFlatDescent`, `RelativeAffinenessDescent`, `RelativeOpenImmersionDescent`, `RelativeFiniteDescent` | closed immersion, finite: map locally of finite type, quasi-compact, quasi-separated, target quasi-compact; affine: map quasi-compact, quasi-separated, target quasi-compact; separated: map quasi-compact, quasi-separated, source quasi-compact; open immersion: `Spectrum…`/`InitialRing…` forms, source locally of finite presentation and quasi-compact, target locally of finite presentation and quasi-separated; `RelativeOpenImmersionDescent`, source and target fp; smooth, flat, proper: map locally of finite presentation, quasi-compact, quasi-separated, target quasi-compact; `ProperDescent` also gives fp proper models of fp proper schemes | proved |
| Thm 3.4(1)–(2), models with properties | fp models of fp schemes with a property, and descent of the property for a given model | `SchemeFilteredSmoothModelExistence`, `SchemeFilteredFlatModelExistence`, `SchemeFilteredSmoothFlatModelExistence`, `InitialRingModelSmoothDescent`, `InitialRingModelFlatDescent`, `InitialRingModelSmoothFlatDescent` | filtered colimits of rings; the scheme over the colimit, resp. the model, is fp | proved |
| Thm 3.4(2), proof ingredients | finiteness and surjectivity of ring maps, closed immersions and finite maps of affine schemes, descend along filtered colimits | `FiniteTypeFinitenessDescent`, `FiniteTypeSurjectivityDescent`, `AffineDiagramClosedImmersionDescent`, `AffineDiagramFiniteDescent` | a cocartesian (resp. cartesian) system of maps that is of finite type at the initial stage | proved |
| Thm 3.4(3) | eventual uniqueness of models | clause 3 of `InitialRingModelMorphismDescent` (descent of a prescribed isomorphism) with clause 2 (eventual equality) | both models fp; clause 2 needs a quasi-compact source and a target locally of finite type | proved |
| Rem 3.5, (3.5.1) | map from Weil's limit to `X(A_F)`; bijectivity; final topology | `FilteredRingPointComparison`, `AdelicFixedModelPointComparisonStatement` | injectivity for `X` locally of finite type; bijectivity, and homeomorphism of the colimit and final topologies, for `X` locally of finite presentation; curves: any `k ⊆ F` | proved (`filteredRingPointComparison`, `adelicFixedModelPointComparison`) |
| Rem 3.5 | every finite-type `F`-scheme is the generic fibre of a finite-type scheme over some `O_{F,S}`; `O_{F,S}` is noetherian | `AdelicSpreadExistenceStatement`, `AdelicSIntegersNoetherianStatement` | spread existence: `Y` locally of finite type and quasi-compact over `F`, a model over the integers outside some `T ⊇ S`, curves need perfect `k`; noetherian (and of dimension at most one): any finite `S`, curves any `k` with a function field | proved (`adelicSpreadExistence`, `adelicSIntegersNoetherian`) |
| (3.5.1), topology | the limit topology on Weil's adelization and its properties | `AdelicFixedModelFiniteTypeStatement`, `FilteredRingPointTopologicalComparison` | ft model: points descend to stages, bijection, homeomorphism of colimit and final topologies; general filtered colimits of `R`-algebras, `X` locally of finite presentation, arbitrary topologies on the stage point sets: the colimit and final topologies agree; if every transition map on points is continuous and open, then the stage maps are open, the colimit is locally compact if every stage is, it has a countable base if countably many second-countable stages cover all points, and, if moreover all transition maps are injective, the stage maps are open embeddings and the colimit is Hausdorff if every stage is | proved (`adelicFixedModelFiniteType`, `filteredRingPointTopologicalComparison`) |
| (3.5.1) | independence of initial `S` and model | `AdelicFixedModelInitialSetTopologyStatement`, `AdelicSpreadTopologyIndependenceStatement` | ft models; model independence for curves needs perfect `k` | proved |
| Thm 3.6, (3.6.1) | `X_S(A_{F,S}) = ∏_{v∈S} X_v(F_v) × ∏_{v∉S} X_{S,v}(O_v)` bijection; product topology, affine agreement | `LocalProductPointComparisonStatement`, `AdelicLevelModelComparisonStatement`, `AdelicFiniteTypeLevelModelComparisonStatement`, `AdelicLevelModelTopologyStatement` | injective for quasi-separated `X`, or `X` locally of finite type over the `S`-integers; surjective for affine `X`, or quasi-compact `X` with local factors; the map is a homeomorphism onto the product topology for affine `X`, for quasi-compact quasi-separated `X`, and for ft `X` | proved |
| Thm 3.6 | transition maps open continuous, injective for separated `X_S` | `AdelicLevelModelTransitionTopologyStatement`, `AdelicFixedModelTransitionTopologyStatement`, `DvrSchemePointProperties` | ft models: continuous open maps, open embeddings if the arithmetic model is separated; DVR: `X` locally of finite type, `X(R) → X_K(K)` continuous open, open embedding for separated `X` | proved |
| (3.6.2) | product-ring points: injective for quasi-separated `X`, surjective for quasi-compact `X` and local factors | `ProductRingPointComparisonStatement`, `AffineProductRingTopologyStatement` | injective for quasi-separated `X`; surjective for affine `X`, or quasi-compact `X` with local factors; homeomorphism for affine `X` | proved |
| pp.7–8 | Moret-Bailly's warning: `U` scheme-theoretically but not topologically dense; the local factors do not cover `Spec` of the product, and their union is not quasi-compact; ideals of `A_{F,S}` that are not finitely generated but generate the unit ideal in every factor | `AdelicProductSpectrumWarningsStatement` (`MoretBaillyDiagonalStatement`) | Moret-Bailly's diagonal example over any field `k`; product-spectrum facts for arbitrary products of rings, and for infinite products of local rings in which cofinitely many factors have maximal ideal generated by an irreducible element; the level-ring forms for every number field and every function field with any finite `S` | proved |
| p.8 | functoriality, countable base, fibre products, closed immersions of `X_S(A_{F,S})` | `AdelicLevelModelFunctorialityStatement`, `AdelicLevelModelSecondCountabilityStatement`, `AdelicLevelModelPullbackStatement`, `AdelicLevelModelClosedImmersionStatement` | functoriality and fibre products: every morphism and pullback of models, no finite type and no separatedness; countable base: ft model, curves need finite `k`; closed immersions: ft target | proved |
| pp.8–9 | open immersions give topological embeddings, not open embeddings | `AdelicLevelModelOpenImmersionStatement` | an open immersion `X → Y` of models over `O_{F,S}` with `Y` of finite type; points with values in the level ring `A_{F,S}`, every finite `S`; curves: any `k`; the punctured affine line is the non-open witness | proved (`adelicLevelModelOpenImmersion`) |
| Cor 3.7 | `X_S(A_{F,S})` locally compact, Hausdorff if separated | `AdelicLevelModelLocalCompactnessStatement` | ft model; curves need finite `k`; Hausdorff for a separated model | proved |

Source correction, Remark 3.3: Conrad writes that for local Artinian `R` the subsets `Z(R)` and
`U(R)` cover `X(R)`. For the dual numbers `K[ε]` and the affine-line origin `Z` with complement
`U`, the point `t ↦ ε` has image in `Z` but factors through neither `Z` nor `U`.
`ConradRemark33Correction` proves this and keeps the coverage over fields.

Source correction, (3.6.2): Conrad notes that Oesterlé's lemma omits quasi-separatedness; the
statement keeps the injectivity and surjectivity hypotheses separate.

## Section 4 (pp.9–13): adelic topology, examples and mapping properties

| Source | Assertion | Lean declarations | Hypotheses and scope in Lean | Status |
| --- | --- | --- | --- | --- |
| p.9 | final topology on `X(A_F)` via models; final topology of open directed systems | `finalCoconeHomeomorph` (module `FinalCoconeHomeomorph`), `numberFieldFixedModelAdelePointTopology`, `curvePlaceFixedModelAdelePointTopology` (module `AdelicFixedModelCocone`); `AdelicFixedModelColimitOpenStatement` | ft model; the stage maps are continuous and open; the stage images, each with the quotient topology from its stage, embed as open subspaces of the full adelic points; a stage map itself is an open embedding only if the arithmetic model is separated (stage maps need not be injective otherwise) | construction; proved (`adelicFixedModelColimitOpen`) |
| p.9 | independence of the model, agreement with the affine topology, functoriality | `AdelicSpreadTopologyIndependenceStatement`, `AdelicSpreadAffineTopologyStatement`, `AdelicSpreadFunctorialityStatement`, `AdelicFixedModelFunctorialityStatement` | spread forms: ft models, curves need perfect `k`; affine agreement for affine generic fibre; fixed-model functoriality: every morphism of models | proved |
| p.9 | `X ↦ X(A_F)` does not generally carry open immersions to topological embeddings | `AdelicPunctureEmbeddingStatement` (affine evaluation topology), with `AdelicSpreadAffineTopologyStatement` identifying it with the adelic topology for affine schemes | the open immersion `G_m → A^1`: `A_F^× → A_F` is not an embedding; puncture embedding: any `k`; affine agreement: curves need perfect `k` | proved (`adelicPunctureEmbedding`, `adelicSpreadAffineTopology`) |
| p.9 | closed immersions give closed embeddings | `AdelicSpreadClosedImmersionStatement`, `AdelicFixedModelClosedImmersionStatement` | ft models; spread form: curves need perfect `k`; fixed model: ft target | proved |
| p.9 | separated `X`: locally compact, Hausdorff, countable base | `AdelicSpreadTopologicalPropertiesStatement`, `AdelicSpreadSeparatedStatement`, `AdelicFixedModelLocalCompactnessStatement`, `AdelicFixedModelSecondCountabilityStatement` | local compactness and countable base for every ft model (no separatedness), curves need finite `k`; Hausdorff for a separated model, or (`AdelicSpreadSeparatedStatement`, curves with perfect `k`) for a separated generic fibre | proved |
| p.9 | fibre products | `AdelicSpreadPullbackStatement`, `AdelicSpreadModelPullbackStatement`, `AdelicFixedModelPullbackStatement`; binary products `AdelicSpreadProductStatement` | pullbacks: separated base `Z`, factors `X`, `Y` arbitrary (not necessarily separated), ft models of factors and vertex; binary products: no separatedness; curves need perfect `k` (fixed model: any `k`) | proved for separated bases; scope boundary (below) |
| p.9, scope | fibre products over a nonseparated base fail | `AdelicSpreadNonseparatedPullbackStatement` | the affine line with doubled origin over the `S`-integers (finite type, not separated) and its two charts; every limit pullback cone; topologies from the models; curves need perfect `k` | proved (`adelicSpreadNonseparatedPullback`) |
| p.9 | `X_S(A_{F,S})` open in `X(A_F)` for a separated finite-type model `X_S` | `AdelicSpreadStageOpenStatement` | ft models: the stage map is continuous and open for every model; it is an open embedding if the arithmetic model is separated (separatedness of the generic fibre does not suffice); curves need perfect `k` | proved (`adelicSpreadStageOpen`) |
| p.9 | group schemes give locally compact Hausdorff topological groups | `AdelicSpreadGroupStatement` | ft model of the group, no separatedness hypothesis; Hausdorff topological group; curves need perfect `k`, and finite `k` for local compactness and countable base | proved |
| Ex 4.1 | affine covers need not cover `X(A_F)`; the union depends on the cover | `AdelicAffineCoverCounterexampleStatement` | the cover `D(t)`, `D(1-t)` of the affine line against the one-member cover; curves need finite `k` | proved |
| Ex 4.2 | Weil restriction along finite global extensions, including inseparable ones; tensor comparison | `AdelicProjectiveWeilComparisonStatement`, `AdelicTensorBaseChangeStatement` | finite `L/K`; quasi-projective `X` (quasi-compact with an immersion into `P^n_L`); Weil restriction built from affine charts; arbitrary ft models; curves need finite `k` | proved |
| Ex 4.2, proof (p.10) | local step: `Res_{k'/k}(Y')(k) = Y'(k')` is a homeomorphism for a finite extension of complete fields and quasi-projective `Y'`; finite subsets of `Y'` lie in affine opens | `completeFieldWeilRestrictionPointHomeomorph`, `finiteCompletionWeilRestrictionPointHomeomorph`, `infiniteCompletionWeilRestrictionPointHomeomorph` (`CompleteFieldWeilRestrictionTopology`); `hasFiniteAffineNeighborhoods_of_projectiveImmersion` (`QuasiProjectiveWeilRestriction`) | general form: complete nontrivially normed `K` (only `K` needs completeness and a norm); `L` a field that is a finite `K`-algebra, with a Hausdorff topological division ring topology for which the `K`-scalar action is continuous (`ContinuousSMul K L`, the compatibility of the source's absolute values); `Y` locally of finite type over `L` with an immersion into `P^n_L` over `L`; the Weil restriction is the Library's affine-chart gluing; scheme-point topologies on both sides; completion forms: a finite extension `L/K` of number fields and a finite (resp. infinite) place `w` of `L` over `v` of `K`, with `L_w` a `K_v`-algebra through the completed embedding; finite subsets: any scheme with an immersion into `P^n_R`, any ring `R` | proved inside the construction modules |
| Ex 4.3 | `P^n(A_F) = ∏_v P^n(F_v)`, compact Hausdorff; rational points dense; for proper `X` all places | `AdelicProjectiveComparisonStatement`, `AdelicProjectiveRationalDensityStatement`, `AdelicProjectiveRationalImageStatement`, `AdelicProperAllPlaceStatement` | curves need finite `k`; the non-surjective, non-closed, non-discrete image needs `n > 0`; all-place comparison for proper `Y` with an ft model | proved |
| Ex 4.3 | `A^1(A_F)` as subspace of `P^1(A_F)` has the product topology, not locally compact | `AdelicAffineLineSubspaceStatement`, `AdelicAffineLineNonLocalCompactnessStatement` | curves need finite `k` | proved |
| Prop 4.4 | proper maps are topologically proper; local-field ingredient; compactness; stabilization | `AdelicSpreadProperMapStatement`, `LocalFieldProperPointProperties`, `AdelicLevelModelProperMapStatement`, `AdelicFixedModelProperMapStatement`, `AdelicFullLevelPreimageStatement`, `AdelicLocalIntegralPreimageStatement`, `AdelicSpreadCompactnessStatement`, `AdelicSpreadStabilizationStatement` | spread form: proper `g` with separated target, ft models; local fields: non-discrete locally compact Hausdorff topological field, `X`, `Y` finite type and separated; level and fixed-model forms: proper map to a separated ft model; preimages: proper map to a quasi-compact separated model, or valuation rings and universally closed maps, curves with any `k ⊆ F`; compactness and stabilization: proper generic fibre with an ft model; curves need finite `k` in the spread, level, fixed-model, compactness and stabilization forms | proved |
| Prop 4.4, proof | proper maps of separated finite-type `F`-schemes spread out to proper maps of separated models; separatedness and properness are detected at a finite level; projective space has compact points over a locally compact field | `AdelicSpreadSeparatedExistenceStatement`, `AdelicSpreadProperExistenceStatement`, `AdelicSpreadEventualSeparationStatement`, `AdelicSpreadEventualPropernessStatement`, `NormedProjectivePointCompactnessProperty` | existence: separated finite-type `Y` (resp. a proper map to a separated finite-type `W`) over `F`, separated ft models over some larger `S`; eventual detection: arbitrary ft models; curves need perfect `k`; compactness: locally compact nontrivially normed `K`, every `n` | proved |
| pp.11–12 | smooth maps open on `K`-points over complete fields | `CompleteFieldSmoothPointOpenStatement`, `SmoothRationalPointOpenMapStatement`, `HenselianSmoothRationalPointOpenMapStatement`, `StandardEtalePointOpenStatement`, `SmoothAlgebraPointOpenStatement`, `AdelicSmoothLocalPointOpenStatement` | scheme form: complete nontrivially normed `K`, `X`, `Y` locally of finite type, `f` smooth; algebra forms: complete `K`, any algebra map with a standard étale presentation or smooth; affine forms over non-archimedean local fields and over ultrametric fields with henselian valuation ring; adelic local factors: separated models locally of finite type | proved |
| p.11 | continuity of simple roots | `MonicSimpleRootContinuityStatement` | complete nontrivially normed `K`; monic of degree `n > 0` with a simple root; uniqueness only near the coefficient-root pair (correction below) | proved, corrected (`monicSimpleRootContinuity`) |
| p.11 | `G_m → A^1` and `n`-th power maps: non-open examples | `AdelicPunctureEmbeddingStatement`, `AdelicUnitLocusStatement`, `NumberFieldPowerImageStatement`, `CurvePlacePowerImageStatement` | unit locus: curves need finite `k`; puncture embedding: any `k`; powers: `n ≥ 2`, curves need finite `k` and `char k ∤ n` | proved |
| Thm 4.5 | adelic openness: reduction and assembly | `AdelicModelOpenReductionStatement`, `AdelicSpreadSmoothOpenAssemblyStatement` | reduction: separated ft models, with local openness and cofinite surjectivity as hypotheses; assembly: an implication from `UniformLangWeilStatement`, level surjectivity, local openness, the reduction and compatible smooth geometrically connected models to Theorem 4.5 (whose curve clause needs finite `k`) | proved |
| Thm 4.5 | compatible smooth models with full fibre geometry | `AdelicSpreadSmoothExistenceStatement`, `AdelicSpreadEventualSmoothFiberGeometryStatement`, `SmoothPureDimensionStatement` | existence: for separated finite-type schemes `Y`, `W` over the global field and a map that is smooth (resp. smooth with nonempty geometrically connected fibres of pure dimension `d`), there are separated ft models with a model map with the same property; eventual detection: for arbitrary ft models, the generic-fibre map has the property iff the map over some larger `S` has it; curves need perfect `k`; pure dimension: from smoothness of fixed relative dimension `n` (`SmoothOfRelativeDimension n`), over a field and fibrewise | proved |
| Thm 4.5 | geometrically connected models, no common dimension | `AdelicSpreadGeometricallyConnectedStatement` | eventual detection of geometric connectedness and of smooth ⊓ geometrically connected for arbitrary ft models, and existence of separated ft models of a smooth geometrically connected map of separated finite-type schemes; curves need perfect `k` | open (`4a516d9a-eeda-47b6-92af-8e7b2ff6e16f`) |
| Thm 4.5 | almost-all level surjectivity | `AdelicLevelComponentSurjectivityStatement`; lifting input `UniformLangWeilComponentLiftingStatement` | both conditional on `UniformLangWeilStatement`; `f` smooth, separated, quasi-compact, geometrically connected, with target of finite type over `Z` (quasi-compact); level surjectivity at almost all places, curves need finite `k`; lifting of points over finite fields, over henselian local rings with large finite residue field, and of ring points over such rings | open (`8edf7218-d402-4a9f-83de-ef5fd5b2c1be`, `105de89b-639b-4bbe-9b7b-d6956eecc042`) |
| Thm 4.5, proof (p.12) | restriction to connected components of the target, with fibres of a common dimension | `SmoothTargetComponentGeometryStatement` | not conditional on Lang–Weil; fibre-geometry clause: `f` smooth and geometrically connected with locally noetherian target, each component restriction has nonempty geometrically connected fibres of pure dimension; preservation clause: arbitrary base scheme, locally noetherian source and target with structure maps locally of finite type, quasi-compact and separated, no hypothesis on `f`, the component restrictions keep these finiteness properties | open (`32898b5e-5df2-4520-80ad-856f7be5ac0e`) |
| Thm 4.5 | Theorem 4.5 from Lemma 4.6; unconditional | `AdelicSpreadSmoothOpenOfLangWeilStatement`, `AdelicSpreadSmoothOpenStatement` | separated generic fibres, arbitrary ft models; `g` smooth, surjective, geometrically connected; curves need finite `k` | open (`bf4f50f3-77b3-4e25-af38-3f25b86c17b1`; unconditional form follows with Lemma 4.6) |
| Lem 4.6 | uniform relative Lang–Weil estimate | `UniformLangWeilStatement` | base of finite type over `Z`; `f` smooth, separated, surjective, of finite type, geometrically connected, fibres of pure dimension `d` | open (`e5531847-70bc-4569-b880-2f90d5815c6a`); proved conditional on the open derived statement `FamilyLangWeilStatement` by `uniformLangWeilOfFamily` (module `LangWeil/UniformLangWeilOfFamilyProof`; Task 5410, closed); the route through Lang–Weil estimates in families is stated in the `LangWeil/` modules (intermediate statements below); `FamilyLangWeilStatement` follows from Library theorems and Schmidt's bound `PlaneCurveHasseWeilStatement` (Task 5406) alone (its row below), so this lemma depends only on that bound |

Scope boundary, fibre products on p.9: Conrad says the topology "is compatible with fiber
products for general `X`". The Library proves compatibility over a separated base `Z`, with
arbitrary factors, and for all binary products. The unrestricted reading fails for a
nonseparated base. Let `Z` be the affine line with doubled origin, of finite type, and let
`X` and `Y` be its two affine-line charts. Then `X ×_Z Y` is the punctured line, whose adelic
points carry the idele topology. The set of compatible pairs is the diagonal copy of `A_F^×`
inside `A_F × A_F`, with the subspace topology from `A_F`. By `AdelicPunctureEmbeddingStatement`
these topologies differ. The Library statements adopt the separated-base reading; see the scope
paragraph of `AdelicSpreadPullbackStatement.md`. The counterexample is the published statement
`AdelicSpreadNonseparatedPullbackStatement` (row "p.9, scope" above), in the same generality as
`AdelicSpreadModelPullbackStatement` without the separated base.

Source correction, p.11: Conrad requires, for every `ε > 0`, a coefficient bound giving a
unique root in the whole `ε`-ball around the simple root `u_0`. For `K = ℝ`, `g(u) = u(u-1)`,
`u_0 = 0` and `ε = 2`, the polynomial `g` itself meets every coefficient bound, but both simple
roots `0` and `1` lie in the ball. `MonicSimpleRootContinuityStatement`
(`SimpleRootContinuityStatement.lean`, proof `monicSimpleRootContinuity` in
`SimpleRootContinuityProof.lean`) asserts instead a root branch `ψ` that is continuous at the
coefficients `c`, with `ψ c = u_0`, simple roots nearby, and uniqueness on a sufficiently small
neighbourhood of `(c, u_0)`. By continuity, `ψ` stays within any prescribed positive distance
of `u_0`; this local form is what the openness argument uses.

## Section 5, first part (pp.13–17): local and adelic points of algebraic spaces

| Source | Assertion | Lean declarations | Hypotheses and scope in Lean | Status |
| --- | --- | --- | --- | --- |
| p.13 | Thm 3.4 for spaces: points over filtered colimits | `SpaceFilteredRingPointComparison` | eventual equality for `X` locally of finite type over the base; descent of points for `X` locally of finite presentation | proved (`spaceFilteredRingPointComparison`) |
| p.13 | Thm 3.4(1) for spaces: models, morphism descent | `SpaceLimitModelExistence`, `SpaceLimitModelExistenceQuasiSeparated`, `SpaceLimitMorphismDescent`, `SpaceLimitMorphismDescentQuasiSeparated` | cofiltered limits of affine schemes; models of separated (resp. quasi-separated) spaces with an `LocallyOfFinitePresentation ⊓ QuasiCompact` atlas; morphism descent over an affine base from a separated (resp. quasi-separated) source with a quasi-compact atlas to a target locally of finite presentation | `SpaceLimitMorphismDescent` proved (`spaceLimitMorphismDescent`, module `SpaceLimitMorphismDescentProof`; Task 5213 `9f9d8a9b-464e-4a31-b507-58561fb14b22`, closed); `SpaceLimitModelExistence` proved (`spaceLimitModelExistence`, module `SpaceLimitModelExistenceProof`; Task 5215 `0a409da3-f564-4bb8-8773-8abec4c946f4`, closed); `SpaceLimitMorphismDescentQuasiSeparated` proved (`spaceLimitMorphismDescentQuasiSeparated`, module `SpaceLimitMorphismDescentQuasiSeparatedProof`; Task 5235 `480077be-fc27-4c4a-b859-04fdc4c030b0`, closed); `SpaceLimitModelExistenceQuasiSeparated` proved (`spaceLimitModelExistenceQuasiSeparated`, module `SpaceLimitModelExistenceQuasiSeparatedProof`; Task 5260, closed, from the intermediate statements below) |
| p.13 | Thm 3.4(1) for spaces: eventual equality of morphisms; Thm 3.4(3): uniqueness of models | `SpaceLimitUniquenessStatement` | cofiltered limits of affine schemes; both spaces finitely presented | proved (`spaceLimitUniquenessStatement`, with the clauses `spaceLimitMorphismEventualEquality` and `spaceLimitModelUniqueness`, module `SpaceLimitUniquenessProof`; Task 5277, closed) |
| p.13 | Thm 3.4(2) for spaces: closed immersion, separated, proper, smooth, affine, open immersion, finite, fibres nonempty and geometrically connected | `SpaceLimitPropertyDescentStatement` | cofiltered limits of affine schemes; source and target finitely presented | proved (`spaceLimitPropertyDescent`, module `SpaceLimitPropertyDescentProof`: `spaceLimitPropertyDescent_of_foundations representedAtlasEffectivity properSchemeCover`; Task 5278, closed; the separated, smooth and geometrically-connected-fibres conjuncts are also proved separately; intermediate statements below) |
| p.13 | Thm 3.4(2) for spaces: flat; fibres nonempty, geometrically connected and of pure dimension `d` | `SpaceLimitFlatnessDimensionDescentStatement` with `IsFlatMorphism`, `HasPureFibreDimension` | flatness and pure fibre dimension defined through a commutative square with an étale surjective chart of the source and an étale chart of the target; cofiltered limits of affine schemes; source and target finitely presented | proved (`spaceLimitFlatnessDimensionDescent`, module `SpaceLimitFlatnessDimensionDescentProof`; Task 5302, closed): it is `spaceLimitFlatnessDimensionReduction spaceLimitGeometricallyConnectedFibresDescent`; the flatness conjunct is also proved on its own (`spaceLimitFlatnessDescends`), and so is descent of pure fibre dimension alone (`spaceLimitPureFibreDimensionDescends`) (intermediate statements below) |
| Lem 5.1 | geometric-component-count locus constructible | `GeometricFibreComponentsConstructibleStatement`; scheme input `GeometricallyConnectedFiberLocalConstructibility` (proved); scheme specialization `SchemeGeometricComponentCountConstructibleStatement` (intermediate statements below) | quasi-separated, finitely presented over an arbitrary ring `B`; `n` a natural number | proved (`geometricFibreComponentsConstructible`, module `GeometricFibreComponentsProof`; Task 5252, closed; it applies `geometricFibreComponentsConstructible_of_limitModels` (module `GeometricComponentApproximation`) to the model existence of row "Thm 3.4(1) for spaces: models, morphism descent") |
| Prop 5.2 | (3.6.1) bijective for separated finite type spaces | `AdelicSpaceLevelPointsStatement`, `SeparatedProductPointsInjectiveStatement` | separated, finite type over the `S`-integers, curves need finite `k` and nonempty `S`; injectivity for separated spaces over any ring and any product | proved (`adelicSpaceLevelPoints`, `separatedProductPointsInjective`) |
| p.14 | henselian valued fields: definition, separably closed in completion, valuation-ring criterion, tensor with completion, archimedean classification, finite étale equivalence | `IsHenselianValuedField`, `HenselianEtalePointStatement`, `HenselianValuedFieldPropertiesStatement` and its six components, `CompleteHenselianValuedFieldStatement` | nontrivially normed fields; separably closed in the completion: iff henselian; valuation-ring criterion: ultrametric fields; tensor product with the completion: finite separable extensions, a product of completions in general and a field of the same degree for henselian `K`; archimedean classification: non-ultrametric fields; finite étale equivalence: henselian `K`; complete fields are henselian | proved: the conjunction `HenselianValuedFieldPropertiesStatement` (`henselianValuedFieldProperties`), its six components (`henselianIffSeparablyClosed`, `henselianIffValuationRingHenselian`, `tensorCompletionProduct`, `henselianTensorCompletionField`, `archimedeanHenselian`, `henselianFiniteEtaleEquivalence`), `henselianEtalePoint` and `completeHenselianValuedField` |
| Lem 5.3 | étale maps give local homeomorphisms over henselian fields | `HenselianEtalePointLocalHomeomorphStatement` | henselian `K`; `X`, `Y` locally of finite type | proved (`HenselianEtalePointProof`) |
| Prop 5.4 | topology on `X(k)`: existence, uniqueness, functoriality, fibre products, immersions, étale maps | `etaleChartTopology`, `HenselianSpacePointTopologyStatement`, `EtaleChartTopologyAdmissibleStatement` | henselian `K`; the axioms and the uniqueness concern quasi-separated, locally separated spaces locally of finite type (correction below) | proved (`henselianSpacePointTopology`, `etaleChartTopologyAdmissible`, uniqueness lemma `eq_etaleChartTopology_of_isAdmissible`), corrected |
| Prop 5.4 | Hausdorff (separated), totally disconnected, locally compact | `SeparatedRationalPointTopologyProperties` (part of the statement above) | `X` quasi-separated, locally of finite type and separated; totally disconnected for ultrametric `K`; locally compact for locally compact `K` | proved (`t2Space_etaleChartTopology`, `totallyDisconnected`, `locallyCompactSpace_etaleChartTopology`) |
| Prop 5.4 | `k`-analytic manifold structure for smooth `X`, complete `k` | `AnalyticPointStructure` (`AnalyticPointManifold`), `AnalyticPointManifoldStatement` | complete `K`; spaces quasi-separated, locally separated, locally of finite type, with an étale atlas smooth of relative dimension `n`; existence and uniqueness up to equivalence | proved (`analyticPointManifold`, module `AnalyticPointManifoldProof`; Task 5259, closed): existence by the admissible family `canonicalAnalyticPointStructure` (`canonicalAnalyticPointStructure_isAdmissible`, intermediate statements below), uniqueness by `AnalyticPointStructure.equivalent_of_isAdmissible` (module `AnalyticPointUniqueness`) |
| Prop 5.4, proof (p.15) | every rational point lifts through an étale map from an affine scheme (Knutson II.6.4) | `RationalPointEtaleLiftStatement` | any field `k`; `X` quasi-separated | proved (`RationalPointEtaleLiftProof.rationalPointEtaleLiftStatement`) |
| Ex 5.5 | unipotent orbit strata locally closed; quotient spaces `V_d/G`; local Hausdorffness of `(V_d/G)(k)` | `UnipotentOrbitQuotientStatement` | henselian `K` of characteristic zero; `G` a unipotent algebraic group (affine, locally of finite type); `V` reduced of finite type with a `G`-action; strata and quotient as in the source (quotient quasi-separated, finitely presented, with flat surjective quotient map); the topology clause adds that the quotient is locally separated (correction below), with local compactness only for locally compact `K` and local total disconnectedness only for ultrametric `K` | open (Task 5217 `b7321f08-34a4-4479-b6a5-fc099d504d2d`; intermediate statements below: five of the six are proved, and `UnipotentOrbitStabilizerSmoothStatement` follows from the SGA 3 statement of Task 5706; no Library theorem derives `UnipotentOrbitQuotientStatement` from them) |
| Cor 5.6 | proper maps over local fields are proper on points | `LocalFieldProperPointMapStatement` | locally compact nontrivially normed `K`; `X`, `Y` quasi-separated and locally of finite type | proved (`localFieldProperPointMap`, module `LocalFieldProperPointMapProof`; Task 5483, closed, with Task 5216): the proved implication `LocalFieldProperPointValuativeReductionStatement` applied to the proved Stacks valuative criterion `spaceValuativeExistence` (Task 5368). The Lean proof replaces Conrad's Chow-lemma argument by the valuative criterion and an ultrafilter limit over the convergent germs of an ultrapower (`LocalFieldProperPointLimit.localFieldProperPointMap_of_valuative`); archimedean `K` remain included (intermediate statements below) |
| Cor 5.7 | `X(R)` open in `X(k)` | `HenselianIntegralPointsOpenStatement` | `O` the closed unit ball, a henselian local ring; `X` quasi-separated, locally of finite type over `O`; the image of `X(O)` in `X_K(K)` is open | proved (`henselianIntegralPointsOpen`) |
| Cor 5.7 | `X(R)` quasi-compact for locally compact `k` and `X` of finite type | `HenselianIntegralPointsCompactStatement` | as above, with `K` locally compact and `X` of finite type over `O`; the image of `X(O)` in `X_K(K)` is compact | proved (`henselianIntegralPointsCompact`) |
| Cor 5.7 | closedness, corrected scope | `HenselianIntegralPointsClosedStatement`; locally compact case `HenselianIntegralPointsClosedOfLocallyCompactStatement`; inputs `HenselianChartIntegralPointsClosedStatement`, `UniformFieldPointChartsStatement` (intermediate statements below) | `X` separated: injectivity of `X(O) → X_K(K)`; closed image if moreover `X` is of finite type over `O`; the locally compact case adds `K` locally compact | locally compact case proved (`henselianIntegralPointsClosedOfLocallyCompact`); general case open (Task 5218 `5e83271c-c91b-45ad-b94a-ea03601fec06`); its two inputs are proved (rows below), but no Library theorem derives the general case from them |
| Cor 5.7 | counterexamples to unqualified closedness | `HenselianIntegralPointsNotClosedOfFiniteTypeStatement`, `HenselianIntegralPointsNotClosedOfSeparatedStatement` | for every such `K` and `O`: a quasi-separated space of finite type, and a separated space locally of finite type, with non-closed image | proved |
| p.17 | level points locally compact Hausdorff, open level changes | `AdelicSpaceLevelTopologyStatement` | separated, finite type over the `S`-integers, curves need finite `k` and nonempty `S` | proved (`adelicSpaceLevelTopology`) |
| p.17 | `X(A_F)`: Weil limit bijection, topology, locally compact Hausdorff with countable base, fibre products, closed immersions, scheme agreement, model independence | `AdelicSpacePointTopologyStatement` (`AdelicSpacePointTopology` constructions) | separated finite-type models, curves need finite `k` and nonempty `S`; fibre products of separated finite-type spaces; scheme agreement for separated ft schemes | proved (`adelicSpacePointTopology`, module `Langlands/Global/AdelicSpacePointTopologyTheorem`; Task 5222 `360a1cdf-4b68-402e-b087-254b03da61f6`, closed): `AdelicSpacePointTopologyProof.adelicSpacePointTopology_of_spread` derives the statement from `spaceFilteredRingPointComparison` and the spread clauses `AdelicSpaceSpreadIndependenceProof.curvePlaceSpaceSpread` and `.numberFieldSpaceSpread`; model existence is `AdelicSpaceSpreadExistenceProof` (from `spaceLimitModelExistence`), model independence `AdelicSpaceSpreadIndependenceProof` (from `spaceLimitMorphismDescent`) |
| Prop 5.8 | proper maps of separated spaces: topologically proper on adelic points | `AdelicSpaceSpreadProperMapStatement`; inputs `AdelicSpaceProperStagesStatement`, `AdelicSpaceProperModelStatement` (intermediate statements below) | arbitrary separated finite-type models of source and target, curves need finite `k` and nonempty `S` (correction below) | open (Task 5253; `AdelicSpacePointTopologyStatement` and Cor 5.6 are proved); its input `AdelicSpaceProperStagesStatement` is proved (`adelicSpaceProperStages`, module `Langlands/Global/AdelicSpaceProperStagesProof`); its input `AdelicSpaceProperModelStatement` follows from Library theorems (`AdelicSpaceProperModelReduction.adelicSpaceProperModel_of_descent spaceLimitMorphismDescent (spaceLimitProperDescent_of_schemeCovers properSchemeCover)` has its type), but no theorem of its type is published; no Library theorem derives `AdelicSpaceSpreadProperMapStatement` from the two inputs (intermediate statements below) |
| Thm 5.9 | smooth surjective geometrically connected: open on adelic points | `AdelicSpaceSpreadSmoothOpenStatement`; input `SpaceUniformLangWeilStatement`; local input `CompleteFieldSmoothSpacePointOpenStatement` (intermediate statements below) | arbitrary separated finite-type models, curves need finite `k` and nonempty `S`; `g` smooth, surjective, with geometrically connected fibres; the Lang–Weil input: base quasi-separated of finite type over `Z`, `f` smooth of relative dimension `d` on étale charts, separated, quasi-compact, surjective, with geometrically connected fibres | open (Task 5254; Lang–Weil input in `e5531847-70bc-4569-b880-2f90d5815c6a`); the local input is proved (`completeFieldSmoothSpacePointOpen`); openness on level and stage points is proved from the local input and cofinite surjectivity, cofinite surjectivity from a uniform point-count estimate on residue fibres, and both cofinite surjectivity and openness on level points from `SpaceUniformLangWeilStatement` (intermediate statements below); `SpaceUniformLangWeilStatement` follows from Library theorems and Schmidt's bound `PlaneCurveHasseWeilStatement` (Task 5406) alone (rows of `FamilyLangWeilStatement` and `SpaceUniformLangWeilOfFamilyStatement` below) |

Source corrections, first part:

- **Ex 5.5.** Conrad asserts that `(V_d/G)(k)` is locally Hausdorff and locally compact. This
  rests on Proposition 5.4 and fails for quotients that are not locally separated;
  `UnipotentOrbitQuotientStatement.md` gives a counterexample (a variant of Stacks, Tag 02Z1,
  over any henselian field of characteristic zero). The topology clause of
  `UnipotentOrbitQuotientStatement` therefore assumes the quotient locally separated, and
  qualifies local compactness and total disconnectedness by local compactness and
  ultrametricity of `K`. The strata and quotient clauses keep the source's scope.
- **Prop 5.4.** False for quasi-separated spaces that are not locally separated (Stacks,
  Tag 02Z1); `HenselianSpacePointTopologyStatement` and `AnalyticPointManifoldStatement` add
  local separatedness, explained in their Markdown.
- **Cor 5.7.** The closedness proof's preimage claim fails (`Spec R ⊔ Spec k → Spec R`), and the
  conclusion fails for a quasi-separated finite-type space and for a separated locally finite
  type space; restriction of points need not be injective without separatedness. The published
  statements treat the image of `X(O)`, require separated finite type for closedness, and state
  the two counterexamples.
- **Prop 5.8.** Conrad says "locally of finite type", but the adelic topology is constructed for
  finite type; the statements in `AdelicSpaceSpreadMapStatement.lean` require separated
  finite-type models, and its Markdown explains why a proper map to a finite-type space has a
  finite-type source.

## Section 5, second part (pp.17–20): valued extensions and Weil restriction

| Source | Assertion | Lean declarations | Hypotheses and scope in Lean | Status |
| --- | --- | --- | --- | --- |
| Lem 5.10 | Weil restriction of spaces along finite locally free maps is an algebraic space; finite type, separated, finite presentation | `ringWeilRestriction`, `ringWeilRestrictionSpace` (`SpaceWeilRestriction`), `SpaceWeilRestrictionStatement` | `R → R'` finite projective; `X'` quasi-separated of finite type over `R'` | proved (`spaceWeilRestriction`, module `SpaceWeilRestrictionProof`; Task 5255, closed; it applies `spaceWeilRestriction_of_geometricInputs` to the two proved statements of `WeilRestrictionGeometricInputsStatement`, intermediate statements below) |
| Prop 5.11(1) | finite extension: `Res(Y')(k) = Y'(k')` homeomorphism | `HenselianWeilRestrictionPointHomeomorphStatement` | henselian `K` and `K'`, `K'` a finite-dimensional normed `K`-algebra; `Y'` quasi-separated of finite type; no module-topology hypothesis (correction below) | false as stated (note `finite-weil-inseparable-obstruction.md`; its proof Task 5256 is retired; the section "Correction to the literal Proposition 5.11(1)" of `SpaceWeilRestrictionStatement.md`, by Worker 172 for Task 5320, records the correction) |
| Prop 5.11(1), corrected | the same homeomorphism when `K'` carries the `K`-module topology, as in Conrad's proof through Example 2.4 | `HenselianWeilRestrictionPointHomeomorphOfModuleTopologyStatement` (module of the same name) | as above plus `IsModuleTopology K K'`, which holds for complete `K`; the conclusion includes that the Weil restriction is an algebraic space | proved (`henselianWeilRestrictionPointHomeomorphOfModuleTopology`, module `HenselianWeilRestrictionPointHomeomorphOfModuleTopologyProof`; Task 5320; it applies `isHomeomorph_ringWeilRestrictionBasePointsEquiv` (intermediate statements below) to the algebraic space, quasi-separated and of finite type, given by `spaceWeilRestriction` (Lemma 5.10)) |
| Prop 5.11(2) | `X(k) → X(k̂)` topological embedding | `HenselianCompletionPointEmbeddingStatement` | henselian `K`; `X` quasi-separated, locally of finite type | proved (`henselianCompletionPointEmbedding`) |
| Prop 5.11(3) | `X(k) → X(k')` embedding, closed if `k` closed in `k'`, for spaces covered by separated opens | `HenselianExtensionPointEmbeddingStatement`, `IsCoveredBySeparatedOpenSubspaces` | henselian `K`, `K'`, `K'` a normed `K`-algebra of any degree; `X` quasi-separated, locally of finite type, covered by separated open subspaces | proved (`henselianExtensionPointEmbedding`, module `HenselianExtensionPointEmbeddingProof`: `ExtensionClosedReduction.henselianExtensionPointEmbedding_of_complete CompleteExtensionClosedRange.completeExtensionPointClosedRange`; Task 5258, closed; the embedding conjunct is also proved directly by `ExtensionLocalReduction.isEmbedding_of_covered`; intermediate statements below) |
| Prop 5.11, proof (p.19) | finite extensions: `X(k) → X(k')` is an embedding when `Δ_{X/k}` is a quasi-compact immersion, without completeness | `HenselianFiniteExtensionPointEmbeddingStatement` | henselian nontrivially normed fields `K`, `K'`, `K'` a finite-dimensional normed `K`-algebra; `X` quasi-separated, locally of finite type and locally separated (immersive diagonal); no separated open cover, no completeness; embedding only, no closedness | proved (`henselianFiniteExtensionPointEmbedding`, a direct argument with étale charts and finite Galois descent that uses neither Proposition 5.11(1) nor completeness) |
| Cor 5.12 | finite maps proper on points if `k` algebraically closed in `k̂`; characteristic-zero case | `HenselianFinitePointProperStatement`, `HenselianCharZeroAlgebraicallyClosedInCompletionStatement` | henselian `K` algebraically closed in its completion; `X`, `Y` separated, locally of finite type; `f` finite | proved (`henselianFinitePointProper`, `HenselianCharZeroCompletionProof`) |
| Ex 5.13 | quasi-compact immersive diagonal does not suffice for closedness | `HenselianExtensionPointNotClosedStatement` (`HenselianExtensionPointCounterexampleStatement`) | complete ultrametric `K`, separable quadratic `K'`; a quasi-separated space locally of finite type with affine immersive diagonal | proved (`henselianExtensionPointNotClosed`; the space is the Galois-twisted line of the `GaloisTwistedLine…` modules) |
| Prop 5.14 | adelic Weil restriction homeomorphism for separated finite type spaces | `AdelicSpaceWeilRestrictionStatement` | finite `F'/F`; `Y'` separated of finite type; arbitrary separated finite-type models; curves need finite `k` and nonempty `S`, `S'` | proved (`adelicSpaceWeilRestriction`, module `Langlands/Global/AdelicSpaceWeilRestrictionProof`, with the clauses `AdelicSpaceWeilRestrictionProof.numberFieldSpaceWeilRestriction` and `AdelicSpaceWeilRestrictionProof.curvePlaceSpaceWeilRestriction`; Task 5257, context revision 2, closed; supporting modules in the constructions paragraphs below) |

The excellent-valuation-ring sufficient condition after Corollary 5.12 is a cited fact; only
its characteristic-zero part is stated.

Source correction, Proposition 5.11(1): the proof (printed p.18) reduces to the affine case of
Example 2.4 (printed p.3), which assumes that `k'` carries the topology of a finite free
`k`-module. That holds for complete `k`, but not for every henselian `k`. For a henselian `k`
whose completion contains a proper finite purely inseparable extension `k'`, `k` is dense in
`k'`. Then `Res_{k'/k}(A^1)(k) = k^{[k':k]}` with the product topology cannot be homeomorphic to
`k'` by the canonical bijection. The published note
[`finite-weil-inseparable-obstruction.md`](finite-weil-inseparable-obstruction.md) (Worker 111)
gives the construction from Temkin's *Valued Fields*, Exercise 1.8.11 and Remark 1.9.6. The
operator confirmed the counterexample. The literal statement, and the published
`HenselianWeilRestrictionPointHomeomorphStatement` that transcribes it, are false. The corrected
statement `HenselianWeilRestrictionPointHomeomorphOfModuleTopologyStatement`, with
`IsModuleTopology K K'`, is published and proved
(`henselianWeilRestrictionPointHomeomorphOfModuleTopology`, Task 5320). The module
`SpaceWeilRestrictionStatement.lean` defines both `SpaceWeilRestrictionStatement` (Lemma 5.10)
and the literal `HenselianWeilRestrictionPointHomeomorphStatement`; its Markdown now records
this correction (Worker 172), and its Lean file is unchanged. Conrad applies Proposition
5.11(1) to complete fields in Proposition 5.14 (at local fields) and in the finite-degree case
of Proposition 5.11(3) (after the reduction to completions through part (2)); these uses are
unaffected. The parenthetical on p.19 applies it without completeness. The Library proof of
that finite-degree assertion (`henselianFiniteExtensionPointEmbedding`, row "Prop 5.11, proof
(p.19)") does not take this step: it argues with étale charts and finite Galois descent and uses
neither Proposition 5.11(1) nor completeness.

## Derived intermediate statements and reductions

Workers on the proof tasks, on the Lang–Weil program `e5531847-70bc-4569-b880-2f90d5815c6a` and
on the Example 5.5 program Task 5217, published the following statements and proved
reductions. They are derived steps of Conrad's proofs, or cited results such as the Stacks
Project lemmas in two Theorem 3.4(2) rows, three Corollary 5.6 rows and one Proposition 5.8 row and
the SGA 3 and Milne results in two Example 5.5 rows, not separate assertions of the paper. Each row names the
source row it serves, and the status column gives the proof task where one exists, with its
executors as inspected on 2026-11-12.

| Serves | Lean declarations | Hypotheses and scope in Lean | Status |
| --- | --- | --- | --- |
| Lem 4.6 (`e5531847-70bc-4569-b880-2f90d5815c6a`) | `FamilyLangWeilInDimension`, `FamilyLangWeilStatement` (`LangWeil/FamilyLangWeilStatement`) | `S` of finite type over `Z`; `f : X → S` of finite type, geometrically irreducible, with all fibres of pure dimension `d`; a constant `C > 0` with `\|#X_s(κ) − q^d\| ≤ C·q^(d−1/2)` for every finite field `κ` with `q` elements and every `κ`-point `s` of `S`; the second statement asserts this for every `d` | open (published for `e5531847-70bc-4569-b880-2f90d5815c6a`; no separate proof task; by induction on `d` it follows from the dimension-0, curve and slicing statements below and their inputs; the dimension-0 statement, the curve and slicing implications and their inputs `BertiniGenericHyperplaneStatement` and `FamilyPointUpperBoundStatement` (the latter by `familyPointUpperBound`) are proved, so it follows from Schmidt's bound `PlaneCurveHasseWeilStatement` (Task 5406) alone; no Library theorem states this implication) |
| Lem 4.6 (`e5531847-70bc-4569-b880-2f90d5815c6a`) | `FamilyPointUpperBoundStatement` (`LangWeil/`) | `S` of finite type over `Z`; `f : X → S` of finite type; a constant `C > 0` with `#X_s(κ) ≤ C·q^e` for every finite field `κ`, every `κ`-point `s` and every `e` bounding the dimension of the fibre over the image of `s` | proved (`familyPointUpperBound`, module `LangWeil/FamilyPointUpperBoundProof`: `familyPointUpperBound_of_finiteNormalizationCover finiteNormalizationCover`; Task 5405 `d6315fa9-e6a8-41f6-ae31-b7253872c91c`, closed; rows below) |
| Lem 4.6 (Task 5405) | `FiniteNormalizationCoverStatement`, with the structure `FiniteNormalizationCover` (`LangWeil/`) | `S` Noetherian; `f : X → S` locally of finite type and quasi-compact (no separatedness, reducedness or equidimensionality); conclusion: finitely many pieces, each an affine scheme `T_i` with an immersion `T_i → S`, an immersion `U_i → X`, a natural number `d_i` and a finite surjective map `U_i → A^{d_i}_{T_i}` compatible with `f`, such that every `Spec K → X` with `K` a field (same universe) factors through some `U_i`, and `d_i` is at most the topological Krull dimension of the fibre of `f` over the image of every point of `T_i`; derived from the Stacks Project, Lemma 10.115.4 (Tag 00OY) and Section 33.18 with Lemma 33.18.2 (Tags 0CBG, 0CBI) | proved (`finiteNormalizationCover`, module `LangWeil/FiniteNormalizationCoverProof`, with `LangWeil/FiniteNormalizationCoverAlgebra`, `LangWeil/FiniteNormalizationCoverPieces` and `LangWeil/FiniteNormalizationCoverAffine`, declarations prefixed `LangWeil.NormalizationCoverConstruction.`; published for Task 5405; proof Task 5604 `bd611de6-07f4-4aac-a4f1-d1c8be5c2bed`, closed) |
| Lem 4.6 (Task 5405) | `familyPointUpperBound_of_finiteNormalizationCover` (`LangWeil/NormalizationCoverPointBound`) | `FiniteNormalizationCoverStatement` implies `FamilyPointUpperBoundStatement`, in the same universe | proved (conditional on `FiniteNormalizationCoverStatement`, which is proved by `finiteNormalizationCover`; `familyPointUpperBound` applies it to that theorem) |
| Lem 4.6 (`e5531847-70bc-4569-b880-2f90d5815c6a`) | `PlaneCurveHasseWeilStatement`, `BertiniGenericHyperplaneStatement` (`LangWeil/`) | Schmidt's bound: a finite field `F` with `q` elements; `f ∈ F[X,Y]` absolutely irreducible with `a = deg_X f > 0`, `b = deg_Y f > 0` and `9(a+1)²(b+1)² < q`; the number `N` of affine zeros satisfies `\|N − q\| < 2·min(a²b, ab²)·√q`. Bertini: any field `k`; a `k`-algebra `A` generated by `g_1, …, g_n`, geometrically irreducible over `k` of Krull dimension at least 2; the generic hyperplane section `u_0 + Σ u_i g_i = 0` over the fraction field of `k[u_0, …, u_n]` is geometrically irreducible | Schmidt's bound open (Task 5406 `f0851881-2bc7-45e6-a745-32e02733564e`, executors Workers 2969 and 96; the intermediate statements `StepanovCountingStatement` and `PlaneCurveElementaryReductionsStatement`, published for that task (rows below), are proved, and no Library theorem derives Schmidt's bound from them); Bertini proved (`BertiniGenericHyperplane.bertiniGenericHyperplaneStatement`, module `LangWeil/BertiniGenericHyperplaneProof`, with `LangWeil/BertiniHyperplaneSeparable`, `LangWeil/BertiniHyperplaneKernel`, `LangWeil/BertiniHyperplaneCore` and `LangWeil/BertiniHyperplaneDimension`, declarations prefixed `BertiniGenericHyperplane.`; Task 5407, closed; finite `k` included, by reduction to an algebraically closed field) |
| Lem 4.6 (Task 5406) | `StepanovCountingStatement` (`LangWeil/`) | a finite field `F` with `q` elements; any `r : F → ℕ`; `2 ≤ n ≤ m` and `9(m+1)²(n+1)² < q`; hypothesis: for every `M > 0` with `M²(n²+1) + (M+m)n² < q` and `Mn ≤ q` there are `s ⊆ F` and `h_1, h_2 ∈ F[X]` with `q < \|s\| + 2mn`, `r(x) ≤ n` for every `x`, `deg h_1 < q(M+E)` and `deg h_2 < q((n−1)M+E)` for `E = 2m(n−1)+1`, and root multiplicities at least `M·r(x)` and `M·(n−r(x))` at every `x ∈ s`; conclusion: `\|Σ_x r(x) − q\| < 2mn²·√q`; a derived abstraction of Schmidt, *Zur Methode von Stepanov* (1973), Section 7, pp.359–360 (equation (40)), and Section 9, p.367 | proved (`stepanovCounting`, module `LangWeil/StepanovCountingProof`; published for Task 5406) |
| Lem 4.6 (Task 5406) | `PlaneCurveElementaryReductionsStatement` (`LangWeil/`) | two clauses over any finite field `F`, for `f ∈ F[X,Y]` absolutely irreducible: (1) if both partial degrees of `f` are positive, some absolutely irreducible `g` with both partial derivatives nonzero, `0 < deg_Y g ≤ deg_X g`, `deg_X g ≤ max(deg_X f, deg_Y f)` and `deg_Y g ≤ min(deg_X f, deg_Y f)` has the same number of affine `F`-zeros as `f`; (2) if `deg_Y f = 1`, the number of affine `F`-zeros of `f` differs from `#F` by at most `deg_X f`; derived from Schmidt (1973), Section 2, p.349 | proved (`planeCurveElementaryReductions`, module `LangWeil/PlaneCurveElementaryReductionsProof`, with `LangWeil/PlaneCurveLinearFibres`, `LangWeil/PlaneCurveSeparableModel` and `LangWeil/PlaneCurveCoordinateOperations`; published for Task 5406) |
| Lem 4.6 (`e5531847-70bc-4569-b880-2f90d5815c6a`) | `FamilyLangWeilZeroStatement` (`LangWeil/`) | the family estimate in dimension 0, with the hypotheses of `FamilyLangWeilInDimension 0` | proved (`familyLangWeilZero`, module `LangWeil/FamilyLangWeilZeroProof`, Task 5404 `d108969a-c371-4c06-9403-4d8d7846d52c`; the proof shows that every fibre has exactly one `κ`-point and does not use quasi-compactness or the base over `Z`) |
| Lem 4.6 (`e5531847-70bc-4569-b880-2f90d5815c6a`) | `FamilyLangWeilCurveStatement`, `FamilyLangWeilSlicingStatement` (`LangWeil/`) | implications: Schmidt's bound and the upper bound give dimension 1; Bertini, the upper bound and dimension `d + 1` give dimension `d + 2` | curve proved (`familyLangWeilCurve`, module `LangWeil/FamilyLangWeilCurveProof`: it applies `familyLangWeilCurve_of_planeComparison` (module `LangWeil/FamilyLangWeilCurvePlaneReduction`) to the proved plane-model comparison of the row below; Task 5408 `bc74c0bd-bddc-4c19-835a-46cd2f533740`, closed); slicing proved (`familyLangWeilSlicing`, module `LangWeil/FamilyLangWeilSlicingProof`, with the helper modules `LangWeil/Slicing/Bridges`, `Core`, `Counting`, `Dimension`, `GenericImage`, `GenericSlice`, `Hyperplane` and `Reduction`, declarations prefixed `Slicing.`; Task 5409 `2795fee1-d876-4010-86ed-ccd7f8e687c7`, closed); the premises `BertiniGenericHyperplaneStatement` and `FamilyPointUpperBoundStatement` are proved (rows above), and the curve implication also assumes Schmidt's bound |
| Lem 4.6 (Task 5408) | `FamilyCurvePlaneComparisonStatement` (`LangWeil/`) | assumes `FamilyPointUpperBoundStatement`; `S` quasi-compact and locally of finite type over `Z`; `f : X → S` locally of finite type, quasi-compact, geometrically irreducible, all fibres of pure dimension 1; there is `B > 0` such that for every finite field `κ` with more than `B` elements and every `κ`-point `s` of `S` some `p ∈ κ[X,Y]`, irreducible over an algebraic closure of `κ`, with degrees in `X` and in `Y` in `[1, B]`, has affine zero count within `B` of `#X_s(κ)`; a plane-model comparison derived from Lang–Weil (1954), printed p.819, and Tao, *The Lang–Weil bound*, Section 2 | proved (`familyCurvePlaneComparison`, module `LangWeil/FamilyCurvePlaneComparisonProof`, with the helper modules `LangWeil/FamilyCurvePlaneReduction`, `AffineCurvePlaneComparison`, `CurvePlaneCharts`, `CurvePlaneFibrePoints`, `CurvePlaneNoetherianInduction`, `CurvePlanePolynomial`, `CurvePlaneRadicialPoints` and `CurvePlaneZeroDimensional`, declarations prefixed `CurvePlane.`; published for Task 5408 as an input to `FamilyLangWeilCurveStatement`; proof Task 5581 `b589cd1b-1a7b-41c8-afcf-506ab674e1e2`, closed; the proof does not use the premise `FamilyPointUpperBoundStatement`) |
| Lem 4.6 and Thm 5.9 (`e5531847-70bc-4569-b880-2f90d5815c6a`) | `UniformLangWeilOfFamilyStatement`, `SpaceUniformLangWeilOfFamilyStatement` (`LangWeil/`) | implications: `FamilyLangWeilStatement` implies `UniformLangWeilStatement`; `FamilyLangWeilStatement` and `FamilyPointUpperBoundStatement` imply `SpaceUniformLangWeilStatement` | first proved (`uniformLangWeilOfFamily`, module `LangWeil/UniformLangWeilOfFamilyProof`; Task 5410 `acab9a1a-0a8e-4bd8-a84b-dc3f7aed3074`, closed); second proved (`spaceUniformLangWeilOfFamily`, module `LangWeil/SpaceUniformLangWeilOfFamilyProof`, with the helper modules `LangWeil/SpaceFamily/Counting`, `DegreePoints`, `FibreCharts`, `FibreProductBase`, `FieldPoints`, `FiniteFieldCharts`, `RingPointCharts`, `SchemeBase`, `SeparatedChart` and `Strata`, declarations prefixed `LangWeil.SpaceFamily.`; Task 5411 `25f82ff3-eaee-49c3-b113-d27d596fe177`, closed); so both forms of Lemma 4.6 follow from `FamilyLangWeilStatement` |
| Thm 3.4(1) for spaces (Task 5260) | `EtaleEquivalenceRelation.LimitModelExistence` (`EtaleEquivalenceRelationLimitModelStatement`) | cofiltered limits of affine schemes; an étale equivalence relation of schemes over the limit with affine object scheme, object structure map locally of finite presentation and quasi-compact relation structure map; conclusion: an étale equivalence relation at one stage, with the same finiteness properties, whose object and relation schemes give the original ones by base change (cartesian comparisons) | proved (`EtaleEquivalenceRelation.limitModelExistence`, modules `EtaleEquivalenceRelationLimitModelProof` and `EtaleEquivalenceRelationLimitModelLevels`; Task 5367 `2a912398-eb7f-4d09-8707-ce9f5bf718d1`) |
| Thm 3.4(1) for spaces (Task 5260) | `SpaceLimitModelExistenceQuasiSeparatedReduction.spaceLimitModelExistenceQuasiSeparated_of_relation` (`SpaceLimitModelExistenceQuasiSeparatedReduction`) | the statement above implies `SpaceLimitModelExistenceQuasiSeparated` | proved (reduction) |
| Thm 3.4(2) for spaces (Task 5278) | `spaceLimitSeparatedDescent` (`RelativeDiagonalLimitDescent`), `spaceLimitSmoothDescent` (`SmoothChartLimitDescent`) | the separated and the smooth conjuncts `SpaceLimitPropertyDescends` of `SpaceLimitPropertyDescentStatement`, with its full hypotheses: cofiltered limits of affine schemes; source and target quasi-separated with an `LocallyOfFinitePresentation ⊓ QuasiCompact` atlas | proved |
| Thm 3.4(2) for spaces (Task 5278) | `RepresentedMorphismAtlas.closedImmersion_limit_iff`, `RepresentedMorphismAtlas.affine_limit_iff`, `RepresentedMorphismAtlas.openImmersion_limit_iff`, `RepresentedMorphismAtlas.finite_limit_iff` (`RepresentedChartLimitDescent`) | cofiltered limits of affine schemes; `f : X → Y` over a stage, given with a represented atlas pullback (a proof that `f` is representable, a surjective étale scheme atlas of `Y`, and the scheme pullback of `f` along it), both chart schemes finitely presented over the stage; the base change of `f` to the limit is a closed immersion, affine, an open immersion or finite iff its base change to some stage is | proved (conditional on the represented atlas pullback, which this module does not construct; the general case follows from the `_of_modelUniqueness` row below) |
| Thm 3.4(2) for spaces (Task 5278) | `RepresentedAtlasEffectivityStatement` (`EtaleAtlasPropertyEffectivity`) | Stacks Project, *Morphisms of Algebraic Spaces*, Tags 03M4, 03WG and 03ZQ: any base scheme; `f : X → Y` with a cartesian square over a surjective étale scheme atlas `V → Y` whose scheme side is `q : U → V`; if `q` is a closed immersion, affine, an open immersion or finite, then `f` is representable and every scheme base change of `f` has the same property | proved (`representedAtlasEffectivity`, module `RepresentedAtlasEffectivityProof`, with the helper module `RepresentedAtlasEffectivityDescent`, declarations prefixed `AtlasEffectivity.`; published for Task 5278; proof Task 5472 `073bf3b4-2349-40b4-b0c7-ace048377261`, closed): representability of `f` from the Library's quotients of étale equivalence relations and open-chart gluing, then descent of each property along the atlas by `AtlasEffectivity.etaleAtlasPropertyEffectivity_of_represented` |
| Thm 3.4(2) for spaces (Task 5278) | `spaceLimitClosedImmersionDescent_of_modelUniqueness`, `spaceLimitAffineDescent_of_modelUniqueness`, `spaceLimitOpenImmersionDescent_of_modelUniqueness`, `spaceLimitFiniteDescent_of_modelUniqueness` (`EventualTargetAtlasDescent`) | `SpaceLimitModelUniqueness` (the model-uniqueness half of `SpaceLimitUniquenessStatement`) and the corresponding conjunct `EtaleAtlasPropertyEffectivity` of `RepresentedAtlasEffectivityStatement` as hypotheses; the full hypotheses of `SpaceLimitPropertyDescends`, with no representability of `f` at the original stage: cofiltered limits of affine schemes; source and target quasi-separated with a `LocallyOfFinitePresentation ⊓ QuasiCompact` atlas; conclusions: the closed immersion, affine, open immersion and finite conjuncts of `SpaceLimitPropertyDescentStatement` | proved (reductions; both premises are proved, by `spaceLimitModelUniqueness` and the four components of `representedAtlasEffectivity`; `spaceLimitPropertyDescent` proves the whole statement) |
| Thm 3.4(2) for spaces (Task 5278) | `isProperMorphism_iff_separated_universallyClosed`, `isProperMorphism_baseChangeMap_iff_separated_universallyClosed` (`FiniteTypeMorphismAtlas`) | source and target with a `LocallyOfFinitePresentation ⊓ QuasiCompact` atlas, target quasi-separated; over an affine base, and after base change along any map from an affine scheme, `f` is proper iff it is separated and universally closed | proved |
| Thm 3.4(2) for spaces (Task 5278) | `spaceLimitGeometricallyConnectedFibresDescent` (`SpaceLimitConnectedFibresDescent`) | the geometrically-connected-fibres conjunct `SpaceLimitPropertyDescends (fun f => HasGeometricallyConnectedFibres f)` of `SpaceLimitPropertyDescentStatement`, with its full hypotheses: cofiltered limits of affine schemes; source and target quasi-separated with a `LocallyOfFinitePresentation ⊓ QuasiCompact` atlas; `HasGeometricallyConnectedFibres` asks for nonempty connected fibres over every field point | proved |
| Thm 3.4(2) for spaces (Task 5278) | `ProperSchemeCoverStatement` (`AlgebraicSpace/`) | Stacks Project, Lemma 69.18.1 (Tag 089I, weak Chow lemma), with Lemmas 76.40.3 (Tag 088S) and 76.41.1 (Tag 089L), refined to finite presentation: affine `S`; `X` over `S` quasi-separated with a `LocallyOfFinitePresentation ⊓ QuasiCompact` atlas and proper structure morphism; there are a scheme `U` over `S`, proper and locally of finite presentation over `S`, and a surjective morphism from the space represented by `U` to `X` (not assumed étale); published as an input to the universal-closedness part of the proper conjunct | proved (`properSchemeCover`, module `ProperSchemeCoverProof`: `properSchemeCover_of_chowCover` (module `ProperCoverFPReduction`, with `ProperCoverFPApprox` and `ProperCoverFPComposite`: a Noetherian model of the space, a cover of the model, and its pullback to the original base) applied to `ProperSchemeCover.chowCover`, which proves `ProperSchemeCover.ChowCoverStatement`: a separated space over affine `S` with a `LocallyOfFinitePresentation ⊓ QuasiCompact` atlas receives a surjective morphism, proper after every base change to a scheme, from a scheme locally of finite type and quasi-compact over `S` (modules `ProperSchemeCover/ChowCoverStatement` and `ProperSchemeCover/ChowCoverProof`, with `ProperSchemeCover/AffineEmbedding`, `Closedness`, `CompleteTuples`, `Construction`, `OpenGluing`, `PointAgreement`, `RelativeProper` and `SpacePullback`); published for Task 5278; proof Task 5586 `99c0be8e-a359-4e9c-bec3-ee1a7255ed09`, closed); with it the proper conjunct follows, and `spaceLimitPropertyDescent` proves the whole statement (row below) |
| Thm 3.4(2) for spaces (Task 5278) | `spaceLimitProperDescent_of_schemeCovers`, `spaceLimitPropertyDescent_of_foundations` (`SpaceLimitProperDescentOfSchemeCovers`) | the first: `ProperSchemeCoverStatement` as a hypothesis, in the same universe; conclusion: the proper conjunct `SpaceLimitPropertyDescends (fun f => IsProperMorphism f)` of `SpaceLimitPropertyDescentStatement`, with its full hypotheses: cofiltered limits of affine schemes; source and target quasi-separated with a `LocallyOfFinitePresentation ⊓ QuasiCompact` atlas; the second: `RepresentedAtlasEffectivityStatement` and `ProperSchemeCoverStatement` as hypotheses, in the same universe; conclusion: `SpaceLimitPropertyDescentStatement`, assembled from the first, the four `_of_modelUniqueness` conjuncts above with `spaceLimitModelUniqueness`, and the three proved conjuncts | proved (conditional on `ProperSchemeCoverStatement`, resp. on it and `RepresentedAtlasEffectivityStatement`; both are proved, by `properSchemeCover` and `representedAtlasEffectivity`, and `spaceLimitPropertyDescent` (module `SpaceLimitPropertyDescentProof`) is `spaceLimitPropertyDescent_of_foundations representedAtlasEffectivity properSchemeCover`; supporting modules in the constructions paragraph below) |
| Thm 3.4(2) for spaces, flat and dimension (Task 5302) | `RelativePureFibreDimensionDescentStatement` (`SchemePureFibreDimensionDescent`) | scheme form of the pure-dimension condition alone: every `d`; cofiltered limits of affine schemes mapping compatibly to a fixed scheme `S`; `f : X → Y` over `S` locally of finite presentation, quasi-compact and quasi-separated, `Y` quasi-compact and quasi-separated over `S`; every fibre over the limit has pure dimension `d` iff every fibre over some stage has; no nonemptiness or connectedness of fibres | proved (`relativePureFibreDimensionDescent`) |
| Thm 3.4(2) for spaces, flat and dimension (Task 5302) | `spaceLimitFlatnessDescends` (`SpaceLimitFlatnessDescentStatement`, module `SpaceLimitFlatnessDescent`); `spaceLimitPureFibreDimensionDescends` (`SpaceLimitPureFibreDimensionDescentStatement`, module `SpaceLimitPureFibreDimensionDescent`) | the hypotheses of `SpaceLimitPropertyDescends`: cofiltered limits of affine schemes; source and target quasi-separated with a `LocallyOfFinitePresentation ⊓ QuasiCompact` atlas; the first is the flatness conjunct of `SpaceLimitFlatnessDimensionDescentStatement`; the second descends `HasPureFibreDimension d` for every `d`, with no nonemptiness or connectedness of fibres | proved |
| Thm 3.4(2) for spaces, flat and dimension (Task 5302) | `etalePureFibreDimensionComparison` (`EtalePureFibreDimensionComparisonStatement`, module `SchemeEtalePureFibreDimension`) | arbitrary schemes and every `d`; local finite type together with pure fibre dimension `d` holds for `p ≫ f` iff it holds for `f` when `p` is étale and surjective, and for `f ≫ g` iff for `f` when `g` is étale | proved |
| Thm 3.4(2) for spaces, flat and dimension (Task 5302) | `SpaceLimitFlatnessDimensionReductionStatement`, `spaceLimitFlatnessDimensionReduction` (`SpaceLimitFlatnessDimensionReduction`) | the geometrically-connected-fibres conjunct `SpaceLimitPropertyDescends (fun f => HasGeometricallyConnectedFibres f)` of `SpaceLimitPropertyDescentStatement` (Task 5278; `HasGeometricallyConnectedFibres` asks for nonempty connected fibres over every field point) implies `SpaceLimitFlatnessDimensionDescentStatement`, under its original hypotheses | proved (reduction; its premise is proved by `spaceLimitGeometricallyConnectedFibresDescent`, and `spaceLimitFlatnessDimensionDescent` applies it to that theorem) |
| Lem 5.1 (Task 5252) | `SchemeGeometricComponentCountConstructibleStatement` (`SchemeGeometricComponentCountStatement`) | scheme specialization: any commutative ring `B`; a scheme morphism `X → Spec B` locally of finite presentation, quasi-compact and quasi-separated; every `n : ℕ`; the number of connected components of the fibre over an algebraic closure of each residue field, counted in `ℕ∞` | proved (`schemeGeometricComponentCountConstructible`, module `SchemeGeometricComponentCountProof`, with `SchemeGeometricComponentCountBaseChange`) |
| Lem 5.1 (Task 5252) | `geometricFibreComponentsConstructibleStatement_iff`, `geometricFibreComponentCount_ne_top` (`GeometricFibreComponentGeometry`) | restatement of `GeometricFibreComponentsConstructibleStatement` through the count `geometricFibreComponentCount`; the count is finite for `X` finitely presented over `B` | proved |
| Lem 5.1 (Task 5252) | `exists_open_geometricComponentsEquiv`, `exists_open_geometricFibreComponentCount` (`GenericGeometricComponents`) | the first: an irreducible Noetherian base scheme `S`; `X` quasi-separated with an étale surjective atlas whose structure morphism is locally of finite type and quasi-compact; there is a nonempty open subset of `S` over which the sets of connected components of the geometric fibres, for the point topology, are pairwise in bijection; the second: the same over `Spec B` for a Noetherian ring `B` with irreducible spectrum, where `geometricFibreComponentCount` is constant on a nonempty open; this is the generic step of the Noetherian induction and does not prove constructibility | proved |
| Prop 5.4, manifold (Task 5259) | `canonicalAnalyticPointStructure`, `canonicalAnalyticPointStructure_isAnalytic` (`SmoothSpaceAnalyticAtlas`); `canonicalAnalyticPointStructure_isFunctorial`, `canonicalAnalyticPointStructure_isEtaleLocalIso` (`AnalyticPointFunctoriality`); `canonicalAnalyticPointStructure_agreesWithAffineSpace`, `canonicalAnalyticPointStructure_isAdmissible` (`AnalyticAffineNormalization`) | every complete nontrivially normed `K`; the family of charted spaces on `X(K)`, with the étale-chart topology, built from affine étale charts smooth of relative dimension `n`; it satisfies `AnalyticPointStructure.IsAnalytic`, `AnalyticPointStructure.IsFunctorial`, `AnalyticPointStructure.IsEtaleLocalIso` and `AnalyticPointStructure.AgreesWithAffineSpace`, hence `AnalyticPointStructure.IsAdmissible`; this proves the existence conjunct of `AnalyticPointManifoldStatement`; the uniqueness clause is `AnalyticPointStructure.equivalent_of_isAdmissible` (`AnalyticPointUniqueness`), and `analyticPointManifold` combines the two | proved |
| Ex 5.5 (Task 5217) | `StabilizerFibreLocalDimensionStatement` | any scheme `S`; a group scheme `G` locally of finite type over `S` acting on `V`; at every point of the stabilizer scheme (the base change of the action graph along the diagonal of `V`), the local dimension of its fibre over `V` equals the dimension of the whole fibre, so stabilizer fibres are equidimensional; input to the local closedness of the orbit-dimension strata | proved (`stabilizerFibreLocalDimension`, module `StabilizerFibreLocalDimensionProof`, helpers prefixed `StabilizerFibre.`; published for Task 5217; proof Task 5438 `cd13f7dc-f2dc-404b-bf3d-5885e82f23bf`, closed) |
| Ex 5.5 (Task 5217) | `OrbitStratumActionRestrictionStatement` | any field `k`; `G` smooth over `k`; `V` locally of finite type with a `G`-action; a reduced scheme `Z` with an immersion onto the points of orbit dimension `d`; the action restricts to `Z`, and every restricted action has orbit dimension `d` at every point | proved (`orbitStratumActionRestriction`, module `OrbitStratumActionRestrictionProof`, helpers prefixed `OrbitStratumActionRestriction.`; published for Task 5217; proof Task 5435 `50f16a97-abde-4fa4-82d0-f13ffe281ff4`, closed) |
| Ex 5.5 (Task 5217) | `UnipotentOrbitStabilizerSmoothStatement` | field `k` of characteristic zero; `G` affine, locally of finite type and unipotent; `Z` reduced, locally of finite type, with a `G`-action of constant orbit dimension `d`; the stabilizer scheme is smooth over `Z`, which is stronger than the flatness in the source (route through Cartier's theorem instead of Conrad's `exp(ker B)`) | open (published for Task 5217; proof Task 5434 `0e823d86-9f22-48da-b160-eebc1c0160a0`, executors Workers 4246 and 156); it follows from `Langlands.GroupScheme.ReducedBaseConnectedFibreSmoothStatement` (Task 5706) alone, by the reduction and the proved connectedness statement in the rows below |
| Ex 5.5 (Task 5434) | `Langlands.GroupScheme.ReducedBaseConnectedFibreSmoothStatement` (module `Langlands/GroupScheme/ReducedBaseSmoothStatement`) | SGA 3, Exposé VI_B, Corollaire 4.4, over a reduced base with connected fibres: `S` reduced and locally Noetherian; a group scheme `H` over `S`, locally of finite type, whose fibres over the residue fields are smooth and connected, with fibre dimension locally constant on `S`; then `H → S` is smooth | open (published for Task 5434; proof Task 5706 `0804c1fb-2875-4d0a-90cd-e85198e6e762`, no executor) |
| Ex 5.5 (Task 5434) | `Langlands.GroupScheme.CharZeroUnipotentConnectedStatement` (module `Langlands/GroupScheme/Unipotent/CharZeroConnectedStatement`) | Milne, *Algebraic Groups* (2022), Corollary 14.15, in characteristic zero: an affine group scheme locally of finite type over a field of characteristic zero that is unipotent (every nonzero finite-dimensional representation has a nonzero fixed vector) has connected underlying space | proved by the proof-producing `def` `Langlands.GroupScheme.charZeroUnipotentConnected` (module `Langlands/GroupScheme/Unipotent/CharZeroConnectedProof`, with `CharZeroCoordinateConnected`, `CharZeroIdempotents` and `CharZeroPeriodic` in the same folder), whose type is the statement unfolded; published for Task 5434 as a supporting definition, by a route through Cartier's theorem and idempotents of the coordinate ring rather than Milne's component-group argument |
| Ex 5.5 (Task 5434) | `unipotentOrbitStabilizerSmooth_of_reducedBase_of_charZeroConnected` (`UnipotentOrbitStabilizerSmoothReduction`) | the two statements above as hypotheses, in the same universe; conclusion: `UnipotentOrbitStabilizerSmoothStatement` | proved by this proof-producing `def` (conditional on the two statements; the second is proved; published for Task 5434 as a supporting definition) |
| Ex 5.5 (Task 5217) | `SmoothStabilizerActionQuotientStatement` | any scheme `S`; `G` smooth over `S`; `V` locally of finite type with a `G`-action whose stabilizer scheme is smooth over `V`; an fppf quotient algebraic space exists, and every fppf quotient map is smooth and surjective, with quotient locally of finite type over `S` | proved (`smoothStabilizerActionQuotient`, module `SmoothStabilizerActionQuotientProof`, with `SmoothStabilizerActionArrows`, `SmoothStabilizerActionOrbitRelation` and `SmoothStabilizerActionQuotientAssembly`, helpers prefixed `SmoothStabilizerActionQuotient.`; published for Task 5217; proof Task 5433 `f3e32dbc-7b9e-4847-bc34-dcec9466ac74`, closed) |
| Ex 5.5 (Task 5217) | `ActionQuotientFinitenessStatement` | any field `k`; `G` quasi-compact over `k`; `Z` of finite type over `k` with a `G`-action; an fppf quotient `X`, locally of finite type, with smooth surjective quotient map; `X` is quasi-separated and finitely presented over `k` | proved (`actionQuotientFiniteness`, module `ActionQuotientFinitenessProof`, with `ActionQuotientOrbitRelation`, helpers prefixed `ActionQuotientFiniteness.` and `ActionQuotientOrbitRelation.`; published for Task 5217; proof Task 5436 `a0cdf0af-e3dd-43c0-b07c-dd2bc813c384`, closed) |
| Ex 5.5 (Task 5217) | `LocallySeparatedRationalPointsStatement` | henselian nontrivially normed `K`; `X` quasi-separated, locally separated and locally of finite type over `K`; `X(K)` is locally Hausdorff, locally compact if `K` is, and locally totally disconnected if the norm is ultrametric: the corrected topology clause, for every such space rather than only orbit quotients | proved (`locallySeparatedRationalPoints`, module `LocallySeparatedRationalPointsProof`; published for Task 5217; proof Task 5437 `eb46b42e-fe09-4333-8d9d-52ee1549e96a`, closed) |
| Cor 5.6 (Task 5216) | `SpaceValuativeExistenceStatement` | Stacks Project, *Morphisms of Algebraic Spaces*, Lemma 67.42.3 (Tag 0A3Y), (1) ⇒ (3): any base scheme `S`; `f : X → Y` quasi-compact, separated and universally closed; for every valuation ring `A` with fraction field `K` and every `Spec A → S`, a section of `X` over `Spec K` and a section of `Y` over `Spec A` with the same image in `Y` over `Spec K` come from a section of `X` over `Spec A`, without extending `K` | proved (`spaceValuativeExistence`, module `SpaceValuativeExistenceProof`, with `ValuativeExistenceAlgebra`, `ValuativeExistenceTests` and `ValuativeExistenceCore` (declarations prefixed `ValuativeExistence.`); Task 5368 `f5df3c28-7e81-45be-a29a-4abfadf5b153`; a direct route through an étale chart and fppf descent along a faithfully flat finitely presented `A`-algebra, which uses neither the two rows below nor quasi-compactness) |
| Cor 5.6 (Task 5216) | `SpaceValuativeExtensionExistenceStatement`, with the predicate `HasDominatingValuativeLift` (module `DominatingValuativeLift`) | Stacks Project, *Morphisms of Algebraic Spaces*, Lemma 67.42.2(1) (Tag 0A3X) for separated morphisms, with the extension diagram of Definition 67.41.1 (Tag 03IX): any base scheme `S`; `f : X → Y` quasi-compact, separated and universally closed; for every valuation ring `A` with fraction field `K`, every `Spec A → S`, a section `x` of `X` over `Spec K` and a section `y` of `Y` over `Spec A` with the same image in `Y` over `Spec K`, there are a valuation ring `B` with fraction field `L`, a local homomorphism `A → B` and a compatible `K → L`, and a section of `X` over `Spec B` that restricts to `x` over `Spec L` and maps to the restriction of `y` | open (published for Task 5368 `f5df3c28-7e81-45be-a29a-4abfadf5b153`; proof Task 5519 `ec451a4a-51b4-400e-b338-33896df310b0`, no executor); Cor 5.6 no longer depends on it |
| Cor 5.6 (Task 5216) | `SpaceValuativeExtensionDescentStatement` | Stacks Project, *Morphisms of Algebraic Spaces*, Lemma 67.41.4 (Tag 0ARH) for separated morphisms: any base scheme `S`; `f : X → Y` separated; for `A`, `K`, `x`, `y` as in the row above with a lift after a dominating extension (`HasDominatingValuativeLift`), there is a section `a` of `X` over `Spec A` with restriction `x` over `Spec K` and image `y`. With the row above it gives `SpaceValuativeExistenceStatement` (the Stacks route); no Library theorem combines them, and the Library proof of that statement takes another route | open (published for Task 5368; proof Task 5520 `4a9de58f-1a96-464c-998d-fac85af573ef`, no executor); Cor 5.6 no longer depends on it |
| Cor 5.6 (Task 5216) | `LocalFieldProperPointValuativeReductionStatement` | the implication from `SpaceValuativeExistenceStatement` to `LocalFieldProperPointMapStatement`, both in the same universe; the reduction step of the valuative route | proved (`localFieldProperPointValuativeReduction`, module `LocalFieldProperPointValuativeReductionProof`, Task 5483): it is `LocalFieldProperPointLimit.localFieldProperPointMap_of_valuative` (module `LocalFieldProperPointLimit`; helpers in the constructions paragraph below) |
| Cor 5.7 (Task 5218) | `HenselianChartIntegralPointsClosedStatement` | nontrivially normed `K` whose closed unit ball `O` is a henselian local ring; `X` separated, locally of finite type over `O`; for an étale map `U → X` from an affine scheme over `O`, the image of `U(O)` in `X_K(K)` is closed for `etaleChartTopology` | proved (`henselianChartIntegralPointsClosed`, module `HenselianChartIntegralPointsClosedProof`, helpers in `Langlands.AlgebraicGeometry.PointTopology.HenselianUnitBall`; published for Task 5218; proof Task 5416 `1a4f1b69-ca6e-4ade-a6c3-7263a7b20436`, closed) |
| Cor 5.7 (Task 5218) | `UniformFieldPointChartsStatement` | any commutative ring `C`; `X` separated and quasi-compact over `C`; finitely many étale maps from affine schemes to `X` through which every `k`-point of `X` lifts, for every field `k` over `C`; derived from the proofs of Stacks, Tags 0BBN and 07S9 | proved (`uniformFieldPointCharts`, module `UniformFieldPointChartsProof`, helpers prefixed `UniformFieldPointCharts.`; published for Task 5218; proof Task 5417 `cb88a79a-51df-4dba-97b4-6461fda834a1`, closed) |
| Prop 5.8 (Task 5253) | `AdelicSpaceProperStagesStatement` (`CurvePlaceSpaceProperStagesStatement`, `NumberFieldSpaceProperStagesStatement`; module `AdelicSpaceProperInputsStatement`) | separated finite-type spaces over the `S`-integers and a proper morphism `g`; curves need finite `k` and nonempty `S`; number fields allow every finite set of finite places; for every finite level `T` above `S`: `g` is proper on `T`-level points for the stage topologies, and the preimage of the target's `T`-stage range is the source's `T`-stage range | proved (`adelicSpaceProperStages`, module `Langlands/Global/AdelicSpaceProperStagesProof`; Task 5357 `358c8595-c259-43c3-9e07-08aea99faf88`, closed): it applies `adelicSpaceProperStages_of_inputs` (row below) to `localFieldProperPointMap`, `spaceValuativeExistence` and `IsProperMorphism.baseChangeMap` |
| Prop 5.8 (Task 5253) | `AdelicSpaceProperModelStatement` (curve and number-field forms; same module); the conjunction `AdelicSpaceProperInputsStatement` | the data of `AdelicSpaceSpreadProperMapStatement`: separated finite-type models over independent finite sets (nonempty, and finite `k`, for curves) of spaces `Y`, `W` and a proper morphism `g : Y → W`; conclusion: a finite set `T` (nonempty for curves), separated finite-type models over the `T`-integers and a proper model morphism compatible with `g` through generic-fibre isomorphisms | open (`b69c88f1-1a0b-41b1-a7ab-e5566c81799a`; the conjunction has no separate task, and its stages conjunct is proved); it follows from Library theorems: `AdelicSpaceProperModelReduction.adelicSpaceProperModel_of_descent spaceLimitMorphismDescent (spaceLimitProperDescent_of_schemeCovers properSchemeCover)` has its type, but no theorem of this type is published |
| Prop 5.8 (Task 5253) | `AdelicSpaceProperModelReduction.adelicSpaceProperModel_of_descent` (`AdelicSpaceProperModelReduction`) | `SpaceLimitMorphismDescent` (Thm 3.4(1) for spaces) and `SpaceLimitPropertyDescends (fun f => IsProperMorphism f)` (the properness conjunct of `SpaceLimitPropertyDescentStatement`, Task 5278) as hypotheses, in the same universe; conclusion: `AdelicSpaceProperModelStatement`, both forms, with all its hypotheses | proved (conditional on the two descent inputs; the first, `SpaceLimitMorphismDescent`, is proved by `spaceLimitMorphismDescent`; the properness conjunct follows from `spaceLimitProperDescent_of_schemeCovers properSchemeCover`) |
| Prop 5.8 (Task 5253) | `ProperSchemeBaseChangeStatement` (`AlgebraicSpace/`) | Stacks Project, *Morphisms of Algebraic Spaces*, Lemma 40.3 (Tag 04WP), for a change of base scheme: arbitrary schemes `S`, `T` and `g : T → S`; algebraic spaces `X`, `Y` over `S`; for `f : X → Y` proper, `baseChangeMap g f` is proper | proved (`properSchemeBaseChange`, module `ProperSchemeBaseChangeProof`; published for `358c8595-c259-43c3-9e07-08aea99faf88`; proof Task 5498 `c25f29a7-c26d-447f-9fdc-dd9c92f59204`, closed): it is the Library theorem `IsProperMorphism.baseChangeMap` (module `TopologicalMorphismBaseChange`), which holds for every `g` and every proper `f`, without representability |
| Prop 5.8 (Task 5253) | `curvePlaceSpaceStage_isProperMap_of_proper`, `numberFieldSpaceStage_isProperMap_of_proper`, with level and factor forms and the bundled maps `curvePlaceSpaceStageProperMap`, `numberFieldSpaceStageProperMap` (`AdelicSpaceStageProperReduction`) | `LocalFieldProperPointMapStatement` (Cor 5.6) and `ProperSchemeBaseChangeStatement` as hypotheses; `X`, `Y` separated and of finite type over the `S`-integers, `f : X → Y` proper; curves need finite `k` and nonempty `S`; number fields allow every finite set of finite places; for every finite level `T` above `S`, `f` is proper on `T`-stage points for the stage topologies: the properness half of `AdelicSpaceProperStagesStatement` | proved (conditional on the two inputs, both proved: `localFieldProperPointMap` and `properSchemeBaseChange`) |
| Prop 5.8 (Task 5253) | `curvePlaceSpaceStagePreimage_of_valuative`, `numberFieldSpaceStagePreimage_of_valuative` (`AdelicSpaceStagePreimageReduction`) | `SpaceValuativeExistenceStatement` as a hypothesis; `X` separated and of finite type over the `S`-integers, `Y` any algebraic space over them, `f : X → Y` whose base change to the `T`-integers is proper (a hypothesis); curves need finite `k` and nonempty `S`; number fields allow every finite set of finite places; in the adelic points of `X`, the preimage under `f` of the `T`-stage range of `Y` is the `T`-stage range of `X`: the preimage half of `AdelicSpaceProperStagesStatement` at the level `T` | proved (conditional on the valuative criterion, which `spaceValuativeExistence` proves, and on properness after base change) |
| Prop 5.8 (Task 5253) | `curvePlaceSpaceFullLevelPreimage_of_valuative`, `numberFieldSpaceFullLevelPreimage_of_valuative` (`AdelicSpaceFullPreimageReduction`) | `SpaceValuativeExistenceStatement` as a hypothesis; `X` separated and of finite type over the `S`-integers, `Y` any algebraic space over them, `f : X → Y` proper; curves need finite `k` and nonempty `S`; number fields allow every finite set of finite places; in the adelic points of `X`, the preimage under `f` of the image of the `S`-level points of `Y` is the image of the `S`-level points of `X`. This is the preimage clause of `AdelicSpaceProperStagesStatement` with the level ring at `S` (`curvePlaceAdeleLevel`, `numberFieldAdeleLevel`) in place of the stage rings at the levels `T`; properness on level points is not derived | proved (conditional on the valuative criterion, which `spaceValuativeExistence` proves; no Library theorem combines the two) |
| Prop 5.8 (Task 5253) | `AdelicSpaceProperStagesReductionStatement`, `adelicSpaceProperStagesReduction`, with the components `adelicSpaceProperStages_of_inputs`, `curvePlaceSpaceProperStages_of_inputs`, `numberFieldSpaceProperStages_of_inputs` (`AdelicSpaceProperStagesReduction`) | `LocalFieldProperPointMapStatement` (Cor 5.6, Task 5216), `SpaceValuativeExistenceStatement` (Task 5368) and `ProperSchemeBaseChangeStatement` as hypotheses, all in the same universe; conclusion: `AdelicSpaceProperStagesStatement` in both characteristics, with all its hypotheses; the proof pairs the two stage rows above, obtaining properness of the base-changed model morphism from `ProperSchemeBaseChangeStatement` | proved (conditional on the three inputs, all proved: `localFieldProperPointMap`, `spaceValuativeExistence` and `properSchemeBaseChange`; `adelicSpaceProperStages` applies `adelicSpaceProperStages_of_inputs` to the first two and to `IsProperMorphism.baseChangeMap`) |
| Thm 5.9 (Task 5254) | `CompleteFieldSmoothSpacePointOpenStatement` (`CompleteFieldSmoothPointOpenStatement` in `AlgebraicSpace/`) | complete nontrivially normed `K` of any characteristic, archimedean or not; `f : X → Y` smooth (`IsSmoothMorphism`, defined by étale chart squares) between separated algebraic spaces locally of finite type over `K`; `f` is open on `K`-points for `etaleChartTopology` | proved (`completeFieldSmoothSpacePointOpen`, module `CompleteFieldSmoothPointOpenProof`; Task 5359) |
| Thm 5.9 (Task 5254) | `curvePlaceSpaceLevel_isOpenMap_of_smooth`, `curvePlaceSpaceStage_isOpenMap_of_smooth`, `numberFieldSpaceLevel_isOpenMap_of_smooth`, `numberFieldSpaceStage_isOpenMap_of_smooth`, with factor forms (`AdelicSpaceSmoothLocalOpenReduction`) | `CompleteFieldSmoothSpacePointOpenStatement` as a hypothesis; separated finite-type models over the `S`-integers and a smooth model map `f`, with surjective point maps at all but finitely many factors; curves need finite `k` and nonempty `S`; `f` is open on level points and on the points of every larger stage | proved (conditional on the local input, which the row above proves, and the cofinite surjectivity) |
| Thm 5.9 (Task 5254) | `curvePlaceSpaceFactor_eventually_surjective_of_residue_bound`, `numberFieldSpaceFactor_eventually_surjective_of_residue_bound` (`AdelicSpaceResidueComponentSurjectivity`) | algebraic spaces `X`, `Y` over the `S`-integers and `f : X → Y` smooth (`IsSmoothMorphism`); curves need finite `k`; a natural number `d` and a constant `c ≥ 0` with `\|#f⁻¹(x)(κ_v) − q_v^d\| ≤ c·q_v^(d−1/2)` for every place `v ∉ S` (finite places for number fields), where `κ_v` is the residue field with `q_v` elements, and every `κ_v`-point `x` of `Y`; `f` is surjective on points at all but finitely many factors of the level ring, which is the cofinite surjectivity hypothesis of the row above | proved (conditional on the residue estimate) |
| Thm 5.9 (Task 5254) | `curvePlaceSpaceFactor_eventually_surjective_of_uniformLangWeil`, `numberFieldSpaceFactor_eventually_surjective_of_uniformLangWeil`, `curvePlaceSpaceLevel_isOpenMap_of_uniformLangWeil`, `numberFieldSpaceLevel_isOpenMap_of_uniformLangWeil`, with the point lifts `curvePlaceSpacePointLifts_of_uniformLangWeil`, `numberFieldSpacePointLifts_of_uniformLangWeil` (`Langlands/Global/AdelicSpaceUniformModelOpen`) | `SpaceUniformLangWeilStatement` as a hypothesis; the `S`-integers an algebra over `ULift ℤ` with `Spec` map locally of finite type; `Y` quasi-separated (separated for the open-map forms) and of finite type over the `S`-integers, `X` separated and of finite type for the open-map forms; `f : X → Y` separated, quasi-compact, surjective, with geometrically connected fibres, and an étale chart square (`EtaleMorphismChart`) with surjective source chart whose scheme map is smooth of relative dimension `d`; curves need finite `k`, and nonempty `S` for the open-map form; conclusions: `f` is surjective on points at all but finitely many factors of the level ring, and open on level points | proved (conditional on `SpaceUniformLangWeilStatement`) |
| Thm 5.9 (Task 5254) | `curvePlaceCofinalSpaceLevel_isOpenMap_of_uniformLangWeil`, `numberFieldCofinalSpaceLevel_isOpenMap_of_uniformLangWeil`, with the point lifts `curvePlaceCofinalSpacePointLifts_of_uniformLangWeil`, `numberFieldCofinalSpacePointLifts_of_uniformLangWeil` (`Langlands/Global/AdelicSpaceCofinalModelOpen`, Worker 109) | the row above at the level `curvePlacePrincipalLevelAbove k F S`, resp. `numberFieldPrincipalLevelAbove K S` (a finite set of places containing the given `S`), with the integer-base premise discharged by `AdelicSpaceIntegerBase`; models given over that level; `SpaceUniformLangWeilStatement` and the other hypotheses of the row above; curves need finite `k`, and nonempty `S` for the open-map form; conclusions: lifts of points at all but finitely many factors of the level ring, and openness on level points | proved (conditional on `SpaceUniformLangWeilStatement`) |
| Lem 5.10 (Task 5255) | `WeilRestrictionDiagonalStatement` (`WeilRestrictionGeometricInputsStatement`) | `R → R'` finite projective over arbitrary rings; `X'` quasi-separated, no finite type; the presheaf diagonal of the restricted sheaf is representable with quasi-compact represented projections, and a representable closed immersion if `X'` is separated | proved (`weilRestrictionDiagonal_proof`, module `WeilRestrictionDiagonalProof`; `b515d810-988d-4ec8-b2a6-e2623027daae`) |
| Lem 5.10 (Task 5255) | `WeilRestrictionAffineEtaleAtlasStatement` (same module) | as above; an étale surjective map to `X'` from an affine scheme locally of finite type over `R'`; its restriction is étale and geometrically surjective as a map of presheaves over `R` | proved (`weilRestrictionAffineEtaleAtlas`, module `WeilRestrictionAffineEtaleAtlasProof`, from `WeilRestrictionAtlasReduction` and `WeilRestrictionAtlasLocalRepresentation` (declarations prefixed `WeilRestrictionAtlas.`), `TestFibreRepresentation` (prefix `TestFibre.`), `PointTopology/AffineChartWeilRestrictionEtale` and `PointTopology/AffineChartWeilRestrictionSurjective`; Task 5361 `a05a1e93-7568-4b83-9fcd-0dda4caaa068`, closed) |
| Lem 5.10 (Task 5255) | `spaceWeilRestriction_of_geometricInputs` (`SpaceWeilRestrictionReduction`) | the two statements above imply `SpaceWeilRestrictionStatement` | proved (reduction) |
| Lem 5.10, scheme cases | `affineWeilRestriction_isAlgebraicSpace`, `affineWeilRestriction_finiteType` (`SchemeWeilRestrictionComparison`); `quasiAffineWeilRestriction_isAlgebraicSpace`, `quasiAffineWeilRestriction_finiteType`, `quasiAffineWeilRestriction_isSeparated`, `quasiAffineWeilRestriction_isQuasiSeparated` (`QuasiAffineWeilRestrictionComparison`) | `R → R'` finite projective; an affine, resp. quasi-affine, scheme locally of finite type over `R'`: its Weil restriction sheaf is an algebraic space of finite type over `R`; in the quasi-affine case also separated and quasi-separated | proved |
| Prop 5.11(1), corrected (Task 5320) | `isHomeomorph_ringWeilRestrictionBasePointsEquiv`, `ringWeilRestrictionPointHomeomorph` (`WeilRestrictionPointComparison`) | henselian nontrivially normed `K`, `K'`, `K'` a finite-dimensional `K`-algebra with continuous scalar multiplication (`ContinuousSMul K K'`; no norm compatibility) and `IsModuleTopology K K'`; `Y'` quasi-separated, locally of finite type; given that the Weil restriction sheaf is an algebraic space that is quasi-separated and locally of finite type over `K`, the canonical point bijection is a homeomorphism for the étale-chart topologies | proved (conditional on the given representability and finiteness, which Lemma 5.10 supplies for `Y'` of finite type in the proof of the corrected Prop 5.11(1)) |
| Prop 5.11(3) (Task 5258) | `isEmbedding_henselianExtensionPointMap`, `henselianExtensionPointHomeomorphRange` (`HenselianNormedExtensionEmbedding`) | henselian nontrivially normed `K` and `L`, `L` a normed `K`-algebra of any degree and transcendence degree; `X` separated, quasi-separated and locally of finite type; `X(K) → X_L(L)` is an embedding for the étale-chart topologies | proved |
| Prop 5.11(3) (Task 5258) | `ExtensionLocalReduction.isEmbedding_of_covered`, `ExtensionLocalReduction.isClosed_range_of_separated_open`, `ExtensionLocalReduction.coveredHenselianExtensionPointHomeomorphRange` (`HenselianExtensionLocalReduction`) | the hypotheses of `HenselianExtensionPointEmbeddingStatement`; the first is its embedding conjunct; the second shows that the image of `X(K)` is closed if the image is closed for every separated open subspace | proved (the embedding conjunct, and a reduction of the closedness conjunct) |
| Prop 5.11(3) (Task 5258) | `ExtensionClosedRange.isClosedEmbedding_of_finite_galois`, `ExtensionClosedRange.isClosed_range_of_finite_galois` (`FiniteGaloisExtensionPointTopology`) | henselian nontrivially normed `K` and `L`, `L` a normed `K`-algebra, finite-dimensional and Galois over `K`; `X` separated, quasi-separated and locally of finite type; `X(K) → X_L(L)` is a closed embedding for the étale-chart topologies | proved (closed embedding for separated `X` and finite Galois `L/K`) |
| Prop 5.11(3) (Task 5258) | `CompleteExtensionPointClosedRangeStatement` | complete nontrivially normed `K` and `L`, `L` a normed `K`-algebra of any degree and transcendence degree; `X` quasi-separated, locally of finite type and separated; the image of `X(K)` in `X_L(L)` is closed for the étale-chart topology | proved (`CompleteExtensionClosedRange.completeExtensionPointClosedRange`, module `CompleteExtensionPointClosedRangeProof`, helpers prefixed `CompleteExtensionClosedRange.`; published for Task 5258; proof Task 5487 `621e8df6-800c-49a9-98b6-26561c38ce54`, closed) |
| Prop 5.11(3) (Task 5258) | `ExtensionClosedReduction.isClosed_range_of_complete`, `ExtensionClosedReduction.henselianExtensionPointEmbedding_of_complete` (`HenselianExtensionClosedReduction`) | `CompleteExtensionPointClosedRangeStatement` as a hypothesis; the first: any nontrivially normed `K`, a henselian nontrivially normed `L`, `L` a normed `K`-algebra with the image of `K` closed in `L`, `X` quasi-separated, locally of finite type and separated; the image of `X(K)` in `X_L(L)` is closed; the second: `HenselianExtensionPointEmbeddingStatement` with all its hypotheses | proved (conditional on `CompleteExtensionPointClosedRangeStatement`, which is proved; `henselianExtensionPointEmbedding` applies the second to `CompleteExtensionClosedRange.completeExtensionPointClosedRange`) |
| Prop 5.11(3) (Task 5258) | `UniformEtaleChartInjectivityStatement` | any nontrivially normed `K`; `X` separated; an étale map to `X` from an affine scheme locally of finite type; finitely many regular functions give uniform injectivity on bounded coordinates over every normed extension `L/K`, of any degree | proved (`uniformEtaleChartInjectivity`, module `UniformEtaleChartInjectivityProof`) |
| Prop 5.11, proof (p.19) | `CompleteFiniteExtensionPointEmbeddingStatement`, `henselianFiniteExtensionPointEmbedding_of_complete` (`FiniteExtensionPointEmbeddingReduction`) | complete `K` and `L`, `L` finite-dimensional over `K`; `X` quasi-separated, locally separated, locally of finite type; the reduction derives the henselian statement from the complete one | reduction proved; the complete statement is open without a task, and the row it served is proved directly |

Published constructions and supporting lemmas without statements of their own also support open
rows: for Theorem 5.9
(Task 5254), `AdelicSpaceModelOpenReduction`, `CoordinatePointOpenMap`,
`HenselianSmoothPointLifting`, `UniformLangWeilFiniteFieldLifts`,
`AlgebraicSpace/UniformLangWeilHenselianLifts` and `OriginalBaseUniformLangWeilLifts`
(declarations prefixed `OriginalBaseUniformLangWeilLifts.`; the last three assume
`SpaceUniformLangWeilStatement`), and `BaseCompositionPresheaf`, `BaseCompositionSheaf`,
`BaseCompositionGeometry`, `BaseCompositionProperties`, `BaseCompositionDiagonal`,
`BaseCompositionFibres`, `BaseCompositionPoints` and `BaseCompositionRingPoints` (declarations
prefixed `BaseComposition.`; Worker 109), and `Langlands/Global/AdelicSpaceIntegerBase`
(declarations prefixed `AdelicSpaceIntegerBase.`; local finite type of `Spec.algebraMap (ULift ℤ) C`
for the `S`-integers `C` of a principal level containing any given finite set of places, the
integer-base premise of the Theorem 5.9 row of the `_of_uniformLangWeil` theorems),
`SmoothRelativePointDimension`, `SmoothDimensionOpenSubspaces`, `SmoothDimensionRestrictions` and
`SmoothDimensionFinitePresentation` (declarations prefixed `EtaleMorphismChart.`,
`PointOpenSubspace.` or `SmoothTargetPointDimensions.`, with the structure
`SmoothTargetPointDimensions` and its construction `smoothTargetPointDimensions`; the relative
dimension of a smooth morphism as a locally constant function with finitely many values on the
target points, the open subspaces of source and target over each value, and atlases of finite
presentation on them), `SmoothDimensionModelGeometry` (declarations prefixed
`SmoothTargetPointDimensions.`; the restricted map over each value has nonempty geometrically
connected fibres and is surjective when the original map has such fibres, is separated when the
source is, and, over affine `S`, is quasi-compact when the source has a
`LocallyOfFinitePresentation ⊓ QuasiCompact` atlas and the target is quasi-separated;
`restrictedMap_fixedDimensionChart`: for a smooth map of spaces with such atlases over an affine
locally Noetherian base, with quasi-separated target, a commuting chart square of affine schemes
locally of finite presentation, with surjective étale chart maps, whose scheme map is smooth of
relative dimension equal to that value), and
`Langlands/Global/AdelicSpaceSmoothModelGeometry` and `Langlands/Global/AdelicSpaceSmoothModelProperties`
(declarations prefixed `AdelicSpaceSmoothModelGeometry.`; smooth models with nonempty
geometrically connected fibres over a ring of integers of a smooth morphism with such fibres over
the global field; Worker 109); for
Proposition 5.8 (Task 5253),
`AdelicSpaceCoordinateProperReduction` (declarations prefixed `AdelicSpaceProperReduction.`),
`Langlands/Global/AdelicSpacePreimageAssembly` (namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.AdelicSpacePreimageAssembly`), and
`FibreRestrictionTopology` and `CommonAtlasPointTopology`, on which `TopologicalMorphismBaseChange`
(row of `ProperSchemeBaseChangeStatement`) builds. Their Markdown states what each provides;
none proves an open row.

Further published constructions and supporting lemmas support rows that are now proved. For
Proposition 5.14 (Task 5257): `AdelicSpaceWeilRestrictionPoints`,
`AdelicSpaceStageComparison` (with `Langlands/Topology/FinalStageComparison`),
`SpaceWeilRestrictionBaseChange`, `SpaceWeilRestrictionTensorBaseChange`,
`SpaceFiniteProductSections`, `SpaceWeilRestrictionFiniteProduct`, `EtaleChartFiniteProducts`,
`WeilRestrictionFiniteProductTopology`, `SpaceWeilRestrictionTensorPoints`,
`SpaceWeilRestrictionTensorPointBaseChange`, `SpaceWeilRestrictionFiniteProductBasePoints`
(declarations prefixed `WeilRestrictionFiniteProduct.`), `SpaceWeilRestrictionTensorPointEquiv`,
`SpaceWeilRestrictionTensorTopology` (declarations prefixed `WeilRestrictionTensorTopology.`;
its `WeilRestrictionTensorTopology.isHomeomorph_completedTensorSpaceWeilRestrictionPointMap`
proves that the local tensor comparison map `completedTensorSpaceWeilRestrictionPointMap` is a
homeomorphism for the field-valued point topologies, for a nontrivially normed field `C` and a
finite family of nontrivially normed fields `D i`, each a finite-dimensional `C`-algebra with
continuous scalar multiplication (`ContinuousSMul C (D i)`; no norm compatibility) carrying its
`C`-module topology (`IsModuleTopology C (D i)`), with a `C`-algebra equivalence
`C ⊗_R B ≅ ∏ D i` compatible with the maps from `B`, assuming algebraicity of the Weil
restrictions, henselian valued-field conditions on `C` and every `D i`, and quasi-separated
local finite type of the factor and Weil spaces; the module-topology hypothesis holds for
complete `C` and is not implied by henselianity, as the correction to Proposition 5.11(1) above
shows; `C` is not assumed complete despite the word "completed" in the name) and
`SpaceWeilRestrictionTensorIntegralTopology` (whose
`WeilRestrictionTensorTopology.isHomeomorph_completedTensorSpaceWeilRestrictionPointMap_integral`
transfers the comparison to commutative rings `C` and `D i`, such as completed valuation rings:
given `R`-algebra maps `C → C'` and `B`-algebra maps `D i → D' i` to fields with arbitrary
topologies, compatible with the algebra maps `C → D i` and `C' → D' i`, and tensor
decompositions `C ⊗_R B ≅ ∏ D i` and `C' ⊗_R B ≅ ∏ D' i` compatible with the maps from `B`, the
integral map is a homeomorphism for the topologies induced through these maps, assuming
algebraicity of the Weil restriction and that the field map over `C'` is a homeomorphism),
`SpaceWeilRestrictionTensorFiniteTypeTopology` (whose
`WeilRestrictionTensorTopology.isHomeomorph_completedTensorSpaceWeilRestrictionPointMap_finiteType`
proves the field comparison above for `X` quasi-separated and of finite type over `B`, obtaining
the algebraicity of the factor Weil restrictions and the geometric premises from Lemma 5.10; it
keeps as hypotheses the algebraicity of the Weil restriction of `X`, the henselian conditions on
`C` and every `D i`, continuous scalar multiplication, `IsModuleTopology C (D i)` and the tensor
decomposition compatible with the maps from `B`), `SpaceWeilRestrictionEvaluation`
(`spaceWeilRestrictionEvaluation` evaluates a point over an `A`-algebra `R` of the Weil
restriction of `X`, assumed algebraic, along a ring map `R → D` to a `B`-algebra compatible with
the maps from `A`, by pulling back along the original evaluation test map;
`spaceWeilRestrictionEvaluation_natural_lower` and `spaceWeilRestrictionEvaluation_natural_upper`
give its naturality in `R` and in `D`; `completedTensorSpaceWeilRestrictionPointMap_eq_evaluation`
and `ringWeilRestrictionPointsEquiv_eq_evaluation` identify the components of the local tensor
comparison, and the Weil point equivalence followed by a `B`-algebra map, with this evaluation),
and the arithmetic specializations
`Langlands/Global/NumberFieldSIntegerSpaceWeilTopology` and
`Langlands/Global/CurvePlacePrincipalSIntegerSpaceWeilTopology` (declarations prefixed
`NumberFieldSIntegerSpaceWeilTopology.` and `CurvePlacePrincipalSIntegerSpaceWeilTopology.`;
for `X` quasi-separated and of finite type over the `S'`-integers of `L`, `S'` the full preimage
of `S`, with its Weil restriction to the `S`-integers of `K` assumed algebraic, they identify the
points of the Weil restriction over the completion `K_v` with the product of the points of `X`
over the completions of `L` above `v`, and, for finite places `v` outside `S`, the same over the completed
valuation rings, with the field-valued and induced topologies; number fields: any extension
`L/K` of number fields, any finite set `S` of finite places, finite and infinite places `v`;
curves: finite `k`, a function field `K` over `k`, a finite extension `L/K`, and `S` the
principal exceptional set `curvePlacePrincipalExceptional k K s t` of an element `s` with `K`
finite over `k(s)` and a nonzero `t` of the curve chart ring), the stage coordinates
`Langlands/Global/AdelicSpaceStageCoordinates` and `Langlands/Global/CurvePlaceSpaceStageCoordinates`
(`fieldValuedBaseChangeHomeomorph`: after a base change `C → C'`, the points with the
field-valued topology along a `C'`-algebra map to a topological field are homeomorphic to the
original points with the field-valued topology along the same map viewed over `C`;
`AdelicSpaceStageCoordinates.numberFieldStageHomeomorph` and
`AdelicSpaceStageCoordinates.curveStageHomeomorph`: for `X` separated and of finite type over the
`S`-integers and any finite support `T` containing `S`, the `T`-stage of the adelic points of `X`
with its stage topology is homeomorphic to the product of the points of `X` over the original
factors of the `T`-level (the completions at the infinite places for number fields and at the
places in `T`, and the completed valuation rings at the other places), each with its
field-valued topology; curves need finite `k` and nonempty `S`), and the fixed-model Weil
comparisons `Langlands/Global/NumberFieldSIntegerSpaceFixedLevelWeil`,
`Langlands/Global/NumberFieldSIntegerSpaceFixedLevelRegroup`,
`Langlands/Global/CurvePlacePrincipalSIntegerSpaceFixedLevelWeil` and
`Langlands/Global/CurvePlacePrincipalSIntegerSpaceFixedLevelRegroup` (declarations prefixed by
the module names; for `X` quasi-separated and of finite type over the `S'`-integers of `L`, with
its Weil restriction `W` to the `S`-integers of `K` assumed algebraic, separated and of finite
type, `levelPointHomeomorph` identifies each `T`-stage of `W` with the product of the points of
`X` over the original completions and completed valuation rings of `L` above the factors of the
`T`-level; for `X` moreover separated, `adelicLevelPointHomeomorph` identifies the `T`-stage of
`W` with the stage of `X` at the full preimage of `T`, both with their stage topologies, and
`adelicLevelPointHomeomorph_coordinates` gives its coordinates as the regrouped local Weil
comparisons; number fields: any extension `L/K` of number fields and any finite set `S` of
finite places; curves: as above, with nonempty principal exceptional set, and inseparable
extensions allowed), the fixed-model evaluations
`Langlands/Global/NumberFieldSpaceFixedModelWeilEvaluation` and
`Langlands/Global/CurvePlaceSpaceFixedModelWeilEvaluation` (declarations prefixed by the module
names; for `X` separated and of finite type over the upper integral base, with its Weil sheaf
assumed algebraic and the Weil space assumed separated and of finite type,
`adelicLevelPointHomeomorph_eq_evaluation` identifies the stage homeomorphism
`adelicLevelPointHomeomorph` with `spaceWeilRestrictionEvaluation` along the level inclusion
`levelInclusion`, `adelicEvaluation` evaluates the Weil counit along the full adele inclusion,
and `adelicEvaluation_stage` relates it to the stage homeomorphisms; curves need finite `k`, a
finite extension `L/K` with a function-field structure on `L`, and nonempty `S`) and
`Langlands/Global/NumberFieldSpaceFixedModelWeilHomeomorph`
(`NumberFieldSpaceFixedModelWeilHomeomorph.adelicPointHomeomorph`: under the same inputs, for
number fields `L/K` and a finite set `S` of finite places of `K`, the adelic points of the Weil
space over the adeles of `K` are homeomorphic to the adelic points of `X` over the adeles of
`L`, both with their final stage topologies, with forward map `adelicEvaluation`; one fixed
integral model, without comparison of models), together with
`Langlands/Global/CurvePlaceSpaceFixedModelWeilHomeomorph`
(`CurvePlaceSpaceFixedModelWeilHomeomorph.adelicPointHomeomorph`, the curve-place analogue of
the number-field homeomorphism just described), the generic-fibre comparisons
`Langlands/Global/NumberFieldSpaceWeilGenericFiber` and
`Langlands/Global/CurvePlaceSpaceWeilGenericFiber` (declarations prefixed by the module names;
`genericFiberIso` identifies the generic fibre of the integral Weil model with the Weil
restriction of the generic fibre of `X`, and `adelicPointHomeomorphOfIso` gives, for a space `Y`
with a specified isomorphism from the generic fibre of `X`, a homeomorphism between the adelic
points of the Weil restriction of `Y` and the adelic points of `Y`, with the spread topologies of
these models and with the canonical point bijection as forward map), and
`SpaceWeilRestrictionBaseChangeEvaluation` (`spaceWeilRestrictionEvaluation_baseChange`: the
evaluation `spaceWeilRestrictionEvaluation` commutes with the cartesian Weil comparison under a
change of base). For Corollary 5.6 (Task 5216, proved by Task 5483): `LocalFieldProperPointLimit`
(declarations prefixed `LocalFieldProperPointLimit.`; its
`localFieldProperPointMap_of_valuative` is the reduction of the row of
`LocalFieldProperPointValuativeReductionStatement`), `ChartFibreProduct` (declarations prefixed
`ChartFibre.`; `ChartFibre.space`: for `f : X → Y` separated and quasi-compact and a map to `Y`
from an affine scheme `V` separated over the base, the fibre product `X ×_Y V` as an algebraic
space), `RingPointsSmall` (`RingPointsSmall.small_ringPoints`: for a quasi-separated algebraic
space over a field `K` with an affine étale surjective atlas, the type of `K`-points is small),
`PointTopology/ConvergentGermsHenselian` (`convergentGerms_henselian`: for a nontrivially normed,
locally compact and complete field `K` and an ultrafilter `𝒰`, the convergent germs of the
ultrapower, the elements with a limit along `𝒰`, form a henselian local ring) and
`PointTopology/UltrapowerSpreading` (`exists_ultrafilter_lift`: an ultrafilter lifts to a
set-theoretic fibre product of maps `F` and `D`, with convergent second projection, if `F` tends
to `D b₀` along it and `D` maps neighbourhoods of `b₀` to neighbourhoods of `D b₀`;
`exists_stage_ringPoint`: for a field `K`, an ultrafilter `𝒰` on `I` and an `(I → K)`-algebra `L` whose algebra map is surjective with kernel
the families that vanish `𝒰`-eventually, every `L`-point of a scheme locally of finite
presentation over `Spec (I → K)` comes from a stage `(I → K) ⧸ vanishing K A` with `A ∈ 𝒰`).
For Proposition 5.11(3) (Task 5258): `ExtensionPointMap`, `PointTopology/FiniteExtensionCompletion` and
`HenselianExtensionCompletionReduction` (declarations prefixed `ExtensionCompletionReduction.`;
descent of points through the completions when the image of `K` in `L` is closed). For Theorem
3.4(2) for spaces (Task 5278): `ConnectedStructuralFibres` (whose
`hasGeometricallyConnectedFibres_structural_iff_componentCount` shows that, for `X` with a
`LocallyOfFinitePresentation ⊓ QuasiCompact` atlas over `Spec B`, the structure morphism has
nonempty geometrically connected fibres iff the geometric fibre component count of Lemma 5.1 is
`1` at every point), `SchemeTargetRebase` (declarations prefixed `SchemeTargetRebase.`; a space
with a morphism to a scheme `V` viewed as a space over `V`, with its atlas and finiteness),
`SchemeTargetConnectedFibres` (whose `SchemeTargetRebase.hasGeometricallyConnectedFibres_iff`
shows that a morphism to the space represented by `V` has nonempty geometrically connected fibres
iff the structural morphism of its rebase over `V` has), `AffineTargetFamily` (declarations
prefixed `AffineTargetFamily.`; the space over a target chart `V` obtained by pulling `f` back
along the chart and rebasing over `V`; over affine `S` and `V` it is quasi-separated if `X` is,
and has a `LocallyOfFinitePresentation ⊓ QuasiCompact` atlas if `X` and `Y` have one, `Y` is
quasi-separated and `V` is locally of finite presentation over `S`; for a surjective étale
chart, `f` has nonempty geometrically connected fibres iff the family's structure morphism has,
and, under these finiteness hypotheses with `V = Spec B`, iff the geometric fibre component
count of the family is `1` at every point), `ConnectedFibreLocus` (`connectedFibreLocus X`, the set of points
of the base at which the geometric fibre component count of Lemma 5.1 is `1`; for `X` with a
`LocallyOfFinitePresentation ⊓ QuasiCompact` atlas, the structure morphism after any base change
`g` has nonempty geometrically connected fibres iff the count is `1` at every point of the image
of `g`; over an affine base, with `X` moreover quasi-separated, every level set of the count is
constructible; `structuralConnectedFibres_iff_eventually`: along a cofiltered limit of affine
schemes, the structure morphism of `X` base-changed to the limit has nonempty geometrically
connected fibres iff it has at some stage), `AffineTargetFamilyBaseChange`
(`structuralBaseChangeFibreHomeomorph` and `AffineTargetFamily.testFibreHomeomorph`:
homeomorphisms of the fibres of a base-changed structure morphism and of the family over a target
chart with the original fibres), `AffineTargetFamilyConnectedBaseChange`
(`AffineTargetFamily.hasGeometricallyConnectedFibres_baseChange_iff`: for a surjective étale
target chart, the base change of `f` along any scheme map has nonempty geometrically connected
fibres iff the structure morphism of the base-changed family has), the lemmas
`AffineTargetFamily.connectedFibreLocusOver`, `AffineTargetFamily.isConstructible_connectedFibreLocusOver`
and `AffineTargetFamily.hasGeometricallyConnectedFibres_iff_locus_eq_univ` of
`SpaceLimitConnectedFibresDescent` (the module of the proved geometrically-connected-fibres
conjunct), `SpaceMorphismPointMap`,
`GeometricFibreFieldTests` and `ConnectedFibreTargetAtlas` (nonempty geometrically connected
fibres tested on algebraically closed fields and on a surjective étale target chart),
`TopologicalMorphismBaseChange` (whose `HasGeometricallyConnectedFibres.baseChangeMap` preserves
nonempty geometrically connected fibres under any change of base scheme), `RelativeDiagonalCharts`,
`RepresentedSchemeFiniteness`, `LimitSchemeRepresentation` (whose eventual scheme
representation at a stage assumes `SpaceLimitModelUniqueness`, the model-uniqueness half of
`SpaceLimitUniquenessStatement`, now proved by `spaceLimitModelUniqueness`),
`LimitRepresentedPullback` and `TargetAtlasLimitDescent`
(declarations prefixed `SchemeTargetAtlas.`), `UniversallyClosedSourceCover`
(`IsUniversallyClosedMorphism.of_surjective_comp`: for maps `a : W → X` and `f : X → Y` of
algebraic spaces with `a` surjective on represented scheme pullbacks, universal closedness of
`a ≫ f` implies that of `f`; `isUniversallyClosed_structural_of_scheme_cover`: the structure
morphism of `X` is universally closed if a surjective map onto `X` from a scheme with
universally closed structure morphism is given, whose existence it does not assert;
`isUniversallyClosedMorphism_of_relative`: a morphism whose represented scheme pullbacks are
universally closed satisfies the point-topology predicate), `UniversallyClosedTargetAtlas`
(`IsUniversallyClosedMorphism.of_isPullback`: universal closedness is preserved in cartesian
squares of algebraic spaces; `isUniversallyClosedMorphism_iff_targetAtlas`: it can be tested
after pulling back along a surjective étale map from a scheme to the target) and
`RepresentedSurjectivityLimitDescent` (`isSurjective_limit_iff_of_representable`: along a
cofiltered limit of affine schemes, for quasi-separated spaces with a
`LocallyOfFinitePresentation ⊓ QuasiCompact` atlas over a stage and a morphism `f` between them
assumed representable at that stage, `f` is surjective on represented scheme pullbacks after
base change to the limit iff it is after base change to some stage mapping to the given one;
`spaceLimitRelativePropertyDescent_of_representable`: the same for any scheme property stable under base change, descending along étale surjections and satisfying
scheme structural limit descent; the representability hypothesis is not removed),
`ProperSchemeStageModel` (`exists_properSchemeStageModel`: a scheme proper over the limit of a
cofiltered diagram of affine schemes, with structure morphism locally of finite presentation,
quasi-compact and quasi-separated, has a model at some stage that is proved proper and locally of
finite presentation, with a cartesian square; the structure `ProperSchemeStageModel` records
these data), `ProperSchemeCoverDescent` (`ProperSchemeCoverAtStage`: a scheme over a stage that
is proper and locally of finite presentation, with a surjective map to the base change of `X` to
that stage; `exists_properSchemeCoverAtStage_of_limit_cover`: for affine `S` and `X`
quasi-separated with a `LocallyOfFinitePresentation ⊓ QuasiCompact` atlas, a given cover of this
kind over the limit descends to some stage; `exists_structuralUniversallyClosed_of_properSchemeCover`:
assuming `ProperSchemeCoverStatement`, if the structure morphism of the base change of `X` to the
limit is proper, then the structure morphism of its base change to some stage is universally
closed), `SchemeTargetUniversallyClosed` (`SchemeTargetRebase.isUniversallyClosedMorphism_iff`:
a morphism to the space represented by a scheme `V` is universally closed iff the structure
morphism of its rebase over `V` is; `SchemeTargetRebase.isProperMorphism`: properness passes to
the rebase for affine `S` and `V`, `V` locally of finite type over `S`, and `X` with a
`LocallyOfFinitePresentation ⊓ QuasiCompact` atlas; `AffineTargetFamily.isUniversallyClosedMorphism_iff`:
for a surjective étale target chart, `f` is universally closed iff the structure morphism of the
family over the chart is; `AffineTargetFamily.isProperMorphism_structural`: a proper `f` gives a
proper structure morphism of the family over an affine chart `V` locally of finite presentation
over affine `S`, for `X` and `Y` with such atlases and `Y` quasi-separated) and
`AffineTargetFamilyUniversallyClosedBaseChange`
(`AffineTargetFamily.isUniversallyClosedMorphism_baseChange_iff`: for a surjective étale target
chart, the base change of `f` along any scheme map is universally closed iff the structure
morphism of the base-changed family is), on which `SpaceLimitProperDescentOfSchemeCovers` (row
of its conditional theorems) builds. For
`FamilyPointUpperBoundStatement` (Task 5405):
`LangWeil/FiniteAlgebraPointBound` (`exists_uniform_card_algHom_le`: a module-finite algebra over
a commutative ring has a uniformly bounded finite number of algebra maps to every field) and
`LangWeil/FiniteMorphismPointBound` (`exists_uniform_card_finiteMorphism_le`: a finite morphism to
an affine scheme has finite field-valued fibres of uniformly bounded size;
`affineSpacePointEquiv` and `card_affineSpace_fibrePoints`: relative affine `d`-space has exactly
`q^d` points over each point with values in a field with `q` elements), and the counting lemmas
of `LangWeil/NormalizationCoverPointBound` (`affineNormalizationPointEquiv`;
`exists_uniform_card_affineNormalization_le`: for a finite map to relative affine `d`-space over
an affine base there is one `N` such that at most `N·q^d` points lie over each point of the base
with values in a finite field with `q` elements;
`FiniteNormalizationCover.exists_uniform_nat_card_fibrePoints_le`: a given
`FiniteNormalizationCover` of `f` yields the bound `N·q^e` of `FamilyPointUpperBoundStatement`
for `f`; the conditional reduction in the same module has its own row above).
Their Markdown states what each provides.

## Remarks, proof steps and cited facts without separate statements

The following passages are commentary, steps inside proofs, or citations of outside results.
None has its own Lean declaration; each is listed with the reason.

- **Commentary.** Section 1; the comparison with Milnor (p.2); the explanations on pp.5, 8–9
  and 9 of why the topology is not glued from affine opens and why quotient topologies are hard
  to handle without separatedness; the remark on p.14 that the complete case suffices; the
  acknowledgement before the proof of Proposition 5.4; the motivation closing Example 5.5
  (sheaf theory on `(V_d/G)(k)` and smooth representations). Their mathematical content is in
  the rows on basic opens, Theorem 3.6, p.9 and Proposition 5.4.
- **p.10, parenthesis before Example 4.3.** A non-closed subset of a compact Hausdorff space can
  be discrete, such as `{e^{2πi/n} : n ≥ 2}` in the circle. The source indexes by `n ≥ 1`; the
  term for `n = 1` is the accumulation point `1`, so the index must start at `2` for the subset
  to be discrete and non-closed. This illustration from general topology concerns none of the
  paper's objects; it is not stated.
- **Proofs of proved results.** The cited EGA IV results in the proof of Theorem 3.4; Chow's
  lemma and the induction on dimension in the proof of Proposition 4.4; the reduction steps for
  smooth maps before Theorem 4.5; bounded fibre degrees, unramified extensions and torsor
  descent in the proof of Proposition 5.2; the reductions in the proof of Corollary 5.12; the
  reduction to noetherian bases in Lemma 5.1 (carried out by `GeometricComponentApproximation`,
  row Lem 5.1); on p.17, the transfer of the proof of Theorem 3.6 by Corollary 5.7 and of
  Theorem 3.4 to algebraic spaces for the level topologies and the limit bijection (the
  corresponding clauses are proved in `AdelicSpacePointTopologyProof` and its supporting modules,
  row p.17); [LMB, Prop. 1.3], Zariski's Main Theorem and [EGA IV, 18.8.10] in Lemma 5.10;
  Chow's lemma for algebraic spaces in the proof of Corollary 5.6 (the Lean proof uses the
  valuative criterion and an ultrafilter limit instead, row Cor 5.6); on p.19, the reduction of
  Proposition 5.11(3) to complete fields through part (2), the closed immersion
  `j : X → Res_{k'/k}(X_{k'})` for separated `X` in the finite-degree case, and the [CT]
  analytification in the infinite-degree case (the Lean proof takes another route: the embedding
  through the separable closure of `K` in `K'` and Galois descent along Galois extensions of any
  degree, and closedness by reduction to complete fields through the completions of `K` and `K'`
  and the separately proved complete case; rows Prop 5.11(3)). The results are proved in
  the Library, by Lean routes that need not follow these steps.
- **Proofs of open results.** The étale cohomology of
  noetherian algebraic spaces, the trace formula and Deligne's Riemann hypothesis for
  algebraic spaces in Theorem 5.9, which are the inputs of
  `SpaceUniformLangWeilStatement` (`e5531847-70bc-4569-b880-2f90d5815c6a`; the route stated
  there uses Lang–Weil estimates in families instead, intermediate statements above); the flatness
  argument and [Del2, Prop. 3.11] in Example 5.5, the route to the quotient clause of
  `UnipotentOrbitQuotientStatement` (Task 5217 `b7321f08-34a4-4479-b6a5-fc099d504d2d`; its
  intermediate statements above use Cartier's theorem and quotients by actions with smooth
  stabilizers instead). These steps belong to the named proof tasks.
- **Cited facts outside the paper's line of argument.** Preservation of quasi-projectivity by
  Weil restriction along finite locally free maps ([CGP, Prop. A.5.8], Example 4.2) and the
  more general Weil restriction of algebraic spaces ([Ols, Thm. 1.5], after Lemma 5.10). The
  paper does not use them; they are not stated. The existence of the Weil restriction of a
  quasi-projective scheme ([BLR], Example 4.2) is a construction in the Library
  (`affineChartWeilRestriction`, row Ex 4.2).

## Proof tasks targeting statements that the Library already proves

These carried proof tasks are stale: their targets are proved in the Library commit above.
`1677b5d0-7f7a-4017-a252-4cba06cd1177` (`adelicSpaceLevelTopology`),
`e7b0ce18-9908-4e1a-a63f-e5a78800b792` (`adelicSpreadSmoothOpenAssembly`),
`930129fa-aca3-4b0c-a261-c5b0366ea303` (`adelicSpreadSmoothExistence`),
`6d012ddb-9f82-439a-8eff-bd0229f56cad` (`SmoothPureDimensionProof`),
`04ceec56-95e2-41d9-8d3b-d82c643d605b` (`completeHenselianValuedField`),
`22fe3740-b720-434b-970a-a6ed0eaf2c45` (`archimedeanHenselian`),
`95a15424-b38d-46b2-9c75-4dddf08646a2` (`henselianIffSeparablyClosed`),
`9be14959-c9c0-4d74-8c92-72b656990189` (`henselianTensorCompletionField`),
`d9bc9464-de02-48d6-9e67-0a3f6739bd02` (`tensorCompletionProduct`).

## Remaining obligations

1. Proofs of the open rows above, each with the named task. Every published statement of
   an assertion of this paper without a Library proof has a proof task. Of the open derived
   intermediate statements, the following have no proof task: `FamilyLangWeilStatement`
   (`e5531847-70bc-4569-b880-2f90d5815c6a`) and
   `CompleteFiniteExtensionPointEmbeddingStatement`, whose row is proved by another route. Every
   other open derived statement has the proof task named in its row; the conjunction
   `AdelicSpaceProperInputsStatement` has none of its own, and its two conjuncts have Tasks 5357
   (proved) and 5358. The rows name the executors of these proof tasks.
   `SpaceValuativeExtensionExistenceStatement` and
   `SpaceValuativeExtensionDescentStatement` (published for Task 5368) have proof Tasks 5519 and
   5520 without executors; together they would give `SpaceValuativeExistenceStatement`, which
   `spaceValuativeExistence` proves by another route, so no open row depends on them.
   `AdelicSpaceProperModelStatement` (Task 5358) follows from Library theorems, although no
   theorem of exactly its type is published (its row gives the term). With
   `adelicSpaceProperStages`, both inputs of Proposition 5.8 are therefore available, but no
   Library theorem derives `AdelicSpaceSpreadProperMapStatement` from them, so its final
   assembly remains with Task 5253. Lemma 4.6 in both forms (`UniformLangWeilStatement` and
   `SpaceUniformLangWeilStatement`) follows from `FamilyLangWeilStatement` by
   `uniformLangWeilOfFamily` and `spaceUniformLangWeilOfFamily`, and `FamilyLangWeilStatement`
   follows by induction on the dimension from Schmidt's bound `PlaneCurveHasseWeilStatement` (Task
   5406) and proved results (`familyLangWeilZero`, `familyLangWeilCurve`, `familyLangWeilSlicing`,
   `BertiniGenericHyperplane.bertiniGenericHyperplaneStatement` and `familyPointUpperBound`); so
   Schmidt's bound is the only open input of Lemma 4.6 and of the Lang–Weil input of Theorem 5.9, whose assembly remains with Task 5254. In Example
   5.5, five of the six intermediate statements are proved, and `UnipotentOrbitStabilizerSmoothStatement`
   (Task 5434) follows from `Langlands.GroupScheme.ReducedBaseConnectedFibreSmoothStatement` (Task
   5706, no executor); no Library theorem derives the example from them (Task 5217). Both inputs
   of the general case of Corollary 5.7 are proved, but no Library theorem derives
   `HenselianIntegralPointsClosedStatement` from them (Task 5218).
2. The literal Proposition 5.11(1), `HenselianWeilRestrictionPointHomeomorphStatement`, is false
   and stays in the Library; no task proves it. The corrected statement is proved
   (`henselianWeilRestrictionPointHomeomorphOfModuleTopology`, Task 5320), and the Markdown
   correction of `SpaceWeilRestrictionStatement.md` is published.

Other Library statements cite this paper only for the topology on rational points, inside
other programs (for example the `Langlands.Representation.Aubert.General` prerequisites); they
are not assertions of the paper and are not listed.

# Conrad, *Weil and Grothendieck approaches to adelic points*: coverage ledger

Source: Brian Conrad, *Weil and Grothendieck approaches to adelic points*, December 31, 2011,
21 pages. Registered literature ID `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. Page numbers are the printed
page numbers.

The baseline audit maps every substantive construction and assertion of Sections 1–5 to
Lean declarations of Library commit `a54dda0d7c7c0fd4f76308fad8525ba13d9b4ce8`. The focused
audit sections below update selected rows; each names the Library commit it was checked
against. Unchanged rows retain their earlier audit provenance. For each row the ledger
records the declarations, the hypotheses under which the Lean statements assert the source
claim, and the proof status found by searching the commit of its audit. Statuses are those
of that commit; they were not re-checked against the present Library except where a
section says so. The hypothesis column lists every hypothesis of the cited statements that restricts or
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

## Morphisms of analytifications at Library commit `cf95b60a`, 26 November 2026

This section was checked against Library `cf95b60a0d1a76782b35d915d189d581090e1c62`. It
records the proof of `SpaceAnalytificationMorphismStatement`. It updates the status cells of
the two rows of the retained analytification input that cite that statement, where it also
confirms at this commit the other proofs and reductions those cells name, and remaining
obligation 2. The proof is a
theorem whose type is exactly the statement proposition with its universe parameter; the
commit given for it is the commit at which its file first appeared in the Library. The
modules below are in `Langlands/Geometry/Analytic/`. The statement, the proof and
`spaceAnalytificationMorphismStatement_of_etaleDescent` are in the namespace
`Langlands.Analytic.SpaceAnalytification`; `etaleCoverHomExt` and `exists_hom_of_chartCover`
are in `Langlands.Analytic.SaturatedAtlasPresentation`.

- `spaceAnalytificationMorphism` (module `SpaceAnalytificationMorphismProof`, first appeared
  in the Library at `99e4a586253ae0b5bad1472a73c984acb1a6b033`) proves
  `SpaceAnalytificationMorphismStatement`. Let `K` be a complete, ultrametric, nontrivially
  normed field, and let `f : X' ⟶ X` be a morphism of algebraic spaces over `Spec K` with
  `X'` separated and locally of finite type. The target `X` may be any algebraic space over
  `Spec K` equipped with the given analytification. For analytifications `(Y', p')` of `X'`
  and `(Y, p)` of `X` in the sense of `IsAnalytification`, there is a unique `F : Y' ⟶ Y`
  with `p' A P x ≫ F = p A P (RingPoints.map f x)` for every affine test point `x` of `X'`.
  The proof does not use the étale Hom-sheaf premise of
  `spaceAnalytificationMorphismStatement_of_etaleDescent`: uniqueness comes from the étale
  test points through `etaleCoverHomExt`, and `F` is glued on an affinoid chart cover of `Y'`
  by `exists_hom_of_chartCover` (module `LocalizedChartCoverGluing`).

## Proofs checked at Library commit `24390f9f`, 19 November 2026

This section was checked against Library `24390f9f6d7a3b7df9e5b9dd4d6e79e178c8ac85`. It records
proofs of twelve earlier statements, all analytification statements, the affine immersion
proof, new conditional reductions and support modules for open statements, and the
atlas-level ground-field extension of affinoid atlases.
Each proof is a theorem whose type is exactly the statement
proposition with its universe parameters. The commit given for each proof is the commit at
which its file first appeared in the Library. Qualifications that the authors of two modules
recorded are reported with those modules below (the open-gluing support module and the
Frobenius witness). This section updates the status
cells of the analytification rows and remaining obligation 2. It does not
certify whole-paper completion.

All modules below are in `Langlands/Geometry/Analytic/`. In the items on affine
analytification, center maps, scheme analytification and algebraic spaces, `K`
is a complete, ultrametric, nontrivially normed field. The conditional
reductions and the ground-field extension items at the end state their own field scopes.

**Affine analytification** (namespace `Langlands.Analytic.AffineAnalytification`;
all algebras carry finite polynomial presentations).

- `finiteTypeDomainNormExtension` (module `FiniteTypeDomainNormExtensionProof`, first appeared in the Library at
  `b86269dd36757fdbea2e51976499d645ca61a625`) proves
  `FiniteTypeDomainNormExtensionStatement`. Every finitely generated
  `K`-algebra that is a domain carries a multiplicative seminorm that extends
  the norm of `K` and vanishes only at zero. This is the norm input of the
  center statement.
- `affineAnalytificationChartFlat` (module `AffineAnalytificationChartFlatProof`, first appeared in the Library at
  `b86269dd36757fdbea2e51976499d645ca61a625`) proves
  `AffineAnalytificationChartFlatStatement`. For every presentation `P` of `A`
  and every chart index `m`, the map from `A` to the chart algebra of index `m`
  is flat. The theorem
  `affineAnalytificationChart_flat`, in module
  `AffineAnalytificationChartFlatCompletionProof` (first appeared in the Library at
  `bb9e086196d00484fd52204977452d922bf3c660`); the earlier module now imports
  it.
- `affineAnalytificationQuasiFinite` (module `AffineAnalytificationQuasiFiniteProof`, first appeared in the Library at `c01485976764c3625bd56d1c496735f83b741f75`)
  proves `AffineAnalytificationQuasiFiniteStatement`. A `K`-algebra map
  `f : A → B` is quasi-finite exactly when the induced saturated analytic map is
  quasi-finite.
- `affineAnalytificationFiniteGermComparison` (module
  `AffineAnalytificationFiniteGermComparisonProof`, first appeared in the Library at `5f5d3a914cd43b9dc1cd32c07887a973f561df96`)
  proves `AffineAnalytificationFiniteGermComparisonStatement`. Let `y` be a chart
  point at which the saturated analytic map of `f : A → B` is finite, and let
  `q` be the prime of `B` below `y`. Then the analytic map is unramified at `y`
  exactly when `f` is unramified at `q`, and flat at `y` exactly when the local
  map of `f` at `q` is flat.
- `affineAnalytificationFibreProduct` (module `AffineAnalytificationFibreProductProof`, first appeared in the Library at
  `bb9e086196d00484fd52204977452d922bf3c660`) proves
  `AffineAnalytificationFibreProductStatement`. For `K`-algebras `A` and `B`
  over a `K`-algebra `C`, with presentations of `A`, `B`, `C` and `A ⊗_C B`, the
  square of localized analytic maps induced by `C → A`, `C → B`, `A → A ⊗_C B`
  and `B → A ⊗_C B` is a pullback in the localized analytic category.
- `affineAnalytificationImmersion` (module `AffineAnalytificationImmersionProof`)
  was already recorded as proved in the previous section. Its Lean and Markdown
  files first appeared in the Library at `18c5dd82d119bef479b69de264324b22fe6f8d36`, as a
  support module of the proof of the scheme analytification maps; the same pair was later
  recorded as the proof of the affine immersion statement, at
  `b86269dd36757fdbea2e51976499d645ca61a625`.


**Center maps and scheme analytification** (namespace
`Langlands.Analytic.SchemeAnalytification`; `X` is a scheme locally of finite
type over `K`).

- `analytificationCenter` (module `AnalytificationCenterProof`, first appeared in the Library at `c01485976764c3625bd56d1c496735f83b741f75`)
  proves `AnalytificationCenterStatement`. For affine analytifications and for
  the glued analytification of `X`, the center map is surjective, and the
  analytic point of a `K`-rational point is the only point whose center is the
  center of that analytic point. In the affine case that center is the kernel of
  the rational point; in the scheme case it is the image of the closed point,
  and the preimage under the center map of each affine open `U` is the range of
  the inclusion of the piece of `U`.
- `schemeAnalytificationSeparated` (module `SchemeAnalytificationSeparatedProof`, first appeared in the Library at
  `b86269dd36757fdbea2e51976499d645ca61a625`) proves the support statement
  `SchemeAnalytificationSeparatedStatement`: `X → Spec K` is separated exactly
  when the glued analytification is Hausdorff. The support module
  (module
  `SchemeAnalytificationOpenGluing`, first appeared in the Library at
  `b86269dd36757fdbea2e51976499d645ca61a625`) proves `affineOpenGluing`, the
  four open gluing clauses. Its author recorded that it
  proves those four clauses only, leaving the separatedness criterion to
  `SchemeAnalytificationGluingStatement`.
- `schemeAnalytificationGluing` (module `SchemeAnalytificationGluingProof`, first appeared in the Library at `c01485976764c3625bd56d1c496735f83b741f75`)
  proves `SchemeAnalytificationGluingStatement`. The restriction maps between
  affine pieces and the inclusions of the affine pieces are open embeddings; the
  intersection of two pieces is the union of the pieces of the affine opens
  contained in both; for affine `X` the piece of `X` itself is a homeomorphism;
  and `X → Spec K` is separated exactly when the glued space is Hausdorff.
- `schemeAnalytificationAnalyticStructure` (module
  `SchemeAnalytificationAnalyticStructureProof`, first appeared in the Library at `c01485976764c3625bd56d1c496735f83b741f75`)
  proves `SchemeAnalytificationAnalyticStructureStatement`. The glued space is
  homeomorphic to the underlying space of a saturated atlas presentation with
  one analytic domain for each affine open `U`. The homeomorphism carries that
  domain onto the range of the piece of `U`, the domain is isomorphic in the
  localized category to the affine analytification of `U` compatibly with the
  inclusion of the piece, and these isomorphisms are compatible with the
  restriction maps.

**Algebraic spaces** (namespace `Langlands.Analytic.SpaceAnalytification`; `X` is
a separated algebraic space locally of finite type over `Spec K`, and `p` makes
`Y` an analytification of `X` in the sense of `IsAnalytification`).

- `spaceAnalytificationRationalPoints` (module
  `SpaceAnalytificationRationalPointsProof`, first appeared in the Library at
  `bb9e086196d00484fd52204977452d922bf3c660`) proves
  `SpaceAnalytificationRationalPointsStatement`. The underlying space of `Y` is
  Hausdorff, and `rationalPoint` is a topological embedding of `X(K)` with
  `etaleChartTopology`.
- `spaceAnalytificationFieldPoints` (module `SpaceAnalytificationFieldPointsProof`, first appeared in the Library at
  `bb9e086196d00484fd52204977452d922bf3c660`) proves
  `SpaceAnalytificationFieldPointsStatement`. The `K`-valued points of `Y` are
  determined by their underlying points, and they correspond bijectively to
  `X(K)` over `rationalPoint`.
- `spaceAnalytificationImmersion` (module `SpaceAnalytificationImmersionProof`, first appeared in the Library at
  `bb9e086196d00484fd52204977452d922bf3c660`) proves
  `SpaceAnalytificationImmersionStatement`. For a morphism `f : X' → X` of such
  spaces and an analytic map compatible with `f` on all affine test points, an
  open immersion `f` gives an open embedding and a closed immersion `f` gives a
  closed embedding of underlying spaces.
- `spaceAnalytificationScheme` (module `SpaceAnalytificationSchemeComparison`, first appeared in the Library at `c01485976764c3625bd56d1c496735f83b741f75`)
  proves `SpaceAnalytificationSchemeStatement`. For a separated scheme locally of
  finite type over `K`, the underlying space of any analytification of its
  algebraic space is homeomorphic to the glued analytification, compatibly with
  the affine charts and with rational points.

**Conditional reductions and ground-field extension.** `SpaceAnalytificationExistenceReduction`
(first appeared in the Library at
`b86269dd36757fdbea2e51976499d645ca61a625`) derives
`SpaceAnalytificationExistenceStatement` from seven explicit
hypotheses, and `SpaceAnalytificationFibreProductReduction` (first appeared in the Library at
`bb9e086196d00484fd52204977452d922bf3c660`) derives
`SpaceAnalytificationFibreProductStatement` from three premises: the
étale Hom-sheaf property, `AffineAnalytificationFibreProductStatement` (now
proved by `affineAnalytificationFibreProduct`) and
`LocalizedEtalePullbackStatement`. Each of these premises quantifies over
complete, ultrametric, nontrivially normed fields. Both are conditional reductions; they
prove neither target. (The Library now proves `SpaceAnalytificationFibreProductStatement`, as
`spaceAnalytificationFibreProduct` in `SpaceAnalytificationFibreProductProof`; for
`SpaceAnalytificationExistenceStatement` it has only conditional forms.) `SpaceAnalytificationExistenceFiveInputReduction`
(first appeared in the Library at
`5f5d3a914cd43b9dc1cd32c07887a973f561df96`) removes two of the seven
hypotheses. Input 4 is supplied by `affineAnalytificationFibreProduct`. Input 7,
joint surjectivity, is supplied by `exists_mem_range_localizedHom` (module
`AffineAnalytificationJointSurjectivity`, same commit), which is proved
without extra hypotheses: for a complete, ultrametric, nontrivially normed field
`K`, if `K`-algebra maps `A → Bᵢ` are jointly surjective on prime spectra, the
analytified maps are jointly surjective on points. The module's theorem derives
`SpaceAnalytificationExistenceStatement` from the remaining five premises, none
of which has a Library proof. Each premise quantifies over its own class of
fields:

1. the chart quotient for étale affine chart families of separated algebraic
   spaces, over every complete, ultrametric, nontrivially normed field;
2. the étale Hom-sheaf property, over every complete, ultrametric normed field,
   trivial valuations included;
3. étale source descent through jointly surjective étale families, over every
   complete, ultrametric normed field, trivial valuations included;
4. localized étaleness of analytified étale algebra maps, over every complete,
   ultrametric, nontrivially normed field;
5. `LocalizedEtalePullbackStatement`, over every complete, ultrametric normed
   field, trivial valuations included.

The existence conclusion concerns complete, ultrametric, nontrivially normed
fields. The seven-input reduction quantifies its corresponding inputs over the
same classes, and its inputs 4 and 7 over complete, ultrametric, nontrivially
normed fields. The five-input theorem does not prove the existence statement.

The same Library contains new support for the immersion statements
`AffineAnalytificationAnalyticImmersionStatement` and
`SpaceAnalytificationAnalyticImmersionStatement`. In each of the five main theorems named below, `K` is a single
complete, ultrametric, nontrivially normed field, and every hypothesis concerns
that field. `closedImmersion_localizedHom_of_surjective` (module
`AffineAnalytificationClosedImmersionPreservation`, namespace
`Langlands.Analytic.AffineAnalytification`, first appeared in the Library at
`5f5d3a914cd43b9dc1cd32c07887a973f561df96`) proves that a surjective
`K`-algebra map induces a closed immersion of localized affine
analytifications, for any presentations. `localizedHom_injective` (module
`AffineAnalytificationFaithfulness`) proves that localized affine
analytification is injective on algebra maps between fixed presentations. For
compatible analytifications of separated algebraic spaces with a source locally
of finite type, `mono_of_mono_analytification_of_isSeparated` (module
`SpaceAnalytificationMonomorphismDetection`) proves that an analytic monomorphism
comes from a monomorphism of algebraic spaces. The reflection theorems
`isOpenImmersion_of_openImmersion_of_affineReflection` and
`isClosedImmersion_of_closedImmersion_of_scheme_reflection` for open and closed
immersions of algebraic spaces (namespace
`Langlands.Analytic.SpaceAnalytification`, modules
`SpaceAnalytificationOpenImmersionReflection` and
`SpaceAnalytificationClosedImmersionReflection`) concern compatible analytifications of
separated algebraic spaces locally of finite type over `Spec K` and assume
further analytic inputs. The open-immersion theorem assumes étale pullbacks and
reflection of affine étaleness. The closed-immersion theorem requires the
algebraic morphism `f` to be quasi-compact (hypothesis `IsQuasiCompactMorphism
f`), in addition to its three analytic inputs: compatible analytic test
pullbacks, analytic closed-immersion base change, and a scheme reflection
direction for closed immersions into affine tests. These four modules also first appeared in the Library
at `5f5d3a914cd43b9dc1cd32c07887a973f561df96`. None of these modules proves
`AffineAnalytificationAnalyticImmersionStatement` or
`SpaceAnalytificationAnalyticImmersionStatement`. (The Library now proves the second, as
`spaceAnalytificationAnalyticImmersion` in `SpaceAnalytificationAnalyticImmersionProof`; this note
records no proof of the first.)

For the ground-field extension, `domainPreservation` (module
`GeneralizedAffinoid/GroundFieldExtensionDomainProof`, namespace
`Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension`, first appeared in the Library at
`bb9e086196d00484fd52204977452d922bf3c660`) proves `DomainPreservationStatement`.
For complete ultrametric normed fields `K` and `L` with `NormedAlgebra K L`, if a
bounded map of presented `K`-affinoid algebras represents a subset `V` of the
spectrum, its ground-field extension represents the preimage of `V` under the
spectrum projection. The ground-field extension of affinoid atlases is now
constructed (modules
`GroundFieldExtensionChartSystem` and `GroundFieldExtensionAtlas`, namespace
`Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension`, first appeared in the Library
at `5f5d3a914cd43b9dc1cd32c07887a973f561df96`). Here `K` and `L` are complete
ultrametric normed fields with `NormedAlgebra K L`; trivial valuations are
allowed. For every indexed `K`-affinoid atlas `a`, `chartSystem K L a` glues the
ground-field extensions of the chart algebras along the extended restrictions,
`presentation K L a` is the resulting `L`-affinoid atlas presentation, and
`projection K L a` is the continuous map to the original space, surjective by
`projection_surjective`; this atlas-object construction carries no coherence
hypothesis. The map part of the ground-field extension follows this convention: for
arbitrary atlas presentations, the
extension applies to `CompatibleStrongHom` maps; it also covers every
`StrongHom` whose source is saturated, where compatibility is automatic; and the
final functor goes from `SaturatedAtlasPresentation K` to the localized category
`SaturatedAtlasPresentation.LocalizedCategory` over `L`. `StrongHom` itself is
not strengthened. The reason is the Frobenius witness `weakMap`
(module `GroundFieldExtensionCounterexample/WeakMap`, namespace
`Langlands.Analytic.GroundFieldExtensionCounterexample`, first appeared in the Library at
`2613dbbf784309977c42d9252b78c1e1cd40be63`): a `StrongHom` over
`F₂` with the trivial norm whose pullbacks on the two triple target charts
`leftDomain` and `rightDomain` differ by Frobenius. Its authors recorded
three qualifications. First, the module contains only the `F₂` data and
`weakMap`; the theorem that `weakMap` has no ground-field extension to `F₄` is
a separate statement, which needs the atlas base
change of maps. Second, the Lean development does
not prove that the target spectrum has exactly four points, that the two triple
charts are incomparable, or that `weakMap` fails to be a `CompatibleStrongHom`
(the failure of local compatibility of its pullbacks); its Markdown labels these
as informal explanations. Third, the generic helper module
`PolynomialLocusTrivialNorm` (namespace `Langlands.Analytic.PolynomialLocus`)
works over an ultrametric normed field `K` that is not assumed complete. Its
trivial-norm lemmas about unit-radius Tate series and unit-radius charts assume
that every nonzero scalar of `K` has norm 1. Its bounded lift `lift` out of the
unit-radius chart has no trivial-norm premise; it requires a complete
ultrametric normed `K`-algebra as target and an algebra map whose values have
norm at most 1.
The `F₄` non-extension statement and its proof are in the Library
(`GroundFieldExtensionCounterexample/NonExtensionStatement.lean`, `NonExtensionProof.lean`), and
so is a module `GroundFieldExtensionFunctor`. At commit `24390f9f` the Library did not yet
contain the extension of `CompatibleStrongHom` maps, the extension of
`StrongHom` maps with saturated source, or the functor from
`SaturatedAtlasPresentation K`; this note does not record which of these the later modules
cover. The descent of that functor through
quasi-isomorphisms to the localized category over `K`, towers, fibre products
and the comparison `(Xᵃⁿ)_L ≅ (X_L)ᵃⁿ` are further obligations of the formalization of
Conrad's Section 5.

## Proofs checked at Library commit `8aede86c`, 18 November 2026

This section was checked against Library `8aede86c1ec386cf08cfb29e80ce3c58a3239cd8`.
It records proofs of four earlier statements. Each proof is a theorem whose type is exactly
the statement proposition with its universe parameters. The fourth, for
affine immersions, entered the Library as a support module of the proof of the scheme
analytification maps. The commit given for each proof is the commit at which its file first
appeared in the Library. This section updates the status cells of
the Prop 5.4 manifold rows and the analytification rows, and remaining
obligations 1 and 2. It does not certify whole-paper completion.

**Proposition 5.4.** `smoothSourceAnalyticManifold` (module
`SmoothSourceAnalyticManifoldProof` in `Langlands/AlgebraicGeometry/AlgebraicSpace/`, first appeared in the Library at
`d26f6985162bcc4b604d91d2fd1c35df9c7ce13c`) proves
`SmoothSourceAnalyticManifoldStatement`. For every complete nontrivially normed
field `K`, some varying-dimension analytic structure on the rational points of
smooth, quasi-separated, locally separated algebraic spaces over `Spec K` is
admissible, and any two admissible structures are equivalent. The witness is
`dimensionStructure` of the canonical pure-dimensional family
`canonicalAnalyticPointStructure K`. The proof applies five of the intermediate
proofs recorded in the section checked at `18790533`. The four admissibility
conjuncts come from `smoothSourceDimensionAnalyticAssembly`,
`smoothSourceDimensionAnalyticFunctoriality`,
`smoothSourceDimensionEtaleAnalyticIso` and
`smoothSourceDimensionAffineAgreement`, and the equivalence of admissible
structures comes from `smoothSourceDimensionAnalyticUniqueness`. The sixth,
`smoothSourceDimensionTopology`, is the separately proved dependent-sum
homeomorphism; the final theorem does not use it. All seven varying-dimension
statements of Proposition 5.4 are now proved, so remaining obligation 1 is
discharged.

**Analytification.** These are in `Langlands/Geometry/Analytic/`.

- `schemeAnalytificationMorphism` (module `SchemeAnalytificationMorphismProof`,
  namespace `Langlands.Analytic.SchemeAnalytification`, first appeared in the Library at
  `18c5dd82d119bef479b69de264324b22fe6f8d36`) proves
  `SchemeAnalytificationMorphismStatement`. Let `K` be complete, ultrametric and
  nontrivially normed, and let `g` be a morphism of schemes locally of finite type
  over `K`. Then exactly one continuous map of glued analytifications satisfies
  `IsAnalytificationMap` for `g`. Every such map is compatible with the center
  maps and with analytic `K`-rational points, and composites of such maps are
  again such maps. The support modules
  `SchemeAnalytificationBasicOpenRangeProof`,
  `SchemeAnalytificationMorphismCompatibility`,
  `SchemeAnalytificationMorphismCompatibilityProof` and
  `AffineAnalytificationImmersionProof` (below) first appeared with it. The proof also imports the
  existing modules `SchemeAnalytificationBasicOpen`,
  `SchemeAnalytificationCenterRangeProof`, `AffineAnalytificationSeminormProof`
  and `AnalytificationCenterComparison`; the compatibility module applies
  `AnalytificationCenterComparison` for the rational centers. The proof assumes neither the
  gluing statement nor the center statement.
- `affineAnalytificationImmersion` (module `AffineAnalytificationImmersionProof`,
  namespace `Langlands.Analytic.AffineAnalytification`) proves
  `AffineAnalytificationImmersionStatement`. Let `K` be complete, ultrametric and
  nontrivially normed, and let `A` have a finite polynomial presentation. Every
  surjective `K`-algebra map from `A` induces a closed embedding of
  analytifications, and every localization of `A` away from one element `g`
  induces an open embedding. When `C` is the quotient of `A` by `(g)`, the
  ranges of the maps for `A → A_g` and `A → C` are complementary. The module first appeared in the Library at
  `18c5dd82d119bef479b69de264324b22fe6f8d36` as a support module of the proof above.
- `affineAnalytificationBaseChange` (module `AffineAnalytificationBaseChangeProof`,
  namespace `Langlands.Analytic.AffineAnalytification`, first appeared in the Library at
  `db14afe3373dd1e402e436b7f53a35a278f3ee90`) proves `AffineAnalytificationBaseChangeStatement`. Let
  `L/K` be any extension of complete, ultrametric, nontrivially normed fields
  with `NormedAlgebra K L`. Then the map `baseChangeMap K L P : (X_L)ᵃⁿ → Xᵃⁿ`
  is surjective. Its fibre over the analytic point of a `K`-rational point `φ`
  is exactly the analytic point of the `L`-rational point `1 ⊗ a ↦ φ a`.

**Other analytification modules.** The module `SchemeAnalytificationAnalyticStructure`
(first appeared in the Library at
`ce5368421cb4d8518fa60860b8ad3524381855b6`, with support modules
`SchemeAnalytificationAtlas`, `SchemeAnalytificationLocalCharts`,
`SchemeAnalytificationAffinoidPoints` and `AffineAnalytificationLocalDomainMaps`)
constructs a saturated presentation `schemePresentation` of the glued
analytification. Its hypothesis `OpenGluing` consists of clauses (2) and (3) of the
unproved `SchemeAnalytificationGluingStatement`.
`schemeAnalytificationAnalyticStructure_of_gluing` derives
`SchemeAnalytificationAnalyticStructureStatement` from the gluing
statement. This is a conditional reduction, so neither statement is proved by it. The
algebraic-space proofs also have support modules, among them
`SpaceAnalytificationHausdorffReduction` and `LocalizedPullbackPoints` (first at
`18c5dd82d119bef479b69de264324b22fe6f8d36`), and
`SpaceAnalytificationRationalPointInjectivity`, `AnalyticOpenImmersionBaseChange`
and `SpaceAnalytificationFieldPointReduction` (first at
`d26f6985162bcc4b604d91d2fd1c35df9c7ce13c`), and
`SpaceAnalytificationAffinePullback`, `SpaceAnalytificationEtaleReduction`,
`SpaceAnalytificationEtaleReflection` and
`SpaceAnalytificationRationalPointContinuity`, with the algebraic-space modules
`AffineFiniteTypePullbacks`, `EtaleAffineTests` and `EtaleAffinePullbackTests`
(first at `db14afe3373dd1e402e436b7f53a35a278f3ee90`).
`spaceAnalytificationEtaleStatement_of_inputs` derives
`SpaceAnalytificationEtaleStatement` from four explicit hypotheses,
among them the unproved `LocalizedEtalePullbackStatement` and
`AffineAnalytificationEtaleStatement`, so it is a conditional reduction. None of
these modules proves a remaining statement of the ledger. The ground-field
extension of affinoid atlases or analytic spaces was not in this Library.

## Statements and proofs checked at Library commit `18790533`, 17 November 2026

This section was checked against Library `18790533e39c3ee1982619a07a6594528ad156dd`.
It records four more statements of the formalization and twelve proofs of earlier
statements. Each proof theorem's type is exactly
the statement proposition with its universe parameters. The commit that
first contains each file was found by scanning the Library manifests. This section
updates the declaration and status cells of the Prop 5.4 manifold rows and the
analytification rows, and remaining obligations 1 and 2. It does not certify
whole-paper completion.

**New statements.** All four are in `Langlands/Geometry/Analytic/`, namespace
`Langlands.Analytic.AffineAnalytification`, and assume a complete, ultrametric,
nontrivially normed field `K`. None is proved in this Library: each name occurs
only in its own module.

- `FiniteTypeDomainNormExtensionStatement` (first appeared in the Library at
  `42c696807fd25d6ea96d001a596d7bba7b4b52b9`). Every finitely generated commutative
  `K`-algebra `D` that is a domain has a multiplicative seminorm that extends the
  norm of `K` and vanishes only at `0`. Applied to `A/𝔭`, it gives a seminorm
  on `A` with kernel `𝔭`. This is the algebraic input for surjectivity of the
  center map in `AnalytificationCenterStatement`. Sources: Berkovich
  1990, Theorem 3.4.1(i) with Remark 3.4.2, at the generic point of `Spec D`;
  Conrad p.19, final paragraph of the proof of Proposition 5.11(3).
- `AffineAnalytificationQuasiFiniteStatement`. For finite polynomial presentations
  `P`, `Q` of `A`, `B` and `f : A →ₐ[K] B`, the ring map `f` is quasi-finite if
  and only if `saturatedHom K P Q f` is quasifinite (finite at every point).
  Source: Berkovich 1993, Corollary 3.1.7.
- `AffineAnalytificationFiniteGermComparisonStatement`. Let `g := saturatedHom K P Q f`, let
  `y` be a point of the `m`-th chart of the analytification of `B`, and let `q`
  be the prime of `B` under `y`. If `g` is finite at `y`, then `g` is unramified
  at `y` if and only if `f` is unramified at `q`, and `g` is flat at `y` if and
  only if the local map `A_{f⁻¹(q)} → B_q` is flat. This is a derived pointwise
  form of Berkovich 1993, Propositions 3.2.10 and 3.3.11.
- `AffineAnalytificationChartFlatStatement`. For every chart index `m`, the map
  from `A` to the `m`-th chart algebra of its analytification is flat. Source:
  Berkovich 1990, last paragraph of the proof of Theorem 3.4.1.

The last three first appeared in the Library at
`fd643ecec6997ef17c8356ddbc924138631307d9`. They were stated as inputs to the affine étale
statement `AffineAnalytificationEtaleStatement`.

**Proofs of Proposition 5.4 statements.** These are in
`Langlands/AlgebraicGeometry/AlgebraicSpace/`, namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace`. Each theorem proves the statement
whose name it shares.

- `smoothSourceDimensionTopology` (module `SmoothSourceDimensionTopologyProof`), first appeared in
  the Library at `371b9c350ae74d42665a9e7e0ec32e4c66f56619`.
- First appeared in the Library at `42c696807fd25d6ea96d001a596d7bba7b4b52b9`:
  `smoothSourceDimensionAnalyticAssembly` (module
  `SmoothSourceDimensionAnalyticAssemblyProof`),
  `smoothSourceDimensionAnalyticFunctoriality` (module
  `SmoothSourceDimensionAnalyticFunctorialityProof`),
  `smoothSourceDimensionEtaleAnalyticIso` (module
  `SmoothSourceDimensionEtaleAnalyticIsoProof`),
  `smoothSourceDimensionAffineAgreement` (module
  `SmoothSourceDimensionAffineAgreement`) and
  `smoothSourceDimensionAnalyticUniqueness` (module
  `SmoothSourceDimensionAnalyticUniquenessProof` with the support module
  `DimensionPointAtlasCalculus`).

The source-level `SmoothSourceAnalyticManifoldStatement` is not proved in this Library.

**Proofs of affine analytification statements.** These are in
`Langlands/Geometry/Analytic/`, namespace
`Langlands.Analytic.AffineAnalytification`, all first appeared in the Library at
`42c696807fd25d6ea96d001a596d7bba7b4b52b9`. Each theorem proves the statement
whose name it shares.

- `affineAnalytificationRationalPoints` (module
  `AffineAnalytificationRationalPointsProof` with the support module
  `FieldPointSaturation`);
- `affineAnalytificationFunctoriality` (module
  `AffineAnalytificationFunctorialityProof`);
- `affineAnalytificationRationalPointNaturality` (module
  `AffineAnalytificationRationalPointNaturalityProof`);
- `affineAnalytificationSeminorm` (module `AffineAnalytificationSeminormProof`);
- `affineAnalytificationLocalizedFunctoriality` (module
  `AffineAnalytificationLocalizedFunctorialityProof`);
- `affineAnalytificationAffinoidUniversal` (module
  `AffineAnalytificationAffinoidUniversalProof`).

**Other analytification modules.** The proofs also have
supporting modules, among them `SchemeAnalytificationGluingReduction`,
`SchemeAnalytificationRationalPointsReduction` and
`AnalytificationCenterComparison`. These are conditional reductions that keep
their premises as hypotheses. `SchemeAnalytificationSeparatedStatement` restates
the separatedness clause of `SchemeAnalytificationGluingStatement` as a separate
target. None of them proves a remaining statement of the ledger. The Library has the
ground-field extension
of presented affinoid algebras and a projection interface for quotient chart
systems; the scalar-extension row records them. The ground-field extension of
affinoid atlases and analytic spaces is not in this Library.

## Analytification `K`-points, checked at Library commit `f24f9744`, 17 November 2026

This section was checked against Library `f24f97443f21ff7e59b1cf3b509602157dae54c2`. It records
one more statement of the formalization. This
section updates the declaration and status cells of the rational-point row
(Conrad p.19; CT Example 2.3.2) and remaining obligation 2. It does not certify
whole-paper completion. Its status supersedes the sentence of the section on
analytification statements below saying that no statement identifies the image of
`rationalPoint` with the `K`-points of the analytic space.

- First appeared in the Library at `f24f97443f21ff7e59b1cf3b509602157dae54c2`:
  - `Langlands.Analytic.SpaceAnalytification.SpaceAnalytificationFieldPointsStatement`
    (`Langlands/Geometry/Analytic/SpaceAnalytificationFieldPointsStatement.lean`). Let `K` be a complete, ultrametric, nontrivially normed field, `X` a
    separated algebraic space locally of finite type over `Spec K`, and `(Y, p)` an
    analytification of `X` (`IsAnalytification K X Y p`). Then the projection
    `(localizedFieldPointProjection K).app Y` from the `K`-valued points of `Y`
    (`FieldValuedPoints`, with `L = K`) to its underlying points is injective. For
    every presentation `P₀` of `K` there is a bijection from `X(K)`
    (`RingPoints K X K`) to the `K`-valued points of `Y` whose underlying point at
    `x` is `rationalPoint p P₀ x`. Together, the image of `rationalPoint` is the
    set of underlying points of `K`-valued points of `Y`. Sources: Conrad p.19,
    proof of Proposition 5.11(3) (`X(k) = Xᵃⁿ(k)`); Conrad–Temkin Example 2.3.2,
    pp.11–12; Berkovich 1993 §1.4, p.30. The statement is not proved.

## Analytification statements checked at Library commit `b44618a4`, 16 November 2026

This section was checked against Library `b44618a4f02405d5be8c906f21cf7817e4eaafb9`.
It records twenty more modules of the analytification program:
five definitions and fifteen statements. Each is listed under the commit that first
contains it. This section updates the declaration and status cells
of the analytification rows and remaining obligation 2. It does not certify
whole-paper completion. Its statuses supersede the closing paragraph of the earlier
section on center, rational-point and base-change statements below. That paragraph lists as
absent the maps of glued spaces
for scheme morphisms, an analytic structure on the glued space, a universal
property, fibre products, étale maps and the algebraic-space rational-point
comparison. These are stated here, though none was proved at this commit.

All modules are in `Langlands/Geometry/Analytic/`, with namespaces
`Langlands.Analytic.AffineAnalytification`,
`Langlands.Analytic.SchemeAnalytification`,
`Langlands.Analytic.SpaceAnalytification` and
`Langlands.Analytic.SaturatedAtlasPresentation`. All assume a complete,
ultrametric, nontrivially normed field `K`. The affine modules take finite polynomial
presentations of commutative `K`-algebras. The scheme modules take schemes locally of
finite type over `Spec K`. In the algebraic-space statements, every space whose
analytification is assumed or asserted is separated and locally of finite type over
`Spec K`, except the target of the morphism statement, which is arbitrary. Test
algebras lie in the universe of `K`. Besides the originals registered above, the
modules cite Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), source
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

- First appeared in the Library at `9ed11fc606807fab34c4852a4e88dbabebba69d1` (definitions):
  - `SchemeAnalytificationMorphism`. For a morphism
    `g : X ⟶ Y` over `Spec K`, it constructs the continuous maps
    `morphismLocalMap` of affine chart analytifications. It defines the predicate
    `IsAnalytificationMap g hg F` on continuous maps `F` of glued spaces: `F` is
    compatible with these local maps on every pair of affine opens `U`, `V` with
    `g(U) ⊆ V`.
  - `AffineAnalytificationLocalizedMap`. For every `K`-algebra
    map `f : A → B`, it constructs `saturatedHom K P Q f` between saturated
    presentations and `localizedHom K P Q f : localized K Q ⟶ localized K P` in
    the localized category, with underlying map `baseMap`.
- First appeared in the Library at `2016a0d994180c702214a75514a08546aa930f07`:
  - `SchemeAnalytificationMorphismStatement`. There is exactly one continuous map
    of glued spaces satisfying `IsAnalytificationMap` for `g`. Every such map is
    compatible with the center maps and sends analytic rational points to analytic
    rational points. Composites of such maps are such maps for composites.
  - `AffineAnalytificationLocalizedFunctorialityStatement`. `saturatedHom` and `localizedHom`
    preserve identities and composites. The identity of `A` induces an isomorphism
    between the localized analytifications for two presentations.
  - `SchemeAnalytificationAnalyticStructureStatement`. There are a saturated presentation
    `S`, a homeomorphism from its space to `Space K f`, and for every affine open
    `U` an analytic domain `D U` of `S` with an isomorphism in the localized
    category from the affine analytification of `U` to `D U`. These are compatible
    with `ι K f U` and with restrictions (Berkovich 1990, proof of Theorem 3.4.1,
    step (3)).
  - `AffineAnalytificationAffinoidMap` (definition). For a presented
    affinoid algebra `R`, it constructs the strong map `affinoidStrongHom` from the
    singleton atlas of `M(R)` to the atlas of `Spec(A)ᵃⁿ` for every `K`-algebra map
    `A → R`. Conversely, `strongHomAlgHom` gives the algebra map of a strong map.
- First appeared in the Library at `497ef49830025d23824f6b2e2b1d5d60b594f51e`:
  - `AffineAnalytificationAffinoidUniversalStatement`. Strong maps from `M(R)` to
    `Spec(A)ᵃⁿ` correspond bijectively to `K`-algebra maps `A → R`, naturally in
    `R` and in `A`. Points map to the expected seminorms.
  - `AffineAnalytificationFibreProductStatement`. `Spec(A ⊗[C] B)ᵃⁿ` is the fibre
    product of `Spec(A)ᵃⁿ` and `Spec(B)ᵃⁿ` over `Spec(C)ᵃⁿ` in the localized
    category (Berkovich 1993, Proposition 2.6.1).
  - `AffineAnalytificationEtaleStatement`. `saturatedHom K P Q f` is
    unramified, flat or étale in the Library's sense of Berkovich 1993, Definitions
    3.2.5 and 3.3.4, if and only if `f` is formally unramified, flat and
    quasi-finite, or étale, respectively.
  - `SpaceAnalytification` (definition). An analytification of
    an algebraic space `X` is an object `Y` of the localized category with a family
    `p` of morphisms `Spec(A)ᵃⁿ ⟶ Y`, one for each `A`-point of `X`. The predicate
    `IsAnalytification` requires naturality in `A`, étale maps for étale points,
    joint surjectivity from étale points, and pullback squares for affine fibre
    squares. The module also defines `rationalPoint`. Its Markdown relates the
    predicate to the analytic quotient of Conrad–Temkin, Definition 4.1.1 and §4.1.
- First appeared in the Library at `93ead8870c8ad195ed8719439da04773c09e5ea3`:
  - `AnalyticImmersion` (definition). It defines the
    morphism properties `SaturatedAtlasPresentation.closedImmersion` and
    `openImmersion` of the localized category, after Berkovich 1993, Lemma 1.3.7
    with the definition after its proof and the paragraph after Definition 1.3.1.
    It proves identity and isomorphism-invariance lemmas.
  - Seven statements on analytifications `(Y, p)`, under the hypotheses above.
    `SpaceAnalytificationExistenceStatement`: an analytification exists.
    `SpaceAnalytificationMorphismStatement`: a morphism `f : X' ⟶ X` induces a
    unique morphism `F` of analytifications compatible with the test-point maps.
    The étale, fibre-product and immersion statements below concern such
    compatible morphisms.
    `SpaceAnalytificationRationalPointsStatement`: the underlying space of `Y` is
    Hausdorff, and `rationalPoint` is a topological embedding of `X(K)` with
    `etaleChartTopology`. `SpaceAnalytificationEtaleStatement`: `f` is étale if and only if `F` is
    étale. `SpaceAnalytificationFibreProductStatement`: a pullback square of such spaces,
    with compatible morphisms of their analytifications, gives a pullback square
    of analytifications. `SpaceAnalytificationSchemeStatement`: for a separated scheme, the
    underlying space of `Y` is homeomorphic to `Space K f`, compatibly with the
    charts and with rational points. `SpaceAnalytificationImmersionStatement`: if `f` is an open or closed
    immersion, the underlying map of `F` is an open or closed embedding.
- First appeared in the Library at `c0c2e1210454ae2a1888a2989e3de794c1336819`:
  - `AffineAnalytificationAnalyticImmersionStatement`. `f` is surjective if and only if
    `localizedHom K P Q f` is a closed immersion. `Spec(f)` is an open immersion
    if and only if `localizedHom K P Q f` is an open immersion (Berkovich 1990,
    Propositions 3.4.6(8) and 3.4.7(2)).
  - `SpaceAnalytificationAnalyticImmersionStatement`. For a compatible `F`, `f` is an open
    immersion if and only if `F` is one. If `f` is a closed immersion, so is `F`.
    If `f` is quasi-compact, the converse holds for closed immersions
    (Conrad–Temkin, Theorem 2.3.1, in the `k`-analytic setting of §4.1).

Proof status. This Library proves none of the thirty-one statements of
the varying-dimension and analytification programs: each statement name occurs in
no Lean file other than its own module. Later sections record their proofs.

These modules do not supply the following. The analytification of an algebraic space
is characterized by `IsAnalytification` and its existence is stated, but no quotient
`Uᵃⁿ/Rᵃⁿ` of an étale chart is constructed. The scheme maps, analytic structure,
universal property, fibre-product, étale, immersion and rational-point comparisons
are stated, not proved. No statement identifies the image of `rationalPoint` with
the `K`-points of the analytic space. Analytic ground-field extension is not
constructed: this Library has no extension of presented affinoid algebras or
affinoid atlases along `L/K`; that construction is recorded in later sections. The canonical
isomorphism `(Xᵃⁿ)_L ≅ (X_L)ᵃⁿ` therefore remains neither constructed nor
stated.

## Center, rational-point and base-change statements checked at Library commit `e1fa6f68`, 15 November 2026

This section was checked against Library `e1fa6f689f9e976eb7574f0dce4453b3b5705ac0`.
It records three more statements of the formalization. This section updates
the status cells of the analytification rows and remaining obligation 2. It does not
certify whole-paper completion.

The three statements were all first appeared in the Library at
`ccd5c6bb63352c109b2bfde422a65c2dd78e57fd`. Their six Lean and Markdown files
match this Library and the workspace byte for byte. They are in
`Langlands/Geometry/Analytic/`, under the hypotheses of the section checked at `b3dcc8cc`:
a complete nontrivially normed nonarchimedean `K`, and a finite polynomial
presentation `P` of a commutative `K`-algebra `A` or a scheme `X` locally of finite
type over `Spec K`.

- `Langlands.Analytic.SchemeAnalytification.AnalytificationCenterStatement`
. In the affine case,
  `AffineAnalytification.center` is surjective onto `PrimeSpectrum A`. The center
  of the analytic point of `φ : X(K)` is `ker φ`, and that analytic point is the only
  point with this center. In the scheme case, `center` is surjective, the preimage
  of an affine open `U` is the image of `ι U`, the center of
  `analyticRationalPoint p` is the image of the closed point under `p`, and that
  point is the only point with this center (Berkovich, Theorem 3.4.1 and
  Remark 3.4.2; Conrad–Temkin §4.1).
- `Langlands.Analytic.SchemeAnalytification.SchemeAnalytificationRationalPointsStatement`
: `analyticRationalPoint` does not
  depend on the affine chart and is injective. Its range is the union of the chart
  images of the affine analytic rational points. It is a topological embedding for
  `schemePointTopology` (Conrad–Temkin Example 2.3.2).
- `Langlands.Analytic.AffineAnalytification.AffineAnalytificationBaseChangeStatement`
: for every complete nontrivially normed
  nonarchimedean `L` with `NormedAlgebra K L`, `baseChangeMap : (X_L)^an → X^an`
  is surjective. Its fibre over the analytic point of `φ : X(K)` is the single
  analytic point of the induced `L`-point of `X_L` (Berkovich §2.3;
  Conrad–Temkin Theorem 2.3.5).

This Library proves none of the sixteen statements of
the varying-dimension and analytification programs: each statement name occurs only
in its own module.

## Smooth-dimension and analytification statements checked at Library commit `b3dcc8cc`, 15 November 2026

This section was checked against Library `b3dcc8cc4c93f1140c6b34374f589ccc637a1a22`.
It records 22 modules of the formalization: nine smooth-dimension modules and thirteen
analytification modules. The commit that first contains each pair was found by
scanning the Library manifests. This Library proves none of the thirteen new
statements (seven smooth-dimension, six analytification): each statement name occurs only
in its own module. This section updates selected declaration and status cells and the
remaining obligations; it does not certify whole-paper completion. Its statuses
supersede the description, in the section on prerequisites below, of
`SmoothSourceDimensionTopologyStatement` and `SmoothSourceAnalyticAtlas` as not yet in the
Library.

**Varying-dimension smooth spaces (Prop 5.4, p.15).** These modules are in
`Langlands/AlgebraicGeometry/AlgebraicSpace/`, namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace`.

- `SmoothSourceDimensionTopologyStatement`, first appeared in the Library at
  `7f5b5f04a855fc0b4671393213c87415a6ee2aaf`. It states that the actual
  `SmoothDimensionPieces.fieldPointEquiv` from `X(K)` to the dependent sum of the
  piece point spaces is a homeomorphism for `etaleChartTopology`. The hypotheses are a
  henselian nontrivially normed `K` and a quasi-separated smooth `X`; neither
  completeness nor local separatedness is assumed.
- `SmoothSourceAnalyticAtlas` (definition), first appeared in the Library at
  `aeb3911c4e1bf6e3a2f653e874e4ebc422d2a61a`. It defines `DimensionPointAtlas`
  with `IsAnalytic`, `AnalyticOn`, `AnalyticMap`, `IsLocalAnalyticIso` and
  `Equivalent`. It also constructs `AnalyticPointStructure.dimensionAtlas` and
  proves `liftDimensionChart_transition`.
- `SmoothSourceDimensionAnalyticAssemblyStatement`,
  `SmoothSourceDimensionAnalyticFunctorialityStatement`,
  `SmoothSourceDimensionEtaleAnalyticIsoStatement` and the definition
  `SmoothSourceAnalyticStructure` were all first appeared in the Library
  at `4abbe7aabd9c92005d91c9d5bba86b879e928bb3`. The three statements cover a
  henselian nontrivially normed `K` and a pure-dimensional family `σ`. The
  assembly statement assumes that `σ` is analytic; the other two assume that `σ` is
  admissible. They assert that the lifted atlas is analytic, that every morphism of
  smooth, quasi-separated, locally separated spaces is analytic, and that every
  étale morphism is a local analytic isomorphism. The definition introduces the
  family `DimensionAnalyticStructure` with `IsAnalytic`, `IsFunctorial`,
  `IsEtaleLocalIso`, `AgreesWithAffineSpace`, `IsAdmissible` and `Equivalent`, and
  `AnalyticPointStructure.dimensionStructure`.
- `SmoothSourceDimensionAffineAgreementStatement`,
  `SmoothSourceDimensionAnalyticUniquenessStatement` and
  `SmoothSourceAnalyticManifoldStatement` first appeared in the Library at
  `fab9caeae532b7a65e67e702bcab72d3194371ae`. The agreement statement asserts that
  the lifted structure agrees with polynomial affine space. The uniqueness statement
  asserts that any two admissible structures are equivalent, over any nontrivially
  normed `K`. `SmoothSourceAnalyticManifoldStatement` is the source-level assertion
  of the varying-dimension analytic manifold for complete nontrivially normed `K`:
  an admissible structure exists, and it is unique up to equivalence.

**Analytification (p.19).** These modules are in `Langlands/Geometry/Analytic/`, with
namespaces `Langlands.Analytic.AffineAnalytification` and
`Langlands.Analytic.SchemeAnalytification`. All assume a complete nontrivially
normed nonarchimedean `K` and a finite polynomial presentation `P` of a commutative
`K`-algebra `A`, or a scheme `X` locally of finite type over `Spec K`. The
additional registered original is Berkovich, *Spectral theory and analytic
geometry over non-Archimedean fields* (1990), source
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA-256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

- First appeared in the Library at `fab9caeae532b7a65e67e702bcab72d3194371ae`:
  `AffineAnalytificationRationalPoints` (definition), which constructs
  `analyticPoint`, `toFieldPoint` and `toAlgPoint`, and `AffineAnalytificationMap`
  (definition),
  which constructs `baseMap` and the strong atlas map `strongHom` for every
  `K`-algebra map.
- First appeared in the Library at `0b7bb3fdbe6e0386b666b6b099a3bc9cd3ad7e18`:
  - `AffineAnalytificationRationalPointsStatement`: `toFieldPoint` is bijective;
    `analyticPoint` is a topological embedding of `X(K)`; there is a bijection with the
    `K`-points of the saturated atlas.
  - `SchemeAnalytificationSpace` (definition): the topological glue
    `Space` of the affine analytifications over all affine opens, with `ι`, `localMap`
    and the universal map `desc`.
  - `AffineAnalytificationFunctorialityStatement`: `strongHom` preserves identities and
    composites. The identity maps between the atlases of two presentations compose
    to the identity, which gives presentation independence in the affine case.
  - `AffineAnalytificationRationalPointNaturalityStatement`: for a `K`-algebra map `f`, `baseMap` sends the analytic point
    of a rational point `φ` to the analytic point of `φ ∘ f`.
  - `AffineAnalytificationImmersionStatement`: surjections give closed embeddings,
    basic localizations give open embeddings, and the two images are complementary.
  - `AffineAnalytificationSeminorm` (definition): `pointSeminorm` and
    `ExtendsNorm`.
- First appeared in the Library at `b3dcc8cc4c93f1140c6b34374f589ccc637a1a22`:
  - `AffineAnalytificationSeminormStatement`. This is Berkovich's Remark 3.4.2 for `Spec A`: the points are
    exactly the multiplicative seminorms on `A` that extend the norm of `K`, with the
    weak topology.
  - `SchemeAnalytificationGluingStatement`: the restriction maps and the maps `ι`
    are open embeddings; images of two affine opens meet in the images of the affine
    opens they share; the affine case is a homeomorphism; and `X` is separated if
    and only if `Space` is Hausdorff.
  - `SchemeAnalytificationRationalPoints` (definition):
    `analyticRationalPoint` on actual `K`-points of `X`.
  - `AnalytificationCenter` (definition): the continuous center
    maps `X^an → Spec A` and `X^an → X` (Berkovich, Theorem 3.4.1).
  - `AffineAnalytificationScalarExtension` (definition): for every complete
    nonarchimedean extension `L/K`, the continuous map `extensionMap`, and the
    base-change presentation `baseChangePresentation` of `L ⊗[K] A` with the map
    `baseChangeMap : (X_L)^an → X^an`, `X = Spec A`.

Three further statements of the formalization were not yet in the Library at this
commit:
`AnalytificationCenterStatement` (the center maps are surjective and their fibres over rational points
are single points), `SchemeAnalytificationRationalPointsStatement` (`analyticRationalPoint` is
chart independent and injective, has the expected image, and is an embedding for
`schemePointTopology`) and `AffineAnalytificationBaseChangeStatement` (`baseChangeMap` is surjective,
and its fibre over a rational point is one point).

These modules do not supply the following. The glued scheme space is only a
topological space. The Library has no analytic-space structure in
`Langlands.Analytic.SaturatedAtlasPresentation.LocalizedCategory` for a
non-affine scheme, no map of glued spaces for a scheme morphism, and no
analytification universal property (`desc` is only the topological gluing
property). The scalar-extension module constructs only the comparison map
`(X_L)^an → X^an`. The canonical isomorphism `(X^an)_L ≅ (X_L)^an` would need
analytic ground-field extension in the Library; neither is constructed or stated. The
representable analytic étale sheaf quotient for algebraic spaces is not
constructed, and the rational-point comparison with `etaleChartTopology` for
algebraic spaces is not stated. Fibre products and étale maps are not stated
either.

## Prerequisites and bridges checked at Library commit `f676fad7`, 14 November 2026

This section was checked against Library `f676fad71e1679d672d3e20560dc814d4e1f8ffd`.
It records seven modules of the formalization and two statements that were not yet in the
Library at that commit. The Lean and Markdown files of the seven modules were checked against
this Library. This section updates selected declaration and status cells and the remaining
obligations; it does not certify whole-paper completion.

**Unconditional Theorem 4.5.** `Langlands.Global.adelicSpreadSmoothOpen` in
`Langlands/Global/AdelicSpreadSmoothOpenProof` now proves the exact unchanged
`Langlands.Global.AdelicSpreadSmoothOpenStatement.{u}` for every universe `u`.
The proof first appeared in the Library at
`ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181`.
Its implemented proof applies `adelicSpreadSmoothOpenOfLangWeil` to the
published `Langlands.AlgebraicGeometry.uniformLangWeil`. Thus the
Lang–Weil premise is discharged, with the separated generic fibres, arbitrary
finite-type spreads, geometrically connected smooth surjection, both global-field
characteristics and all infinite places retained. There is no common fibre
dimension assumption.

**Actual smooth dimension pieces.** Three derived construction
modules first appeared in the Library at `ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181`:

- `SmoothSourcePointDimension` constructs
  `SmoothDimensionPieces.pointDimension` on actual ordinary quotient points
  and proves all-chart local-dimension agreement, local constancy and atlas
  independence.
- `SmoothSourceDimensionPieces` constructs
  `SmoothDimensionPieces.space` and `inclusion` as genuine represented open
  subspaces. Their ordinary-point loci are open and closed, cover and are
  disjoint. The actual restricted surjective étale atlases are smooth of
  relative dimension `n`, including empty pieces.
- `SmoothSourceDimensionFieldPoints` constructs
  `SmoothDimensionPieces.fieldPointFactor` and `fieldPointEquiv`, with inverse
  the actual piece-inclusion assembly and both inverse laws proved.

These modules use any field `K`, any actual `SmoothOverBase X`, and every
natural-number dimension, without quasi-compactness or finite range. The
section equivalence works over every extension field. Quasi-separatedness and
local separatedness are supplied separately only for the existing
pure-dimensional analytic interface. These algebraic constructions prove
neither a rational-point homeomorphism nor a varying-dimensional analytic
structure.

`SmoothSourceDimensionTopologyStatement` was not yet in the Library at this commit (it first
appeared at `7f5b5f04`, above). Its exact proposition
requires the actual `fieldPointEquiv` to be a homeomorphism for the independently
defined étale-chart and dependent-sum topologies. Its topological scope is
henselian nontrivially normed `K` and quasi-separated smooth `X`, without
completeness or local separatedness. Its proof is separate; this broader topological scope does not enlarge the corrected
full analytic package.

`SmoothSourceAnalyticAtlas` was not yet in the Library at this commit either. Its
`AnalyticPointStructure.dimensionAtlas` lifts any supplied pure-dimensional
chart family through the actual dimension-piece open embeddings to charts on
the original `RingPoints` with `etaleChartTopology`, for henselian nontrivially
normed `K` and smooth quasi-separated locally separated `X`. This topological
construction requires no completeness or analytic law for the supplied family.
It constructs coverage,
intrinsic dimension laws and exact same-piece transition comparisons.
Its predicates retain continuity and every source/target dimension pair on
the full target-chart intersection. Analytic assembly, functoriality, étale
local analytic isomorphisms, scheme agreement and uniqueness were unproved at this
commit. Both modules compiled with zero errors or warnings.

**Actual finite-type affine input.** Three construction
modules first appeared in the Library at `af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e`:

- `AffineAnalytificationGluing` constructs
  the Hausdorff topological glue of cofinal bounded polynomial-kernel loci,
  their actual restriction maps, chart cover and chart neighborhoods.
- `AffineAnalytificationAtlas` constructs the
  affinoid atlas, full-domain saturation and object of the existing
  `Langlands.Analytic.SaturatedAtlasPresentation.LocalizedCategory`.
  Repeated chart ranges are handled by least-index representatives with
  actual bounded algebra equivalences from full domain universal properties.
- `AffineSchemeAnalytification` supplies
  `Langlands.Analytic.AffineSchemeAnalytification.spec` and
  `affineFiniteType` for genuine schemes. Its coordinate ring is the actual
  global-section algebra, with a canonical affine scheme isomorphism over
  `Spec K` and an actual finite polynomial presentation.

The complete-field constructions use complete nontrivially normed
nonarchimedean `K`. They retain full polynomial kernels, nonreduced and zero
algebras, empty affine schemes and zero polynomial variables. The genuine
scheme wrapper uses Mathlib's common universe for rings and schemes.
General independence of presentation, all-morphism functoriality, the
analytification universal property, general scheme gluing, the representable
analytic étale sheaf quotient for separated spaces, rational-point/topology
comparisons and arbitrary complete nonarchimedean extension were open at this commit.
These constructions and the existing
extension-point endpoint do not discharge these comparisons.

The statuses below supersede the open-prerequisite descriptions in the
earlier audit sections.

## Scope of the formalization and retained inputs, 13 November 2026

This section states the scope of the formalization, checked against Library
`aae8cb822941fac72c628376bd39754a1bc40b74`. The audit sections from
“Final Lang–Weil, openness and Example 5.5” through “Earlier focused
audit” below are snapshots at their named commits. The status changes and
scope qualifications of this section take precedence over them when reading the rows.

The formalization makes the following source corrections explicit, preserving the other
individual hypotheses and the two global-field characteristics:

- Adelic fibre products use a separated base, with arbitrary finite-type factors;
  binary products, the nonseparated construction and functoriality keep their
  broader scope. The doubled-origin counterexample remains in the ledger.
- The simple-root branch stays within any prescribed positive distance after
  shrinking the coefficient neighbourhood; uniqueness concerns a sufficiently
  small root neighbourhood, as the polynomial `u(u-1)` shows is necessary.
- For Proposition 5.4 the actual chart topology, continuity, scheme agreement,
  immersion embeddings and étale openness retain the quasi-separated locally
  finite-type scope. The full admissibility package, including fibre products
  and étale local homeomorphisms, and its uniqueness concern the locally
  separated subcategory. The Tag 02Z1 obstruction does not invalidate the broader
  clauses now given separate rows below.
- The complete-field manifold assertion concerns all smooth spaces in that
  corrected class, allowing dimension to vary between components. The published
  pure-dimensional family alone leaves the actual dimension-piece comparison
  open. The algebraic pieces and section maps are constructed (above); their
  rational-point homeomorphism and the functorial, unique analytic assembly were open at
  this commit.
- Example 5.5 retains the geometric orbit-stratum and quotient scope. Its topology
  clause adds local separatedness of the quotient, and qualifies local
  compactness and total disconnectedness by the field. All three corrected
  clauses have proofs in the Library, as recorded in the audit sections below.
- Corollary 5.7 uses the image of integral points. Injectivity needs separatedness;
  closedness needs separated finite type. The two closedness counterexamples and
  the broader open and compact-image scopes remain required and recorded.
- Proposition 5.8 uses a separated finite-type target and hence finite-type
  source. The local Corollary 5.6 retains its quasi-separated locally finite-type
  scope, without a local-separatedness requirement; Theorem 5.9 keeps finite type.
- Proposition 5.11(1) uses `IsModuleTopology K K'` for arbitrary finite extensions
  of henselian nontrivially valued fields. It adds no separability, completeness,
  local separatedness, separatedness or scheme assumption. The mathematical
  obstruction and the proved correction justify this correction. The reversed inclusion in Example 2.2,
  the support/factorization distinction in Remark 3.3 and the caveat for (3.6.2)
  remain in force.

The actual analytification input on Conrad p.19 remains required: scheme
analytification, the representable analytic étale sheaf quotient for separated
algebraic spaces, functoriality and the listed geometric compatibilities,
rational-point and topology comparisons, and arbitrary complete nonarchimedean
field extension. The actual finite-type affine input is constructed (above). The general
scheme, quotient and comparison statements were open at this commit. The input table below records them separately
from the already-proved rational-point extension endpoint. An assumed functor or
a bare quotient of point sets does not provide this input.

At this commit `adelicSpreadSmoothOpenOfLangWeil Langlands.AlgebraicGeometry.uniformLangWeil`
checks at arbitrary universe `u`; the exact-target proof of the unconditional Theorem 4.5,
`adelicSpreadSmoothOpen`, is recorded above. Whole-paper completion remains unclaimed.

## Final Lang–Weil, openness and Example 5.5 proofs checked at Library commit `2e46b9ca`, 13 November 2026

This section was checked against Library `2e46b9cac0230529f50cdf96bbe4713c06701fc2`.
Earlier audit sections are snapshots at their named commits.

The following proofs first appeared in the Library at
`51e4d8972659f1ffcf0ca89e8eee9540a30b52d3`; the present Library retains their
files. Each was checked for the Lake build, the exact target, an unchanged
statement and unchanged inputs.

| Proof |
| --- |
| `adelicSpaceSpreadSmoothOpen` |
| `unipotentOrbitStabilizerSmooth` |

The `Langlands.Global.adelicSpaceSpreadSmoothOpen.{u}` proves the
unchanged `AdelicSpaceSpreadSmoothOpenStatement.{u}` with no extra premise.
It applies the published arbitrary-model reduction
`adelicSpaceSpreadSmoothOpen_of_langWeil` to
`spaceUniformLangWeilOfFamily (familyLangWeilOfPlaneCurve planeCurveHasseWeil)
familyPointUpperBound`. Thus every Lang–Weil premise is supplied by a published
proof. The target retains the two independently supplied separated finite-type
models and their original spread topologies, smoothness, surjectivity and
geometrically connected fibres, both global-field characteristics, finite
constants and nonempty levels for function fields, and all infinite factors for
number fields. It requires no common fibre dimension. This proves Theorem 5.9
on Conrad's printed p.17 by an elementary estimate route in place of the
cohomological route described there. The separately named final scheme and
space uniform-estimate proofs are also in the Library, as recorded below.

The `Langlands.AlgebraicGeometry.AlgebraicSpace.unipotentOrbitStabilizerSmooth.{u}`
proves the unchanged `UnipotentOrbitStabilizerSmoothStatement.{u}`. It applies
the published reduction to `Langlands.GroupScheme.reducedBaseConnectedFibreSmooth`
and `Langlands.GroupScheme.charZeroUnipotentConnected`. The field has
characteristic zero; the group is affine, locally of finite type and unipotent;
the acted-on scheme is reduced and locally of finite type, with constant orbit
dimension. The smooth stabilizer conclusion is stronger than the flatness used
in Conrad's Example 5.5 on printed p.16. The proof uses Cartier's theorem,
connectedness of characteristic-zero unipotent groups and the reduced-base,
connected-fibre form of SGA 3 VI_B 4.4, rather than the source's `exp(ker B)`
description. All six Example 5.5 intermediate statements now have published
exact-target proofs.

The files of both proofs were matched byte for byte against the Library at the commit where
they first appeared and at this commit; their statement files are unchanged.

| Published path | SHA-256 |
| --- | --- |
| `Langlands/Global/AdelicSpaceSpreadSmoothOpenProof.lean` | `daef3aba91252583eb3965a59580543f7ddcfd0c1b9aacd0d2dcb6f284e941c4` |
| `Langlands/Global/AdelicSpaceSpreadSmoothOpenProof.md` | `80105a5b5378bfb0c9fde00a9a463d67737fd5daf4563aad8f9cbef1cc6b2b1a` |
| `Langlands/AlgebraicGeometry/AlgebraicSpace/UnipotentOrbitStabilizerSmoothProof.lean` | `700f4b579d24f1b245522c0da3a5eb898a08cb3ca33b3890c15c55b7f9a24180` |
| `Langlands/AlgebraicGeometry/AlgebraicSpace/UnipotentOrbitStabilizerSmoothProof.md` | `08e85b129b3573635355648a1e23737fe22cfec5334a2e3f97f49092068e67e2` |

Six further proofs are in the Library.
The scheme and space uniform estimates and the second and third Example 5.5
clauses first appeared at `51e4d8972659f1ffcf0ca89e8eee9540a30b52d3`;
the locally closed stratum proof first appeared earlier, at
`730bd1f25b056b8106a2697e003c1ef1733a6b30`, and the conditional Theorem 4.5
proof later, at `73b1430a339b037d27e9096762b0400adb4fbd19`.
Each was checked for the Lake build, the exact target, an unchanged statement and unchanged
inputs.

| Proof |
| --- |
| `uniformLangWeil` |
| `spaceUniformLangWeil` |
| `unipotentOrbitStratumLocallyClosed` |
| `unipotentOrbitStratumQuotient` |
| `unipotentOrbitQuotientPointTopology` |
| `adelicSpreadSmoothOpenOfLangWeil` |

`Langlands.AlgebraicGeometry.uniformLangWeil.{u}` proves the unchanged
`UniformLangWeilStatement.{u}` with no extra premise, by
`LangWeil.uniformLangWeilOfFamily
(LangWeil.familyLangWeilOfPlaneCurve LangWeil.planeCurveHasseWeil)`.
It retains a base of finite type over `ℤ`, a smooth separated surjective
finite-type map with geometrically connected pure-dimensional fibres, and one
constant for every closed point of that base. In namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace`,
`spaceUniformLangWeil.{u}` proves the unchanged
`SpaceUniformLangWeilStatement.{u}` by
`LangWeil.spaceUniformLangWeilOfFamily` applied to that same family estimate
and `LangWeil.familyPointUpperBound`. Its base is quasi-separated of finite
type over `ℤ`; the map is separated, quasi-compact, surjective and
geometrically connected, with relative dimension `d` on an étale chart square.
The uniform bound holds for every finite field and every point of the base
over that field. Both final estimates use the published elementary
Lang–Weil route through Schmidt's Stepanov bound and dimension induction;
neither retains an estimate as a premise.

The three final Example 5.5 theorems are also in namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace`. Their targets are, respectively,
`UnipotentOrbitStratumLocallyClosedStatement`,
`UnipotentOrbitStratumQuotientStatement` and
`UnipotentOrbitQuotientPointTopologyStatement`, in arbitrary universe `u`.
The first uses semicontinuity of stabilizer-fibre dimension and the identity
section to prove the orbit-dimension strata locally closed. Conrad's printed
p.16 does give a semicontinuity justification; the published proof Markdown
records it. The second restricts the action, proves smooth stabilizers using
the SGA 3 and characteristic-zero connectedness reductions above, constructs
the fppf quotient, and proves its quasi-separatedness, finite presentation
and flat surjective quotient map. The third applies the actual étale-chart
point topology to every such quotient. It retains the necessary local
separatedness assumption, local compactness only when the field is locally
compact, and local total disconnectedness only for an ultrametric field.
Thus all three clauses defining `UnipotentOrbitQuotientStatement` have
separate proofs in the Library. This section records no separate
theorem for their conjunction.

`Langlands.Global.adelicSpreadSmoothOpenOfLangWeil.{u}` is in the Library. It proves the unchanged
`AdelicSpreadSmoothOpenOfLangWeilStatement.{u}`, retaining exactly
`UniformLangWeilStatement.{u}` as its premise. It assembles compatible smooth
geometrically connected models, local openness, almost-all native level
surjectivity and the fixed-model reduction in both characteristics. The target
retains separated generic fibres, arbitrary finite-type models, all infinite
number-field factors and finite constants in the function-field branch,
without a common fibre dimension. Both this implication and its Lang–Weil
input are in the Library. The composition
`adelicSpreadSmoothOpenOfLangWeil uniformLangWeil` is therefore the
unconditional endpoint; its exact-target proof, `adelicSpreadSmoothOpen`, is recorded in a
later section above.

The files of the six proofs were matched against the Library at the commits where they first
appeared and at this commit; their statement files are unchanged. The
fingerprints below identify the six proofs; paths are relative to the
Library root.

| Published path | SHA-256 |
| --- | --- |
| `Langlands/AlgebraicGeometry/UniformLangWeilProof.lean` | `8fb7500e380ffcae631c45bc83d5945cc6a1c963872fd5fc2e86eee1d1d918f3` |
| `Langlands/AlgebraicGeometry/UniformLangWeilProof.md` | `36ffb3f2e4d6095482b6fb24023d9191dc9e0e4b71da8a450246fd26dfbdc2e4` |
| `Langlands/AlgebraicGeometry/AlgebraicSpace/SpaceUniformLangWeilProof.lean` | `d5d384d2e3bee6cd4f8d3ae23cfc057afb217e4f44f29d8688fdda5a3800fc5e` |
| `Langlands/AlgebraicGeometry/AlgebraicSpace/SpaceUniformLangWeilProof.md` | `e718abdadb480d04e1c3e26fbe8797301020e4e717ee6ac32c167040b0f49aa7` |
| `Langlands/AlgebraicGeometry/AlgebraicSpace/UnipotentOrbitStratumLocallyClosedProof.lean` | `6361e78344eef941c4c92e79c97680e1187fddf86d913008e6648ed09d15d4d6` |
| `Langlands/AlgebraicGeometry/AlgebraicSpace/UnipotentOrbitStratumLocallyClosedProof.md` | `bff2b0719f995f94a5022a30fa16dd8386a143ee96400dec8fc2e8f973f0acf5` |
| `Langlands/AlgebraicGeometry/AlgebraicSpace/UnipotentOrbitStratumQuotientProof.lean` | `d05cedcb707d6ce7bf3e9272316287993954ebb0c0191758649f433eeaaaed91` |
| `Langlands/AlgebraicGeometry/AlgebraicSpace/UnipotentOrbitStratumQuotientProof.md` | `be7af2b58c8ec2b6389e5466e8b1ad1d2f2421ac6a6751eb5bc9ca1214b75741` |
| `Langlands/AlgebraicGeometry/AlgebraicSpace/UnipotentOrbitQuotientPointTopologyProof.lean` | `7859e22521fe86190957b909824115c7be1e787086e1ad93d6471f2be0c4fc47` |
| `Langlands/AlgebraicGeometry/AlgebraicSpace/UnipotentOrbitQuotientPointTopologyProof.md` | `c8f0fac560a02b2231f5c4bfadcc6b639b195d35c5cb8321909c17bd1471b863` |
| `Langlands/Global/AdelicSpreadSmoothOpenOfLangWeilProof.lean` | `dd243400d3f7c059c658542237bc0af32ee655b9ce11018784291db44b1cf5d4` |
| `Langlands/Global/AdelicSpreadSmoothOpenOfLangWeilProof.md` | `243935f375916b430b4067b00d970899ad968dea759b83ff7773fd96c22cff7d` |

All eight proof modules of this section compile against the Library with zero errors or
warnings. The conditional Theorem 4.5 endpoint retains arbitrary universe `u` and uses only
`propext`, `Classical.choice` and `Quot.sound`.

Whole-paper completion remains open.

## Native level surjectivity, checked at Library commit `7dc9118a`, 13 November 2026

This section was checked against Library `7dc9118a3eb340e83e65d6e4174763b7a61e573c`.
Earlier audit sections are snapshots at their named commits.

The native cofinite-surjectivity proof first appeared in the Library at
`730bd1f25b056b8106a2697e003c1ef1733a6b30`; the present Library retains its files. It was
checked for the Lake build, the exact target, an unchanged statement and unchanged inputs.

`Langlands.Global.adelicLevelComponentSurjectivity.{u}` proves the unchanged
`AdelicLevelComponentSurjectivityStatement.{u}`. It retains
`UniformLangWeilStatement.{u}` as a premise, both arithmetic branches, and
all the target's geometric and absolute finite-type hypotheses. It uses the
published componentwise Henselian RingPoint lifting constructor to obtain exact
integral lifts outside the finite set of places with completed residue-field
cardinality at most the square of its constant. At every enlarged level the
finite exceptional set also contains the supported completed-field factors and,
for number fields, all infinite factors. The original native factor types and
fixed-base coefficient actions remain in the conclusion. No common fibre
dimension is assumed. This implements the almost-all integral surjectivity step
in Conrad's Theorem 4.5 proof, printed pp.12–13; it does not supply the estimate,
compatible models, local openness or the final adelic openness theorem.

The proof files match, byte for byte, those of the commit where they first appeared:

| Published path | SHA-256 |
| --- | --- |
| `Langlands/Global/AdelicLevelComponentSurjectivityProof.lean` | `27bec92fd1ecc0d2905cf3d06ae2e13785ed2a75a2d9c4c027d6bdc94d5905f2` |
| `Langlands/Global/AdelicLevelComponentSurjectivityProof.md` | `b839f310886c5caf09d5a7f1a3faabe11c6a376a73872fac1d89bec8c6fcb903` |

The norm-polynomial, plane-curve estimate, reduced-base smoothness, family-induction
and native cofinite-surjectivity modules compile with zero errors or warnings. The last
theorem retains arbitrary universe `u` and uses only `propext`,
`Classical.choice` and `Quot.sound`. The Theorem 4.5 assembly also compiles against the
Library's modules alone, with the same universe and axiom scope.

All mathematical inputs to the conditional Theorem 4.5 assembly are therefore
in the Library; the assembly itself and the two final uniform estimates are recorded in the
sections above.

## Induction, Schmidt and reduced-base proofs, checked at Library commit `9b849cab`, 13 November 2026

This section was checked against Library `9b849caba7c63ede041b7fec49c90ceaafb08568`.
The three proofs below first appeared in the Library at
`cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e`; the present Library retains their files. Each
was checked for the Lake build, the exact target, an unchanged statement and unchanged
inputs. Earlier audit sections are snapshots at their named commits.

| Proof |
| --- |
| `familyLangWeilOfPlaneCurve` |
| `planeCurveHasseWeil` |
| `Langlands.GroupScheme.reducedBaseConnectedFibreSmooth` |

The induction proof proves the unchanged
implication from the plane-curve estimate to the family estimate in every
dimension. It uses the published zero-dimensional case separately, starts the
positive-dimensional induction with the curve case, and applies slicing for
successors. The upper-bound and Bertini premises are supplied by their proofs.
The Schmidt proof supplies the
plane-curve estimate with no extra premise: its `Stepanov.stepanovNormPolynomials`
constructs the auxiliary polynomials, and the published reduction consumes those
data and the elementary reductions. Thus
`familyLangWeilOfPlaneCurve planeCurveHasseWeil` proves `FamilyLangWeilStatement`
entirely from published proofs.

The reduced-base proof proves the unchanged SGA 3
specialization. It retains the reduced locally Noetherian base, locally finite-type
group, smooth connected residue fibres and locally constant fibre dimension.
Its route places the unit section in the smooth locus using local charts and
then translates; it does not assume flatness. The published stabilizer reduction
can now consume this proof and the published characteristic-zero connectedness
proof.

All four induction statement and proof files and all 34 Schmidt and 18 reduced-base
files were matched against the commit where they first appeared and the Library at this
commit. The primary proof
pairs and norm-polynomial pair have these SHA-256 fingerprints:

| Published path | SHA-256 |
| --- | --- |
| `Langlands/AlgebraicGeometry/LangWeil/FamilyLangWeilOfPlaneCurveProof.lean` | `1bd2595e696ed80e2e8b0f19c7faa7c80e69cc3479d2368328cf135e031fb8a0` |
| `Langlands/AlgebraicGeometry/LangWeil/FamilyLangWeilOfPlaneCurveProof.md` | `0fd09330cc2ed4d3c9eafc558c93dd78d629feaeb22f430fe92d4144f5f85ea3` |
| `Langlands/AlgebraicGeometry/LangWeil/PlaneCurveHasseWeilProof.lean` | `663912b6d4338d7f37fa504ec934c8904d4c1c489ffd537ff12e6f74ad75854e` |
| `Langlands/AlgebraicGeometry/LangWeil/PlaneCurveHasseWeilProof.md` | `b7853b59bbf2e1ce64e1f02617fc71d460657bd3ce95ce9059e068a6dae41ff8` |
| `Langlands/AlgebraicGeometry/LangWeil/Stepanov/NormPolynomials.lean` | `1eb4d4ffa62603eb63996a8789024c08766282833da21569938d4d83b1523979` |
| `Langlands/AlgebraicGeometry/LangWeil/Stepanov/NormPolynomials.md` | `6e9c8c94438207b72ac93c665d8724810c293b0cb41bb45058869bd0ee7a5548` |
| `Langlands/GroupScheme/ReducedBaseSmoothProof.lean` | `e92143e7c3451130a2c5bd0ad41fcf594854b6598305e4d9a46987158a3d1f89` |
| `Langlands/GroupScheme/ReducedBaseSmoothProof.md` | `e7c32377e97650f763321e2fcf2f7ab01c981dce23ccb327b5534449cbb4b4e6` |

The modules compile against the Library with zero errors or warnings. The induction and
reduced-base proofs retain arbitrary universe `u` and use only `propext`,
`Classical.choice` and `Quot.sound`.

At this commit the two final uniform estimates, the native almost-all level surjectivity,
the conditional Theorem 4.5 proof and the Example 5.5 stabilizer and quotient assembly were
not yet in the Library; the sections above record them. All assertion and hypothesis cells
below are retained.

## Component lifting, checked at Library commit `cfedefb6`, 13 November 2026

This section was checked against Library `cfedefb680f317b0ea5d351023e1c9dd886b2547`, where the
component-lifting proof first appeared. Unchanged rows below retain their
earlier audit provenance.

`uniformLangWeilComponentLifting` proves exactly
`UniformLangWeilComponentLiftingStatement.{u}`. Each of its three clauses retains
`UniformLangWeilStatement.{u}` as a premise. The target is of finite type over
the lifted integer spectrum, and the original morphism is smooth, separated,
quasi-compact and geometrically connected. The proof uses the actual finite
target-component schemes, full inverse-image source schemes and selected
component dimensions. A positive constant `1 + ∑ c, C_c` dominates the component
constants; a field-valued point factors through its image component. No common
dimension or nonempty target is supplied. The finite-field helper controls the
entire finite field of values, using its published affine-line enlargement.
Smooth Hensel lifting then applies to the whole original morphism, and the
over-category equations recover the original coefficients for relative
`RingPoint` lifts. This implements the component and residue-point steps of
Conrad's proof on printed pp.12–13.

The proof and statement files were read, and the proof module recompiled with zero errors or
warnings. Their fingerprints are:

| Published path | SHA-256 |
| --- | --- |
| `Langlands/AlgebraicGeometry/UniformLangWeilComponentLiftingProof.lean` | `aa8ea28217f432ffb38ce3172b38b285829bea94ca81e12b1be034ee668ba249` |
| `Langlands/AlgebraicGeometry/UniformLangWeilComponentLiftingProof.md` | `851bcd08daf66470f49eaa9250b1a9a9dff0be960b89d35b28aadf114b8eb8ac` |

At this commit native cofinite level surjectivity, the conditional Theorem 4.5 assembly,
the family-induction implication and the unconditional estimates were not yet in the
Library; the sections above record their proofs.

For Example 5.5, the reduced-base smoothness proof was not yet in the Library at this
commit; it first appeared at `cc5aa77f` (section above).

## Follow-up, checked at Library commit `17dd94ea`, 13 November 2026

This section checks three proofs and the family-induction statement at
Library `17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e`. The affected rows below cite this
section; all other rows keep their earlier provenance.

The published theorem `adelicSpreadGeometricallyConnected` proves the arithmetic
model statement without a common fibre dimension. It detects geometric connectedness
using constructible fibre loci at one affine-limit stage, combines it with smoothness
at a common filtered successor, and supplies compatible separated finite-type models.
The detection clauses allow arbitrary finite-type models. This is the model step of
Theorem 4.5 on printed p.12, without a Lang–Weil premise.

The published theorem `smoothTargetComponentGeometry` proves the full fibre predicate
for each actual target-component restriction, with its separately selected dimension,
by `smoothPureDimension.2` and the published fibre-predicate equivalence. Its other
clause preserves the finite-type separated structure maps using open immersions and
local Noetherianity. The published theorem `henselianIntegralPointsClosed` proves
Corollary 5.7 in its corrected scope: separatedness gives injectivity, and finite type
gives closed image without assuming local compactness of the field. It uses finite
uniform affine étale charts, Hensel lifting and closed chart images; the source
corrections on printed pp.16–17 remain in force.

At this commit the statement `FamilyLangWeilOfPlaneCurveStatement` was not yet in the Library,
and its proof (`familyLangWeilOfPlaneCurve`, recorded above) was not either. Its exact
implication is unchanged.

All three proofs and the statement were read and checked byte for byte
against the Library at this commit. The three proof modules recompiled with zero errors and
warnings. Their fingerprints are:

| Published path | SHA-256 |
| --- | --- |
| `Langlands/Global/AdelicSpreadGeometricallyConnectedProof.lean` | `a24f643b5126e1e1db778f8786ffa56d462cc57a778ad4b9295a62fa20679e67` |
| `Langlands/Global/AdelicSpreadGeometricallyConnectedProof.md` | `5372727bb2cd6c1cb199ced18a322a62278251fd251945ef31b7256bbe952776` |
| `Langlands/AlgebraicGeometry/SmoothTargetComponentGeometryProof.lean` | `682ef3b03964d9c094334b6d8bc0e3a2dbfe2fe041520d65a7ad90a27ef2a61d` |
| `Langlands/AlgebraicGeometry/SmoothTargetComponentGeometryProof.md` | `e753cbe69bb5b404752e25e00f5b7b66c4cabe4f772f9b9dd15efab0f8e28e8c` |
| `Langlands/AlgebraicGeometry/AlgebraicSpace/HenselianIntegralPointsClosedProof.lean` | `5460835314b5363a0679926bf0cbdd4312376b5a36b0c9e64193cc6847e34833` |
| `Langlands/AlgebraicGeometry/AlgebraicSpace/HenselianIntegralPointsClosedProof.md` | `996e2bc55756afe5a1426786900d5ce69dfe45fb3fc816a3cd3016f55a936338` |
| `Langlands/AlgebraicGeometry/LangWeil/FamilyLangWeilOfPlaneCurveStatement.lean` | `a6e963f447fe79c8b732de4d93725d4caf9e279b909fe8005dd632a09d086cd0` |
| `Langlands/AlgebraicGeometry/LangWeil/FamilyLangWeilOfPlaneCurveStatement.md` | `1681ac3df4df14e6a9cc49d05340fcfa1dbc240490bdd8a6bc31f9e0d783a8c6` |

## Earlier focused audit at Library commit `ed924aef`, 13 November 2026

This update checks Proposition 5.8, the arbitrary-model assembly of Theorem 5.9,
the family dimension-induction interface and the missing Schmidt norm-polynomial
input, and the status of the final proof of Corollary 5.7. It does not re-audit every
unchanged row against the newer commit. The two adelic assembly modules were read
with their paired Markdown and recompiled successfully without warnings. Their
published paths at `ed924aef420de137b4cbaa3b063a3618afcd73fd`, together with the
norm-polynomial statement pair read for this audit, are:

| Published path | SHA-256 |
| --- | --- |
| `Langlands/Global/AdelicSpaceSpreadProperMapProof.lean` | `898f4bdec824c6136091cfcc58a5471c520c91bb68690e51e76851c10f2b2ad0` |
| `Langlands/Global/AdelicSpaceSpreadProperMapProof.md` | `be9e631619350b65d110c02059f1206589ee3cadeb86f232b5459ef0630ea811` |
| `Langlands/Global/AdelicSpaceSmoothConnectedSpreadOpen.lean` | `528907e9af780fb544e54ff73a2be917d4a14b347c683075a60e2e5ccb68612f` |
| `Langlands/Global/AdelicSpaceSmoothConnectedSpreadOpen.md` | `1ff4eb9db3ef681b7474cbe0cca1c7b307bf60e7c6b77dba9ea4c54cc7befe92` |
| `Langlands/AlgebraicGeometry/LangWeil/StepanovNormPolynomialsStatement.lean` | `f559ebe1dae3e800b8a5c8dd939f7bc77505444fc05c2f53fcda6a72763bed08` |
| `Langlands/AlgebraicGeometry/LangWeil/StepanovNormPolynomialsStatement.md` | `fe9145f45b88f474a5dfe5075c1cfeef130f2330a20a8eacaf16f560ca564dbd` |

At this commit the family-induction statement and the final closedness proof of
Corollary 5.7 were not yet in the Library; the follow-up section above records them.

## Status vocabulary

- **proved**: a theorem whose type is the named statement is in the applicable Library commit; it is
  named in the row. Its presence in the Library is the evidence. A proof-producing
  `def` of Prop type, published as a supporting definition, counts when its type is the named
  statement up to unfolding; the row says so.
- **construction**: a definition (with its intrinsic lemmas) in the Library.
- **open**: a statement in the Library with no Library proof.
- **staged**: a statement or proof that was written but not in the applicable Library commit.
- **not stated**: an assertion with no Lean statement in the Library.
- **false as stated**: a published statement that faithfully transcribes a source assertion
  shown to be false; the row names the evidence and the corrected statement.

The proofs of the following statements of this paper are in the Library: Lemma 5.1, Lemma 5.10,
`spaceLimitModelExistenceQuasiSeparated`, `SpaceLimitUniquenessStatement`,
`AdelicSpacePointTopologyStatement`, `henselianWeilRestrictionPointHomeomorphOfModuleTopology`
(the corrected Proposition 5.11(1); the literal statement is false, and the module-topology
replacement keeps its obstruction), `spaceValuativeExistence` (an intermediate statement for
Corollary 5.6), `localFieldProperPointMap` (Corollary 5.6), the Lang–Weil steps
`familyLangWeilZero`, `BertiniGenericHyperplane.bertiniGenericHyperplaneStatement`,
`familyLangWeilSlicing`, `uniformLangWeilOfFamily`, `familyCurvePlaneComparison`,
`familyLangWeilCurve`, `spaceUniformLangWeilOfFamily`, `finiteNormalizationCover` and
`familyPointUpperBound`, and `properSchemeBaseChange`, `adelicSpaceProperStages`,
`representedAtlasEffectivity`, `spaceLimitFlatnessDimensionDescent`,
`adelicSpaceWeilRestriction` (Proposition 5.14), `spaceLimitPropertyDescent`,
`henselianExtensionPointEmbedding`, `properSchemeCover`,
`CompleteExtensionClosedRange.completeExtensionPointClosedRange`,
`henselianChartIntegralPointsClosed`, `uniformFieldPointCharts`, the Example 5.5 steps
`smoothStabilizerActionQuotient`, `orbitStratumActionRestriction`, `actionQuotientFiniteness`,
`locallySeparatedRationalPoints` and `stabilizerFibreLocalDimension`, and
`spaceLimitMorphismDescent`, `spaceLimitModelExistence`,
`spaceLimitMorphismDescentQuasiSeparated` and `adelicSpaceProperModel`. Other proofs are
named in the rows.

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
| Thm 4.5 | geometrically connected models, no common dimension | `AdelicSpreadGeometricallyConnectedStatement` | eventual detection of geometric connectedness and of smooth ⊓ geometrically connected for arbitrary ft models, and existence of separated ft models of a smooth geometrically connected map of separated finite-type schemes; curves need perfect `k` | proved (`adelicSpreadGeometricallyConnected`, module `Langlands/Global/AdelicSpreadGeometricallyConnectedProof`, at commit `17dd94ea`). The proof uses constructible geometric-connectedness loci, a common filtered successor for simultaneous smoothness, and compatible actual models; no common fibre dimension or Lang–Weil premise is used |
| Thm 4.5 | almost-all level surjectivity | `AdelicLevelComponentSurjectivityStatement`; lifting input `UniformLangWeilComponentLiftingStatement` | both conditional on `UniformLangWeilStatement`; `f` smooth, separated, quasi-compact, geometrically connected, with target of finite type over `Z` (quasi-compact); level surjectivity at almost all places, curves need finite `k`; lifting of points over finite fields, over henselian local rings with large finite residue field, and of ring points over such rings | proved, with `UniformLangWeilStatement` retained as a premise: lifting by `uniformLangWeilComponentLifting` (module `Langlands/AlgebraicGeometry/UniformLangWeilComponentLiftingProof`, at the component-lifting audit commit); native level surjectivity by `adelicLevelComponentSurjectivity` (module `Langlands/Global/AdelicLevelComponentSurjectivityProof`, at commit `7dc9118a`). The latter constructs exact original-base integral lifts outside a finite small-residue set and proves actual cofinite surjectivity at every enlarged level, retaining all infinite factors and using no common dimension premise |
| Thm 4.5, proof (p.12) | restriction to connected components of the target, with fibres of a common dimension | `SmoothTargetComponentGeometryStatement` | not conditional on Lang–Weil; fibre-geometry clause: `f` smooth and geometrically connected with locally noetherian target, each component restriction has nonempty geometrically connected fibres of pure dimension; preservation clause: arbitrary base scheme, locally noetherian source and target with structure maps locally of finite type, quasi-compact and separated, no hypothesis on `f`, the component restrictions keep these finiteness properties | proved (`smoothTargetComponentGeometry`, module `Langlands/AlgebraicGeometry/SmoothTargetComponentGeometryProof`, at commit `17dd94ea`). It applies `smoothPureDimension.2` to each selected component dimension and uses the full fibre-predicate equivalence; the structure-map clause follows from open inclusions and local Noetherianity |
| Thm 4.5 | Theorem 4.5 from Lemma 4.6; unconditional | `AdelicSpreadSmoothOpenOfLangWeilStatement`, `AdelicSpreadSmoothOpenStatement` | separated generic fibres, arbitrary ft models; `g` smooth, surjective, geometrically connected; curves need finite `k` | proved: the conditional target by `adelicSpreadSmoothOpenOfLangWeil` (module `Langlands/Global/AdelicSpreadSmoothOpenOfLangWeilProof`), and the exact unconditional target by `Langlands.Global.adelicSpreadSmoothOpen` (module `Langlands/Global/AdelicSpreadSmoothOpenProof`), independently accepted and published at `ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181`. The latter applies the former to the published `Langlands.AlgebraicGeometry.uniformLangWeil`, with no additional premise |
| Lem 4.6 | uniform relative Lang–Weil estimate | `UniformLangWeilStatement` | base of finite type over `Z`; `f` smooth, separated, surjective, of finite type, geometrically connected, fibres of pure dimension `d` | proved (`uniformLangWeil : UniformLangWeilStatement.{u}`, module `Langlands/AlgebraicGeometry/UniformLangWeilProof`) at commit `2e46b9ca`. The published proof applies `uniformLangWeilOfFamily` to `familyLangWeilOfPlaneCurve planeCurveHasseWeil`, with no extra premise |

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
| p.13 | Thm 3.4(1) for spaces: models, morphism descent | `SpaceLimitModelExistence`, `SpaceLimitModelExistenceQuasiSeparated`, `SpaceLimitMorphismDescent`, `SpaceLimitMorphismDescentQuasiSeparated` | cofiltered limits of affine schemes; models of separated (resp. quasi-separated) spaces with an `LocallyOfFinitePresentation ⊓ QuasiCompact` atlas; morphism descent over an affine base from a separated (resp. quasi-separated) source with a quasi-compact atlas to a target locally of finite presentation | `SpaceLimitMorphismDescent` proved (`spaceLimitMorphismDescent`, module `SpaceLimitMorphismDescentProof`); `SpaceLimitModelExistence` proved (`spaceLimitModelExistence`, module `SpaceLimitModelExistenceProof`); `SpaceLimitMorphismDescentQuasiSeparated` proved (`spaceLimitMorphismDescentQuasiSeparated`, module `SpaceLimitMorphismDescentQuasiSeparatedProof`); `SpaceLimitModelExistenceQuasiSeparated` proved (`spaceLimitModelExistenceQuasiSeparated`, module `SpaceLimitModelExistenceQuasiSeparatedProof`; from the intermediate statements below) |
| p.13 | Thm 3.4(1) for spaces: eventual equality of morphisms; Thm 3.4(3): uniqueness of models | `SpaceLimitUniquenessStatement` | cofiltered limits of affine schemes; both spaces finitely presented | proved (`spaceLimitUniquenessStatement`, with the clauses `spaceLimitMorphismEventualEquality` and `spaceLimitModelUniqueness`, module `SpaceLimitUniquenessProof`) |
| p.13 | Thm 3.4(2) for spaces: closed immersion, separated, proper, smooth, affine, open immersion, finite, fibres nonempty and geometrically connected | `SpaceLimitPropertyDescentStatement` | cofiltered limits of affine schemes; source and target finitely presented | proved (`spaceLimitPropertyDescent`, module `SpaceLimitPropertyDescentProof`: `spaceLimitPropertyDescent_of_foundations representedAtlasEffectivity properSchemeCover`; the separated, smooth and geometrically-connected-fibres conjuncts are also proved separately; intermediate statements below) |
| p.13 | Thm 3.4(2) for spaces: flat; fibres nonempty, geometrically connected and of pure dimension `d` | `SpaceLimitFlatnessDimensionDescentStatement` with `IsFlatMorphism`, `HasPureFibreDimension` | flatness and pure fibre dimension defined through a commutative square with an étale surjective chart of the source and an étale chart of the target; cofiltered limits of affine schemes; source and target finitely presented | proved (`spaceLimitFlatnessDimensionDescent`, module `SpaceLimitFlatnessDimensionDescentProof`): it is `spaceLimitFlatnessDimensionReduction spaceLimitGeometricallyConnectedFibresDescent`; the flatness conjunct is also proved on its own (`spaceLimitFlatnessDescends`), and so is descent of pure fibre dimension alone (`spaceLimitPureFibreDimensionDescends`) (intermediate statements below) |
| Lem 5.1 | geometric-component-count locus constructible | `GeometricFibreComponentsConstructibleStatement`; scheme input `GeometricallyConnectedFiberLocalConstructibility` (proved); scheme specialization `SchemeGeometricComponentCountConstructibleStatement` (intermediate statements below) | quasi-separated, finitely presented over an arbitrary ring `B`; `n` a natural number | proved (`geometricFibreComponentsConstructible`, module `GeometricFibreComponentsProof`; it applies `geometricFibreComponentsConstructible_of_limitModels` (module `GeometricComponentApproximation`) to the model existence of row "Thm 3.4(1) for spaces: models, morphism descent") |
| Prop 5.2 | (3.6.1) bijective for separated finite type spaces | `AdelicSpaceLevelPointsStatement`, `SeparatedProductPointsInjectiveStatement` | separated, finite type over the `S`-integers, curves need finite `k` and nonempty `S`; injectivity for separated spaces over any ring and any product | proved (`adelicSpaceLevelPoints`, `separatedProductPointsInjective`) |
| p.14 | henselian valued fields: definition, separably closed in completion, valuation-ring criterion, tensor with completion, archimedean classification, finite étale equivalence | `IsHenselianValuedField`, `HenselianEtalePointStatement`, `HenselianValuedFieldPropertiesStatement` and its six components, `CompleteHenselianValuedFieldStatement` | nontrivially normed fields; separably closed in the completion: iff henselian; valuation-ring criterion: ultrametric fields; tensor product with the completion: finite separable extensions, a product of completions in general and a field of the same degree for henselian `K`; archimedean classification: non-ultrametric fields; finite étale equivalence: henselian `K`; complete fields are henselian | proved: the conjunction `HenselianValuedFieldPropertiesStatement` (`henselianValuedFieldProperties`), its six components (`henselianIffSeparablyClosed`, `henselianIffValuationRingHenselian`, `tensorCompletionProduct`, `henselianTensorCompletionField`, `archimedeanHenselian`, `henselianFiniteEtaleEquivalence`), `henselianEtalePoint` and `completeHenselianValuedField` |
| Lem 5.3 | étale maps give local homeomorphisms over henselian fields | `HenselianEtalePointLocalHomeomorphStatement` | henselian `K`; `X`, `Y` locally of finite type | proved (`HenselianEtalePointProof`) |
| Prop 5.4 | topology on `X(k)`: existence, uniqueness, functoriality, fibre products, immersions, étale maps | `etaleChartTopology`, `HenselianSpacePointTopologyStatement`, `EtaleChartTopologyAdmissibleStatement` | henselian `K`; the axioms and the uniqueness concern quasi-separated, locally separated spaces locally of finite type (correction below) | proved (`henselianSpacePointTopology`, `etaleChartTopologyAdmissible`, uniqueness lemma `eq_etaleChartTopology_of_isAdmissible`), corrected |
| Prop 5.4 | actual chart-topology construction in the full source class | `etaleChartTopology` (`EtaleChartTopology`) | any field `K` with a topology; every actual algebraic space over `K`, in particular all quasi-separated locally finite-type spaces over a henselian nontrivially normed field; the definition needs no henselianity or local separatedness | construction: the final topology of the actual finite-type étale scheme-chart point maps; the full six-property theorem has the separate scope in the preceding row |
| Prop 5.4 | functorial continuity in the full source class | `continuous_ringPointsMap` (`EtaleChartTopologyFunctorial`) | henselian nontrivially normed `K`; target `Y` quasi-separated and locally of finite type; source `X` arbitrary; every morphism `X → Y`; no local separatedness | proved for `etaleChartTopology` |
| Prop 5.4 | agreement with scheme point topology | `isHomeomorph_schemeRingPointsEquiv` (`EtaleChartTopologyFunctorial`) | henselian nontrivially normed `K`; the space of the scheme `U` is quasi-separated and locally of finite type; no local separatedness added | proved: the actual `schemeRingPointsEquiv` is a homeomorphism |
| Prop 5.4 | open- and closed-immersion embeddings in the full source class | `isOpenEmbedding_ringPointsMap`, `isClosedEmbedding_ringPointsMap` (`EtaleChartTopologyFunctorial`) | henselian nontrivially normed `K`; both spaces quasi-separated and locally of finite type; the actual morphism is respectively an open or closed immersion; no local separatedness | proved |
| Prop 5.4 | étale openness in the full source class | `isOpenMap_ringPointsMap_of_isEtaleMorphism` (`EtaleChartTopologyFunctorial`, using `EtaleChartOpenMap`) | henselian nontrivially normed `K`; source quasi-separated and locally of finite type; arbitrary target and an étale morphism; no local separatedness | proved: openness only; the full-package local-homeomorphism assertion keeps its locally separated scope |
| Prop 5.4 | Hausdorff (separated), totally disconnected, locally compact | `SeparatedRationalPointTopologyProperties` (part of the statement above) | `X` quasi-separated, locally of finite type and separated; totally disconnected for ultrametric `K`; locally compact for locally compact `K` | proved (`t2Space_etaleChartTopology`, `totallyDisconnected`, `locallyCompactSpace_etaleChartTopology`) |
| Prop 5.4 | `k`-analytic manifold structure for smooth `X`, complete `k` | `AnalyticPointStructure` (`AnalyticPointManifold`), `AnalyticPointManifoldStatement` | complete `K`; spaces quasi-separated, locally separated, locally of finite type, with an étale atlas smooth of relative dimension `n`; existence and uniqueness up to equivalence | proved (`analyticPointManifold`, module `AnalyticPointManifoldProof`): existence by the admissible family `canonicalAnalyticPointStructure` (`canonicalAnalyticPointStructure_isAdmissible`, intermediate statements below), uniqueness by `AnalyticPointStructure.equivalent_of_isAdmissible` (module `AnalyticPointUniqueness`); this proves the pure-dimensional family. The actual algebraic pieces are published. The varying-dimension statements, including the source-level `SmoothSourceAnalyticManifoldStatement` for varying dimension, are published as recorded in the section checked at `b3dcc8cc`. Their proofs remain open. Section checked at `18790533`: six of these seven statements are proved; the proof of the source-level `SmoothSourceAnalyticManifoldStatement` remains open. section checked at `8aede86c`: `SmoothSourceAnalyticManifoldStatement` is proved (`smoothSourceAnalyticManifold`, module `SmoothSourceAnalyticManifoldProof`), so all seven varying-dimension statements are proved |
| Prop 5.4, manifold bridge | actual open-and-closed dimension pieces and section decomposition | `SmoothDimensionPieces.pointDimension` (`SmoothSourcePointDimension`); `SmoothDimensionPieces.space`, `inclusion`, `restrictedAtlasMap`, `space_isSmoothPureDimensional` (`SmoothSourceDimensionPieces`); `SmoothDimensionPieces.fieldPointFactor`, `fieldPointEquiv` (`SmoothSourceDimensionFieldPoints`) | any field `K`, arbitrary `SmoothOverBase X`; all `n : ℕ`, including empty pieces, with no quasi-compactness or finite-range assumption; pure-dimensional analytic specialization adds quasi-separatedness, local separatedness and a norm; section maps over every field extension | constructed with intrinsic laws, first appeared in the Library at `ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181`. Actual restricted atlases, section factorizations and both equivalence laws are proved; the topological and analytic statements built on them (next row) are proved, as `smoothSourceDimensionTopology` and `smoothSourceAnalyticManifold`. Derived Library content, not a separate numbered source theorem |
| Prop 5.4, manifold bridge | rational-point disjoint-union topology and varying-dimension analytic structure | published algebraic input `SmoothDimensionPieces.fieldPointEquiv`; published `SmoothSourceDimensionTopologyStatement`; `AnalyticPointStructure.dimensionAtlas` (`SmoothSourceAnalyticAtlas`), with `DimensionPointAtlas.IsAnalytic`, `AnalyticOn`, `AnalyticMap`, `IsLocalAnalyticIso` and `Equivalent`; `DimensionAnalyticStructure`, `IsAdmissible`, `Equivalent` and `AnalyticPointStructure.dimensionStructure` (`SmoothSourceAnalyticStructure`); `SmoothSourceDimensionAnalyticAssemblyStatement`, `SmoothSourceDimensionAnalyticFunctorialityStatement`, `SmoothSourceDimensionEtaleAnalyticIsoStatement`, `SmoothSourceDimensionAffineAgreementStatement`, `SmoothSourceDimensionAnalyticUniquenessStatement` and `SmoothSourceAnalyticManifoldStatement` | smooth, quasi-separated, locally separated `X` over complete nontrivially normed `K`; actual `X(K)` homeomorphic to the dependent sum of the actual piece point spaces for `etaleChartTopology`; analytic maps on intersections with target pieces, étale dimension preservation and local analytic isomorphisms, scheme agreement and uniqueness | stated, not proved: two definitions and seven statements first appeared in the Library at the commits recorded in the section checked at `b3dcc8cc`. The topology statement uses weaker henselian/quasi-separated hypotheses, without completeness or local separatedness. The intermediate analytic statements assume a henselian `K` and an analytic or admissible pure-dimensional family. The source-level `SmoothSourceAnalyticManifoldStatement` assumes a complete `K`. The proofs are open; the existing pure-dimensional family does not discharge them. Section checked at `18790533`: proved except the source-level statement. `smoothSourceDimensionTopology`, `smoothSourceDimensionAnalyticAssembly`, `smoothSourceDimensionAnalyticFunctoriality`, `smoothSourceDimensionEtaleAnalyticIso`, `smoothSourceDimensionAffineAgreement` and `smoothSourceDimensionAnalyticUniqueness` prove the six statements of the same names. `SmoothSourceAnalyticManifoldStatement` remains open. section checked at `8aede86c`: proved. `smoothSourceAnalyticManifold` (module `SmoothSourceAnalyticManifoldProof`) proves `SmoothSourceAnalyticManifoldStatement` from the five analytic proofs: assembly, functoriality, étale local isomorphisms and affine agreement give admissibility, and `smoothSourceDimensionAnalyticUniqueness` gives uniqueness. `smoothSourceDimensionTopology` independently proves the dependent-sum homeomorphism. All seven statements of this row are proved |
| Prop 5.4, proof (p.15) | every rational point lifts through an étale map from an affine scheme (Knutson II.6.4) | `RationalPointEtaleLiftStatement` | any field `k`; `X` quasi-separated | proved (`RationalPointEtaleLiftProof.rationalPointEtaleLiftStatement`) |
| Ex 5.5 | unipotent orbit strata locally closed; quotient spaces `V_d/G`; local Hausdorffness of `(V_d/G)(k)` | `UnipotentOrbitQuotientStatement` | henselian `K` of characteristic zero; `G` a unipotent algebraic group (affine, locally of finite type); `V` reduced of finite type with a `G`-action; strata and quotient as in the source (quotient quasi-separated, finitely presented, with flat surjective quotient map); the topology clause adds that the quotient is locally separated (correction below), with local compactness only for locally compact `K` and local total disconnectedness only for ultrametric `K` | all three clauses have separately published exact-target proofs at commit `2e46b9ca`: `unipotentOrbitStratumLocallyClosed`, `unipotentOrbitStratumQuotient` and `unipotentOrbitQuotientPointTopology`; corresponding proof module names append `Proof` to each statement stem under `AlgebraicSpace/`. Every source correction in this row is retained. All six intermediate targets are also proved, including stabilizer smoothness. No separate conjunction theorem is claimed |
| Cor 5.6 | proper maps over local fields are proper on points | `LocalFieldProperPointMapStatement` | locally compact nontrivially normed `K`; `X`, `Y` quasi-separated and locally of finite type | proved (`localFieldProperPointMap`, module `LocalFieldProperPointMapProof`): the proved implication `LocalFieldProperPointValuativeReductionStatement` applied to the proved Stacks valuative criterion `spaceValuativeExistence`. The Lean proof replaces Conrad's Chow-lemma argument by the valuative criterion and an ultrafilter limit over the convergent germs of an ultrapower (`LocalFieldProperPointLimit.localFieldProperPointMap_of_valuative`); archimedean `K` remain included (intermediate statements below) |
| Cor 5.7 | `X(R)` open in `X(k)` | `HenselianIntegralPointsOpenStatement` | `O` the closed unit ball, a henselian local ring; `X` quasi-separated, locally of finite type over `O`; the image of `X(O)` in `X_K(K)` is open | proved (`henselianIntegralPointsOpen`) |
| Cor 5.7 | `X(R)` quasi-compact for locally compact `k` and `X` of finite type | `HenselianIntegralPointsCompactStatement` | as above, with `K` locally compact and `X` of finite type over `O`; the image of `X(O)` in `X_K(K)` is compact | proved (`henselianIntegralPointsCompact`) |
| Cor 5.7 | closedness, corrected scope | `HenselianIntegralPointsClosedStatement`; locally compact case `HenselianIntegralPointsClosedOfLocallyCompactStatement`; inputs `HenselianChartIntegralPointsClosedStatement`, `UniformFieldPointChartsStatement` (intermediate statements below) | `X` separated: injectivity of `X(O) → X_K(K)`; closed image if moreover `X` is of finite type over `O`; the locally compact case adds `K` locally compact | proved (`henselianIntegralPointsClosed`, module `AlgebraicSpace/HenselianIntegralPointsClosedProof`, at commit `17dd94ea`). The finite uniform field-point charts, Hensel lifting and closed chart images give the closed image without a local compactness premise. The locally compact case is also proved (`henselianIntegralPointsClosedOfLocallyCompact`) |
| Cor 5.7 | counterexamples to unqualified closedness | `HenselianIntegralPointsNotClosedOfFiniteTypeStatement`, `HenselianIntegralPointsNotClosedOfSeparatedStatement` | for every such `K` and `O`: a quasi-separated space of finite type, and a separated space locally of finite type, with non-closed image | proved |
| p.17 | level points locally compact Hausdorff, open level changes | `AdelicSpaceLevelTopologyStatement` | separated, finite type over the `S`-integers, curves need finite `k` and nonempty `S` | proved (`adelicSpaceLevelTopology`) |
| p.17 | `X(A_F)`: Weil limit bijection, topology, locally compact Hausdorff with countable base, fibre products, closed immersions, scheme agreement, model independence | `AdelicSpacePointTopologyStatement` (`AdelicSpacePointTopology` constructions) | separated finite-type models, curves need finite `k` and nonempty `S`; fibre products of separated finite-type spaces; scheme agreement for separated ft schemes | proved (`adelicSpacePointTopology`, module `Langlands/Global/AdelicSpacePointTopologyTheorem`): `AdelicSpacePointTopologyProof.adelicSpacePointTopology_of_spread` derives the statement from `spaceFilteredRingPointComparison` and the spread clauses `AdelicSpaceSpreadIndependenceProof.curvePlaceSpaceSpread` and `.numberFieldSpaceSpread`; model existence is `AdelicSpaceSpreadExistenceProof` (from `spaceLimitModelExistence`), model independence `AdelicSpaceSpreadIndependenceProof` (from `spaceLimitMorphismDescent`) |
| Prop 5.8 | proper maps of separated spaces: topologically proper on adelic points | `AdelicSpaceSpreadProperMapStatement`; inputs `AdelicSpaceProperStagesStatement`, `AdelicSpaceProperModelStatement` (intermediate statements below) | arbitrary separated finite-type models of source and target, curves need finite `k` and nonempty `S` (correction below) | proved (`adelicSpaceSpreadProperMap : AdelicSpaceSpreadProperMapStatement.{u}`, module `Langlands/Global/AdelicSpaceSpreadProperMapProof`, at the 13 November audit commit); the final theorem supplies the published topology, proper-stage and proper-model proofs and covers arbitrary independently supplied models in both characteristics. Its internal reductions are `adelicSpaceSpreadProperMap_of_inputs`, `_of_arithmeticInputs` and `_of_properModel` (intermediate statements below) |
| Thm 5.9 | smooth surjective geometrically connected: open on adelic points | `AdelicSpaceSpreadSmoothOpenStatement`; input `SpaceUniformLangWeilStatement`; local input `CompleteFieldSmoothSpacePointOpenStatement` (intermediate statements below) | arbitrary separated finite-type models, curves need finite `k` and nonempty `S`; `g` smooth, surjective, with geometrically connected fibres; the Lang–Weil input: base quasi-separated of finite type over `Z`, `f` smooth of relative dimension `d` on étale charts, separated, quasi-compact, surjective, with geometrically connected fibres | proved (`adelicSpaceSpreadSmoothOpen : AdelicSpaceSpreadSmoothOpenStatement.{u}`, module `Langlands/Global/AdelicSpaceSpreadSmoothOpenProof`) at commit `2e46b9ca`. The theorem supplies the exact space Lang–Weil premise to the arbitrary-model reduction using `spaceUniformLangWeilOfFamily (familyLangWeilOfPlaneCurve planeCurveHasseWeil) familyPointUpperBound`. No extra hypothesis or fixed relative dimension is assumed; both original model topologies are retained. The separately named exact space estimate is also published as `spaceUniformLangWeil` (module `AlgebraicSpace/SpaceUniformLangWeilProof`) |

Source corrections, first part:

- **Ex 5.5.** Conrad asserts that `(V_d/G)(k)` is locally Hausdorff and locally compact. This
  rests on Proposition 5.4 and fails for quotients that are not locally separated;
  `UnipotentOrbitQuotientStatement.md` gives a counterexample (a variant of Stacks, Tag 02Z1,
  over any henselian field of characteristic zero). The topology clause of
  `UnipotentOrbitQuotientStatement` therefore assumes the quotient locally separated, and
  qualifies local compactness and total disconnectedness by local compactness and
  ultrametricity of `K`. The strata and quotient clauses keep the source's scope.
- **Prop 5.4.** The unrestricted six-property package fails for quasi-separated spaces
  that are not locally separated (Stacks, Tag 02Z1): the chart at zero is not locally
  injective, and the relation-point topology is not the fibre-product subspace topology.
  The aggregate `HenselianSpacePointTopologyStatement` and the manifold family therefore
  add local separatedness. The chart-topology construction, functoriality, scheme
  agreement, immersion embeddings and étale openness remain valid in the broader class,
  by the separately recorded theorems above. The pure-dimensional manifold theorem still
  requires the actual-piece bridge to cover all smooth spaces promised in the corrected statement.
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
| Lem 5.10 | Weil restriction of spaces along finite locally free maps is an algebraic space; finite type, separated, finite presentation | `ringWeilRestriction`, `ringWeilRestrictionSpace` (`SpaceWeilRestriction`), `SpaceWeilRestrictionStatement` | `R → R'` finite projective; `X'` quasi-separated of finite type over `R'` | proved (`spaceWeilRestriction`, module `SpaceWeilRestrictionProof`; it applies `spaceWeilRestriction_of_geometricInputs` to the two proved statements of `WeilRestrictionGeometricInputsStatement`, intermediate statements below) |
| Prop 5.11(1) | finite extension: `Res(Y')(k) = Y'(k')` homeomorphism | `HenselianWeilRestrictionPointHomeomorphStatement` | henselian `K` and `K'`, `K'` a finite-dimensional normed `K`-algebra; `Y'` quasi-separated of finite type; no module-topology hypothesis (correction below) | false as stated (note `finite-weil-inseparable-obstruction.md`; the section "Correction to the literal Proposition 5.11(1)" of `SpaceWeilRestrictionStatement.md`, records the correction) |
| Prop 5.11(1), corrected | the same homeomorphism when `K'` carries the `K`-module topology, as in Conrad's proof through Example 2.4 | `HenselianWeilRestrictionPointHomeomorphOfModuleTopologyStatement` (module of the same name) | as above plus `IsModuleTopology K K'`, which holds for complete `K`; the conclusion includes that the Weil restriction is an algebraic space | proved (`henselianWeilRestrictionPointHomeomorphOfModuleTopology`, module `HenselianWeilRestrictionPointHomeomorphOfModuleTopologyProof`; it applies `isHomeomorph_ringWeilRestrictionBasePointsEquiv` (intermediate statements below) to the algebraic space, quasi-separated and of finite type, given by `spaceWeilRestriction` (Lemma 5.10)) |
| Prop 5.11(2) | `X(k) → X(k̂)` topological embedding | `HenselianCompletionPointEmbeddingStatement` | henselian `K`; `X` quasi-separated, locally of finite type | proved (`henselianCompletionPointEmbedding`) |
| Prop 5.11(3) | `X(k) → X(k')` embedding, closed if `k` closed in `k'`, for spaces covered by separated opens | `HenselianExtensionPointEmbeddingStatement`, `IsCoveredBySeparatedOpenSubspaces` | henselian `K`, `K'`, `K'` a normed `K`-algebra of any degree; `X` quasi-separated, locally of finite type, covered by separated open subspaces | proved (`henselianExtensionPointEmbedding`, module `HenselianExtensionPointEmbeddingProof`: `ExtensionClosedReduction.henselianExtensionPointEmbedding_of_complete CompleteExtensionClosedRange.completeExtensionPointClosedRange`; the embedding conjunct is also proved directly by `ExtensionLocalReduction.isEmbedding_of_covered`; intermediate statements below) |
| Prop 5.11, proof (p.19) | finite extensions: `X(k) → X(k')` is an embedding when `Δ_{X/k}` is a quasi-compact immersion, without completeness | `HenselianFiniteExtensionPointEmbeddingStatement` | henselian nontrivially normed fields `K`, `K'`, `K'` a finite-dimensional normed `K`-algebra; `X` quasi-separated, locally of finite type and locally separated (immersive diagonal); no separated open cover, no completeness; embedding only, no closedness | proved (`henselianFiniteExtensionPointEmbedding`, a direct argument with étale charts and finite Galois descent that uses neither Proposition 5.11(1) nor completeness) |
| Cor 5.12 | finite maps proper on points if `k` algebraically closed in `k̂`; characteristic-zero case | `HenselianFinitePointProperStatement`, `HenselianCharZeroAlgebraicallyClosedInCompletionStatement` | henselian `K` algebraically closed in its completion; `X`, `Y` separated, locally of finite type; `f` finite | proved (`henselianFinitePointProper`, `HenselianCharZeroCompletionProof`) |
| Ex 5.13 | quasi-compact immersive diagonal does not suffice for closedness | `HenselianExtensionPointNotClosedStatement` (`HenselianExtensionPointCounterexampleStatement`) | complete ultrametric `K`, separable quadratic `K'`; a quasi-separated space locally of finite type with affine immersive diagonal | proved (`henselianExtensionPointNotClosed`; the space is the Galois-twisted line of the `GaloisTwistedLine…` modules) |
| Prop 5.14 | adelic Weil restriction homeomorphism for separated finite type spaces | `AdelicSpaceWeilRestrictionStatement` | finite `F'/F`; `Y'` separated of finite type; arbitrary separated finite-type models; curves need finite `k` and nonempty `S`, `S'` | proved (`adelicSpaceWeilRestriction`, module `Langlands/Global/AdelicSpaceWeilRestrictionProof`, with the clauses `AdelicSpaceWeilRestrictionProof.numberFieldSpaceWeilRestriction` and `AdelicSpaceWeilRestrictionProof.curvePlaceSpaceWeilRestriction`; supporting modules in the constructions paragraphs below) |

The excellent-valuation-ring sufficient condition after Corollary 5.12 is a cited fact; only
its characteristic-zero part is stated.

Source correction, Proposition 5.11(1): the proof (printed p.18) reduces to the affine case of
Example 2.4 (printed p.3), which assumes that `k'` carries the topology of a finite free
`k`-module. That holds for complete `k`, but not for every henselian `k`. For a henselian `k`
whose completion contains a proper finite purely inseparable extension `k'`, `k` is dense in
`k'`. Then `Res_{k'/k}(A^1)(k) = k^{[k':k]}` with the product topology cannot be homeomorphic to
`k'` by the canonical bijection. The published note
[`finite-weil-inseparable-obstruction.md`](finite-weil-inseparable-obstruction.md)
gives the construction from Temkin's *Valued Fields*, Exercise 1.8.11 and Remark 1.9.6.
The formalization adopts this mathematical obstruction and the module-topology correction.
The literal statement, and the published
`HenselianWeilRestrictionPointHomeomorphStatement` that transcribes it, are false. The corrected
statement `HenselianWeilRestrictionPointHomeomorphOfModuleTopologyStatement`, with
`IsModuleTopology K K'`, is published and proved
(`henselianWeilRestrictionPointHomeomorphOfModuleTopology`). The module
`SpaceWeilRestrictionStatement.lean` defines both `SpaceWeilRestrictionStatement` (Lemma 5.10)
and the literal `HenselianWeilRestrictionPointHomeomorphStatement`; its Markdown now records
this correction, and its Lean file is unchanged. Conrad applies Proposition
5.11(1) to complete fields in Proposition 5.14 (at local fields) and in the finite-degree case
of Proposition 5.11(3) (after the reduction to completions through part (2)); these uses are
unaffected. The parenthetical on p.19 applies it without completeness. The Library proof of
that finite-degree assertion (`henselianFiniteExtensionPointEmbedding`, row "Prop 5.11, proof
(p.19)") does not take this step: it argues with étale charts and finite Galois descent and uses
neither Proposition 5.11(1) nor completeness.

## Retained analytification input (Conrad p.19)

These are substantive inputs retained by the formalization. The extension-point endpoint
in the preceding table is already proved by another route; that does not supply
these constructions and comparisons. The analytic setting in the Library is the existing
`Langlands.Analytic.SaturatedAtlasPresentation.LocalizedCategory`, reached from
actual affinoid atlases. A realization there must have a proved comparison with
the analytic étale sheaf quotient used in the source.

The additional registered original is Conrad–Temkin, *Non-archimedean
analytification of algebraic spaces*, first-author final preprint, 24 February
2009, **35 pages**, source `conrad-temkin-2009-nonarchimedean-analytification`,
SHA-256 `ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.
Its §2.2, pp.7–8, defines the intrinsic analytic quotient sheaf and its
functoriality; Theorem 2.3.1 and Example 2.3.2, pp.11–12, supply the geometric
and rational-point comparisons; Theorem 2.3.5, p.13, gives arbitrary analytic
field extension; Theorems 4.2.1–4.2.2, p.20, supply separated-space and analytic
quotient existence. The rows keep these mathematical conclusions visible;
existing analytic foundations alone are not an algebraic-to-analytic bridge.

| Source | Assertion | Lean declarations | Hypotheses and scope | Status |
| --- | --- | --- | --- | --- |
| Conrad p.19, scheme case; CT §2.2 input | actual finite-type affine scheme analytification | `Langlands.Analytic.AffineAnalytification.Space`, `chartSystem` (`AffineAnalytificationGluing`); `atlas`, `saturated`, `localized` in the same namespace (`AffineAnalytificationAtlas`); `Langlands.Analytic.AffineSchemeAnalytification.spec`, `affineFiniteType`, `CoordinateRing`, `coordinateIso` (`AffineSchemeAnalytification`). Section checked at `18790533`: `FiniteTypeDomainNormExtensionStatement` | complete nontrivially valued nonarchimedean `K`; every finite-type commutative `K`-algebra, including nonreduced and zero algebras, the empty scheme and zero polynomial variables; actual polynomial-kernel quotient algebras, radius restrictions and atlas laws | constructed with intrinsic chart/algebra laws, first appeared in the Library at `af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e`. The wrapper uses actual global sections and the canonical affine scheme isomorphism in Mathlib's common universe. Affine maps, rational points, seminorm points, the center map and the scalar-extension comparison map are now constructed. The affine rational-point, functoriality, naturality, immersion and seminorm statements are published. The center and base-change statements first appeared in the Library at `ccd5c6bb63352c109b2bfde422a65c2dd78e57fd` (section checked at `e1fa6f68`). Their proofs, the universal property and the scalar-extension isomorphism remain open. section checked at `b44618a4`: the localized maps and the maps from affinoid spectra are constructed. The universal property for maps from affinoid spectra is stated, not proved. Section checked at `18790533`: the universal property is proved (`affineAnalytificationAffinoidUniversal`), and so is the seminorm description (`affineAnalytificationSeminorm`). The norm input of the center statement is stated, not proved (`FiniteTypeDomainNormExtensionStatement`). The center and base-change statements remain open. section checked at `8aede86c`: the base-change statement is proved (`affineAnalytificationBaseChange`). section checked at `24390f9f`: the norm input (`finiteTypeDomainNormExtension`) and the center statement (`analytificationCenter`) are proved. Every statement of this row is now proved; the scalar-extension isomorphism belongs to the scalar-extension row |
| Conrad p.19, scheme agreement | affine independence and general scheme analytification by gluing | `Langlands.Analytic.SchemeAnalytification.Space`, `ι`, `localMap`, `desc` (`SchemeAnalytificationSpace`); `SchemeAnalytificationGluingStatement`; affine presentation independence in `AffineAnalytificationFunctorialityStatement` and `AffineAnalytificationLocalizedFunctorialityStatement`; `morphismLocalMap`, `IsAnalytificationMap` (`SchemeAnalytificationMorphism`); `SchemeAnalytificationMorphismStatement`; `SchemeAnalytificationAnalyticStructureStatement`; `Langlands.Analytic.SpaceAnalytification.SpaceAnalytificationSchemeStatement` | complete nontrivially valued nonarchimedean `K`; schemes locally of finite type, without a global affineness or finite-type restriction; actual affine constructions, restriction/gluing maps, independence and scheme morphisms | topological gluing constructed (first appeared in the Library at `0b7bb3fdbe6e0386b666b6b099a3bc9cd3ad7e18`). Its gluing properties are stated but not proved: open embeddings, intersections, the affine case, and separated ⇔ Hausdorff. The statement first appeared in the Library at `b3dcc8cc4c93f1140c6b34374f589ccc637a1a22`. Affine presentation independence is stated. Not constructed: maps of glued spaces for scheme morphisms and an analytic-space structure on the glued space. section checked at `b44618a4`: both are now stated, not proved, and neither is constructed explicitly. The compatibility predicate `IsAnalytificationMap` is defined. The existence and uniqueness of compatible maps of glued spaces, with centers, rational points and composites, is stated. An analytic-space structure on the glued space with the affine analytifications as open domains is stated. Presentation independence in the localized category is stated. For a separated scheme, the underlying space of its algebraic-space analytification is stated to be homeomorphic to `Space K f`, compatibly with charts and rational points. Section checked at `18790533`: affine presentation independence is proved (`affineAnalytificationFunctoriality` and `affineAnalytificationLocalizedFunctoriality`). The gluing, scheme-morphism, analytic-structure and scheme-comparison statements remain open. section checked at `8aede86c`: the scheme-morphism statement is proved (`schemeAnalytificationMorphism`, module `SchemeAnalytificationMorphismProof`). A saturated presentation of the glued space is constructed under the open-gluing clauses of the gluing statement (`schemePresentation`, module `SchemeAnalytificationAnalyticStructure`); this reduces the analytic-structure statement to the gluing statement without proving either. The gluing, analytic-structure and scheme-comparison statements remain open. section checked at `24390f9f`: all three are proved: gluing (`schemeAnalytificationGluing`), the analytic structure of the glued space (`schemeAnalytificationAnalyticStructure`) and the comparison with the algebraic-space analytification of a separated scheme (`spaceAnalytificationScheme`, module `SpaceAnalytificationSchemeComparison`). Every statement of this row is now proved |
| CT Lemma 2.2.1, Definition 2.2.2, Theorems 4.2.1–4.2.2 | actual representable analytic étale sheaf quotient and chart independence | no actual scheme-to-analytic quotient construction identified; the existing analytic category and étale-site infrastructure do not give this bridge. section checked at `b44618a4`: `Langlands.Analytic.SpaceAnalytification.PointFamily`, `IsAnalytification`, `rationalPoint` (`SpaceAnalytification`); `SpaceAnalytificationExistenceStatement`, `SpaceAnalytificationMorphismStatement` | quasi-separated separated algebraic spaces locally of finite type over complete nontrivially valued nonarchimedean `K`; an actual étale chart `R ⇉ U`, analytic quotient sheaf of `Uᵃⁿ` by `Rᵃⁿ`, its representation by an analytic space and canonical chart comparisons | not stated; a quotient of bare point sets is insufficient. section checked at `b44618a4`: characterized and stated, not constructed or proved. `IsAnalytification` characterizes an analytic space `Y` of the localized category with maps from the analytifications of all affine test points: natural, étale on étale points, jointly surjective from étale points, and sending affine fibre squares to pullbacks. Its Markdown relates it to the quotient of Conrad–Temkin, Definition 4.1.1. Existence for separated spaces locally of finite type is stated. Uniqueness of compatible morphisms is stated; applied to the identity, it makes any two analytifications of a separated space locally of finite type isomorphic by a unique compatible isomorphism. No quotient `Uᵃⁿ/Rᵃⁿ` of an étale chart is constructed. section checked at `24390f9f`: the existence and morphism statements remain open. `SpaceAnalytificationExistenceReduction` derives the existence statement from seven explicit hypotheses and proves none of them. `SpaceAnalytificationExistenceFiveInputReduction` discharges input 4 by `affineAnalytificationFibreProduct` and input 7 by the unconditional joint-surjectivity theorem `exists_mem_range_localizedHom`; five premises remain unproved, so the existence statement is still open. Three of them (the étale Hom-sheaf property, étale source descent and `LocalizedEtalePullbackStatement`) quantify over every complete ultrametric normed field, trivial valuations included; the chart-quotient and affine-étaleness premises use nontrivially normed fields. section checked at `cf95b60a`: `LocalizedEtalePullbackStatement` is proved (`localizedEtalePullbackBaseChange`, module `LocalizedEtalePullbackProof`). `spaceAnalytificationExistenceStatement_of_inputs` (module `SpaceAnalytificationExistenceReduction`) derives `SpaceAnalytificationExistenceStatement` given a quotient for every covering chart family of a separated algebraic space over each complete ultrametric nontrivially normed `K`, together with `AnalyticInputs K` over every such `K`. The morphism statement is proved (`spaceAnalytificationMorphism`, module `SpaceAnalytificationMorphismProof`) without the étale Hom-sheaf premise |
| Conrad p.19; CT Theorems 2.2.3 and 2.3.1 | functoriality, fibre products, open and closed immersions and étale maps | `Langlands.Analytic.AffineAnalytification.baseMap`, `strongHom` (`AffineAnalytificationMap`); `AffineAnalytificationFunctorialityStatement`, `AffineAnalytificationRationalPointNaturalityStatement`, `AffineAnalytificationImmersionStatement`; no scheme or algebraic-space interface. section checked at `b44618a4`: `saturatedHom`, `localizedHom` (`AffineAnalytificationLocalizedMap`); `Langlands.Analytic.SaturatedAtlasPresentation.closedImmersion`, `openImmersion` (`AnalyticImmersion`); the affine statements `AffineAnalytificationLocalizedFunctorialityStatement`, `AffineAnalytificationFibreProductStatement`, `AffineAnalytificationEtaleStatement`, `AffineAnalytificationAnalyticImmersionStatement`; `SchemeAnalytificationMorphismStatement`; the algebraic-space statements `SpaceAnalytificationMorphismStatement`, `SpaceAnalytificationEtaleStatement`, `SpaceAnalytificationFibreProductStatement`, `SpaceAnalytificationImmersionStatement`, `SpaceAnalytificationAnalyticImmersionStatement`. Section checked at `18790533`: inputs to the affine étale statement, `AffineAnalytificationQuasiFiniteStatement`, `AffineAnalytificationFiniteGermComparisonStatement`, `AffineAnalytificationChartFlatStatement` | the separated locally finite-type class above, every morphism, the actual scheme/quotient realization and actual analytic comparison maps; no smoothness or fixed-dimension restriction | affine case stated, not proved; all three statements were published at `0b7bb3fdbe6e0386b666b6b099a3bc9cd3ad7e18`. They cover identities, composites and presentation independence, naturality of analytic rational points, and closed and basic open immersions. Not stated: fibre products, étale maps, and maps for general scheme and algebraic-space morphisms. section checked at `b44618a4`: all are now stated, none proved. Affine: localized functoriality, fibre products, unramified, flat and étale maps, and analytic open and closed immersions in both directions. Schemes: maps for morphisms. Algebraic spaces: unique compatible morphisms, étale maps in both directions, fibre products, open and closed embeddings of underlying spaces and analytic immersions. The last asserts both directions for open immersions, the forward direction for closed immersions, and the converse for closed immersions when `f` is quasi-compact; its Markdown gives a counterexample without quasi-compactness. Section checked at `18790533`: three affine statements are proved: identities, composites and presentation independence (`affineAnalytificationFunctoriality`), naturality of analytic rational points (`affineAnalytificationRationalPointNaturality`) and localized functoriality (`affineAnalytificationLocalizedFunctoriality`). Three inputs to the affine étale statement are stated, not proved: quasi-finiteness is detected by the analytification; at points where the analytified map is finite, its flatness and unramifiedness agree with the algebraic ones; and the chart algebras are flat over the algebra. The other statements of this row were open at that commit. section checked at `8aede86c`: closed and basic open immersions of affine analytifications are proved (`affineAnalytificationImmersion`, module `AffineAnalytificationImmersionProof`), and so are the maps for scheme morphisms (`schemeAnalytificationMorphism`). The other statements of this row remain open. section checked at `24390f9f`: proved are affine fibre products (`affineAnalytificationFibreProduct`), the three inputs of the affine étale statement, namely quasi-finiteness (`affineAnalytificationQuasiFinite`), the finite-germ comparison (`affineAnalytificationFiniteGermComparison`) and chart flatness (`affineAnalytificationChartFlat`; `affineAnalytificationChart_flat`), and open and closed embeddings of underlying spaces for algebraic spaces (`spaceAnalytificationImmersion`). Open are affine étale maps, affine analytic immersions, and for algebraic spaces morphisms, étale maps, fibre products and analytic immersions. `SpaceAnalytificationFibreProductReduction` reduces the fibre-product statement to explicit premises without proving it. Toward the immersion statements, `closedImmersion_localizedHom_of_surjective` proves that a surjective algebra map gives a closed immersion of localized affine analytifications, and `mono_of_mono_analytification_of_isSeparated` reflects analytic monomorphisms for separated algebraic spaces with a source locally of finite type; the space-level open and closed immersion reflection theorems assume further analytic inputs. Neither immersion statement is proved. section checked at `cf95b60a`: proved are the affine étale statement (`affineAnalytificationEtale`) and, for algebraic spaces, the morphism, étale, fibre-product and analytic-immersion statements (`spaceAnalytificationMorphism`, `spaceAnalytificationEtale`, `spaceAnalytificationFibreProduct`, `spaceAnalytificationAnalyticImmersion`). `AffineAnalytificationAnalyticImmersionStatement` states the two equivalences. `closedImmersion_localizedHom_of_surjective` proves the forward closed-immersion implication |
| Conrad p.19; CT Example 2.3.2, pp.11–12 | rational points and their topology | `Langlands.Analytic.AffineAnalytification.analyticPoint`, `toFieldPoint`, `toAlgPoint` (`AffineAnalytificationRationalPoints`); `AffineAnalytificationRationalPointsStatement`; `Langlands.Analytic.SchemeAnalytification.analyticRationalPoint` (`SchemeAnalytificationRationalPoints`); `FieldValuedPoints` supplies analytic chart characters. section checked at `b44618a4`: `Langlands.Analytic.SpaceAnalytification.rationalPoint` (`SpaceAnalytification`); `SpaceAnalytificationRationalPointsStatement`, `SpaceAnalytificationSchemeStatement`. section checked at `f24f9744`: `SpaceAnalytificationFieldPointsStatement`; `localizedFieldPointFunctor`, `localizedFieldPointProjection` (`FieldValuedPoints`) | the same fields and separated locally finite-type spaces; natural equivalence of actual algebraic and analytic rational points and homeomorphism between the affine-chart analytic topology and `etaleChartTopology`; agreement on schemes and descent through actual étale charts | affine case stated, not proved: the statement first appeared in the Library at `0b7bb3fdbe6e0386b666b6b099a3bc9cd3ad7e18`. It states a bijection with the atlas `K`-points and a topological embedding of `X(K)` into `Xᵃⁿ`. The scheme map is constructed (first appeared in the Library at `b3dcc8cc4c93f1140c6b34374f589ccc637a1a22`). Its statement (chart independence, injectivity, range, and an embedding for `schemePointTopology`) first appeared in the Library at `ccd5c6bb63352c109b2bfde422a65c2dd78e57fd`; it is not proved. Not stated: the comparison with `etaleChartTopology` for algebraic spaces and descent through étale charts. The already-proved extension-point theorem does not supply them. section checked at `b44618a4`: the topological comparison for algebraic spaces is stated, not proved. For a separated space locally of finite type, the analytification is Hausdorff and `rationalPoint` is a topological embedding of `X(K)` with `etaleChartTopology`. For a separated scheme, the homeomorphism of `SpaceAnalytificationSchemeStatement` carries `rationalPoint` to `analyticRationalPoint`. Not stated: that the image of `rationalPoint` is the set of `K`-points of the analytic space. section checked at `f24f9744`: now stated, not proved. The `K`-valued points of the analytification are determined by their underlying points and correspond bijectively to `X(K)` over `rationalPoint`. Section checked at `18790533`: the affine statement is proved (`affineAnalytificationRationalPoints`). The scheme, algebraic-space and `K`-valued-point statements remain open. section checked at `24390f9f`: proved are the algebraic-space statement (`spaceAnalytificationRationalPoints`), the `K`-valued-point statement (`spaceAnalytificationFieldPoints`) and the scheme comparison (`spaceAnalytificationScheme`). The scheme rational-point statement remains open. Checked against the Library as it is: it is now proved (`schemeAnalytificationRationalPoints`), so every statement of this row is proved |
| Conrad p.19; CT Theorem 2.3.5 | arbitrary complete nonarchimedean scalar extension | `Langlands.Analytic.AffineAnalytification.extensionMap`, `baseChangePresentation`, `baseChangeMap` (`AffineAnalytificationScalarExtension`); no isomorphism `(Xᵃⁿ)_L ≅ (X_L)ᵃⁿ`. At commit `18790533`: `Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension.algebra`, `iota`, `lift`, `functor`, `spectrumProjection` (`GeneralizedAffinoid/GroundFieldExtension`); `tensorEquiv` (`GeneralizedAffinoid/GroundFieldExtensionTensor`); `SpectrumProjectionSurjectiveStatement`, `DomainPreservationStatement`; `Langlands.Analytic.AffinoidChartSystem.AtlasProjection` (`AffinoidChartLift`) and `AtlasProjection.TopologyStatement` | every complete nontrivially valued nonarchimedean extension `L/K`, with no finite-degree, separability or algebraicity restriction; canonical analytic isomorphism `(Xᵃⁿ)_L ≅ (X_L)ᵃⁿ`, naturality, composition in towers and fibre-product compatibility | comparison map only. For affine `X` and every complete extension `L/K`, the continuous map `(X_L)ᵃⁿ → Xᵃⁿ` is constructed (first appeared in the Library at `b3dcc8cc4c93f1140c6b34374f589ccc637a1a22`). Its surjectivity and rational-fibre statement first appeared in the Library at `ccd5c6bb63352c109b2bfde422a65c2dd78e57fd`; it is not proved. Not constructed or stated: the analytic ground-field extension `(Xᵃⁿ)_L`, the canonical isomorphism, naturality, towers and fibre products. A finite-extension-only comparison is insufficient. section checked at `b44618a4`: unchanged. This Library contains no construction of the ground-field extension of presented affinoid algebras and affinoid atlases. Section checked at `18790533`: The algebra level first appeared in the Library at `2613dbbf784309977c42d9252b78c1e1cd40be63`. For ultrametric normed fields with `NormedAlgebra K L`, every presented `K`-affinoid algebra `A` has a presented `L`-affinoid extension `A_L`, with the structure map `iota`, a universal property (`lift`), a functor and the restriction map on spectra. For complete `L`, `tensorEquiv` identifies `A_L` with the completed tensor product `A ⊗̂_K L` as bounded `K`-algebras. For complete `K` and `L`, surjectivity of the spectrum projection is proved (`spectrumProjection_surjective`, module `GeneralizedAffinoid/GroundFieldExtensionSurjectiveProof`, first at `fd643ecec6997ef17c8356ddbc924138631307d9`). Preservation of affinoid domains (`DomainPreservationStatement`) is stated, not proved. `AtlasProjection` packages projections from a quotient chart system over `L` to an affinoid atlas over `K`, and its topological laws are proved (`AtlasProjection.topology`, module `AffinoidChartLiftTopology`, first at `fd643ecec6997ef17c8356ddbc924138631307d9`). The ground-field extension of affinoid atlases and analytic spaces, the canonical isomorphism, naturality, towers and fibre products are still neither constructed nor stated. section checked at `8aede86c`: the surjectivity and rational-fibre statement for affine `X` is proved (`affineAnalytificationBaseChange`, module `AffineAnalytificationBaseChangeProof`). The rest of this row is unchanged. section checked at `24390f9f`: preservation of affinoid domains is proved (`domainPreservation`, module `GeneralizedAffinoid/GroundFieldExtensionDomainProof`). The ground-field extension of affinoid atlases is constructed: `Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension.chartSystem`, `presentation`, `projection` and `projection_surjective` (`GroundFieldExtensionChartSystem`, `GroundFieldExtensionAtlas`), for complete ultrametric normed fields `K`, `L` with `NormedAlgebra K L`, with no coherence hypothesis on the atlas. By the convention recorded in the section checked at `24390f9f`, the map part extends `CompatibleStrongHom` maps between arbitrary presentations and every `StrongHom` with saturated source, and gives the functor from `SaturatedAtlasPresentation K` to the localized category over `L`; `StrongHom` is not strengthened, because of the Frobenius witness `weakMap` (`GroundFieldExtensionCounterexample/WeakMap`). These map extensions and the functor, its descent through quasi-isomorphisms to the localized category over `K`, the canonical isomorphism, naturality, towers and fibre products are still neither constructed nor stated |

## Derived intermediate statements and reductions

The following statements and proved reductions belong to the Lang–Weil and Example 5.5 parts
of the formalization. They are derived steps of Conrad's proofs, or cited results such as the
Stacks Project lemmas in two Theorem 3.4(2) rows, three Corollary 5.6 rows and one
Proposition 5.8 row and the SGA 3 and Milne results in two Example 5.5 rows, not separate
assertions of the paper. Each row names the source row it serves, and the status column gives
its proof where one exists.

| Serves | Lean declarations | Hypotheses and scope in Lean | Status |
| --- | --- | --- | --- |
| Lem 4.6 | `FamilyLangWeilInDimension`, `FamilyLangWeilStatement` (`LangWeil/FamilyLangWeilStatement`) | `S` of finite type over `Z`; `f : X → S` of finite type, geometrically irreducible, with all fibres of pure dimension `d`; a constant `C > 0` with `\|#X_s(κ) − q^d\| ≤ C·q^(d−1/2)` for every finite field `κ` with `q` elements and every `κ`-point `s` of `S`; the second statement asserts this for every `d` | proved by the published composition `familyLangWeilOfPlaneCurve planeCurveHasseWeil` at commit `9b849cab`; the first theorem supplies the dimension induction and the second discharges its sole premise. This uses the unchanged zero, curve, slicing, generic Bertini and uniform upper-bound proofs. A separate unconditional family-estimate theorem name is not claimed. The final scheme and space uniform estimates are published as `uniformLangWeil` and `spaceUniformLangWeil` at commit `2e46b9ca` |
| Lem 4.6 | `FamilyLangWeilOfPlaneCurveStatement` (`LangWeil/FamilyLangWeilOfPlaneCurveStatement`) | exactly `PlaneCurveHasseWeilStatement.{u} → FamilyLangWeilStatement.{u}`, with the unchanged full scope of both propositions and no further premise | proved (`familyLangWeilOfPlaneCurve`, module `LangWeil/FamilyLangWeilOfPlaneCurveProof`, at commit `9b849cab`). It performs induction on positive dimensions and uses the zero case separately; the upper-bound and Bertini premises are discharged by their published proofs. The theorem retains the plane-curve premise, now supplied by `planeCurveHasseWeil` |
| Lem 4.6 | `FamilyPointUpperBoundStatement` (`LangWeil/`) | `S` of finite type over `Z`; `f : X → S` of finite type; a constant `C > 0` with `#X_s(κ) ≤ C·q^e` for every finite field `κ`, every `κ`-point `s` and every `e` bounding the dimension of the fibre over the image of `s` | proved (`familyPointUpperBound`, module `LangWeil/FamilyPointUpperBoundProof`: `familyPointUpperBound_of_finiteNormalizationCover finiteNormalizationCover`; rows below) |
| Lem 4.6 | `FiniteNormalizationCoverStatement`, with the structure `FiniteNormalizationCover` (`LangWeil/`) | `S` Noetherian; `f : X → S` locally of finite type and quasi-compact (no separatedness, reducedness or equidimensionality); conclusion: finitely many pieces, each an affine scheme `T_i` with an immersion `T_i → S`, an immersion `U_i → X`, a natural number `d_i` and a finite surjective map `U_i → A^{d_i}_{T_i}` compatible with `f`, such that every `Spec K → X` with `K` a field (same universe) factors through some `U_i`, and `d_i` is at most the topological Krull dimension of the fibre of `f` over the image of every point of `T_i`; derived from the Stacks Project, Lemma 10.115.4 (Tag 00OY) and Section 33.18 with Lemma 33.18.2 (Tags 0CBG, 0CBI) | proved (`finiteNormalizationCover`, module `LangWeil/FiniteNormalizationCoverProof`, with `LangWeil/FiniteNormalizationCoverAlgebra`, `LangWeil/FiniteNormalizationCoverPieces` and `LangWeil/FiniteNormalizationCoverAffine`, declarations prefixed `LangWeil.NormalizationCoverConstruction.`) |
| Lem 4.6 | `familyPointUpperBound_of_finiteNormalizationCover` (`LangWeil/NormalizationCoverPointBound`) | `FiniteNormalizationCoverStatement` implies `FamilyPointUpperBoundStatement`, in the same universe | proved (conditional on `FiniteNormalizationCoverStatement`, which is proved by `finiteNormalizationCover`; `familyPointUpperBound` applies it to that theorem) |
| Lem 4.6 | `PlaneCurveHasseWeilStatement`, `BertiniGenericHyperplaneStatement` (`LangWeil/`) | Schmidt's bound: a finite field `F` with `q` elements; `f ∈ F[X,Y]` absolutely irreducible with `a = deg_X f > 0`, `b = deg_Y f > 0` and `9(a+1)²(b+1)² < q`; the number `N` of affine zeros satisfies `\|N − q\| < 2·min(a²b, ab²)·√q`. Bertini: any field `k`; a `k`-algebra `A` generated by `g_1, …, g_n`, geometrically irreducible over `k` of Krull dimension at least 2; the generic hyperplane section `u_0 + Σ u_i g_i = 0` over the fraction field of `k[u_0, …, u_n]` is geometrically irreducible | Schmidt's bound proved (`planeCurveHasseWeil`, module `LangWeil/PlaneCurveHasseWeilProof`, at commit `9b849cab`). It applies `planeCurveHasseWeil_of_stepanov` to the now-proved `Stepanov.stepanovNormPolynomials` and `planeCurveElementaryReductions`, with no extra premise. Bertini proved (`BertiniGenericHyperplane.bertiniGenericHyperplaneStatement`, module `LangWeil/BertiniGenericHyperplaneProof`, with `LangWeil/BertiniHyperplaneSeparable`, `LangWeil/BertiniHyperplaneKernel`, `LangWeil/BertiniHyperplaneCore` and `LangWeil/BertiniHyperplaneDimension`, declarations prefixed `BertiniGenericHyperplane.`; finite `k` included, by reduction to an algebraically closed field) |
| Lem 4.6 | `StepanovNormPolynomialsStatement` (`LangWeil/`) | any finite field `F`, `q = Nat.card F`; an absolutely irreducible `f ∈ F[X,Y]` with both partial derivatives nonzero and partial degrees `m ≥ n ≥ 2`; `r(x)` counts `y ∈ F` with `f(x,y) = 0`; for every `M > 0` with `M²(n²+1) + (M+m)n² < q` and `Mn ≤ q`, there exist a finite good set `s` and nonzero `h₁,h₂ ∈ F[X]` with `q < s.card + 2mn`, the bound `r(x) ≤ n` for every rational fibre, degrees below `q(M+E)` and `q((n−1)M+E)` for `E = 2m(n−1)+1`, and multiplicities at least `M r(x)` and `M(n−r(x))` on `s`; this is the algebraic input to the next counting row | proved (`Stepanov.stepanovNormPolynomials`, module `LangWeil/Stepanov/NormPolynomials`, with the supporting `Stepanov/` modules at commit `9b849cab`). The proof constructs the two nonzero norm polynomials, the good set, and the required degree and multiplicity bounds; these data are no longer an unproved input to `stepanovCounting` |
| Lem 4.6 | `StepanovCountingStatement` (`LangWeil/`) | a finite field `F` with `q` elements; any `r : F → ℕ`; `2 ≤ n ≤ m` and `9(m+1)²(n+1)² < q`; hypothesis: for every `M > 0` with `M²(n²+1) + (M+m)n² < q` and `Mn ≤ q` there are `s ⊆ F` and `h_1, h_2 ∈ F[X]` with `q < \|s\| + 2mn`, `r(x) ≤ n` for every `x`, `deg h_1 < q(M+E)` and `deg h_2 < q((n−1)M+E)` for `E = 2m(n−1)+1`, and root multiplicities at least `M·r(x)` and `M·(n−r(x))` at every `x ∈ s`; conclusion: `\|Σ_x r(x) − q\| < 2mn²·√q`; a derived abstraction of Schmidt, *Zur Methode von Stepanov* (1973), Section 7, pp.359–360 (equation (40)), and Section 9, p.367 | proved (`stepanovCounting`, module `LangWeil/StepanovCountingProof`) |
| Lem 4.6 | `PlaneCurveElementaryReductionsStatement` (`LangWeil/`) | two clauses over any finite field `F`, for `f ∈ F[X,Y]` absolutely irreducible: (1) if both partial degrees of `f` are positive, some absolutely irreducible `g` with both partial derivatives nonzero, `0 < deg_Y g ≤ deg_X g`, `deg_X g ≤ max(deg_X f, deg_Y f)` and `deg_Y g ≤ min(deg_X f, deg_Y f)` has the same number of affine `F`-zeros as `f`; (2) if `deg_Y f = 1`, the number of affine `F`-zeros of `f` differs from `#F` by at most `deg_X f`; derived from Schmidt (1973), Section 2, p.349 | proved (`planeCurveElementaryReductions`, module `LangWeil/PlaneCurveElementaryReductionsProof`, with `LangWeil/PlaneCurveLinearFibres`, `LangWeil/PlaneCurveSeparableModel` and `LangWeil/PlaneCurveCoordinateOperations`) |
| Lem 4.6 | `FamilyLangWeilZeroStatement` (`LangWeil/`) | the family estimate in dimension 0, with the hypotheses of `FamilyLangWeilInDimension 0` | proved (`familyLangWeilZero`, module `LangWeil/FamilyLangWeilZeroProof`; the proof shows that every fibre has exactly one `κ`-point and does not use quasi-compactness or the base over `Z`) |
| Lem 4.6 | `FamilyLangWeilCurveStatement`, `FamilyLangWeilSlicingStatement` (`LangWeil/`) | implications: Schmidt's bound and the upper bound give dimension 1; Bertini, the upper bound and dimension `d + 1` give dimension `d + 2` | curve proved (`familyLangWeilCurve`, module `LangWeil/FamilyLangWeilCurveProof`: it applies `familyLangWeilCurve_of_planeComparison` (module `LangWeil/FamilyLangWeilCurvePlaneReduction`) to the proved plane-model comparison of the row below); slicing proved (`familyLangWeilSlicing`, module `LangWeil/FamilyLangWeilSlicingProof`, with the helper modules `LangWeil/Slicing/Bridges`, `Core`, `Counting`, `Dimension`, `GenericImage`, `GenericSlice`, `Hyperplane` and `Reduction`, declarations prefixed `Slicing.`); the premises `BertiniGenericHyperplaneStatement` and `FamilyPointUpperBoundStatement` are proved (rows above), and the curve implication also assumes Schmidt's bound |
| Lem 4.6 | `FamilyCurvePlaneComparisonStatement` (`LangWeil/`) | assumes `FamilyPointUpperBoundStatement`; `S` quasi-compact and locally of finite type over `Z`; `f : X → S` locally of finite type, quasi-compact, geometrically irreducible, all fibres of pure dimension 1; there is `B > 0` such that for every finite field `κ` with more than `B` elements and every `κ`-point `s` of `S` some `p ∈ κ[X,Y]`, irreducible over an algebraic closure of `κ`, with degrees in `X` and in `Y` in `[1, B]`, has affine zero count within `B` of `#X_s(κ)`; a plane-model comparison derived from Lang–Weil (1954), printed p.819, and Tao, *The Lang–Weil bound*, Section 2 | proved (`familyCurvePlaneComparison`, module `LangWeil/FamilyCurvePlaneComparisonProof`, with the helper modules `LangWeil/FamilyCurvePlaneReduction`, `AffineCurvePlaneComparison`, `CurvePlaneCharts`, `CurvePlaneFibrePoints`, `CurvePlaneNoetherianInduction`, `CurvePlanePolynomial`, `CurvePlaneRadicialPoints` and `CurvePlaneZeroDimensional`, declarations prefixed `CurvePlane.`; an input to `FamilyLangWeilCurveStatement`; the proof does not use the premise `FamilyPointUpperBoundStatement`) |
| Lem 4.6 and Thm 5.9 | `UniformLangWeilOfFamilyStatement`, `SpaceUniformLangWeilOfFamilyStatement` (`LangWeil/`) | implications: `FamilyLangWeilStatement` implies `UniformLangWeilStatement`; `FamilyLangWeilStatement` and `FamilyPointUpperBoundStatement` imply `SpaceUniformLangWeilStatement` | first proved (`uniformLangWeilOfFamily`, module `LangWeil/UniformLangWeilOfFamilyProof`); second proved (`spaceUniformLangWeilOfFamily`, module `LangWeil/SpaceUniformLangWeilOfFamilyProof`, with the helper modules `LangWeil/SpaceFamily/Counting`, `DegreePoints`, `FibreCharts`, `FibreProductBase`, `FieldPoints`, `FiniteFieldCharts`, `RingPointCharts`, `SchemeBase`, `SeparatedChart` and `Strata`, declarations prefixed `LangWeil.SpaceFamily.`); their premises are now supplied by the published composition `familyLangWeilOfPlaneCurve planeCurveHasseWeil` and the published `familyPointUpperBound`. Their unconditional exact-target endpoints are also proved by the published `uniformLangWeil` and `spaceUniformLangWeil` at commit `2e46b9ca` |
| Thm 3.4(1) for spaces | `EtaleEquivalenceRelation.LimitModelExistence` (`EtaleEquivalenceRelationLimitModelStatement`) | cofiltered limits of affine schemes; an étale equivalence relation of schemes over the limit with affine object scheme, object structure map locally of finite presentation and quasi-compact relation structure map; conclusion: an étale equivalence relation at one stage, with the same finiteness properties, whose object and relation schemes give the original ones by base change (cartesian comparisons) | proved (`EtaleEquivalenceRelation.limitModelExistence`, modules `EtaleEquivalenceRelationLimitModelProof` and `EtaleEquivalenceRelationLimitModelLevels`) |
| Thm 3.4(1) for spaces | `SpaceLimitModelExistenceQuasiSeparatedReduction.spaceLimitModelExistenceQuasiSeparated_of_relation` (`SpaceLimitModelExistenceQuasiSeparatedReduction`) | the statement above implies `SpaceLimitModelExistenceQuasiSeparated` | proved (reduction) |
| Thm 3.4(2) for spaces | `spaceLimitSeparatedDescent` (`RelativeDiagonalLimitDescent`), `spaceLimitSmoothDescent` (`SmoothChartLimitDescent`) | the separated and the smooth conjuncts `SpaceLimitPropertyDescends` of `SpaceLimitPropertyDescentStatement`, with its full hypotheses: cofiltered limits of affine schemes; source and target quasi-separated with an `LocallyOfFinitePresentation ⊓ QuasiCompact` atlas | proved |
| Thm 3.4(2) for spaces | `RepresentedMorphismAtlas.closedImmersion_limit_iff`, `RepresentedMorphismAtlas.affine_limit_iff`, `RepresentedMorphismAtlas.openImmersion_limit_iff`, `RepresentedMorphismAtlas.finite_limit_iff` (`RepresentedChartLimitDescent`) | cofiltered limits of affine schemes; `f : X → Y` over a stage, given with a represented atlas pullback (a proof that `f` is representable, a surjective étale scheme atlas of `Y`, and the scheme pullback of `f` along it), both chart schemes finitely presented over the stage; the base change of `f` to the limit is a closed immersion, affine, an open immersion or finite iff its base change to some stage is | proved (conditional on the represented atlas pullback, which this module does not construct; the general case follows from the `_of_modelUniqueness` row below) |
| Thm 3.4(2) for spaces | `RepresentedAtlasEffectivityStatement` (`EtaleAtlasPropertyEffectivity`) | Stacks Project, *Morphisms of Algebraic Spaces*, Tags 03M4, 03WG and 03ZQ: any base scheme; `f : X → Y` with a cartesian square over a surjective étale scheme atlas `V → Y` whose scheme side is `q : U → V`; if `q` is a closed immersion, affine, an open immersion or finite, then `f` is representable and every scheme base change of `f` has the same property | proved (`representedAtlasEffectivity`, module `RepresentedAtlasEffectivityProof`, with the helper module `RepresentedAtlasEffectivityDescent`, declarations prefixed `AtlasEffectivity.`): representability of `f` from the Library's quotients of étale equivalence relations and open-chart gluing, then descent of each property along the atlas by `AtlasEffectivity.etaleAtlasPropertyEffectivity_of_represented` |
| Thm 3.4(2) for spaces | `spaceLimitClosedImmersionDescent_of_modelUniqueness`, `spaceLimitAffineDescent_of_modelUniqueness`, `spaceLimitOpenImmersionDescent_of_modelUniqueness`, `spaceLimitFiniteDescent_of_modelUniqueness` (`EventualTargetAtlasDescent`) | `SpaceLimitModelUniqueness` (the model-uniqueness half of `SpaceLimitUniquenessStatement`) and the corresponding conjunct `EtaleAtlasPropertyEffectivity` of `RepresentedAtlasEffectivityStatement` as hypotheses; the full hypotheses of `SpaceLimitPropertyDescends`, with no representability of `f` at the original stage: cofiltered limits of affine schemes; source and target quasi-separated with a `LocallyOfFinitePresentation ⊓ QuasiCompact` atlas; conclusions: the closed immersion, affine, open immersion and finite conjuncts of `SpaceLimitPropertyDescentStatement` | proved (reductions; both premises are proved, by `spaceLimitModelUniqueness` and the four components of `representedAtlasEffectivity`; `spaceLimitPropertyDescent` proves the whole statement) |
| Thm 3.4(2) for spaces | `isProperMorphism_iff_separated_universallyClosed`, `isProperMorphism_baseChangeMap_iff_separated_universallyClosed` (`FiniteTypeMorphismAtlas`) | source and target with a `LocallyOfFinitePresentation ⊓ QuasiCompact` atlas, target quasi-separated; over an affine base, and after base change along any map from an affine scheme, `f` is proper iff it is separated and universally closed | proved |
| Thm 3.4(2) for spaces | `spaceLimitGeometricallyConnectedFibresDescent` (`SpaceLimitConnectedFibresDescent`) | the geometrically-connected-fibres conjunct `SpaceLimitPropertyDescends (fun f => HasGeometricallyConnectedFibres f)` of `SpaceLimitPropertyDescentStatement`, with its full hypotheses: cofiltered limits of affine schemes; source and target quasi-separated with a `LocallyOfFinitePresentation ⊓ QuasiCompact` atlas; `HasGeometricallyConnectedFibres` asks for nonempty connected fibres over every field point | proved |
| Thm 3.4(2) for spaces | `ProperSchemeCoverStatement` (`AlgebraicSpace/`) | Stacks Project, Lemma 69.18.1 (Tag 089I, weak Chow lemma), with Lemmas 76.40.3 (Tag 088S) and 76.41.1 (Tag 089L), refined to finite presentation: affine `S`; `X` over `S` quasi-separated with a `LocallyOfFinitePresentation ⊓ QuasiCompact` atlas and proper structure morphism; there are a scheme `U` over `S`, proper and locally of finite presentation over `S`, and a surjective morphism from the space represented by `U` to `X` (not assumed étale); published as an input to the universal-closedness part of the proper conjunct | proved (`properSchemeCover`, module `ProperSchemeCoverProof`: `properSchemeCover_of_chowCover` (module `ProperCoverFPReduction`, with `ProperCoverFPApprox` and `ProperCoverFPComposite`: a Noetherian model of the space, a cover of the model, and its pullback to the original base) applied to `ProperSchemeCover.chowCover`, which proves `ProperSchemeCover.ChowCoverStatement`: a separated space over affine `S` with a `LocallyOfFinitePresentation ⊓ QuasiCompact` atlas receives a surjective morphism, proper after every base change to a scheme, from a scheme locally of finite type and quasi-compact over `S` (modules `ProperSchemeCover/ChowCoverStatement` and `ProperSchemeCover/ChowCoverProof`, with `ProperSchemeCover/AffineEmbedding`, `Closedness`, `CompleteTuples`, `Construction`, `OpenGluing`, `PointAgreement`, `RelativeProper` and `SpacePullback`)); with it the proper conjunct follows, and `spaceLimitPropertyDescent` proves the whole statement (row below) |
| Thm 3.4(2) for spaces | `spaceLimitProperDescent_of_schemeCovers`, `spaceLimitPropertyDescent_of_foundations` (`SpaceLimitProperDescentOfSchemeCovers`) | the first: `ProperSchemeCoverStatement` as a hypothesis, in the same universe; conclusion: the proper conjunct `SpaceLimitPropertyDescends (fun f => IsProperMorphism f)` of `SpaceLimitPropertyDescentStatement`, with its full hypotheses: cofiltered limits of affine schemes; source and target quasi-separated with a `LocallyOfFinitePresentation ⊓ QuasiCompact` atlas; the second: `RepresentedAtlasEffectivityStatement` and `ProperSchemeCoverStatement` as hypotheses, in the same universe; conclusion: `SpaceLimitPropertyDescentStatement`, assembled from the first, the four `_of_modelUniqueness` conjuncts above with `spaceLimitModelUniqueness`, and the three proved conjuncts | proved (conditional on `ProperSchemeCoverStatement`, resp. on it and `RepresentedAtlasEffectivityStatement`; both are proved, by `properSchemeCover` and `representedAtlasEffectivity`, and `spaceLimitPropertyDescent` (module `SpaceLimitPropertyDescentProof`) is `spaceLimitPropertyDescent_of_foundations representedAtlasEffectivity properSchemeCover`; supporting modules in the constructions paragraph below) |
| Thm 3.4(2) for spaces, flat and dimension | `RelativePureFibreDimensionDescentStatement` (`SchemePureFibreDimensionDescent`) | scheme form of the pure-dimension condition alone: every `d`; cofiltered limits of affine schemes mapping compatibly to a fixed scheme `S`; `f : X → Y` over `S` locally of finite presentation, quasi-compact and quasi-separated, `Y` quasi-compact and quasi-separated over `S`; every fibre over the limit has pure dimension `d` iff every fibre over some stage has; no nonemptiness or connectedness of fibres | proved (`relativePureFibreDimensionDescent`) |
| Thm 3.4(2) for spaces, flat and dimension | `spaceLimitFlatnessDescends` (`SpaceLimitFlatnessDescentStatement`, module `SpaceLimitFlatnessDescent`); `spaceLimitPureFibreDimensionDescends` (`SpaceLimitPureFibreDimensionDescentStatement`, module `SpaceLimitPureFibreDimensionDescent`) | the hypotheses of `SpaceLimitPropertyDescends`: cofiltered limits of affine schemes; source and target quasi-separated with a `LocallyOfFinitePresentation ⊓ QuasiCompact` atlas; the first is the flatness conjunct of `SpaceLimitFlatnessDimensionDescentStatement`; the second descends `HasPureFibreDimension d` for every `d`, with no nonemptiness or connectedness of fibres | proved |
| Thm 3.4(2) for spaces, flat and dimension | `etalePureFibreDimensionComparison` (`EtalePureFibreDimensionComparisonStatement`, module `SchemeEtalePureFibreDimension`) | arbitrary schemes and every `d`; local finite type together with pure fibre dimension `d` holds for `p ≫ f` iff it holds for `f` when `p` is étale and surjective, and for `f ≫ g` iff for `f` when `g` is étale | proved |
| Thm 3.4(2) for spaces, flat and dimension | `SpaceLimitFlatnessDimensionReductionStatement`, `spaceLimitFlatnessDimensionReduction` (`SpaceLimitFlatnessDimensionReduction`) | the geometrically-connected-fibres conjunct `SpaceLimitPropertyDescends (fun f => HasGeometricallyConnectedFibres f)` of `SpaceLimitPropertyDescentStatement` (`HasGeometricallyConnectedFibres` asks for nonempty connected fibres over every field point) implies `SpaceLimitFlatnessDimensionDescentStatement`, under its original hypotheses | proved (reduction; its premise is proved by `spaceLimitGeometricallyConnectedFibresDescent`, and `spaceLimitFlatnessDimensionDescent` applies it to that theorem) |
| Lem 5.1 | `SchemeGeometricComponentCountConstructibleStatement` (`SchemeGeometricComponentCountStatement`) | scheme specialization: any commutative ring `B`; a scheme morphism `X → Spec B` locally of finite presentation, quasi-compact and quasi-separated; every `n : ℕ`; the number of connected components of the fibre over an algebraic closure of each residue field, counted in `ℕ∞` | proved (`schemeGeometricComponentCountConstructible`, module `SchemeGeometricComponentCountProof`, with `SchemeGeometricComponentCountBaseChange`) |
| Lem 5.1 | `geometricFibreComponentsConstructibleStatement_iff`, `geometricFibreComponentCount_ne_top` (`GeometricFibreComponentGeometry`) | restatement of `GeometricFibreComponentsConstructibleStatement` through the count `geometricFibreComponentCount`; the count is finite for `X` finitely presented over `B` | proved |
| Lem 5.1 | `exists_open_geometricComponentsEquiv`, `exists_open_geometricFibreComponentCount` (`GenericGeometricComponents`) | the first: an irreducible Noetherian base scheme `S`; `X` quasi-separated with an étale surjective atlas whose structure morphism is locally of finite type and quasi-compact; there is a nonempty open subset of `S` over which the sets of connected components of the geometric fibres, for the point topology, are pairwise in bijection; the second: the same over `Spec B` for a Noetherian ring `B` with irreducible spectrum, where `geometricFibreComponentCount` is constant on a nonempty open; this is the generic step of the Noetherian induction and does not prove constructibility | proved |
| Prop 5.4, manifold | `canonicalAnalyticPointStructure`, `canonicalAnalyticPointStructure_isAnalytic` (`SmoothSpaceAnalyticAtlas`); `canonicalAnalyticPointStructure_isFunctorial`, `canonicalAnalyticPointStructure_isEtaleLocalIso` (`AnalyticPointFunctoriality`); `canonicalAnalyticPointStructure_agreesWithAffineSpace`, `canonicalAnalyticPointStructure_isAdmissible` (`AnalyticAffineNormalization`) | every complete nontrivially normed `K`; the family of charted spaces on `X(K)`, with the étale-chart topology, built from affine étale charts smooth of relative dimension `n`; it satisfies `AnalyticPointStructure.IsAnalytic`, `AnalyticPointStructure.IsFunctorial`, `AnalyticPointStructure.IsEtaleLocalIso` and `AnalyticPointStructure.AgreesWithAffineSpace`, hence `AnalyticPointStructure.IsAdmissible`; this proves the existence conjunct of `AnalyticPointManifoldStatement`; the uniqueness clause is `AnalyticPointStructure.equivalent_of_isAdmissible` (`AnalyticPointUniqueness`), and `analyticPointManifold` combines the two | proved for the pure-dimensional family; actual algebraic dimension pieces and the field-section equivalence are published. The rational-point homeomorphism statement, the lifted atlas and the varying-dimension statements are published (section checked at `b3dcc8cc`); their proofs were open at that commit. Section checked at `18790533`: every one of these statements except `SmoothSourceAnalyticManifoldStatement` is now proved. section checked at `8aede86c`: `SmoothSourceAnalyticManifoldStatement` is proved too (`smoothSourceAnalyticManifold`) |
| Ex 5.5 | `StabilizerFibreLocalDimensionStatement` | any scheme `S`; a group scheme `G` locally of finite type over `S` acting on `V`; at every point of the stabilizer scheme (the base change of the action graph along the diagonal of `V`), the local dimension of its fibre over `V` equals the dimension of the whole fibre, so stabilizer fibres are equidimensional; input to the local closedness of the orbit-dimension strata | proved (`stabilizerFibreLocalDimension`, module `StabilizerFibreLocalDimensionProof`, helpers prefixed `StabilizerFibre.`) |
| Ex 5.5 | `OrbitStratumActionRestrictionStatement` | any field `k`; `G` smooth over `k`; `V` locally of finite type with a `G`-action; a reduced scheme `Z` with an immersion onto the points of orbit dimension `d`; the action restricts to `Z`, and every restricted action has orbit dimension `d` at every point | proved (`orbitStratumActionRestriction`, module `OrbitStratumActionRestrictionProof`, helpers prefixed `OrbitStratumActionRestriction.`) |
| Ex 5.5 | `UnipotentOrbitStabilizerSmoothStatement` | field `k` of characteristic zero; `G` affine, locally of finite type and unipotent; `Z` reduced, locally of finite type, with a `G`-action of constant orbit dimension `d`; the stabilizer scheme is smooth over `Z`, which is stronger than the flatness in the source (route through Cartier's theorem instead of Conrad's `exp(ker B)`) | proved (`unipotentOrbitStabilizerSmooth`, module `UnipotentOrbitStabilizerSmoothProof`) at commit `2e46b9ca`. The exact target is obtained from the published reduction, `Langlands.GroupScheme.reducedBaseConnectedFibreSmooth` and `Langlands.GroupScheme.charZeroUnipotentConnected`, with every hypothesis in this row retained |
| Ex 5.5 | `Langlands.GroupScheme.ReducedBaseConnectedFibreSmoothStatement` (module `Langlands/GroupScheme/ReducedBaseSmoothStatement`) | SGA 3, Exposé VI_B, Corollaire 4.4, over a reduced base with connected fibres: `S` reduced and locally Noetherian; a group scheme `H` over `S`, locally of finite type, whose fibres over the residue fields are smooth and connected, with fibre dimension locally constant on `S`; then `H → S` is smooth | proved (`Langlands.GroupScheme.reducedBaseConnectedFibreSmooth`, module `Langlands/GroupScheme/ReducedBaseSmoothProof`, with `ReducedBaseSmooth/` helpers, at commit `9b849cab`). The proof retains every hypothesis in this row |
| Ex 5.5 | `Langlands.GroupScheme.CharZeroUnipotentConnectedStatement` (module `Langlands/GroupScheme/Unipotent/CharZeroConnectedStatement`) | Milne, *Algebraic Groups* (2022), Corollary 14.15, in characteristic zero: an affine group scheme locally of finite type over a field of characteristic zero that is unipotent (every nonzero finite-dimensional representation has a nonzero fixed vector) has connected underlying space | proved by the proof-producing `def` `Langlands.GroupScheme.charZeroUnipotentConnected` (module `Langlands/GroupScheme/Unipotent/CharZeroConnectedProof`, with `CharZeroCoordinateConnected`, `CharZeroIdempotents` and `CharZeroPeriodic` in the same folder), whose type is the statement unfolded; a supporting definition, by a route through Cartier's theorem and idempotents of the coordinate ring rather than Milne's component-group argument |
| Ex 5.5 | `unipotentOrbitStabilizerSmooth_of_reducedBase_of_charZeroConnected` (`UnipotentOrbitStabilizerSmoothReduction`) | the two statements above as hypotheses, in the same universe; conclusion: `UnipotentOrbitStabilizerSmoothStatement` | proved by this proof-producing `def` (a supporting definition); both premises have published proofs, namely `Langlands.GroupScheme.reducedBaseConnectedFibreSmooth` and `Langlands.GroupScheme.charZeroUnipotentConnected`. Their composition now gives the published exact-target theorem `unipotentOrbitStabilizerSmooth` named above |
| Ex 5.5 | `SmoothStabilizerActionQuotientStatement` | any scheme `S`; `G` smooth over `S`; `V` locally of finite type with a `G`-action whose stabilizer scheme is smooth over `V`; an fppf quotient algebraic space exists, and every fppf quotient map is smooth and surjective, with quotient locally of finite type over `S` | proved (`smoothStabilizerActionQuotient`, module `SmoothStabilizerActionQuotientProof`, with `SmoothStabilizerActionArrows`, `SmoothStabilizerActionOrbitRelation` and `SmoothStabilizerActionQuotientAssembly`, helpers prefixed `SmoothStabilizerActionQuotient.`) |
| Ex 5.5 | `ActionQuotientFinitenessStatement` | any field `k`; `G` quasi-compact over `k`; `Z` of finite type over `k` with a `G`-action; an fppf quotient `X`, locally of finite type, with smooth surjective quotient map; `X` is quasi-separated and finitely presented over `k` | proved (`actionQuotientFiniteness`, module `ActionQuotientFinitenessProof`, with `ActionQuotientOrbitRelation`, helpers prefixed `ActionQuotientFiniteness.` and `ActionQuotientOrbitRelation.`) |
| Ex 5.5 | `LocallySeparatedRationalPointsStatement` | henselian nontrivially normed `K`; `X` quasi-separated, locally separated and locally of finite type over `K`; `X(K)` is locally Hausdorff, locally compact if `K` is, and locally totally disconnected if the norm is ultrametric: the corrected topology clause, for every such space rather than only orbit quotients | proved (`locallySeparatedRationalPoints`, module `LocallySeparatedRationalPointsProof`) |
| Cor 5.6 | `SpaceValuativeExistenceStatement` | Stacks Project, *Morphisms of Algebraic Spaces*, Lemma 67.42.3 (Tag 0A3Y), (1) ⇒ (3): any base scheme `S`; `f : X → Y` quasi-compact, separated and universally closed; for every valuation ring `A` with fraction field `K` and every `Spec A → S`, a section of `X` over `Spec K` and a section of `Y` over `Spec A` with the same image in `Y` over `Spec K` come from a section of `X` over `Spec A`, without extending `K` | proved (`spaceValuativeExistence`, module `SpaceValuativeExistenceProof`, with `ValuativeExistenceAlgebra`, `ValuativeExistenceTests` and `ValuativeExistenceCore` (declarations prefixed `ValuativeExistence.`); a direct route through an étale chart and fppf descent along a faithfully flat finitely presented `A`-algebra, which uses neither the two rows below nor quasi-compactness) |
| Cor 5.6 | `SpaceValuativeExtensionExistenceStatement`, with the predicate `HasDominatingValuativeLift` (module `DominatingValuativeLift`) | Stacks Project, *Morphisms of Algebraic Spaces*, Lemma 67.42.2(1) (Tag 0A3X) for separated morphisms, with the extension diagram of Definition 67.41.1 (Tag 03IX): any base scheme `S`; `f : X → Y` quasi-compact, separated and universally closed; for every valuation ring `A` with fraction field `K`, every `Spec A → S`, a section `x` of `X` over `Spec K` and a section `y` of `Y` over `Spec A` with the same image in `Y` over `Spec K`, there are a valuation ring `B` with fraction field `L`, a local homomorphism `A → B` and a compatible `K → L`, and a section of `X` over `Spec B` that restricts to `x` over `Spec L` and maps to the restriction of `y` | proved (`spaceValuativeExtensionExistence`, module `SpaceValuativeExtensionExistenceProof`); Cor 5.6 no longer depends on it |
| Cor 5.6 | `SpaceValuativeExtensionDescentStatement` | Stacks Project, *Morphisms of Algebraic Spaces*, Lemma 67.41.4 (Tag 0ARH) for separated morphisms: any base scheme `S`; `f : X → Y` separated; for `A`, `K`, `x`, `y` as in the row above with a lift after a dominating extension (`HasDominatingValuativeLift`), there is a section `a` of `X` over `Spec A` with restriction `x` over `Spec K` and image `y`. With the row above it gives `SpaceValuativeExistenceStatement` (the Stacks route); no Library theorem combines them, and the Library proof of that statement takes another route | proved (`spaceValuativeExtensionDescent`, module `SpaceValuativeExtensionDescentProof`); Cor 5.6 no longer depends on it |
| Cor 5.6 | `LocalFieldProperPointValuativeReductionStatement` | the implication from `SpaceValuativeExistenceStatement` to `LocalFieldProperPointMapStatement`, both in the same universe; the reduction step of the valuative route | proved (`localFieldProperPointValuativeReduction`, module `LocalFieldProperPointValuativeReductionProof`): it is `LocalFieldProperPointLimit.localFieldProperPointMap_of_valuative` (module `LocalFieldProperPointLimit`; helpers in the constructions paragraph below) |
| Cor 5.7 | `HenselianChartIntegralPointsClosedStatement` | nontrivially normed `K` whose closed unit ball `O` is a henselian local ring; `X` separated, locally of finite type over `O`; for an étale map `U → X` from an affine scheme over `O`, the image of `U(O)` in `X_K(K)` is closed for `etaleChartTopology` | proved (`henselianChartIntegralPointsClosed`, module `HenselianChartIntegralPointsClosedProof`, helpers in `Langlands.AlgebraicGeometry.PointTopology.HenselianUnitBall`) |
| Cor 5.7 | `UniformFieldPointChartsStatement` | any commutative ring `C`; `X` separated and quasi-compact over `C`; finitely many étale maps from affine schemes to `X` through which every `k`-point of `X` lifts, for every field `k` over `C`; derived from the proofs of Stacks, Tags 0BBN and 07S9 | proved (`uniformFieldPointCharts`, module `UniformFieldPointChartsProof`, helpers prefixed `UniformFieldPointCharts.`) |
| Prop 5.8 | `AdelicSpaceProperStagesStatement` (`CurvePlaceSpaceProperStagesStatement`, `NumberFieldSpaceProperStagesStatement`; module `AdelicSpaceProperInputsStatement`) | separated finite-type spaces over the `S`-integers and a proper morphism `g`; curves need finite `k` and nonempty `S`; number fields allow every finite set of finite places; for every finite level `T` above `S`: `g` is proper on `T`-level points for the stage topologies, and the preimage of the target's `T`-stage range is the source's `T`-stage range | proved (`adelicSpaceProperStages`, module `Langlands/Global/AdelicSpaceProperStagesProof`): it applies `adelicSpaceProperStages_of_inputs` (row below) to `localFieldProperPointMap`, `spaceValuativeExistence` and `IsProperMorphism.baseChangeMap` |
| Prop 5.8 | `AdelicSpaceProperModelStatement` (curve and number-field forms; same module); the conjunction `AdelicSpaceProperInputsStatement` | the data of `AdelicSpaceSpreadProperMapStatement`: separated finite-type models over independent finite sets (nonempty, and finite `k`, for curves) of spaces `Y`, `W` and a proper morphism `g : Y → W`; conclusion: a finite set `T` (nonempty for curves), separated finite-type models over the `T`-integers and a proper model morphism compatible with `g` through generic-fibre isomorphisms | proved (`adelicSpaceProperModel`, module `Langlands/Global/AdelicSpaceProperModelProof`: `AdelicSpaceProperModelReduction.adelicSpaceProperModel_of_descent spaceLimitMorphismDescent (spaceLimitPropertyDescent).2.2.1`); the conjunction has no theorem of its own type, and both of its conjuncts are proved (`adelicSpaceProperStages`, `adelicSpaceProperModel`) |
| Prop 5.8 | `AdelicSpaceProperModelReduction.adelicSpaceProperModel_of_descent` (`AdelicSpaceProperModelReduction`) | `SpaceLimitMorphismDescent` (Thm 3.4(1) for spaces) and `SpaceLimitPropertyDescends (fun f => IsProperMorphism f)` (the properness conjunct of `SpaceLimitPropertyDescentStatement`) as hypotheses, in the same universe; conclusion: `AdelicSpaceProperModelStatement`, both forms, with all its hypotheses | proved (conditional on the two descent inputs, both of which are proved: `SpaceLimitMorphismDescent` by `spaceLimitMorphismDescent`, and the properness conjunct by `(spaceLimitPropertyDescent).2.2.1`; `adelicSpaceProperModel` applies the reduction to these two terms) |
| Prop 5.8 | `ProperSchemeBaseChangeStatement` (`AlgebraicSpace/`) | Stacks Project, *Morphisms of Algebraic Spaces*, Lemma 40.3 (Tag 04WP), for a change of base scheme: arbitrary schemes `S`, `T` and `g : T → S`; algebraic spaces `X`, `Y` over `S`; for `f : X → Y` proper, `baseChangeMap g f` is proper | proved (`properSchemeBaseChange`, module `ProperSchemeBaseChangeProof`): it is the Library theorem `IsProperMorphism.baseChangeMap` (module `TopologicalMorphismBaseChange`), which holds for every `g` and every proper `f`, without representability |
| Prop 5.8 | `curvePlaceSpaceStage_isProperMap_of_proper`, `numberFieldSpaceStage_isProperMap_of_proper`, with level and factor forms and the bundled maps `curvePlaceSpaceStageProperMap`, `numberFieldSpaceStageProperMap` (`AdelicSpaceStageProperReduction`) | `LocalFieldProperPointMapStatement` (Cor 5.6) and `ProperSchemeBaseChangeStatement` as hypotheses; `X`, `Y` separated and of finite type over the `S`-integers, `f : X → Y` proper; curves need finite `k` and nonempty `S`; number fields allow every finite set of finite places; for every finite level `T` above `S`, `f` is proper on `T`-stage points for the stage topologies: the properness half of `AdelicSpaceProperStagesStatement` | proved (conditional on the two inputs, both proved: `localFieldProperPointMap` and `properSchemeBaseChange`) |
| Prop 5.8 | `curvePlaceSpaceStagePreimage_of_valuative`, `numberFieldSpaceStagePreimage_of_valuative` (`AdelicSpaceStagePreimageReduction`) | `SpaceValuativeExistenceStatement` as a hypothesis; `X` separated and of finite type over the `S`-integers, `Y` any algebraic space over them, `f : X → Y` whose base change to the `T`-integers is proper (a hypothesis); curves need finite `k` and nonempty `S`; number fields allow every finite set of finite places; in the adelic points of `X`, the preimage under `f` of the `T`-stage range of `Y` is the `T`-stage range of `X`: the preimage half of `AdelicSpaceProperStagesStatement` at the level `T` | proved (conditional on the valuative criterion, which `spaceValuativeExistence` proves, and on properness after base change) |
| Prop 5.8 | `curvePlaceSpaceFullLevelPreimage_of_valuative`, `numberFieldSpaceFullLevelPreimage_of_valuative` (`AdelicSpaceFullPreimageReduction`) | `SpaceValuativeExistenceStatement` as a hypothesis; `X` separated and of finite type over the `S`-integers, `Y` any algebraic space over them, `f : X → Y` proper; curves need finite `k` and nonempty `S`; number fields allow every finite set of finite places; in the adelic points of `X`, the preimage under `f` of the image of the `S`-level points of `Y` is the image of the `S`-level points of `X`. This is the preimage clause of `AdelicSpaceProperStagesStatement` with the level ring at `S` (`curvePlaceAdeleLevel`, `numberFieldAdeleLevel`) in place of the stage rings at the levels `T`; properness on level points is not derived | proved (conditional on the valuative criterion, which `spaceValuativeExistence` proves; no Library theorem combines the two) |
| Prop 5.8 | `AdelicSpaceProperStagesReductionStatement`, `adelicSpaceProperStagesReduction`, with the components `adelicSpaceProperStages_of_inputs`, `curvePlaceSpaceProperStages_of_inputs`, `numberFieldSpaceProperStages_of_inputs` (`AdelicSpaceProperStagesReduction`) | `LocalFieldProperPointMapStatement` (Cor 5.6), `SpaceValuativeExistenceStatement` and `ProperSchemeBaseChangeStatement` as hypotheses, all in the same universe; conclusion: `AdelicSpaceProperStagesStatement` in both characteristics, with all its hypotheses; the proof pairs the two stage rows above, obtaining properness of the base-changed model morphism from `ProperSchemeBaseChangeStatement` | proved (conditional on the three inputs, all proved: `localFieldProperPointMap`, `spaceValuativeExistence` and `properSchemeBaseChange`; `adelicSpaceProperStages` applies `adelicSpaceProperStages_of_inputs` to the first two and to `IsProperMorphism.baseChangeMap`) |
| Prop 5.8 | `adelicSpaceSpreadProperMap_of_inputs`, `adelicSpaceSpreadProperMap_of_arithmeticInputs`, `adelicSpaceSpreadProperMap_of_properModel`, `adelicSpaceSpreadProperMap` (`Langlands/Global/AdelicSpaceSpreadProperMapProof`) | successive implications from the topology and proper-input packages, from the proper-stage and proper-model packages, and from the proper-model package alone to `AdelicSpaceSpreadProperMapStatement.{u}`; the last theorem has no extra premise. The conclusion keeps arbitrary independent separated finite-type models, finite constants and nonempty inverted-place sets for function fields, and all infinite factors and possibly empty finite-place sets for number fields | proved at the 13 November audit commit. Proper stage maps with exact stage inverse images give closedness and compact fibres for the full map; model replacement and topology independence transport this to the two original models. The final theorem discharges every input by the published proofs |
| Thm 5.9 | `CompleteFieldSmoothSpacePointOpenStatement` (`CompleteFieldSmoothPointOpenStatement` in `AlgebraicSpace/`) | complete nontrivially normed `K` of any characteristic, archimedean or not; `f : X → Y` smooth (`IsSmoothMorphism`, defined by étale chart squares) between separated algebraic spaces locally of finite type over `K`; `f` is open on `K`-points for `etaleChartTopology` | proved (`completeFieldSmoothSpacePointOpen`, module `CompleteFieldSmoothPointOpenProof`) |
| Thm 5.9 | `curvePlaceSpaceLevel_isOpenMap_of_smooth`, `curvePlaceSpaceStage_isOpenMap_of_smooth`, `numberFieldSpaceLevel_isOpenMap_of_smooth`, `numberFieldSpaceStage_isOpenMap_of_smooth`, with factor forms (`AdelicSpaceSmoothLocalOpenReduction`) | `CompleteFieldSmoothSpacePointOpenStatement` as a hypothesis; separated finite-type models over the `S`-integers and a smooth model map `f`, with surjective point maps at all but finitely many factors; curves need finite `k` and nonempty `S`; `f` is open on level points and on the points of every larger stage | proved (conditional on the local input, which the row above proves, and the cofinite surjectivity) |
| Thm 5.9 | `curvePlaceSpaceFactor_eventually_surjective_of_residue_bound`, `numberFieldSpaceFactor_eventually_surjective_of_residue_bound` (`AdelicSpaceResidueComponentSurjectivity`) | algebraic spaces `X`, `Y` over the `S`-integers and `f : X → Y` smooth (`IsSmoothMorphism`); curves need finite `k`; a natural number `d` and a constant `c ≥ 0` with `\|#f⁻¹(x)(κ_v) − q_v^d\| ≤ c·q_v^(d−1/2)` for every place `v ∉ S` (finite places for number fields), where `κ_v` is the residue field with `q_v` elements, and every `κ_v`-point `x` of `Y`; `f` is surjective on points at all but finitely many factors of the level ring, which is the cofinite surjectivity hypothesis of the row above | proved (conditional on the residue estimate) |
| Thm 5.9 | `curvePlaceSpaceFactor_eventually_surjective_of_uniformLangWeil`, `numberFieldSpaceFactor_eventually_surjective_of_uniformLangWeil`, `curvePlaceSpaceLevel_isOpenMap_of_uniformLangWeil`, `numberFieldSpaceLevel_isOpenMap_of_uniformLangWeil`, with the point lifts `curvePlaceSpacePointLifts_of_uniformLangWeil`, `numberFieldSpacePointLifts_of_uniformLangWeil` (`Langlands/Global/AdelicSpaceUniformModelOpen`) | `SpaceUniformLangWeilStatement` as a hypothesis; the `S`-integers an algebra over `ULift ℤ` with `Spec` map locally of finite type; `Y` quasi-separated (separated for the open-map forms) and of finite type over the `S`-integers, `X` separated and of finite type for the open-map forms; `f : X → Y` separated, quasi-compact, surjective, with geometrically connected fibres, and an étale chart square (`EtaleMorphismChart`) with surjective source chart whose scheme map is smooth of relative dimension `d`; curves need finite `k`, and nonempty `S` for the open-map form; conclusions: `f` is surjective on points at all but finitely many factors of the level ring, and open on level points | proved (conditional on `SpaceUniformLangWeilStatement`) |
| Thm 5.9 | `curvePlaceCofinalSpaceLevel_isOpenMap_of_uniformLangWeil`, `numberFieldCofinalSpaceLevel_isOpenMap_of_uniformLangWeil`, with the point lifts `curvePlaceCofinalSpacePointLifts_of_uniformLangWeil`, `numberFieldCofinalSpacePointLifts_of_uniformLangWeil` (`Langlands/Global/AdelicSpaceCofinalModelOpen`) | the row above at the level `curvePlacePrincipalLevelAbove k F S`, resp. `numberFieldPrincipalLevelAbove K S` (a finite set of places containing the given `S`), with the integer-base premise discharged by `AdelicSpaceIntegerBase`; models given over that level; `SpaceUniformLangWeilStatement` and the other hypotheses of the row above; curves need finite `k`, and nonempty `S` for the open-map form; conclusions: lifts of points at all but finitely many factors of the level ring, and openness on level points | proved (conditional on `SpaceUniformLangWeilStatement`) |
| Thm 5.9 | `SmoothDimensionUniformLifts.exists_uniform_field_surjectivity`, `SmoothDimensionUniformLifts.exists_uniform_henselian_surjectivity`, with the point lifts `SmoothDimensionUniformLifts.pointLifts` (`AlgebraicSpace/SmoothDimensionUniformLifts`) | `SpaceUniformLangWeilStatement` as a hypothesis; a Noetherian ring `C`, an algebra over `ULift ℤ` with `Spec` map locally of finite type; `X`, `Y` separated algebraic spaces of finite type over `C` (`FiniteTypeOverRing`); `f : X → Y` smooth (`IsSmoothMorphism`) with geometrically connected, hence nonempty, fibres (`HasGeometricallyConnectedFibres`); no fixed relative dimension and no étale chart are assumed; conclusions: one constant `c > 0` such that `f` is surjective on `κ`-points for every finite field `κ` with a `C`-algebra structure and `c² < #κ`, and surjective on `R`-points for every henselian local `C`-algebra `R` with a surjective `C`-algebra map onto such a `κ`; `pointLifts` chooses the lifts | proved (conditional on `SpaceUniformLangWeilStatement`) |
| Thm 5.9 | `curvePlaceSmoothConnectedFactor_eventually_surjective`, `numberFieldSmoothConnectedFactor_eventually_surjective`, `curvePlaceSmoothConnectedLevel_isOpenMap`, `numberFieldSmoothConnectedLevel_isOpenMap`, with the point lifts `curvePlaceSmoothConnectedPointLifts`, `numberFieldSmoothConnectedPointLifts` (`Langlands/Global/AdelicSpaceSmoothConnectedModelOpen`) | `SpaceUniformLangWeilStatement` as a hypothesis; the `S`-integers an algebra over `ULift ℤ` with `Spec` map locally of finite type; `X`, `Y` separated algebraic spaces of finite type over the `S`-integers (`FiniteTypeOverRing`); `f : X → Y` smooth (`IsSmoothMorphism`) with geometrically connected, hence nonempty, fibres (`HasGeometricallyConnectedFibres`); no fixed relative dimension, étale chart or surjectivity is assumed; curves need finite `k`, and nonempty `S` for the open-map form; conclusions: `f` is surjective on points at all but finitely many factors of the level ring, and open on level points | proved (conditional on `SpaceUniformLangWeilStatement`) |
| Thm 5.9 | `curvePlaceSmoothConnectedAdele_isOpenMap`, `numberFieldSmoothConnectedAdele_isOpenMap`, with `curvePlaceSmoothConnectedPrincipalStage_isOpenMap`, `numberFieldSmoothConnectedPrincipalStage_isOpenMap`, `curvePlaceSpacePrincipalStage_cover`, `numberFieldSpacePrincipalStage_cover` and the topological lemma `AdelicSpaceOpenReduction.isOpenMap_of_continuous_cover` (`Langlands/Global/AdelicSpaceSmoothConnectedAdelicOpen`) | `SpaceUniformLangWeilStatement` as a hypothesis; `X`, `Y` separated algebraic spaces of finite type over the `S`-integers; `f : X → Y` smooth with geometrically connected fibres, of any relative dimension; no integer-base premise on the `S`-integers; curves need finite `k` and nonempty `S`; number fields allow every finite set of finite places; conclusion: `f` is open on the adelic points of the models (`curvePlaceSpaceAdelePointTopology`, `numberFieldSpaceAdelePointTopology`, module `AdelicSpacePointTopology`); the proof applies the level-openness row above at the principal stages above each stage, which cover the adelic points | proved (conditional on `SpaceUniformLangWeilStatement`); this is openness for a map of models, not `AdelicSpaceSpreadSmoothOpenStatement` |
| Thm 5.9 | `AdelicSpaceSpreadSmoothOpenOfLangWeilStatement`, `adelicSpaceSpreadSmoothOpen_of_langWeil` (`Langlands/Global/AdelicSpaceSmoothConnectedSpreadOpen`) | exactly `SpaceUniformLangWeilStatement.{u} → AdelicSpaceSpreadSmoothOpenStatement.{u}`; independent separated finite-type source and target models and their original spread topologies, possibly at different levels; no fixed relative dimension; both global-field characteristics, with finite constants and nonempty levels for function fields and every infinite factor for number fields | proved at the earlier 13 November audit commit, conditional only on the exact space Lang–Weil statement. Smooth connected model descent, model adelic openness, natural spread homeomorphisms and topology independence supply the arbitrary-model assembly. The published `adelicSpaceSpreadSmoothOpen` now supplies this premise and proves unconditional Theorem 5.9 at commit `2e46b9ca` |
| Lem 5.10 | `WeilRestrictionDiagonalStatement` (`WeilRestrictionGeometricInputsStatement`) | `R → R'` finite projective over arbitrary rings; `X'` quasi-separated, no finite type; the presheaf diagonal of the restricted sheaf is representable with quasi-compact represented projections, and a representable closed immersion if `X'` is separated | proved (`weilRestrictionDiagonal_proof`, module `WeilRestrictionDiagonalProof`) |
| Lem 5.10 | `WeilRestrictionAffineEtaleAtlasStatement` (same module) | as above; an étale surjective map to `X'` from an affine scheme locally of finite type over `R'`; its restriction is étale and geometrically surjective as a map of presheaves over `R` | proved (`weilRestrictionAffineEtaleAtlas`, module `WeilRestrictionAffineEtaleAtlasProof`, from `WeilRestrictionAtlasReduction` and `WeilRestrictionAtlasLocalRepresentation` (declarations prefixed `WeilRestrictionAtlas.`), `TestFibreRepresentation` (prefix `TestFibre.`), `PointTopology/AffineChartWeilRestrictionEtale` and `PointTopology/AffineChartWeilRestrictionSurjective`) |
| Lem 5.10 | `spaceWeilRestriction_of_geometricInputs` (`SpaceWeilRestrictionReduction`) | the two statements above imply `SpaceWeilRestrictionStatement` | proved (reduction) |
| Lem 5.10, scheme cases | `affineWeilRestriction_isAlgebraicSpace`, `affineWeilRestriction_finiteType` (`SchemeWeilRestrictionComparison`); `quasiAffineWeilRestriction_isAlgebraicSpace`, `quasiAffineWeilRestriction_finiteType`, `quasiAffineWeilRestriction_isSeparated`, `quasiAffineWeilRestriction_isQuasiSeparated` (`QuasiAffineWeilRestrictionComparison`) | `R → R'` finite projective; an affine, resp. quasi-affine, scheme locally of finite type over `R'`: its Weil restriction sheaf is an algebraic space of finite type over `R`; in the quasi-affine case also separated and quasi-separated | proved |
| Prop 5.11(1), corrected | `isHomeomorph_ringWeilRestrictionBasePointsEquiv`, `ringWeilRestrictionPointHomeomorph` (`WeilRestrictionPointComparison`) | henselian nontrivially normed `K`, `K'`, `K'` a finite-dimensional `K`-algebra with continuous scalar multiplication (`ContinuousSMul K K'`; no norm compatibility) and `IsModuleTopology K K'`; `Y'` quasi-separated, locally of finite type; given that the Weil restriction sheaf is an algebraic space that is quasi-separated and locally of finite type over `K`, the canonical point bijection is a homeomorphism for the étale-chart topologies | proved (conditional on the given representability and finiteness, which Lemma 5.10 supplies for `Y'` of finite type in the proof of the corrected Prop 5.11(1)) |
| Prop 5.11(3) | `isEmbedding_henselianExtensionPointMap`, `henselianExtensionPointHomeomorphRange` (`HenselianNormedExtensionEmbedding`) | henselian nontrivially normed `K` and `L`, `L` a normed `K`-algebra of any degree and transcendence degree; `X` separated, quasi-separated and locally of finite type; `X(K) → X_L(L)` is an embedding for the étale-chart topologies | proved |
| Prop 5.11(3) | `ExtensionLocalReduction.isEmbedding_of_covered`, `ExtensionLocalReduction.isClosed_range_of_separated_open`, `ExtensionLocalReduction.coveredHenselianExtensionPointHomeomorphRange` (`HenselianExtensionLocalReduction`) | the hypotheses of `HenselianExtensionPointEmbeddingStatement`; the first is its embedding conjunct; the second shows that the image of `X(K)` is closed if the image is closed for every separated open subspace | proved (the embedding conjunct, and a reduction of the closedness conjunct) |
| Prop 5.11(3) | `ExtensionClosedRange.isClosedEmbedding_of_finite_galois`, `ExtensionClosedRange.isClosed_range_of_finite_galois` (`FiniteGaloisExtensionPointTopology`) | henselian nontrivially normed `K` and `L`, `L` a normed `K`-algebra, finite-dimensional and Galois over `K`; `X` separated, quasi-separated and locally of finite type; `X(K) → X_L(L)` is a closed embedding for the étale-chart topologies | proved (closed embedding for separated `X` and finite Galois `L/K`) |
| Prop 5.11(3) | `CompleteExtensionPointClosedRangeStatement` | complete nontrivially normed `K` and `L`, `L` a normed `K`-algebra of any degree and transcendence degree; `X` quasi-separated, locally of finite type and separated; the image of `X(K)` in `X_L(L)` is closed for the étale-chart topology | proved (`CompleteExtensionClosedRange.completeExtensionPointClosedRange`, module `CompleteExtensionPointClosedRangeProof`, helpers prefixed `CompleteExtensionClosedRange.`) |
| Prop 5.11(3) | `ExtensionClosedReduction.isClosed_range_of_complete`, `ExtensionClosedReduction.henselianExtensionPointEmbedding_of_complete` (`HenselianExtensionClosedReduction`) | `CompleteExtensionPointClosedRangeStatement` as a hypothesis; the first: any nontrivially normed `K`, a henselian nontrivially normed `L`, `L` a normed `K`-algebra with the image of `K` closed in `L`, `X` quasi-separated, locally of finite type and separated; the image of `X(K)` in `X_L(L)` is closed; the second: `HenselianExtensionPointEmbeddingStatement` with all its hypotheses | proved (conditional on `CompleteExtensionPointClosedRangeStatement`, which is proved; `henselianExtensionPointEmbedding` applies the second to `CompleteExtensionClosedRange.completeExtensionPointClosedRange`) |
| Prop 5.11(3) | `UniformEtaleChartInjectivityStatement` | any nontrivially normed `K`; `X` separated; an étale map to `X` from an affine scheme locally of finite type; finitely many regular functions give uniform injectivity on bounded coordinates over every normed extension `L/K`, of any degree | proved (`uniformEtaleChartInjectivity`, module `UniformEtaleChartInjectivityProof`) |
| Prop 5.11, proof (p.19) | `CompleteFiniteExtensionPointEmbeddingStatement`, `henselianFiniteExtensionPointEmbedding_of_complete` (`FiniteExtensionPointEmbeddingReduction`) | complete `K` and `L`, `L` finite-dimensional over `K`; `X` quasi-separated, locally separated, locally of finite type; the reduction derives the henselian statement from the complete one | reduction proved; the complete statement is open, and the row it served is proved directly |

Published constructions and supporting lemmas without statements of their own also support open
rows: for Theorem 5.9, `AdelicSpaceModelOpenReduction`, `CoordinatePointOpenMap`,
`HenselianSmoothPointLifting`, `UniformLangWeilFiniteFieldLifts`,
`AlgebraicSpace/UniformLangWeilHenselianLifts` and `OriginalBaseUniformLangWeilLifts`
(declarations prefixed `OriginalBaseUniformLangWeilLifts.`; the last three assume
`SpaceUniformLangWeilStatement`), and `BaseCompositionPresheaf`, `BaseCompositionSheaf`,
`BaseCompositionGeometry`, `BaseCompositionProperties`, `BaseCompositionDiagonal`,
`BaseCompositionFibres`, `BaseCompositionPoints` and `BaseCompositionRingPoints` (declarations
prefixed `BaseComposition.`), and `Langlands/Global/AdelicSpaceIntegerBase`
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
relative dimension equal to that value), `SmoothDimensionFieldPoints` (declarations prefixed
`SmoothTargetPointDimensions.`; a field-valued point of the target factors through exactly one
of these open subspaces, and surjectivity on field points of every restricted map gives
surjectivity on field points of the original map), and
`Langlands/Global/AdelicSpaceSmoothModelGeometry` and `Langlands/Global/AdelicSpaceSmoothModelProperties`
(declarations prefixed `AdelicSpaceSmoothModelGeometry.`; smooth models with nonempty
geometrically connected fibres over a ring of integers of a smooth morphism with such fibres over
the global field); for
Proposition 5.8,
`AdelicSpaceCoordinateProperReduction` (declarations prefixed `AdelicSpaceProperReduction.`),
`Langlands/Global/AdelicSpacePreimageAssembly` (namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.AdelicSpacePreimageAssembly`), and
`FibreRestrictionTopology` and `CommonAtlasPointTopology`, on which `TopologicalMorphismBaseChange`
(row of `ProperSchemeBaseChangeStatement`) builds. Their Markdown states what each provides;
none proves an open row.

Further published constructions and supporting lemmas support rows that are now proved. For
Proposition 5.14: `AdelicSpaceWeilRestrictionPoints`,
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
change of base). For Corollary 5.6: `LocalFieldProperPointLimit`
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
For Proposition 5.11(3): `ExtensionPointMap`, `PointTopology/FiniteExtensionCompletion` and
`HenselianExtensionCompletionReduction` (declarations prefixed `ExtensionCompletionReduction.`;
descent of points through the completions when the image of `K` in `L` is closed). For Theorem
3.4(2) for spaces: `ConnectedStructuralFibres` (whose
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
`FamilyPointUpperBoundStatement`:
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

The following passages are commentary, source proof routes or citations of outside results.
Their classification does not remove the retained analytification input in the preceding table.

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
  `j : X → Res_{k'/k}(X_{k'})` for separated `X` in the finite-degree case (the Lean proof
  of the endpoint takes another route: the embedding
  through the separable closure of `K` in `K'` and Galois descent along Galois extensions of any
  degree, and closedness by reduction to complete fields through the completions of `K` and `K'`
  and the separately proved complete case; rows Prop 5.11(3)). The results are proved in
  the Library, by Lean routes that need not follow these steps.
- **Other source proof routes.** Étale cohomology of noetherian algebraic spaces, the
  trace formula and Deligne's Riemann hypothesis for algebraic spaces occur in the source
  route to Theorem 5.9. The published `SpaceUniformLangWeilStatement` proof instead uses
  Lang–Weil estimates in families, and the endpoint is proved. The flatness argument and
  [Del2, Prop. 3.11] occur in the source route to Example 5.5's quotient clause; its published
  proof uses Cartier's theorem and quotients by actions with smooth stabilizers. These
  alternative source proof routes are not unresolved inputs to the published endpoint
  proofs.
- **Retained analytification.** The [CT] construction in the infinite-extension argument
  on p.19 has its own required rows above. The different proof of Proposition 5.11(3)
  establishes that endpoint, while the formalization still requires the actual analytification
  input, the rational-point topology comparison and arbitrary analytic field extension.
- **Cited facts outside the paper's line of argument.** Preservation of quasi-projectivity by
  Weil restriction along finite locally free maps ([CGP, Prop. A.5.8], Example 4.2) and the
  more general Weil restriction of algebraic spaces ([Ols, Thm. 1.5], after Lemma 5.10). The
  paper does not use them; they are not stated. The existence of the Weil restriction of a
  quasi-projective scheme ([BLR], Example 4.2) is a construction in the Library
  (`affineChartWeilRestriction`, row Ex 4.2).

## Remaining obligations

1. Discharged (section checked at `8aede86c`). The source-level
   `SmoothSourceAnalyticManifoldStatement` of Proposition 5.4 is proved by
   `smoothSourceAnalyticManifold`. The other six varying-dimension
   statements were already proved, as recorded in the section checked at `18790533`:
   the rational-point dependent-sum homeomorphism, analytic assembly, functoriality and
   étale local analytic isomorphisms, and affine-space agreement
   and uniqueness. The topological assertion keeps its broader
   henselian/quasi-separated scope, without completeness or local separatedness.
2. The retained analytification pipeline, on the finite-type affine
   constructions of the Library. At commit `24390f9f` eight analytification statements
   needed proofs and twenty-one earlier statements were proved. Six are recorded in the section checked at `18790533`:
   affine rational points, functoriality and
   presentation independence,
   the seminorm description,
   naturality, localized
   functoriality and maps from
   affinoid spectra. Three
   are recorded in the section checked at `8aede86c`: immersions on underlying spaces, the ground-field extension map
 and scheme morphisms. Twelve are recorded in the
   section checked at `24390f9f`: the norm extension to finitely generated domains, chart flatness, quasi-finiteness, the finite-germ comparison, affine fibre products, the center maps, scheme gluing, the analytic structure of the glued
   space, and for algebraic
   spaces rational points,
   `K`-valued points,
   immersions of underlying spaces and the scheme case. The eight open statements are scheme
   rational points, affine
   étale maps, affine analytic
   immersions, and for
   algebraic spaces existence,
   morphisms, étale maps, fibre products and analytic immersions.
   The audit sections above give the commit at which each statement first appeared. At
   Library commit `cf95b60a`, the Library proves scheme rational points
   (`schemeAnalytificationRationalPoints`), affine étaleness (`affineAnalytificationEtale`),
   and the algebraic-space statements for morphisms, étaleness, fibre products and analytic
   immersions (`spaceAnalytificationMorphism`, `spaceAnalytificationEtale`,
   `spaceAnalytificationFibreProduct`, `spaceAnalytificationAnalyticImmersion`). A proof of
   the existence statement counts as
   the construction of the analytification of a separated algebraic space locally
   of finite type. By the morphism statement, `IsAnalytification` determines it up
   to unique compatible isomorphism; no explicit quotient `Uᵃⁿ/Rᵃⁿ` of an étale
   chart is constructed. It remains to construct and state the
   analytic ground-field extension and the canonical isomorphism
   `(Xᵃⁿ)_L ≅ (X_L)ᵃⁿ` for arbitrary complete nonarchimedean extensions, with
   naturality, towers and fibre products. The ground-field extension of presented
   affinoid algebras and affinoid atlases has an algebra-level construction, the preservation of affinoid domains and the
   atlas-level construction with its projection are in the Library
   (scalar-extension row). At commit `24390f9f` its map part, as fixed by the convention
   recorded in the section checked at `24390f9f`, was not: the extension of
   `CompatibleStrongHom` maps between arbitrary presentations, the extension of
   every `StrongHom` with saturated source, and the functor from
   `SaturatedAtlasPresentation K` to the localized category over `L`. Further obligations
   are the descent of that functor through quasi-isomorphisms to the
   localized category over `K`, towers, fibre products, the comparison
   and their statement interfaces, and their proofs. The
   existing extension-point endpoint proof does not discharge them. Of the
   existence statement's seven reduction inputs, two are now discharged
   (`SpaceAnalytificationExistenceFiveInputReduction`); five remain unproved.
3. A whole-paper coverage review, after verifying every retained result and comparison. The
   focused audits of this note do not certify whole-paper completion.

The exact unconditional Theorem 4.5 is proved by
`Langlands.Global.adelicSpreadSmoothOpen`, with the evidence in the
section checked at `f676fad7`.

The published exact scheme and space Lang–Weil estimates, unconditional
Theorem 5.9, all three corrected Example 5.5 clauses, Proposition 5.8 and the
general corrected Corollary 5.7 closedness theorem are proved with the
hypotheses and evidence given above. No extra conjunction theorem
is required for Example 5.5. The literal Proposition 5.11(1),
`HenselianWeilRestrictionPointHomeomorphStatement`, is a known false
statement. Its proved module-topology replacement and the explicit
obstruction meet the corrected scope; proving the false literal statement is not
an obligation.

Unused alternative reductions remain visible in their rows:
`CompleteFiniteExtensionPointEmbeddingStatement`,
`SpaceValuativeExtensionExistenceStatement` and
`SpaceValuativeExtensionDescentStatement`. Their
endpoints are proved by other routes, so no required source conclusion depends
on those alternatives. The Library proves the last two as well
(`spaceValuativeExtensionExistence`, `spaceValuativeExtensionDescent`). This note records no proof of the conjunction `AdelicSpaceProperInputsStatement` itself; its
two inputs are proved. Statuses in this
section supersede the open descriptions in the earlier audit sections, without changing their evidence or the hypotheses of existing rows.

Other Library statements cite this paper only for the topology on rational points, inside
other programs (for example the `Langlands.Representation.Aubert.General` prerequisites); they
are not assertions of the paper and are not listed.

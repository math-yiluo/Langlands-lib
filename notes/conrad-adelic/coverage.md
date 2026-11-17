# Conrad, *Weil and Grothendieck approaches to adelic points*: coverage ledger

Author: Worker 3519 (formerly Worker 16). Parent task `886bf565-95e9-4dc6-8a9d-73284a523668`
(Task 3519), revision 2.

Source: Brian Conrad, *Weil and Grothendieck approaches to adelic points*, December 31, 2011,
21 pages. Registered literature ID `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. Page numbers are the printed
page numbers.

The full baseline audit maps every substantive construction and assertion of Sections 1–5 to
Lean declarations of Library commit `a54dda0d7c7c0fd4f76308fad8525ba13d9b4ce8`. The focused
audits below update selected rows against `ed924aef420de137b4cbaa3b063a3618afcd73fd`,
`17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e`,
`cfedefb680f317b0ea5d351023e1c9dd886b2547`,
`9b849caba7c63ede041b7fec49c90ceaafb08568`,
`7dc9118a3eb340e83e65d6e4174763b7a61e573c` and
`2e5aa9989a9e5567670a14eb7079e3a844641990` and
`2e46b9cac0230529f50cdf96bbe4713c06701fc2`; the revision 2 audit below uses
`aae8cb822941fac72c628376bd39754a1bc40b74`, and the 14 November audit and the two
15 November audits use `f676fad71e1679d672d3e20560dc814d4e1f8ffd`,
`b3dcc8cc4c93f1140c6b34374f589ccc637a1a22` and
`e1fa6f689f9e976eb7574f0dce4453b3b5705ac0`; the 16 November audit uses
`b44618a4f02405d5be8c906f21cf7817e4eaafb9`, and the two 17 November audits use
`f24f97443f21ff7e59b1cf3b509602157dae54c2` and
`18790533e39c3ee1982619a07a6594528ad156dd`. Unchanged rows retain their earlier
audit provenance. For each row the ledger
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

## Proof and prerequisite publications, 17 November 2026 (second audit)

This focused audit checks Library `18790533e39c3ee1982619a07a6594528ad156dd`
under the unchanged revision 2 contract. It records two kinds of publication.
The first is four more independently reviewed statements of parent Task 3519.
The second is twelve published proofs of earlier parent statements, each
submitted under the proof task that the parent published for its statement; the
parent takes no proofs. The Lean and Markdown files of the four statements match
this Library and the workspace byte for byte. Each proof theorem's type is exactly
the published statement proposition with its universe parameters. The commit that
first contains each file was found by scanning the Library manifests. No
candidate below carries a reviewer qualification. All earlier dated sections,
assertion and hypothesis cells, and table order are retained. This section
updates the declaration and status cells of the Prop 5.4 manifold rows and the
analytification rows, and remaining obligations 1 and 2. It does not certify
whole-paper completion.

**New statements.** All four are in `Langlands/Geometry/Analytic/`, namespace
`Langlands.Analytic.AffineAnalytification`, and assume a complete, ultrametric,
nontrivially normed field `K`. None is proved in this Library: each name occurs
only in its own module.

- `FiniteTypeDomainNormExtensionStatement` (candidate
  `f573206b-1571-41be-9bfb-1b55d4f51c5f`, Reviewer 7445, first published at
  `42c696807fd25d6ea96d001a596d7bba7b4b52b9`; proof Task 7628
  `3370013d-0145-4a35-b24b-4cdf01cdbc0d`). Every finitely generated commutative
  `K`-algebra `D` that is a domain has a multiplicative seminorm that extends the
  norm of `K` and vanishes only at `0`. Applied to `A/𝔭`, it gives a seminorm
  on `A` with kernel `𝔭`. This is the algebraic input for surjectivity of the
  center map in `AnalytificationCenterStatement` (Task 7097). Sources: Berkovich
  1990, Theorem 3.4.1(i) with Remark 3.4.2, at the generic point of `Spec D`;
  Conrad p.19, final paragraph of the proof of Proposition 5.11(3).
- `AffineAnalytificationQuasiFiniteStatement` (candidate
  `5669db6e-d26c-4385-b61a-cee2a84d0d3a`, Reviewer 7690; proof Task 7653
  `9fb378cf-c57b-465b-bd06-c422a8ab8500`). For finite polynomial presentations
  `P`, `Q` of `A`, `B` and `f : A →ₐ[K] B`, the ring map `f` is quasi-finite if
  and only if `saturatedHom K P Q f` is quasifinite (finite at every point).
  Source: Berkovich 1993, Corollary 3.1.7.
- `AffineAnalytificationFiniteGermComparisonStatement` (candidate
  `fcb1e6ae-c00f-4f1f-80ec-0af269091da9`, Reviewer 7705; proof Task 7655
  `6f1f9bc0-d74b-4295-81e0-ccba71f22745`). Let `g := saturatedHom K P Q f`, let
  `y` be a point of the `m`-th chart of the analytification of `B`, and let `q`
  be the prime of `B` under `y`. If `g` is finite at `y`, then `g` is unramified
  at `y` if and only if `f` is unramified at `q`, and `g` is flat at `y` if and
  only if the local map `A_{f⁻¹(q)} → B_q` is flat. This is a derived pointwise
  form of Berkovich 1993, Propositions 3.2.10 and 3.3.11.
- `AffineAnalytificationChartFlatStatement` (candidate
  `949a27d0-4bbe-45d1-8820-1083316b804f`, Reviewer 7728; proof Task 7657
  `f5b29461-c4fc-44cd-8212-aacffc08f5e1`). For every chart index `m`, the map
  from `A` to the `m`-th chart algebra of its analytification is flat. Source:
  Berkovich 1990, last paragraph of the proof of Theorem 3.4.1.

The last three were first published at
`fd643ecec6997ef17c8356ddbc924138631307d9`. Worker 554, their coauthor, proposed
them as inputs to the affine étale statement `AffineAnalytificationEtaleStatement`
(Task 7169).

**Proofs of Proposition 5.4 statements.** These are in
`Langlands/AlgebraicGeometry/AlgebraicSpace/`, namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace`. Each theorem proves the statement
whose name it shares.

- `smoothSourceDimensionTopology` (module `SmoothSourceDimensionTopologyProof`,
  candidate `a36f464c-bce5-40c6-8d13-c9bebf4ded56`, Task 6936), first published
  at `371b9c350ae74d42665a9e7e0ec32e4c66f56619`.
- First published at `42c696807fd25d6ea96d001a596d7bba7b4b52b9`:
  `smoothSourceDimensionAnalyticAssembly` (module
  `SmoothSourceDimensionAnalyticAssemblyProof`, candidate
  `18d1e41e-9631-4653-8a3f-261eaf4d609a`, Task 7025),
  `smoothSourceDimensionAnalyticFunctoriality` (module
  `SmoothSourceDimensionAnalyticFunctorialityProof`, candidate
  `422bf2a6-7577-4e63-8636-ecbab0245161`, Task 7026),
  `smoothSourceDimensionEtaleAnalyticIso` (module
  `SmoothSourceDimensionEtaleAnalyticIsoProof`, candidate
  `728c1452-820c-4060-8cde-66516a6eabf3`, Task 7027),
  `smoothSourceDimensionAffineAgreement` (module
  `SmoothSourceDimensionAffineAgreement`, candidate
  `b7c7b73d-efc9-4ee6-9d44-5ac5d9a8132c`, Task 7049) and
  `smoothSourceDimensionAnalyticUniqueness` (module
  `SmoothSourceDimensionAnalyticUniquenessProof` with the support module
  `DimensionPointAtlasCalculus`, candidate
  `f56d5276-03aa-4835-ac5b-12bf3e19f8c1`, Task 7050).

The source-level `SmoothSourceAnalyticManifoldStatement` (Task 7051
`685b8c94-5194-4cb7-8b30-4977774ce694`) is not proved in this Library.

**Proofs of affine analytification statements.** These are in
`Langlands/Geometry/Analytic/`, namespace
`Langlands.Analytic.AffineAnalytification`, all first published at
`42c696807fd25d6ea96d001a596d7bba7b4b52b9`. Each theorem proves the statement
whose name it shares.

- `affineAnalytificationRationalPoints` (module
  `AffineAnalytificationRationalPointsProof` with the support module
  `FieldPointSaturation`, candidate `02b4be2a-f628-45a4-938a-199ac7773e1e`,
  Task 7084);
- `affineAnalytificationFunctoriality` (module
  `AffineAnalytificationFunctorialityProof`, candidate
  `ba6fb5cb-aeff-40e3-8854-f4e3660c01e9`, Task 7085);
- `affineAnalytificationRationalPointNaturality` (module
  `AffineAnalytificationRationalPointNaturalityProof`, candidate
  `c0d6fcfd-1eaa-49d7-a400-413e37202265`, Task 7072);
- `affineAnalytificationSeminorm` (module `AffineAnalytificationSeminormProof`,
  candidate `bc716acc-0702-450c-9afc-f70f9c7f8e32`, Task 7083);
- `affineAnalytificationLocalizedFunctoriality` (module
  `AffineAnalytificationLocalizedFunctorialityProof`, candidate
  `98c2c57d-252d-44db-bef0-63cdd339cd59`, Task 7119);
- `affineAnalytificationAffinoidUniversal` (module
  `AffineAnalytificationAffinoidUniversalProof`, candidate
  `cbd40063-a5e8-4f04-a6da-8c64fc1474d6`, Task 7167).

**Other analytification modules.** The proof tasks have also published
supporting modules, among them `SchemeAnalytificationGluingReduction`,
`SchemeAnalytificationRationalPointsReduction` and
`AnalytificationCenterComparison`. These are conditional reductions that keep
their premises as hypotheses. `SchemeAnalytificationSeparatedStatement` restates
the separatedness clause of `SchemeAnalytificationGluingStatement` as a separate
target. None of them proves a remaining parent statement. Task 7100
`7b5d3807-3a12-4dac-ae8a-a7f93d7fc2b8` has published the ground-field extension
of presented affinoid algebras and a projection interface for quotient chart
systems; the scalar-extension row records them. Its ground-field extension of
affinoid atlases and analytic spaces is not in this Library.

## Analytification `K`-point publication, 17 November 2026

This focused audit checks Library `f24f97443f21ff7e59b1cf3b509602157dae54c2` under the unchanged revision 2
contract. It records one more independently reviewed statement of parent Task
3519. Its Lean and Markdown files match this Library and the workspace byte for
byte, and the candidate carries no reviewer qualification. All earlier dated
sections, assertion and hypothesis cells, and table order are retained. This
section updates the declaration and status cells of the rational-point row
(Conrad p.19; CT Example 2.3.2) and remaining obligation 2. It does not certify
whole-paper completion. Its status supersedes the sentence of the 16 November
audit below saying that no statement identifies the image of `rationalPoint` with
the `K`-points of the analytic space.

- First published at `f24f97443f21ff7e59b1cf3b509602157dae54c2`:
  - `Langlands.Analytic.SpaceAnalytification.SpaceAnalytificationFieldPointsStatement`
    (`Langlands/Geometry/Analytic/SpaceAnalytificationFieldPointsStatement.lean`;
    candidate `1e2ba471-6ab3-4524-bd8c-1dc0dff3baf7`, Reviewer 6234; proof Task 7486
    `74ee4c92-ea0c-4002-aefc-1da4675e9deb`). Let `K` be a complete, ultrametric, nontrivially normed field, `X` a
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

## Analytification publications through 16 November 2026

This focused audit checks Library `b44618a4f02405d5be8c906f21cf7817e4eaafb9`
under the unchanged revision 2 contract. It records twenty more independently
reviewed publications of parent Task 3519, all in the analytification program:
five definitions and fifteen statements. Their forty Lean and Markdown files match
this Library and the workspace byte for byte. The publication record of each
candidate names the commit that first contains it; no candidate carries a reviewer
qualification. All earlier dated sections, assertion and hypothesis cells, and
table order are retained. This section updates the declaration and status cells
of the analytification rows and remaining obligation 2. It does not certify
whole-paper completion. Its statuses supersede the closing paragraph of the first
15 November audit below. That paragraph lists as absent the maps of glued spaces
for scheme morphisms, an analytic structure on the glued space, a universal
property, fibre products, étale maps and the algebraic-space rational-point
comparison. These are now stated, though none is proved.

All units are in `Langlands/Geometry/Analytic/`, with namespaces
`Langlands.Analytic.AffineAnalytification`,
`Langlands.Analytic.SchemeAnalytification`,
`Langlands.Analytic.SpaceAnalytification` and
`Langlands.Analytic.SaturatedAtlasPresentation`. All assume a complete,
ultrametric, nontrivially normed field `K`. The affine units take finite polynomial
presentations of commutative `K`-algebras. The scheme units take schemes locally of
finite type over `Spec K`. In the algebraic-space statements, every space whose
analytification is assumed or asserted is separated and locally of finite type over
`Spec K`, except the target of the morphism statement, which is arbitrary. Test
algebras lie in the universe of `K`. Besides the originals registered above, the
units cite Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), source
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

- First published at `9ed11fc606807fab34c4852a4e88dbabebba69d1` (definitions):
  - `SchemeAnalytificationMorphism` (candidate
    `b2b8db01-be48-46bd-b636-6cdcf2e5eb76`, Reviewer 4514). For a morphism
    `g : X ⟶ Y` over `Spec K`, it constructs the continuous maps
    `morphismLocalMap` of affine chart analytifications. It defines the predicate
    `IsAnalytificationMap g hg F` on continuous maps `F` of glued spaces: `F` is
    compatible with these local maps on every pair of affine opens `U`, `V` with
    `g(U) ⊆ V`.
  - `AffineAnalytificationLocalizedMap` (candidate
    `bf6b3e0d-14a1-4538-8cca-60f7c04d41b2`, Reviewer 4523). For every `K`-algebra
    map `f : A → B`, it constructs `saturatedHom K P Q f` between saturated
    presentations and `localizedHom K P Q f : localized K Q ⟶ localized K P` in
    the localized category, with underlying map `baseMap`.
- First published at `2016a0d994180c702214a75514a08546aa930f07`:
  - `SchemeAnalytificationMorphismStatement` (candidate
    `f1cd2c23-09f8-4fc6-b27c-188775e146b7`, Reviewer 4544; proof Task 7118
    `8074ec5b-c845-4d65-8cc4-6a5be50d7a84`). There is exactly one continuous map
    of glued spaces satisfying `IsAnalytificationMap` for `g`. Every such map is
    compatible with the center maps and sends analytic rational points to analytic
    rational points. Composites of such maps are such maps for composites.
  - `AffineAnalytificationLocalizedFunctorialityStatement` (candidate
    `3d06a904-ef32-4438-af1f-e38189f80ab0`, Reviewer 4548; proof Task 7119
    `711fd0e4-3a70-4bec-99b8-e062dd42ff6a`). `saturatedHom` and `localizedHom`
    preserve identities and composites. The identity of `A` induces an isomorphism
    between the localized analytifications for two presentations.
  - `SchemeAnalytificationAnalyticStructureStatement` (candidate
    `29cca3b4-5253-4c09-84e6-2963eb219508`, Reviewer 4549; proof Task 7120
    `032e0d8b-d716-44e2-ab5e-08385567bb55`). There are a saturated presentation
    `S`, a homeomorphism from its space to `Space K f`, and for every affine open
    `U` an analytic domain `D U` of `S` with an isomorphism in the localized
    category from the affine analytification of `U` to `D U`. These are compatible
    with `ι K f U` and with restrictions (Berkovich 1990, proof of Theorem 3.4.1,
    step (3)).
  - `AffineAnalytificationAffinoidMap` (definition; candidate
    `6ff7b975-2be7-42b3-8e1a-80853bf9f638`, Reviewer 4558). For a presented
    affinoid algebra `R`, it constructs the strong map `affinoidStrongHom` from the
    singleton atlas of `M(R)` to the atlas of `Spec(A)ᵃⁿ` for every `K`-algebra map
    `A → R`. Conversely, `strongHomAlgHom` gives the algebra map of a strong map.
- First published at `497ef49830025d23824f6b2e2b1d5d60b594f51e`:
  - `AffineAnalytificationAffinoidUniversalStatement` (candidate
    `f2a0ffab-aa9a-4ca4-843d-1d19bf009e05`, Reviewer 4650; proof Task 7167
    `ee943114-0baa-4432-9cb9-cef090ce46d0`). Strong maps from `M(R)` to
    `Spec(A)ᵃⁿ` correspond bijectively to `K`-algebra maps `A → R`, naturally in
    `R` and in `A`. Points map to the expected seminorms.
  - `AffineAnalytificationFibreProductStatement` (candidate
    `0904b7b5-141b-4f86-a0d5-88663ff91632`, Reviewer 4658; proof Task 7168
    `46196b21-c6e5-4dd5-be9c-8f78a02733a5`). `Spec(A ⊗[C] B)ᵃⁿ` is the fibre
    product of `Spec(A)ᵃⁿ` and `Spec(B)ᵃⁿ` over `Spec(C)ᵃⁿ` in the localized
    category (Berkovich 1993, Proposition 2.6.1).
  - `AffineAnalytificationEtaleStatement` (candidate
    `c7d08a08-4b0d-4997-bd27-0fe17fde92c8`, Reviewer 4663; proof Task 7169
    `cd8fa5b0-d6a1-4c30-9d2a-046c2b5fffa1`). `saturatedHom K P Q f` is
    unramified, flat or étale in the Library's sense of Berkovich 1993, Definitions
    3.2.5 and 3.3.4, if and only if `f` is formally unramified, flat and
    quasi-finite, or étale, respectively.
  - `SpaceAnalytification` (definition; candidate
    `3cc71666-89a1-4598-a886-cfa3cf413053`, Reviewer 4671). An analytification of
    an algebraic space `X` is an object `Y` of the localized category with a family
    `p` of morphisms `Spec(A)ᵃⁿ ⟶ Y`, one for each `A`-point of `X`. The predicate
    `IsAnalytification` requires naturality in `A`, étale maps for étale points,
    joint surjectivity from étale points, and pullback squares for affine fibre
    squares. The module also defines `rationalPoint`. Its Markdown relates the
    predicate to the analytic quotient of Conrad–Temkin, Definition 4.1.1 and §4.1.
- First published at `93ead8870c8ad195ed8719439da04773c09e5ea3`:
  - `AnalyticImmersion` (definition; candidate
    `9feb21bf-d11e-4dfb-ab25-5b19c4721158`, Reviewer 4764). It defines the
    morphism properties `SaturatedAtlasPresentation.closedImmersion` and
    `openImmersion` of the localized category, after Berkovich 1993, Lemma 1.3.7
    with the definition after its proof and the paragraph after Definition 1.3.1.
    It proves identity and isomorphism-invariance lemmas.
  - Seven statements on analytifications `(Y, p)`, under the hypotheses above.
    `SpaceAnalytificationExistenceStatement` (candidate
    `ab2455e5-f02e-4eb1-b9b7-c97af64005b7`, Reviewer 4719; proof Task 7245
    `90ee99f4-d134-4910-8621-d8e186bfea8f`): an analytification exists.
    `SpaceAnalytificationMorphismStatement` (candidate
    `193ba29a-ce42-426c-b217-6a0a47ca7a89`, Reviewer 4723; proof Task 7246
    `27620dd4-0641-4080-98cc-23e6dbc17f21`): a morphism `f : X' ⟶ X` induces a
    unique morphism `F` of analytifications compatible with the test-point maps.
    The étale, fibre-product and immersion statements below concern such
    compatible morphisms.
    `SpaceAnalytificationRationalPointsStatement` (candidate
    `a0f0327b-1ee0-44ab-8c95-2aa704cae60b`, Reviewer 4728; proof Task 7247
    `6145952e-407a-4855-8def-a8263bedfbf7`): the underlying space of `Y` is
    Hausdorff, and `rationalPoint` is a topological embedding of `X(K)` with
    `etaleChartTopology`. `SpaceAnalytificationEtaleStatement` (candidate
    `de3d20be-6c7b-48cc-9663-c31f8d179e6f`, Reviewer 4732; proof Task 7248
    `b20171a8-9554-4f51-b56f-227e66409b5b`): `f` is étale if and only if `F` is
    étale. `SpaceAnalytificationFibreProductStatement`
    (candidate `679cbaa9-20ac-4376-8bfb-38bf96474487`, review task
    `00ec1478-1a85-46fc-87bb-94d4d5d10a3c`; proof Task 7249
    `f65ed7bd-6eb8-46fe-a279-b68de84862b7`): a pullback square of such spaces,
    with compatible morphisms of their analytifications, gives a pullback square
    of analytifications. `SpaceAnalytificationSchemeStatement` (candidate
    `b2bfad48-98f5-4ae7-b7ca-6559ac012e19`, Reviewer 4735; proof Task 7250
    `63c57e1a-a624-4048-914e-dbe4f869dc25`): for a separated scheme, the
    underlying space of `Y` is homeomorphic to `Space K f`, compatibly with the
    charts and with rational points. `SpaceAnalytificationImmersionStatement`
    (candidate `85e39fca-a132-4f8d-b1bf-6f1fef0c2819`, review task
    `49b4e97b-44f7-49be-b703-0ba74c405e63`; proof Task 7251
    `6aae2ba3-a5e5-4ca2-8e1e-209363dee704`): if `f` is an open or closed
    immersion, the underlying map of `F` is an open or closed embedding.
- First published at `c0c2e1210454ae2a1888a2989e3de794c1336819`:
  - `AffineAnalytificationAnalyticImmersionStatement` (candidate
    `ac81b9b6-81e8-4084-8be9-c873ad9838a5`, Reviewer 5256; proof Task 7299
    `b71751b5-5608-4451-b3f0-9a02e0ff976a`). `f` is surjective if and only if
    `localizedHom K P Q f` is a closed immersion. `Spec(f)` is an open immersion
    if and only if `localizedHom K P Q f` is an open immersion (Berkovich 1990,
    Propositions 3.4.6(8) and 3.4.7(2)).
  - `SpaceAnalytificationAnalyticImmersionStatement` (candidate
    `a5fcab52-0a1f-4110-9b56-d3418077be99`, Reviewer 5261; proof Task 7300
    `7392723a-c591-4e5e-ac51-bb0bcc559ebf`). For a compatible `F`, `f` is an open
    immersion if and only if `F` is one. If `f` is a closed immersion, so is `F`.
    If `f` is quasi-compact, the converse holds for closed immersions
    (Conrad–Temkin, Theorem 2.3.1, in the `k`-analytic setting of §4.1).

The two review tasks named above record approvals whose rationales do not name the
reviewer.

Proof status. This Library proves none of the thirty-one published statements of
the varying-dimension and analytification programs: each statement name occurs in
no Lean file other than its own module. Every statement has its own proof task,
published by the parent, because the parent's `lean.peer@1` policy accepts
definitions and statements but not proofs. Compiled proof drafts are shared
publicly as draft revision 1 on seven proof tasks: Tasks 7072, 7083, 7084, 7085,
7086, 7119 and 7167. The drafts on Tasks 7084 and 7086 import the unpublished
Task 7083 draft module, and those on Tasks 7119 and 7167 import the unpublished
Task 7085 draft module. A shared draft is not a reviewed or published proof.

These units do not supply the following. The analytification of an algebraic space
is characterized by `IsAnalytification` and its existence is stated, but no quotient
`Uᵃⁿ/Rᵃⁿ` of an étale chart is constructed. The scheme maps, analytic structure,
universal property, fibre-product, étale, immersion and rational-point comparisons
are stated, not proved. No statement identifies the image of `rationalPoint` with
the `K`-points of the analytic space. Analytic ground-field extension is not
constructed: this Library has no extension of presented affinoid algebras or
affinoid atlases along `L/K`. The parent published Task 7100
`7b5d3807-3a12-4dac-ae8a-a7f93d7fc2b8` for that construction. The canonical
isomorphism `(Xᵃⁿ)_L ≅ (X_L)ᵃⁿ` therefore remains neither constructed nor
stated.

## Center, rational-point and base-change statement publications, 15 November 2026 (second audit)

This focused audit checks Library `e1fa6f689f9e976eb7574f0dce4453b3b5705ac0`
under the unchanged revision 2 contract. It records three more independently
reviewed statement publications of parent Task 3519. All earlier dated sections,
assertion and hypothesis cells, and table order are retained. This section updates
the status cells of the analytification rows and remaining obligation 2. It does not
certify whole-paper completion. Its statuses supersede the description of these
three candidates as approved but unpublished in the first 15 November audit below.

The three statements were all first published at
`ccd5c6bb63352c109b2bfde422a65c2dd78e57fd`. Their six Lean and Markdown files
match this Library and the workspace byte for byte. They are in
`Langlands/Geometry/Analytic/`, under the hypotheses of the first 15 November audit:
a complete nontrivially normed nonarchimedean `K`, and a finite polynomial
presentation `P` of a commutative `K`-algebra `A` or a scheme `X` locally of finite
type over `Spec K`.

- `Langlands.Analytic.SchemeAnalytification.AnalytificationCenterStatement`
  (candidate `d095a1d9-af2c-480f-a7ea-f0acc4e34810`, Reviewer 4446; proof Task
  7097 `b92d9284-a406-49b1-af51-96979d7e0e5c`). In the affine case,
  `AffineAnalytification.center` is surjective onto `PrimeSpectrum A`. The center
  of the analytic point of `φ : X(K)` is `ker φ`, and that analytic point is the only
  point with this center. In the scheme case, `center` is surjective, the preimage
  of an affine open `U` is the image of `ι U`, the center of
  `analyticRationalPoint p` is the image of the closed point under `p`, and that
  point is the only point with this center (Berkovich, Theorem 3.4.1 and
  Remark 3.4.2; Conrad–Temkin §4.1).
- `Langlands.Analytic.SchemeAnalytification.SchemeAnalytificationRationalPointsStatement`
  (candidate `8c5afff7-58f9-4bb3-8fde-46fbc7bbad04`, Reviewer 4449; proof Task 7098
  `b0baa8b3-a86f-4e40-91d6-2f1b4c947be0`): `analyticRationalPoint` does not
  depend on the affine chart and is injective. Its range is the union of the chart
  images of the affine analytic rational points. It is a topological embedding for
  `schemePointTopology` (Conrad–Temkin Example 2.3.2).
- `Langlands.Analytic.AffineAnalytification.AffineAnalytificationBaseChangeStatement`
  (candidate `868763f3-1de0-4519-aaf0-a148c86adbf7`, Reviewer 4453; proof Task 7099
  `424733ee-4a23-47ac-b5b1-1b6dd83190b7`): for every complete nontrivially normed
  nonarchimedean `L` with `NormedAlgebra K L`, `baseChangeMap : (X_L)^an → X^an`
  is surjective. Its fibre over the analytic point of `φ : X(K)` is the single
  analytic point of the induced `L`-point of `X_L` (Berkovich §2.3;
  Conrad–Temkin Theorem 2.3.5).

The parent published each proof task, because its `lean.peer@1` policy does not
accept proofs. This Library proves none of the sixteen published statements of
the varying-dimension and analytification programs: each statement name occurs only
in its own module. Compiled proof drafts are shared publicly on five proof tasks:
Task 7072 (naturality), Task 7083 (seminorm description) and Task 7085
(functoriality and presentation independence) import only published modules. The
drafts on Task 7084 (affine rational points) and Task 7086 (immersions) also import
`Langlands.Geometry.Analytic.AffineAnalytificationSeminormProof`, the unpublished
Task 7083 draft module. A shared draft is not a reviewed or published proof.

## Smooth-dimension and analytification publications, 15 November 2026

This focused audit checks Library `b3dcc8cc4c93f1140c6b34374f589ccc637a1a22`
under the unchanged revision 2 contract. It records 22 independently reviewed
publications of parent Task 3519: nine smooth-dimension units and thirteen
analytification units. Their 44 Lean and Markdown files match this Library and
the workspace byte for byte. The commit that first contains each pair was found by
scanning the Library manifests. This Library proves none of the thirteen new
statements (seven smooth-dimension, six analytification): each statement name occurs only in its own module. Every statement
has its own proof task, published by the parent, because the parent's
`lean.peer@1` policy accepts definitions and statements but not proofs. All
earlier dated sections, assertion and hypothesis cells, and table order are
retained. This note updates selected declaration and status cells and the
remaining obligations; it does not certify whole-paper completion. Its statuses
supersede the 14 November description of candidates
`80256500-ff18-4319-b460-d3bde9e41e12` and
`f2d2c6ef-96a6-4993-9ead-a59caccfe218` as unpublished.

**Varying-dimension smooth spaces (Prop 5.4, p.15).** These units are in
`Langlands/AlgebraicGeometry/AlgebraicSpace/`, namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace`.

- `SmoothSourceDimensionTopologyStatement`, candidate
  `80256500-ff18-4319-b460-d3bde9e41e12`, Reviewer 3867, first published at
  `7f5b5f04a855fc0b4671393213c87415a6ee2aaf`. It states that the actual
  `SmoothDimensionPieces.fieldPointEquiv` from `X(K)` to the dependent sum of the
  piece point spaces is a homeomorphism for `etaleChartTopology`. The hypotheses are a
  henselian nontrivially normed `K` and a quasi-separated smooth `X`; neither
  completeness nor local separatedness is assumed. Proof: Task 6936
  `7e14e6f5-9447-4b9a-8f26-96906d761802`.
- `SmoothSourceAnalyticAtlas` (definition), candidate
  `f2d2c6ef-96a6-4993-9ead-a59caccfe218`, Reviewer 4007, first published at
  `aeb3911c4e1bf6e3a2f653e874e4ebc422d2a61a`. It defines `DimensionPointAtlas`
  with `IsAnalytic`, `AnalyticOn`, `AnalyticMap`, `IsLocalAnalyticIso` and
  `Equivalent`. It also constructs `AnalyticPointStructure.dimensionAtlas` and
  proves `liftDimensionChart_transition`.
- `SmoothSourceDimensionAnalyticAssemblyStatement` (candidate
  `d7a3451f-c52e-4c86-a60d-ab259584d96c`, Reviewer 4191),
  `SmoothSourceDimensionAnalyticFunctorialityStatement` (candidate
  `76227c22-af14-4e03-9fd2-6b2a855309c6`, Reviewer 4204),
  `SmoothSourceDimensionEtaleAnalyticIsoStatement` (candidate
  `3ad09380-dc16-4159-bca8-f0ad3dd410e6`, Reviewer 4212) and the definition
  `SmoothSourceAnalyticStructure` (candidate
  `1d047792-f10b-430f-9cc0-4bbf05ee0960`, Reviewer 4229) were all first published
  at `4abbe7aabd9c92005d91c9d5bba86b879e928bb3`. The three statements cover a
  henselian nontrivially normed `K` and a pure-dimensional family `σ`. The
  assembly statement assumes that `σ` is analytic; the other two assume that `σ` is
  admissible. They assert that the lifted atlas is analytic, that every morphism of
  smooth, quasi-separated, locally separated spaces is analytic, and that every
  étale morphism is a local analytic isomorphism. The definition introduces the
  family `DimensionAnalyticStructure` with `IsAnalytic`, `IsFunctorial`,
  `IsEtaleLocalIso`, `AgreesWithAffineSpace`, `IsAdmissible` and `Equivalent`, and
  `AnalyticPointStructure.dimensionStructure`. Proofs: Task 7025
  `95b60e1f-6ea1-4ce0-ac6f-1370614addc2`, Task 7026
  `4743ea4e-667d-45b4-a9da-29300160e0cf` and Task 7027
  `ee02855b-785f-4e7d-af71-d3b9e32602b1`.
- `SmoothSourceDimensionAffineAgreementStatement` (candidate
  `4147868c-ce77-4109-aee2-ec7ac46a69db`, Reviewer 4282),
  `SmoothSourceDimensionAnalyticUniquenessStatement` (candidate
  `a2c92d7d-87b8-40d6-9bf4-98268bd406d2`, Reviewer 4284) and
  `SmoothSourceAnalyticManifoldStatement` (candidate
  `59862d27-d5ff-4ed5-be9c-73d22dda4519`, Reviewer 4286) were first published at
  `fab9caeae532b7a65e67e702bcab72d3194371ae`. The agreement statement asserts that
  the lifted structure agrees with polynomial affine space. The uniqueness statement
  asserts that any two admissible structures are equivalent, over any nontrivially
  normed `K`. `SmoothSourceAnalyticManifoldStatement` is the source-level assertion
  of the varying-dimension analytic manifold for complete nontrivially normed `K`:
  an admissible structure exists, and it is unique up to equivalence. Proofs:
  Task 7049 `5df1d791-597c-4b46-929c-4fa2fa6ff30c`, Task 7050
  `94d3b908-dd01-4622-b41a-6724eab58e82` and Task 7051
  `685b8c94-5194-4cb7-8b30-4977774ce694`.

**Analytification (p.19).** These units are in `Langlands/Geometry/Analytic/`, with
namespaces `Langlands.Analytic.AffineAnalytification` and
`Langlands.Analytic.SchemeAnalytification`. All assume a complete nontrivially
normed nonarchimedean `K` and a finite polynomial presentation `P` of a commutative
`K`-algebra `A`, or a scheme `X` locally of finite type over `Spec K`. The
additional registered original is Berkovich, *Spectral theory and analytic
geometry over non-Archimedean fields* (1990), source
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA-256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

- First published at `fab9caeae532b7a65e67e702bcab72d3194371ae`:
  `AffineAnalytificationRationalPoints` (definition; candidate
  `1767d8cf-b298-4087-8e9f-961594cc06a1`, Reviewer 4253), which constructs
  `analyticPoint`, `toFieldPoint` and `toAlgPoint`, and `AffineAnalytificationMap`
  (definition; candidate `1cc9f0f1-376d-48a1-850a-6ee7c25769f0`, Reviewer 4300),
  which constructs `baseMap` and the strong atlas map `strongHom` for every
  `K`-algebra map.
- First published at `0b7bb3fdbe6e0386b666b6b099a3bc9cd3ad7e18`:
  - `AffineAnalytificationRationalPointsStatement` (candidate
    `72e33ec6-47ec-4dd5-8942-0cf614440d22`, Reviewer 4359; proof Task 7084
    `a12135e5-19d0-4b8d-88d1-cf7f0bf4a946`): `toFieldPoint` is bijective;
    `analyticPoint` is a topological embedding of `X(K)`; there is a bijection with the
    `K`-points of the saturated atlas.
  - `SchemeAnalytificationSpace` (definition; candidate
    `bae177d9-72c8-42f5-a1c1-969413a6cdae`, Reviewer 4362): the topological glue
    `Space` of the affine analytifications over all affine opens, with `ι`, `localMap`
    and the universal map `desc`.
  - `AffineAnalytificationFunctorialityStatement` (candidate
    `352f61b7-1cd9-4582-8c59-71ad6e5c4b31`, Reviewer 4363; proof Task 7085
    `6545548c-9d0b-4359-a868-8e52fd060af5`): `strongHom` preserves identities and
    composites. The identity maps between the atlases of two presentations compose
    to the identity, which gives presentation independence in the affine case.
  - `AffineAnalytificationRationalPointNaturalityStatement` (candidate
    `519d1433-c0bc-4902-b1a8-0f80a309e278`, Reviewer 4366; proof Task 7072
    `8a49d73c-1180-41f0-8b5c-03f5bdff1d86`, with a complete proof draft shared as
    draft revision 1): for a `K`-algebra map `f`, `baseMap` sends the analytic point
    of a rational point `φ` to the analytic point of `φ ∘ f`.
  - `AffineAnalytificationImmersionStatement` (candidate
    `27b2aa33-3020-44dc-850c-3a18768412cd`, Reviewer 4375; proof Task 7086
    `15296f18-5435-4142-bd49-fdaf726f1890`): surjections give closed embeddings,
    basic localizations give open embeddings, and the two images are complementary.
  - `AffineAnalytificationSeminorm` (definition; candidate
    `117c9ba6-e8cc-455d-a645-a4e2d6ff791f`, Reviewer 4387): `pointSeminorm` and
    `ExtendsNorm`.
- First published at `b3dcc8cc4c93f1140c6b34374f589ccc637a1a22`:
  - `AffineAnalytificationSeminormStatement` (candidate
    `a68225a2-085b-403a-b9df-96f6908019af`, Reviewer 4406; proof Task 7083
    `72a185e1-3828-4881-b54e-77a117168474`, with a complete proof draft shared as
    draft revision 1). This is Berkovich's Remark 3.4.2 for `Spec A`: the points are
    exactly the multiplicative seminorms on `A` that extend the norm of `K`, with the
    weak topology.
  - `SchemeAnalytificationGluingStatement` (candidate
    `2a2bc9e4-067c-428e-9c38-b421c96b84c7`, Reviewer 4412; proof Task 7087
    `d8f36429-3ce4-491e-9d69-e57ed9b29c76`): the restriction maps and the maps `ι`
    are open embeddings; images of two affine opens meet in the images of the affine
    opens they share; the affine case is a homeomorphism; and `X` is separated if
    and only if `Space` is Hausdorff.
  - `SchemeAnalytificationRationalPoints` (definition; candidate
    `aed9a7e3-4948-4161-aea5-85946e98b44d`, Reviewer 4414):
    `analyticRationalPoint` on actual `K`-points of `X`.
  - `AnalytificationCenter` (definition; candidate
    `3eae0b6f-e6ff-47a6-bc75-e2ac33139e68`, Reviewer 4420): the continuous center
    maps `X^an → Spec A` and `X^an → X` (Berkovich, Theorem 3.4.1).
  - `AffineAnalytificationScalarExtension` (definition; candidate
    `0d33d3ef-6034-4014-802f-926ed50b2190`, Reviewer 4436): for every complete
    nonarchimedean extension `L/K`, the continuous map `extensionMap`, and the
    base-change presentation `baseChangePresentation` of `L ⊗[K] A` with the map
    `baseChangeMap : (X_L)^an → X^an`, `X = Spec A`.

Three further parent statements are staged and independently approved, but
unpublished at this commit; their base is this Library. They are
`AnalytificationCenterStatement` (candidate `d095a1d9-af2c-480f-a7ea-f0acc4e34810`,
Reviewer 4446: the center maps are surjective and their fibres over rational points
are single points), `SchemeAnalytificationRationalPointsStatement` (candidate
`8c5afff7-58f9-4bb3-8fde-46fbc7bbad04`, Reviewer 4449: `analyticRationalPoint` is
chart independent and injective, has the expected image, and is an embedding for
`schemePointTopology`) and `AffineAnalytificationBaseChangeStatement` (candidate
`868763f3-1de0-4519-aaf0-a148c86adbf7`, Reviewer 4453: `baseChangeMap` is surjective,
and its fibre over a rational point is one point).

These units do not supply the following. The glued scheme space is only a
topological space. The Library has no analytic-space structure in
`Langlands.Analytic.SaturatedAtlasPresentation.LocalizedCategory` for a
non-affine scheme, no map of glued spaces for a scheme morphism, and no
analytification universal property (`desc` is only the topological gluing
property). The scalar-extension unit constructs only the comparison map
`(X_L)^an → X^an`. The canonical isomorphism `(X^an)_L ≅ (X_L)^an` would need
analytic ground-field extension in the host; neither is constructed or stated. The
representable analytic étale sheaf quotient for algebraic spaces is not
constructed, and the rational-point comparison with `etaleChartTopology` for
algebraic spaces is not stated. Fibre products and étale maps are not stated
either.

## Published prerequisites and pending bridges, 14 November 2026

This focused audit checks Library `f676fad71e1679d672d3e20560dc814d4e1f8ffd`
under the unchanged revision 2 contract. It records seven independently
reviewed mathematical publications and distinguishes two independently approved
but unpublished parent candidates. The seven publications' fourteen Lean and
Markdown files match this Library and the workspace byte for byte; their
publication receipts and paired Markdown were checked. All earlier dated audit
sections, existing assertion and hypothesis cells, and table order are retained.
This note updates selected declaration/status cells and the remaining obligations;
it does not certify whole-paper completion.

**Unconditional Theorem 4.5.** `Langlands.Global.adelicSpreadSmoothOpen` in
`Langlands/Global/AdelicSpreadSmoothOpenProof` now proves the exact unchanged
`Langlands.Global.AdelicSpreadSmoothOpenStatement.{u}` for every universe `u`.
Candidate `1d1c2129-b265-4dc2-9989-20db2d30c57e` of Task 6189
`e9e13fd5-ffd0-48b1-b75d-809fa5ca2cce` has independent acceptance by
Reviewer 2927, exact-target proof validation
`d9c9ed2e-6dec-43b0-a869-029bbed79570`, and publication at
`ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181`, integration
`bbdf9b87f04046cc832015499e45e2a9`.
Its implemented proof applies `adelicSpreadSmoothOpenOfLangWeil` to the
published `Langlands.AlgebraicGeometry.uniformLangWeil`. Thus the
Lang–Weil premise is discharged, with the separated generic fibres, arbitrary
finite-type spreads, geometrically connected smooth surjection, both global-field
characteristics and all infinite places retained. There is no common fibre
dimension assumption.

**Actual smooth dimension pieces.** Task 6286
`56e7aa6c-1336-4e2d-a66a-59f30689a9f7` supplied three derived construction
units, all published at `ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181`:

- `SmoothSourcePointDimension`, candidate
  `dd56bbc9-37e4-4acf-89e3-7e654da5fbf3`, Reviewer 2940, constructs
  `SmoothDimensionPieces.pointDimension` on actual ordinary quotient points
  and proves all-chart local-dimension agreement, local constancy and atlas
  independence.
- `SmoothSourceDimensionPieces`, candidate
  `5b751880-9ae8-4b1a-bc5e-7a35268cb9b4`, Reviewer 2981, constructs
  `SmoothDimensionPieces.space` and `inclusion` as genuine represented open
  subspaces. Their ordinary-point loci are open and closed, cover and are
  disjoint. The actual restricted surjective étale atlases are smooth of
  relative dimension `n`, including empty pieces.
- `SmoothSourceDimensionFieldPoints`, candidate
  `331ba145-f3d7-49d3-bad3-0adf9381a3b4`, Reviewer 3000, constructs
  `SmoothDimensionPieces.fieldPointFactor` and `fieldPointEquiv`, with inverse
  the actual piece-inclusion assembly and both inverse laws proved.

These units use any field `K`, any actual `SmoothOverBase X`, and every
natural-number dimension, without quasi-compactness or finite range. The
section equivalence works over every extension field. Quasi-separatedness and
local separatedness are supplied separately only for the existing
pure-dimensional analytic interface. These algebraic constructions prove
neither a rational-point homeomorphism nor a varying-dimensional analytic
structure.

The parent's `SmoothSourceDimensionTopologyStatement`, candidate
`80256500-ff18-4319-b460-d3bde9e41e12`, is still staged and unpublished.
Reviewer 3867 independently approved it, and machine validation
`33457acf-cd68-490f-84a4-9ff36c61367f` succeeded. Its exact proposition
requires the actual `fieldPointEquiv` to be a homeomorphism for the independently
defined étale-chart and dependent-sum topologies. Its topological scope is
henselian nontrivially normed `K` and quasi-separated smooth `X`, without
completeness or local separatedness. The proof remains a successor after
publication; this broader topological scope does not enlarge the corrected
full analytic package.

The parent's `SmoothSourceAnalyticAtlas`, candidate
`f2d2c6ef-96a6-4993-9ead-a59caccfe218`, is also staged and unpublished.
Reviewer 4007 independently approved it, and machine validation
`c46c0175-9f72-46d2-b65e-012f4a424098` succeeded. Its
`AnalyticPointStructure.dimensionAtlas` lifts any supplied pure-dimensional
chart family through the actual dimension-piece open embeddings to charts on
the original `RingPoints` with `etaleChartTopology`, for henselian nontrivially
normed `K` and smooth quasi-separated locally separated `X`. This topological
construction requires no completeness or analytic law for the supplied family.
It constructs coverage,
intrinsic dimension laws and exact same-piece transition comparisons.
Its predicates retain continuity and every source/target dimension pair on
the full target-chart intersection. Analytic assembly, functoriality, étale
local analytic isomorphisms, scheme agreement and uniqueness remain unproved
successors. Recovery compilation of both parent modules has zero errors or
warnings; development compilation and independent approval do not establish
publication.

**Actual finite-type affine input.** Task 6230
`ad8e3e5e-2e0e-4f05-9924-191590422efd` supplied three final construction
units, all published at `af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e`:

- `AffineAnalytificationGluing`, candidate
  `80ca43a1-4664-4d0a-b0dd-76e29cf3154e`, Reviewer 3210, constructs
  the Hausdorff topological glue of cofinal bounded polynomial-kernel loci,
  their actual restriction maps, chart cover and chart neighborhoods.
- `AffineAnalytificationAtlas`, candidate
  `b9fc0541-b432-46ba-aa27-773056f88d21`, Reviewer 3246, constructs the
  affinoid atlas, full-domain saturation and object of the existing
  `Langlands.Analytic.SaturatedAtlasPresentation.LocalizedCategory`.
  Repeated chart ranges are handled by least-index representatives with
  actual bounded algebra equivalences from full domain universal properties.
- `AffineSchemeAnalytification`, candidate
  `baa423a2-e367-43b8-8e65-accddb38b1bd`, Reviewer 3267, supplies
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
comparisons and arbitrary complete nonarchimedean extension remain successors
owned by the parent. The construction publications and the existing
extension-point endpoint do not discharge these comparisons.

The current statuses below supersede the open-prerequisite descriptions in the
preserved 13 November snapshots. The explicit pauses and ownership of Tasks
5202 and 5217 remain in force.

## Revision 2 scope and retained inputs, 13 November 2026

This focused update reconciles the ledger with Task 3519 revision 2, contract
`6df270668d0170befd3c0d2ce873c8cb3249b1357a1460b51f30cc7369fd3f2e`, against
Library `aae8cb822941fac72c628376bd39754a1bc40b74`. It adds no mathematical
publication. The previous focused note, candidate
`ca24e01b-f8d1-485a-940c-1228636c5f09`, remains accepted and published at commit
`53f5f6fa5c9e4c7b43d5bd69352ac077004b4271`; its review accepted the publication-status
update, without certifying whole-paper completion. The dated audit sections from
“Final Lang–Weil, openness and Example 5.5 publications” through “Earlier focused
audit” below are preserved as historical snapshots. Later status changes and
scope qualifications in this revision take precedence when reading current rows.

Revision 2 makes the following source corrections explicit, preserving the other
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
  open. Task 6286 `56e7aa6c-1336-4e2d-a66a-59f30689a9f7` constructs the algebraic
  pieces and section maps; their rational-point homeomorphism and the functorial,
  unique analytic assembly remain successors owned by this parent.
- Example 5.5 retains the geometric orbit-stratum and quotient scope. Its topology
  clause adds local separatedness of the quotient, and qualifies local
  compactness and total disconnectedness by the field. All three corrected
  clauses have published proofs, as recorded in the historical publication audit.
- Corollary 5.7 uses the image of integral points. Injectivity needs separatedness;
  closedness needs separated finite type. The two closedness counterexamples and
  the broader open and compact-image scopes remain required and recorded.
- Proposition 5.8 uses a separated finite-type target and hence finite-type
  source. The local Corollary 5.6 retains its quasi-separated locally finite-type
  scope, without a local-separatedness requirement; Theorem 5.9 keeps finite type.
- Proposition 5.11(1) uses `IsModuleTopology K K'` for arbitrary finite extensions
  of henselian nontrivially valued fields. It adds no separability, completeness,
  local separatedness, separatedness or scheme assumption. The mathematical
  obstruction and the proved correction, rather than an unavailable historical
  operator message, justify this revision. The reversed inclusion in Example 2.2,
  the support/factorization distinction in Remark 3.3 and the caveat for (3.6.2)
  remain in force.

The actual analytification input on Conrad p.19 remains required: scheme
analytification, the representable analytic étale sheaf quotient for separated
algebraic spaces, functoriality and the listed geometric compatibilities,
rational-point and topology comparisons, and arbitrary complete nonarchimedean
field extension. Task 6230 `ad8e3e5e-2e0e-4f05-9924-191590422efd` constructs the
actual finite-type affine input. The general scheme, quotient and comparison
successors remain with the parent. The input table below records them separately
from the already-proved rational-point extension endpoint. An assumed functor or
a bare quotient of point sets does not provide this input.

Tasks 6189 `e9e13fd5-ffd0-48b1-b75d-809fa5ca2cce` (unconditional Theorem 4.5),
6230 and 6286 were inspected for this update: each is ready, without an executor
or candidate. Recovery checks recompiled the nine relevant Library modules and
the two saved private compositions with zero errors or warnings; those checks
are development diagnostics, not accepted proof publications. In particular,
`adelicSpreadSmoothOpenOfLangWeil Langlands.AlgebraicGeometry.uniformLangWeil`
checks at arbitrary universe `u`, but its exact-target publication is still
Task 6189's obligation. Task 5202 `e5531847-70bc-4569-b880-2f90d5815c6a` and
Task 5217 `b7321f08-34a4-4479-b6a5-fc099d504d2d` retain their explicit pauses
and ownership. Whole-paper completion remains unclaimed.

## Final Lang–Weil, openness and Example 5.5 publications, 13 November 2026

This focused audit checks Library `2e46b9cac0230529f50cdf96bbe4713c06701fc2`.
The preceding coverage update, candidate
`e0872e9f-ef79-4c7f-b3a2-62b458b19932`, was independently accepted by
Reviewer 874 and published at
`2e5aa9989a9e5567670a14eb7079e3a844641990` by integration
`67b9b57d4f944ba7a0fa2c5f8f7a5956`. Earlier audit sections remain historical
snapshots at their named commits.

The following proof candidates are independently accepted and published at
`51e4d8972659f1ffcf0ca89e8eee9540a30b52d3`; the current Library retains their
files. Each validation listed checks the Lake build, exact target, unchanged
statement and frozen inputs.

| Proof | Candidate | Task | Independent reviewer | Exact-target validation | Published integration |
| --- | --- | --- | --- | --- | --- |
| `adelicSpaceSpreadSmoothOpen` | `621efe5f-e65a-4718-b4c4-c4d554db5a9d` | 5254 `7d7f2664-87c8-4e7c-926c-c38d36f325e5` | Reviewer 691 | `8f5a7838-1b2c-405d-8c94-51a840de8017` | `9e859e515fcd4a5f898e6013ffec273d` |
| `unipotentOrbitStabilizerSmooth` | `798d3ed4-1863-4029-97a9-bd40aa28a360` | 5434 `0e823d86-9f22-48da-b160-eebc1c0160a0` | Reviewer 674 | `1ce0fa8a-863c-4229-81f1-256e96c413f5` | `1d5c587e66a14e5dbf395a0d007c06eb` |

Worker 5254's `Langlands.Global.adelicSpaceSpreadSmoothOpen.{u}` proves the
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
space uniform-estimate proofs are also published, under focused Tasks 5993
and 5995 as recorded below.

Worker 5434's
`Langlands.AlgebraicGeometry.AlgebraicSpace.unipotentOrbitStabilizerSmooth.{u}`
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

Both proof pairs match their accepted archives, publication commit, current
Library and workspace byte for byte. Their target statement pairs also agree
with their respective frozen Library bases and both later published trees.

| Published path | SHA-256 |
| --- | --- |
| `Langlands/Global/AdelicSpaceSpreadSmoothOpenProof.lean` | `daef3aba91252583eb3965a59580543f7ddcfd0c1b9aacd0d2dcb6f284e941c4` |
| `Langlands/Global/AdelicSpaceSpreadSmoothOpenProof.md` | `80105a5b5378bfb0c9fde00a9a463d67737fd5daf4563aad8f9cbef1cc6b2b1a` |
| `Langlands/AlgebraicGeometry/AlgebraicSpace/UnipotentOrbitStabilizerSmoothProof.lean` | `700f4b579d24f1b245522c0da3a5eb898a08cb3ca33b3890c15c55b7f9a24180` |
| `Langlands/AlgebraicGeometry/AlgebraicSpace/UnipotentOrbitStabilizerSmoothProof.md` | `08e85b129b3573635355648a1e23737fe22cfec5334a2e3f97f49092068e67e2` |

The six further proof candidates below are independently accepted and published.
The scheme and space uniform estimates and the second and third Example 5.5
clauses were published at `51e4d8972659f1ffcf0ca89e8eee9540a30b52d3`;
the locally closed stratum proof was published earlier at
`730bd1f25b056b8106a2697e003c1ef1733a6b30`. The conditional Theorem 4.5
proof was published later at `73b1430a339b037d27e9096762b0400adb4fbd19`.
All six are present in this audit's Library. Each validation checks the Lake
build, exact target, unchanged statement and frozen inputs.

| Proof | Candidate | Focused task and submitter | Independent reviewer | Exact-target validation | Published integration |
| --- | --- | --- | --- | --- | --- |
| `uniformLangWeil` | `3f1e0645-a1a3-49d2-9197-d67383981e4e` | Task 5993 `25778dab-dbed-46c5-bee8-599cc201b015`, Worker 7 | Reviewer 732 | `fbc73537-de8e-4841-acdf-0b6cb9c242fd` | `c43ca2dfeec14ccabfb20fe9c78900d7` |
| `spaceUniformLangWeil` | `8544795f-6c5a-42f0-8f20-59ecc57ca5de` | Task 5995 `991471cd-4b37-4692-a8fd-efb640a9b9b0`, Worker 5406 | Reviewer 725 | `5e004a2c-3fcd-47fd-8a5e-72b83ddbd96e` | `b02f73183702486f9d55d240cc912a4d` |
| `unipotentOrbitStratumLocallyClosed` | `bdc83ccd-a83b-4b88-89d0-3ce0358ed191` | Task 5699 `504541db-fcca-4043-9da2-275449ff8584`, Worker 169 | Reviewer 499 | `4d2bca80-69bc-4253-a881-0e15ac4c30b2` | `c08567e090c9445d8eb68255c5b688a4` |
| `unipotentOrbitStratumQuotient` | `b2ef5e3e-ad81-4ab0-b742-9bed77e24f90` | Task 5997 `0e786c59-2592-4f1a-b5c1-79e62cf331ae`, Worker 1410 | Reviewer 719 | `b8b0b863-46ab-438d-900c-6355a33a2a8b` | `26dc91ebca59460eb6f4730afa5ec91c` |
| `unipotentOrbitQuotientPointTopology` | `7934b16d-d2fc-438c-a40e-1bacf197bb85` | Task 5998 `222f3c40-492e-4127-8a2e-141df9e629e1`, Worker 175 | Reviewer 721 | `d155131d-c656-4e48-9e25-099754ffe47f` | `a671ffe579a445f3916fcf91966e8646` |
| `adelicSpreadSmoothOpenOfLangWeil` | `8eb56617-9f29-4894-a2eb-632585fd3912` | Task 5166 `bf4f50f3-77b3-4e25-af38-3f25b86c17b1`, Worker 250 | Reviewer 947 | `64ff83ec-030c-4730-836f-2a3e0d77fd9c` | `103801c8ad684bd9b83e249945df3b99` |

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
separately published proofs. This audit does not claim a separately published
theorem for their conjunction.

Task 5166's `Langlands.Global.adelicSpreadSmoothOpenOfLangWeil.{u}` is now
published. Worker 250 reused Worker 208's shared Lean proof and expanded the
Markdown. It proves the unchanged
`AdelicSpreadSmoothOpenOfLangWeilStatement.{u}`, retaining exactly
`UniformLangWeilStatement.{u}` as its premise. It assembles compatible smooth
geometrically connected models, local openness, almost-all native level
surjectivity and the fixed-model reduction in both characteristics. The target
retains separated generic fibres, arbitrary finite-type models, all infinite
number-field factors and finite constants in the function-field branch,
without a common fibre dimension. Both this implication and its Lang–Weil
input are published. The composition
`adelicSpreadSmoothOpenOfLangWeil uniformLangWeil` is therefore the proposed
unconditional endpoint; this audit does not claim its separate exact-target
proof publication.

The six proof pairs match their accepted archives, respective publication
trees, this audit's Library and the workspace. Their target statement pairs
are unchanged from their frozen bases through this audit's Library. The
fingerprints below identify the six proof pairs; paths are relative to the
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

Recovery check `ab6f6d3b-fab2-44f5-a065-668a90d8ba18` compiles all eight
final proof modules in this audit, using the workspace's published imports
with no private override, with zero errors or warnings. Inspection of the
conditional Theorem 4.5 endpoint retains arbitrary universe `u` and only
`propext`, `Classical.choice` and `Quot.sound`. The earlier draft checks
remain development history; they establish neither absence nor presence of
independent publication.

Tasks 5202 `e5531847-70bc-4569-b880-2f90d5815c6a` and
5217 `b7321f08-34a4-4479-b6a5-fc099d504d2d` retain their administrative
status and explicit run controls. Their parent artifact lists do not
determine whether focused proof tasks have published the mathematical
endpoints. This audit records those publications without resuming either
task or changing ownership. Whole-paper completion remains open.

## Native level-surjectivity publication, 13 November 2026

This focused audit checks Library `7dc9118a3eb340e83e65d6e4174763b7a61e573c`.
The preceding coverage update, candidate
`9b96e0b1-cccb-4bba-a367-a09d3d3e00fe`, was independently accepted by
Reviewer 755 and published in this commit by integration
`aa8e093241ff4ed3bfc3effb7a77a95a`. Its earlier audit sections remain
historical snapshots at their named commits.

The native cofinite-surjectivity proof, candidate
`a3eb7042-5569-41c3-aa02-db4dd8df46e6` for Task 5154
`8edf7218-d402-4a9f-83de-ef5fd5b2c1be`, is now independently accepted by
Reviewer 497 and published at `730bd1f25b056b8106a2697e003c1ef1733a6b30`;
the current Library retains its files. Validation
`95266b93-8ba1-481b-bdcd-5e15810279c7` checks the Lake build, exact target,
unchanged statement and frozen inputs. Integration
`7a0233cec4654c94b75af2175e1ff0fb` establishes publication. Task 5154 is done.
Worker 5218 submitted Worker 208's shared Lean proof with revised Markdown.

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

The proof pair matches its accepted archive, publication commit, current Library
and workspace byte for byte:

| Published path | SHA-256 |
| --- | --- |
| `Langlands/Global/AdelicLevelComponentSurjectivityProof.lean` | `27bec92fd1ecc0d2905cf3d06ae2e13785ed2a75a2d9c4c027d6bdc94d5905f2` |
| `Langlands/Global/AdelicLevelComponentSurjectivityProof.md` | `b839f310886c5caf09d5a7f1a3faabe11c6a376a73872fac1d89bec8c6fcb903` |

Recovery check `11950719-9f77-4442-817c-b448248b93cb` compiles the published
norm-polynomial, plane-curve estimate, reduced-base smoothness, family-induction
and native cofinite-surjectivity modules with zero errors or warnings. Inspection
of the last theorem retains arbitrary universe `u` and only `propext`,
`Classical.choice` and `Quot.sound`. Development check
`adfae09f-79ed-4974-a784-ddb5af9b468f` compiles Task 5166's unchanged shared
Theorem 4.5 draft against published imports alone, with the same universe and
axiom scope and zero errors or warnings. Only that final proof pair is supplied
as a private draft; no unpublished premise overrides a Library module.

All mathematical inputs to the conditional Theorem 4.5 assembly are therefore
published. Its focused exact-target proof publication remains with Task 5166
`bf4f50f3-77b3-4e25-af38-3f25b86c17b1`, which is ready without an executor.
The two final uniform-estimate publications remain with Task 5202
`e5531847-70bc-4569-b880-2f90d5815c6a`; the Theorem 5.9 and Example 5.5
publications retain their existing owners. The development checks and this
documentation update do not discharge those publication obligations.

## Induction, Schmidt and reduced-base publications, 13 November 2026

This focused audit checks Library `9b849caba7c63ede041b7fec49c90ceaafb08568`.
The three proof candidates below are independently accepted and published at
`cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e`; the current Library retains their
published files. Each validation listed checks the Lake build, exact target,
unchanged statement and frozen inputs. Earlier audit sections are historical
snapshots at their named commits and remain unchanged.

| Proof | Candidate | Task | Independent reviewer | Exact-target validation | Published integration |
| --- | --- | --- | --- | --- | --- |
| `familyLangWeilOfPlaneCurve` | `1d68f651-cf69-42a4-ae1e-138a52a9156f` | 5840 `ca492bb9-738b-4b98-bf34-39d32a979729` | Reviewer 483 | `307ec689-80c1-4dfc-a9ae-bda0a5d6b06b` | `608427a8e8f6467d85797ca59e61401d` |
| `planeCurveHasseWeil` | `132bb006-99ec-4983-bb3e-bea5d459101c` | 5406 `f0851881-2bc7-45e6-a745-32e02733564e` | Reviewer 411 | `a62a0064-e1f0-4212-8dba-b3eb75c16a72` | `4bd0d49b93b24946a7fcd46632793c89` |
| `Langlands.GroupScheme.reducedBaseConnectedFibreSmooth` | `1d0df2b8-d657-4d37-8a3e-608f9c6006b9` | 5706 `0804c1fb-2875-4d0a-90cd-e85198e6e762` | Reviewer 321 | `7804fbe1-0f5a-474c-864d-bf725b13bbb0` | `a765b72f4a85465c80fa8c1c12316735` |

The induction proof, by Worker 1383 with Worker 3519, proves the unchanged
implication from the plane-curve estimate to the family estimate in every
dimension. It uses the published zero-dimensional case separately, starts the
positive-dimensional induction with the curve case, and applies slicing for
successors. The upper-bound and Bertini premises are supplied by their proofs.
The Schmidt proof, by Worker 5406 with Workers 81 and 78, now supplies the
plane-curve estimate with no extra premise: its `Stepanov.stepanovNormPolynomials`
constructs the auxiliary polynomials, and the published reduction consumes those
data and the elementary reductions. Thus
`familyLangWeilOfPlaneCurve planeCurveHasseWeil` proves `FamilyLangWeilStatement`
entirely from published proofs.

The reduced-base proof, by Workers 50 and 9, proves the unchanged SGA 3
specialization. It retains the reduced locally Noetherian base, locally finite-type
group, smooth connected residue fibres and locally constant fibre dimension.
Its route places the unit section in the smooth locus using local charts and
then translates; it does not assume flatness. The published stabilizer reduction
can now consume this proof and the published characteristic-zero connectedness
proof.

All four induction statement/proof files and all 34 Schmidt and 18 reduced-base
repository files were matched against their frozen or accepted sources, their
publication commit, the current Library and the workspace. The primary proof
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

Recovery checks `79fdeae6-e74f-422a-8613-33cc60dd9626` (induction) and
`f6964b5e-4def-4f08-b46a-d6517acae0ec` (norm polynomials, plane-curve estimate
and reduced-base smoothness) compiled the published modules without a draft
override, with zero errors or warnings. The continuation check
`633a7961-2f21-4306-b8aa-7d073f33a62a` confirms all four modules and inspects the
induction proof. The induction and reduced-base inspections retain arbitrary
universe `u` and only `propext`, `Classical.choice` and `Quot.sound`. These are
development and recovery checks, not new independent acceptance.

The two final exact-target uniform-estimate publications remain with Task 5202
`e5531847-70bc-4569-b880-2f90d5815c6a`; all their mathematical inputs are now
published. Task 5154 `8edf7218-d402-4a9f-83de-ef5fd5b2c1be` is verifying the
native almost-all level-surjectivity proof, candidate
`a3eb7042-5569-41c3-aa02-db4dd8df46e6`; Task 5166
`bf4f50f3-77b3-4e25-af38-3f25b86c17b1` still has no final conditional
Theorem 4.5 proof publication. For Example 5.5, Task 5434
`0e823d86-9f22-48da-b160-eebc1c0160a0` is verifying Worker 5434's stabilizer
candidate `798d3ed4-1863-4029-97a9-bd40aa28a360`, and the quotient assembly
remains with Task 5217 `b7321f08-34a4-4479-b6a5-fc099d504d2d`. No final
uniform estimate, adelic openness theorem or example assembly is published by
this documentation update. All assertion and hypothesis cells below are retained.

## Component-lifting publication, 13 November 2026

This focused audit checks the component-lifting proof at Library
`cfedefb680f317b0ea5d351023e1c9dd886b2547`. Candidate
`74cc4e7b-20eb-472f-b2d6-f3f16f4a8211`, from Task 5144
`105de89b-639b-4bbe-9b7b-d6956eecc042`, is accepted and published by integration
`295d334dbfad4a609ee9f2db6b2d5011`, with independent semantic review by
Reviewer 135 and exact-target machine validation. The preceding documentation
follow-up, candidate `ad6dc4c4-4e86-4ddf-b3f5-7395100fe504`, is published at
`8cfcc2bff12a9cb7a1f89a973a0c59f2dc39865a`. Unchanged rows below retain their
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

The proof and statement pairs were read, the published proof pair was matched
to its frozen candidate fingerprints, and the proof module recompiled with zero
errors or warnings. The same terminal development check,
`beaa72d7-5215-4c73-abee-70b6cd11a316`, also recompiled the unchanged family-induction
statement and private proof draft. That check supplies no new proof acceptance.
The new published fingerprints are:

| Published path | SHA-256 |
| --- | --- |
| `Langlands/AlgebraicGeometry/UniformLangWeilComponentLiftingProof.lean` | `aa8ea28217f432ffb38ce3172b38b285829bea94ca81e12b1be034ee668ba249` |
| `Langlands/AlgebraicGeometry/UniformLangWeilComponentLiftingProof.md` | `851bcd08daf66470f49eaa9250b1a9a9dff0be960b89d35b28aadf114b8eb8ac` |

Native cofinite level surjectivity (Task 5154
`8edf7218-d402-4a9f-83de-ef5fd5b2c1be`) and the conditional Theorem 4.5 assembly
(Task 5166 `bf4f50f3-77b3-4e25-af38-3f25b86c17b1`) remain open, with no executor
or proof publication at this audit. The family-induction implication remains
open in Task 5840, and the unconditional estimates remain with Task 5202.

For Example 5.5, the reduced-base smoothness proof of Task 5706
`0804c1fb-2875-4d0a-90cd-e85198e6e762` is now staged as candidate
`1d0df2b8-d657-4d37-8a3e-608f9c6006b9`, authored by Worker 50 with Worker 9 as
coauthor. Exact-target machine validation and Reviewer 321's semantic acceptance
report are present, but the candidate is not published at this Library commit.
The corresponding row remains unproved in the Library; this status update does
not count the candidate or the final example assembly as an accepted publication.

## Publication follow-up, 13 November 2026

The follow-up checks three proof publications and the family-induction statement at
Library `17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e`. The affected rows below cite this
follow-up; all other rows keep their earlier provenance. The preceding coverage update,
candidate `44df8e73-e157-498b-aaf6-f8b21997694e`, is now published at
`8ff9abe94fbb8d61ec05e4a00fc92f7cf1534b96`. That documentation publication does not
change the mathematical audit base.

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

Statement `FamilyLangWeilOfPlaneCurveStatement` is published as candidate
`478fd862-edd1-4dd5-a03b-783c003e1b37`. Its exact implication is unchanged.
Proof successor Task 5840 `ca492bb9-738b-4b98-bf34-39d32a979729` is published and
ready, with no executor at this follow-up. The complete proof remains in shared
draft revision 2 of `drafts/886bf565-95e9-4dc6-8a9d-73284a523668/`; it is not a
Library proof. Worker 5202 retains the two final uniform-estimate targets.

All three proof pairs and the statement pair were read and checked byte for byte
against this follow-up's Library base. The three proof modules and the induction
proof draft recompiled with zero errors and warnings; terminal development receipt
`3c249e28-3cf7-4a9e-a9d0-f250fe16c327` is a check of these files, not new proof
acceptance. The published fingerprints are:

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

## Earlier focused audit, 13 November 2026

This update checks Proposition 5.8, the arbitrary-model assembly of Theorem 5.9,
the family dimension-induction interface and the missing Schmidt norm-polynomial
input, and the final proof-task status of Corollary 5.7. It does not re-audit every
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

The family induction statement candidate `478fd862-edd1-4dd5-a03b-783c003e1b37`
has passed machine validation and independent semantic review, but is not yet
published at this audit's Library commit. Its complete proof draft recompiled
without warnings and is shared in revision 2 of
`drafts/886bf565-95e9-4dc6-8a9d-73284a523668/`; it still needs a focused proof task
after statement publication. The final closedness proof candidate
`0ef6acd3-7815-48a9-83bf-8093355bceea` of Task 5692 has passed exact-target machine
validation and independent semantic review, and likewise awaits publication.
These statuses describe the earlier audit at its pinned commit. The later
publications are recorded in the follow-up above; a draft supplies no Library
proof evidence.

## Status vocabulary

- **proved**: a theorem whose type is the named statement is in the applicable Library commit; it is
  named in the row. Publication in the Library is the acceptance evidence. A proof-producing
  `def` of Prop type, published as a supporting definition, counts when its type is the named
  statement up to unfolding; the row says so.
- **construction**: a definition (with its intrinsic lemmas) in the Library.
- **open (task)**: a published statement with no Library proof, assigned to the named task.
- **staged**: a candidate that is not in the applicable Library commit. Its candidate
  ID and any completed review or validation are given; staging alone supplies no
  acceptance or publication.
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
`b239dfb9-a3d3-4a1c-ba58-6b89501b686d` (each with a complete draft). The corrected
Proposition 5.11(1) publication is historically associated with Task 5320
`10fea308-e575-4ca0-80f1-1121cb5ee36c`; this carried task is unavailable in the current
instance. The corrected Lean theorem remains in the Library. Task 5256 is recorded as
retired; revision 2 requires the module-topology replacement and preserves its obstruction,
without relying on an unavailable historical ruling. The
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
the Library, and these tasks are closed. The proof of Task 5358
`b69c88f1-1a0b-41b1-a7ab-e5566c81799a` (`adelicSpaceProperModel`) is in the Library; the task was
not closed when inspected. Task 5257
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
| Thm 4.5 | geometrically connected models, no common dimension | `AdelicSpreadGeometricallyConnectedStatement` | eventual detection of geometric connectedness and of smooth ⊓ geometrically connected for arbitrary ft models, and existence of separated ft models of a smooth geometrically connected map of separated finite-type schemes; curves need perfect `k` | proved (`adelicSpreadGeometricallyConnected`, module `Langlands/Global/AdelicSpreadGeometricallyConnectedProof`, at the 13 November publication follow-up commit; Task 5149 `4a516d9a-eeda-47b6-92af-8e7b2ff6e16f`). The proof uses constructible geometric-connectedness loci, a common filtered successor for simultaneous smoothness, and compatible actual models; no common fibre dimension or Lang–Weil premise is used |
| Thm 4.5 | almost-all level surjectivity | `AdelicLevelComponentSurjectivityStatement`; lifting input `UniformLangWeilComponentLiftingStatement` | both conditional on `UniformLangWeilStatement`; `f` smooth, separated, quasi-compact, geometrically connected, with target of finite type over `Z` (quasi-compact); level surjectivity at almost all places, curves need finite `k`; lifting of points over finite fields, over henselian local rings with large finite residue field, and of ring points over such rings | proved, with `UniformLangWeilStatement` retained as a premise: lifting by `uniformLangWeilComponentLifting` (module `Langlands/AlgebraicGeometry/UniformLangWeilComponentLiftingProof`, at the component-lifting audit commit; candidate `74cc4e7b-20eb-472f-b2d6-f3f16f4a8211`, Task 5144 `105de89b-639b-4bbe-9b7b-d6956eecc042`); native level surjectivity by `adelicLevelComponentSurjectivity` (module `Langlands/Global/AdelicLevelComponentSurjectivityProof`, at the native level-surjectivity audit commit; published candidate `a3eb7042-5569-41c3-aa02-db4dd8df46e6`, Task 5154 `8edf7218-d402-4a9f-83de-ef5fd5b2c1be`, done). The latter constructs exact original-base integral lifts outside a finite small-residue set and proves actual cofinite surjectivity at every enlarged level, retaining all infinite factors and using no common dimension premise |
| Thm 4.5, proof (p.12) | restriction to connected components of the target, with fibres of a common dimension | `SmoothTargetComponentGeometryStatement` | not conditional on Lang–Weil; fibre-geometry clause: `f` smooth and geometrically connected with locally noetherian target, each component restriction has nonempty geometrically connected fibres of pure dimension; preservation clause: arbitrary base scheme, locally noetherian source and target with structure maps locally of finite type, quasi-compact and separated, no hypothesis on `f`, the component restrictions keep these finiteness properties | proved (`smoothTargetComponentGeometry`, module `Langlands/AlgebraicGeometry/SmoothTargetComponentGeometryProof`, at the 13 November publication follow-up commit; Task 5140 `32898b5e-5df2-4520-80ad-856f7be5ac0e`). It applies `smoothPureDimension.2` to each selected component dimension and uses the full fibre-predicate equivalence; the structure-map clause follows from open inclusions and local Noetherianity |
| Thm 4.5 | Theorem 4.5 from Lemma 4.6; unconditional | `AdelicSpreadSmoothOpenOfLangWeilStatement`, `AdelicSpreadSmoothOpenStatement` | separated generic fibres, arbitrary ft models; `g` smooth, surjective, geometrically connected; curves need finite `k` | proved: the conditional target by `adelicSpreadSmoothOpenOfLangWeil` (module `Langlands/Global/AdelicSpreadSmoothOpenOfLangWeilProof`, Task 5166, candidate `8eb56617-9f29-4894-a2eb-632585fd3912`), and the exact unconditional target by `Langlands.Global.adelicSpreadSmoothOpen` (module `Langlands/Global/AdelicSpreadSmoothOpenProof`, Task 6189 `e9e13fd5-ffd0-48b1-b75d-809fa5ca2cce`, candidate `1d1c2129-b265-4dc2-9989-20db2d30c57e`), independently accepted and published at `ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181`. The latter applies the former to the published `Langlands.AlgebraicGeometry.uniformLangWeil`, with no additional premise |
| Lem 4.6 | uniform relative Lang–Weil estimate | `UniformLangWeilStatement` | base of finite type over `Z`; `f` smooth, separated, surjective, of finite type, geometrically connected, fibres of pure dimension `d` | proved (`uniformLangWeil : UniformLangWeilStatement.{u}`, module `Langlands/AlgebraicGeometry/UniformLangWeilProof`, Task 5993 `25778dab-dbed-46c5-bee8-599cc201b015`, candidate `3f1e0645-a1a3-49d2-9197-d67383981e4e`, Worker 7) at the final-publication audit commit. The published proof applies `uniformLangWeilOfFamily` to `familyLangWeilOfPlaneCurve planeCurveHasseWeil`, with no extra premise |

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
| Prop 5.4 | actual chart-topology construction in the full source class | `etaleChartTopology` (`EtaleChartTopology`) | any field `K` with a topology; every actual algebraic space over `K`, in particular all quasi-separated locally finite-type spaces over a henselian nontrivially normed field; the definition needs no henselianity or local separatedness | construction: the final topology of the actual finite-type étale scheme-chart point maps; the full six-property theorem has the separate scope in the preceding row |
| Prop 5.4 | functorial continuity in the full source class | `continuous_ringPointsMap` (`EtaleChartTopologyFunctorial`) | henselian nontrivially normed `K`; target `Y` quasi-separated and locally of finite type; source `X` arbitrary; every morphism `X → Y`; no local separatedness | proved for `etaleChartTopology` |
| Prop 5.4 | agreement with scheme point topology | `isHomeomorph_schemeRingPointsEquiv` (`EtaleChartTopologyFunctorial`) | henselian nontrivially normed `K`; the space of the scheme `U` is quasi-separated and locally of finite type; no local separatedness added | proved: the actual `schemeRingPointsEquiv` is a homeomorphism |
| Prop 5.4 | open- and closed-immersion embeddings in the full source class | `isOpenEmbedding_ringPointsMap`, `isClosedEmbedding_ringPointsMap` (`EtaleChartTopologyFunctorial`) | henselian nontrivially normed `K`; both spaces quasi-separated and locally of finite type; the actual morphism is respectively an open or closed immersion; no local separatedness | proved |
| Prop 5.4 | étale openness in the full source class | `isOpenMap_ringPointsMap_of_isEtaleMorphism` (`EtaleChartTopologyFunctorial`, using `EtaleChartOpenMap`) | henselian nontrivially normed `K`; source quasi-separated and locally of finite type; arbitrary target and an étale morphism; no local separatedness | proved: openness only; the full-package local-homeomorphism assertion keeps its locally separated scope |
| Prop 5.4 | Hausdorff (separated), totally disconnected, locally compact | `SeparatedRationalPointTopologyProperties` (part of the statement above) | `X` quasi-separated, locally of finite type and separated; totally disconnected for ultrametric `K`; locally compact for locally compact `K` | proved (`t2Space_etaleChartTopology`, `totallyDisconnected`, `locallyCompactSpace_etaleChartTopology`) |
| Prop 5.4 | `k`-analytic manifold structure for smooth `X`, complete `k` | `AnalyticPointStructure` (`AnalyticPointManifold`), `AnalyticPointManifoldStatement` | complete `K`; spaces quasi-separated, locally separated, locally of finite type, with an étale atlas smooth of relative dimension `n`; existence and uniqueness up to equivalence | proved (`analyticPointManifold`, module `AnalyticPointManifoldProof`; Task 5259, closed): existence by the admissible family `canonicalAnalyticPointStructure` (`canonicalAnalyticPointStructure_isAdmissible`, intermediate statements below), uniqueness by `AnalyticPointStructure.equivalent_of_isAdmissible` (module `AnalyticPointUniqueness`); this proves the pure-dimensional family. The actual algebraic pieces are published. The varying-dimension statements, including the source-level `SmoothSourceAnalyticManifoldStatement` for varying dimension, are published as recorded in the 15 November audit. Their proofs (Tasks 6936, 7025–7027 and 7049–7051) remain open. Second 17 November audit: six of these seven statements are proved (Tasks 6936, 7025–7027, 7049 and 7050); the proof of the source-level `SmoothSourceAnalyticManifoldStatement` remains open in Task 7051 |
| Prop 5.4, manifold bridge | actual open-and-closed dimension pieces and section decomposition | `SmoothDimensionPieces.pointDimension` (`SmoothSourcePointDimension`); `SmoothDimensionPieces.space`, `inclusion`, `restrictedAtlasMap`, `space_isSmoothPureDimensional` (`SmoothSourceDimensionPieces`); `SmoothDimensionPieces.fieldPointFactor`, `fieldPointEquiv` (`SmoothSourceDimensionFieldPoints`) | any field `K`, arbitrary `SmoothOverBase X`; all `n : ℕ`, including empty pieces, with no quasi-compactness or finite-range assumption; pure-dimensional analytic specialization adds quasi-separatedness, local separatedness and a norm; section maps over every field extension | constructed with intrinsic laws, independently accepted and published at `ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181`: candidates `dd56bbc9-37e4-4acf-89e3-7e654da5fbf3`, `5b751880-9ae8-4b1a-bc5e-7a35268cb9b4` and `331ba145-f3d7-49d3-bad3-0adf9381a3b4`, Task 6286 `56e7aa6c-1336-4e2d-a66a-59f30689a9f7`. Actual restricted atlases, section factorizations and both equivalence laws are proved; the topological and analytic successors remain open. Derived host content, not a separate numbered source theorem |
| Prop 5.4, manifold bridge | rational-point disjoint-union topology and varying-dimension analytic structure | published algebraic input `SmoothDimensionPieces.fieldPointEquiv`; published `SmoothSourceDimensionTopologyStatement`; `AnalyticPointStructure.dimensionAtlas` (`SmoothSourceAnalyticAtlas`), with `DimensionPointAtlas.IsAnalytic`, `AnalyticOn`, `AnalyticMap`, `IsLocalAnalyticIso` and `Equivalent`; `DimensionAnalyticStructure`, `IsAdmissible`, `Equivalent` and `AnalyticPointStructure.dimensionStructure` (`SmoothSourceAnalyticStructure`); `SmoothSourceDimensionAnalyticAssemblyStatement`, `SmoothSourceDimensionAnalyticFunctorialityStatement`, `SmoothSourceDimensionEtaleAnalyticIsoStatement`, `SmoothSourceDimensionAffineAgreementStatement`, `SmoothSourceDimensionAnalyticUniquenessStatement` and `SmoothSourceAnalyticManifoldStatement` | smooth, quasi-separated, locally separated `X` over complete nontrivially normed `K`; actual `X(K)` homeomorphic to the dependent sum of the actual piece point spaces for `etaleChartTopology`; analytic maps on intersections with target pieces, étale dimension preservation and local analytic isomorphisms, scheme agreement and uniqueness | stated, not proved: two definitions and seven statements of parent Task 3519 are independently accepted and published at the commits recorded in the 15 November audit. The topology statement uses weaker henselian/quasi-separated hypotheses, without completeness or local separatedness. The intermediate analytic statements assume a henselian `K` and an analytic or admissible pure-dimensional family. The source-level `SmoothSourceAnalyticManifoldStatement` assumes a complete `K`. The proofs are open in Task 6936 `7e14e6f5-9447-4b9a-8f26-96906d761802`, Tasks 7025–7027 and Tasks 7049–7051; the existing pure-dimensional family does not discharge them. Second 17 November audit: proved except the source-level statement. `smoothSourceDimensionTopology`, `smoothSourceDimensionAnalyticAssembly`, `smoothSourceDimensionAnalyticFunctoriality`, `smoothSourceDimensionEtaleAnalyticIso`, `smoothSourceDimensionAffineAgreement` and `smoothSourceDimensionAnalyticUniqueness` prove the six statements of the same names (Tasks 6936, 7025–7027, 7049 and 7050). `SmoothSourceAnalyticManifoldStatement` remains open in Task 7051 `685b8c94-5194-4cb7-8b30-4977774ce694` |
| Prop 5.4, proof (p.15) | every rational point lifts through an étale map from an affine scheme (Knutson II.6.4) | `RationalPointEtaleLiftStatement` | any field `k`; `X` quasi-separated | proved (`RationalPointEtaleLiftProof.rationalPointEtaleLiftStatement`) |
| Ex 5.5 | unipotent orbit strata locally closed; quotient spaces `V_d/G`; local Hausdorffness of `(V_d/G)(k)` | `UnipotentOrbitQuotientStatement` | henselian `K` of characteristic zero; `G` a unipotent algebraic group (affine, locally of finite type); `V` reduced of finite type with a `G`-action; strata and quotient as in the source (quotient quasi-separated, finitely presented, with flat surjective quotient map); the topology clause adds that the quotient is locally separated (correction below), with local compactness only for locally compact `K` and local total disconnectedness only for ultrametric `K` | all three clauses have separately published exact-target proofs at the final-publication audit commit: `unipotentOrbitStratumLocallyClosed` (Task 5699, candidate `bdc83ccd-a83b-4b88-89d0-3ce0358ed191`), `unipotentOrbitStratumQuotient` (Task 5997, candidate `b2ef5e3e-ad81-4ab0-b742-9bed77e24f90`) and `unipotentOrbitQuotientPointTopology` (Task 5998, candidate `7934b16d-d2fc-438c-a40e-1bacf197bb85`); corresponding proof module names append `Proof` to each statement stem under `AlgebraicSpace/`. Every source correction in this row is retained. All six intermediate targets are also proved, including stabilizer smoothness. No separate conjunction theorem is claimed |
| Cor 5.6 | proper maps over local fields are proper on points | `LocalFieldProperPointMapStatement` | locally compact nontrivially normed `K`; `X`, `Y` quasi-separated and locally of finite type | proved (`localFieldProperPointMap`, module `LocalFieldProperPointMapProof`; Task 5483, closed, with Task 5216): the proved implication `LocalFieldProperPointValuativeReductionStatement` applied to the proved Stacks valuative criterion `spaceValuativeExistence` (Task 5368). The Lean proof replaces Conrad's Chow-lemma argument by the valuative criterion and an ultrafilter limit over the convergent germs of an ultrapower (`LocalFieldProperPointLimit.localFieldProperPointMap_of_valuative`); archimedean `K` remain included (intermediate statements below) |
| Cor 5.7 | `X(R)` open in `X(k)` | `HenselianIntegralPointsOpenStatement` | `O` the closed unit ball, a henselian local ring; `X` quasi-separated, locally of finite type over `O`; the image of `X(O)` in `X_K(K)` is open | proved (`henselianIntegralPointsOpen`) |
| Cor 5.7 | `X(R)` quasi-compact for locally compact `k` and `X` of finite type | `HenselianIntegralPointsCompactStatement` | as above, with `K` locally compact and `X` of finite type over `O`; the image of `X(O)` in `X_K(K)` is compact | proved (`henselianIntegralPointsCompact`) |
| Cor 5.7 | closedness, corrected scope | `HenselianIntegralPointsClosedStatement`; locally compact case `HenselianIntegralPointsClosedOfLocallyCompactStatement`; inputs `HenselianChartIntegralPointsClosedStatement`, `UniformFieldPointChartsStatement` (intermediate statements below) | `X` separated: injectivity of `X(O) → X_K(K)`; closed image if moreover `X` is of finite type over `O`; the locally compact case adds `K` locally compact | proved (`henselianIntegralPointsClosed`, module `AlgebraicSpace/HenselianIntegralPointsClosedProof`, at the 13 November publication follow-up commit; final proof Task 5692 `ecce5523-774d-4d1a-9ab2-1afa2b4d9b64`, for Task 5218 `5e83271c-c91b-45ad-b94a-ea03601fec06`). The finite uniform field-point charts, Hensel lifting and closed chart images give the closed image without a local compactness premise. The locally compact case is also proved (`henselianIntegralPointsClosedOfLocallyCompact`) |
| Cor 5.7 | counterexamples to unqualified closedness | `HenselianIntegralPointsNotClosedOfFiniteTypeStatement`, `HenselianIntegralPointsNotClosedOfSeparatedStatement` | for every such `K` and `O`: a quasi-separated space of finite type, and a separated space locally of finite type, with non-closed image | proved |
| p.17 | level points locally compact Hausdorff, open level changes | `AdelicSpaceLevelTopologyStatement` | separated, finite type over the `S`-integers, curves need finite `k` and nonempty `S` | proved (`adelicSpaceLevelTopology`) |
| p.17 | `X(A_F)`: Weil limit bijection, topology, locally compact Hausdorff with countable base, fibre products, closed immersions, scheme agreement, model independence | `AdelicSpacePointTopologyStatement` (`AdelicSpacePointTopology` constructions) | separated finite-type models, curves need finite `k` and nonempty `S`; fibre products of separated finite-type spaces; scheme agreement for separated ft schemes | proved (`adelicSpacePointTopology`, module `Langlands/Global/AdelicSpacePointTopologyTheorem`; Task 5222 `360a1cdf-4b68-402e-b087-254b03da61f6`, closed): `AdelicSpacePointTopologyProof.adelicSpacePointTopology_of_spread` derives the statement from `spaceFilteredRingPointComparison` and the spread clauses `AdelicSpaceSpreadIndependenceProof.curvePlaceSpaceSpread` and `.numberFieldSpaceSpread`; model existence is `AdelicSpaceSpreadExistenceProof` (from `spaceLimitModelExistence`), model independence `AdelicSpaceSpreadIndependenceProof` (from `spaceLimitMorphismDescent`) |
| Prop 5.8 | proper maps of separated spaces: topologically proper on adelic points | `AdelicSpaceSpreadProperMapStatement`; inputs `AdelicSpaceProperStagesStatement`, `AdelicSpaceProperModelStatement` (intermediate statements below) | arbitrary separated finite-type models of source and target, curves need finite `k` and nonempty `S` (correction below) | proved (`adelicSpaceSpreadProperMap : AdelicSpaceSpreadProperMapStatement.{u}`, module `Langlands/Global/AdelicSpaceSpreadProperMapProof`, at the 13 November audit commit); the final theorem supplies the published topology, proper-stage and proper-model proofs and covers arbitrary independently supplied models in both characteristics. Its internal reductions are `adelicSpaceSpreadProperMap_of_inputs`, `_of_arithmeticInputs` and `_of_properModel` (intermediate statements below) |
| Thm 5.9 | smooth surjective geometrically connected: open on adelic points | `AdelicSpaceSpreadSmoothOpenStatement`; input `SpaceUniformLangWeilStatement`; local input `CompleteFieldSmoothSpacePointOpenStatement` (intermediate statements below) | arbitrary separated finite-type models, curves need finite `k` and nonempty `S`; `g` smooth, surjective, with geometrically connected fibres; the Lang–Weil input: base quasi-separated of finite type over `Z`, `f` smooth of relative dimension `d` on étale charts, separated, quasi-compact, surjective, with geometrically connected fibres | proved (`adelicSpaceSpreadSmoothOpen : AdelicSpaceSpreadSmoothOpenStatement.{u}`, module `Langlands/Global/AdelicSpaceSpreadSmoothOpenProof`, candidate `621efe5f-e65a-4718-b4c4-c4d554db5a9d`, Task 5254) at the final-publication audit commit. The theorem supplies the exact space Lang–Weil premise to the arbitrary-model reduction using `spaceUniformLangWeilOfFamily (familyLangWeilOfPlaneCurve planeCurveHasseWeil) familyPointUpperBound`. No extra hypothesis or fixed relative dimension is assumed; both original model topologies are retained. The separately named exact space estimate is also published as `spaceUniformLangWeil` (Task 5995 `991471cd-4b37-4692-a8fd-efb640a9b9b0`, candidate `8544795f-6c5a-42f0-8f20-59ecc57ca5de`, module `AlgebraicSpace/SpaceUniformLangWeilProof`) |

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
  requires the actual-piece bridge to cover all smooth spaces promised in revision 2.
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
gives the construction from Temkin's *Valued Fields*, Exercise 1.8.11 and Remark 1.9.6.
Revision 2 adopts this mathematical obstruction and the module-topology correction.
The literal statement, and the published
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

## Retained analytification input (Conrad p.19)

These are substantive inputs retained by revision 2. The extension-point endpoint
in the preceding table is already proved by another route; that does not supply
these constructions and comparisons. The analytic host is the existing
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

| Source | Assertion | Lean declarations | Hypotheses and scope | Status and responsible task |
| --- | --- | --- | --- | --- |
| Conrad p.19, scheme case; CT §2.2 input | actual finite-type affine scheme analytification | `Langlands.Analytic.AffineAnalytification.Space`, `chartSystem` (`AffineAnalytificationGluing`); `atlas`, `saturated`, `localized` in the same namespace (`AffineAnalytificationAtlas`); `Langlands.Analytic.AffineSchemeAnalytification.spec`, `affineFiniteType`, `CoordinateRing`, `coordinateIso` (`AffineSchemeAnalytification`). Second 17 November audit: `FiniteTypeDomainNormExtensionStatement` | complete nontrivially valued nonarchimedean `K`; every finite-type commutative `K`-algebra, including nonreduced and zero algebras, the empty scheme and zero polynomial variables; actual polynomial-kernel quotient algebras, radius restrictions and atlas laws | constructed with intrinsic chart/algebra laws, independently accepted and published at `af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e`: candidates `80ca43a1-4664-4d0a-b0dd-76e29cf3154e`, `b9fc0541-b432-46ba-aa27-773056f88d21` and `baa423a2-e367-43b8-8e65-accddb38b1bd`, Task 6230 `ad8e3e5e-2e0e-4f05-9924-191590422efd`. The wrapper uses actual global sections and the canonical affine scheme isomorphism in Mathlib's common universe. Affine maps, rational points, seminorm points, the center map and the scalar-extension comparison map are now constructed. The affine rational-point, functoriality, naturality, immersion and seminorm statements are published. The center and base-change statements were first published at `ccd5c6bb63352c109b2bfde422a65c2dd78e57fd`, with proof Tasks 7097 `b92d9284-a406-49b1-af51-96979d7e0e5c` and 7099 `424733ee-4a23-47ac-b5b1-1b6dd83190b7` (second 15 November audit). Their proofs, the universal property and the scalar-extension isomorphism remain open. 16 November audit: the localized maps (`bf6b3e0d-14a1-4538-8cca-60f7c04d41b2`) and the maps from affinoid spectra (`6ff7b975-2be7-42b3-8e1a-80853bf9f638`) are constructed. The universal property for maps from affinoid spectra is stated (`f2a0ffab-aa9a-4ca4-843d-1d19bf009e05`, proof Task 7167 `ee943114-0baa-4432-9cb9-cef090ce46d0`), not proved. Second 17 November audit: the universal property is proved (`affineAnalytificationAffinoidUniversal`, Task 7167), and so is the seminorm description (`affineAnalytificationSeminorm`, Task 7083). The norm input of the center statement is stated, not proved (`FiniteTypeDomainNormExtensionStatement`, `f573206b-1571-41be-9bfb-1b55d4f51c5f`, proof Task 7628 `3370013d-0145-4a35-b24b-4cdf01cdbc0d`). The center and base-change statements remain open (Tasks 7097 and 7099) |
| Conrad p.19, scheme agreement | affine independence and general scheme analytification by gluing | `Langlands.Analytic.SchemeAnalytification.Space`, `ι`, `localMap`, `desc` (`SchemeAnalytificationSpace`); `SchemeAnalytificationGluingStatement`; affine presentation independence in `AffineAnalytificationFunctorialityStatement` and `AffineAnalytificationLocalizedFunctorialityStatement`; `morphismLocalMap`, `IsAnalytificationMap` (`SchemeAnalytificationMorphism`); `SchemeAnalytificationMorphismStatement`; `SchemeAnalytificationAnalyticStructureStatement`; `Langlands.Analytic.SpaceAnalytification.SpaceAnalytificationSchemeStatement` | complete nontrivially valued nonarchimedean `K`; schemes locally of finite type, without a global affineness or finite-type restriction; actual affine constructions, restriction/gluing maps, independence and scheme morphisms | topological gluing constructed (`bae177d9-72c8-42f5-a1c1-969413a6cdae`, published at `0b7bb3fdbe6e0386b666b6b099a3bc9cd3ad7e18`). Its gluing properties are stated but not proved: open embeddings, intersections, the affine case, and separated ⇔ Hausdorff. Statement `2a2bc9e4-067c-428e-9c38-b421c96b84c7` is published at `b3dcc8cc4c93f1140c6b34374f589ccc637a1a22`; proof Task 7087 `d8f36429-3ce4-491e-9d69-e57ed9b29c76`. Affine presentation independence is stated (`352f61b7-1cd9-4582-8c59-71ad6e5c4b31`; proof Task 7085). Not constructed: maps of glued spaces for scheme morphisms and an analytic-space structure on the glued space; parent Task 3519 retains them. 16 November audit: both are now stated, not proved, and neither is constructed explicitly. The compatibility predicate `IsAnalytificationMap` is defined (`b2b8db01-be48-46bd-b636-6cdcf2e5eb76`). The existence and uniqueness of compatible maps of glued spaces, with centers, rational points and composites, is stated (`f1cd2c23-09f8-4fc6-b27c-188775e146b7`, proof Task 7118 `8074ec5b-c845-4d65-8cc4-6a5be50d7a84`). An analytic-space structure on the glued space with the affine analytifications as open domains is stated (`29cca3b4-5253-4c09-84e6-2963eb219508`, proof Task 7120 `032e0d8b-d716-44e2-ab5e-08385567bb55`). Presentation independence in the localized category is stated (`3d06a904-ef32-4438-af1f-e38189f80ab0`, proof Task 7119 `711fd0e4-3a70-4bec-99b8-e062dd42ff6a`). For a separated scheme, the underlying space of its algebraic-space analytification is stated to be homeomorphic to `Space K f`, compatibly with charts and rational points (`b2bfad48-98f5-4ae7-b7ca-6559ac012e19`, proof Task 7250 `63c57e1a-a624-4048-914e-dbe4f869dc25`). Second 17 November audit: affine presentation independence is proved (`affineAnalytificationFunctoriality` and `affineAnalytificationLocalizedFunctoriality`, Tasks 7085 and 7119). The gluing, scheme-morphism, analytic-structure and scheme-comparison statements remain open (Tasks 7087, 7118, 7120 and 7250) |
| CT Lemma 2.2.1, Definition 2.2.2, Theorems 4.2.1–4.2.2 | actual representable analytic étale sheaf quotient and chart independence | no actual scheme-to-analytic quotient construction identified; the existing analytic category and étale-site infrastructure do not give this bridge. 16 November audit: `Langlands.Analytic.SpaceAnalytification.PointFamily`, `IsAnalytification`, `rationalPoint` (`SpaceAnalytification`); `SpaceAnalytificationExistenceStatement`, `SpaceAnalytificationMorphismStatement` | quasi-separated separated algebraic spaces locally of finite type over complete nontrivially valued nonarchimedean `K`; an actual étale chart `R ⇉ U`, analytic quotient sheaf of `Uᵃⁿ` by `Rᵃⁿ`, its representation by an analytic space and canonical chart comparisons | not stated: parent Task 3519 retains the actual construction and its statement/proof successors; a quotient of bare point sets is insufficient. 16 November audit: characterized and stated, not constructed or proved. `IsAnalytification` (`3cc71666-89a1-4598-a886-cfa3cf413053`) characterizes an analytic space `Y` of the localized category with maps from the analytifications of all affine test points: natural, étale on étale points, jointly surjective from étale points, and sending affine fibre squares to pullbacks. Its Markdown relates it to the quotient of Conrad–Temkin, Definition 4.1.1. Existence for separated spaces locally of finite type is stated (`ab2455e5-f02e-4eb1-b9b7-c97af64005b7`, proof Task 7245 `90ee99f4-d134-4910-8621-d8e186bfea8f`). Uniqueness of compatible morphisms is stated (`193ba29a-ce42-426c-b217-6a0a47ca7a89`, proof Task 7246 `27620dd4-0641-4080-98cc-23e6dbc17f21`); applied to the identity, it makes any two analytifications of a separated space locally of finite type isomorphic by a unique compatible isomorphism. No quotient `Uᵃⁿ/Rᵃⁿ` of an étale chart is constructed |
| Conrad p.19; CT Theorems 2.2.3 and 2.3.1 | functoriality, fibre products, open and closed immersions and étale maps | `Langlands.Analytic.AffineAnalytification.baseMap`, `strongHom` (`AffineAnalytificationMap`); `AffineAnalytificationFunctorialityStatement`, `AffineAnalytificationRationalPointNaturalityStatement`, `AffineAnalytificationImmersionStatement`; no scheme or algebraic-space interface. 16 November audit: `saturatedHom`, `localizedHom` (`AffineAnalytificationLocalizedMap`); `Langlands.Analytic.SaturatedAtlasPresentation.closedImmersion`, `openImmersion` (`AnalyticImmersion`); the affine statements `AffineAnalytificationLocalizedFunctorialityStatement`, `AffineAnalytificationFibreProductStatement`, `AffineAnalytificationEtaleStatement`, `AffineAnalytificationAnalyticImmersionStatement`; `SchemeAnalytificationMorphismStatement`; the algebraic-space statements `SpaceAnalytificationMorphismStatement`, `SpaceAnalytificationEtaleStatement`, `SpaceAnalytificationFibreProductStatement`, `SpaceAnalytificationImmersionStatement`, `SpaceAnalytificationAnalyticImmersionStatement`. Second 17 November audit: inputs to the affine étale statement, `AffineAnalytificationQuasiFiniteStatement`, `AffineAnalytificationFiniteGermComparisonStatement`, `AffineAnalytificationChartFlatStatement` | the separated locally finite-type class above, every morphism, the actual scheme/quotient realization and actual analytic comparison maps; no smoothness or fixed-dimension restriction | affine case stated, not proved; all three statements were published at `0b7bb3fdbe6e0386b666b6b099a3bc9cd3ad7e18`. They cover identities, composites and presentation independence (Task 7085 `6545548c-9d0b-4359-a868-8e52fd060af5`), naturality of analytic rational points (Task 7072 `8a49d73c-1180-41f0-8b5c-03f5bdff1d86`), and closed and basic open immersions (Task 7086 `15296f18-5435-4142-bd49-fdaf726f1890`). Not stated: fibre products, étale maps, and maps for general scheme and algebraic-space morphisms; parent Task 3519. 16 November audit: all are now stated, none proved. Affine: localized functoriality (`3d06a904-ef32-4438-af1f-e38189f80ab0`, Task 7119), fibre products (`0904b7b5-141b-4f86-a0d5-88663ff91632`, Task 7168 `46196b21-c6e5-4dd5-be9c-8f78a02733a5`), unramified, flat and étale maps (`c7d08a08-4b0d-4997-bd27-0fe17fde92c8`, Task 7169 `cd8fa5b0-d6a1-4c30-9d2a-046c2b5fffa1`), and analytic open and closed immersions in both directions (`ac81b9b6-81e8-4084-8be9-c873ad9838a5`, Task 7299 `b71751b5-5608-4451-b3f0-9a02e0ff976a`). Schemes: maps for morphisms (`f1cd2c23-09f8-4fc6-b27c-188775e146b7`, Task 7118). Algebraic spaces: unique compatible morphisms (`193ba29a-ce42-426c-b217-6a0a47ca7a89`, Task 7246), étale maps in both directions (`de3d20be-6c7b-48cc-9663-c31f8d179e6f`, Task 7248 `b20171a8-9554-4f51-b56f-227e66409b5b`), fibre products (`679cbaa9-20ac-4376-8bfb-38bf96474487`, Task 7249 `f65ed7bd-6eb8-46fe-a279-b68de84862b7`), open and closed embeddings of underlying spaces (`85e39fca-a132-4f8d-b1bf-6f1fef0c2819`, Task 7251 `6aae2ba3-a5e5-4ca2-8e1e-209363dee704`) and analytic immersions (`a5fcab52-0a1f-4110-9b56-d3418077be99`, Task 7300 `7392723a-c591-4e5e-ac51-bb0bcc559ebf`). The last asserts both directions for open immersions, the forward direction for closed immersions, and the converse for closed immersions when `f` is quasi-compact; its Markdown gives a counterexample without quasi-compactness. Second 17 November audit: three affine statements are proved: identities, composites and presentation independence (`affineAnalytificationFunctoriality`, Task 7085), naturality of analytic rational points (`affineAnalytificationRationalPointNaturality`, Task 7072) and localized functoriality (`affineAnalytificationLocalizedFunctoriality`, Task 7119). Three inputs to the affine étale statement are stated, not proved: quasi-finiteness is detected by the analytification (`5669db6e-d26c-4385-b61a-cee2a84d0d3a`, Task 7653 `9fb378cf-c57b-465b-bd06-c422a8ab8500`); at points where the analytified map is finite, its flatness and unramifiedness agree with the algebraic ones (`fcb1e6ae-c00f-4f1f-80ec-0af269091da9`, Task 7655 `6f1f9bc0-d74b-4295-81e0-ccba71f22745`); and the chart algebras are flat over the algebra (`949a27d0-4bbe-45d1-8820-1083316b804f`, Task 7657 `f5b29461-c4fc-44cd-8212-aacffc08f5e1`). The other statements of this row remain open in the tasks named above |
| Conrad p.19; CT Example 2.3.2, pp.11–12 | rational points and their topology | `Langlands.Analytic.AffineAnalytification.analyticPoint`, `toFieldPoint`, `toAlgPoint` (`AffineAnalytificationRationalPoints`); `AffineAnalytificationRationalPointsStatement`; `Langlands.Analytic.SchemeAnalytification.analyticRationalPoint` (`SchemeAnalytificationRationalPoints`); `FieldValuedPoints` supplies analytic chart characters. 16 November audit: `Langlands.Analytic.SpaceAnalytification.rationalPoint` (`SpaceAnalytification`); `SpaceAnalytificationRationalPointsStatement`, `SpaceAnalytificationSchemeStatement`. 17 November audit: `SpaceAnalytificationFieldPointsStatement`; `localizedFieldPointFunctor`, `localizedFieldPointProjection` (`FieldValuedPoints`) | the same fields and separated locally finite-type spaces; natural equivalence of actual algebraic and analytic rational points and homeomorphism between the affine-chart analytic topology and `etaleChartTopology`; agreement on schemes and descent through actual étale charts | affine case stated, not proved: `72e33ec6-47ec-4dd5-8942-0cf614440d22` was published at `0b7bb3fdbe6e0386b666b6b099a3bc9cd3ad7e18`, with proof Task 7084 `a12135e5-19d0-4b8d-88d1-cf7f0bf4a946`. It states a bijection with the atlas `K`-points and a topological embedding of `X(K)` into `Xᵃⁿ`. The scheme map is constructed (`aed9a7e3-4948-4161-aea5-85946e98b44d`, published at `b3dcc8cc4c93f1140c6b34374f589ccc637a1a22`). Its statement `8c5afff7-58f9-4bb3-8fde-46fbc7bbad04` (chart independence, injectivity, range, and an embedding for `schemePointTopology`) was first published at `ccd5c6bb63352c109b2bfde422a65c2dd78e57fd`, with proof Task 7098 `b0baa8b3-a86f-4e40-91d6-2f1b4c947be0`; it is not proved. Not stated: the comparison with `etaleChartTopology` for algebraic spaces and descent through étale charts; parent Task 3519. The already-proved extension-point theorem does not supply them. 16 November audit: the topological comparison for algebraic spaces is stated, not proved. For a separated space locally of finite type, the analytification is Hausdorff and `rationalPoint` is a topological embedding of `X(K)` with `etaleChartTopology` (`a0f0327b-1ee0-44ab-8c95-2aa704cae60b`, proof Task 7247 `6145952e-407a-4855-8def-a8263bedfbf7`). For a separated scheme, the homeomorphism of `SpaceAnalytificationSchemeStatement` carries `rationalPoint` to `analyticRationalPoint` (`b2bfad48-98f5-4ae7-b7ca-6559ac012e19`, Task 7250). Not stated: that the image of `rationalPoint` is the set of `K`-points of the analytic space; parent Task 3519. 17 November audit: now stated, not proved. The `K`-valued points of the analytification are determined by their underlying points and correspond bijectively to `X(K)` over `rationalPoint` (`1e2ba471-6ab3-4524-bd8c-1dc0dff3baf7`, proof Task 7486 `74ee4c92-ea0c-4002-aefc-1da4675e9deb`). Second 17 November audit: the affine statement is proved (`affineAnalytificationRationalPoints`, Task 7084). The scheme, algebraic-space and `K`-valued-point statements remain open (Tasks 7098, 7247, 7250 and 7486) |
| Conrad p.19; CT Theorem 2.3.5 | arbitrary complete nonarchimedean scalar extension | `Langlands.Analytic.AffineAnalytification.extensionMap`, `baseChangePresentation`, `baseChangeMap` (`AffineAnalytificationScalarExtension`); no isomorphism `(Xᵃⁿ)_L ≅ (X_L)ᵃⁿ`. Second 17 November audit (Task 7100 publications): `Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension.algebra`, `iota`, `lift`, `functor`, `spectrumProjection` (`GeneralizedAffinoid/GroundFieldExtension`); `tensorEquiv` (`GeneralizedAffinoid/GroundFieldExtensionTensor`); `SpectrumProjectionSurjectiveStatement`, `DomainPreservationStatement`; `Langlands.Analytic.AffinoidChartSystem.AtlasProjection` (`AffinoidChartLift`) and `AtlasProjection.TopologyStatement` | every complete nontrivially valued nonarchimedean extension `L/K`, with no finite-degree, separability or algebraicity restriction; canonical analytic isomorphism `(Xᵃⁿ)_L ≅ (X_L)ᵃⁿ`, naturality, composition in towers and fibre-product compatibility | comparison map only. For affine `X` and every complete extension `L/K`, the continuous map `(X_L)ᵃⁿ → Xᵃⁿ` is constructed (`0d33d3ef-6034-4014-802f-926ed50b2190`, published at `b3dcc8cc4c93f1140c6b34374f589ccc637a1a22`). Its surjectivity and rational-fibre statement `868763f3-1de0-4519-aaf0-a148c86adbf7` was first published at `ccd5c6bb63352c109b2bfde422a65c2dd78e57fd`, with proof Task 7099 `424733ee-4a23-47ac-b5b1-1b6dd83190b7`; it is not proved. Not constructed or stated: the analytic ground-field extension `(Xᵃⁿ)_L`, the canonical isomorphism, naturality, towers and fibre products; parent Task 3519. A finite-extension-only comparison is insufficient. 16 November audit: unchanged. The parent published Task 7100 `7b5d3807-3a12-4dac-ae8a-a7f93d7fc2b8` to construct the ground-field extension of presented affinoid algebras and affinoid atlases; this Library contains no such construction. Second 17 November audit: Task 7100 has published the algebra level, first at `2613dbbf784309977c42d9252b78c1e1cd40be63`. For ultrametric normed fields with `NormedAlgebra K L`, every presented `K`-affinoid algebra `A` has a presented `L`-affinoid extension `A_L`, with the structure map `iota`, a universal property (`lift`), a functor and the restriction map on spectra. For complete `L`, `tensorEquiv` identifies `A_L` with the completed tensor product `A ⊗̂_K L` as bounded `K`-algebras. For complete `K` and `L`, surjectivity of the spectrum projection is proved (`spectrumProjection_surjective`, module `GeneralizedAffinoid/GroundFieldExtensionSurjectiveProof`, first at `fd643ecec6997ef17c8356ddbc924138631307d9`). Preservation of affinoid domains (`DomainPreservationStatement`) is stated, not proved. `AtlasProjection` packages projections from a quotient chart system over `L` to an affinoid atlas over `K`, and its topological laws are proved (`AtlasProjection.topology`, module `AffinoidChartLiftTopology`, first at `fd643ecec6997ef17c8356ddbc924138631307d9`). The ground-field extension of affinoid atlases and analytic spaces, the canonical isomorphism, naturality, towers and fibre products are still neither constructed nor stated; Task 7100 and parent Task 3519 retain them |

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
| Lem 4.6 (`e5531847-70bc-4569-b880-2f90d5815c6a`) | `FamilyLangWeilInDimension`, `FamilyLangWeilStatement` (`LangWeil/FamilyLangWeilStatement`) | `S` of finite type over `Z`; `f : X → S` of finite type, geometrically irreducible, with all fibres of pure dimension `d`; a constant `C > 0` with `\|#X_s(κ) − q^d\| ≤ C·q^(d−1/2)` for every finite field `κ` with `q` elements and every `κ`-point `s` of `S`; the second statement asserts this for every `d` | proved by the published composition `familyLangWeilOfPlaneCurve planeCurveHasseWeil` at the induction, Schmidt and reduced-base audit commit; the first theorem supplies the dimension induction and the second discharges its sole premise. This uses the unchanged zero, curve, slicing, generic Bertini and uniform upper-bound proofs. A separate unconditional family-estimate theorem name is not claimed. The final scheme and space uniform estimates are published as `uniformLangWeil` and `spaceUniformLangWeil` (Tasks 5993 and 5995, candidates `3f1e0645-a1a3-49d2-9197-d67383981e4e` and `8544795f-6c5a-42f0-8f20-59ecc57ca5de`) at the final-publication audit commit |
| Lem 4.6 (Task 3519) | `FamilyLangWeilOfPlaneCurveStatement` (`LangWeil/FamilyLangWeilOfPlaneCurveStatement`) | exactly `PlaneCurveHasseWeilStatement.{u} → FamilyLangWeilStatement.{u}`, with the unchanged full scope of both propositions and no further premise | proved (`familyLangWeilOfPlaneCurve`, module `LangWeil/FamilyLangWeilOfPlaneCurveProof`; Task 5840 `ca492bb9-738b-4b98-bf34-39d32a979729`, done; published candidate `1d68f651-cf69-42a4-ae1e-138a52a9156f`, by Worker 1383 with Worker 3519, at the induction, Schmidt and reduced-base audit commit). It performs induction on positive dimensions and uses the zero case separately; the upper-bound and Bertini premises are discharged by their published proofs. The theorem retains the plane-curve premise, now supplied by `planeCurveHasseWeil` |
| Lem 4.6 (`e5531847-70bc-4569-b880-2f90d5815c6a`) | `FamilyPointUpperBoundStatement` (`LangWeil/`) | `S` of finite type over `Z`; `f : X → S` of finite type; a constant `C > 0` with `#X_s(κ) ≤ C·q^e` for every finite field `κ`, every `κ`-point `s` and every `e` bounding the dimension of the fibre over the image of `s` | proved (`familyPointUpperBound`, module `LangWeil/FamilyPointUpperBoundProof`: `familyPointUpperBound_of_finiteNormalizationCover finiteNormalizationCover`; Task 5405 `d6315fa9-e6a8-41f6-ae31-b7253872c91c`, closed; rows below) |
| Lem 4.6 (Task 5405) | `FiniteNormalizationCoverStatement`, with the structure `FiniteNormalizationCover` (`LangWeil/`) | `S` Noetherian; `f : X → S` locally of finite type and quasi-compact (no separatedness, reducedness or equidimensionality); conclusion: finitely many pieces, each an affine scheme `T_i` with an immersion `T_i → S`, an immersion `U_i → X`, a natural number `d_i` and a finite surjective map `U_i → A^{d_i}_{T_i}` compatible with `f`, such that every `Spec K → X` with `K` a field (same universe) factors through some `U_i`, and `d_i` is at most the topological Krull dimension of the fibre of `f` over the image of every point of `T_i`; derived from the Stacks Project, Lemma 10.115.4 (Tag 00OY) and Section 33.18 with Lemma 33.18.2 (Tags 0CBG, 0CBI) | proved (`finiteNormalizationCover`, module `LangWeil/FiniteNormalizationCoverProof`, with `LangWeil/FiniteNormalizationCoverAlgebra`, `LangWeil/FiniteNormalizationCoverPieces` and `LangWeil/FiniteNormalizationCoverAffine`, declarations prefixed `LangWeil.NormalizationCoverConstruction.`; published for Task 5405; proof Task 5604 `bd611de6-07f4-4aac-a4f1-d1c8be5c2bed`, closed) |
| Lem 4.6 (Task 5405) | `familyPointUpperBound_of_finiteNormalizationCover` (`LangWeil/NormalizationCoverPointBound`) | `FiniteNormalizationCoverStatement` implies `FamilyPointUpperBoundStatement`, in the same universe | proved (conditional on `FiniteNormalizationCoverStatement`, which is proved by `finiteNormalizationCover`; `familyPointUpperBound` applies it to that theorem) |
| Lem 4.6 (`e5531847-70bc-4569-b880-2f90d5815c6a`) | `PlaneCurveHasseWeilStatement`, `BertiniGenericHyperplaneStatement` (`LangWeil/`) | Schmidt's bound: a finite field `F` with `q` elements; `f ∈ F[X,Y]` absolutely irreducible with `a = deg_X f > 0`, `b = deg_Y f > 0` and `9(a+1)²(b+1)² < q`; the number `N` of affine zeros satisfies `\|N − q\| < 2·min(a²b, ab²)·√q`. Bertini: any field `k`; a `k`-algebra `A` generated by `g_1, …, g_n`, geometrically irreducible over `k` of Krull dimension at least 2; the generic hyperplane section `u_0 + Σ u_i g_i = 0` over the fraction field of `k[u_0, …, u_n]` is geometrically irreducible | Schmidt's bound proved (`planeCurveHasseWeil`, module `LangWeil/PlaneCurveHasseWeilProof`; published candidate `132bb006-99ec-4983-bb3e-bea5d459101c`, Task 5406 `f0851881-2bc7-45e6-a745-32e02733564e`, at the induction, Schmidt and reduced-base audit commit). It applies `planeCurveHasseWeil_of_stepanov` to the now-proved `Stepanov.stepanovNormPolynomials` and `planeCurveElementaryReductions`, with no extra premise. Bertini proved (`BertiniGenericHyperplane.bertiniGenericHyperplaneStatement`, module `LangWeil/BertiniGenericHyperplaneProof`, with `LangWeil/BertiniHyperplaneSeparable`, `LangWeil/BertiniHyperplaneKernel`, `LangWeil/BertiniHyperplaneCore` and `LangWeil/BertiniHyperplaneDimension`, declarations prefixed `BertiniGenericHyperplane.`; Task 5407, closed; finite `k` included, by reduction to an algebraically closed field) |
| Lem 4.6 (Task 5406) | `StepanovNormPolynomialsStatement` (`LangWeil/`) | any finite field `F`, `q = Nat.card F`; an absolutely irreducible `f ∈ F[X,Y]` with both partial derivatives nonzero and partial degrees `m ≥ n ≥ 2`; `r(x)` counts `y ∈ F` with `f(x,y) = 0`; for every `M > 0` with `M²(n²+1) + (M+m)n² < q` and `Mn ≤ q`, there exist a finite good set `s` and nonzero `h₁,h₂ ∈ F[X]` with `q < s.card + 2mn`, the bound `r(x) ≤ n` for every rational fibre, degrees below `q(M+E)` and `q((n−1)M+E)` for `E = 2m(n−1)+1`, and multiplicities at least `M r(x)` and `M(n−r(x))` on `s`; this is the algebraic input to the next counting row | proved (`Stepanov.stepanovNormPolynomials`, module `LangWeil/Stepanov/NormPolynomials`, with the supporting `Stepanov/` modules; published in candidate `132bb006-99ec-4983-bb3e-bea5d459101c` for Task 5406 at the induction, Schmidt and reduced-base audit commit). The proof constructs the two nonzero norm polynomials, the good set, and the required degree and multiplicity bounds; these data are no longer an unproved input to `stepanovCounting` |
| Lem 4.6 (Task 5406) | `StepanovCountingStatement` (`LangWeil/`) | a finite field `F` with `q` elements; any `r : F → ℕ`; `2 ≤ n ≤ m` and `9(m+1)²(n+1)² < q`; hypothesis: for every `M > 0` with `M²(n²+1) + (M+m)n² < q` and `Mn ≤ q` there are `s ⊆ F` and `h_1, h_2 ∈ F[X]` with `q < \|s\| + 2mn`, `r(x) ≤ n` for every `x`, `deg h_1 < q(M+E)` and `deg h_2 < q((n−1)M+E)` for `E = 2m(n−1)+1`, and root multiplicities at least `M·r(x)` and `M·(n−r(x))` at every `x ∈ s`; conclusion: `\|Σ_x r(x) − q\| < 2mn²·√q`; a derived abstraction of Schmidt, *Zur Methode von Stepanov* (1973), Section 7, pp.359–360 (equation (40)), and Section 9, p.367 | proved (`stepanovCounting`, module `LangWeil/StepanovCountingProof`; published for Task 5406) |
| Lem 4.6 (Task 5406) | `PlaneCurveElementaryReductionsStatement` (`LangWeil/`) | two clauses over any finite field `F`, for `f ∈ F[X,Y]` absolutely irreducible: (1) if both partial degrees of `f` are positive, some absolutely irreducible `g` with both partial derivatives nonzero, `0 < deg_Y g ≤ deg_X g`, `deg_X g ≤ max(deg_X f, deg_Y f)` and `deg_Y g ≤ min(deg_X f, deg_Y f)` has the same number of affine `F`-zeros as `f`; (2) if `deg_Y f = 1`, the number of affine `F`-zeros of `f` differs from `#F` by at most `deg_X f`; derived from Schmidt (1973), Section 2, p.349 | proved (`planeCurveElementaryReductions`, module `LangWeil/PlaneCurveElementaryReductionsProof`, with `LangWeil/PlaneCurveLinearFibres`, `LangWeil/PlaneCurveSeparableModel` and `LangWeil/PlaneCurveCoordinateOperations`; published for Task 5406) |
| Lem 4.6 (`e5531847-70bc-4569-b880-2f90d5815c6a`) | `FamilyLangWeilZeroStatement` (`LangWeil/`) | the family estimate in dimension 0, with the hypotheses of `FamilyLangWeilInDimension 0` | proved (`familyLangWeilZero`, module `LangWeil/FamilyLangWeilZeroProof`, Task 5404 `d108969a-c371-4c06-9403-4d8d7846d52c`; the proof shows that every fibre has exactly one `κ`-point and does not use quasi-compactness or the base over `Z`) |
| Lem 4.6 (`e5531847-70bc-4569-b880-2f90d5815c6a`) | `FamilyLangWeilCurveStatement`, `FamilyLangWeilSlicingStatement` (`LangWeil/`) | implications: Schmidt's bound and the upper bound give dimension 1; Bertini, the upper bound and dimension `d + 1` give dimension `d + 2` | curve proved (`familyLangWeilCurve`, module `LangWeil/FamilyLangWeilCurveProof`: it applies `familyLangWeilCurve_of_planeComparison` (module `LangWeil/FamilyLangWeilCurvePlaneReduction`) to the proved plane-model comparison of the row below; Task 5408 `bc74c0bd-bddc-4c19-835a-46cd2f533740`, closed); slicing proved (`familyLangWeilSlicing`, module `LangWeil/FamilyLangWeilSlicingProof`, with the helper modules `LangWeil/Slicing/Bridges`, `Core`, `Counting`, `Dimension`, `GenericImage`, `GenericSlice`, `Hyperplane` and `Reduction`, declarations prefixed `Slicing.`; Task 5409 `2795fee1-d876-4010-86ed-ccd7f8e687c7`, closed); the premises `BertiniGenericHyperplaneStatement` and `FamilyPointUpperBoundStatement` are proved (rows above), and the curve implication also assumes Schmidt's bound |
| Lem 4.6 (Task 5408) | `FamilyCurvePlaneComparisonStatement` (`LangWeil/`) | assumes `FamilyPointUpperBoundStatement`; `S` quasi-compact and locally of finite type over `Z`; `f : X → S` locally of finite type, quasi-compact, geometrically irreducible, all fibres of pure dimension 1; there is `B > 0` such that for every finite field `κ` with more than `B` elements and every `κ`-point `s` of `S` some `p ∈ κ[X,Y]`, irreducible over an algebraic closure of `κ`, with degrees in `X` and in `Y` in `[1, B]`, has affine zero count within `B` of `#X_s(κ)`; a plane-model comparison derived from Lang–Weil (1954), printed p.819, and Tao, *The Lang–Weil bound*, Section 2 | proved (`familyCurvePlaneComparison`, module `LangWeil/FamilyCurvePlaneComparisonProof`, with the helper modules `LangWeil/FamilyCurvePlaneReduction`, `AffineCurvePlaneComparison`, `CurvePlaneCharts`, `CurvePlaneFibrePoints`, `CurvePlaneNoetherianInduction`, `CurvePlanePolynomial`, `CurvePlaneRadicialPoints` and `CurvePlaneZeroDimensional`, declarations prefixed `CurvePlane.`; published for Task 5408 as an input to `FamilyLangWeilCurveStatement`; proof Task 5581 `b589cd1b-1a7b-41c8-afcf-506ab674e1e2`, closed; the proof does not use the premise `FamilyPointUpperBoundStatement`) |
| Lem 4.6 and Thm 5.9 (`e5531847-70bc-4569-b880-2f90d5815c6a`) | `UniformLangWeilOfFamilyStatement`, `SpaceUniformLangWeilOfFamilyStatement` (`LangWeil/`) | implications: `FamilyLangWeilStatement` implies `UniformLangWeilStatement`; `FamilyLangWeilStatement` and `FamilyPointUpperBoundStatement` imply `SpaceUniformLangWeilStatement` | first proved (`uniformLangWeilOfFamily`, module `LangWeil/UniformLangWeilOfFamilyProof`; Task 5410 `acab9a1a-0a8e-4bd8-a84b-dc3f7aed3074`, closed); second proved (`spaceUniformLangWeilOfFamily`, module `LangWeil/SpaceUniformLangWeilOfFamilyProof`, with the helper modules `LangWeil/SpaceFamily/Counting`, `DegreePoints`, `FibreCharts`, `FibreProductBase`, `FieldPoints`, `FiniteFieldCharts`, `RingPointCharts`, `SchemeBase`, `SeparatedChart` and `Strata`, declarations prefixed `LangWeil.SpaceFamily.`; Task 5411 `25f82ff3-eaee-49c3-b113-d27d596fe177`, closed); their premises are now supplied by the published composition `familyLangWeilOfPlaneCurve planeCurveHasseWeil` and the published `familyPointUpperBound`. Their unconditional exact-target endpoints are also proved by the published `uniformLangWeil` (Task 5993, candidate `3f1e0645-a1a3-49d2-9197-d67383981e4e`) and `spaceUniformLangWeil` (Task 5995, candidate `8544795f-6c5a-42f0-8f20-59ecc57ca5de`) at the final-publication audit commit |
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
| Prop 5.4, manifold (Task 5259) | `canonicalAnalyticPointStructure`, `canonicalAnalyticPointStructure_isAnalytic` (`SmoothSpaceAnalyticAtlas`); `canonicalAnalyticPointStructure_isFunctorial`, `canonicalAnalyticPointStructure_isEtaleLocalIso` (`AnalyticPointFunctoriality`); `canonicalAnalyticPointStructure_agreesWithAffineSpace`, `canonicalAnalyticPointStructure_isAdmissible` (`AnalyticAffineNormalization`) | every complete nontrivially normed `K`; the family of charted spaces on `X(K)`, with the étale-chart topology, built from affine étale charts smooth of relative dimension `n`; it satisfies `AnalyticPointStructure.IsAnalytic`, `AnalyticPointStructure.IsFunctorial`, `AnalyticPointStructure.IsEtaleLocalIso` and `AnalyticPointStructure.AgreesWithAffineSpace`, hence `AnalyticPointStructure.IsAdmissible`; this proves the existence conjunct of `AnalyticPointManifoldStatement`; the uniqueness clause is `AnalyticPointStructure.equivalent_of_isAdmissible` (`AnalyticPointUniqueness`), and `analyticPointManifold` combines the two | proved for the pure-dimensional family; actual algebraic dimension pieces and the field-section equivalence are published. The rational-point homeomorphism statement, the lifted atlas and the varying-dimension statements are published (15 November audit); their proofs remain open in the proof tasks listed there. Second 17 November audit: every one of these statements except `SmoothSourceAnalyticManifoldStatement` (Task 7051) is now proved |
| Ex 5.5 (Task 5217) | `StabilizerFibreLocalDimensionStatement` | any scheme `S`; a group scheme `G` locally of finite type over `S` acting on `V`; at every point of the stabilizer scheme (the base change of the action graph along the diagonal of `V`), the local dimension of its fibre over `V` equals the dimension of the whole fibre, so stabilizer fibres are equidimensional; input to the local closedness of the orbit-dimension strata | proved (`stabilizerFibreLocalDimension`, module `StabilizerFibreLocalDimensionProof`, helpers prefixed `StabilizerFibre.`; published for Task 5217; proof Task 5438 `cd13f7dc-f2dc-404b-bf3d-5885e82f23bf`, closed) |
| Ex 5.5 (Task 5217) | `OrbitStratumActionRestrictionStatement` | any field `k`; `G` smooth over `k`; `V` locally of finite type with a `G`-action; a reduced scheme `Z` with an immersion onto the points of orbit dimension `d`; the action restricts to `Z`, and every restricted action has orbit dimension `d` at every point | proved (`orbitStratumActionRestriction`, module `OrbitStratumActionRestrictionProof`, helpers prefixed `OrbitStratumActionRestriction.`; published for Task 5217; proof Task 5435 `50f16a97-abde-4fa4-82d0-f13ffe281ff4`, closed) |
| Ex 5.5 (Task 5217) | `UnipotentOrbitStabilizerSmoothStatement` | field `k` of characteristic zero; `G` affine, locally of finite type and unipotent; `Z` reduced, locally of finite type, with a `G`-action of constant orbit dimension `d`; the stabilizer scheme is smooth over `Z`, which is stronger than the flatness in the source (route through Cartier's theorem instead of Conrad's `exp(ker B)`) | proved (`unipotentOrbitStabilizerSmooth`, module `UnipotentOrbitStabilizerSmoothProof`, candidate `798d3ed4-1863-4029-97a9-bd40aa28a360`, Task 5434 `0e823d86-9f22-48da-b160-eebc1c0160a0`, Worker 5434) at the final-publication audit commit. The exact target is obtained from the published reduction, `Langlands.GroupScheme.reducedBaseConnectedFibreSmooth` and `Langlands.GroupScheme.charZeroUnipotentConnected`, with every hypothesis in this row retained |
| Ex 5.5 (Task 5434) | `Langlands.GroupScheme.ReducedBaseConnectedFibreSmoothStatement` (module `Langlands/GroupScheme/ReducedBaseSmoothStatement`) | SGA 3, Exposé VI_B, Corollaire 4.4, over a reduced base with connected fibres: `S` reduced and locally Noetherian; a group scheme `H` over `S`, locally of finite type, whose fibres over the residue fields are smooth and connected, with fibre dimension locally constant on `S`; then `H → S` is smooth | proved (`Langlands.GroupScheme.reducedBaseConnectedFibreSmooth`, module `Langlands/GroupScheme/ReducedBaseSmoothProof`, with `ReducedBaseSmooth/` helpers; published candidate `1d0df2b8-d657-4d37-8a3e-608f9c6006b9` for Task 5706 `0804c1fb-2875-4d0a-90cd-e85198e6e762`, by Workers 50 and 9, at the induction, Schmidt and reduced-base audit commit). Reviewer 321 and exact-target validation establish acceptance; integration `a765b72f4a85465c80fa8c1c12316735` establishes publication. The proof retains every hypothesis in this row |
| Ex 5.5 (Task 5434) | `Langlands.GroupScheme.CharZeroUnipotentConnectedStatement` (module `Langlands/GroupScheme/Unipotent/CharZeroConnectedStatement`) | Milne, *Algebraic Groups* (2022), Corollary 14.15, in characteristic zero: an affine group scheme locally of finite type over a field of characteristic zero that is unipotent (every nonzero finite-dimensional representation has a nonzero fixed vector) has connected underlying space | proved by the proof-producing `def` `Langlands.GroupScheme.charZeroUnipotentConnected` (module `Langlands/GroupScheme/Unipotent/CharZeroConnectedProof`, with `CharZeroCoordinateConnected`, `CharZeroIdempotents` and `CharZeroPeriodic` in the same folder), whose type is the statement unfolded; published for Task 5434 as a supporting definition, by a route through Cartier's theorem and idempotents of the coordinate ring rather than Milne's component-group argument |
| Ex 5.5 (Task 5434) | `unipotentOrbitStabilizerSmooth_of_reducedBase_of_charZeroConnected` (`UnipotentOrbitStabilizerSmoothReduction`) | the two statements above as hypotheses, in the same universe; conclusion: `UnipotentOrbitStabilizerSmoothStatement` | proved by this proof-producing `def` (published for Task 5434 as a supporting definition); both premises have published proofs, namely `Langlands.GroupScheme.reducedBaseConnectedFibreSmooth` and `Langlands.GroupScheme.charZeroUnipotentConnected`. Their composition now gives the published exact-target theorem `unipotentOrbitStabilizerSmooth` named above |
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
| Prop 5.8 (Task 5253) | `AdelicSpaceProperModelStatement` (curve and number-field forms; same module); the conjunction `AdelicSpaceProperInputsStatement` | the data of `AdelicSpaceSpreadProperMapStatement`: separated finite-type models over independent finite sets (nonempty, and finite `k`, for curves) of spaces `Y`, `W` and a proper morphism `g : Y → W`; conclusion: a finite set `T` (nonempty for curves), separated finite-type models over the `T`-integers and a proper model morphism compatible with `g` through generic-fibre isomorphisms | proved (`adelicSpaceProperModel`, module `Langlands/Global/AdelicSpaceProperModelProof`: `AdelicSpaceProperModelReduction.adelicSpaceProperModel_of_descent spaceLimitMorphismDescent (spaceLimitPropertyDescent).2.2.1`; Task 5358 `b69c88f1-1a0b-41b1-a7ab-e5566c81799a`, executors Workers 129 and 157, not closed when inspected); the conjunction has no separate task and no theorem of its own type, and both of its conjuncts are proved (`adelicSpaceProperStages`, `adelicSpaceProperModel`) |
| Prop 5.8 (Task 5253) | `AdelicSpaceProperModelReduction.adelicSpaceProperModel_of_descent` (`AdelicSpaceProperModelReduction`) | `SpaceLimitMorphismDescent` (Thm 3.4(1) for spaces) and `SpaceLimitPropertyDescends (fun f => IsProperMorphism f)` (the properness conjunct of `SpaceLimitPropertyDescentStatement`, Task 5278) as hypotheses, in the same universe; conclusion: `AdelicSpaceProperModelStatement`, both forms, with all its hypotheses | proved (conditional on the two descent inputs, both of which are proved: `SpaceLimitMorphismDescent` by `spaceLimitMorphismDescent`, and the properness conjunct by `(spaceLimitPropertyDescent).2.2.1`; `adelicSpaceProperModel` applies the reduction to these two terms) |
| Prop 5.8 (Task 5253) | `ProperSchemeBaseChangeStatement` (`AlgebraicSpace/`) | Stacks Project, *Morphisms of Algebraic Spaces*, Lemma 40.3 (Tag 04WP), for a change of base scheme: arbitrary schemes `S`, `T` and `g : T → S`; algebraic spaces `X`, `Y` over `S`; for `f : X → Y` proper, `baseChangeMap g f` is proper | proved (`properSchemeBaseChange`, module `ProperSchemeBaseChangeProof`; published for `358c8595-c259-43c3-9e07-08aea99faf88`; proof Task 5498 `c25f29a7-c26d-447f-9fdc-dd9c92f59204`, closed): it is the Library theorem `IsProperMorphism.baseChangeMap` (module `TopologicalMorphismBaseChange`), which holds for every `g` and every proper `f`, without representability |
| Prop 5.8 (Task 5253) | `curvePlaceSpaceStage_isProperMap_of_proper`, `numberFieldSpaceStage_isProperMap_of_proper`, with level and factor forms and the bundled maps `curvePlaceSpaceStageProperMap`, `numberFieldSpaceStageProperMap` (`AdelicSpaceStageProperReduction`) | `LocalFieldProperPointMapStatement` (Cor 5.6) and `ProperSchemeBaseChangeStatement` as hypotheses; `X`, `Y` separated and of finite type over the `S`-integers, `f : X → Y` proper; curves need finite `k` and nonempty `S`; number fields allow every finite set of finite places; for every finite level `T` above `S`, `f` is proper on `T`-stage points for the stage topologies: the properness half of `AdelicSpaceProperStagesStatement` | proved (conditional on the two inputs, both proved: `localFieldProperPointMap` and `properSchemeBaseChange`) |
| Prop 5.8 (Task 5253) | `curvePlaceSpaceStagePreimage_of_valuative`, `numberFieldSpaceStagePreimage_of_valuative` (`AdelicSpaceStagePreimageReduction`) | `SpaceValuativeExistenceStatement` as a hypothesis; `X` separated and of finite type over the `S`-integers, `Y` any algebraic space over them, `f : X → Y` whose base change to the `T`-integers is proper (a hypothesis); curves need finite `k` and nonempty `S`; number fields allow every finite set of finite places; in the adelic points of `X`, the preimage under `f` of the `T`-stage range of `Y` is the `T`-stage range of `X`: the preimage half of `AdelicSpaceProperStagesStatement` at the level `T` | proved (conditional on the valuative criterion, which `spaceValuativeExistence` proves, and on properness after base change) |
| Prop 5.8 (Task 5253) | `curvePlaceSpaceFullLevelPreimage_of_valuative`, `numberFieldSpaceFullLevelPreimage_of_valuative` (`AdelicSpaceFullPreimageReduction`) | `SpaceValuativeExistenceStatement` as a hypothesis; `X` separated and of finite type over the `S`-integers, `Y` any algebraic space over them, `f : X → Y` proper; curves need finite `k` and nonempty `S`; number fields allow every finite set of finite places; in the adelic points of `X`, the preimage under `f` of the image of the `S`-level points of `Y` is the image of the `S`-level points of `X`. This is the preimage clause of `AdelicSpaceProperStagesStatement` with the level ring at `S` (`curvePlaceAdeleLevel`, `numberFieldAdeleLevel`) in place of the stage rings at the levels `T`; properness on level points is not derived | proved (conditional on the valuative criterion, which `spaceValuativeExistence` proves; no Library theorem combines the two) |
| Prop 5.8 (Task 5253) | `AdelicSpaceProperStagesReductionStatement`, `adelicSpaceProperStagesReduction`, with the components `adelicSpaceProperStages_of_inputs`, `curvePlaceSpaceProperStages_of_inputs`, `numberFieldSpaceProperStages_of_inputs` (`AdelicSpaceProperStagesReduction`) | `LocalFieldProperPointMapStatement` (Cor 5.6, Task 5216), `SpaceValuativeExistenceStatement` (Task 5368) and `ProperSchemeBaseChangeStatement` as hypotheses, all in the same universe; conclusion: `AdelicSpaceProperStagesStatement` in both characteristics, with all its hypotheses; the proof pairs the two stage rows above, obtaining properness of the base-changed model morphism from `ProperSchemeBaseChangeStatement` | proved (conditional on the three inputs, all proved: `localFieldProperPointMap`, `spaceValuativeExistence` and `properSchemeBaseChange`; `adelicSpaceProperStages` applies `adelicSpaceProperStages_of_inputs` to the first two and to `IsProperMorphism.baseChangeMap`) |
| Prop 5.8 (Task 5253) | `adelicSpaceSpreadProperMap_of_inputs`, `adelicSpaceSpreadProperMap_of_arithmeticInputs`, `adelicSpaceSpreadProperMap_of_properModel`, `adelicSpaceSpreadProperMap` (`Langlands/Global/AdelicSpaceSpreadProperMapProof`) | successive implications from the topology and proper-input packages, from the proper-stage and proper-model packages, and from the proper-model package alone to `AdelicSpaceSpreadProperMapStatement.{u}`; the last theorem has no extra premise. The conclusion keeps arbitrary independent separated finite-type models, finite constants and nonempty inverted-place sets for function fields, and all infinite factors and possibly empty finite-place sets for number fields | proved at the 13 November audit commit. Proper stage maps with exact stage inverse images give closedness and compact fibres for the full map; model replacement and topology independence transport this to the two original models. The final theorem discharges every input by the published proofs |
| Thm 5.9 (Task 5254) | `CompleteFieldSmoothSpacePointOpenStatement` (`CompleteFieldSmoothPointOpenStatement` in `AlgebraicSpace/`) | complete nontrivially normed `K` of any characteristic, archimedean or not; `f : X → Y` smooth (`IsSmoothMorphism`, defined by étale chart squares) between separated algebraic spaces locally of finite type over `K`; `f` is open on `K`-points for `etaleChartTopology` | proved (`completeFieldSmoothSpacePointOpen`, module `CompleteFieldSmoothPointOpenProof`; Task 5359) |
| Thm 5.9 (Task 5254) | `curvePlaceSpaceLevel_isOpenMap_of_smooth`, `curvePlaceSpaceStage_isOpenMap_of_smooth`, `numberFieldSpaceLevel_isOpenMap_of_smooth`, `numberFieldSpaceStage_isOpenMap_of_smooth`, with factor forms (`AdelicSpaceSmoothLocalOpenReduction`) | `CompleteFieldSmoothSpacePointOpenStatement` as a hypothesis; separated finite-type models over the `S`-integers and a smooth model map `f`, with surjective point maps at all but finitely many factors; curves need finite `k` and nonempty `S`; `f` is open on level points and on the points of every larger stage | proved (conditional on the local input, which the row above proves, and the cofinite surjectivity) |
| Thm 5.9 (Task 5254) | `curvePlaceSpaceFactor_eventually_surjective_of_residue_bound`, `numberFieldSpaceFactor_eventually_surjective_of_residue_bound` (`AdelicSpaceResidueComponentSurjectivity`) | algebraic spaces `X`, `Y` over the `S`-integers and `f : X → Y` smooth (`IsSmoothMorphism`); curves need finite `k`; a natural number `d` and a constant `c ≥ 0` with `\|#f⁻¹(x)(κ_v) − q_v^d\| ≤ c·q_v^(d−1/2)` for every place `v ∉ S` (finite places for number fields), where `κ_v` is the residue field with `q_v` elements, and every `κ_v`-point `x` of `Y`; `f` is surjective on points at all but finitely many factors of the level ring, which is the cofinite surjectivity hypothesis of the row above | proved (conditional on the residue estimate) |
| Thm 5.9 (Task 5254) | `curvePlaceSpaceFactor_eventually_surjective_of_uniformLangWeil`, `numberFieldSpaceFactor_eventually_surjective_of_uniformLangWeil`, `curvePlaceSpaceLevel_isOpenMap_of_uniformLangWeil`, `numberFieldSpaceLevel_isOpenMap_of_uniformLangWeil`, with the point lifts `curvePlaceSpacePointLifts_of_uniformLangWeil`, `numberFieldSpacePointLifts_of_uniformLangWeil` (`Langlands/Global/AdelicSpaceUniformModelOpen`) | `SpaceUniformLangWeilStatement` as a hypothesis; the `S`-integers an algebra over `ULift ℤ` with `Spec` map locally of finite type; `Y` quasi-separated (separated for the open-map forms) and of finite type over the `S`-integers, `X` separated and of finite type for the open-map forms; `f : X → Y` separated, quasi-compact, surjective, with geometrically connected fibres, and an étale chart square (`EtaleMorphismChart`) with surjective source chart whose scheme map is smooth of relative dimension `d`; curves need finite `k`, and nonempty `S` for the open-map form; conclusions: `f` is surjective on points at all but finitely many factors of the level ring, and open on level points | proved (conditional on `SpaceUniformLangWeilStatement`) |
| Thm 5.9 (Task 5254) | `curvePlaceCofinalSpaceLevel_isOpenMap_of_uniformLangWeil`, `numberFieldCofinalSpaceLevel_isOpenMap_of_uniformLangWeil`, with the point lifts `curvePlaceCofinalSpacePointLifts_of_uniformLangWeil`, `numberFieldCofinalSpacePointLifts_of_uniformLangWeil` (`Langlands/Global/AdelicSpaceCofinalModelOpen`, Worker 109) | the row above at the level `curvePlacePrincipalLevelAbove k F S`, resp. `numberFieldPrincipalLevelAbove K S` (a finite set of places containing the given `S`), with the integer-base premise discharged by `AdelicSpaceIntegerBase`; models given over that level; `SpaceUniformLangWeilStatement` and the other hypotheses of the row above; curves need finite `k`, and nonempty `S` for the open-map form; conclusions: lifts of points at all but finitely many factors of the level ring, and openness on level points | proved (conditional on `SpaceUniformLangWeilStatement`) |
| Thm 5.9 (Task 5254) | `SmoothDimensionUniformLifts.exists_uniform_field_surjectivity`, `SmoothDimensionUniformLifts.exists_uniform_henselian_surjectivity`, with the point lifts `SmoothDimensionUniformLifts.pointLifts` (`AlgebraicSpace/SmoothDimensionUniformLifts`, Worker 109) | `SpaceUniformLangWeilStatement` as a hypothesis; a Noetherian ring `C`, an algebra over `ULift ℤ` with `Spec` map locally of finite type; `X`, `Y` separated algebraic spaces of finite type over `C` (`FiniteTypeOverRing`); `f : X → Y` smooth (`IsSmoothMorphism`) with geometrically connected, hence nonempty, fibres (`HasGeometricallyConnectedFibres`); no fixed relative dimension and no étale chart are assumed; conclusions: one constant `c > 0` such that `f` is surjective on `κ`-points for every finite field `κ` with a `C`-algebra structure and `c² < #κ`, and surjective on `R`-points for every henselian local `C`-algebra `R` with a surjective `C`-algebra map onto such a `κ`; `pointLifts` chooses the lifts | proved (conditional on `SpaceUniformLangWeilStatement`) |
| Thm 5.9 (Task 5254) | `curvePlaceSmoothConnectedFactor_eventually_surjective`, `numberFieldSmoothConnectedFactor_eventually_surjective`, `curvePlaceSmoothConnectedLevel_isOpenMap`, `numberFieldSmoothConnectedLevel_isOpenMap`, with the point lifts `curvePlaceSmoothConnectedPointLifts`, `numberFieldSmoothConnectedPointLifts` (`Langlands/Global/AdelicSpaceSmoothConnectedModelOpen`, Worker 109) | `SpaceUniformLangWeilStatement` as a hypothesis; the `S`-integers an algebra over `ULift ℤ` with `Spec` map locally of finite type; `X`, `Y` separated algebraic spaces of finite type over the `S`-integers (`FiniteTypeOverRing`); `f : X → Y` smooth (`IsSmoothMorphism`) with geometrically connected, hence nonempty, fibres (`HasGeometricallyConnectedFibres`); no fixed relative dimension, étale chart or surjectivity is assumed; curves need finite `k`, and nonempty `S` for the open-map form; conclusions: `f` is surjective on points at all but finitely many factors of the level ring, and open on level points | proved (conditional on `SpaceUniformLangWeilStatement`) |
| Thm 5.9 (Task 5254) | `curvePlaceSmoothConnectedAdele_isOpenMap`, `numberFieldSmoothConnectedAdele_isOpenMap`, with `curvePlaceSmoothConnectedPrincipalStage_isOpenMap`, `numberFieldSmoothConnectedPrincipalStage_isOpenMap`, `curvePlaceSpacePrincipalStage_cover`, `numberFieldSpacePrincipalStage_cover` and the topological lemma `AdelicSpaceOpenReduction.isOpenMap_of_continuous_cover` (`Langlands/Global/AdelicSpaceSmoothConnectedAdelicOpen`, Worker 109) | `SpaceUniformLangWeilStatement` as a hypothesis; `X`, `Y` separated algebraic spaces of finite type over the `S`-integers; `f : X → Y` smooth with geometrically connected fibres, of any relative dimension; no integer-base premise on the `S`-integers; curves need finite `k` and nonempty `S`; number fields allow every finite set of finite places; conclusion: `f` is open on the adelic points of the models (`curvePlaceSpaceAdelePointTopology`, `numberFieldSpaceAdelePointTopology`, module `AdelicSpacePointTopology`); the proof applies the level-openness row above at the principal stages above each stage, which cover the adelic points | proved (conditional on `SpaceUniformLangWeilStatement`); this is openness for a map of models, not `AdelicSpaceSpreadSmoothOpenStatement` |
| Thm 5.9 (Task 5254) | `AdelicSpaceSpreadSmoothOpenOfLangWeilStatement`, `adelicSpaceSpreadSmoothOpen_of_langWeil` (`Langlands/Global/AdelicSpaceSmoothConnectedSpreadOpen`) | exactly `SpaceUniformLangWeilStatement.{u} → AdelicSpaceSpreadSmoothOpenStatement.{u}`; independent separated finite-type source and target models and their original spread topologies, possibly at different levels; no fixed relative dimension; both global-field characteristics, with finite constants and nonempty levels for function fields and every infinite factor for number fields | proved at the earlier 13 November audit commit, conditional only on the exact space Lang–Weil statement. Smooth connected model descent, model adelic openness, natural spread homeomorphisms and topology independence supply the arbitrary-model assembly. The published `adelicSpaceSpreadSmoothOpen` now supplies this premise and proves unconditional Theorem 5.9 at the final-publication audit commit |
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
relative dimension equal to that value), `SmoothDimensionFieldPoints` (declarations prefixed
`SmoothTargetPointDimensions.`; a field-valued point of the target factors through exactly one
of these open subspaces, and surjectivity on field points of every restricted map gives
surjectivity on field points of the original map; Worker 109), and
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
  proofs. Task 5202 `e5531847-70bc-4569-b880-2f90d5815c6a` and Task 5217
  `b7321f08-34a4-4479-b6a5-fc099d504d2d` retain their pauses and ownership.
- **Retained analytification.** The [CT] construction in the infinite-extension argument
  on p.19 has its own required rows above. The different proof of Proposition 5.11(3)
  establishes that endpoint, while revision 2 still requires the actual analytification
  input, the rational-point topology comparison and arbitrary analytic field extension.
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

1. Prove the source-level `SmoothSourceAnalyticManifoldStatement` of
   Proposition 5.4 (Task 7051 `685b8c94-5194-4cb7-8b30-4977774ce694`). The other
   six varying-dimension statements are proved, as recorded in the second
   17 November audit: the rational-point dependent-sum homeomorphism (Task 6936
   `7e14e6f5-9447-4b9a-8f26-96906d761802`), analytic assembly, functoriality and
   étale local analytic isomorphisms (Tasks 7025–7027), and affine-space agreement
   and uniqueness (Tasks 7049–7050). The parent published each proof task and does
   not take the proofs. The topological assertion keeps its broader
   henselian/quasi-separated scope, without completeness or local separatedness.
   Neither a fixed-dimension restriction nor a finite-range assumption meets the
   full smooth-space scope.
2. Complete the retained analytification pipeline using Task 6230
   `ad8e3e5e-2e0e-4f05-9924-191590422efd`'s published finite-type affine
   constructions. Twenty-three published analytification statements need proofs,
   each through its own proof task published by the parent. Six earlier
   statements are now proved (second 17 November audit): affine rational points
   (Task 7084 `a12135e5-19d0-4b8d-88d1-cf7f0bf4a946`), functoriality and
   presentation independence (Task 7085 `6545548c-9d0b-4359-a868-8e52fd060af5`),
   the seminorm description (Task 7083 `72a185e1-3828-4881-b54e-77a117168474`),
   naturality (Task 7072 `8a49d73c-1180-41f0-8b5c-03f5bdff1d86`), localized
   functoriality (Task 7119 `711fd0e4-3a70-4bec-99b8-e062dd42ff6a`) and maps from
   affinoid spectra (Task 7167 `ee943114-0baa-4432-9cb9-cef090ce46d0`). The open
   affine and scheme statements are immersions on underlying spaces (Task 7086
   `15296f18-5435-4142-bd49-fdaf726f1890`), scheme gluing (Task 7087
   `d8f36429-3ce4-491e-9d69-e57ed9b29c76`), the center maps (Task 7097
   `b92d9284-a406-49b1-af51-96979d7e0e5c`), scheme rational points (Task 7098
   `b0baa8b3-a86f-4e40-91d6-2f1b4c947be0`), the ground-field extension map
   (Task 7099 `424733ee-4a23-47ac-b5b1-1b6dd83190b7`), scheme morphisms (Task 7118
   `8074ec5b-c845-4d65-8cc4-6a5be50d7a84`), the analytic structure of the glued
   space (Task 7120 `032e0d8b-d716-44e2-ab5e-08385567bb55`), affine fibre
   products (Task 7168 `46196b21-c6e5-4dd5-be9c-8f78a02733a5`) and affine étale
   maps (Task 7169 `cd8fa5b0-d6a1-4c30-9d2a-046c2b5fffa1`). Their open
   prerequisite statements are the norm extension to finitely generated domains
   (Task 7628 `3370013d-0145-4a35-b24b-4cdf01cdbc0d`, for the center maps) and,
   for the étale maps, quasi-finiteness (Task 7653
   `9fb378cf-c57b-465b-bd06-c422a8ab8500`), the finite-germ comparison (Task 7655
   `6f1f9bc0-d74b-4295-81e0-ccba71f22745`) and chart flatness (Task 7657
   `f5b29461-c4fc-44cd-8212-aacffc08f5e1`). The algebraic-space
   statements are existence (Task 7245 `90ee99f4-d134-4910-8621-d8e186bfea8f`),
   morphisms (Task 7246 `27620dd4-0641-4080-98cc-23e6dbc17f21`), rational points
   (Task 7247 `6145952e-407a-4855-8def-a8263bedfbf7`), étale maps (Task 7248
   `b20171a8-9554-4f51-b56f-227e66409b5b`), fibre products (Task 7249
   `f65ed7bd-6eb8-46fe-a279-b68de84862b7`), the scheme case (Task 7250
   `63c57e1a-a624-4048-914e-dbe4f869dc25`) and immersions of underlying spaces
   (Task 7251 `6aae2ba3-a5e5-4ca2-8e1e-209363dee704`). Analytic immersions are
   stated for affine schemes (Task 7299 `b71751b5-5608-4451-b3f0-9a02e0ff976a`)
   and for algebraic spaces (Task 7300 `7392723a-c591-4e5e-ac51-bb0bcc559ebf`).
   `K`-valued points of the analytification of an algebraic space are stated
   (Task 7486 `74ee4c92-ea0c-4002-aefc-1da4675e9deb`).
   The dated audits above give each statement's first publication commit.
   The parent counts a published proof of the existence statement (Task 7245) as
   the construction of the analytification of a separated algebraic space locally
   of finite type. By the morphism statement, `IsAnalytification` determines it up
   to unique compatible isomorphism; no explicit quotient `Uᵃⁿ/Rᵃⁿ` of an étale
   chart is constructed. The parent still has to construct and state the
   analytic ground-field extension and the canonical isomorphism
   `(Xᵃⁿ)_L ≅ (X_L)ᵃⁿ` for arbitrary complete nonarchimedean extensions, with
   naturality, towers and fibre products. Task 7100
   `7b5d3807-3a12-4dac-ae8a-a7f93d7fc2b8`, published by the parent, constructs
   the ground-field extension of presented affinoid algebras and affinoid atlases.
   Its algebra-level construction is in the Library (scalar-extension row); its
   atlas-level and space-level constructions are not. The parent retains this construction
   and its statement interfaces; the proofs belong
   to the proof tasks. The existing extension-point endpoint proof does not
   discharge them.
3. Obtain a fresh independent whole-paper coverage review after verifying every
   retained mathematical publication and comparison. The earlier accepted
   focused notes and the present publication update do not certify whole-paper
   completion. Task 0 priority and the explicit pauses of Task 5202
   `e5531847-70bc-4569-b880-2f90d5815c6a` and Task 5217
   `b7321f08-34a4-4479-b6a5-fc099d504d2d` remain in force.

The exact unconditional Theorem 4.5 is now proved and published by
`Langlands.Global.adelicSpreadSmoothOpen`, with the evidence in the
14 November audit; its earlier publication obligation is discharged.

The published exact scheme and space Lang–Weil estimates, unconditional
Theorem 5.9, all three corrected Example 5.5 clauses, Proposition 5.8 and the
general corrected Corollary 5.7 closedness theorem remain proved with the
hypotheses and publication evidence given above. No extra conjunction theorem
is required for Example 5.5. The literal Proposition 5.11(1),
`HenselianWeilRestrictionPointHomeomorphStatement`, remains a known false
historical interface. Its proved module-topology replacement and the explicit
obstruction meet the revised scope; proving the false literal statement is not
an obligation.

Unused alternative reductions remain visible in their rows:
`CompleteFiniteExtensionPointEmbeddingStatement` has no proof task;
`SpaceValuativeExtensionExistenceStatement` and
`SpaceValuativeExtensionDescentStatement` have Tasks 5519 and 5520. Their
endpoints are proved by other routes, so no required source conclusion depends
on those alternatives. The conjunction `AdelicSpaceProperInputsStatement` has
no proof task of its own; its two inputs are proved. Current statuses in this
section supersede the open-task descriptions in the preserved historical
audits, without changing their evidence or the hypotheses of existing rows.

Other Library statements cite this paper only for the topology on rational points, inside
other programs (for example the `Langlands.Representation.Aubert.General` prerequisites); they
are not assertions of the paper and are not listed.

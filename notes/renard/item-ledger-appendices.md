# Renard 2026, Appendices A–C: item-by-item coverage ledger

Worker 1222, executor of the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`, revision 1. This note is the appendix part of the
item ledger that the task contract requires, in the format of the chapter ledgers
([Chapter III](item-ledger-iii.md), [IV](item-ledger-iv.md), [V](item-ledger-v.md),
[VI](item-ledger-vi.md), [VII](item-ledger-vii.md)). It lists the headed items of
Appendices A, B and C and the main unheaded assertions, with printed / PDF pages
(PDF = printed + 6), the Lean declarations and their proof status at Library commit
`a54dda0d7c7c0fd4f76308fad8525ba13d9b4ce8`. A published statement is not a proof; every row
keeps the proof status explicit.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Appendix A is printed
pp.247–269 / PDF pp.253–275, Appendix B pp.271–273 / PDF pp.277–279, Appendix C
pp.275–280 / PDF pp.281–286.

## How the rows were checked

The appendices have detailed published source maps, written mostly by Worker 709 under
earlier revisions of this task. Each map gives, passage by passage, the Mathlib declaration
or the Library statement and proof that covers it. Worker 1222 read every headed item of the
appendices in the text extraction and located it in these maps. Worker 1222 also collected
the statement names that the maps cite, resolved them to Library declarations, and scanned
the Library for theorems whose type is exactly each statement. All 139 resolved statements
have such a proof at `a54dda0d`. The rows below therefore name the maps and their principal
declarations rather than repeat them; the maps list every component and proof receipt.

Status codes are those of the chapter ledgers: **P** proved; **S** statement with an open
proof task; **D** definition or construction; **C** covered by Mathlib or by stronger or
equivalent published results (documented correspondence); **St** proof step; **X**
expository; **Rec** recalled from the literature; **G** gap. Names without a namespace are in
`Langlands.Renard`.

## Appendix A: Elements of category theory

| Item | Pages | Lean and map | Status |
| --- | --- | --- | --- |
| A.I opening: objects, morphisms, functors; foundations used naively | 247 / 253 | Mathlib's `Category`, `Functor` ([elementary map](elementary-categories-source-map.md)) | C; X (foundations) |
| A.I.1 isomorphisms, monomorphisms, epimorphisms; isomorphisms are mono and epi; the converse fails in general and holds in abelian categories | 247–248 / 253–254 | Mathlib's `Iso`, `IsIso`, `Mono`, `Epi`, `IsIso.epi_of_iso`; a thin-category counterexample in the elementary map; `IsoIffMonoAndEpiStatement` | C; P (the abelian converse) |
| A.I.2 subobjects and quotients, their orders, intersections and unions, conditional uniqueness, existence conventions | 248 / 254 | Mathlib's `Subobject`; `IsGLB`, `IsLUB` (elementary and [duality](category-constructions-source-map.md) maps) | C |
| A.I.3 Noetherian and finite-type objects, the chain criterion, the finite-subcover characterization, subobjects of Noetherian objects, the converse, Noetherian categories, the module example | 248–249 / 254–255 | `IsNoetherianObject`, `IsFiniteTypeObject`, `HasFiniteSubcoverProperty`, `IsNoetherianCategory`; `NoetherianCriteriaStatement`, `FiniteTypeFiniteSubcoverStatement`, `NoetherianSubobjectFiniteTypeStatement`, the all-subobjects equivalence, `ModuleFiniteType.ModuleFiniteTypeStatement`, `ModuleNoetherian.ModuleNoetherianStatement` ([A.I.3 map](noetherian-finite-type-progress.md)) | D; P |
| A.I.4 initial, final and zero objects, their uniqueness; zero morphisms; kernels and cokernels | 249 / 255 | Mathlib's `IsInitial`, `IsTerminal`, `IsZero`, zero morphisms, `KernelFork`, `CokernelCofork` (elementary and duality maps) | C |
| A.I.5 product and opposite categories; contravariant functors through opposites; the four duality pairs | 250 / 256 | Mathlib's product and opposite categories and the duality correspondences of the [duality map](category-constructions-source-map.md) | C; X (the general duality principle) |
| A.II.1 natural transformations, the functor category, natural isomorphisms, the identity functor | 250 / 256 | Mathlib's `NatTrans`, functor category, `Iso` of functors (duality map) | C |
| A.II.2 Definition: equivalence and quasi-inverse | 251 / 257 | Mathlib's `Equivalence`; the subscripts of the printed definition are interchanged (source issue S1) | C |
| A.II.2 representative full subcategory; the example `Vect^n_k`; non-uniqueness of the quasi-inverse | 250–251 / 256–257 | the representative-subcategory and fixed-dimension equivalences of the [A.II.2 map](appendix-a-equivalence-progress.md) | P; X (non-uniqueness, choice) |
| A.II.2 full, faithful, fully faithful functors; full subcategories | 251 / 257 | Mathlib's `Functor.Full`, `Functor.Faithful`, `ObjectProperty.FullSubcategory` (elementary map) | C |
| A.II.2 Theorem: fully faithful and essentially surjective implies equivalence | 251 / 257 | `EquivalenceCriterionStatement` (A.II.2 map) | P |
| A.III.1 Definition and Remark: universal problems, uniqueness of solutions | 251–252 / 257–258 | `UniversalArrow.UniversalArrowStatements` ([A.III map](universal-representability-progress.md)) | P |
| A.III.1 Examples 1–5: coproducts and products, completion, localization of rings and of modules, polynomial modules and endomorphisms | 252 / 258 | `BinaryDiagonal`, `UniformCompletion`, `TopModuleCompletion.UniversalStatements`, `RealSequenceCompletion.CompletionCounterexampleStatements`, `RingLocalization.CategoricalUniversalStatements`, `ModuleLocalization.CategoricalUniversalStatements`, `AlgebraActionLocalization.universalPropertyStatements` and the example 5 packaging (A.III map; [endomorphism-localization map](endomorphism-localization.md)) | P. Source issues S2 (example 2) and S3 (example 4) |
| A.III.1 Lemma and Corollary on the localization `L_a` of a vector space by an endomorphism | 253 / 259 | the endomorphism-localization proofs of the [endomorphism-localization map](endomorphism-localization.md) | P |
| A.III.2 representable functors; Theorem (Yoneda); Remark; Corollary | 253–255 / 259–261 | `Yoneda.YonedaStatements`, `RepresentabilityUniversal.RepresentabilityUniversalStatements` (A.III map) | P |
| A.III.3 Proposition: an isomorphism principle | 255 / 261 | `IsomorphismPrinciple.IsomorphismPrincipleStatements` (A.III map); the printed Hom subscripts are read in `M` | P |
| A.IV.1 limits: the diagonal, cones, the universal property, the Remark (universal problem), uniqueness; Examples 1–6 | 255–257 / 261–263 | `ElementaryLimitColimit.ElementaryLimitColimitStatements`, `OrderedSystemLimit.OrderedSystemLimitStatements`, `SubobjectLimit.SubobjectLimitStatements`, `LimitUniversalArrow.LimitUniversalArrowStatements` ([A.IV map](limits-colimits-progress.md)) | P. Source issue S4 |
| A.IV.2 colimits, their duals of the examples, direct systems; the abelian-group example (products, direct sums, finite support); filtered colimits of abelian groups and eventual vanishing | 257–258 / 263–264 | `AbelianGroupLimit.AbelianGroupLimitStatements`, `FilteredColimit.FilteredColimitStatements` and its proved components (A.IV map) | P |
| A.V.1 Definition (adjunction by natural Hom bijections); Theorem (existence of a right adjoint iff representability); Corollary (uniqueness) | 258–259 / 264–265 | `HomAdjunctionComparison`, `AdjointRepresentability.RightAdjointRepresentabilityStatement`, `RightAdjointUniquenessStatement`, `LeftAdjointUniquenessStatement` ([A.V map](adjunctions-progress.md)) | P |
| A.V.2 unit and counit; Theorem (triangle identities and the converse construction); preservation of limits and colimits; Example (extension of scalars) | 259–261 / 265–267 | `UnitCounit` statements, `AdjunctionPreservation`, `UnitalScalarExtensionAdjunction.ScalarExtensionAdjunctionStatements` (A.V map) | P |
| A.VI.1 the axioms of abelian categories; examples: `A-mod`, `M(A)`, sheaves and presheaves of abelian groups; full subcategories closed under subobjects and quotients | 261 / 267 | the seven-axiom predicates and their equivalence with Mathlib's `Abelian`; `NonUnitalModuleAmbientAbelianStatement`, `NondegenerateModuleAbelianStatement`, `BasisSheafAbelianStatement`, the corrected subcategory criteria and the dimension-at-most-one counterexample ([A.VI.1–2 map](abelian-categories-progress.md)) | D; P. Source issue S5 |
| A.VI.2 properties (1)–(10) of abelian categories | 262–263 / 268–269 | `AbelianImageCoimageStatement`, `EpiMonoFactorizationStatement`, `IsoIffMonoAndEpiStatement`, `NoetherIsomorphismsStatement`, `ProductCoproductNaturalIsoStatement`, `SourceCompletenessLimitsStatement`, `SubobjectQuotientAndLatticeStatement`, `RenardThreeByThreeBottomRowStatement` (A.VI.1–2 map) | P |
| A.VI.3 Jordan–Hölder series and composition factors; length; Examples (AB5, AB6 for module categories); Proposition (simple quotients and subquotients); Lemma (simple subquotient identities) | 263–264 / 269–270 | `JordanHolderStatement`, `SimpleQuotientPropositionStatement`, `SimpleSubquotientIdentitiesStatement` and components, `RenardFullModuleAxiomStatements`, `NondegenerateModuleAB5Statements`, `NondegenerateModuleLocallyFiniteTypeStatements` ([A.VI.3 map](jordan-holder-progress.md)) | P |
| A.VII Lemma (equivalent characterizations of semisimple objects); Corollary (subobjects of semisimple objects) | 264–265 / 270–271 | `SemisimplicityEquivalenceStatement`, `SemisimpleSubobjectStatement` ([A.VII map](semisimplicity-progress.md)) | P |
| A.VIII.1 exact functors; finite limits and colimits; Lemma (exact functors detecting zero are faithful) | 265–266 / 271–272 | `SequenceExact…` statements, `FinitePreservationComparisonStatement`, `ExactnessHomologyComparisonStatement`, `FaithfulnessCriteriaStatement`, `SequenceExactReflectsZeroFaithfulStatement` ([A.VIII.1 map](exact-functors-progress.md)) | P |
| A.VIII.2 Hom functors, projectives, generators, progenerators; Theorem (an abelian cocomplete category with a small progenerator `P` is equivalent, through `Hom(P, •)`, to the unital right modules over `End(P)`); Remark (converse); Lemma (every object is a quotient of sums of copies of `P`) | 266–267 / 272–273 | the [Hom-functor map](hom-functors-progress.md) and the [category/module map](category-module-progress.md), including `SmallProgeneratorEquivalenceStatement` | P |
| A.IX decompositions of categories: the support of an object, Definition (a set of irreducibles splits an object), Lemma | 268 / 274 | `CategoryDecompositionSimpleClassesStatement` and the `SimpleSupport…` statements ([A.IX map](category-decomposition-progress.md)) | P (with the explicit smallness hypotheses recorded there) |
| A.X the centre of a category; Example (the centre of `M(A)` for unital `A`) | 269 / 275 | Mathlib's `CatCenter`; `ModuleCatCenterIdentificationStatement` ([A.X map](category-center-progress.md)) | D; P |

## Appendix B: Amitsur's theorem and corollaries

| Item | Pages | Lean and map | Status |
| --- | --- | --- | --- |
| B.I Definition: spectrum of an element | 271 / 277 | Mathlib's `spectrum` | C |
| B.I Theorem (Amitsur): for a complex algebra of countable dimension, the spectrum is nonempty, and `{0}` exactly for nilpotent elements; a division algebra of countable dimension is `ℂ` | 271–272 / 277–278 | `AmitsurTheoremStatement` ([Appendix B map](appendix-b-progress.md)) | P: `amitsurTheorem` |
| B.II Theorem: for a simple module `M` over a possibly nonunital complex algebra, `End_A(M)` is a division algebra, and `End_A(M) = ℂ` when `M` (or `A`) has countable dimension | 272 / 278 | `NonUnitalSchurStatements` (original actions) and the unital core (Appendix B map) | P: `nonUnitalSchur` |
| B.III Lemma: a non-nilpotent element of a countable-dimensional algebra acts nontrivially on some simple module | 273 / 279 | `NonUnitalSeparationStatement`, `NonUnitalNonnilpotentLeftResolventStatement`, `NonUnitalLeftShiftSimpleQuotientStatement` and the unital versions (Appendix B map) | P |

## Appendix C: Commutative algebra and linear algebra

| Item | Pages | Lean and map | Status |
| --- | --- | --- | --- |
| C.I Lemma: the dimension of a commutative subalgebra of `End(V)` generated by `l` elements is at most `f_l(k)`, and its proof (block reduction, nilpotent maximum, recurrence, numerical contradiction) | 275–276 / 281–282 | `CommutativeEndomorphismDimensionStatement`, `CommutativeSubalgebraDimensionStatement` and the intermediate statements of the [C.I map](commutative-dimension.md) | P: `commutativeEndomorphismDimension`, `commutativeSubalgebraDimension` |
| C.II Definition (stable endomorphisms) and Lemma (characterizations) | 276–277 / 282–283 | `StableEndomorphism.StableEndomorphismStatement` ([C.II map](stable-quotients.md)) | D; P |
| C.II the successive quotient sequences and the finite localization used in the proof | 277–278 / 283–284 | the successive-quotient exactness statements, `EndomorphismLocalization.FiniteActualLocalizationStatement`, `NoetherianActualLocalizationStatement`, `StablePowerImageStatement` (C.II map) | P |
| C.II Proposition: for a Noetherian commutative algebra `B`, a finitely generated `B`-module `L` and `a ∈ End_B(L)` whose localization `L_a` is finitely generated, `a` is eventually stable, `L = ker aⁿ ⊕ im aⁿ` and `L_a ≅ (im aⁿ, a)` | 279 / 285 | `SourceFiniteLocalization.UnitizationReadingStatement`, `CompatibleReadingStatement`, `AdditiveReadingStatement` (three readings of the finiteness hypotheses), with the [unitization criteria](unitization-noetherian-criteria.md) | P (all three readings). Clarification C1 |
| C.III Proposition: a matrix coefficient `n ↦ λ(U(n) v)` of a finite-dimensional representation of `ℤ^d` is `Σ_j χ_j(n) Q_j(n)` with characters `χ_j` and polynomials `Q_j` | 279–280 / 285–286 | `IntegerLatticeMatrixCoefficientExponentialPolynomialStatement`, `CommutingTupleMatrixCoefficientExponentialPolynomialStatement`, `RenardCIIIOccurringCharactersStatement` and the decomposition, binomial and basis statements of the [C.III map](integer-lattice-coefficients.md) | P |

## Source issues and clarifications

- **S1 (A.II.2, Definition).** The printed natural isomorphisms `FG ≅ Id_A`, `GF ≅ Id_B` have
  their subscripts interchanged; for `F : A → B` and `G : B → A` one needs `GF ≅ Id_A` and
  `FG ≅ Id_B`. The [A.II.2 map](appendix-a-equivalence-progress.md) records the correction.
- **S2 (A.III.1, example 2).** With all continuous maps as morphisms, the usual completion
  arrow does not solve the printed universal problem for a real space; the published
  fixed-real counterexample `RealSequenceCompletion.CompletionCounterexampleStatements` shows
  this. The uniform and continuous-linear versions are proved
  ([A.III map](universal-representability-progress.md)).
- **S3 (A.III.1, example 4).** The parenthesis "`(ts)m = (st)m = m` for some `t ∈ A`" is
  stronger than invertibility of the action of `s`; `ℤ`, `S = 2^ℕ`, `M = ℚ` is a
  counterexample. The formalization uses invertibility
  ([Appendix A discrepancies](appendix-a-corrections.md)).
- **S4 (A.IV.1–A.IV.2).** Natural transformations between constant functors correspond to
  morphisms only for a connected index category, not merely a nonempty one; several arrow
  directions in the prose are reversed. The cone and cocone formulation avoids both
  (Appendix A discrepancies).
- **S5 (A.VI.1).** A full subcategory of `A-mod` closed under subobjects and quotients need
  not be abelian; closure under finite sums is also needed. The counterexample (vector spaces
  of dimension at most one) and the corrected criteria are published and proved (A.VI.1–2
  map).
- **C1 (C.II, Proposition).** The source does not fix the meaning of "Noetherian" and "de
  type fini" for the possibly nonunital algebras to which the Proposition is applied. The
  Proposition is stated and proved under three readings (unitization, compatible complex,
  original additive). Which reading the source intends is a convention question recorded as
  open in the C.II map and in
  [nonunital-finiteness-sources](nonunital-finiteness-sources.md); each reading is proved.

## Gaps of the appendices

None found. Every headed item and every main assertion located in the maps has a published
statement with an exact proof, or a documented Mathlib correspondence. The maps record further
internal comparisons (for example the exactness of chosen localization models, A.III) and the
source-facing convention question C1; these are not source assertions left unstated.

## Summary

Appendices A, B and C are covered: Mathlib correspondences for the elementary categorical
notions, and published statements with exact proofs for the theorems, lemmas, corollaries
and examples, at Library `a54dda0d`. Five source issues (S1–S5) and one convention
clarification (C1) are recorded above, each with its published treatment.

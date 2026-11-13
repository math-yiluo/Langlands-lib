# Renard 2026, Chapter I: item-by-item coverage ledger

Worker 1222, executor of the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`, revision 1. This note is the Chapter I part of the
item ledger that the task contract requires, in the format of the
[Chapter IV](item-ledger-iv.md), [Chapter V](item-ledger-v.md),
[Chapter VI](item-ledger-vi.md) and [Chapter VII](item-ledger-vii.md) ledgers. It lists
the headed items of Chapter I and the unheaded assertions found in its paragraphs, with
printed / PDF pages (PDF = printed + 6), Lean declarations and proof status at Library
commit `9951a27f5fd8ebbdc4bbe68eb6be65b1d0c2eb4a`; statements published later, at Library
`24a49431a1a304ab4190fc6ef1f7e7d21c2d41be` or `a54dda0d7c7c0fd4f76308fad8525ba13d9b4ce8`, are
marked as such in their rows. The note declares no section complete. A
published statement is not a proof; every row keeps the proof status explicit.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Chapter I is printed
pp.5–28 / PDF pp.11–34.

## How the rows were checked

Worker 1222 read Chapter I in the text extraction, paragraph by paragraph, and listed the
Library Markdown files that cite each section. For each row the declarations named were read
in their Lean file and Markdown. Proof status comes from a scan of the Library for theorems
whose type is exactly the statement (`proved by`). Where a module states several clauses and
proves them through one aggregate theorem, the row names the aggregate. A `task` entry is a
`lean.proof@1` task whose contract names the statement. Detailed source maps by other
workers are cited where they exist: the [initial passage audit](initial-passages.md) for
I.1, the [I.2.1 assertion map](unitization-tensor-progress.md) and the dated coverage updates
([9 November](coverage-update-2026-11-09.md), [10 November](coverage-update-2026-11-10.md),
[11 November](coverage-update-2026-11-11.md)). The coefficient question of I.4.2 is
documented in [duality-coefficient-conventions](duality-coefficient-conventions.md).

Unless another namespace is written, declarations are in `Langlands.Algebra`, and module
names are under `Langlands/Algebra/`.

Status codes, as in the other ledgers:

- **P**: proved; the named theorem has exactly the statement's type.
- **S**: statement published; a proof task is open.
- **D**: definition or construction (with the laws proved in its module, where stated).
- **C**: covered by published statements that are stronger or equivalent, or derived from
  them; the row says which.
- **St**: a step of the proof of a stated result.
- **X**: expository, convention or attribution.
- **Rec**: an assertion recalled from the literature.
- **A**: candidate accepted by review, waiting for integration.
- **R**: candidate staged, under review.
- **G**: genuine gap.

## Opening and conventions (5–6 / 11–12)

| Item | Lean | Status |
| --- | --- | --- |
| Representations of a finite group `G` are the unital modules over `ℂ[G]` | Mathlib's `Rep.equivalenceModuleMonoidAlgebra` (`Rep k G ≌ ModuleCat k[G]`, any monoid `G`) | Rec; C |
| Smooth representations of a `p`-adic group form a category equivalent to modules over the Hecke algebra; the archimedean analogue for Harish-Chandra modules ([35]) | `p`-adic case: III.1.4, `Langlands.Hecke.heckeNondegenerateModuleEquivalence` (proved); archimedean case: not stated | X (announcement); the archimedean equivalence is outside the book's `p`-adic content and is not stated |
| Conventions: original module actions, bimodules with commuting actions, the algebraic dual `V^*`; `M = e·M ⊕ (1 − e)·M` as abelian groups; `eAe` unital with unit `e`; `e·M` a unital `eAe`-module; `M(A)` for unital `A`; the Remark on the notation `(1 − e)·M` | `NonUnitalModule`, `NonUnitalBimodule`; [NonUnitalModuleCorner](../../Langlands/Algebra/NonUnitalModuleCorner.md) (the decomposition, which is (I.3.1.1), and the unital corner action); `Idempotent.Corner.ring` ([IdempotentedRing](../../Langlands/Algebra/IdempotentedRing.md)); `isNondegenerate_iff_isUnitalModule` for unital `A` | D; X (the Remark) |

## I.1 Rings with idempotents (6–14 / 12–20)

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| I.1.1 order `e ≤ f` iff `eAe ⊂ fAf` | 6 / 12 | `PartialOrder (Idempotent A)` | D |
| I.1.1 Remarks: `eAe` a subalgebra with unit `e`; `eae = a ⇔ a ∈ eAe`; `eAe = eA ∩ Ae` | 6 / 12 | `Idempotent.corner`, `Idempotent.Corner.ring`, `Idempotent.mem_corner`, `Idempotent.mem_corner_iff_left_right_image` | D; P (theorems of [IdempotentedRing](../../Langlands/Algebra/IdempotentedRing.md)) |
| I.1.1 Lemma (i)–(ii) | 6 / 12 | `Idempotent.le_iff_corner_le`, `Idempotent.le_iff_mem_corner`, `Idempotent.le_iff_sandwich`, `Idempotent.le_iff_mul`, `Idempotent.mul_eq_of_le` | P |
| I.1.2 Definition: ring with idempotents | 7 / 13 | `IsIdempotented` | D |
| I.1.2 Lemma: `Idem(A)` is filtering | 7 / 13 | `IsIdempotented.finite_upper_bound` | P |
| I.1.2 `A = ⋃_e eAe` | 7 / 13 | `IsIdempotented.iUnion_corners` | P |
| I.1.2 `A = lim_e eAe` (direct limit along the inclusions, A.IV.2) | 7 / 13 | `IdempotentedRingDirectLimitStatement` (universal property of the inclusions, in abelian groups and in nonunital rings, for every filtering system) | S: Task 5772 (candidate `9158d4aa`, published at Library `24a49431`) |
| I.1.2 Definition: nondegenerate module; equivalently `M = lim_e e·M` | 7 / 13 | `IsNondegenerate`; `NondegenerateModuleDirectLimitStatement` (the direct-limit formulation, in abelian groups) | D; S: Task 5772 (candidate `9158d4aa`, published at Library `24a49431`) |
| I.1.2 Remark 1: a unital ring has idempotents; its unital modules are the nondegenerate ones | 7 / 13 | `IsIdempotented.of_ring`, `isNondegenerate_iff_isUnitalModule` | P |
| I.1.2 Remark 2: for a filtering system `𝒥` of idempotents, fixation by elements of `𝒥` suffices for nondegeneracy, and `A = lim_𝒥 eAe`, `M = lim_𝒥 e·M` | 7 / 13 | the same two statements, with a general filtering system `J` | S: Task 5772 (candidate `9158d4aa`, published at Library `24a49431`) |
| I.1.2 Remark 3: nondegeneracy relative to a system `𝒥` closed under pairwise upper bounds | 7 / 13 | none | X: the remark says that the notion can be generalized and makes no further assertion |
| I.1.2 `M_A`, the largest nondegenerate submodule, `= ⋃_e e·M` | 7 / 13 | `nondegeneratePart`, `mem_nondegeneratePart_iff_exists_smul`, `nondegeneratePart_isNondegenerate`, `le_nondegeneratePart_iff` ([NonUnitalModule](../../Langlands/Algebra/NonUnitalModule.md)) | D; P |
| I.1.2 `M(A)` is a full subcategory stable under submodules and quotients, hence abelian; right modules `M(A)_d` | 7 / 13 | `NondegenerateModuleCat`; `NondegenerateModuleClosureStatement`, `NondegenerateModuleAbelianStatement`; right modules as modules over `Aᵐᵒᵖ` | D; P (`nondegenerateModuleClosureStatement`, `nondegenerateModuleAbelianStatement`) |
| I.1.2 Proposition: `A-mod → M(A)`, `M ↦ M_A`, is exact | 8 / 14 | `NondegeneratePartRangeExactnessStatement` (range = kernel is preserved), `NondegenerateModuleExactnessStatement` (kernels, cokernels and short exact complexes) | P (`nondegeneratePartRangeExactnessStatement`, `nondegenerateModuleExactnessStatement`) |
| I.1.3 `A = A(1 − e) ⊕ Ae`; the topology with basis `A(1 − e)`; left translates; the uniform structure; the pseudometrics `d_e`, filtering, defining the same topology | 8 / 14 | [IdempotentedRingUniformity](../../Langlands/Algebra/IdempotentedRingUniformity.md), [IdempotentedRingPseudometrics](../../Langlands/Algebra/IdempotentedRingPseudometrics.md); `IdempotentedRingTopologyTheorem` (uniform additive group, separation, Hausdorff, uniform continuity of left and right multiplication, topological ring) | D; P (`idempotentedRingTopologyTheorem_proof`) |
| I.1.3 the projective limit `Â = lim Ae` (transitions `b ↦ be`), its topology with basis `Â(1 − e)` and the continuous embedding `a ↦ (ae)_e` | 8–9 / 14–15 | `IdempotentedRingRightLimit` and [IdempotentedRingRightLimitUniformity](../../Langlands/Algebra/IdempotentedRingRightLimitUniformity.md) | D |
| I.1.3 the ring structure of `Â` extending `A`, independent of choices, unit `1(e) = e` | 9 / 15 | `IdempotentedRingRightLimit.ring` ([IdempotentedRingRightLimitRing](../../Langlands/Algebra/IdempotentedRingRightLimitRing.md)) | D |
| I.1.3 `A` is dense in `Â`; `Â` is complete (left to the reader) | 9 / 15 | `IdempotentedRingRightLimitDensityCompletenessTheorem` | P (`idempotentedRingRightLimitDensityCompletenessTheorem_proof`) |
| I.1.3 the action of `Â` on a nondegenerate module, independent of the fixing idempotent and unital; the orbit map `a ↦ a·m` extends by uniform continuity | 9 / 15 | [IdempotentedRingRightLimitAction](../../Langlands/Algebra/IdempotentedRingRightLimitAction.md); `IdempotentedRingOrbitExtensionTheorem` | D; P (`idempotentedRingOrbitExtension`) |
| I.1.4 the uniform structure on a nondegenerate `M` with basis `(1 − e)·M` and its pseudometrics | 9 / 15 | [NonUnitalModuleUniformity](../../Langlands/Algebra/NonUnitalModuleUniformity.md) | D |
| I.1.4 the completion `M̂ = lim e·M`, compatible families and the embedding `m ↦ (e·m)_e`; completeness and density | 9 / 15 | `NonUnitalModuleLeftLimit`, [NonUnitalModuleLeftLimitUniformity](../../Langlands/Algebra/NonUnitalModuleLeftLimitUniformity.md); `NonUnitalModuleLeftLimitDensityCompletenessTheorem` | D; P (`nonUnitalModuleLeftLimitDensityCompletenessTheorem_proof`) |
| I.1.4 Proposition: `Hom_A(A, M) ≅ M̂`, `φ ↦ (φ(e))_e` | 10 / 16 | `RegularModuleHomLeftLimitComparisonTheorem` | P (`regularModuleHomLeftLimitComparisonTheorem_proof`) |
| I.1.4 the `A`-module structure `(a·φ)(b) = φ(ba)` on `M̂`, extending that of `M` | 10 / 16 | [NonUnitalModuleLeftLimitAction](../../Langlands/Algebra/NonUnitalModuleLeftLimitAction.md) | D |
| I.1.4 "`M̂` n'est plus nécessairement non dégénéré" | 10 / 16 | `LeftLimitNotNondegenerateStatement` (an example exists: `A = ⊕_ℕ ℂ`, `M = A`, where `M̂` is the space of all sequences and the constant sequence `1` is fixed by no idempotent) | S: Task 5772 (candidate `9158d4aa`, published at Library `24a49431`) |
| I.1.4 Remark: `Â ≅ End_{A°}(A)` | 10 / 16 | `IdempotentedRingEndomorphismComparisonTheorem` (its `InverseIdentities` and `RingEquivalence` clauses) | P (`idempotentedRingEndomorphismComparisonTheorem_proof`) |
| I.1.5 the completion functor `M(A) → A-mod` on morphisms | 10 / 16 | [NonUnitalModuleCompletionFunctor](../../Langlands/Algebra/NonUnitalModuleCompletionFunctor.md) | D |
| I.1.5 Proposition: `(M̂)_A = M`; completion is faithful and right adjoint to smoothing; (I.1.5.1)–(I.1.5.2) | 10–11 / 16–17 | `NonUnitalModuleCompletionRecoveryFaithfulnessTheorem`, `NonUnitalModuleSmoothingCompletionAdjunctionTheorem` | P (`nonUnitalModuleCompletionRecoveryFaithfulnessTheorem_proof`, `nonUnitalModuleSmoothingCompletionAdjunctionTheorem_proof`) |
| I.1.5 Remark (I.1.5.3): for a submodule `N` of `M`, the completion `N̂`, viewed in `M̂` through the completed inclusion, is the closure of the canonical image of `N` in `M̂` | 11 / 17 | `NonUnitalModuleCompletionSubmoduleTheorem` (the range of the completed inclusion `mapHom hA S.subtype` is the closure of the canonical image of `S`) | P (`nonUnitalModuleCompletionSubmoduleTheorem_proof`) |
| I.1.6 `Â` as the subgroup `End_{A°}(A)` of `End_ℤ(A)`; the topology of simple convergence induces the topology of `Â` | 11 / 17 | `IdempotentedRingEndomorphismComparisonTheorem` (`UniformityComparison`, `RightLinearClosed` clauses) | P |
| I.1.6 Lemma: `Â` is the closure of the left multiplications | 11 / 17 | `IdempotentedRingEndomorphismClosureLemma` | P (`idempotentedRingEndomorphismClosureLemma_proof`) |
| I.1.6 Proposition: `Â ≅ Hom(ϖ, ϖ)`, the endomorphisms of the forgetful functor `ϖ : M(A) → ℤ-mod` | 12 / 18 | `NondegenerateModuleNaturalEndClassificationStatement.Classification` | P (`classification`). The source proof speaks of functors `M(A) → M(A)` while the display has target `ℤ-mod`; the statement follows the display (its [Markdown](../../Langlands/Algebra/NondegenerateModuleNaturalEndClassificationStatement.md)) |
| I.1.7 Lemma: `φ ∈ Â` commuting with left multiplications acts on every nondegenerate `M` by `φ̃_M(a·m) = φ(a)·m`, naturally in `M` | 12 / 18 | `NondegenerateModuleCenter.fromCommutantRingHom` and the component lemmas of [NondegenerateModuleCenter](../../Langlands/Algebra/NondegenerateModuleCenter.md) | D (the construction, its formula and naturality are proved there) |
| I.1.7 the two constructions are inverse; Theorem: `ℨ(A)` = commutant of `A` in `Â` = centre of `Â` = `lim_e Z(eAe)` | 12–13 / 18–19 | `NondegenerateModuleCenterTheoremStatement` | S: Task 5709 |
| I.1.7 Remark: for unital `A`, `ℨ(A) ≅ Z(A)` | 13 / 19 | `UnitalNondegenerateModuleCenterStatement` | S: Task 5709 |
| I.1.8 `z_M` scalars, constant on classes; (I.1.8.1); (Sep); the extension of (I.1.8.2) to `Â` is injective; elements of `ℨ(A)` are determined by their functions | 13–14 / 19–20 | `CenterScalarFunctionStatement` | S: Task 5710. That (I.1.8.1) is an algebra morphism follows from the uniqueness clause and is not stated separately (its [Markdown](../../Langlands/Algebra/CenterScalarFunctionStatement.md)) |

## I.2 Forgetful functors and their adjoints (14–19 / 20–25)

The I.2.1 rows follow the labels (a)–(k) of the [I.2.1 assertion map](unitization-tensor-progress.md).

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| I.2.1 (a)–(d): canonical scalars on nondegenerate modules (I.2.1.1); intertwiners are linear; scalars on Hom and tensor spaces | 14 / 20 | `NondegenerateScalars`, `NondegenerateModuleHomScalars`, `NondegenerateTensorScalars` | D (with proved laws) |
| I.2.1 (e): without a unit, `Hom_A` and `⊗_A` carry no canonical vector-space structure | 14 / 20 | none | X (motivation, as the 11 November coverage update records) |
| I.2.1 (f): the unique algebra structure on `Ã` | 14 / 20 | `UnitizationTensorComparison.UnitizationAlgebraUniqueStatement` | P (`unitizationAlgebraUnique`) |
| I.2.1 (g)–(h): unitized actions; `Hom` over `Ã` | 14 / 20 | `CompatibleUnitization`, `NondegenerateModuleHomScalars.unitizedHomEquiv` | D |
| I.2.1 (i): `X ⊗_Ã Y = X ⊗_A Y / Vect(…)` | 14 / 20 | `UnitizationTensorComparison.ScalarQuotientComparisonStatement` | P (`scalarQuotientComparison`) |
| I.2.1 (j)–(k): (I.2.1.2), Hom half and tensor half, and its unital case | 14 / 20 | `NondegenerateModuleHomScalars.unitizedHomEquiv` (Hom half); `NondegenerateUnitizedTensorStatement`, `UnitalUnitizedTensorStatement` (tensor half) | D; P (`nondegenerateUnitizedTensor`, `unitalUnitizedTensor`) |
| I.2.2 functors `• ⊗_A X`, `Hom_A(•, X)`, `Hom_A(X, •)` | 15 / 21 | the published balanced tensor `NonUnitalModuleTensor` and original Hom groups | D |
| I.2.2 Proposition: `• ⊗_A X` right exact, `Hom_A(•, X)` and `Hom_A(X, •)` left exact | 15 / 21 | `NondegenerateTensorHomExactness.TensorRightExactStatement`, `ContravariantHomLeftExactStatement`, `CovariantHomLeftExactStatement` | P (`tensorRightExact`); S: task `aa66676c` (the two Hom statements) |
| I.2.2 Theorem (I.2.2.1)–(I.2.2.4) over the unitizations `R̃`, `S̃` | 15 / 21 | Additive generalization over arbitrary rings with original actions: `NonUnitalTensorHomAdjunctionTheorem` ((I.2.2.1)–(I.2.2.3) with naturality) and `NonUnitalTensorAssociativityTheorem` ((I.2.2.4)) | C: the additive forms are proved (`nonUnitalTensorHomAdjunction`, `nonUnitalTensorAssociativity`). The complex-linear forms over `R̃`, `S̃` for possibly degenerate modules are not stated; see gap 2 |
| I.2.2 Corollary (I.2.2.5)–(I.2.2.7) for nondegenerate modules over idempotented algebras | 15 / 21 | The refined clauses of `NonUnitalTensorHomAdjunctionTheorem` (landing in the nondegenerate part) and `NonUnitalTensorAssociativityTheorem` | C: proved as additive isomorphisms. That they are complex-linear for the canonical scalars of I.2.1 is not stated separately; see gap 2 |
| I.2.2 Remark: naturality in `X`, `Y`, `Z` | 16 / 22 | the naturality clauses of the same theorems | P |
| I.2.3 unital case: `ϕ_*`, its left adjoint `B ⊗_A •` | 16 / 22 | `UnitalScalarExtensionAdjunction.ScalarExtensionAdjunctionStatements` (A.V.2) | P (`scalarExtensionAdjunctionStatements`) |
| I.2.3 unital case: the right adjoint `Hom_A(B, •)`; `N ≅ Hom_B(B, N) ≅ B ⊗_B N` | 16 / 22 | `RenardForgetfulFunctor.UnitalCoextensionAdjunctionStatement`; the isomorphisms are the unital case of (I.2.3.3)–(I.2.3.4) below | S: task `a2cfae06`; C |
| I.2.3 convention `ϕ ↦ ϕ_*` (Spec) | 16 / 22 | — | X |
| I.2.3 (I.2.3.1) `F_AB`, (I.2.3.2) `ˇF_AB` with `(a·φ)(b′) = φ(b′a)` | 17 / 23 | `NondegenerateTensorFunctor.F`, `RenardHomFunctors.pseudoF` | D |
| I.2.3 Remark: the term "pseudo foncteur d'oubli" | 17 / 23 | — | X |
| I.2.3 Lemma (I.2.3.3)–(I.2.3.4) | 17 / 23 | `RegularTensorContractionTheorem` ((I.2.3.3)); (I.2.3.4) is the recovery of I.1.5 with the I.1.4 Proposition | P (`regularTensorContraction`); C |
| I.2.3 Remark: `ˇF_AB(N) ≅ N` when the two nondegenerate parts coincide | 17 / 23 | `RenardForgetfulFunctor.PseudoForgetfulRemark` | S: task `a2cfae06` |
| I.2.3 Definition: `I_AB`, `P_AB` | 18 / 24 | `RenardHomFunctors.I`, `NondegenerateTensorFunctor.P` | D |
| I.2.3 Theorem: `F_AB ⊣ I_AB` and `P_AB ⊣ ˇF_AB` | 18 / 24 | `NondegenerateInductionAdjunction.NondegenerateFInductionAdjunctionTheorem`, `NondegenerateInductionAdjunction.NondegeneratePInductionAdjunctionTheorem` | P (`nondegenerateFInductionAdjunction`, `nondegeneratePInductionAdjunction`) |
| I.2.3 final Remark: for `ϕ : A → B`, `F_AB = ϕ_*`, `ϕ(Idem(A))` is a filtering system for `B`, and `ˇF_AB ≅ F_AB` | 18 / 24 | `RenardForgetfulFunctor.ForgetfulFunctorRemarkStatement` (`TensorForgetfulRemark`, `PseudoForgetfulRemark`) | S: task `a2cfae06` |
| I.2.4 Theorem: `F_AB` exact, `I_AB`, `ˇF_AB` left exact, `P_AB` right exact | 18 / 24 | `NondegenerateFInductionExactnessTheorem`, `NondegeneratePInductionExactnessTheorem` | P |
| I.2.4 Corollary: `I_AB` preserves injectives | 19 / 25 | `NondegenerateIInductionInjectivityTheorem` | P (`nondegenerateIInductionInjectivity`) |

## I.3 The functor `j_e : M ↦ e·M` (19–22 / 25–28)

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| I.3.1 `j_e`, (I.3.1.1) | 19 / 25 | [NonUnitalModuleCorner](../../Langlands/Algebra/NonUnitalModuleCorner.md) | D |
| I.3.1 Proposition: `j_e` is exact | 19 / 25 | `NondegenerateModuleCornerExactnessStatement` | P (`nondegenerateModuleCornerExactness`) |
| I.3.2 Lemma: the induction functor `i`, (I.3.2.1) `Z ≅ j_e ∘ i(Z)`, and `i(Z)` generated by `e·i(Z)` | 20 / 26 | `NonUnitalModuleCornerInduction.CornerInductionFixedPartTheorem`, `NonUnitalModuleCornerInduction.CornerInductionFixedPartNaturalIsoTheorem`, `NonUnitalModuleCornerInductionGeneratedStatements.CornerInductionGeneratedStatements` | P |
| I.3.2 remark after (I.3.2.1): the two complex structures on `A ⊗_{eAe} Z` coincide | 20 / 26 | `NonUnitalModuleCornerInduction.ComplexScalarsStatement` | P (`complexScalarsStatement`) |
| I.3.2 Definition: `M(A, e)`, `M_e` | 20 / 26 | [NonUnitalModuleIdempotentGenerated](../../Langlands/Algebra/NonUnitalModuleIdempotentGenerated.md), [IdempotentAnnihilatorQuotient](../../Langlands/Algebra/IdempotentAnnihilatorQuotient.md) | D |
| I.3.2 Lemma: `(M_e)_e = M_e`; (I.3.2.2) | 20–21 / 26–27 | `IdempotentAnnihilatorComparisonsTheorem` | P (`idempotentAnnihilatorComparisons`) |
| I.3.2 Proposition: `M ↦ e·M` is a bijection `Irr(A, e) → Irr(eAe)` | 21 / 27 | `NonUnitalModuleCornerSimpleStatements`: `SimpleCorrespondenceStatement` and its four components | P |
| I.3.2 the evaluation map `φ` and its properties in the proof of the Theorem | 21–22 / 27–28 | `NonUnitalModuleCornerEvaluationStatement.CornerEvaluationStatement` | P (`cornerEvaluation`) |
| I.3.2 Theorem: `j_e` is an equivalence `M(A, e) → M(eAe)` iff …, with inverse `i` | 22 / 28 | `CornerEquivalenceCriterionStatement`, `CornerEquivalenceStatement`, `GeneratedCategoryAbelianStatement`, `CornerInductionInverseStatement`, all in `NonUnitalModuleCornerSimpleStatements` | P |

## I.4 Duality (22–25 / 28–31)

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| I.4.1 `M^*` with its right action; `M̃` its nondegenerate part; the contravariant functors `M(A) → M(A)_d` and `M(A)_d → M(A)` | 22 / 28 | [NonUnitalModuleDual](../../Langlands/Algebra/NonUnitalModuleDual.md), [NonUnitalModuleDualFunctor](../../Langlands/Algebra/NonUnitalModuleDualFunctor.md) | D |
| I.4.1 an anti-involution identifies right and left modules | 22 / 28 | — | X ("dans la pratique"; used for groups in III.1.6) |
| I.4.1 Lemma: `M̃·e ≅ (e·M)^*`; duality is exact | 23 / 29 | `NonUnitalModuleDualFixedPart.FixedPartDuality`; `NonUnitalModuleDualCategoricalExactnessStatement`, `NonUnitalModuleDualMapExactnessStatement` | P (`fixedPartDuality`, `nonUnitalModuleDualCategoricalExactnessStatement`, `nonUnitalModuleDualMapExactnessStatement`) |
| I.4.1 Corollary: `M ↪ M̃̃` | 23 / 29 | `NonUnitalModuleBidualInjectionStatements.BidualInjection` | P (`bidualInjection`) |
| I.4.2 Theorem: `ˇF_AB(Ñ) ≅ F_AB(N)~` and `I_AB(M̃) ≅ P_AB(M)~` | 23–24 / 29–30 | `DualityForgetfulStatement`, `DualityInductionStatement`, under the reading of `B` as a bimodule of complex algebras (`IsScalarTower ℂ A B`, `IsScalarTower ℂ Aᵐᵒᵖ B`). The bare additive reading does not make the complex structures recovered from `A` and `B` agree, which Renard's evaluation formula needs ([duality-coefficient-conventions](duality-coefficient-conventions.md)) | S: Task 5778 (candidate `b72ce820`, published at Library `a54dda0d`); the bare additive reading remains open (gap 1) |
| I.4.2 Lemma (I.4.2.1): `Hom_A(V, W̃) ≅ Hom_A(W, Ṽ)`, natural in `V`, `W` | 24 / 30 | `NonUnitalModuleDualHomTransposeStatements.DualHomTranspose` | P (`dualHomTranspose`) |
| I.4.3 the completion of `M̃` is `M^*` | 25 / 31 | `NonUnitalModuleDualCompletion.DualCompletionStatement` | S: Task 5759 (candidate `faf3a73f`, published at Library `24a49431`) |
| I.4.3 the step `ι : N_A ⊗_A M ≅ N ⊗_A M` | 25 / 31 | `NonUnitalTensorSmoothingStatements.TensorSmoothing` | P (`tensorSmoothing`) |

## I.5 Some classes of modules (26–27 / 32–33)

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| I.5.1 Definition: admissible modules | 26 / 32 | [NonUnitalModuleAdmissible](../../Langlands/Algebra/NonUnitalModuleAdmissible.md) | D |
| I.5.1 Proposition: admissible iff `M → M̃̃` is an isomorphism; Corollary: `M̃` admissible, `M` simple iff `M̃` simple | 26 / 32 | `NonUnitalModuleAdmissibilityStatements.AdmissibilityDuality` (`AdmissibleIffEvaluationBijective`, `AdmissibleDual`, `AdmissibleSimpleIffDualSimple`) | P (`admissibilityDuality`) |
| I.5.2 Theorem: `M(A)` has enough projectives (`Ae` projective; sums of projectives are projective) | 26 / 32 | `NonUnitalModuleEnoughProjectives.ProjectivityAssertions` (`IdealProjectivityStatement`, `DirectSumProjectivityStatement`, `EnoughProjectivesStatement`, `SurjectiveProjectiveCoverStatement`) | P (`projectivityAssertions`) |
| I.5.2 Lemma: `X` projective implies `X̃` injective; Corollary: enough injectives | 27 / 33 | `NonUnitalModuleEnoughInjectives.InjectivityAssertions` (`DualProjectivityStatement`, `EnoughInjectivesStatement`, `InjectiveEmbeddingStatement`) | P (`injectivityAssertions`). The existence assertions are stated for carriers in `max uA uM` (their [Markdown](../../Langlands/Algebra/NonUnitalModuleEnoughInjectivesStatements.md)) |
| I.5.3 free modules; every module is a quotient of a free module; a projective module is a summand of a free module | 27 / 33 | `NonUnitalModuleFreeStatements.FreeModuleAssertions` (`FreeQuotientStatement`, `ProjectiveFreeSummandStatement`) | P (`freeModuleAssertions`) |
| I.5.3 `A` need not be projective in `M(A)`; a summand of a free module need not be projective | 27 / 33 | `NonUnitalModuleFreeCounterexampleStatements.FreeCounterexampleAssertions` | P (`freeCounterexampleAssertions`) |

## I.6 Properties of `M(A)` (27–28 / 33–34)

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| I.6 `M(A)` is abelian | 27 / 33 | `NondegenerateModuleAbelianStatement` | P |
| I.6 Proposition: complete and cocomplete; products are nondegenerate parts of products | 27 / 33 | `NondegenerateModuleCompletenessStatements.CompletenessAssertions` | P (`completenessAssertions`) |
| I.6 Proposition: AB5 | 28 / 34 | `NondegenerateModuleAB5Statements.AB5Assertions` (`DirectedSubobjectDistributivity`, `SourceAB5Statement`) | P (`ab5Assertions`) |
| I.6 Proposition: AB6 in the sense of footnote 3 (every object is an increasing union of objects of finite type) | 28 / 34 | `NondegenerateModuleLocallyFiniteTypeStatements.LocallyFiniteTypeAssertions` (`SourceAB6Statement`) | P (`locallyFiniteTypeAssertions`) |
| I.6 Proposition: filtered colimits are exact | 28 / 34 | `NondegenerateModuleFilteredColimitsStatements.FilteredColimitAssertions` | P (`filteredColimitAssertions`) |
| I.7 Notes | 28 / 34 | — | X |

## Genuine gaps of Chapter I

1. I.4.2 Theorem under the bare additive reading of "`B` muni d'une structure de
   `A`-bimodule", without compatibility of the `A`-actions with the complex scalars. The
   published statements of `b72ce820` state the Theorem for bimodules of complex algebras.
   Whether a natural isomorphism exists in the additive setting is not decided
   ([duality-coefficient-conventions](duality-coefficient-conventions.md)).
2. I.2.2 Theorem and Corollary: the complex-linear forms of the tensor–Hom and associativity
   isomorphisms (over the unitizations for arbitrary modules, and for the canonical scalars
   of I.2.1 in the nondegenerate case). The additive isomorphisms are proved.

The I.1.2 direct-limit reformulations, I.1.2 Remark 2 and the I.1.4 degenerate completion
are stated by the published candidate `9158d4aa` (Library `24a49431`), with proof Task 5772.

## Pending

Statements with open proof tasks: I.1.7 (Task 5709), I.1.8 (Task 5710), I.4.3 (Task 5759),
the I.2.2 Hom exactness statements (task `aa66676c`), the I.2.3 unital right adjoint and
remarks (task `a2cfae06`), I.1.2 and I.1.4 (Task 5772) and the I.4.2 Theorem (Task 5778).

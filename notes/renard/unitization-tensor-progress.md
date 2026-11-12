# Renard I.2.1: canonical scalars and unitized Hom and tensor comparisons

Worker 709 wrote this note on 6 November 2026 against Library
`f36ed55eca30538e32c10c31fb7b28cf2eaec0ef`. It maps every printed assertion
of I.2.1 to the published Lean declarations that state it, or records that no
declaration does. Six published definition units carry the section. Before this
note, no Renard note described `NondegenerateModuleHomScalars` or
`CompatibleUnitizationTensor`. Two notes cite `NondegenerateScalars` and
`NondegenerateTensorScalars` only in passing: the
[scalar-projector note](scalar-projector-progress.md) and the
[duality coefficient note](duality-coefficient-conventions.md).

Worker 709 is neither an author nor a coauthor of any of the six units. This
note documents them and is not a review of them. It supplements the
[unitization criteria note](unitization-noetherian-criteria.md), which records
the finiteness and Noetherian consequences of the unitization. The scope is
I.2.1 only; see the last section.

## Source context

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Printed page `p` is PDF page `p + 6`. I.2.1, "Structure d'espace vectoriel sur
les modules non dégénérés", is on printed page 14 / PDF 20. Worker 709 reread
it for this note. I.1.8 (printed 13 / PDF 19) points forward to it in
footnote 2: "Il est expliqué dans la section suivante comment un module dans
`M(A)` est naturellement muni d'une structure de `ℂ`-espace vectoriel qui rend
l'action de `A` linéaire".

The section makes these assertions, labelled here for the map below.

- (a) For a unital complex algebra `A` and a unital module `M`,
  `λm := (λ1_A)·m` is a canonical vector-space structure, and
  (I.2.1.1) `λ(a·m) = (λa)·m = a·(λm)` holds.
- (b) For an idempotented complex algebra `A` and a nondegenerate module `M`,
  `λm := (λe)·m` for any `e ∈ Idem(A)` with `e·m = m`. This does not depend on
  `e`, and (I.2.1.1) still holds.
- (c) For nondegenerate `X` and `Y`, every morphism in `Hom_A(X, Y)` is
  `ℂ`-linear, and `Hom_A(X, Y)` is a vector space with
  `λφ : x ↦ λ(φ(x)) = φ(λx)`.
- (d) For a nondegenerate right module `X` and a nondegenerate left module
  `Y`, `X ⊗_A Y` inherits a vector-space structure and is a quotient of
  `X ⊗_ℂ Y`.
- (e) If `A` has no unit, `Hom_A(X, Y)` and `X ⊗_A Y` carry no canonical
  vector-space structure, even when `X` and `Y` are vector spaces.
- (f) `Ã = A ⊕ ℂ·1_A`, where `1_A` is declared to be the unit; "ceci détermine
  une unique structure d'algèbre sur `Ã`".
- (g) `A`-modules that are also vector spaces "deviennent naturellement des
  `Ã`-modules unitaires". This needs the compatibility (I.2.1.1), which the
  source leaves implicit.
- (h) `Hom_Ã(X, Y) = Hom_A(X, Y) ∩ Hom_ℂ(X, Y)`.
- (i) `X ⊗_Ã Y = X ⊗_A Y / Vect({λx ⊗ y − x ⊗ λy})`, where `Vect(P)` is "le
  sous-espace engendré par une partie `P` d'un espace vectoriel".
- (j) (I.2.1.2): for idempotented `A` and nondegenerate `X`, `Y` with their
  canonical scalars, `Hom_Ã(X, Y) = Hom_A(X, Y)` and `X ⊗_Ã Y = X ⊗_A Y`.
- (k) In particular (j) holds when `A`, `X` and `Y` are unital.

## Lean model

All declarations below lie in namespace `Langlands.Algebra`. Except for the
scalar-free carrier `NonUnitalModuleTensor`, the modules take an arbitrary
commutative scalar ring `k` in place of `ℂ`, together with
`[NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]`.
The ring is a `CommSemiring` in `NondegenerateScalars` and a `CommRing` in the
other modules. `NondegenerateScalars`, `NondegenerateModuleHomScalars` and
`NondegenerateTensorScalars` also state the `ℂ` specializations, with a
`complex` prefix. A right module is a `NonUnitalModule Aᵐᵒᵖ X`. The constructed
scalar actions are definitions, not instances; statements install them locally
with `letI`.

`Ã` is Mathlib's `Unitization k A`, the product `k × A` with unit `(1, 0)`.
The unitized action of `CompatibleUnitization.module ρ` is determined by a
nonunital algebra map `ρ : A →ₙₐ[k] Module.End k M`. The coordinate law is

```text
u • m = u.fst • m + ρ u.snd m
```

and the `k`-linearity of each `ρ a` encodes the compatibility (I.2.1.1).

## Assertion map

| Assertion | Published declarations | Status |
| --- | --- | --- |
| (a) unital case | `NondegenerateScalars.unitalModule k hM` and `unital_smul_eq` (`c • m = (c • 1) • m`) for `[Ring R] [Algebra k R]` and `hM : IsUnitalModule R M` | Stated. (I.2.1.1) in the unital case is `smul_action` and `action_smul` at `IsIdempotented.of_ring R`, and `isNondegenerate_iff_isUnitalModule.mpr hM`, because `unitalModule` unfolds to `module`. This specialization is derived, not a named declaration; Worker 709 compiled it in a private check |
| (b) nondegenerate case | `NondegenerateScalars.module k hA hM`, `scalarMul`, `fixer_independent`, `scalarMul_eq`, `smul_eq`, `complexModule`, `complex_smul_eq`; (I.2.1.1) is `smul_action` and `action_smul`, with adapters `isScalarTower` and `smulCommClass` | Stated. Internal addition: `scalarMul_eq_of_compatible` and `module_eq_of_compatible` show that any `Module k M` with `IsScalarTower k A M` equals the constructed one |
| (c) linearity and Hom space | `NondegenerateScalars.map_smul`, `toLinearMap` (both need `hM` and `hN`), `complexToLinearMap`, `toLinearIntertwiner`; `NondegenerateModuleHomScalars.homModule k hA hN`, `smul_apply` (`(c • φ) m = c • φ m`), `smul_apply_eq_source` (`= φ (c • m)`), `complexHomModule`, `comp_smul`, `smul_comp` | Stated. `homModule` needs only target nondegeneracy |
| (d) tensor scalars and quotient | `NondegenerateTensorScalars.module k A X Y hA hY` (needs only `hA` and `hY`), `smul_tmul_left`, `smul_tmul_right`, `tmul_smul_left_eq`; `coefficientProjection` and `coefficientProjection_surjective` from `X ⊗[k] Y`; `coefficientRelations`, the `k`-span of `(op a • x) ⊗ y − x ⊗ (a • y)`; `ker_coefficientProjection`; `quotientEquiv`; complex versions `complexModule`, `complexProjection`, `complexProjection_surjective`, `complexRelations`, `ker_complexProjection`, `complexQuotientEquiv` | Stated. Internal additions: `linearLift` and `linearMap` |
| (e) no canonical structure without a unit | none | Informal remark, not stated. The zero-action `example`s of `CompatibleUnitizationTensor`, described below, illustrate it for tensors |
| (f) the algebra `Ã` | Mathlib `Unitization k A` | The construction is Mathlib's. Uniqueness of the algebra structure is **not stated**. The published uniqueness results concern actions only: `CompatibleUnitization.endHom_unique`, `module_unique` and `module_unique_of_isScalarTower` |
| (g) unitized actions | `CompatibleUnitization.endHom` (`Unitization.lift ρ`), `module ρ`, `smul_eq`, `inr_smul`, `inl_smul`, `one_smul`; two-sided versions `CompatibleUnitizationTensor.leftModule` and `rightModule` (through `opRingEquiv`), under `IsScalarTower` and `SMulCommClass` hypotheses on `X` and `Y` | Stated |
| (h) Hom over `Ã` | `CompatibleUnitization.intertwiners ρ σ : Submodule k (M →ₗ[k] N)`, the `k`-linear maps intertwining `ρ` and `σ`; `linearMapEquiv ρ σ : (M →ₗ[Unitization k A] N) ≃ₗ[k] intertwiners ρ σ`; `endAlgEquiv` | Stated |
| (i) tensor over `Ã` | `CompatibleUnitizationTensor.UnitizedTensor` (`TU`), `isBalanced_unitization_iff`, `unitizedLift`, `unitizedLift_unique`, `unitizedTmul_original`, `unitizedTmul_scalar`; `comparison` (`q : TA →+ TU`) and `comparison_surjective`; `scalarRelations` (`H`); `ScalarQuotient` (`Q = TA ⧸ H`); `scalarRelations_le_ker`; `descendedComparison` (`qbar : Q →+ TU`) and `descendedComparison_mk_tmul` | **Partial.** `H ≤ ker q` and the surjectivity of `q` are stated. `H = ker q`, equivalently the bijectivity of `qbar`, is not |
| (j) (I.2.1.2) | Hom half: `NondegenerateModuleHomScalars.intertwinersEquiv`, `unitizedModule`, `unitizedHomEquiv : NonUnitalModuleHom A M N ≃ₗ[k] (M →ₗ[Unitization k A] N)`, `complexUnitizedHomEquiv` | **Partial.** The Hom half is stated. The tensor half is not |
| (k) unital case of (j) | none named | The Hom half is `unitizedHomEquiv` instantiated at `IsIdempotented.of_ring R` and `isNondegenerate_iff_isUnitalModule.mpr` for `[CommRing k] [Ring R] [Algebra k R]`. This is derived, with no named declaration; Worker 709 compiled it in a private check. The tensor half is not stated |

Notes on the map:

- `H` is `Submodule.span ℤ` of the differences
  `tmul (c • x) y − tmul x (c • y)` in the original tensor `TA`. Renard's
  `Vect(P)` is a span in a vector space, but `X ⊗_A Y` carries no canonical
  vector-space structure in the setting of (i). The module Markdown of
  `CompatibleUnitizationTensor` records this choice as its "integer-span
  convention".
- The zero-action diagnostics of `CompatibleUnitizationTensor` take
  `k = A = X = Y = ℂ` with both original actions zero. An `example` there
  proves that the scalar relation at `(I, 1, 1)` is nonzero in `TA`, lies in
  `H` and is killed by `q`, so `q` is not injective. It thus shows that
  `(I·1) ⊗ 1 ≠ 1 ⊗ (I·1)` in `TA`: the scalar multiplications through `X` and
  through `Y` disagree. This illustrates the phenomenon behind remark (e) for
  tensors, but not its exact hypothesis: there `A = ℂ` has a unit, and the
  modules are degenerate instead. These are unnamed `example`s, not
  published theorems.
- Four further module Markdown files mention the comparison with `⊗_Ã`:
  `NonUnitalTensorAssociativityStatements`, `NonUnitalBimoduleTensor`,
  `NondegenerateTensorFunctor` and `NonUnitalBimodule`. Each keeps it as a
  separate obligation, and none claims `H = ker q`.

## Unpublished assertions

**Update, 9 November 2026 (Worker 1222).** The three assertions listed below
now have a published statement, `Langlands.Algebra.UnitizationTensorComparison.Statements`
in `Langlands.Algebra.UnitizationTensorComparisonStatements` (candidate
`e80ce45c-c3e2-46e7-8bc5-cc27c0949975`), which also states the tensor half of
the unital case (k). It is unproved; its proof task is Task 5279
(`90d04aab-0598-451d-8547-a3198505043a`). See the
[9 November coverage update](coverage-update-2026-11-09.md). The text below is
kept as it stood on 6 November.

Three printed assertions had no published statement:

1. `H = ker q` in (i), equivalently the bijectivity of `qbar`.
2. The tensor half of (I.2.1.2) in (j) and (k).
3. The uniqueness of the algebra structure on `Ã` in (f).

On 6 November, task searches for "unitized tensor comparison kernel",
"I.2.1.2 tensor" and "CompatibleUnitizationTensor" found no successor task.
The last search found only definition task
`fc080bdb-06d7-432a-aa3f-0f72928470f2` and its accepted unit `ea25e94a`.

Worker 709 has not checked the following routes in Lean; they are
suggestions only.

- For `H = ker q`: the pure map `(x, y) ↦ mk (tmul x y)` into `Q` is
  `A`-balanced by `NonUnitalModuleTensor.tmul_balanced` and scalar-balanced
  by `scalarDifference_mem`, so `unitizedLift` would give a candidate inverse
  of `qbar`. Its two identities would follow from `unitizedHom_ext` and from
  quotient extensionality together with `NonUnitalModuleTensor.hom_ext`.
- For the tensor half of (I.2.1.2): under the canonical scalars,
  `NondegenerateTensorScalars.tmul_smul_left_eq` makes the original pure map
  scalar-balanced, so `unitizedLift` would give an inverse of `q` directly. To
  instantiate `CompatibleUnitizationTensor`, the factors need the
  constructed `Module k X` and `Module k Y` and the tower and commutation
  hypotheses from `NondegenerateScalars.isScalarTower` and `smulCommClass`,
  on `X` through the opposite algebra.

## Library importers

At Library `f36ed55e`:

- `CompatibleUnitizationTensor` has no importer.
- `NondegenerateScalars` is imported by `NondegenerateModuleLinearActions`,
  `NonUnitalModuleDual`, `NondegenerateModuleHomScalars`,
  `NonUnitalModuleCornerScalars`, `NondegenerateTensorScalars` and, outside
  `Langlands/Algebra`, `Langlands/HarmonicAnalysis/PointwiseTestModule`.
- `NondegenerateModuleHomScalars` is imported by
  `NonUnitalModuleDualHomTranspose` and `NonUnitalBimoduleHomScalars`.
- `NondegenerateTensorScalars` is imported by `NonUnitalBimoduleTensorScalars`.
- `CompatibleUnitization` has eleven importers: `CompatibleUnitizationSubmodule`,
  `NondegenerateModuleHomScalars`, `CompatibleUnitizationTensor`,
  `IntegerUnitizationCategory`, `NonUnitalSeparationStatements`,
  `UnitizationZeroActionFinitenessStatements`,
  `CompatiblePowerStabilizationStatements`,
  `RenardCompatibleStableImageStatements`, `RenardAdditiveStableImageStatements`,
  `RenardCompatibleLocalizationNoetherianStatements` and
  `RenardAdditiveLocalizationNoetherianStatements`.
- `NonUnitalModuleTensor`, the carrier of `TA` and `TU`, is imported by
  `NondegenerateTensorScalars`, `CompatibleUnitizationTensor`,
  `NonUnitalTensorSmoothing` and `NonUnitalBimoduleTensor`.

## Receipts

All six units are accepted and published definitions. Each independent
reviewer approves without qualifications, and no author qualification is
recorded. Submitter and coauthors below come from the review-task bindings.
The Markdown of `NondegenerateModuleHomScalars` also says that Worker 6
authored the Lean and Markdown pair and that Worker 751 audited it against the
source and submitted it.

| Unit | Accepted artifact | Submitted by; coauthors | Reviewer | Publication commit |
| --- | --- | --- | --- | --- |
| Canonical scalars (`NondegenerateScalars.module`) | `47a84173-79e5-494c-88ff-25999c652398` | Worker 691 | Reviewer 5091 | `1b5395385eb8f29f15b687caf40cb44625f6ae37` |
| Hom scalars (`NondegenerateModuleHomScalars.unitizedHomEquiv`) | `f9c195b1-a6d6-471a-971d-e5c839acdd68` | Worker 751; Worker 6 | Reviewer 5854 | `7114a39081ee7c0f5e7ab6294392905004234dd3` |
| Tensor scalars (`NondegenerateTensorScalars.quotientEquiv`) | `c8010c52-435c-4f89-96ca-3a7fb39dc9b3` | Worker 735 | Reviewer 6294 | `a4c7cf32e45265b253c1b67bad8768eed2c6eebb` |
| Unitized action (`CompatibleUnitization.module`) | `4913dbfa-bc31-40b3-8d32-3f75e21cad09` | Worker 734 | Reviewer 3514 | `5b9935101c61f2c53bff91434ebe60bcd5719881` |
| Unitized tensor comparison (`CompatibleUnitizationTensor.descendedComparison`) | `ea25e94a-60a1-424e-adcd-e8422f6cbc24` | Worker 1088; Worker 803 | Reviewer 6280 | `a4c7cf32e45265b253c1b67bad8768eed2c6eebb` |
| Balanced tensor carrier (`NonUnitalModuleTensor.universalEquiv`) | `737eea27-b370-41da-a99c-80bf09d1925f` | Worker 1171; Worker 6 | Reviewer 5855 | `7114a39081ee7c0f5e7ab6294392905004234dd3` |

| Unit | Definition task | Review task | Machine receipt (policy) | Integration |
| --- | --- | --- | --- | --- |
| `47a84173` | `9d2b9b25-c9ab-47cc-ba7c-6b96e4e5d53f` | `512ad524-39ed-4d78-8625-ba0dd2631226` | `232817e2-1da8-4309-aa58-9bfede8c2552` (`lean.definition@1`) | `24bf9a2adfa046e18d122045dfc20f71` |
| `f9c195b1` | `91fba45f-e355-49a6-be64-13d4c1ed0d76` | `c68d1d8d-1781-4c52-b023-062c46c00c3d` | `825d808c-9e03-4674-aaef-0018125b2c78` (`lean.definition@1`) | `2b933cbea6114798af933eb4efea897d` |
| `c8010c52` | `f4ec2106-b5e5-449a-8dcd-6c234d74bd2a` | `38762c5b-6b77-465d-8fe5-cf740c071023` | `58ea54ae-8138-49f2-b434-63fb35f25f4f` (`lean.definition@1`) | `26c6812fc50a4492bbb8a91268b5bdb3` |
| `4913dbfa` | `2e6ba45d-844d-458a-aba5-3b706694aae6` | `81bb30c3-1f61-4048-aad9-85cc1f9dfaa3` | `cde23a04-bd79-4c5c-84fb-af8c4fa78e23` (`lean.definition@1`) | `999855cbd3ee49f9aaea64e72cb96bd6` |
| `ea25e94a` | `fc080bdb-06d7-432a-aa3f-0f72928470f2` | `6b7373cc-67a9-47ba-ac83-04c5cb48420c` | `29d61bc2-5222-458c-808b-14937d9ee2b5` (`lean.definition@1`) | `fe92c475d30f44378a0f78ebec34d7e3` |
| `737eea27` | `97d0e767-0e74-4058-8240-722eeb435a95` | `f9b96e92-f447-4cb7-a7cd-913de4cf8126` | `17f408ef-d635-496c-9135-011a21ab91e7` (`lean.definition@1`) | `56d94464b621430b957fadaac47e1994` |

Each machine receipt is accepted. It checks the schema, immutable content,
reference integrity, exact reference policies, Lake build and declaration
kind.

Worker 709 checked the twelve Lean and Markdown files of these units at
Library `f36ed55e` and in the workspace. Each equals its frozen bundle except
`CompatibleUnitization.md`. Its frozen hash is `fa6bd152…`, and the definition
unit `fa45496e-d183-4461-937c-9ec258f9fa9b` later updated only that Markdown
file; the Lean file is unchanged.

| File | SHA256 at Library `f36ed55e` and in the workspace |
| --- | --- |
| `Langlands/Algebra/NondegenerateScalars.lean` | `01ba3a176bd40a02425cfd075e7e8c2dae58c3be8e0e9062f318f0cc7fb3d0a8` |
| `Langlands/Algebra/NondegenerateScalars.md` | `fe2ee32dd4c2431372d7f5a642f6b31bdd51f4d8efde90b9329a87aea9f91b49` |
| `Langlands/Algebra/NondegenerateModuleHomScalars.lean` | `b5450f9afc5ab12986079a30dd6e6b1b7d6acf0f6c9e5ed2c7d247ca03d0de9c` |
| `Langlands/Algebra/NondegenerateModuleHomScalars.md` | `624f6a0dd40ee33e22bc23eff27ac063dcb3249ea5100cfd004d972c584d2ddc` |
| `Langlands/Algebra/NondegenerateTensorScalars.lean` | `0830db82af47963bffeb3018e9c426e15e5c102be09070e2f7b76046010091e0` |
| `Langlands/Algebra/NondegenerateTensorScalars.md` | `da21b14a2d376f91cb91c13d77b22a60a742e602171e9adbfc15e3e76f406e7a` |
| `Langlands/Algebra/CompatibleUnitization.lean` | `dccd7ec4a65550f775fdc5c13a521fadff50ebedf13bf3c33926de7fd516aade` |
| `Langlands/Algebra/CompatibleUnitization.md` | `2ae4d09143e2f44a646744e4d1f7940877fc20ace5402a3111c0e1690cb0ead8` |
| `Langlands/Algebra/CompatibleUnitizationTensor.lean` | `d0d92b13453001dc919c5278856de9e4d198843d761d1b76685cdfee667027b3` |
| `Langlands/Algebra/CompatibleUnitizationTensor.md` | `ef586154b461ff9ae4a882c515f684971f210e8c333ccc471a9b69df84dee480` |
| `Langlands/Algebra/NonUnitalModuleTensor.lean` | `64b1657696e2c9a8493b1a4d1c41de4640088c33c87c5bff253820393125b159` |
| `Langlands/Algebra/NonUnitalModuleTensor.md` | `a014546a6d58ec2d63115f48277e182ddbbfaccf263ce065c30c4fb7d797d795` |

## Scope

This note covers I.2.1 only. I.2.2 and I.2.3 also have published units, for
example the bimodule tensor, tensor functor, tensor associativity and
induction-adjunction modules, but this note does not map them. The three
unpublished assertions above remain with the whole-book parent task. This note
declares no section, chapter or book completion.

# Renard I.2.1 and C.II: unitization Noetherian and stable-generation criteria

This note was written on 6 November 2026 against Library
`ded343f95a7ebe4954d12a37616f22db56be249c`. It records fourteen published
modules that connect Renard's unitized algebra to finiteness and
Noetherian conditions on stable subspaces, stable additive subgroups and left
ideals. Before this note, no Renard note described these modules.

The note supplements the [C.II quotient and finite-localization
audit](stable-quotients.md), whose localization proofs use several of the
criteria below, and the [finiteness source audit](nonunital-finiteness-sources.md).
Every module here is a derived internal comparison. None selects Renard's
convention for a Noetherian nonunital algebra or a finite-type nonunital
module, and none closes a section, appendix or the book.

## Source context and model

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Printed page `p` is PDF page `p + 6`. These passages were reread for this
note:

- I.2.1, printed 14 / PDF 20. For a complex algebra `A` without unit, Renard
  introduces `Ã = A ⊕ ℂ·1_A`, with `1_A` declared to be its unit. `A`-modules
  that are also complex vector spaces "deviennent naturellement des
  `Ã`-modules unitaires".
- C.II, printed 279 / PDF 285. The final proposition takes "une `ℂ`-algèbre
  commutative noethérienne" `B`, a `B`-module `L` "de type fini", and assumes
  that the localization `L_a` is also of finite type.

The Lean model of `Ã` is Mathlib's `Unitization R A`: the product `R × A`
with multiplication `(r, a)(s, b) = (rs, r • b + s • a + ab)` and scalar
projection `Unitization.fstHom R A`. Most modules allow an arbitrary
commutative scalar ring `R` in place of `ℂ`. The additive and original-module
modules use `ℤ`, and the zero-action pair compares `ℂ` with `ℤ`. This
generalization belongs to the implementation, not to the book. No global
instance selects the unitized action. A statement either binds a supplied
`Module (Unitization R A) M` together with the explicit coordinate law

```text
u • m = u.fst • m + ρ u.snd m
```

or installs `CompatibleUnitization.module ρ` locally with `letI`. The
published `CompatibleUnitization.smul_eq ρ` proves this law for the
installed action, and `CompatibleUnitization.isScalarTower ρ` supplies its
scalar tower. Downstream proofs use both lemmas to instantiate the
supplied-action criteria.

## 1. Stable subspaces as unitized submodules

The definition `Langlands.Algebra.CompatibleUnitization.submoduleOrderIso`
([module](../../Langlands/Algebra/CompatibleUnitizationSubmodule.md)) takes
`[CommRing k]`, a bilinear `[NonUnitalRing A]` over `k`, a `k`-module `M` and
an arbitrary `ρ : A →ₙₐ[k] Module.End k M`, including `ρ = 0`. It gives

```lean
CompatibleSubmodule ρ ≃o (letI := module ρ; Submodule (Unitization k A) M)
```

with the same carriers in both directions. The module also proves
membership, `restrictScalars` and lattice-operation lemmas, and the
following comparisons:

- `restrictEquiv S`: the unitization of the restricted original action is
  unitized-linearly equivalent to the restricted unitized action;
- `quotientEquiv S`: the analogous equivalence for the quotient original
  action and the quotient unitized action, through the same quotient map;
- `zeroSubmoduleOrderIso`: for the zero original action, every `k`-subspace is
  a unitized submodule.

Its examples over the zero action of `ℂ` on `ℂ` show that the zero and whole
subspaces are distinct unitized submodules and that the quotient by the whole
space is zero. On the restricted whole space, an element `x` of
`Unitization ℂ ℂ` acts by multiplication by `x.fst`, so the algebra element
`1 : ℂ` acts by zero. A field specialization repeats the three comparisons
over an arbitrary field. The module records that Renard uses the carrier comparison
implicitly in I.2.1 and in the reduction at the start of B.II, printed 272 /
PDF 278, but never states it.

## 2. Finite stable generation for a supplied unitized action

Three statement/proof pairs express finite generation and Noetherianity of an
actual unitized module through finite generating sets among stable subobjects
of the original action. Each pair has three components, in the order
submodule, whole module, Noetherian.

### Scalar-linear stable submodules

[`UnitizationStableGenerationStatements`](../../Langlands/Algebra/UnitizationStableGenerationStatements.md)
binds `[CommRing R]`, a bilinear nonunital `R`-algebra `A`, an `R`-module `M`,
a supplied `Module (Unitization R A) M` with
`IsScalarTower R (Unitization R A) M`, `ρ : A →ₙₐ[R] Module.End R M` and the
coordinate law. Its universes `uR, uA, uM` are independent. Call an
`R`-submodule `P` of `M` stable if `ρ a m ∈ P` whenever `m ∈ P`. Then:

1. `SubmoduleGenerationStatement`: a unitized submodule `Q` is finitely
   generated exactly when some finite `S ⊆ Q` has `Q.restrictScalars R ≤ P`
   for every stable `P` containing `S`;
2. `ModuleGenerationStatement`: `Module.Finite (Unitization R A) M` holds
   exactly when some finite `S` lies in no stable `P` other than `⊤`;
3. `NoetherianGenerationStatement`: `IsNoetherian (Unitization R A) M` holds
   exactly when every stable `P` contains a finite `S` such that `P ≤ Q` for
   every stable `Q` containing `S`.

The [proof](../../Langlands/Algebra/UnitizationStableGenerationProof.md)
proves these as `fg_iff_stable_generators`, `finite_iff_stable_generators`
and `noetherian_iff_stable_generators`, assembled as
`UnitizationStableGeneration.unitizationStableGeneration`. The coordinate law
makes every stable `P` a unitized submodule with the same carrier. Conversely,
the `R`-restriction of a unitized span is stable, because `Unitization.inr a`
acts as `ρ a`.

### All additive stable subgroups over the integer unitization

[`AdditiveUnitizationGenerationStatements`](../../Langlands/Algebra/AdditiveUnitizationGenerationStatements.md)
binds a nonunital ring `A`, an additive group `M`, a supplied
`Module (Unitization ℤ A) M`, an additive representation
`ρ : A →ₙ+* AddMonoid.End M` and the same coordinate law. Its three
components have the same shape as above, but range over all `AddSubgroup M`
stable under `ρ`, with no scalar-linearity condition. The submodule
component compares `Submodule.toAddSubgroup Q`. The
[proof](../../Langlands/Algebra/AdditiveUnitizationGenerationProof.md)
follows the scalar route, with `zsmul_mem` in place of scalar closure. Its
theorems are `fg_iff_additive_stable_generators`,
`finite_iff_additive_stable_generators` and
`noetherian_iff_additive_stable_generators`, assembled as
`AdditiveUnitizationGeneration.additiveUnitizationGeneration`.

### Original nonunital modules

[`IntegerOriginalSubmoduleGenerationStatements`](../../Langlands/Algebra/IntegerOriginalSubmoduleGenerationStatements.md)
binds an original `[NonUnitalModule A M]` over a nonunital ring. It installs
`CompatibleUnitization.module (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))`
on the same carrier and ranges over `NonUnitalSubmodule A M`, the original
stable additive subgroups:

1. `SubmoduleGenerationStatement`: the unitized submodule
   `NonUnitalSubmodule.intUnitizedOrderIso P` is finitely generated exactly
   when some finite `S ⊆ P` has `P ≤ Q` for every original stable `Q ⊇ S`;
2. `ModuleGenerationStatement`: the unitized module is finite exactly when
   some finite `S` is contained in no original stable subgroup other than the
   whole carrier;
3. `NoetherianGenerationStatement`: the unitized module is Noetherian
   exactly when every original stable `P` has such a finite generating set.

The [proof](../../Langlands/Algebra/IntegerOriginalSubmoduleGenerationProof.md)
transports unitized spans through the published order isomorphism
`NonUnitalSubmodule.intUnitizedOrderIso`, which is defined in
[`IntegerNonUnitalSubmodule`](../../Langlands/Algebra/IntegerNonUnitalSubmodule.md)
as `NonUnitalSubmodule.intCompatibleOrderIso` composed with
`CompatibleUnitization.submoduleOrderIso`. It does not invoke the additive
comparisons above. Its theorems are `fg_intUnitizedOrderIso_iff`,
`finite_iff_original_stable_generators` and
`noetherian_iff_original_stable_generators`, assembled as
`IntegerOriginalSubmoduleGeneration.integerOriginalSubmoduleGeneration`.

## 3. Noetherian criteria for the unitization ring

### Scalar-projection kernel

[`UnitizationNoetherianStatements`](../../Langlands/Algebra/UnitizationNoetherianStatements.md)
states, for `[CommRing R]` and a bilinear nonunital `R`-algebra `A`:

```lean
IsNoetherianRing (Unitization R A) ↔
  IsNoetherianRing R ∧
    IsNoetherian (Unitization R A) (RingHom.ker (Unitization.fstHom R A))
```

This is `KernelCriterionStatement`. `NoetherianScalarCriterionStatement`
drops the first conjunct when `R` is Noetherian, and
`FieldCriterionStatement` specializes it to a field. The general criterion
does not assume that `R` is Noetherian. The
[proof](../../Langlands/Algebra/UnitizationNoetherianProof.md),
`UnitizationNoetherian.noetherian_iff_kernel` with aggregate
`unitizationNoetherian`, obtains `R` as a quotient along the surjective scalar
projection; the kernel is Noetherian as an ideal of a Noetherian ring. For the
converse it makes `R` a unitized module along the
projection, shows that it is Noetherian over the unitization by
`isNoetherian_of_tower`, and applies `isNoetherian_of_range_eq_ker` to the
inclusion of the kernel and the projection.

### Regular module and kernel

The definition
`Langlands.Algebra.UnitizationRegularKernel.regularKernelEquiv`
([module](../../Langlands/Algebra/UnitizationRegularKernel.md)) takes a
supplied `Module (Unitization R A) A` satisfying
`u • a = u.fst • a + u.snd * a`. It is the unitized-linear equivalence from
`A` to `RingHom.ker (Unitization.fstHom R A)` sending `a` to
`Unitization.inr a`, with inverse `x ↦ x.val.snd`. Four `simp` lemmas record
its value, coordinates and inverse. The module adds no general constructor of
that action.

### Regular and left-ideal criteria

[`UnitizationIdealNoetherianStatements`](../../Langlands/Algebra/UnitizationIdealNoetherianStatements.md)
has three components, all with the regular coordinate law above:

1. `RegularCriterionStatement`: `IsNoetherianRing (Unitization R A)` holds
   exactly when `R` is Noetherian and `A` is a Noetherian unitized module;
2. `ScalarIdealCriterionStatement`: over a Noetherian `R`, with
   `IsScalarTower R (Unitization R A) A`, the unitization is a Noetherian ring
   exactly when every `R`-submodule `P` of `A` closed under left
   multiplication by `A` contains a finite `S` such that `P ≤ Q` for every such
   `Q ⊇ S`;
3. `AdditiveIdealCriterionStatement`: over `ℤ`, the same condition ranges over
   all additive subgroups of `A` closed under left multiplication.

The statement's author qualification records that the scalar-tower premise
of component 2 follows from the regular law and `IsScalarTower R A A`, so it
does not restrict the statement. The
[proof](../../Langlands/Algebra/UnitizationIdealNoetherianProof.md),
`UnitizationIdealNoetherian.unitizationIdealNoetherian`, composes:

- `noetherian_iff_scalar_and_regular`: the kernel criterion, rewritten through
  `regularKernelEquiv`;
- `noetherian_iff_regular`: that criterion when `R` is Noetherian;
- `noetherian_iff_scalar_stable_ideals`: then
  `UnitizationStableGeneration.noetherian_iff_stable_generators` with
  `M = A` and `ρ = NonUnitalAlgHom.lmul R A`;
- `noetherian_iff_additive_stable_ideals`: over `ℤ`, then
  `AdditiveUnitizationGeneration.noetherian_iff_additive_stable_generators`
  with left multiplication as `A →ₙ+* AddMonoid.End A`.

The scalar-linear and additive left-ideal criteria are proved separately.
No equivalence between their two families of ideals is asserted.

## 4. Zero-action separation

[`UnitizationZeroActionFinitenessStatements`](../../Langlands/Algebra/UnitizationZeroActionFinitenessStatements.md)
uses the zero original action on the complex line `ℂ`:

- `ComplexZeroActionStatement`: for every bilinear nonunital complex algebra
  `A`, the action `CompatibleUnitization.module (0 : A →ₙₐ[ℂ] Module.End ℂ ℂ)`
  makes `ℂ` a finite and Noetherian `Unitization ℂ A`-module;
- `IntegerZeroActionStatement`: for every nonunital ring `A`, the action
  `CompatibleUnitization.module (0 : A →ₙₐ[ℤ] Module.End ℤ ℂ)` makes `ℂ` a
  `Unitization ℤ A`-module that is neither finite nor Noetherian.

The [proof](../../Langlands/Algebra/UnitizationZeroActionFiniteness.md),
`UnitizationZeroActionFiniteness.zeroActionFiniteness`, transfers finiteness
and Noetherianity of `ℂ` over itself along `CompatibleUnitization.isScalarTower`
in the complex case. In the integer case, the identity of `ℂ` is semilinear
along `Unitization.fstHom ℤ A`. Finiteness would therefore make `ℂ` a finite
`ℤ`-module, hence countable, contradicting `not_countable_complex`.
Noetherianity would imply that finiteness.

The pair proves only these two unitized facts. They show that, for the same
carrier and the same zero original action, unitized finiteness depends on the
scalar ring chosen for the unitization. The pair does not itself compare
categorical predicates, does not supply a counterexample to the book and
does not select the author's convention.

## 5. Published downstream uses

| Published declaration | Module | Uses |
| --- | --- | --- |
| `Langlands.Algebra.NonUnitalSubmodule.intUnitizedOrderIso` | [`IntegerNonUnitalSubmodule`](../../Langlands/Algebra/IntegerNonUnitalSubmodule.md) | `CompatibleUnitization.submoduleOrderIso` for the integer-compatible action |
| `Langlands.Algebra.CompatibleUnitization.compatibleSimpleUnitization` | [`NonUnitalSimplicityProof`](../../Langlands/Algebra/NonUnitalSimplicityProof.md) | transports `IsSimpleOrder` along `submoduleOrderIso ρ` |
| `Langlands.Renard.SourceFiniteLocalization.unitizedSubobjectOrderIso` and `compatibleReading` | [`RenardSourceFiniteLocalizationProof`](../../Langlands/Algebra/RenardSourceFiniteLocalizationProof.md) | `submoduleOrderIso M.action`; `UnitizationIdealNoetherian.noetherian_iff_scalar_and_regular ℂ B` for the regular action |
| `Langlands.Renard.AlgebraActionLocalization.stableIdealFiniteLocalization` | [`RenardStableIdealFiniteLocalizationProof`](../../Langlands/Algebra/RenardStableIdealFiniteLocalizationProof.md) | `UnitizationIdealNoetherian.scalarIdealCriterion ℂ B`; `UnitizationStableGeneration.moduleGeneration` for V and for its actual localization |
| `Langlands.Algebra.NonUnitalModuleFiniteness.finiteType_iff_original_stable_generators` and `noetherianObject_iff_original_stable_generators` | [`NonUnitalModuleFinitenessProof`](../../Langlands/Algebra/NonUnitalModuleFinitenessProof.md) | `IntegerOriginalSubmoduleGeneration.finite_iff_original_stable_generators` and `noetherian_iff_original_stable_generators` |

The C.II audit describes the two localization proofs. The [original-module progress
note](category-module-progress.md) describes the object-finiteness proof.
`NonUnitalModuleFinitenessStatements` imports the original generation
statements, and `UnitizationIdealNoetherianProof` imports the kernel,
regular-kernel and both supplied-action generation proofs. At Library
`ded343f9`, no module imports the zero-action pair.

## 6. In the Library

All fourteen modules are published; this note documents them.

| Module | First appeared at Library commit |
| --- | --- |
| Unitized submodule comparison (definition) | `914d13e3395c5a4417f36ffd7646c45c721a4b3e` |
| Scalar stable-generation statement | `65f39f42712a45624ccc76ac5da7b60f52ebcd6f` |
| Scalar stable-generation proof | `f4b4c23a7ab185fd0e15d16d2864b818a083a194` |
| Additive stable-generation statement | `65f39f42712a45624ccc76ac5da7b60f52ebcd6f` |
| Additive stable-generation proof | `4021bb1d1ec99e65990e08addda3ade7caa73058` |
| Original-module generation statement | `2b8beb8bd3034a40aeb5dc7b2de17b607fae8d11` |
| Original-module generation proof | `333fb3981b648b8ba9f29c1123c27ef3d8626c90` |
| Kernel criterion statement | `65f39f42712a45624ccc76ac5da7b60f52ebcd6f` |
| Kernel criterion proof | `f4b4c23a7ab185fd0e15d16d2864b818a083a194` |
| Regular-kernel equivalence (definition) | `65f39f42712a45624ccc76ac5da7b60f52ebcd6f` |
| Regular and left-ideal criteria statement | `65f39f42712a45624ccc76ac5da7b60f52ebcd6f` |
| Regular and left-ideal criteria proof | `cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b` |
| Zero-action separation statement | `3987c3d7445531c2c7f784464a3fd47061ba0865` |
| Zero-action separation proof | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |

Each proof was checked by a Lake build against its exact target, with the
statement and its inputs unchanged. Each statement or definition module was
checked by a Lake build and for declaration kinds; a statement module proves
nothing. Several modules record derived or statement-only scope. The
regular-kernel equivalence records that the regular action is a supplied
hypothesis.

The 29 Lean/Markdown files of these modules were checked at Library
`ded343f95a7ebe4954d12a37616f22db56be249c`. Each equals its first published
version. The unitized submodule comparison (definition) also updated
`CompatibleUnitization.md`.

| File | SHA256 at Library `ded343f9` |
| --- | --- |
| `Langlands/Algebra/CompatibleUnitization.md` | `2ae4d09143e2f44a646744e4d1f7940877fc20ace5402a3111c0e1690cb0ead8` |
| `Langlands/Algebra/CompatibleUnitizationSubmodule.lean` | `8478b62934a862430fdd0d6a1bdef40ee00c16d5369dd87168298c07d26a6cb3` |
| `Langlands/Algebra/CompatibleUnitizationSubmodule.md` | `1aebcfa5b0f82330996a6447cfb5db95cc0347194c8672b5c217fccece829dfb` |
| `Langlands/Algebra/UnitizationIdealNoetherianStatements.lean` | `48d95e2d25787f25a255545ad281d4d8778164b3d868e20516d247809584baf2` |
| `Langlands/Algebra/UnitizationIdealNoetherianStatements.md` | `9312e4adf78bc949ca782e087786748a01fda25791f5ebef1a6281a153f776ae` |
| `Langlands/Algebra/UnitizationIdealNoetherianProof.lean` | `14c40592d2e9c126775b6a5185a45a07cae0674418abd1f450369087b99bd6d3` |
| `Langlands/Algebra/UnitizationIdealNoetherianProof.md` | `f801f363ceee7549d43b4eb0d4e9c5fde3c27b7cf915357296143365e4368949` |
| `Langlands/Algebra/UnitizationNoetherianStatements.lean` | `a0465d2c555d136c0c123d1391f36a5023f45c99e73ef6fcb6e4f976171fb545` |
| `Langlands/Algebra/UnitizationNoetherianStatements.md` | `1794b4d682e588eb5b9a0078d7d40066c8d485981c4c692225bb58baaacb50f6` |
| `Langlands/Algebra/UnitizationNoetherianProof.lean` | `0d3b83c967731e6a4a3de7b836aec2bb081bad4b4d684e14f6e8c5795d0cf1db` |
| `Langlands/Algebra/UnitizationNoetherianProof.md` | `90cb6ac39d295c5c62bf500ca3919d7efddb380085dd49779a1fdc86ec19104a` |
| `Langlands/Algebra/UnitizationRegularKernel.lean` | `7ac70fbfd98b38d012bbfebf600df1b81b9f327ecbd2b616f640e2602e768e1d` |
| `Langlands/Algebra/UnitizationRegularKernel.md` | `f213fb84d8fc7e8cc4a8ebd5923b774be645bcfcfcdc67b33a810e23249c4083` |
| `Langlands/Algebra/UnitizationZeroActionFinitenessStatements.lean` | `9bbfd83cce617fdfc2efebe85ad8c5f8d427bf8d08d315a701e214545f8ace8f` |
| `Langlands/Algebra/UnitizationZeroActionFinitenessStatements.md` | `ee76cb4b00d01ae1d236176aa4a43ae175fb52e1953d0431844e3fbba74611e7` |
| `Langlands/Algebra/UnitizationZeroActionFiniteness.lean` | `3e8c6d13d031e7b34a4d4c0eaf666c2d61d04e58b3f3efe119d228f3ef33e79d` |
| `Langlands/Algebra/UnitizationZeroActionFiniteness.md` | `50c9a32b6fcd157d1af775dbc97b338da1d881940ae5a9b59cb219bda2cf54e5` |
| `Langlands/Algebra/UnitizationStableGenerationStatements.lean` | `b9053a321b6019b1bb1f7d1b39e92e63c73cc5764545f48f43e5c48dbfedb8bb` |
| `Langlands/Algebra/UnitizationStableGenerationStatements.md` | `6f889509b006a9ba2a3d86c831af2c38331c67eba68af1ee516a4425c510a4e3` |
| `Langlands/Algebra/UnitizationStableGenerationProof.lean` | `8990808f1f5977164d890ebde326e8c6fdac43ac3e6fc4e88326510a380205b6` |
| `Langlands/Algebra/UnitizationStableGenerationProof.md` | `b59702f5c64e4a2f393852826abc9ab7557eebb7c7d5af4c654871f5122c40c9` |
| `Langlands/Algebra/AdditiveUnitizationGenerationStatements.lean` | `13435ff9756f73dd425eeb15949a0c247a8e7499f80ed11ae3cf28e93eb3f7d9` |
| `Langlands/Algebra/AdditiveUnitizationGenerationStatements.md` | `c1cf4aa37dd9dd928991b6d2359edff281c2893410f9d3973b318a2dab2d1e22` |
| `Langlands/Algebra/AdditiveUnitizationGenerationProof.lean` | `b943e39ff71152ce69690aafea7d26ee15d8a6873a54851874b42ba2ed0113d0` |
| `Langlands/Algebra/AdditiveUnitizationGenerationProof.md` | `6fdf67cf12de081033be48889ed7b07fd2db1493e9b6f03b3aff41cba0349415` |
| `Langlands/Algebra/IntegerOriginalSubmoduleGenerationStatements.lean` | `d6514bccea2faa21250cfa97f56f4326ad597403c85ab038cbbd5443beba2329` |
| `Langlands/Algebra/IntegerOriginalSubmoduleGenerationStatements.md` | `860f6578339f72d1a5f2859d23d3c4fca655aa5bc068880e3f47f9f40e76b65b` |
| `Langlands/Algebra/IntegerOriginalSubmoduleGenerationProof.lean` | `e3aa8f3b36a262916778c235e11d940a61fe238c32ba04842bfa9d059ca4e115` |
| `Langlands/Algebra/IntegerOriginalSubmoduleGenerationProof.md` | `a5ba5fac254fca188f2eb12e8825f2654ace04d847c46a0242c248ce028f1540` |

## Scope

These checks concern the listed modules. They do not resolve
which reading of Renard's nonunital Noetherian and finite-type phrases is
meant; that comparison stays with the [C.II audit](stable-quotients.md) and
the [finiteness source audit](nonunital-finiteness-sources.md). The
unitized tensor comparison of I.2.1 is outside this note; the
[I.2.1 assertion map](unitization-tensor-progress.md) records it. The whole-book
coverage ([coverage.md](coverage.md)) keeps every other assertion, and this note declares no
section, appendix or book completion.

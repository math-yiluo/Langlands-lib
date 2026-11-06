# Renard C.II: quotient maps and finite localization

Worker 709, updated 6 November 2026, coordinated with Worker 6 under whole-book
task `f5d1f399-a1f8-4ab5-a981-90b92abd4857` revision 3. This passage audit
records verified publications for the stable-endomorphism lemma, its auxiliary
quotient sequence and actual localization constructions. It also distinguishes
the published internal finite-localization theorems from the unresolved
source-facing nonunital finiteness convention. The additive-to-scalar comparison
below supplies explicit sufficient conditions for the actual localization.
The separate additive stable-image proof identifies that localization for
every supplied positive stable power, without finiteness hypotheses.
Published statements pose the final proposition under each of three
candidate finiteness readings, and their published exact proof establishes
all three. Neither the statements nor the proof chooses the author's
convention.
This update also records four further published internal
statement/proof pairs: the compatible stability criteria, the Noetherian
localization core, ordinary-module actual-localization stability and the
canonical compatible stable image. The last three supply steps of the
localization results below.
This documentation records partial Appendix C coverage; the whole-book
formalization remains open.

## Source and reading

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`. The readable original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
with SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
independently rechecked for this audit. It has 296 PDF pages; the passages here
have PDF page = printed page + 6.

Worker 709 read PDF282–285 and visually checked the quotient formulas on
PDF284 and the final proposition on PDF285. A.III.1 on PDF258–259 and the
global module conventions on PDF12 were also read, including their rendered
pages. The registered supplementary author errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF18–19 were checked. This limited errata reading concerns the older edition;
the 2026 original governs the formalization.

## Successive quotients in Lemma (iv)

For an arbitrary complex vector space V and endomorphism t, put
N_k = ker(t^k) and I_k = range(t^k), for k in the natural numbers, including zero.
The proof on printed278/PDF284 uses actual quotient spaces
E_k = N_(k+1)/N_k and F_k = I_k/I_(k+1).
Each denominator is a submodule of its numerator via the actual inclusion.
There is no finite-dimensionality or eventual-stability hypothesis on these
constructions or on the exact-sequence assertions below.

Write alpha_k, beta_k and gamma_k for the arrows induced respectively by t,
t^k and t. In namespace `Langlands.LinearAlgebra.StableEndomorphism`, the
actual spaces are `KerQuotient t k` and `RangeQuotient t k`; the arrows are
`kerQuotientShift t k`, `kerToRangeQuotient t k` and
`rangeQuotientShift t k`. Their constructions and representative formulas
are in
[StableEndomorphismQuotients](../../Langlands/LinearAlgebra/StableEndomorphismQuotients.md).

| Source assertion, printed278/PDF284 | Exact content | Published coverage |
| --- | --- | --- |
| Quotients and arrows | alpha_k : E_(k+1) -> E_k, beta_k : E_k -> F_k, gamma_k : F_k -> F_(k+1), with the indicated representative formulas | Actual constructions imported unchanged by the published exactness proof |
| Kernel of beta_k | (N_k + (range(t) intersect N_(k+1)))/N_k, as the corresponding submodule of E_k | Clause 2 of `PowerQuotientExactnessAt t k` |
| Image of beta_k | (I_(k+1) + t^k(N_(k+1)))/I_(k+1), as a submodule of F_k | Clause 3 |
| First arrow | alpha_k is injective; its image is (N_k + t(N_(k+2)))/N_k, equal to the displayed kernel of beta_k | Clauses 4–6; the corrected k+2 index is retained |
| Last arrow | gamma_k is surjective; its kernel equals the displayed image of beta_k | Clauses 7–8 |
| Five-term sequence | 0 -> E_(k+1) -> E_k -> F_k -> F_(k+1) -> 0 is exact | Clauses 9–10 give the two range/kernel equalities, with endpoints from clauses 4 and 7 |

The theorem `powerQuotientExactSequenceStatements` in
[StableEndomorphismQuotientProofs](../../Langlands/LinearAlgebra/StableEndomorphismQuotientProofs.md)
has exactly the closed type `PowerQuotientExactSequenceStatements.{uR, uV}`.
It proves all ten clauses for every module over an arbitrary, possibly
noncommutative ring, with independent coefficient and carrier universes and
every natural index, including zero. The aggregate also includes the explicit
complex-vector-space specialization. The ring generality is internal derived
content. No stability or finiteness premise is added. The proof uses direct
element calculations on the actual quotients.

The first-arrow paragraph initially describes the composite
N_(k+2) -> N_(k+1) -> E_k. Its kernel is N_(k+1); passing to the quotient
gives the injective arrow from E_(k+1). Assigning that prequotient kernel to the
induced quotient arrow would misstate the assertion. The 2010 errata's
correction to the image index N_(k+2) is already incorporated in the 2026 text.
The last repeated I_k in the common-index proof is a prose typo; the current
statement Markdown already records the increasing/decreasing comparison.

## Stable-endomorphism lemma

The same namespace in
[StableEndomorphismStatements](../../Langlands/LinearAlgebra/StableEndomorphismStatements.md)
defines `Stable`, `EventuallyStable` and six Prop-valued targets, aggregated in
`StableEndomorphismStatement`. These cover the complementary-kernel/range
criterion, exact-row transfer, monotonicity and the common first stabilization
index for arbitrary-dimensional complex spaces with independent carrier
universes. The theorem `stableEndomorphism` in
[StableEndomorphismProofs](../../Langlands/LinearAlgebra/StableEndomorphismProofs.md)
proves exactly `StableEndomorphismStatement.{uV, uA, uB, uC}`. The accepted
proof retains the common **first** stabilization index, one-sided exact-row
hypotheses and all four independent carrier universes; it adds no dimension or
finiteness hypothesis. This lemma aggregate and the auxiliary quotient
aggregate above are separate published results. Coverage of one is not used
as evidence for the other.

The internal compatible-action adapter is also proved. In namespace
`Langlands.Algebra.CompatiblePowerStabilization`, the theorem
`compatiblePowerStabilization` proves exactly
`CompatiblePowerStabilizationStatements.{uB, uV}`. Its
[statement](../../Langlands/Algebra/CompatiblePowerStabilizationStatements.md)
and [proof](../../Langlands/Algebra/CompatiblePowerStabilizationProofs.md)
use an actual action `ρ : B →ₙₐ[ℂ] Module.End ℂ V`, an actual
`LinearIntertwiner ρ ρ`, and the locally selected
`CompatibleUnitization.module ρ`. The powers come from this unitized
endomorphism monoid and return through the published intertwiner
correspondence. Kernels and ranges are actual compatible submodules.

The four conjuncts give underlying complex-linear power coherence,
unconditional increasing kernels and decreasing ranges, adjacent-equality
equivalence and persistence under eventual stability, and the common first
stabilization index. The eventual-stability witness is positive; the first
index may be zero. Algebra and carrier universes remain independent, and
possibly noncommutative nonunital algebras, degenerate actions and arbitrary
dimensions are included. Worker 691 proves power coherence by induction,
then transports Worker 277's published complex-linear chain theorems through
the injective, order-reflecting compatible-submodule forgetful map. This
adapter does not prove the compatible square/complement/exact-row
criteria, which are the separate unit described next. Nor does it prove
the auxiliary quotient sequences or the source finiteness comparison.

### Compatible stability criteria

In namespace `Langlands.Algebra.CompatibleStability`, the theorem
`compatibleStability` proves exactly
`CompatibleStabilityStatements.{uB, uV, uA, uM, uC}`. Its
[statement](../../Langlands/Algebra/CompatibleStabilityStatements.md),
by Workers 709 and 345, and
[proof](../../Langlands/Algebra/CompatibleStabilityProofs.md), by
Worker 1044, specialize the definition and Lemma (i)–(iii) on
printed276–278/PDF282–284 to actual compatible actions
`ρ : B →ₙₐ[ℂ] Module.End ℂ V` of a possibly noncommutative, nonunital
complex algebra B. The maps are actual `LinearIntertwiner`s with their
compatible kernels and ranges. The four conjuncts are:

1. `Stable f.toLinearMap` holds if and only if the compatible kernels and
   ranges of f and `f.comp f` are equal;
2. `Stable f.toLinearMap` holds if and only if `IsCompl f.ker f.range`
   in the compatible-submodule lattice;
3. right-exact rows: if `phi.range = psi.ker`, psi is surjective, both
   squares commute and fA and fM are stable, then fC is stable;
4. left-exact rows: if phi is injective, `phi.range = psi.ker`, both
   squares commute and fM and fC are stable, then fA is stable.

Each row assumes exactness only at the end it names: surjectivity of psi
or injectivity of phi. The three carriers of a row have independent
universes. The proof reduces the first conjunct to the definition of
`Stable`. For the other three it applies the published complex-linear
results `stable_iff_isCompl`, `stable_of_rightExact` and
`stable_of_leftExact` to the underlying linear maps. It transports
kernels, ranges and complementarity through
`CompatibleSubmodule.toSubmodule`, which preserves infima, suprema,
bottom and top and is injective. No
published Lean module imports this proof; the localization results below
use other routes.

## Actual localization prerequisites

The following replaces the earlier construction backlog. It credits the
actual public interfaces at their verified scope.

| Passage or prerequisite | Current interface or task | Remaining boundary |
| --- | --- | --- |
| A.III.1 example 4, printed252/PDF258 | `Langlands.Renard.ModuleLocalization` in `Langlands/Algebra/RenardModuleLocalization.lean`: actual `LocalizedModule`, `IsSLocal`, inverse action, `factor`, representative, factorization, uniqueness and comparison laws | Full-subcategory and universal-arrow category packaging remain separate |
| First assertion of example 5, printed252/PDF258 | `Langlands.Algebra.PolynomialEndomorphism.equivalence` and `fieldEquivalence`, with actual evaluation actions and linear-intertwiner correspondence | The separate localization construction is given in the next row |
| Localization at powers of X in example 5, printed252–253/PDF258–259 | `Langlands.Renard.EndomorphismLocalization.Localized`, `iota`, `localizedEnd`, `localizedInv`, `localizedEquiv`, `frac`, `factor`, `hasUniversalProperty` | Actual scalar-linear construction and universal property are public; categorical packaging is separately tracked |
| Final sentence of example 5 | `Langlands.Renard.AlgebraActionLocalization.localizedAction` and `fieldLocalizedAction`, with fraction/canonical-map laws, actual intertwiners, inverse commutation and intrinsic uniqueness of the action extension | Construction is public for possibly noncommutative and nonunital actions. The arbitrary-target B-linear universal property is a separate assertion, not supplied by the action-construction receipt |
| Unnumbered lemma and corollary, printed253/PDF259 | Separately tracked assertions over the actual localization | Injective case; K = union_n ker(a^n); induced injective quotient action; compatible quotient-localization identification; inverse-iterate exhaustion and its converse; surjective canonical map gives localization isomorphic to V/K. This note does not re-audit each successor's coverage |

The example-4 artifact 9652aa10-f220-4739-a962-777ceedbd047 was verified as
accepted and public at commit 6e568b3024e33889aa9fcaae1e910b0ff99f9b59; the
exact public Lean/Markdown pair was read. The construction retains arbitrary
commutative coefficient rings, arbitrary unital modules, independent source
and target universes, and zero denominators. Its formal counterexample explains
why invertibility of a scalar endomorphism does not imply an inverse coefficient
in the original ring. Preserve Worker 618's example-4 task ownership
08bb9432-0606-45f0-a725-70e8b0dda929 and Worker 490's polynomial-equivalence
work under task 959d6ee1-9a1f-4812-a911-7cf695869dd1.

The actual
[endomorphism-localization pair](../../Langlands/Algebra/RenardEndomorphismLocalization.md)
was read in full. It retains arbitrary commutative coefficient rings and
independent coefficient, source and target universes; the field specialization
matches the vector-space construction. The canonical map need not be
injective. The localized operator is an actual automorphism.

The
[algebra-action pair](../../Langlands/Algebra/RenardAlgebraActionLocalization.md)
was also read in full. It implements the previously proposed route: extend each
commuting action endomorphism by the published scalar-linear `factor`, then
prove the action laws on fractions. Its source specialization retains both
bilinearity classes on the arbitrary field algebra. No unit-action law,
nondegeneracy or finiteness is required. `iotaIntertwiner`,
`localizedEndIntertwiner` and `localizedInvIntertwiner` are actual compatible
linear intertwiners. The named ambient-action adapters require local selection;
the companion explains scalar-instance choices when coefficient and algebra
types coincide. Intrinsic uniqueness of this action extension does not itself
assert B-linearity of a factor into an arbitrary target.

## Noetherian core and ordinary-module stability

Two published internal units for ordinary unital modules prepare the
final proposition. Both are derived content motivated by printed279/PDF285,
with the localization of A.III.1 example 5 on printed252–253/PDF258–259.
Neither is a translation of the source proposition.

### Noetherian localization core

In namespace `Langlands.LinearAlgebra.NoetherianLocalizationCore`, the
theorem `noetherianLocalizationCore` proves exactly
`NoetherianLocalizationCoreStatement.{uR, uM, uN}`. Its
[statement](../../Langlands/LinearAlgebra/NoetherianLocalizationCoreStatements.md)
was derived by Worker 709; Worker 735 rechecked it and submitted it with
Worker 709 as coauthor. The
[proof](../../Langlands/LinearAlgebra/NoetherianLocalizationCoreProof.md)
was written by Worker 709, then checked and submitted by Worker 735 under
proof task `d5b1de4a-fa7c-47b9-9f10-d8a35ac539c0`. The coefficient ring is
an arbitrary unital ring, not necessarily commutative or Noetherian. The
ring, source and target universes are independent. The three conjuncts
are:

1. an actual linear automorphism of a Noetherian module that maps a
   submodule into itself also maps it into itself under the inverse;
2. if a linear map f intertwines a source endomorphism a with an
   automorphism e of a Noetherian target, and for every target vector y
   some `(e ^ n) y` lies in the range of f, then f is surjective;
3. if in addition the source is Noetherian and every vector killed by f is
   killed by some power of a, then f is surjective and one positive n gives
   `ker f = ker (a ^ n)` together with equality of the kernels and of the
   ranges of `a ^ n` and its square.

The proof uses a quotient-Hopfian argument instead of Renard's
inverse-polynomial argument. The automorphism descends to a surjective
endomorphism of the Noetherian quotient by the submodule, which is
therefore injective. The kernel bound comes from Mathlib's stabilization
of the power-kernel union in a Noetherian module. The published modules
importing this proof are the actual-localization stability proof below
and the two unitized Noetherian adapter proofs described later.

### Actual-localization stability

In namespace `Langlands.Renard.EndomorphismLocalization`, the theorem
`actualLocalizationStabilityStatements` proves exactly
`ActualLocalizationStabilityStatements.{uR, uV}`. Its
[statement](../../Langlands/Algebra/RenardLocalizationStabilityStatements.md)
is by Workers 709 and 977, and its
[proof](../../Langlands/Algebra/RenardLocalizationStabilityProof.md) is by
Worker 977 under proof task `c9d7a084-4b9f-4094-a4d9-88126e384078`. The
data are an arbitrary commutative ring R, an ordinary unital R-module V,
an endomorphism a, and the actual `Localized a`, `iota a` and
`localizedEnd a` described above. Zero rings and modules of any size are
included. The parameterized predicate `StablePowerImageAt a n` says that
`ker (a ^ n)` and `range (a ^ n)` are complementary and that there is a
unique linear equivalence from `Localized a` to `range (a ^ n)` that
intertwines `localizedEnd a` with a and whose inverse is `iota a`
restricted to the range. The three conjuncts are:

1. `NoetherianActualLocalizationStatement`: if V and `Localized a` are
   Noetherian modules, `iota a` is surjective and one positive n gives
   `ker (iota a) = ker (a ^ n)` and stability of `a ^ n` in both kernel and
   range; neither ring Noetherianity nor finite generation is a premise;
2. `StablePowerImageStatement`: every positive n with
   `ker (a ^ n) = ker ((a ^ n) ^ 2)` and
   `range (a ^ n) = range ((a ^ n) ^ 2)` satisfies `StablePowerImageAt a n`,
   with no Noetherian or finiteness premise;
3. `FiniteActualLocalizationStatement`: over a Noetherian ring, finiteness
   of V and of `Localized a` gives the first conclusion together with
   `StablePowerImageAt a n` for every positive stable n.

The authors' scope remarks say that this is an ordinary unital-module
specialization and internal strengthening, and that the full possibly
nonunital complex-algebra proposition is not stated here. The first
conjunct applies the Noetherian core to `iota a`, the automorphism
`localizedEquiv a`, fraction exhaustion and the kernel criterion
`iota_eq_zero_iff`. The second is a direct Fitting argument: stability
gives the complement, and the canonical map restricted to the range is
bijective. The third obtains Noetherian modules by Mathlib's
`isNoetherian_of_isNoetherianRing_of_finite` and combines the first two.

The published pair differs from the frozen bundle in one respect. The
frozen proof proved a local `iota_eq_zero_iff` helper. The published
proof instead imports
`Langlands.Algebra.RenardEndomorphismLocalizationKernelProof` and reuses
`Langlands.Renard.EndomorphismLocalization.iota_eq_zero_iff`, and its
Markdown describes that reuse. This proof and the kernel and
exhaustion proof `16d1ce28-f650-452d-8a80-7fd08a520767`, recorded in the
[endomorphism-localization audit](endomorphism-localization.md), were
published in the same commit `b7a6ea71635c439ae131d5b451e5f403e32dc1c7`. The
second conjunct is used at ℂ by the canonical compatible stable image
below and at ℤ by the additive stable-image proof described later.

## Canonical compatible stable image

In namespace `Langlands.Renard.AlgebraActionLocalization`, the theorem
`compatibleStablePowerImageStatement` proves exactly
`CompatibleStablePowerImageStatement.{uB, uV}`. Its
[statement](../../Langlands/Algebra/RenardCompatibleStableImageStatements.md)
is by Workers 709 and 977, and its
[proof](../../Langlands/Algebra/RenardCompatibleStableImageProof.md) is by
Workers 490 and 926 under proof task
`80c2c945-109d-4be9-bf55-50bd374aa1fa`. For an actual compatible action
ρ of a possibly noncommutative, nonunital complex algebra B, a
self-intertwiner f with `a = f.toLinearMap`, and every n with `0 < n` and
`Stable (a ^ n)`, it gives `CompatibleStablePowerImageAt ρ f n`. Here K
and I are the compatible kernel and range of the n-th power taken in the
locally selected `CompatibleUnitization.module ρ`. The predicate says that
K and I are complementary compatible submodules. It also gives a unique
complex-linear equivalence from the actual `Localized a` to
`I.toSubmodule` satisfying three equations. It carries the actual
localized action to the restricted action of I, it intertwines
`localizedEnd a` with a, and its inverse is `iota a` restricted to I.

The authors' scope remarks say that this is an internal finiteness-free
refinement of the identification clause only. The source's eventual
stability under its finiteness hypotheses is not stated here. There is
no unit-law, nondegeneracy, dimension or finiteness premise. The proof
identifies the unitized powers with the ordinary powers of a and applies
`stablePowerImageStatement` at ℂ. It reflects complementarity through
the injective compatible-submodule forgetful map. It then defines the
equivalence as the inverse of the bijective restricted canonical map.
The action equation follows from `localizedAction_iota` and the operator
equation from `iota_intertwines`. Uniqueness follows from the inverse
normalization. The finite-localization proof below applies its helper
`CompatibleStableImageProof.compatibleStablePowerImageAt_of_stable`.

## Final finite-localization proposition

The proposition on printed279/PDF285 takes a commutative noetherian complex
algebra B, a finite B-module L and a B-linear endomorphism a. Its actual
localization L_a is also assumed finite over B. It concludes that a is
eventually stable. For every positive n with a^n stable, set K = ker(a^n)
and I = range(a^n): the required conclusions are L = K direct-sum I and an
isomorphism of the localized pair with (I, a restricted to I), intertwining
the actual operators. Finite-dimensionality over the complex numbers is not
a source hypothesis.

There is now a published **internal** theorem
`Langlands.Renard.AlgebraActionLocalization.stableIdealFiniteLocalization`
of the exact closed type `StableIdealFiniteLocalizationStatement.{uB, uV}`.
Its
[statement](../../Langlands/Algebra/RenardStableIdealFiniteLocalizationStatements.md)
and
[proof](../../Langlands/Algebra/RenardStableIdealFiniteLocalizationProof.md)
use the actual localized carrier and compatible action. Its hypotheses say:

- Every complex-linear left ideal of B is generated by a finite subset under
  complex-linear span and the original left multiplication.
- V is generated by a finite subset under complex-linear span and the original
  B-action.
- Its actual localization is generated in the same sense under its actual
  localized action.

The algebra and carrier universes remain independent. B may be noncommutative
and nonunital. There is no added nondegeneracy or finite complex dimension.
The first conclusion is `CompatibleLocalizationStabilizationAt ρ f`:
surjectivity of the actual canonical map and one positive exponent giving both
its compatible kernel and stability of the underlying power. For **every**
positive stable exponent, `CompatibleStablePowerImageAt ρ f n` gives
complementary compatible kernel and image and a unique complex-linear
equivalence from the actual localization to that image. The equivalence
intertwines both the action and the operators, and its inverse is the
restriction of the actual canonical map.

The Lean proof converts the three explicit hypotheses to Noetherianity of the
actual complex unitization and finiteness of the two actual unitized modules.
It then applies `stabilizationAt_of_finite` from the complex-compatible
unitized Noetherian adapter described below, which rests on the
quotient-Hopfian Noetherian core. The stable-image clause is
`CompatibleStableImageProof.compatibleStablePowerImageAt_of_stable` from
the canonical compatible stable image above. Renard instead argues through finiteness of End_B(L_a), an inverse
polynomial and invariance of the canonical image. The implemented proof route
need not follow that argument.

The source-facing proposition remains open at the convention comparison:
complex-linear stable ideals/subspaces differ from arbitrary additive
ideals/subgroups. The internal theorem does not silently choose a meaning for
Renard's Noetherian and finite-type phrases. The
[finiteness source audit](nonunital-finiteness-sources.md) records the checked
unital passages in Pareigis and the supplied Douady edition, and their limits
for this nonunital question. Those limits persist after publication of the
internal theorem.

### Statements under the three candidate readings

Worker 709's statement unit
[RenardSourceFiniteLocalizationStatements](../../Langlands/Algebra/RenardSourceFiniteLocalizationStatements.md)
states the proposition once for each candidate model named in the
finiteness source audit. All three take a commutative, possibly nonunital
complex algebra B, a complex vector space V with an actual compatible
action and a B-linear endomorphism f, at independent universes uB and uV.
Each concludes `SourceConclusion ρ f`: `EventuallyStable f.toLinearMap`,
and `CompatibleStablePowerImageAt ρ f n` for every positive stable
exponent n. The readings differ only in the meaning of the hypotheses:

1. `AdditiveReadingStatement`: the published categorical Noetherian and
   finite-type predicates of A.I.3 for actual objects of
   `NonUnitalModuleCat B`, whose subobjects are stable additive subgroups;
2. `CompatibleReadingStatement`: the same predicates in `ActionModuleCat ℂ B`,
   whose morphisms are complex-linear intertwiners;
3. `UnitizationReadingStatement`: `IsNoetherianRing (Unitization ℂ B)` and
   `Module.Finite` over that ring for V and its actual localization.

`SourceFiniteLocalizationStatements.{uB,uV}` is their conjunction, in that
order. These are derived formulations. A proof of all three would give the
proposition whichever of these models is meant, but would not identify the
author's convention. No unit, unit-action law, nondegeneracy or finite
complex dimension is assumed.

[RenardSourceFiniteLocalizationProof](../../Langlands/Algebra/RenardSourceFiniteLocalizationProof.md)
proves the unchanged aggregate as `sourceFiniteLocalizationStatements`,
with uB and uV independent and no added hypothesis. Worker 709 wrote the
proof draft. Worker 1581 checked its source correspondence and submitted
it under exact proof task `211bc556-3c01-4948-97c8-d2e3407747a9`
revision 1. The proof first builds an order isomorphism between the
categorical subobjects of an object of `ActionModuleCat` and its stable
subspaces, and composes it with the published unitized submodule
comparison. This turns the categorical Noetherian and finite-type
predicates in `ActionModuleCat ℂ B` into Noetherianity and finiteness of
the actual unitized modules. The additive reading applies the published
stable-generator characterizations in `NonUnitalModuleCat B` and then
`additiveIdealFiniteLocalization`. The compatible reading obtains a
Noetherian unitization ring from the regular action and applies
`stabilizationAt_of_finite`, which the unitization reading applies
directly. The published stable-image proof then supplies the stable-power
image clause for every positive stable exponent. The implemented route does
not follow Renard's argument through finiteness of the endomorphism module.
The proof establishes the conclusion under each of the three models; it
does not decide which model is the author's.

The [unitization criteria note](unitization-noetherian-criteria.md) records,
with receipts, the published units behind these steps and behind the internal
stable-ideal proof above. They include
`CompatibleUnitization.submoduleOrderIso`,
`UnitizationIdealNoetherian.noetherian_iff_scalar_and_regular` and
`scalarIdealCriterion`, `UnitizationStableGeneration.moduleGeneration`, and
the original-module generation comparisons used by the additive reading.

## Unitized Noetherian localization adapters

Two further published internal proof families isolate the Noetherian
conditions on the actual unitized modules. Each proves three conclusions
with different premises:

| Premises | Conclusion |
| --- | --- |
| Only the actual localized unitized module is Noetherian | The actual canonical map `iota a` is surjective; source and ring Noetherianity are not required. |
| Both actual unitized modules are Noetherian | The canonical map is surjective, and one positive exponent identifies its kernel with the power kernel and makes that same power stable in both kernel and range. |
| The unitization is a Noetherian ring and both actual unitized modules are finite | The same surjectivity and common positive exponent follow. |

For complex-compatible data, the theorem
`Langlands.Renard.AlgebraActionLocalization.compatibleLocalizationNoetherian`
proves the exact closed
`CompatibleLocalizationNoetherianStatements.{uB, uV}`. Its
[statement](../../Langlands/Algebra/RenardCompatibleLocalizationNoetherianStatements.md)
selects `CompatibleUnitization.module ρ` on V and
`CompatibleUnitization.module (localizedAction a ρ ha)` on the actual
`Localized a`. Its parameterized conclusion
`CompatibleLocalizationStabilizationAt ρ f` uses equality of actual
compatible kernels and the existing complex-linear `Stable (a ^ n)`.
There is no finite-dimensionality, commutativity, nondegeneracy or
nontriviality premise.

For original additive data, the theorem
`Langlands.Renard.AdditiveActionLocalization.additiveLocalizationNoetherian`
proves the exact closed
`AdditiveLocalizationNoetherianStatements.{uA, uV}`. Its
[statement](../../Langlands/Algebra/RenardAdditiveLocalizationNoetherianStatements.md)
takes an arbitrary nonunital ring A, an additive group V, its original
`NonUnitalModule A V` and an original `NonUnitalModuleHom A V V`.
It uses the canonical integer-compatible action and integer-linearization,
the actual localization over ℤ, and the actual actions of
`Unitization ℤ A`. Its conclusion is surjectivity and, for one `n > 0`,
the three integer-submodule equalities
`ker(iota a) = ker(a^n)`, `ker(a^n) = ker((a^n)^2)` and
`range(a^n) = range((a^n)^2)`.
The original action remains separate from canonical integer scalars,
including when A is ℤ and the original action is zero. No complex
vector-space structure is imposed.

Worker 735 authored both
[complex-compatible](../../Langlands/Algebra/RenardCompatibleLocalizationNoetherianProof.md)
and [additive](../../Langlands/Algebra/RenardAdditiveLocalizationNoetherianProof.md)
proofs. They build the unitized automorphism from the actual localized
operator and inverse. Actual fraction exhaustion, intertwining and the
canonical-map kernel criterion supply the hypotheses of the published
`NoetherianLocalizationCore` described above. The proof transports its kernel and range
equalities through unchanged functions and power coherence, retaining the
same positive exponent. The finite specializations use the ordinary
finite-module theorem over an arbitrary Noetherian ring. The additive
proof's helpers allow any commutative scalar ring and specialize to ℤ.

These adapters retain independent acting-ring and carrier universes.
Their Noetherian and finite hypotheses are explicit ordinary hypotheses
over the specified unitizations. They do not identify those hypotheses
with Renard's terminology, and neither aggregate contains a stable-image
identification. The compatible stable-image conclusions in the earlier
internal finite-localization theorem and the additive result below are
separate results. The complete source-facing C.II proposition remains open
at the convention comparison.

## Canonical stable image for original additive actions

The published theorem
`Langlands.Renard.AdditiveActionLocalization.additiveStablePowerImageStatement`
proves exactly
`Langlands.Renard.AdditiveActionLocalization.AdditiveStablePowerImageStatement.{uA, uV}`.
Its [statement](../../Langlands/Algebra/RenardAdditiveStableImageStatements.md),
authored by Workers 709 and 926, and
[proof](../../Langlands/Algebra/RenardAdditiveStableImageProof.md),
authored by Workers 490 and 926, give an internal, finiteness-free refinement
motivated by the stable-image conclusion on printed279/PDF285.

The data are an arbitrary nonunital ring A, an additive commutative group V
with its original `NonUnitalModule A V`, and an original additive
`NonUnitalModuleHom A V V`. Set
`a = f.toAddMonoidHom.toIntLinearMap`. For every supplied `n > 0`, assume
exactly `ker(a^n) = ker((a^n)^2)` and
`range(a^n) = range((a^n)^2)` as integer-submodule equalities.
The conclusion `AdditiveStablePowerImageAt f n` gives complementary
compatible kernel and image K and I of the actual unitized power, and a
unique integer-linear equivalence from the actual `Localized a` to
`I.toSubmodule`. It intertwines the actual localized action with the
restricted original action, and the actual localized operator with a.
Its inverse is the restriction of the actual canonical map `iota a`.
All three equations occur inside the unique-existence predicate;
uniqueness uses that inverse normalization.

The proof first establishes coherence of the converted unitized powers
with the ordinary integer-linear powers. It applies the published ordinary
stable-image theorem `stablePowerImageStatement`, described above, at ℤ.
It then reflects complementarity through the
injective compatible-submodule forgetful map. The canonical map on I is
bijective; its inverse defines the required equivalence. Injectivity of
that inverse, `localizedAction_iota` and `iota_intertwines` prove the action
and operator equations. Equality of inverse maps proves uniqueness.
The proof locally selects the existing scalar module of the actual
localization and constructs no replacement action or localization.

The acting-ring and carrier universes remain independent. Noncommutative
rings, degenerate actions and arbitrary carriers are included. Canonical
integer scalars are separate from the original action, even when A is ℤ
acting by zero. There is no complex-vector-space, unit-action,
nondegeneracy, dimension, Noetherian or finiteness premise.
This theorem assumes stability of the supplied positive power; it does
not prove eventual stability or interpret Renard's finiteness terminology.
It therefore leaves the complete source-facing proposition open.

## Additive-to-scalar sufficient conditions

The published theorem
`Langlands.Renard.additiveScalarFiniteLocalization` proves exactly
`Langlands.Renard.AdditiveScalarFiniteLocalizationStatement.{uR, uB, uV}`.
Its [statement](../../Langlands/Algebra/RenardAdditiveScalarFiniteLocalizationStatements.md)
and [proof](../../Langlands/Algebra/RenardAdditiveScalarFiniteLocalization.md)
give an internal implication from explicit additive generation assumptions
to the scalar-linear hypotheses just described. Worker 490 authored the
published proof.

For a supplied compatible action, the first generic component says that a
finite set generating among all stable additive subgroups also generates
among all stable scalar-linear submodules. The second says that if every
stable additive subgroup is generated by a finite subset in this sense,
then every stable scalar-linear submodule has that property among stable
scalar-linear submodules. The corresponding named proofs are
`Langlands.Algebra.AdditiveScalarStableGeneration.moduleGenerationComparison`
and `submoduleGenerationComparison`. They retain the supplied finite sets:
apply the additive hypotheses to the actual `Submodule.toAddSubgroup`, whose
carrier, membership and action-stability condition are unchanged. The
coefficient, algebra and carrier universes remain independent.

The complex component
`Langlands.Renard.AlgebraActionLocalization.additiveIdealFiniteLocalization`
assumes precisely the three written additive generation conditions: every
additive left ideal of B is finitely generated among additive left ideals;
the source is finitely generated among stable additive subgroups; and its
actual localization is finitely generated under its actual localized action.
It applies the second generic comparison to the regular left action
`NonUnitalAlgHom.lmul ℂ B` and the first to each of the two module actions.
The resulting scalar-linear hypotheses allow direct application of
`stableIdealFiniteLocalization`.

Consequently it gives the same actual compatible stabilization and
normalized stable-power image conclusions for every positive stable
exponent. Independent algebra and carrier universes, possibly noncommutative
and nonunital algebras, degenerate actions and arbitrary carrier dimension
are retained. There is no reverse generation implication. This result
does not identify these explicit additive premises with Renard's intended
Noetherian or finite-type terminology; that source-facing comparison and
the complete C.II proposition remain open.

## Verified acceptance and publication

These are exact receipts, not task-publication or compilation-only claims.
The stable-lemma, quotient and internal-localization proof receipts include
independent unqualified approval, exact-target/unchanged-input checks, a Lake
build and fresh integrated validation. The corresponding pairs were checked
against the published Library.

| Unit | Accepted artifact / independent reviewer | Publication commit |
| --- | --- | --- |
| Stable-endomorphism lemma proof | `7e459a2c-e520-488a-b102-1c94e5ad2441`, Reviewer 3448 | `6d91111e6f9b7a27124b1de32a4984bbdd222a61` |
| Successive quotient exactness proof | `e8d09f33-46c5-48a6-a495-7c070345d3f9`, Reviewer 4224 | `b7a6ea71635c439ae131d5b451e5f403e32dc1c7` |
| Compatible-action power-chain proof | `c601c63c-4fc2-41f8-b132-1b2663cccf23`, Reviewer 4485 | `771cfc69d1ff795522e29cdead1b7c40f1a1c308` |
| Actual scalar-linear localization construction | `b3b9bc36-a869-4b1a-a4c1-4e4c7263f87d` | `476e67f4df29c0dcafabdb5af459b61964b720a4` |
| Actual compatible algebra-action construction | `ce219e42-e734-408f-a5b7-32d786a5a581`, Reviewer 4091 | `355c05239d7704a3ed5d72bad864cb1d542b647a` |
| Complex-compatible unitized Noetherian proof | `cc923777-9dbd-44e9-9753-6154fc2dd6ca`, Reviewer 4582 | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| Original-additive unitized Noetherian proof | `ac573fe2-4e6b-41d5-8195-c6b4014a4b32`, Reviewer 4838 | `d3985dbb10c55a703b1ca560439739837d09e8a6` |
| Original-additive canonical stable-image statement | `0b6b9832-9dcc-4643-a427-94c24dfcb09d`, Reviewer 4816 | `7e64f8e360c8778e04e5da7f9cd382cda7c837f6` |
| Original-additive canonical stable-image proof | `932a8912-e918-40ae-807a-3d1a542501cd`, Reviewer 4888 | `e4fe0c0f7a3256e25c5a2d255ea294641c141ac5` |
| Internal stable-ideal finite localization proof | `9bba1e51-88ef-4b14-830e-f1c480e324c3`, exact statement `554ff789-621a-4049-a9c2-ef9778dc73e8` | `ddcb24bcc9c4fe817800414f5fd5f3536da42760` |
| Internal additive-to-scalar statement | `142cecb6-aba9-4fec-ad2f-7cb993888218`, Reviewer 5746 | `26e9adf301abba95f343f5005d9f478af9fc09d4` |
| Internal additive-to-scalar finite-localization proof | `f4447811-d9db-47ac-8da3-ae255a859613`, Reviewer 5804 | `6cb15022e66f7f1f171e7e8d563e74b92072e5ba` |
| Three-reading source statements | `0b44a67d-ab25-4432-a1c0-9826e8467f30`, Reviewer 14742 | `542eaca02a9f2d14f175497b7bf6459436ac5c6d` |
| Three-reading source proof | `7646164d-c224-44cd-b3f6-902fd2d99866`, Reviewer 15061 | `50126e1b2b20b62d408b52dc3552f01089dd1d11` |
| Compatible stability criteria statement | `3e01bae5-3faf-42da-9896-9c62405b14b8`, Reviewer 4273 | `a781b405546498b2d765aa36bf30e49c1aeb32a3` |
| Compatible stability criteria proof | `f0b9cad3-5d08-48a9-857b-f8a2070a4107`, Reviewer 4527 | `b58bd42aee6a565b689f0f0c008506e23b1b6560` |
| Noetherian localization core statement | `c299c22c-8f8a-4b83-bc16-c3c4541997aa`, Reviewer 3508 | `5b9935101c61f2c53bff91434ebe60bcd5719881` |
| Noetherian localization core proof | `2a850cbc-c905-463f-9d42-8853b40278f3`, Reviewer 3888 | `910a6df80701415e9aa68c646393c66ac9bc7512` |
| Actual-localization stability statement | `775d3dc9-2f3c-4f90-937c-fc724c5be241`, Reviewer 4082 | `355c05239d7704a3ed5d72bad864cb1d542b647a` |
| Actual-localization stability proof | `623a5905-faa5-43d8-b53d-b7b82af1c032`, Reviewer 4228 | `b7a6ea71635c439ae131d5b451e5f403e32dc1c7` |
| Canonical compatible stable-image statement | `b5a2b7ee-addb-4933-a865-ed7e51e890eb`, Reviewer 4369 | `84ad0affe3e3e8feae73b57da624fc1f16a6923b` |
| Canonical compatible stable-image proof | `598b9cce-85ed-4c21-9f48-ca6ebe1074cc`, Reviewer 4486 | `771cfc69d1ff795522e29cdead1b7c40f1a1c308` |

For the internal additive-to-scalar finite-localization proof
`f4447811-d9db-47ac-8da3-ae255a859613`, machine receipt
`23ce8c73-c13a-4665-8703-16b70ac268ec` accepts the Lake build, exact
target, unchanged statement and frozen inputs.
Independent Reviewer 5804 approves without qualifications. Integration
`96de716bca444889b0d086698ced52cc` publishes the pair with a successful fresh
integrated build. Worker 709 read the complete independent report and
verified equality of the frozen, published, current and workspace proof
hashes, as well as unchanged bytes for the 28 Lean/Markdown files in the
target statement's project import closure. Focused proof task
`551264ec-c65e-43eb-8047-daafd431ed28` revision 1 is complete; the parent
book task remains open.

For the three additional proofs checked on 4 November, the respective
machine receipts are `81197c8b-30f4-4687-82b1-f506a26103e6`,
`71555b38-5a00-4705-af60-ae7d5dcfdc9a` and
`cdb5c669-bbb1-4fa2-9df7-347b11d6779b`. Each accepts the Lake build,
exact target, unchanged statement and frozen inputs under `lean.proof@1`.
The complete independent reports approve without qualifications.
Integrations `ab17c6563ceb454592906d4e4cc55cdf`,
`773deeda5f8d4314b60fe9f0be6ff400` and
`b903c2c45bbb4c5aa6bc109a5690c4d1` publish them with successful fresh
integrated builds.

Worker 709 read all three current proof/statement pairs and their complete
independent reports. Each proof pair's hashes agree across its frozen
artifact, publication commit, current Library
`32eba017c96530e6a6723f7224c04e2cece5ee5d` and workspace. The respective
14, 22 and 20 Lean/Markdown files in the target statements' project import
closures are unchanged across each proof's Library base, publication,
current Library and workspace. These checks verify the listed internal
publications; they do not resolve the source-convention comparison.

For the additive stable-image proof, machine receipt
`f1ab16ea-bf2d-45c0-b9eb-4cd1913c8f4d` accepts the Lake build, exact
target, unchanged statement and frozen inputs under `lean.proof@1`.
Independent Reviewer 4888 approves without qualifications; integration
`ee57f3bb638d48048e394ac94ee5fc70` publishes the pair with a successful
fresh integrated build. Worker 709 read the complete independent report
and both current proof/statement pairs. Their hashes match their frozen
artifacts, publication commits, current Library
`66022d3631d55433e7dc5f97f0e78671522d05a3` and workspace. All 22
Lean/Markdown files in the target statement's project import closure are
unchanged across the proof's original Library base, integration base,
publication, current Library and workspace. Focused proof task
`41265157-23db-48f3-87f6-a116b5c57781` revision 1 is complete; this
verifies the listed internal result, with the source-facing boundary
described above.

For the three-reading source proof, by Worker 1581 with Worker 709,
machine receipt `f4c460c1-c7aa-48a5-be85-4636509e5136` accepts the Lake
build, exact target, unchanged statement and frozen inputs under
`lean.proof@1`. Independent Reviewer 15061 approves without qualifications
or suggestions in review task `c86aa372-0d21-4247-b091-54c66800d812`.
Integration `f63ed287534d40d88be40b717c46c312` publishes the pair at
`50126e1b2b20b62d408b52dc3552f01089dd1d11` with a successful fresh
integrated build. The published pair equals its frozen bundle: Lean
SHA256 `6bc36019b3f2e58a2b751c8d0fbf08f6cb4d1420cda59b1d84d3b381511c9eae`,
Markdown SHA256
`7245104f98dc10fd79add97000c09598d8c3d2028b3c2abc75dcc3a3e62f03c6`. At that
commit the statement pair is unchanged, with Lean SHA256
`06692eff8d95f2b541707ce27490b58c7ff45a63a762716c7f24ed113a24cadf` and
Markdown SHA256
`f6f99dd14ddd2e3b527560e5be896526c5b4ee9c94cf291786478eb16a09ae96`.
Worker 709 is a coauthor of this proof, so this record is documentation,
not an independent review. The source-facing convention comparison stays
open.

The three-reading statements are public under `lean.statement@1` with
Reviewer 14742's approval without qualifications, in review task
`1d770d85-135c-4d50-b16e-6338fa34b65c`. Machine receipt
`c4b5fc6f-ed79-494e-b542-b0424543c7f2` checks statement compilation and
declaration kind; it proves none of the readings. Integration
`7af7edd3efc24cdfbd93cc385ca8ec2d` publishes the pair. Its Lean/Markdown
SHA256 values
`06692eff8d95f2b541707ce27490b58c7ff45a63a762716c7f24ed113a24cadf` /
`f6f99dd14ddd2e3b527560e5be896526c5b4ee9c94cf291786478eb16a09ae96`
are equal in Library `dd78edadc914cf56ca81c595cee581a3570d415c` and the
workspace. The integration keeps the derived, statement-only scope; it does
not resolve the author's convention.

For the eight units added on 6 November, each independent reviewer
approves without qualifications. The review tasks, machine receipts and
integrations are:

| Unit | Review task | Machine receipt (policy) | Integration |
| --- | --- | --- | --- |
| `3e01bae5` | `00050a91-4c85-4b1a-a8d5-11c7b61427d6` | `a6018a9c-ab5b-469d-b207-692a197a6005` (`lean.statement@1`) | `da8f27c269fa41379dea874cb80a2b67` |
| `f0b9cad3` | `4e9e23a0-c899-4649-a9df-0c845021ced3` | `587dd4b6-7403-4ec6-ac1f-fb686f499e59` (`lean.proof@1`) | `83986632f5d74d648ac7c9468ca6eb2d` |
| `c299c22c` | `842967f2-dc53-49c4-b682-2c5ea9afa51f` | `be1270ae-4b63-49c2-b32f-0d20079c43a7` (`lean.statement@1`) | `6f7d8019c4274aa08c42fd2d3635dfe9` |
| `2a850cbc` | `3bf0d098-4f7a-4c73-b9f2-eabbc6f5763b` | `8e23e285-3678-437e-bf30-1f385721345b` (`lean.proof@1`) | `8e61746bd6cf442384ed9b94ac859618` |
| `775d3dc9` | `04dde906-f4b9-4f4c-9e1f-fa76c4d066e4` | `b159abde-457f-4ef5-9f79-1c7c622fd2ca` (`lean.statement@1`) | `c9cfcda653ca4c019e0a5c8557e8b3fd` |
| `623a5905` | `f3342009-c333-4a9c-b561-4636fb7987b7` | `9a07409e-a7b5-4352-aac8-74ee4765bcd6` (`lean.proof@1`) | `fe20e9fc271b413683b756d7ca7b1b82` |
| `b5a2b7ee` | `2920c95d-dd93-4a07-9865-aba55b320d55` | `eea56298-94e3-43c0-bb80-42d5750aa694` (`lean.statement@1`) | `1ee4048a4413467b87c045752cbf9d72` |
| `598b9cce` | `16be14d1-3693-40e6-a03b-3da7b20fa880` | `dbbf4939-67ee-4258-88f9-683c55073f6c` (`lean.proof@1`) | `33c2c0a29b58450184d07e3b35fd008c` |

Each proof receipt accepts the Lake build, exact target, unchanged
statement and frozen inputs. Each statement receipt checks compilation and
declaration kind; it proves nothing. The proof tasks
`a80d0a05-3a61-4e29-a4c0-0ca8c70c53af`,
`d5b1de4a-fa7c-47b9-9f10-d8a35ac539c0`,
`c9d7a084-4b9f-4094-a4d9-88126e384078` and
`80c2c945-109d-4be9-bf55-50bd374aa1fa` are complete; the parent book task
remains open. Worker 709 is a coauthor of the statements `3e01bae5`,
`c299c22c`, `775d3dc9` and `b5a2b7ee` and wrote the proof `2a850cbc`, so
those records are documentation, not independent review.

Worker 709 checked the sixteen Lean/Markdown files of these pairs at
current Library `87e695f5180726de47820341b89accb81c4e1033` and in the
workspace. Fourteen equal their frozen bundles. The published
actual-localization proof pair differs from its frozen bundle by the
kernel-lemma reuse described above:

| File | SHA256 at Library `87e695f5` and in the workspace | Frozen SHA256, if different |
| --- | --- | --- |
| `Langlands/Algebra/CompatibleStabilityStatements.lean` | `35489cfd0ab61bc48a2747f659bfe5b2826f7c708c338152c11edb729e348240` | |
| `Langlands/Algebra/CompatibleStabilityStatements.md` | `bd3aec5626e7514d7ea20089a07481dd1cdccd319b83289d8650347653b2215d` | |
| `Langlands/Algebra/CompatibleStabilityProofs.lean` | `c1ce1d12be4fe89b3cd55b68d4dc05ad5455b96f740d1fb579a9f744ef7ce2f4` | |
| `Langlands/Algebra/CompatibleStabilityProofs.md` | `1f1ecaf2dd01094bf2396ef3001849f0460717542b5fdd0a5a25187371fd1296` | |
| `Langlands/LinearAlgebra/NoetherianLocalizationCoreStatements.lean` | `b5971a452038cea7803358753b56cbfd60868f4bfe2746f9e4fc317d7567b10c` | |
| `Langlands/LinearAlgebra/NoetherianLocalizationCoreStatements.md` | `530655967a1f687892192313f31582156169dcb05ad4f1a617d648d5a23adb73` | |
| `Langlands/LinearAlgebra/NoetherianLocalizationCoreProof.lean` | `b32df4d21d06721f24fdd7422027d92ea76f8b4c1969dab7eb2da82546d0a107` | |
| `Langlands/LinearAlgebra/NoetherianLocalizationCoreProof.md` | `1f8bbec9e1d7279213d3333f618514f62ff32ce8d4d5ce706217a91be8d3cbaf` | |
| `Langlands/Algebra/RenardLocalizationStabilityStatements.lean` | `6fd86fb15db2f6bd450685b75542e34f2cd5cf2b0fdabcad23580e1f8f6fd9f3` | |
| `Langlands/Algebra/RenardLocalizationStabilityStatements.md` | `c4f97a56dd2c08acba47c452b0ea0a5ff83073da2c6028206ca34afc1699be02` | |
| `Langlands/Algebra/RenardLocalizationStabilityProof.lean` | `68c6c29934171a0a5d4fc05c840409320ae07ce9e40f52849fea0e900bc369cd` | `ee6aaa292490cb98c7664705e8349b5cae0893f9d4138a25cd64ee01d3a5353b` |
| `Langlands/Algebra/RenardLocalizationStabilityProof.md` | `cceb33401efb90d540d9d52ef301482989284c3b780323cbebb3d51c30ec3921` | `ab8f111cb14d9ccf0efec6563309cf3d74943d37dd61393448f164793e883612` |
| `Langlands/Algebra/RenardCompatibleStableImageStatements.lean` | `e55359d3fb85f9e964836fac3ee7d933869f7c1f237a3d7adcc05df74e197f0b` | |
| `Langlands/Algebra/RenardCompatibleStableImageStatements.md` | `7a7b10d8cd0d9bfcdcb1abd29c95c3bfc56cd3fbc1779b4c86fc90d3cbb7e035` | |
| `Langlands/Algebra/RenardCompatibleStableImageProof.lean` | `209de9be738f6a7daf32c49df6bdc9716717cec53d410cdd16a447b8908fd68a` | |
| `Langlands/Algebra/RenardCompatibleStableImageProof.md` | `b904afea49fdd640cb87893adb8ee076ed167590402c64410dd721fecebb8156` | |

These checks verify the listed internal publications. They do not resolve
the source-convention comparison.

The whole-book parent retains the source-convention comparison and every other
unassigned assertion. This note updates only the listed passages and preserves
the ownership of other statement, proof and categorical successors.

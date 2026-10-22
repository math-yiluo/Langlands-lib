# Weil and Weil–Deligne parameters: declaration coverage

This note maps the objects and constructions required by the task "Implement
the Weil and Weil-Deligne parameter definition framework" (task `650de61a`,
Workers 17 and 53) to Library declarations. It is a map, not a theorem: no
comparison between continuity conventions, no classification, no chosen
Frobenius semisimplification and no part of the local Langlands bijection is
claimed below. Each module's paired Markdown gives its exact sources,
conventions and the proofs of its intrinsic certificates.

Namespaces: `Langlands.FiniteRepresentation` (finite representations),
`Langlands.WeilDeligneRepresentation` (pairs) and `Langlands.Weil.Local`
(actual local specialization). Module paths below omit the leading
`Langlands/` of the Library root.

## Modules

| Module | Author | Content |
| --- | --- | --- |
| [`Langlands.Weil.Representation.Basic`](../../Langlands/Weil/Representation/Basic.md) | Worker 17 | Category of finite representations, equivalences, rank, genuine isomorphism classes |
| [`Langlands.Weil.Representation.Predicates`](../../Langlands/Weil/Representation/Predicates.md) | Worker 17 | Separate continuity, open-inertia, finite-image, irreducibility, semisimplicity, unramifiedness, unitarity and Galois-type predicates |
| [`Langlands.Weil.Representation.Invariants`](../../Langlands/Weil/Representation/Invariants.md) | Worker 17 | Invariant subspaces and invariant representations |
| [`Langlands.Weil.Representation.Restriction`](../../Langlands/Weil/Representation/Restriction.md) | Worker 17 | Restriction along homomorphisms |
| [`Langlands.Weil.Representation.SumsTensor`](../../Langlands/Weil/Representation/SumsTensor.md) | Worker 17 | Sums and tensor products |
| [`Langlands.Weil.Representation.DirectSum`](../../Langlands/Weil/Representation/DirectSum.md) | Worker 17 | Finite direct sums |
| [`Langlands.Weil.Representation.Dual`](../../Langlands/Weil/Representation/Dual.md) | Worker 17 | Duals |
| [`Langlands.Weil.Representation.DualClasses`](../../Langlands/Weil/Representation/DualClasses.md) | Worker 17 | Double dual, dual class involution, continuous irreducible dual involution |
| [`Langlands.Weil.Representation.Twist`](../../Langlands/Weil/Representation/Twist.md) | Worker 17 | Character twists |
| [`Langlands.Weil.Representation.Determinant`](../../Langlands/Weil/Representation/Determinant.md) | Worker 17 | Determinant characters |
| [`Langlands.Weil.Representation.InertiaOperations`](../../Langlands/Weil/Representation/InertiaOperations.md) | Worker 17 | Open-inertia certificates and constructors |
| [`Langlands.Weil.Representation.Induction`](../../Langlands/Weil/Representation/Induction.md) | Worker 17 | Finite-index induction by equivariant functions |
| [`Langlands.Weil.Representation.InductionTopology`](../../Langlands/Weil/Representation/InductionTopology.md) | Worker 17 | Open-inertia induction |
| [`Langlands.Weil.Representation.InductionContinuity`](../../Langlands/Weil/Representation/InductionContinuity.md) | Worker 17 | Usual-topology continuity of restriction and induction |
| [`Langlands.WeilDeligne.Basic`](../../Langlands/WeilDeligne/Basic.md) | Worker 17 | Weil–Deligne pairs, maps, equivalences, classes, Frobenius semisimplicity, zero monodromy |
| [`Langlands.WeilDeligne.Parameters`](../../Langlands/WeilDeligne/Parameters.md) | Worker 17 | Parameter conditions and parameter classes |
| [`Langlands.WeilDeligne.Kernels`](../../Langlands/WeilDeligne/Kernels.md) | Worker 17 | Weil representations on the monodromy kernel `ker N` and on `(ker N)^I` of a pair, with functors and class maps |
| [`Langlands.WeilDeligne.Restriction`](../../Langlands/WeilDeligne/Restriction.md) | Worker 17 | Restriction of pairs |
| [`Langlands.WeilDeligne.SumsTensor`](../../Langlands/WeilDeligne/SumsTensor.md) | Worker 17 | Sums and tensors of pairs |
| [`Langlands.WeilDeligne.DirectSum`](../../Langlands/WeilDeligne/DirectSum.md) | Worker 17 | Finite direct sums of pairs |
| [`Langlands.WeilDeligne.SpecialBlocks`](../../Langlands/WeilDeligne/SpecialBlocks.md) | Worker 17 | Special blocks and block data |
| [`Langlands.WeilDeligne.Dual`](../../Langlands/WeilDeligne/Dual.md) | Worker 17 | Dual pairs |
| [`Langlands.WeilDeligne.Twist`](../../Langlands/WeilDeligne/Twist.md) | Worker 17 | Twisted pairs |
| [`Langlands.WeilDeligne.Determinant`](../../Langlands/WeilDeligne/Determinant.md) | Worker 17 | Determinant of pairs |
| [`Langlands.WeilDeligne.Invariants`](../../Langlands/WeilDeligne/Invariants.md) | Worker 17 | Invariants of pairs |
| [`Langlands.WeilDeligne.Induction`](../../Langlands/WeilDeligne/Induction.md) | Worker 17 | Induction of pairs |
| [`Langlands.WeilDeligne.ParameterInduction`](../../Langlands/WeilDeligne/ParameterInduction.md) | Worker 17 | Induction of parameters |
| [`Langlands.WeilDeligne.ParameterRestriction`](../../Langlands/WeilDeligne/ParameterRestriction.md) | Worker 17 | Restriction of parameters |
| [`Langlands.WeilDeligne.ParameterOperations`](../../Langlands/WeilDeligne/ParameterOperations.md) | Worker 17 | Operations on parameters and their classes |
| [`Langlands.WeilDeligne.InductionAlong`](../../Langlands/WeilDeligne/InductionAlong.md) | Worker 17 | Induction along injective homomorphisms |
| [`Langlands.Weil.Local.DegreeCharacters`](../../Langlands/Weil/Local/DegreeCharacters.md) | Worker 53 | Unramified and norm characters from a continuous degree |
| [`Langlands.Weil.Local.ResidueCharacters`](../../Langlands/Weil/Local/ResidueCharacters.md) | Worker 53 | Norm characters with the actual residue cardinality |
| [`Langlands.Weil.Local.ExtensionResidue`](../../Langlands/Weil/Local/ExtensionResidue.md) | Worker 53 | Residue degree and cardinality of an extension |
| [`Langlands.Weil.Local.ExtensionGalois`](../../Langlands/Weil/Local/ExtensionGalois.md) | Worker 53 | Absolute Galois map of an extension |
| [`Langlands.Weil.Local.Assembly`](../../Langlands/Weil/Local/Assembly.md) | Worker 53 | Actual local Weil group, degree, inertia, Frobenius, characters |
| [`Langlands.Weil.Local.AssemblyStatement`](../../Langlands/Weil/Local/AssemblyStatement.md) | Worker 53 | Statement of the properties of the local assembly |
| [`Langlands.Weil.Local.AssemblyProof`](../../Langlands/Weil/Local/AssemblyProof.md) | Worker 100, Worker 53 | Proof `localAssembly : LocalAssemblyStatement` |
| [`Langlands.Weil.Local.Parameters`](../../Langlands/Weil/Local/Parameters.md) | Worker 53 | Local Weil and Weil–Deligne classes and parameters |
| [`Langlands.Weil.Local.ParameterOperations`](../../Langlands/Weil/Local/ParameterOperations.md) | Worker 53 | Local parameter operations and special blocks |
| [`Langlands.Weil.Local.ExtensionWeil`](../../Langlands/Weil/Local/ExtensionWeil.md) | Worker 53 | Weil map of a finite extension |
| [`Langlands.Weil.Local.ExtensionWeilRange`](../../Langlands/Weil/Local/ExtensionWeilRange.md) | Worker 53 | Image of `W_E` as an open finite-index subgroup |
| [`Langlands.Weil.Local.ExtensionParameters`](../../Langlands/Weil/Local/ExtensionParameters.md) | Worker 17 | Restriction and induction along an extension |
| [`Langlands.Weil.Local.ExtensionContinuity`](../../Langlands/Weil/Local/ExtensionContinuity.md) | Worker 17 | Continuity along an extension |

## (1) Finite-dimensional complex Weil representations

Module `Weil/Representation/Basic`:

- Objects on actual vector spaces: `FiniteRepresentation K G` (full subcategory
  of Mathlib `Rep`, independent coefficient, group and carrier universes),
  `of`, `representation`, the fully faithful `forget`.
- Morphisms: category morphisms, `homEquiv` with Mathlib intertwiners.
- Representation equivalences: `Equiv` (linear equivalence commuting with the
  action), `isoOfEquiv`, `equivOfIso`.
- Rank: `rank`, `rank_eq_of_equiv`.
- Genuine isomorphism relation and quotient: `IsIsomorphic`,
  `isomorphismSetoid` (equivalence laws proved), `IsomorphismClasses`,
  `classOf`, `classOf_eq_iff`, `classRank`, `classRank_classOf`,
  `IsomorphismClassesOfRank`; with explicit conditions
  `propertyIsomorphismSetoid`, `IsomorphismClassesWith`,
  `forgetPropertyClass`, `IsomorphismClassesOfRankWith`.

Module `Weil/Representation/Predicates` (separate predicates, none
implying another by definition):

- usual-topology continuity `IsContinuous` (module topology on endomorphisms);
- open inertia kernel `inertiaKernel`, `HasOpenInertiaKernel`;
- finite inertia image `HasFiniteInertiaImage`;
- `IsIrreducible`, `IsSemisimple`, `IsUnramified`, `IsUnitary`
  (existence of an invariant Hermitian inner product);
- finite image `HasFiniteImage` and Galois type along a supplied map
  `IsGaloisTypeAlong`, kept distinct;
- separate subtypes and rank-indexed classes: `ContinuousObjects`,
  `OpenInertiaObjects`, `ContinuousIrreducibleClasses`,
  `OpenInertiaSemisimpleClasses`.

Every rank `n : ℕ` is admitted, so every positive rank is supported and rank
zero is available internally.

## (2) Weil-Deligne pairs

Module `WeilDeligne/Basic`:

- `WeilDeligneRepresentation K G ν`: an actual finite representation with
  nilpotent monodromy `N` and the covariance law `r(g) N r(g)⁻¹ = ν(g) N`.
- Intertwiners `Hom` (with `ext`, `id`, `comp`, category), isomorphisms
  `Equiv` (`toHom`, `refl`, `symm`, `trans`, `toIso`, `ofIso`).
- `IsIsomorphic`, `isomorphismSetoid`, `IsomorphismClasses`, `classOf`,
  `classOf_eq_iff`, `rank`, `classRank`, `IsomorphismClassesOfRank`.
- `IsFrobeniusSemisimple`: every nonzero-degree action operator is semisimple;
  monodromy is unrestricted and no semisimplification is chosen.

Module `WeilDeligne/Parameters`:

- separate conditions `IsParameter` (open inertia kernel) and `IsContinuous`
  (usual topology); `ParameterObjects`, `parameterSetoid`,
  `ParameterClasses`, `ParameterClassesOfRank`;
- `IsFrobeniusSemisimpleParameter`, `FrobeniusSemisimpleParameterClasses`,
  `FrobeniusSemisimpleParameterClassesOfRank` (rank-`n` classes; the
  predicate places no condition on `N`, so nonzero monodromy is admitted).

## (3) Constructions

| Construction | Finite representations | Weil-Deligne pairs | Open-inertia / parameter versions |
| --- | --- | --- | --- |
| zero-monodromy embedding | | `zeroMonodromy`, `zeroMonodromyFunctor`, `zeroMonodromyFullyFaithful` (`WeilDeligne/Basic`) | `zeroMonodromyParameter` (`WeilDeligne/Parameters`) |
| sums, tensors (`N ⊗ 1 + 1 ⊗ N'`) | `sum`, `tensor`, maps, bifunctors, `sumEquiv`, `tensorEquiv`, `sumClass`, `tensorClass` (`Weil/Representation/SumsTensor`) | same names (`WeilDeligne/SumsTensor`) | `openInertiaSum`, `openInertiaTensor` (`Weil/Representation/InertiaOperations`); `parameterSum`, `parameterTensor` and class maps (`WeilDeligne/ParameterOperations`) |
| finite direct sums | `directSum`, `directSumMap`, `directSumFunctor`, `directSumEquiv`, `rank_directSum`, `directSumClass` (`Weil/Representation/DirectSum`) | `directSum` with componentwise `N`, same API (`WeilDeligne/DirectSum`) | `openInertiaDirectSum(Class)`, `parameterDirectSum(Class)` |
| dual (`-transpose(N)`) | `dual`, `dualFunctor`, `dualEquiv`, `dualClass` (`Weil/Representation/Dual`); `dualDualEquiv`, `rank_dual`, `dualClassEquiv`, `continuousIrreducibleDualEquiv` (`Weil/Representation/DualClasses`) | `dual`, `dualMap`, `dualFunctor`, `dualEquiv`, `dualClass` (`WeilDeligne/Dual`) | `openInertiaDual`, `parameterDual(Class)` |
| character twists | `twist`, `twistFunctor`, `twistFullyFaithful`, `twistEquiv`, `twistClass` (`Weil/Representation/Twist`) | `twist` (unchanged `N`), `twistMap`, `untwistMap`, functor, equivalences, classes (`WeilDeligne/Twist`) | `openInertiaTwist`, `parameterTwist(Class)` |
| determinant | `determinantCharacter`, `determinantCharacterClass`, `determinant`, `rank_determinant`, `determinantEquiv`, `determinantClass` (`Weil/Representation/Determinant`) | `determinant` with zero `N`, `trace_monodromy`, `determinant_monodromy_eq_trace` (`WeilDeligne/Determinant`) | `openInertiaDeterminant`, `parameterDeterminant(Class)` |
| invariants and kernels | `invariantSubspace`, `invariants`, `invariants_isTrivial`, maps, functor, classes (`Weil/Representation/Invariants`) | `kernelRepresentation`, `inertiaKernelRepresentation`: finite Weil representations (not pairs) on `ker N` and `(ker N)^I`, with functors and class maps into Weil isomorphism classes (`WeilDeligne/Kernels`); `invariants`: the pair on `V^J`, for a normal subgroup `J` on which `ν` is trivial (for example inertia), with restricted, possibly nonzero `N` (`WeilDeligne/Invariants`) | `openInertiaInvariants`; `parameterKernel`, `parameterInertiaKernel` returning open-inertia Weil representations (`OpenInertiaObjects`), with class maps into `IsomorphismClassesWith` of Weil representations; `parameterInvariants` returning a parameter pair on `V^J`, with class map `parameterInvariantsClass` into `ParameterClasses` (`WeilDeligne/Invariants`) |
| restriction | `restrict`, `restrictFunctor`, `restrictEquiv`, `restrictClass` (`Weil/Representation/Restriction`) | same with pulled-back `ν` and unchanged `N` (`WeilDeligne/Restriction`) | `openInertiaRestrict(Class)`, `parameterRestrict(Class)` (`WeilDeligne/ParameterRestriction`) |
| finite-index induction | `induce` (equivariant functions), `coordinates`, `finite_coindV`, maps, functor, `induceEquiv`, `induceClass`, `rank_induce`, `induceIsoMathlib` (`Weil/Representation/Induction`) | `induce` with `N(f)(g) = ν(g) N(f g)`, nilpotence and covariance, functor, classes, `rank_induce` (`WeilDeligne/Induction`) | `openInertiaInduce(Class)` (`Weil/Representation/InductionTopology`); `parameterInduce`, `parameterInduceClass`, `parameterInduceClassOfRank` (`WeilDeligne/ParameterInduction`) |
| induction along an injective homomorphism | `induceAlong` and API (`WeilDeligne/InductionAlong`) | `ofNormEq`, `induceAlong` and API | `openInertiaInduceAlong(Class)`, `parameterInduceAlong`, `parameterInduceAlongClass`, `parameterInduceAlongClassOfRank` |
| usual-topology continuity of restriction and induction | `isContinuous_restrict`, `continuousRestrict(Class)`; `isContinuous_induce` (open finite-index subgroup), `continuousInduce(Class)`; `isContinuous_induceAlong` (open embedding), `continuousInduceAlong(Class)` (`Weil/Representation/InductionContinuity`) | | |

No construction assumes a preservation, comparison or classification theorem;
open-inertia preservation certificates (`hasOpenInertiaKernel_*`) are proved
in the cited modules.

## (4) Special blocks

Module `WeilDeligne/SpecialBlocks`:

- `Special.action` on `Fin m → K` with weights `ν^j`, `Special.raising`
  (`N` raises `j`), `raising_pow`, `Special.covariance`;
- `specialBlock`, `rank_specialBlock`, `ker_specialBlock` (top-weight
  kernel), `Special.action_topVector`, `specialBlock_monodromy_ne_zero`
  (nonzero `N` in every rank at least two);
- block data for the decomposition statement: `block` (zero-monodromy factor
  tensor special block), `rank_block`, `block_monodromy_tmul`, `blockEquiv`,
  `blockClass`, `BlockDatum`, `BlockDatum.pair`, `BlockDatum.IsIrreducible`,
  `BlockDatum.IrreducibleData`.

Parameter versions: `specialBlockParameter`, `blockParameter`
(`WeilDeligne/ParameterOperations`).

## (5) Actual local specialization

Worker 53's module `Weil/Local/Assembly`, for every prime `p` and
`F : PadicField p`, assembles upstream constructions. Worker 9 built the
absolute residue action, Worker 28 the finite-field comparison
`Galois.FiniteField.toProfiniteIntegers` (it sends arithmetic Frobenius to
`-1`, hence the geometric normalization), and Worker 2 the generic pullback
`Weil.Pullback`.

- `localWeilGroup F := Pullback (localResidueDegree F)`, the existing generic
  pullback (`Weil/Pullback`), no rival Weil group; `localProjection` to the
  absolute Galois group;
- residue field, action and degree `localResidueField`, `localResidueMap`,
  `localResidueDegree`, `localResidueDegree_surjective`;
- integer degree `localDegree`, `localDegreeInt`, `localDegree_surjective`;
- inertia `localInertia`, `localInertia_normal`, `localResidueDegree_ker`,
  `localGaloisInertiaEquiv`, `localInertiaInclusion`;
- geometric Frobenius `localGeometricFrobenius`, chosen only from the proved
  `localDegree_surjective`, with `localGeometricFrobenius_degree` (degree
  `+1`);
- characters `localUnramifiedCharacter` and `localNormCharacter`
  (`canonicalResidueNormCharacter`), both built from `unramifiedCharacter`
  (`Weil/Local/DegreeCharacters`), the norm character through
  `residueNormCharacter` (`Weil/Local/ResidueCharacters`); both modules are
  Worker 53's.

Proved interface, modules `Weil/Local/AssemblyStatement` (Worker 53) and
`Weil/Local/AssemblyProof` (Worker 100 with Worker 53):
`LocalAssemblyProperties F` and `LocalAssemblyStatement` (for every prime `p`
and every `F`), proved as `localAssemblyProperties` and `localAssembly`.
Components: `localResidueCardinality_eq` (`q = Nat.card (localResidueField F)`),
`localResidueMap_projection` (the residue action of `w` is geometric Frobenius
to the power `deg w`), `localProjection_injective`,
`localProjection_denseRange`, `localInertia_eq_comap` (`I_F` is the comap of
the actual absolute inertia), `localInertiaInclusion_range`,
`localInertiaInclusion_isOpenEmbedding`, `localInertia_isOpen`,
`localInertia_isCompact`, `localInertiaEquiv` (`I_F ≃ₜ*` actual inertia,
compatible with the projection), `localWeilGroup_nonarchimedean`,
`localWeilGroup_locallyCompactSpace`, `localWeilGroup_t2Space`,
`localWeilGroup_totallyDisconnectedSpace`, `localGeometricFrobenius_residue`,
`localNormCharacter_apply` (`ν(w) = q^(-deg w)`),
`localNormCharacter_geometricFrobenius` (`ν(Φ) = q⁻¹`, with
`q = F.canonicalTopologicalData.residueCardinality = |k_F|`),
`localUnramifiedCharacter_on_inertia`,
`localUnramifiedCharacter_geometricFrobenius`.

Field-extension inputs (Worker 53), for `F : PadicField.{u} p`,
`E : PadicField.{v} p` and `f : F.Carrier →ₐ[Padic p] E.Carrier`:
`Weil/Local/ExtensionResidue` (`extensionResidueMap`,
`extensionResidueDegree`, `extensionResidueDegree_pos`,
`extensionResidueDegree_comp`, `extensionResidueCardinality`);
`Weil/Local/ExtensionGalois` (`extensionDegree` `[E : F]`,
`extensionGaloisMap`, `extensionGaloisMap_injective`,
`extensionGaloisMap_range_isOpen`, `extensionGaloisMap_range_index`
(`= extensionDegree`), `extensionGaloisMap_isClosedEmbedding`,
`extensionGaloisEquivRange`).

Local classes (Worker 53), module `Weil/Local/Parameters`:
`LocalWeilRepresentation`, `LocalWeilClasses(OfRank)`,
`LocalContinuousWeilObjects`, `LocalOpenInertiaWeilObjects`,
`LocalContinuousIrreducibleWeilClasses`, `LocalSemisimpleWeilClasses`,
`IsLocalGaloisType`, `LocalWeilDeligneRepresentation`,
`LocalWeilDeligneClassesOfRank`, `LocalParameterObjects`,
`LocalParameterClasses(OfRank)`, `IsLocalFrobeniusSemisimpleParameter`,
`LocalFrobeniusSemisimpleParameterClassesOfRank`, `localZeroMonodromyFunctor`,
`localZeroMonodromyFullyFaithful`, `localZeroMonodromyParameter`.

Finite-extension Weil map (Worker 53), module `Weil/Local/ExtensionWeil`.
Write `ι = extensionWeilMap F E f : W_E →ₜ* W_F` and
`r = extensionResidueDegree F E f`: `extensionWeilMap_injective`,
`extensionWeilMap_isEmbedding`, `extensionWeilMap_isOpenEmbedding`,
`extensionWeilMap_range` (the range is the comap of the Galois range along the
projection), `extensionWeilMap_range_isOpen`, `extensionWeilMap_range_index`
(index `[E : F]`), `extensionWeilMap_range_finiteIndex`,
`extensionResidueDegree_dvd_of_mem_range`, `extensionWeilMap_mem_localInertia`
(`ι w ∈ I_F ↔ w ∈ I_E`), `localInertia_eq_comap_extensionWeilMap`, the simp
lemmas `localProjection_extensionWeilMap` and `localDegree_extensionWeilMap`,
`localDegreeInt_extensionWeilMap` (`deg_F (ι w) = r · deg_E w`),
`localNormCharacter_extensionWeilMap` (`ν_F (ι w) = ν_E w`),
`localUnramifiedCharacter_extensionWeilMap` (`χ_z (ι w) = χ_{z^r} w`).
Its image as a subgroup (Worker 53), module `Weil/Local/ExtensionWeilRange`:
`extensionWeilRange`, `extensionWeilRangeEquiv` (`W_E ≃ₜ*` image) with simp
lemmas `extensionWeilRangeEquiv_apply` and
`extensionWeilMap_extensionWeilRangeEquiv_symm`, `extensionWeilOpenSubgroup`,
`extensionWeilRange_index`, the instance `extensionWeilRange_finiteIndex`,
`localInertia_inf_extensionWeilRange`, `localProjection_extensionWeilRange`
(compatibility with `extensionGaloisMap`),
`localNormCharacter_extensionWeilRange`.

Restriction and induction along it (Worker 17), module
`Weil/Local/ExtensionParameters`:
restriction `F → E`: `extensionRestrict(Functor, Class, ClassOfRank)`,
`rank_extensionRestrict`, `isContinuous_extensionRestrict`,
`extensionContinuousRestrict`, `extensionOpenInertiaRestrict(Class)`,
`extensionWDRestrict(Functor, Equiv, Class, ClassOfRank)`,
`extensionWDRestrict_monodromy`, `extensionParameterRestrict(Class,
ClassOfRank)`, `isLocalFrobeniusSemisimpleParameter_extensionWDRestrict`,
`extensionFrobeniusSemisimpleRestrict(Class, ClassOfRank)`;
induction `E → F`: `extensionInduce(Functor, Equiv, Class, ClassOfRank)`,
`rank_extensionInduce` (rank `[E : F] · n`), `extensionOpenInertiaInduce(Class)`,
`extensionWDInduce(Functor, Equiv, Class, ClassOfRank)`,
`rank_extensionWDInduce`, `extensionParameterInduce(Class, ClassOfRank)`.

Local operations (Worker 53), module `Weil/Local/ParameterOperations`:
`localNormCharacter_on_inertia`, the unramified certificate
`localUnramifiedCharacter_inertiaKernel_isOpen`; local sum, tensor, dual,
twist, unramified twist, determinant and invariant parameters (the invariant
pair `localParameterInvariants` lives on `V^I` and keeps the restricted,
possibly nonzero monodromy), with class maps between local parameter classes
`localParameter{Sum,Tensor,Dual,Twist,UnramifiedTwist,Determinant,Invariants}Class`;
the monodromy kernel `localParameterKernel` and its inertia invariants
`localParameterInertiaKernel` on `(ker N)^I`, which are open-inertia Weil
representations (`LocalOpenInertiaWeilObjects`), not pairs, with class maps
`localParameterKernelClass`, `localParameterInertiaKernelClass` into Weil
isomorphism classes (`FiniteRepresentation.IsomorphismClassesWith`);
`localSpecialBlock` (Sp(m)) with `localSpecialBlock_rank`,
`localSpecialBlock_kernel` and `localSpecialBlock_monodromy_ne_zero`
(nonzero monodromy for `m ≥ 2`), and the block constructor.

Continuity along the extension (Worker 17), module
`Weil/Local/ExtensionContinuity`: `extensionContinuousRestrictClass`,
`isContinuous_extensionInduce`, `extensionContinuousInduce(Class)`,
`isContinuous_extensionWDRestrict`, `isContinuous_extensionWDInduce`.

## Conventions

- Geometric Frobenius has degree `+1` (`localGeometricFrobenius_degree`), and
  the norm character is `ν(w) = q^(-deg w)`, so `ν(Φ) = q⁻¹`
  (`localNormCharacter_apply`, `localNormCharacter_geometricFrobenius`), with
  `q` the actual residue cardinality.
- Complex coefficients carry their usual topology. Usual-topology continuity
  (`IsContinuous`, `ContinuousObjects`, locally `LocalContinuousWeilObjects`)
  and the algebraic open-inertia-kernel convention (`HasOpenInertiaKernel`,
  `IsParameter`, locally `LocalOpenInertiaWeilObjects`, `LocalParameterObjects`)
  are separate predicates and classes. No bridge between them is assumed.
- Frobenius semisimplicity does not force `N = 0`: `IsFrobeniusSemisimple`
  constrains only the action operators of nonzero degree and places no
  condition on the monodromy. Pairs with nonzero monodromy exist in every rank
  at least two (`specialBlock_monodromy_ne_zero`).
- Special blocks are uncentered (weights `ν^j`, `N` raising `j`); the dual has
  monodromy `-transpose(N)`, twists keep `N`, and the determinant has zero
  monodromy.
- Every rank is admitted, including rank zero for closure under operations.

## Outside this definition layer

- Comparison of usual-topology continuity with the open-inertia-kernel
  convention, closure and preservation theorems beyond the certificates above,
  and classification statements are separate statement and proof work.
- The properties of the local assembly, mapped in section (5), are recorded
  as a separate statement/proof pair: `LocalAssemblyStatement`
  (`Weil/Local/AssemblyStatement`) and its proof `localAssembly`
  (`Weil/Local/AssemblyProof`).
- Local factors, `V^I/(ker N)^I` quotients and virtual representations are
  built on this layer elsewhere (module directories `Langlands/LocalFactor/`
  and `Langlands/VirtualRepresentation/`).

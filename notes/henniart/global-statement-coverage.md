# Global Henniart statements: declaration coverage and remaining gaps

Author: Worker 12, for task `91266440-3276-48dc-ab77-8d1c1fa386e8`
(global arithmetic, automorphic and weak-induction theorem statements for
Henniart). Most units listed here were authored in the previous instance by
Worker 35 (arithmetic, CM characters, functional equations, separation,
weak association and Harris) and Worker 44 (Jacquet–Shalika rigidity, Arthur–Clozel
transfer, Flath factorization). Their pairs name them as authors. Worker 12
authored the Galois transport of automorphic realizations, the Arthur–Clozel
cyclic transfer statements and the absolute Weil group statements. Definitions
by Worker 8 (task `6c50b2fd-cb4a-47b3-8f5d-d464916d69fb`) are listed where these
statements use them, and so is Worker 5013's pair functional equation
(section 1.6).

This note maps the objective of that task to the published Lean declarations
at Library commit `7103f5282c4897716543f227940fdb2a0e12e70e`, environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Modules are given relative to
`Langlands/`. Consume them by Lean name from the current Library; the commit
and the hashes in section 3 fix the versions described here.

**How to read the status.** Every target below is a `Prop`-valued `def`.
Publication accepts the formulation and its correspondence with the original
source; it does not prove the proposition. A "published proof" is a theorem in
the current Library whose type is exactly the named statement, with no
hypotheses. All other statements are unproved obligations; none of them is an
axiom or a structure field. A Library theorem that derives a statement from
other unproved statements leaves it unproved. Each pair's own Markdown gives the exact
quantifiers, normalizations, original page locators, registered source
fingerprints and source gaps. This note summarizes them and does not replace
them.

## 1. Coverage by clause of the objective

### 1.1 Global class field theory, Weil groups and Chebotarev rigidity

| Module | Declarations | Original source | Proof status |
| --- | --- | --- | --- |
| `Global/Arithmetic/ClassFieldStatement` | `Langlands.Global.{HasArithmeticArtinNormalization, FiniteAbelianArtinReciprocityStatement, OpenIdeleClassSubgroupFiniteIndexStatement, FiniteAbelianClassFieldExistenceStatement, FiniteAbelianClassFieldKernelRigidityStatement, FiniteOrderHeckeArtinRealizationStatement, FiniteAbelianClassFieldStatement}` | Artin–Tate (2009) VII §3 Thm 9 and Cors 2–3, pp.51–52; VIII §§1–2, pp.55–57 | Unproved |
| `Global/Arithmetic/ArtinNormStatement` | `Langlands.Global.{ArtinNormKernelStatement, LocalGlobalNormImageStatement, AbelianIdeleNormIndexStatement, HeckeNormFactorizationStatement, ArtinNormComparisonStatement}` | Artin–Tate VII §3, pp.41–52; VIII §1 Thm 2, pp.55–56; Tate 1979 §1.4.1 | Unproved |
| `Global/Arithmetic/ChebotarevStatement` | `Langlands.Global.{ChebotarevPrimeRealizationStatement, FiniteGaloisFrobeniusRigidityStatement, ChebotarevRigidityStatement}` | Neukirch VII §13 Thm 13.4, pp.545–546; Serre 1977 Part I §§1–2 | Unproved |
| `ClassField/Global/FundamentalClassStatement` (with constructions in `Global/AdelicFunctoriality/Inclusion`) | `Langlands.ClassField.Global.GlobalFundamentalClassStatement` | Artin–Tate VI Thm 1, VII Thms 7–8, 11–12, XIV §3; Tate 1979 §§1.2, 1.6 | Published proof `Langlands.ClassField.Global.globalFundamentalClassStatement` (`ClassField/Global/FundamentalClassProof`) |
| `ClassField/Global/LocalRelativeWeilMap` (definitions) | `Langlands.ClassField.Global.RelativeWeilGroup.IsLocalRelativeWeilMap` and helpers | Tate 1979 (1.2), (1.4.1), §1.5, (1.6.1); Artin–Tate XV §1 | Definition |
| `ClassField/Global/LocalRelativeWeilMapStatement` | `Langlands.ClassField.Global.{LocalRelativeWeilMapConjugacyStatement, LocalRelativeWeilMapExistenceStatement, LocalRelativeWeilMapStatement}` | Tate 1979 §1.5, (1.6.1); Artin–Tate XV §1 | Unproved |
| `ClassField/Global/RelativeWeilTransfer` (definitions) | `Langlands.ClassField.Global.RelativeWeilGroup.transfer` and helpers | Artin–Tate XIII §2, XV §1; Tate 1979 §1.2 | Definition |
| `ClassField/Global/RelativeWeilTransferReciprocityStatement` | `Langlands.ClassField.Global.RelativeWeilGroup.RelativeWeilTransferReciprocityStatement` | Artin–Tate XV Thm 1; Tate 1979 §1.2 | Published proof `relativeWeilTransferReciprocity` (`ClassField/Global/RelativeWeilTransferReciprocityProof`) |
| `Automorphic/AssociatedUniquenessStatement` | `Langlands.ClassField.Global.RelativeWeilGroup.{WeakEquivalenceRigidityStatement, AssociatedRepresentationUniquenessStatement, AssociatedClassUniquenessStatement, AssociatedUniquenessStatement}` | Henniart 2000 §2.2, p.444; Jacquet–Shalika 1981 II Thm 4.2 | Unproved |
| `ClassField/Global/{RelativeWeilMap, AbsoluteWeilGroup, AbsoluteLocalWeilMap}` (definitions, Worker 8) | `Langlands.ClassField.Global.{RelativeWeilGroup.IsWeilMap, WeilMapSystem, WeilMapSystem.WeilGroup, WeilMapSystem.toLevel, WeilMapSystem.IsLocalWeilMap}` | Artin–Tate XV §1, pp.167–180; Tate 1979 (1.4.1), (1.6.1) | Definition |
| `ClassField/Global/AbsoluteWeilGroupStatement` | `Langlands.ClassField.Global.{WeilMapExistenceStatement, WeilMapSystemExistenceStatement, WeilLevelSurjectiveStatement, LocalWeilMapExistenceStatement, LocalWeilMapConjugacyStatement, LocalWeilMapLiftStatement, WeilRepresentationFactorizationStatement, AbsoluteWeilGroupStatement}` | Artin–Tate XV Thms 1–3, pp.168–171, p.177, the lemmas on pp.178–179 and Thm 7, pp.179–180; Tate 1979 (1.6.1) and §2.1 | Unproved |
| `Automorphic/Unramified/{AbsoluteWeilAssociation, IsobaricWeilAssociation}` (definitions, Worker 8) | `Langlands.ClassField.Global.WeilMapSystem.{inflate, localComponent, IsWeaklyAssociated, IsWeaklyAssociatedClass, IsWeaklyAssociatedIsobaric}` and the relative `IsWeaklyAssociatedIsobaric` | Henniart 2000 §2.2, pp.443–444 | Definition |

The Weil-side rigidity of Henniart 2000 §2.2 is stated at the finite relative
level `W_{E/F}` (`WeakEquivalenceRigidityStatement`). The global
representations that Henniart's construction feeds into it, inductions of
Hecke characters from finite extensions, factor through such a group. The
absolute group `W_F` is now Worker 8's `WeilMapSystem.WeilGroup`, the inverse
limit of the relative groups along a system of Weil maps for a fixed algebraic
closure `Ω`. `AbsoluteWeilGroupStatement` states the arithmetic inputs that make
this object the Weil group: existence of the Weil maps and of a system,
surjectivity of the level projections, existence, conjugacy and lifting of
local-to-global maps `W_{F_v} → W_F`, and Tate's factorization (§2.1) of every
continuous finite-dimensional representation of `W_F` through some `W_{K/F}`.
The absolute forms of the rigidity and association statements are not stated
separately. With the factorization statement they reduce to the relative forms
through `WeilMapSystem.inflate`; that reduction is a proof obligation, not a
published theorem.

### 1.2 Field and Hecke-character realization

| Module | Declarations | Original source | Proof status |
| --- | --- | --- | --- |
| `Global/Arithmetic/FieldRealizationStatement` | `Langlands.Global.{TotallyRealGaloisRealizationStatement, HasSplitQuadraticPrime, SplitAuxiliaryQuadraticsStatement, FieldRealizationStatement}` | Henniart 2000 §3.3, p.449; Henniart 1984 Lemma 3.6, pp.34–35 | Published proof `Langlands.Global.fieldRealization` (`Global/Arithmetic/FieldRealizationAggregateProof`) |
| `Global/Arithmetic/CharacterPrescriptionStatement` | `Langlands.Global.{FiniteOrderCharacterPrescriptionStatement, NontrivialOnPrincipalUnits, LocalCharactersArbitrarilyRamifiedStatement, RamifiedTwistIsolationStatement, CharacterPrescriptionStatement}` | Artin–Tate X §2 Thm 5, p.80; Henniart 1986 Prop. 3.4 and §4.3, p.159; Serre, *Local Fields* IV §2 | Published proof `Langlands.Global.characterPrescription` (`Global/Arithmetic/CharacterPrescriptionAggregateProof`) |
| `Global/Arithmetic/CMCharacterStatement` | `Langlands.Global.{CMUnramifiedInfinityRealizationStatement, CMFiniteCharacterPrescriptionStatement, IntegralUnitCharacterExtensionStatement, CMRegularUnitPrescriptionStatement, CMCharacterGlobalizationStatement}` | Henniart 2000 §3.5 Lemma 1, p.450; §3.6 Lemmas 2–3, pp.450–451 | Published proof `Langlands.Global.cmCharacterGlobalization` (`Global/Arithmetic/CMCharacterGlobalizationProof`) |
| `Global/CompletionPadic` (definitions) | `Langlands.Global.CompletionPadic.{rationalPlace, residuePrime, padicMap, padicAlgebra, padicField, topologicalData}` with proved comparison lemmas | Derived bridge from `v.adicCompletion K` to the project's `PadicField` objects | Definition |

### 1.3 Auxiliary general position and splitting

| Module | Declarations | Original source | Proof status |
| --- | --- | --- | --- |
| `Global/Arithmetic/AuxiliaryCharacterStatement` | `Langlands.Global.{HasExactUnitNormStabilizer, AuxiliaryCharacterStatement}` | Henniart 2000 §3.4(3), p.449, §3.6 Lemma 3, p.451; Harris 1998 Lemma 4.7, proof pp.204–206, (4.12)–(4.13) | Published proof `auxiliaryCharacterFirstOrder` (`Global/Arithmetic/AuxiliaryCharacterFirstOrderProof`) |
| `Global/Arithmetic/GeneralPositionStatement` | `Langlands.Global.{HarrisGeneralPositionStatement, GeneralPositionOfExactStabilizerStatement, ExactStabilizerCharacterStatement, GeneralPositionCharacterStatement}` and helpers in `Langlands.Global.GeneralPosition` | Harris 1998 Def. 4.5, (4.12), Lemma 4.7, p.201, proof pp.204–206 | Published proof `harrisGeneralPosition` (`Global/Arithmetic/HarrisGeneralPositionProof`) |

The splitting choices (imaginary and real quadratic fields with prescribed
behaviour at `p`) are `SplitAuxiliaryQuadraticsStatement` (section 1.2). Both
statements include residue characteristic 2, where Harris's p.205 step fails as
printed; both pairs record this, and the targets add no odd-prime restriction.

### 1.4 Cuspidal and isobaric rigidity from unramified data

| Module | Declarations | Original source | Proof status |
| --- | --- | --- | --- |
| `Automorphic/Unramified/CuspidalSpectralRigidityStatement` | `Langlands.Automorphic.Unramified.{CuspidalPowerTraceIndependenceStatement, CuspidalPowerTraceConstituentRecoveryStatement, CuspidalEulerConstituentRecoveryStatement, CuspidalSpectralRigidityStatement}` | Jacquet–Shalika 1981 II Thm 4.2 and the multiplicity step of Thm 4.4, pp.805–809 | Unproved |
| `Automorphic/Unramified/HeckeCharacterRigidityStatement` | `Langlands.Automorphic.Unramified.{HeckeFiniteRamificationStatement, HeckePowerTraceIndependenceStatement, HeckeEulerProductRigidityStatement, HeckeLocalComponentRigidityStatement, HeckeCharacterRigidityStatement}` | Rank-one case of the same; Tate 1979 §§2–3 | Unproved |
| `Automorphic/Unramified/TraceAlgebraStatement` | `Langlands.Automorphic.Unramified.{EulerProductTraceStatement, InductionPolynomialTraceStatement, InductionPolynomialDegreeStatement, TraceAlgebraStatement}` | Polynomial algebra behind JS81 Thm 4.2 and the induction formulas of Tate 1979 (2.3.5) | Components proved: `eulerProductTrace`, `inductionPolynomialTrace`, `inductionPolynomialDegree` |
| `Automorphic/IsobaricData` (definitions, Worker 8) | `Langlands.Automorphic.IsobaricData` (multisets of `PositiveRankCuspidalClass`) with `IsobaricData.{rank, ofCuspidal, IsUnitary, HasSpectralSystem}` | Arthur–Clozel 1989 III Def. 4.1, p.202 | Definition |

The constituent-recovery targets compare finite lists of actual cuspidal
classes (repetitions allowed) through their unramified Euler products. That
is the isobaric rigidity of JS81 Thm 4.4 in terms of cuspidal data. Worker 8's
`IsobaricData` packages such lists as multisets of positive-rank cuspidal
classes, the constituent data of the representations induced from cuspidal
data. A comparison with realized isobaric representations is not stated,
because no realized isobaric object is in the Library (section 5).

### 1.5 Cyclic base change, automorphic induction and descent

| Module | Declarations | Original source | Proof status |
| --- | --- | --- | --- |
| `Representation/Unramified/WeakTransfer`, `Automorphic/Unramified/WeakTransfer` (definitions) | `Langlands.Unramified.SpectralSystem.{IsArithmeticWeakBaseChangeOf, IsArithmeticWeakInductionOf}`; `Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.{IsWeakBaseChangeOf, IsWeakInductionOf}` | Arthur–Clozel 1989 III Def. 1.1, p.199; Def. 6.1 and (6.1)–(6.2), pp.215–216 | Definition (focused task `04d260ad`) |
| `Automorphic/FiniteOrderDeterminantTwist` (definitions) | `Langlands.Automorphic.OperatorRealization.IsFiniteOrderDeterminantTwist` and `Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.IsFiniteOrderDeterminantTwist`; the norm condition is `Langlands.Global.HeckeCharacter.IsTrivialOnNorm` (`Global/HeckeCharacterFiniteOrder`) | Arthur–Clozel III.3.1 conclusion | Definition (focused task `8ff39111`) |
| `Automorphic/Unramified/CyclicCuspidalFiberStatement` | `Langlands.Unramified.SpectralSystem.SameResidueDegreePowers`, `Langlands.Automorphic.Unramified.CyclicCuspidalFiberStatement` | Arthur–Clozel III Thm 3.1, p.201 | Unproved |
| `Automorphic/Unramified/WeakInduction`, `Automorphic/WeakAutomorphicInduction` (definitions) | `Langlands.Unramified.SpectralSystem.IsWeakInductionOf`; `Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.IsWeakAutomorphicInductionOf` | Harris 1998 Def. 1.3(b), p.186 (corrected to the sum over places above, Tate 1979 (2.3.5)) | Definition |
| `Global/ArchimedeanCompactTransport`, `Automorphic/ArithmeticTransportRelation` (definitions) | `Langlands.Global.ArchimedeanCompactTransport.{realPlace, complexPlace, compactEquiv}`; `Langlands.Automorphic.OperatorRealization.{ArithmeticTransportEquations, IsArithmeticTransport}` and the cuspidal class forms `Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.{IsArithmeticTransport, IsGaloisConjugate, IsGaloisStable}` | Arthur–Clozel III §4, p.202 (`Π^σ`); III §6, p.217 | Definition |
| `Automorphic/{AutomorphicArithmeticTransport, OperatorArithmeticTransport, OperatorArithmeticTransportClasses}` (definitions) | `arithmeticEquiv` on the automorphic and cuspidal form spaces; `Langlands.Automorphic.OperatorRealization.arithmeticComap`, `CuspidalOperatorRealization.arithmeticComap`, `isArithmeticTransport_arithmeticComap`; `IsoClass.{arithmeticComap, galoisConj, galoisAction}` and `PositiveRankCuspidalClass.{arithmeticComap, galoisConj, galoisAction}` | Same; construction of `Π^σ = Π ∘ σ` | Definition |
| `Automorphic/Unramified/CyclicTransferStatement` | `Langlands.Global.HeckeCharacter.HasNormKernel`; `Langlands.Automorphic.Unramified.{CyclicPrimeCuspidalLiftStatement, CyclicPrimeSelfTwistStatement, CyclicStableDescentStatement, CyclicRegularInductionStatement, CyclicTransferStatement}` | Arthur–Clozel III Def. 1.1, (2.4), Thm 4.2(a), (b), (d), (e), Def. 6.1, Thm 6.2, Lemmas 6.3–6.4, pp.199–203, 215–218 | Unproved |
| `Automorphic/Unramified/IsobaricWeakTransfer` (definitions) | `Langlands.Automorphic.IsobaricData.{galoisConj, galoisAction, IsGaloisStable, galoisOrbit, IsWeakBaseChangeOf, IsWeakInductionOf}` with the `ofCuspidal` comparison lemmas | Arthur–Clozel III Def. 1.1, 4.1, 6.1 | Definition |
| `Automorphic/Unramified/IsobaricCyclicTransferStatement` | `Langlands.Automorphic.Unramified.{CyclicPrimeIsobaricLiftStatement, CyclicPrimeIsobaricSelfTwistStatement, CyclicPrimeIsobaricBaseChangeStatement, CyclicPrimeIsobaricStableDescentStatement, CyclicIsobaricInductionStatement, CyclicRegularOrbitLiftStatement, CyclicStableIsobaricDescentStatement, IsobaricCyclicTransferStatement}` | Arthur–Clozel III Thm 4.2(a)–(f), Thm 6.2, Lemmas 6.3–6.4, pp.202–203, 215–218 | Unproved |

`CyclicTransferStatement` states the clauses about cuspidal classes: the
cuspidal lift of (a), the weak induction form of (b), the twist description of
Lemma 6.3 (with (d)) and the regular induction of Lemma 6.4 (with (e) and Thm
6.2). `IsobaricCyclicTransferStatement` states the clauses about
representations induced from unitary cuspidal data through their constituent
data: uniqueness in (a) and (b), (c), (f), Thm 6.2 for arbitrary unitary data,
the orbit form of Lemma 6.4 and the exclusion of noncuspidal lifts in Lemma 6.3.
Harris 1998 (1.4)(a), (b), pp.186–187, are (d) and (e), and the proof of his
Prop. 4.8, pp.202–203, uses Lemma 6.4. Arthur–Clozel III.5.1, Cor. III.6.5 and
Lemma III.6.6 are not stated (section 5).

### 1.6 Global functional equations and the archimedean comparison

| Module | Declarations | Original source | Proof status |
| --- | --- | --- | --- |
| `Global/Factors/HeckeFunctionalEquationStatement` | `Langlands.Global.HeckeGlobalFunctionalEquationStatement` with helpers in `Langlands.Global.HeckeFunctionalEquation` | Tate 1979 Thm 3.5.3, pp.15–16; Weil 1973 II.5 and VII.2 | Published proof `heckeGlobalFunctionalEquation_proof` (`Global/Factors/HeckeFunctionalEquationProof`) |
| `Representation/Archimedean/{SmoothVectors, GeneralLinear, Induction, StandardModule}` (definitions) | Smooth vectors, generic Banach representations of `GL_N(ℝ)`, `GL_N(ℂ)`, normalized induction, local-coefficient relation, standard-module parameters | Shahidi 1985 §§1–3; Shahidi 1984 pp.72–73; Knapp 1994 | Definition |
| `Representation/Archimedean/LocalCoefficientGammaStatement` | `Langlands.Archimedean.{RealLocalCoefficientGammaStatement, ComplexLocalCoefficientGammaStatement, LocalCoefficientGammaStatement}` | Shahidi 1985 Thms 3.1 and 3.13, Remark 2, pp.990–991, 1003 | Unproved |
| `Automorphic/ArchimedeanPlaceParameter`, `LocalFactor/ArchimedeanPairFactor` (definitions, Worker 8) | `Langlands.Automorphic.OperatorRealization.{HasRealPlaceParameter, HasComplexPlaceParameter}` and their class forms; `Langlands.LocalFactor.Archimedean.{realPairLFactor, realPairEpsilon, complexPairLFactor, complexPairEpsilon}` | Knapp 1994, pp.399–403, Thms 1–2, 4–5; Tate 1979 (2.2.2), §§3.1–3.4 | Definition |
| `Global/Factors/CuspidalPairFactorData` (definitions, Workers 1794 and 1802) | `Langlands.Global.CuspidalPairFunctionalEquation.{FinitePairFactorChoice, IsUnramifiedOutside, CompletedEquationHolds}` and helpers | JPSS 1983 (9.4), p.458; Henniart 2002 §2.8, p.596; Cogdell 2004 §3, pp.211–217 | Definition |
| `Global/Factors/CuspidalPairFunctionalEquationStatement` (Worker 5013) | `Langlands.Global.CuspidalPairGlobalFunctionalEquationStatement` | Henniart 1986 §2.10, p.155; Cogdell 2004 Thm 4.1, p.219; Getz–Hahn 2024 Thm 11.7.1, p.309 | Unproved |

The Galois-side functional equation for twisted pairs of relative Weil
representations is `Langlands.Global.FunctionalEquationComparison.RelativeWeilTwistFunctionalEquationStatement`
(`Global/Factors/RelativeWeilFunctionalEquationStatement`), authored by
Worker 84 under program `34b81620-20d7-4059-9b08-6bedd1c1c029`; it is reused,
not duplicated. The completed Rankin–Selberg equation for pairs of actual
cuspidal realizations is `CuspidalPairGlobalFunctionalEquationStatement`, stated
by Worker 5013 in focused task `876d1f0c-d287-4743-adf6-aef3a9efb5ba` (Task 5013,
under program `34b81620`). Its finite places use `CuspidalPairFactorData`. At
each infinite place it uses Worker 8's parameters of the realizations (an
injective `(𝔤_v, K_v)`-equivariant map from the `K`-finite standard module of a
block list into the realization) and Worker 8's pair factors of those
parameters. It covers cuspidal pairs, as Henniart 2000 §2.4 needs; pairs of
noncuspidal representations are not stated (section 5). Its Markdown records the
normalizations (shift `1 − s`, actual contragredient pair, sign, self-dual
archimedean measures) and the remaining proof obligations, including the
independence of the archimedean factors from the chosen block list.

### 1.7 Isolation of a finite place by highly ramified twists

`Langlands.Global.RamifiedTwistIsolationStatement` and
`LocalCharactersArbitrarilyRamifiedStatement` (section 1.2) supply the global
characters with prescribed highly ramified components (Henniart 1986 §4.3,
p.159). Both are proved. The local stability of gamma factors under such twists
(Deligne–Henniart 1981 Thm 4.6; Jacquet–Shalika 1985) and the finite
exceptional-set comparison engine (`Global/Factors/FiniteComparisonStatement`,
Henniart 1986 §4.3 (2), (4), (5)) belong to the local-factor branch
(`Langlands/LocalFactor/RankOneStabilityStatement` and the Deligne–Henniart
modules) and to program `34b81620` (row H1). This task does not restate them.

### 1.8 Weak-association gamma comparison, pole regions and separation

| Module | Declarations | Original source | Proof status |
| --- | --- | --- | --- |
| `Automorphic/Unramified/RelativeWeilAssociation` (definitions) | `Langlands.ClassField.Global.RelativeWeilGroup.{localComponent, localPairClass, localEulerPolynomial, IsUnramifiedMatchAt, IsWeaklyAssociated, IsWeaklyAssociatedClass}` | Henniart 2000 §2.2, pp.443–444 | Definition |
| `Automorphic/AssociatedFactorStatement` | `Langlands.ClassField.Global.RelativeWeilGroup.{AssociatedGammaStatement, AssociatedTemperedFactorStatement, AssociatedSupercuspidalInductionStatement, AssociatedCuspidalFactorStatement, AssociatedFactorStatement}` and match predicates | Henniart 2000 Thm 2.3, Cor. 2.3, Thm 2.4, Cor. 2.4, pp.444–445 | Unproved |
| `Automorphic/Contragredient` (definitions) | `Langlands.Automorphic.OperatorRealization.IsContragredientOf` and class forms | Henniart 2000 §2.2, p.444 | Definition |
| `Automorphic/AssociatedContragredientStatement` | `Langlands.ClassField.Global.RelativeWeilGroup.PresentedContragredientAssociationStatement` | Henniart 2000 §2.2, p.444 | Published proof `Langlands.ClassField.Global.RelativeWeilGroup.presentedContragredientAssociation` (`Automorphic/Unramified/ContragredientAssociation`) |
| `Automorphic/AssociatedContragredientStatement` | `Langlands.ClassField.Global.RelativeWeilGroup.{ClassContragredientAssociationStatement, AssociatedContragredientStatement}` | Henniart 2000 §2.2, p.444 | Unproved. `classContragredientAssociation_of_dualPresentationExistence` (`Automorphic/Unramified/ContragredientAssociation`) proves the class form only under the hypothesis `Langlands.Automorphic.CuspidalDualPresentationExistenceStatement`, itself unproved |
| `Automorphic/AssociatedDeterminantTwistStatement` | `Langlands.ClassField.Global.RelativeWeilGroup.{reciprocityCharacter, PresentedDeterminantAssociationStatement, PresentedTwistAssociationStatement, ClassTwistAssociationStatement, AssociatedDeterminantTwistStatement}` | Henniart 2000 §2.2, p.444 | Unproved |
| `Global/Factors/WeilPoleRegionStatement` | `Langlands.Global.{EssentiallyUnitaryPoleRegionStatement, NonJuxtaposedPoleRegionStatement, WeilPairPoleRegionStatement}` | Henniart 1986 Prop. 4.5(i), pp.159–160 | Unproved |
| `Global/Factors/GLPoleRegionStatement` | `Langlands.Global.{EqualRankPoleRegionStatement, UnequalRankPoleRegionStatement, GLPairPoleRegionStatement}` | Henniart 1986 Prop. 4.5(ii), pp.159–160 | Unproved |
| `Global/Factors/SeparationStatement` | `Langlands.Global.{GammaPolynomialSeparationStatement, ReflectedRootRegionStatement, GammaSeparationStatement}` | Henniart 1986 §4.4 Lemma, p.159 | Published proof `Langlands.Global.gammaSeparation` (`Global/Factors/SeparationProof`) |

Weak association is almost-everywhere unramified matching outside one finite
set; it asserts nothing at ramified places. The pole-region conclusions are
exactly the no-common-zero hypotheses of the separation lemma, so gamma
equality is never treated as L/epsilon equality without them.

### 1.9 Harris's weak automorphic induction

| Module | Declarations | Original source | Proof status |
| --- | --- | --- | --- |
| `Global/Arithmetic/HarrisSetup` (definitions) | `Langlands.Global.Harris.{IsAlgebraic, IsAlgebraicAfterTwist, IsConjugateInverse, IsRelativelyRegular, IsSplitImaginaryQuadratic, HasUniquePlaceAbove, PlaceDatum, conjPlace, IsProposition48Datum}` | Harris 1998 pp.185, 192–195, 200–201 | Definition |
| `Automorphic/ConjugateContragredient`, `Global/CMConjugationGL` (definitions) | `Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.IsConjugateSelfDual`; `Langlands.Global.CMConjugation.*` | Harris 1998 Thm 1.2(ii), p.185 | Definition |
| `Automorphic/RegularAlgebraic` (definitions) | `Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.IsRegularAlgebraic` and helpers | Clozel 1990 Déf. 1.8, 3.12, proof of Thm 3.13; Harris p.185 | Definition |
| `Automorphic/SupercuspidalComponent` (definitions) | `Langlands.Automorphic.LocalRealization.IsSupercuspidal`, `Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.HasSupercuspidalComponent` | Harris 1998 Prop. 4.8, p.201 | Definition |
| `Global/Arithmetic/HarrisProposition48Statement` | `Langlands.Global.Harris.Proposition48Statement` | Harris 1998 Prop. 4.8, pp.201–203 | Unproved |

The statement keeps the CM fields, the imaginary quadratic field in which `p`
splits, the normal closure and completion identifications, two pairs of
conjugate places, general position at the auxiliary place, and the regular,
conjugate-inverse, algebraic (Harris p.195 normalization) infinity type. It has
no `n < p` restriction. Its proof needs Harris's Theorems 1.2 and 1.7 with
general cohomological coefficients (owned by the cohomological branch,
`bd93b48c-db25-4739-89f5-97cabc0f6491`) and the Arthur–Clozel inputs of
section 1.5.

## 2. Further prerequisite constructions built under this task

- `Global/AdeleQuotientStatement`: `Langlands.Global.{principalAdeles, AdeleQuotient, adeleQuotientMap}` and
  `AdeleQuotientStatement` (Cassels §§13–14; Weil, *Basic Number Theory* IV §2 Thm 2), proved by
  `Langlands.Global.adeleQuotient` (`Global/AdeleQuotientProof`).
- `Automorphic/ConstantTerm`: maximal-block constant terms and `Langlands.Automorphic.IsCuspidal`
  (Borel–Jacquet 1979 §3.3), under the instance `[CompactSpace (AdeleQuotient K)]`.
- `Global/AdelicFunctoriality/Inclusion`: extension-of-scalars inclusions of adeles, ideles and idele classes.
- `Representation/Smooth/Factorization/{TwoFactorStatement, RestrictedTensorStatement, RestrictedProductExistenceStatement}`:
  Flath 1979 Thms 1–2 and §2 Example 2, pp.179–183. Published proofs:
  `Langlands.flathRestrictedProductExistence`, `Langlands.restrictedTensorFactorUniqueness`,
  `Langlands.admissibleProductFactorization`.

## 3. Exact versions at Library `7103f528`

Lean / Markdown SHA-256, first twelve hex digits; the full values can be
recomputed from the Library at that commit. The first table covers the units
authored under this task or its focused delegated tasks.

| Module | Lean | Markdown |
| --- | --- | --- |
| `Global/Factors/SeparationStatement` | `4d838a2c075d` | `dc4622331d69` |
| `Global/Arithmetic/FieldRealizationStatement` | `9ccba3482f2b` | `a95e8c0c8ae8` |
| `Global/Arithmetic/ChebotarevStatement` | `34a27ae3d4c4` | `33592151d29f` |
| `Global/Arithmetic/CharacterPrescriptionStatement` | `bf39b05110b3` | `ee0abe602590` |
| `Global/Arithmetic/AuxiliaryCharacterStatement` | `fadb37306169` | `7eb086515f56` |
| `Global/Arithmetic/ClassFieldStatement` | `d4f5888bc7dd` | `03b05c452a1b` |
| `Global/Arithmetic/CMCharacterStatement` | `e3985cf0666c` | `b81117d18290` |
| `Global/Arithmetic/ArtinNormStatement` | `92bf450fb7e7` | `fe20811ebaea` |
| `Global/CompletionPadic` | `00eff12c3044` | `c5c6fc582a53` |
| `Global/Factors/HeckeFunctionalEquationStatement` | `2f80ab0a3fcc` | `940ffb6f686b` |
| `Global/Factors/WeilPoleRegionStatement` | `46efb6919853` | `f4ec02fecb12` |
| `Global/Factors/GLPoleRegionStatement` | `3b1f8b980a4d` | `7a429f77c796` |
| `Global/Arithmetic/GeneralPositionStatement` | `cbefa10ace4e` | `881085ccc57e` |
| `Global/AdeleQuotientStatement` | `3a4a69feb5a7` | `d3d92a757c6f` |
| `Automorphic/ConstantTerm` | `c83f402c4a75` | `390d8d14db7f` |
| `ClassField/Global/FundamentalClassStatement` | `00fe196b1384` | `8774502e9fac` |
| `Global/AdelicFunctoriality/Inclusion` | `bacde3469e74` | `a62dc4bebfc1` |
| `Automorphic/Unramified/WeakInduction` | `05f9861fcba8` | `5ed0fd16b52f` |
| `Automorphic/ConjugateContragredient` | `080d2ef43a2a` | `2ae0cc42ac80` |
| `Global/CMConjugationGL` | `e1c203362a40` | `65bbe8841310` |
| `Global/Arithmetic/HarrisSetup` | `2a3a3b0821d7` | `7c920ced9a35` |
| `Automorphic/WeakAutomorphicInduction` | `ee12e11ab69f` | `da315ba96191` |
| `Representation/Archimedean/SmoothVectors` | `3676b7dee472` | `88ee2a3c0d21` |
| `Representation/Archimedean/GeneralLinear` | `ec1932bc4eb9` | `e0f842da9681` |
| `Representation/Archimedean/Induction` | `12979a5bceb5` | `f019b2ec19b7` |
| `Representation/Archimedean/StandardModule` | `05b03fa8871b` | `d2c772fd42d4` |
| `Representation/Archimedean/LocalCoefficientGammaStatement` | `12dfc13f43b0` | `8de32c6401cc` |
| `ClassField/Global/LocalRelativeWeilMap` | `76976f28b7b7` | `071482963fb9` |
| `ClassField/Global/LocalRelativeWeilMapStatement` | `e9c8615e34ac` | `1eb6f50ff288` |
| `Automorphic/Unramified/RelativeWeilAssociation` | `70c6ba206eb3` | `b5fccd10b28b` |
| `Automorphic/AssociatedFactorStatement` | `800371a5ff63` | `81a5177fd934` |
| `Automorphic/AssociatedUniquenessStatement` | `883e2d0a8e9b` | `8106a1e7c506` |
| `Automorphic/Contragredient` | `7ab8cab5857b` | `d1104d9879f2` |
| `Automorphic/AssociatedContragredientStatement` | `e1b37c5f857f` | `727a73888202` |
| `ClassField/Global/RelativeWeilTransfer` | `6e137d078a0d` | `af7d862118dd` |
| `ClassField/Global/RelativeWeilTransferReciprocityStatement` | `be5f6ce380b8` | `25661fd53fb7` |
| `Automorphic/AssociatedDeterminantTwistStatement` | `5bd3c3547958` | `10d9b093e3fe` |
| `Automorphic/RegularAlgebraic` | `9b49c2829db2` | `c27969033086` |
| `Automorphic/SupercuspidalComponent` | `cf0e34c927ff` | `c02715a8ada9` |
| `Global/Arithmetic/HarrisProposition48Statement` | `144bf98eb50a` | `cb613ca1cdb1` |
| `Automorphic/Unramified/TraceAlgebraStatement` | `c9fd4b88c739` | `82365bb50309` |
| `Automorphic/Unramified/HeckeCharacterRigidityStatement` | `d6baa9902aed` | `b6d96367f6ee` |
| `Representation/Smooth/Factorization/TwoFactorStatement` | `0104f1b03db9` | `85b04f03e796` |
| `Representation/Smooth/Factorization/RestrictedTensorStatement` | `e3d72b95a267` | `cea307af8be1` |
| `Representation/Smooth/Factorization/RestrictedProductExistenceStatement` | `5d8228dbe192` | `ebfd41da889e` |
| `Automorphic/Unramified/CuspidalSpectralRigidityStatement` | `a12d63189eca` | `314ad4b2b078` |
| `Automorphic/Unramified/CyclicCuspidalFiberStatement` | `4c70c5c88b7a` | `c0064b015f70` |
| `Automorphic/Unramified/WeakTransfer` | `90c083c84cd2` | `4bed33ca6198` |
| `Representation/Unramified/WeakTransfer` | `33eb11269432` | `05033c693e9e` |
| `Automorphic/FiniteOrderDeterminantTwist` | `e8bc5f2328a2` | `117cffac9ccd` |
| `ClassField/Global/AbsoluteWeilGroupStatement` | `d71b9fbd611e` | `751863331b08` |
| `Global/ArchimedeanCompactTransport` | `8111f3b1ad2a` | `e527e5bb9ab1` |
| `Automorphic/ArithmeticTransportRelation` | `97e1978beccc` | `d7115bd2127f` |
| `Automorphic/AutomorphicArithmeticTransport` | `a252e4bb30ae` | `37f452d5202f` |
| `Automorphic/OperatorArithmeticTransport` | `cf46e509a459` | `168a67d5f6cb` |
| `Automorphic/OperatorArithmeticTransportClasses` | `eb8735218a4b` | `5f72f27403fc` |
| `Automorphic/Unramified/CyclicTransferStatement` | `b8ebe7c30da5` | `90b63a347608` |
| `Automorphic/Unramified/IsobaricWeakTransfer` | `631c6bc8e919` | `e569d0c916e1` |
| `Automorphic/Unramified/IsobaricCyclicTransferStatement` | `d747bbcba88c` | `e883009725f7` |

Several files differ from their frozen candidate hashes because of later
published corrections (the `HarrisSetup` infinity-type correction and
documentation-only audits). The table records the files at the stated commit.

Reused units of other tasks that complete clauses of section 1 (Worker 8's
definitions and Task 5013's pair functional equation) are recorded here at the
same commit. Other reused units are named in section 1 and consumed by Lean name.

| Module | Lean | Markdown |
| --- | --- | --- |
| `Global/Factors/CuspidalPairFactorData` | `8407042d81fd` | `9a941c11a0c5` |
| `Global/Factors/CuspidalPairFunctionalEquationStatement` | `425bedc5169f` | `e11483ee9d52` |
| `Automorphic/ArchimedeanPlaceParameter` | `12874b33adee` | `c8370f8e1f21` |
| `LocalFactor/ArchimedeanPairFactor` | `b462cecfc82a` | `2421a8a769b4` |
| `Automorphic/IsobaricData` | `a70d648a29e9` | `b19751700196` |

## 4. Retained source gaps and derived formulations

These are explained in the pairs' Markdown and kept visible here:

- Harris 1998 Def. 1.3(b), p.186, writes one local induction; the weak-induction
  definitions use the direct sum over all places above (Tate 1979 (2.3.5)).
- Harris's algebraicity is his p.195 normalization `(z/z̄)^{a(ν)/2}` with
  `a(ν) ≡ n − 1 (mod 2)`, implemented by `IsAlgebraicAfterTwist ([E':E] − 1)`.
- The displayed `n(a,i)` on Harris p.201 is not copied; general position uses
  the actual Mackey constituents.
- Arthur–Clozel Thm III.6.2 prints `GL(n, A_F)` where Def. 6.1 and the proof need
  `GL(n·ℓ, A_F)`.
- Arthur–Clozel Lemma III.6.3 prints `π_F ≅ π_F ⊗ η`; its proof and Thm III.4.2(d)
  show that the `ℓ` twists are pairwise non-isomorphic, which is what is stated.
- Arthur–Clozel III.4.2(a) asserts a unique `σ`-stable lift. By (2.4) every lift is
  `σ`-stable, so the statements assert uniqueness among all lifts. Uniqueness
  "among representations induced from cuspidal" is uniqueness of unitary
  isobaric data.
- The isobaric statements are data-level: lifts and inductions of isobaric data
  are defined through attached spectral systems, not through realized induced
  representations.
- Henniart 2000 A.3 prints `r + 2σ` as the most positive real pole; see the
  corrected argument in [the source audit](audit.md), section 3.2.
- The Rankin–Selberg global equation used by Henniart 1986 §2.10 is quoted from
  [JPS4]; Henniart 2000 §2.3 attributes it to Shahidi with Henniart–Herb 1995
  §8.15–8.16. Henniart–Herb 1995 §8.15 notes that the 1981 announcement has no
  proof. The completed cuspidal-pair statement of section 1.6 therefore follows
  Cogdell 2004 Thm 4.1 and Getz–Hahn 2024 Thm 11.7.1.
- Weak association, weak base change and weak induction are almost-everywhere
  unramified relations only; no ramified local compatibility is asserted.

## 5. Remaining statements, owners and gates

| Missing statement | Needed actual objects | Owner and gate |
| --- | --- | --- |
| Arthur–Clozel III.5.1 (strong base change: local base change at every place) | Local base-change character relations at finite and archimedean places | Not started; local base change has no Library object. The Henniart and Harris 1998 steps covered here use only the weak relations of section 1.5. Harris 1999 Thm 5.9 uses base change with supercuspidal-place control; that belongs to the cohomological branch (`bd93b48c-db25-4739-89f5-97cabc0f6491`) |
| Arthur–Clozel Cor. III.6.5 and Lemma III.6.6 (lifts and inductions through stabilizers) | None beyond section 1.5 | Not stated; not used by the steps covered here |
| Noncuspidal forms: the Rankin–Selberg functional equation for pairs of noncuspidal automorphic representations (Henniart 1986 §2.10, Thm 4.1) and Henniart 2000 Thm 2.3 and Cor. 2.3 for noncuspidal `Π` | Realized isobaric representations with their local components and archimedean parameters | Not stated. The cuspidal forms are in sections 1.6 and 1.8; Henniart 2000 §2.4 and Thm 2.4, Cor. 2.4 concern cuspidal representations. Depends on the realized objects of the next row |
| Comparison with realized isobaric representations (JS81 Thm 4.4 in full; Arthur–Clozel statements for realized induced representations) | Realized normalized induced-from-cuspidal representations | Task `6c50b2fd`; program `34b81620`. The data-level statements of section 1.5 do not depend on it |
| Uniqueness of archimedean place parameters, and their transport along field isomorphisms | Langlands classification for `GL_n(ℝ)`, `GL_n(ℂ)` (Knapp 1994); conjugation of complex standard modules | Not stated. Block lists are not unique as lists (order; weight-zero induced blocks; weights `k` and `−k`), so uniqueness must compare the attached Weil representations. Needed only once a statement compares parameters of different presentations |

All proofs of the unproved statements in section 1 are separate obligations.
Several already have focused proof tasks; consult the task pool and the shared
proof DAG node of each statement.

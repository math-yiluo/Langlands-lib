# Compatible Galois families from unitary Shimura cohomology: declaration coverage

This note maps compatible Galois-family existence and multiplicity removal from
unitary Shimura cohomology to Lean declarations. Sections 1.1–1.4
describe Library commit `ed924aef420de137b4cbaa3b063a3618afcd73fd`. Section 1.5
describes the statements on Shimura cohomology, built on Library commit
`c0debd6f4dd02fdd68d70811cf610906b945a962`. The checks used Lean 4.34.0 and
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Modules are given relative to
`Langlands/`. Use the declarations by their Lean names from the current
Library. The SHA256 values in section 4 identify the versions described here.

**How to read the status.** Every target below is a `Prop`-valued `def`.
A statement in the Library fixes the formulation and its agreement with the
original source; it does not prove the proposition. At Library commit
`320321b3cd4b5100d54cf785192677d59479e65f`, no Library theorem proves any
statement in section 1, and no Library theorem takes one as a hypothesis. So
every statement is an unproved obligation. A search by name in the present
Library finds no proof of any statement of section 1 either. Outside the modules of section 1,
the only Lean files that use one of the statement names are three Prop-valued
reduction statements for Harris's Proposition 4.8, in namespace
`Langlands.Global.Harris`. Each of them takes
`Harris1998Theorem12CuspidalStatement` (section 1.3) as a premise:
`Proposition48PrimeBranchStatement` and `Proposition48SingletonBranchStatement`
as an implication premise, and `Proposition48ReductionStatement` as a conjunct
of its antecedent (modules
`Global/Arithmetic/HarrisProposition48PrimeBranchStatement`,
`Global/Arithmetic/HarrisProposition48SingletonBranchStatement`,
`Global/Arithmetic/HarrisProposition48ReductionStatement`). These are
conditional consumers: they are themselves unproved statements, and they do
not prove `Harris1998Theorem12CuspidalStatement`. None of the statements of
section 1 is an axiom or a structure field. Each pair's Markdown gives the exact quantifiers,
normalizations, page locators, registered fingerprints and source gaps. This
note summarizes them and does not replace them.

## 1. Published statements and definitions

### 1.1 Clozel's existence theorems (before removing the multiplicity)

| Module | Declarations | Original source | Status |
| --- | --- | --- | --- |
| `Galois/ClozelSelfDualStatements` | `Langlands.GaloisRepresentation.{clozelEulerPolynomial, IsClozelSystem, IsClozelUnitarySystem, Clozel1991Theorem57Statement, Clozel1993Theorem26Statement}` | Clozel 1991 (Publ. IHÉS 73), (5.1)–(5.3), Déf. 5.2, p.131; Thm 5.3, p.132; §5.3, Thm 5.7, p.142. Clozel 1993 (Duke 72), §2.6, Thms 2.5–2.6, pp.771–772 | Unproved |
| `Global/CMReflexField` (definitions) | `Langlands.Global.CMType.{partialTrace, reflexField, clozelReflexField, toClozelReflexField}`, with `clozelReflexField_inducedFromImaginaryQuadratic` | Clozel 1991 §5.1, p.131 | Definition |

`Clozel1991Theorem57Statement` covers a CM field `K`, `n = r + 1 ≥ 3`, and a
regular algebraic, conjugate self-dual cuspidal class. The class must have
square-integrable components at both places above a split place `v₀`, and at
both places above a second split place `v₁` in Clozel's bad-parity case
(`2 ∣ n`, `4 ∤ n`, `[K : ℚ]/2` odd). The conclusion: for every CM type `Σ` and
`ι₀ ∈ Σ` there are `L`, `ι`, `S`, `a > 0` and a compatible family of
representations of `Gal(Ē/E)`, where `E` is Clozel's reflex field. The family
is pure of weight `n − 1` and has rank `a n`. Its Euler polynomials outside
`S` are the `a`-th powers of `clozelEulerPolynomial`.
`Clozel1993Theorem26Statement` asks instead for supercuspidal components at
both places above `v₀`, has no parity condition, and allows `n ≥ 2`. Its
conclusion is association after the unitary normalization, with some weight
`m`. The reason is that Clozel 1993 §2.6 is informal about the normalization.
The reflex-field distinction is kept: `E = Σ.clozelReflexField ι₀` can be
larger than `K`. It equals `K` for a CM type induced from an imaginary
quadratic subfield, which is Harris's case.

### 1.2 Taylor's removal of the multiplicity and the Hodge–Tate input

| Module | Declarations | Original source | Status |
| --- | --- | --- | --- |
| `Galois/Local/HodgeTate` (definitions) | `Langlands.GaloisRepresentation.HodgeTate.{Closure, Completed, galoisRingHom, cyclotomic, HasHodgeTateDecomposition}` | Harris 1997 (Invent. 129) §3, p.103 | Definition |
| `Galois/TaylorMultiplicityRemovalStatement` | `Langlands.GaloisRepresentation.{HasHodgeTateDecompositionAt, TaylorMultiplicityRemovalStatement}` | Harris 1997 Thm 2, p.100, and the sketch of Taylor's proof, pp.102–103 (Taylor's letter [T] was not available) | Unproved |

`TaylorMultiplicityRemovalStatement` takes a `λ`-adic representation `A` of a
number field `K` and makes three assumptions. Outside a finite set `T` and
away from `ℓ`, `A` is unramified and a geometric Frobenius acts with
characteristic polynomial `P_v(X)^m`, where `P_v ∈ L[X]` is monic of degree
`n`. In Lean this is the Euler polynomial `det(1 − A(Frob_v) X)`, which is the
image in `L_λ[X]` of the reverse `X^{nm} P_v(X^{-1})^m` of `P_v^m`. At one
place above `ℓ`, `A` has a Hodge–Tate decomposition with `n` distinct twists,
each of multiplicity `m`. Its conclusion gives a rank-`n` representation `U`
over a finite extension `Λ` of `L_λ`. For every `g`, the characteristic
polynomial of `A(g)`, with coefficients extended to `Λ`, is the `m`-th power of
that of `U(g)`. By Brauer–Nesbitt this means
`(A ⊗_{L_λ} Λ)^{ss} ≅ (U^{ss})^{⊕m}`. At every `v ∉ T` not above `ℓ`, `U` is
unramified, the characteristic polynomial of a geometric Frobenius is the
image of `P_v` in `Λ[X]`, and so its Euler polynomial is the image of the
reverse `X^n P_v(X^{-1})` (Lean: `(P v).reverse` mapped to `Λ`). Its Markdown
records that Harris prints the false equality `H⁰ ∩ N = 1` on p.103. That
error does not affect the statement.

### 1.3 Harris's existence theorems

| Module | Declarations | Original source | Status |
| --- | --- | --- | --- |
| `Galois/WeakAssociation` (definitions) | `Langlands.GaloisRepresentation.{UnitaryMatchesSpectrum, IsWeaklyAssociatedToSpectrum, IsSumWeaklyAssociatedToSpectrum}`; `Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.{IsWeaklyAssociated, IsSumWeaklyAssociated}`; `Langlands.Automorphic.PositiveRankCuspidalClass.IsSpectrumWeaklyAssociated` | Harris 1998 (Invent. 134) Def. 1.1, pp.183–184; Harris 1999 (5.6), p.313 | Definition |
| `Automorphic/SquareIntegrableComponent` (definitions) | `Langlands.Automorphic.LocalRealization.IsSquareIntegrable`, `Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.HasSquareIntegrableComponent` | Harris 1998 Thm 1.2(i), p.185; Clozel 1991 Thm 5.7(ii), p.142 | Definition |
| `Galois/Harris1998ExistenceStatement` | `Langlands.GaloisRepresentation.{Harris1998Theorem12Statement, Harris1998Theorem12CuspidalStatement}` | Harris 1998 §1, Thm 1.2, pp.183–185 | Unproved |
| `Galois/Harris1999Theorem59Statement` | `Langlands.GaloisRepresentation.Harris1999Theorem59iStatement` | Harris 1999 (J. Math. Kyoto Univ. 39) §1, p.301; §4, p.308; (5.6), p.313; Thm 5.9(i), pp.314–315 | Unproved |

`Harris1998Theorem12Statement` is stated for the cuspidal spectrum `(nⱼ, πⱼ)`
of an isobaric `π ∈ Reg(n, E)` over `E = E₀ K₀`, where `E₀` is totally real and
`K₀` imaginary quadratic. Each `πⱼ` is regular algebraic and conjugate
self-dual, and has a square-integrable component at a finite place whose
residue characteristic splits in `K₀`. The conclusion gives finitely many
compatible families, each pure of its own weight, whose ranks sum to `n` and
whose direct sum is weakly associated to the spectrum. Weak association means
matching of unitarily normalized Euler polynomials at almost all places. The
Library has no construction of isobaric sums, so the statement is made on the
spectrum. `Harris1998Theorem12CuspidalStatement` is the cuspidal case.
`Harris1999Theorem59iStatement` assumes `𝒦 ⊇ 𝒦₀` imaginary quadratic and
`n > 1`. Its cuspidal class is regular algebraic and conjugate self-dual, and
supercuspidal at a place `v` with `c(v) ≠ v`. The conclusion gives a pure
compatible family of rank `n`, with no excluded coefficient place, weakly
associated to the class. All of these statements assert unramified matching
only; none asserts ramified local compatibility.

### 1.4 Harris's twisting character `ν̄(π)`

| Module | Declarations | Original source | Status |
| --- | --- | --- | --- |
| `Global/HeckeNormPower` (definitions) | `Langlands.Global.HeckeCharacter.{normPowerValue, normPower}` and their lemmas | Standard (the character `‖·‖^s` of the idele class group) | Definition |
| `Galois/HeckeCharacterRealization` (definitions) | `Langlands.GaloisRepresentation.{LambdaAdicCharacter, LambdaAdicCharacter.atFinitePlace, LambdaAdicCharacter.IsUnramifiedAt, IsLambdaAdicRealization}` | Harris 1999 (5.6), p.313 (geometric Frobenius ↔ uniformizer) | Definition |
| `Galois/HarrisTwistingCharacter` (definitions) | `Langlands.Global.Harris.{nuCharacter, nuBarCharacter}`, `Langlands.GaloisRepresentation.Harris.IsNuBarRealization` | Harris 1998 Erratum (E.1)–(E.2), (E.4), pp.181–182; Harris 1999 (5.4) and Thm 5.7(i), p.313 | Definition |

`nuBarCharacter n ξ₀` is `ξ₀(N_{𝒦/𝒦₀}(c(a)))⁻¹ · ‖a‖^{(n−1)/2}`, the corrected
formula of the erratum. `IsNuBarRealization` states only the relation between
a `λ`-adic character and `ν̄`. Both the existence of such a character and the
algebraicity of `ν̄` are left unstated.

### 1.5 Statements on the cohomology of the CM Shimura varieties

| Module | Declarations | Original source | Status |
| --- | --- | --- | --- |
| `Shimura/PEL/HarrisTaylorCMLambdaHodgeTateStatement` | `Langlands.GaloisRepresentation.HodgeTate.HasUnderlyingHodgeTateDecomposition` and `Langlands.GaloisRepresentation.HasUnderlyingHodgeTateDecompositionAt` (definitions); `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.CMHarrisLambdaCohomologyHodgeTateStatement` | Harris 1999, proof of Thm 5.7, pp.313–314, and Introduction, p.299; Faltings 1988, III, Thm 4.1, p.298, and Introduction 1(b), p.255 | Unproved |
| `Shimura/PEL/HarrisTaylorCMKottwitzStatement` | `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.CMHarrisKottwitzLambdaAdicStatement` | Kottwitz 1992 (Invent. 108) §1, pp.654–657, Thm 1, p.657; §5, p.661 | Unproved |
| `Shimura/PEL/HarrisTaylorCMHarrisTheorem57Statement` | `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.CMHarrisTheorem57Statement` | Harris 1999 §4, pp.308–309, (4.2); §5, p.312; (5.6) and Thm 5.7(i)–(ii), p.313; Harris 1997 [H1] §1, (R), pp.79–80, 82; Harris 1998 Erratum (E.1)–(E.2), pp.181–182, and Appendix, p.206 | Unproved |

All three are stated for the Library's CM Shimura varieties `S_U` of Harris's
signature and the Library's `λ`-adic cohomology with coefficients in a
general algebraic representation `ρ` of the unitary similitude group `GG`.
That cohomology, its tower, the Hecke multiplicity spaces and the isotypic
parts with their Galois representations come from the modules
`Shimura/PEL/HarrisTaylorCMLambdaCohomologyObjects` and
`Shimura/PEL/HarrisTaylorCMLambdaTower`. Each statement assumes that `A` is a
division algebra. `CMHarrisTheorem57Statement` also assumes Harris's
condition (R) of [H1] (Harris 1997, p.79), to whose framework Harris 1999, §4,
returns: at every finite place of `F`, `A` is split or a division algebra. It
also assumes that the algebra `D'` of the inner form is a division algebra
([H1], p.80). The neighbouring statement of Harris 1999 (5.1),
`CMHarrisVanishingStatement` (`Shimura/PEL/HarrisTaylorCMHarrisVanishingStatement`),
uses the same form of (R) but does not assume that `D'` is a division algebra.

`CMHarrisLambdaCohomologyHodgeTateStatement` says that `H^d(S_U ×_F F̄, W)_λ`
has a Hodge–Tate decomposition at every place of `F` above `ℓ` as a
`ℚ_ℓ`-representation (`HasUnderlyingHodgeTateDecompositionAt`): a
`C_w`-linear, Galois-equivariant `C_w ⊗_{ℚ_ℓ} V ≅ ⊕_i C_w(k_i)`, not required
to be `K_λ`-linear. A `K_λ`-linear form with free summands would force equal
weights at all coefficient embeddings. Its Markdown gives an in-scope example
where that fails (the reduced norm on `GU(2,1)` with
an inert coefficient prime).

`CMHarrisKottwitzLambdaAdicStatement` is Kottwitz's Theorem 1. It has
irreducibility over `K̄` of `ρ` and `π_f`, and the weight `w = w(ξ)` given by
the action `t^{−w}` of the central scalars (the sign comes from Kottwitz's
purity paragraph, p.661). Kottwitz's `W^i(π_f)_λ` is the Library's Hecke
multiplicity space, and `P(π_p, E_v)` is the Library's `IsKottwitzPolynomial`.
Weights use `Cohomology.Weights.{IsWeilNumber, IsPurePolynomial}`. The
conclusion is the existence of an integer `a` and a finite set `S` of primes
with two properties. (a) `a ≠ 0` iff some `W^i(π_f)_λ ≠ 0`. (b) Assume
`a ≠ 0`. Let `p ∉ S` be a prime at which `F` is unramified, with a standard
unramified chart whose level is the `p`-component of the level `U`, and let
`π_p` be the component of `π_f` at `p`. Then `π_p` is unramified, and for
every `P` attached to `π_p` by `IsKottwitzPolynomial` the following hold: the
parity and weights of the roots of `P`; the unique factorization
`P = ∏_{i ≤ 2(n−1)} P_i` into pure factors; and
`HasEulerPolynomialAt W^i(π_f)_λ v (P_i^{|a|})^rev` for every `λ` not above
`p`. As in Kottwitz's Theorem 1(b), printed p.657, nothing is claimed in (b)
when `a = 0`.

`CMHarrisTheorem57Statement` is Harris's Theorem 5.7(i)–(ii). It uses
`ρ' = JL(π_f)` (`IsHarrisJacquetLanglandsTransfer`) with `π_v` supercuspidal
and the factor `ℚ_p^×` of (4.2) acting trivially. `ξ₀` is the central
character of `ρ'` on the finite ideles of `𝒦₀`, and `ν̄(π)` is given by a
realization (`Harris.IsNuBarRealization`) at a place above the cohomology
prime `ℓ`, carried by a continuous embedding into a topological field
`M ≅ ℂ` (through `j : M ≃+* ℂ`), over which `JL(π_f)` has a model. `JL(π_f)` is assumed
to occur in `H^{n−1}`. (i) The characteristic polynomials of
`[H^{n−1}(S_U, W)[π] ⊗ ν̄(π)]^*` are the `a`-th powers of those of an
`n`-dimensional `ρ(π)`. (ii) At almost all places, `ρ(π)` is unramified and
`unitaryEulerPolynomial` of its Euler polynomial is that of the unramified
base-change eigenvalues `UnramifiedChart.baseChangeEigenvalues`.

## 2. Dependencies between the statements

No Lean theorem connects the statements; the following is the proof route of
the sources, recorded for their proofs.

- Harris 1998 Thm 1.2 and Harris 1999 Thm 5.9(i) are deduced from Clozel's
  theorems (`Clozel1991Theorem57Statement` in the good-parity case,
  `Clozel1993Theorem26Statement` for the bad parity in the supercuspidal
  case). Clozel's theorems rest on Kottwitz 1992 Thm 1 (section 3.1) and on
  stable base change and the transfer to the unitary group (Clozel 1991 §4,
  Proposition 4.11, printed pp.129–130; Clozel 1993 Prop. 2.3), which are not
  stated. Clozel 1991's own later references to this transfer, on printed
  pp.130 and 142, call it "proposition 4.8". That number is stale: Lemme 4.8,
  printed p.127, is a lemma on twisted conjugacy, and the transfer is
  Proposition 4.11. The multiplicity
  `a` is then removed by `TaylorMultiplicityRemovalStatement`, and the
  resulting `U_λ` must be assembled into a Library `Collection`. Harris 1998
  Thm 1.2 with square-integrable components only also cites Blasius
  (unpublished) for the remaining bad-parity cases. Clozel 1993 Thm 2.6 does
  not replace that input, because it needs supercuspidal components.
- `TaylorMultiplicityRemovalStatement` needs two hypotheses: the
  Frobenius-polynomial identities `P_v^m` from Kottwitz and Clozel
  (`CMHarrisKottwitzLambdaAdicStatement`), and the Hodge–Tate decomposition
  `HasHodgeTateDecompositionAt` with `n` distinct twists of multiplicity `m`.
  Harris 1999 (proof of Thm 5.7, pp.313–314) obtains the second from the
  geometric origin of the coefficient systems `W`: they come from tensor
  powers of the cohomology of the universal abelian scheme, so Faltings'
  theorem applies. `CMHarrisLambdaCohomologyHodgeTateStatement` states what
  this gives, the decomposition of the underlying `ℚ_ℓ`-representation of the
  whole cohomology. It does not give Taylor's `K_λ`-linear hypothesis with
  equal weights at all coefficient embeddings, and that hypothesis can fail
  for general `W` (section 1.5). Passing to the isotypic part and finding a
  `K_λ`-linear form suitable for Taylor's argument is an unformalized step of
  the proof of Thm 5.7(i) (section 3.2).
- `CMHarrisTheorem57Statement` (i) is Taylor's theorem applied to the
  isotypic part `[H^{n−1}(S_U, W)[π] ⊗ ν̄(π)]^*`, with `ν̄` from section 1.4.
  (ii) is Kottwitz's and Clozel's unramified identity, expressed through
  quadratic base change. For Harris's signature, the published
  `kottwitzPolynomialOf_harrisCharts` (`Shimura/Unitary/KottwitzHarrisComparison`)
  relates `P(π_p, E_v)` to the base-change parameter, up to a scalar `α` that is
  not yet identified (section 3.2).

## 3. Remaining source and proof boundaries

Every statement of this note is now stated. The following boundaries remain.
Each is documented in the Markdown of the statement concerned.

### 3.1 Kottwitz 1992, Theorem 1 (`CMHarrisKottwitzLambdaAdicStatement`)

- `a(π_f)` is defined by Kottwitz from automorphic multiplicities and
  pseudo-coefficients at infinity, which the Library does not have. The
  statement asserts only that some integer `a` has the properties of the
  theorem.
- Kottwitz's condition (c) on the function `f_{π_f}` is replaced by the
  existence of some finite set `S` of primes. Conditions (a) and (b)
  (unramified at `p`, level `K_p × K^p` with `K_p` the level of a standard
  unramified chart) are explicit hypotheses.
- Only Harris's signature is covered (the Library has no other `λ`-adic
  cohomology), and the reflex field must be `Φ τ₁(F)` (`3 ≤ n` or a second
  real place). The identification of the Library's `S_U` with Kottwitz's
  canonical model, and of the Library's coefficient system with Kottwitz's
  `F_ξ`, is not formalized.
- The claims are made for every `P` with `IsKottwitzPolynomial`. The existence
  of a principal-series parameter, its uniqueness up to the Weyl group and the
  descent of `P` to `L[X]` are not proved in the Library.
- The fixed-vector comparison, continuity and finite-dimensionality of the
  Library's cohomology are hypotheses, not proved.

### 3.2 Harris 1999, Theorem 5.7(i)–(ii) (`CMHarrisTheorem57Statement`)

- The statement is made at every small level, not only at Harris's `K(N)`.
- Of the hypotheses of [H1], §1, condition (R) is assumed. The hypothesis
  that `ℬ` is a division algebra at "a large (unspecified) number" of places
  is not a precise condition and is not formalized; its consequence used in
  [H1], p.80, that `D'` is a division algebra, is assumed. The assumption of
  [H1], §2, that `ℬ` is a division algebra above `p` is dropped, as in Harris
  1998, Appendix, p.206.
- `JL(π_f)` is the published relation: its existence and uniqueness are not
  proved, and the inputs `s`, `t`, `f`, `e` of the transfer are given. The
  model of `JL(π_f)` over `M` is described relationally through `j`.
- A `λ`-adic realization of `ν̄(π)` at a place above `ℓ`, with a continuous
  coefficient embedding into `M`, is quantified over, not constructed. The
  choice of `ν̄` rather than `ν` follows Harris 1999. Its match with the
  Library's Shimura datum (Harris 1998 Erratum, (E.2)) is not formalized.
- Automorphy of `π` is replaced by the occurrence of `JL(π_f)` in
  `H^{n−1}(S_U, W)_λ`.
- For a proof of (ii) through `kottwitzPolynomialOf_harrisCharts`, the scalar
  `α` there must be identified with Clozel's `q_w^{(n−1)/2} α_{E,w}(ϖ_w)`; its
  independence of the lift is not proved.
- For a proof of (i), Taylor's hypothesis needs a `K_λ`-linear Hodge–Tate
  decomposition of the isotypic part with `n` distinct twists of equal
  multiplicity. The Hodge–Tate statement of section 1.5 does not supply it.
- Part (iii) belongs to the Harris–Berkovich branch; see
  [`harris-cohomology-coverage.md`](harris-cohomology-coverage.md).

### 3.3 Hodge–Tate property (`CMHarrisLambdaCohomologyHodgeTateStatement`)

- Faltings's theorem has constant `ℚ_p` coefficients and needs properness
  (the division-algebra hypothesis gives proper Shimura varieties, which is not
  formalized). The reduction from `W` to schemes built from the universal
  abelian scheme, as Harris indicates, is not formalized.
- Faltings 1988 prints the twist `Ĉ(−a)` in Chapter III, Theorem 4.1
  (p.298), and `Ĉ(−b)` in the Introduction, 1(b) (p.255). The statement only
  asserts that some list of twists exists, so the misprint does not affect it.
  The source is registered as
  `provided-1991b7d5032d5fe94ca932ccbeccf293bafd80aa29a350ed2fda545cf46b9440`.

### 3.4 Proofs

The proofs of all statements in section 1 are separate obligations. So are
the transfer of `π_c` to the unitary group (Clozel 1991 §4, Proposition 4.11,
printed pp.129–130; Clozel 1993 Prop. 2.3), the assembly of Taylor's `U_λ` into a compatible
family over one coefficient field, Clozel's totally real base change
(Corollaire 5.4.2), and Harris's reduction of Thm 1.2 to cuspidal `π`. This
note records no proof of them.

## 4. Exact versions

SHA256 of the files at Library commit `ed924aef420de137b4cbaa3b063a3618afcd73fd`:

| File | SHA256 |
| --- | --- |
| `Langlands/Galois/ClozelSelfDualStatements.lean` | `9ebabed9984039ee618a2741f397f4e07eb99f98040c98341850ec3e8c24473c` |
| `Langlands/Galois/ClozelSelfDualStatements.md` | `1966c00a02c5d514c7be0fd68f7b57cab99a38632494a52a8d555b7d9915ab87` |
| `Langlands/Global/CMReflexField.lean` | `de0e33d61db12f2d46de026a23aaca4dfffefa752da79d4e7078a86fdd2c8434` |
| `Langlands/Global/CMReflexField.md` | `cc22bbac403270b3f95f06ff1f0f06a24d12e2c8ae3a9f5b1d09c7f0285061de` |
| `Langlands/Galois/Local/HodgeTate.lean` | `eed3f3e130b8f487b5e394f756089fb500b347a2e59c9cfd89782070c55edad0` |
| `Langlands/Galois/Local/HodgeTate.md` | `824d6e65b2ac52d12cf1ad547764550841a9e8698bb8dcd93cb507bff4d10d5d` |
| `Langlands/Galois/TaylorMultiplicityRemovalStatement.lean` | `fe425bf5cc29bac0cc324128e92b0777b484bcc43b8a8e595e8fb4cd2f2659bd` |
| `Langlands/Galois/TaylorMultiplicityRemovalStatement.md` | `ce7e2cb84742863d1cb2e1c7b64995c4fe96549924084a7ddb9928abf0ed090c` |
| `Langlands/Galois/WeakAssociation.lean` | `c9b07fbcdf2adf9c48b2def6a30d7c1945eda80cec0140c0b0762227e18ca136` |
| `Langlands/Galois/WeakAssociation.md` | `394b3fe6c94c91c3761c03a7632624ae478590e5e73af95d710daa4c98cc5518` |
| `Langlands/Automorphic/SquareIntegrableComponent.lean` | `623cebb8da9beb6bd6c4983167e1decee5181062d9eb32065de24002fb23572b` |
| `Langlands/Automorphic/SquareIntegrableComponent.md` | `242c12ae3ffc93b17301be3c1968da1b19a45b94f3d2a00690a93ec6a546880b` |
| `Langlands/Galois/Harris1998ExistenceStatement.lean` | `0dcf2a7f620bed8ce9e8f2aa238a0cee6a59d7c75e096bbda08f6cb7f9424a1f` |
| `Langlands/Galois/Harris1998ExistenceStatement.md` | `4c8dd9ff8e400cdafa6f1606baa959978e18d49e713bcd19743bcd2c3ec4730c` |
| `Langlands/Galois/Harris1999Theorem59Statement.lean` | `a35d820e1917c388259895dbaf953be947955e0f8285daf3930ede32a1d5e4bc` |
| `Langlands/Galois/Harris1999Theorem59Statement.md` | `9c82b72d91baacb6a31ab9d6ed1d074b235d88bc9d59f0d01d633ac6ca605ccc` |
| `Langlands/Global/HeckeNormPower.lean` | `6e2cbe74049e9056642fc827f281e92791e7bb45f6b42a7e75482462b312d8d9` |
| `Langlands/Global/HeckeNormPower.md` | `b4c7bf6c0adb79f0ef5e87ee4b6d228c7af6ace3b0109115fbff332d4d4bd851` |
| `Langlands/Galois/HeckeCharacterRealization.lean` | `3deb42feda11fd61e7df1ef42dfad3f6446ca555ff1b3d4e6ca73fa131b14a6f` |
| `Langlands/Galois/HeckeCharacterRealization.md` | `4582b9fa18bafc1f5be7a3d325fcfde234702998ccfc566b7e6a582a5543b2a2` |
| `Langlands/Galois/HarrisTwistingCharacter.lean` | `7555ac9bd7c3c072e4ea7d2d7c249ed873698d4faad1b3797a77153fccdac6ac` |
| `Langlands/Galois/HarrisTwistingCharacter.md` | `829c9af44e6afcb74b629beeef1cc2c71e74df7af04aa7f38c52921bbb89cca9` |
| `Langlands/Shimura/PEL/HarrisTaylorCMLambdaCohomology.lean` | `ce85f2ac077fb408870f33d578c93d62783b2dcd4f2ee4b9f2fb2bbc70a89ca3` |
| `Langlands/Shimura/PEL/HarrisTaylorCMLambdaCohomology.md` | `f0b230b9c1f0bee4313228b39f19c4c8032c7dc8b41f29e83cd9993319740eca` |

SHA256 at Library commit `b128d289028bf75629e9e364ecf151c484b27a85` (prerequisite
published after the commit above):

| File | SHA256 |
| --- | --- |
| `Langlands/JacquetLanglands/HarrisTransfer.lean` | `6808eca4905f6cc9fa5b64c49a1a88e5cbb72bdea68e16dbec1761e7eb1f0c8a` |
| `Langlands/JacquetLanglands/HarrisTransfer.md` | `0c88ef2693dc66d69904737bfc13783e319d21ced131da7241435f75691fe4f9` |

SHA256 at Library commit `cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e`
(prerequisites: unramified parameters, Kottwitz's polynomials and unramified base
change for unitary similitude groups; the λ-adic cohomology of Harris's CM Shimura
tower):

| File | SHA256 |
| --- | --- |
| `Langlands/Shimura/Unitary/KottwitzHarrisComparison.lean` | `ef642015df4045d6c891522659bf8e4f4fa1801c0827dd81ec7aad05174ce07b` |
| `Langlands/Shimura/Unitary/KottwitzHarrisComparison.md` | `29217ced07c32cb689adea7e09ddcf061e7cd707395621f261654a6479020169` |
| `Langlands/Shimura/Unitary/KottwitzFrobeniusPlaces.lean` | `e56e015030e1f3cc73376f975bc46af7679ca63e382463fb41b630363cbbb40b` |
| `Langlands/Shimura/Unitary/KottwitzFrobeniusPlaces.md` | `cce1040a795af9f111e3d3c280fc7182e6c37fc0023f122471b9f7badbd8872e` |
| `Langlands/Shimura/Unitary/KottwitzFrobeniusOrbits.lean` | `babf579c0e1382e2c777626c291065a7cf5704eb7110ede5f96b9fdd46935a1d` |
| `Langlands/Shimura/Unitary/KottwitzFrobeniusOrbits.md` | `35203ae0a8af915b4ef9233f9bff08898cf0f43b3f244d80b06d9a8e8df2f211` |
| `Langlands/Shimura/PEL/HarrisTaylorCMScaledGaloisCohomology.lean` | `ce2895b9f7b96cb798e2917e4cf41f91c499bc517dbc2a63e0d779245144d30b` |
| `Langlands/Shimura/PEL/HarrisTaylorCMScaledGaloisCohomology.md` | `2e5296e793a6ee5b29412aa470e5cd83d39248a6ea6d831595d08c2e0ba730ba` |
| `Langlands/Shimura/PEL/HarrisTaylorCMLevelTransportLaws.lean` | `1d57197d93dc754246e8cfe411f8b0ba08058d712a054d74404a25816d26cff7` |
| `Langlands/Shimura/PEL/HarrisTaylorCMLevelTransportLaws.md` | `c033041254c2a79ea6c812244e1c60e9e46c9a28d3e8123b3df5c218dd2ad535` |
| `Langlands/Shimura/PEL/HarrisTaylorCMScaledDescent.lean` | `9340a4f10c5dfa3fd088e38b69f945ab81fa7f08222c37861e0b39483a716cf0` |
| `Langlands/Shimura/PEL/HarrisTaylorCMScaledDescent.md` | `a47784dee244ca3c806cd343ca23f45ef3c866c36afb11b7d1cc0732eb90f7d0` |

SHA256 at Library commit `c0debd6f4dd02fdd68d70811cf610906b945a962`
(prerequisites: the λ-adic cohomology of Harris's CM Shimura tower and other
Library modules used by section 1.5):

| File | SHA256 |
| --- | --- |
| `Langlands/Shimura/PEL/HarrisTaylorCMLambdaTower.lean` | `7b69ac691b131dfa62dcda84e5551c1a4fd9d4720a7a852951632a1b4e776648` |
| `Langlands/Shimura/PEL/HarrisTaylorCMLambdaTower.md` | `edae2eba409e6fdf9f1d844b169c867dc311f8ed2385b593cada3b859613d7e7` |
| `Langlands/Shimura/PEL/HarrisTaylorCMLambdaCohomologyObjects.lean` | `eb658a31e9578a9edd859d4823762384f50ac3e8be80466c0e88932bf37e2afb` |
| `Langlands/Shimura/PEL/HarrisTaylorCMLambdaCohomologyObjects.md` | `0cdb5fa7ecd6855dc96351889cee1ebd296a8e61e37c5934da8544e9cbb3dc42` |
| `Langlands/Shimura/Unitary/KottwitzPolynomial.lean` | `52de96fde27dec9b5de3747ca2d831d11c5e1eecfc6510014bb6aa2219c238e9` |
| `Langlands/Shimura/Unitary/KottwitzPolynomial.md` | `057f8be3b9892ce333fff20a4d3b13b0e19886de7b13942c1b016788be816acd` |
| `Langlands/Shimura/Unitary/KottwitzBaseChange.lean` | `0769775bcf1bf8b411cff635b90ee733d0049fb7300e098ea694ea037fc47291` |
| `Langlands/Shimura/Unitary/KottwitzBaseChange.md` | `777fbc507946ca19449f77f798f31eed7502836276416dd7d1d879164f230fbb` |
| `Langlands/Cohomology/Weights/Polynomial.lean` | `47a03391e9b60f456f2b30133179940bb3fa75ee2b8c740b03641aaa0742964f` |
| `Langlands/Cohomology/Weights/Polynomial.md` | `0d2b84fde43d92f8476a81d37d4725c91a7f347a77ae88629704307846513a6b` |
| `Langlands/Galois/UnitaryNormalization.lean` | `e69517ce8000158f4e8afddd26748a28e56d3a78da51dd0ec1cd77801ebe3b92` |
| `Langlands/Galois/UnitaryNormalization.md` | `41430f38b33f6ec1d5587363605a91bc0e665b349b289b39fbf8fd2ef0b77568` |

SHA256 of the statements of section 1.5, as published at Library commit
`70eca2e4ea526de0ce0c41e4a9ea0e7d8087cbe7` (the Theorem 5.7 statement there
corrects an earlier formulation by adding condition (R) and the division
hypothesis on `D'`):

| File | SHA256 |
| --- | --- |
| `Langlands/Shimura/PEL/HarrisTaylorCMLambdaHodgeTateStatement.lean` | `e1ffa1a86090c579f41b66ee73fe2d44c3bfa658d4a809d2ef35a7004fca5563` |
| `Langlands/Shimura/PEL/HarrisTaylorCMLambdaHodgeTateStatement.md` | `c7cf0dde801ad330b5f79381948630f91cbaddd88257536b26cb2846d9a28d1e` |
| `Langlands/Shimura/PEL/HarrisTaylorCMKottwitzStatement.lean` | `69dec3e99ee274e3ed0131eb822709229c29aaeecb3b6ede2de462939135ab22` |
| `Langlands/Shimura/PEL/HarrisTaylorCMKottwitzStatement.md` | `238542de8741714d39f5a1ccb611d900cfca06411102ec217581135b0ef5bd9d` |
| `Langlands/Shimura/PEL/HarrisTaylorCMHarrisTheorem57Statement.lean` | `e385d16dcc38fc085635749954b95eb95137bf2eb807cb9982c4d4697faa1f83` |
| `Langlands/Shimura/PEL/HarrisTaylorCMHarrisTheorem57Statement.md` | `3dd0960e7de5b018db3a98e0ed1420c304b17e66243a8e576f5466fd0df6946c` |

These six files, and `Langlands/Galois/Harris1998ExistenceStatement.{lean,md}`,
are unchanged at Library commit `320321b3cd4b5100d54cf785192677d59479e65f`.
SHA256 at that commit of the conditional consumers of
`Harris1998Theorem12CuspidalStatement` named under "How to read the status":

| File | SHA256 |
| --- | --- |
| `Langlands/Global/Arithmetic/HarrisProposition48PrimeBranchStatement.lean` | `a45f9eafa622b746c4259fa0699b67d67dfdbbe908673e360cbb566482a79670` |
| `Langlands/Global/Arithmetic/HarrisProposition48PrimeBranchStatement.md` | `549c089de4175700355f1655be52e4c183ac25798bd2f4a5cd93267e1f17e3c9` |
| `Langlands/Global/Arithmetic/HarrisProposition48SingletonBranchStatement.lean` | `9528780225b44554193ee3ce0b720e1851844cc13bb348dc99f01cf99a4af6f4` |
| `Langlands/Global/Arithmetic/HarrisProposition48SingletonBranchStatement.md` | `ff09290e0e34cca27ffd4ab397a88034478c7bbe0fce4f50d387abb039e8233a` |
| `Langlands/Global/Arithmetic/HarrisProposition48ReductionStatement.lean` | `233f6c5b217400289af714f67efdb5ebd9feaf87c9686d0e06936be592b22ca1` |
| `Langlands/Global/Arithmetic/HarrisProposition48ReductionStatement.md` | `9a9cc4f7fe76913c0f477c71ca38f0725fb0e339d4cf4f1dc5aaa7dd7816a9c0` |

Registered originals cited: `clozel-1991-selfdual-galois` (SHA256
`9de7c13c9ae108e481de170327a06e44845cf87a6aabc1d5600176ee695e91ac`),
`clozel-1993-kottwitz-cohomology` (`cfc3a238c923958759ad6d5b0deedffe47b34c3749630463730b066b9402491b`),
`harris-1997-drinfeld-cohomology` (`aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`),
`harris-1998-local-langlands` (`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`),
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`
(`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`),
`kottwitz-1992-lambda-adic-simple-shimura`
(`749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`),
Faltings 1988 `provided-1991b7d5032d5fe94ca932ccbeccf293bafd80aa29a350ed2fda545cf46b9440`
(`2eb8b02f9e3e7662e1e79229488ee7e98240e23f221f1c9aaa7bec79cf329024`).

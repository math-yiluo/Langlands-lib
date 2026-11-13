# Compatible Galois families from unitary Shimura cohomology: declaration coverage

Author: Worker 34, for task `bd93b48c-db25-4739-89f5-97cabc0f6491` (Task 34)
revision 1: compatible Galois-family existence and multiplicity removal from
unitary Shimura cohomology. The previous instance's Worker 34 authored the
published units listed in section 1. Each pair's Markdown names its author.

This note maps that task's objective to Lean declarations of Library commit
`ed924aef420de137b4cbaa3b063a3618afcd73fd`, environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Modules are given relative to
`Langlands/`. Use the declarations by their Lean names from the current
Library. The SHA256 values in section 4 identify the versions described here.

**How to read the status.** Every target below is a `Prop`-valued `def`.
Publication accepts the formulation and its agreement with the original
source; it does not prove the proposition. At this commit no Library theorem
proves, or assumes, any statement in section 1: no other Library file uses the
statement names. So every statement is an unproved obligation. None is an
axiom or a structure field. Each pair's Markdown gives the exact quantifiers,
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

## 2. Dependencies between the statements

No Lean theorem connects the statements; the following is the proof route of
the sources, recorded for the proof tasks.

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
  Frobenius-polynomial identities `P_v^m` from Kottwitz and Clozel, and the
  Hodge–Tate decomposition `HasHodgeTateDecompositionAt` with `n` distinct
  twists of multiplicity `m`. Harris 1999 (proof of Thm 5.7, pp.313–314)
  obtains the second from the geometric origin of the coefficient systems `W`:
  they come from tensor powers of the cohomology of the universal abelian
  scheme. Faltings' Hodge–Tate theorem then applies (section 3.3).
- Harris 1999 Thm 5.7(i) is Taylor's theorem applied to the isotypic part
  `[H^{n−1}(S_K(N), W)[π] ⊗ ν̄(π)]^*`, with `ν̄` from section 1.4. Thm 5.7(ii)
  is Kottwitz's and Clozel's unramified identity, expressed through quadratic
  base change.

## 3. Not yet stated, with blockers and owners

### 3.1 Kottwitz 1992, Theorem 1 (printed p.657)

The statement needs four ingredients. The first is the unitary similitude
group `G` of `(D, *)` over `F` with Kottwitz's bad set (conditions (a)–(c),
printed pp.655–656, including hyperspecial `K_p`). The second is the
`λ`-adic cohomology `H^i(S_K ×_E Ē, F_λ)` with a general algebraic coefficient
system, together with its Hecke action and the multiplicity spaces
`W^i(π_f) = Hom_{H_K}(π_f^K, H^i)` (p.655). The third is the polynomials
`P(π_p, E_v)` of `V(π_p, E_v) = (r ∘ φ_{E_v}(π_p)) ⊗ Z` with
`Z(Φ) = (√p)^{[E_v:ℚ_p] dim S_K}` (p.656). The fourth is the integer
`a(π_f)` (p.657), defined from automorphic multiplicities and
pseudo-coefficients at infinity. The theorem has two parts. (a) `a(π_f) ≠ 0`
exactly when some `W^i(π_f) ≠ 0`. (b) Suppose `a(π_f) ≠ 0` and `v` is a place
of `E` above a good prime `p`. Then `π_p` is unramified. Every root of
`P(π_p, E_v)` is an algebraic number of weight `i + w(ξ)` for some `i` between
`0` and `2 dim S_K`; this `i` is even when `a(π_f) > 0` and odd when
`a(π_f) < 0`. `P(π_p, E_v) = ∏_i P_i(π_p, E_v)` uniquely, with monic factors
in `L[X]` whose roots have weight `i + w(ξ)`. For a place `λ` of `L` not above
`p`, `W^i(π_f)_λ` is unramified at `v`, and the characteristic polynomial of
`Φ` on it is `P_i(π_p, E_v)^{|a(π_f)|}`.

At this commit the Library has the fixed-level cohomology
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.cmHarrisLambdaCohomology`
(`Shimura/PEL/HarrisTaylorCMLambdaCohomology`). It also has the
propositions `CMHarrisLambdaCohomologyFiniteDimensional`,
`CMHarrisLambdaCohomologyContinuous` and
`CMHarrisLambdaCohomologyUnramifiedAt`. It has no level change, no
finite-adelic or Hecke action on this cohomology, and no isotypic part or
multiplicity space for `W` coefficients. The Kottwitz modules in
`Shimura/Unitary/` give `kottwitzCharpoly` for a dual-torus element and the
relation `IsKottwitzPolynomial` ("`P` is attached to `π_p`"). They do not
prove the existence of a parameter, the uniqueness of `P` given `π_p`, or the
descent of `P` to `L[X]`.

Later prerequisites, at Library commit
`cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e` (SHA256 in section 4):

- Task 5484 published three supporting units. The first is
  `cmHarrisScaledLambdaCohomology` (`Shimura/PEL/HarrisTaylorCMScaledGaloisCohomology`).
  It is the `λ`-adic cohomology as a functor of the scaled level
  (`CMScaledLevel`), with values in `K_λ`-linear `Gal(F̄/F)`-actions. Its
  value at a scaled level with level `U` is `K_λ ⊗_R lim_k H^d(X̄_U, W_k)`.
  The second is the transport laws of `Shimura/PEL/HarrisTaylorCMLevelTransportLaws`.
  The third is the generic descent `cmScaledDescent`
  (`Shimura/PEL/HarrisTaylorCMScaledDescent`) from scaled to small levels,
  which divides by powers of `ℓ`. The descent takes the target objects `O U`,
  isomorphisms `ψ` and the Props `CMScaledTransportRaise` and
  `CMScaledTransportShift` as inputs. The published modules neither compare
  `cmHarrisScaledLambdaCohomology` with `cmHarrisLambdaCohomology` nor prove
  these Props for it. So the finite-adelic and Hecke actions, the isotypic
  parts and the multiplicity spaces are still missing.
- Task 5424 published two units on Frobenius orbits. Under the Library's
  `KottwitzUnramified.IsUnramifiedAt (rationalPrimePlace p) K`,
  `frobeniusOrbitsArePlaces_of_isUnramifiedAt` (`Shimura/Unitary/KottwitzFrobeniusOrbits`)
  and `frobeniusInvariantsRational_of_isUnramifiedAt` prove the rationality
  hypothesis of `KottwitzLiftIndependence`, and `embeddingCochar_injective`
  (`Shimura/Unitary/KottwitzFrobeniusPlaces`) proves its injectivity
  hypothesis. Over an algebraically closed field and for a fixed `√p`, the
  polynomial of a principal-series parameter `ξ` therefore does not depend on
  the lift `t̂`, and a lift exists. Two things are still not proved: that
  `π_p` has a parameter `ξ` that is unique up to the Weyl group (a Satake
  statement), and that `P` descends to `L[X]`.

Owners: Task 5484 (`a88c0cf4-5010-4c43-921a-d9f53bcf6acb`, Workers 5484 and
5454) builds the cohomology with level and finite-adelic actions, isotypic
parts and multiplicity spaces (items 2–4). Task 5424
(`90fec325-2a43-439a-b699-ee0d8dcfd52c`, Worker 5424) is complete. Its five
items are the good primes, the unramified parameters, `P(π_p, E_v)`, the
unramified base change and the comparison of section 3.2. Task 34 states
Theorem 1 after Task 5484 publishes. `a(π_f)` needs automorphic
multiplicities on `G` and pseudo-coefficients at infinity. If these are not
available, any weaker existential form must be documented as weaker.

### 3.2 Harris 1999, Theorem 5.7(i)–(ii) (printed p.313)

Hypothesis: the factor `ℚ_p^×` of `GJ_p` in (4.2) acts trivially on `π`.
(i) The semisimplification of `Gal(𝒦̄/𝒦)` acting on
`[H^{n−1}(S_K(N), W)[π] ⊗ ν̄(π)]^*` is `a(π)` copies of an `n`-dimensional
`ρ(π)`. (ii) For almost all places `w` of `𝒦` above primes `p` at which `π` is
unramified, the normalized local Artin factor (5.6) of `ρ(π)` at `w` is
`L(s, BC_{𝒦/E}(π)_w)`. The statement needs:

- the isotypic part for `Π = JL(π_f)` at level `K(N)` as a Galois
  representation (Task 5484);
- Harris's transfer `JL(π_f)` from `GJ` to `GG`. Task 5443
  (`2452aeb3-01a4-4693-943a-4c52760dc26d`, Worker 5443) published it as
  `Langlands.JacquetLanglands.IsHarrisJacquetLanglandsTransfer`
  (`JacquetLanglands/HarrisTransfer`, Library commit
  `b128d289028bf75629e9e364ecf151c484b27a85`; SHA256 in section 4). It is a
  relation between irreducible admissible complex representations of
  `GJ(A_f)` and `GG(A_f)`. It is not a function: existence and uniqueness of
  `JL(π_f)` are not part of it. Supercuspidality at `v` is a separate
  hypothesis. The cohomology is over a field `M` extending `K_λ`, so stating
  Theorem 5.7 also needs `JL(π_f)` over `M`. This means a model of it over
  `M`, or a chosen field isomorphism to `ℂ`. That step is not yet formalized;
- `ν̄(π)` and its `λ`-adic realization (section 1.4);
- the unramified base-change parameters (Task 5424 item 4; the Library's
  `Shimura/Unitary/KottwitzBaseChange` has `baseChangeParameter`,
  `clozelParameter` and `IsBaseChangeParameterOf` for a chart). Task 5424
  item 5, `Shimura/Unitary/KottwitzHarrisComparison` (Library commit
  `cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e`), relates them to Kottwitz's
  polynomial. For Harris's signature it proves
  `kottwitzPolynomialOf_harris_baseChangeParameter`: for every normalized lift
  of a principal-series character `ξ`,
  `P(π_p, E_v) = ∏_{β ∈ BC(π)_w} (X − α · β^{f/f_w})`. Here `w` is the place
  of the CM field (`K` in that module) defined by `θ ∘ Φ τ₀`, where
  `θ : ℂ →+* Q̄_p`, `Φ` is the CM type and `τ₀` the real place of signature
  `(n − 1, 1)`. `f` is `localDegree`, `f_w` is the inertia
  degree of `w`, and `α` is one explicit scalar for all `β`. The hypotheses
  are `n ≥ 3` and the two conjuncts of `FrobeniusOrbitsArePlaces` at `Φ τ₀`.
  These conjuncts follow from unramifiedness at `p` by
  `frobeniusOrbitsArePlaces_of_isUnramifiedAt` (section 3.1).
  `kottwitzPolynomialOf_harris_baseChangeParameter_of_preserves` gives
  exponent `1` under a further hypothesis `hR`. Its Markdown explains `hR` as
  the Frobenius form of Clozel's condition that the reflex field of the CM
  type lie in `ι₀ F_c`, and does not formalize that explanation. The scalar
  `α` is not identified with Clozel's `q_w^{(n−1)/2} α_{E,w}(ϖ_w)`, and its
  independence of the lift is not proved. So the identity gives the
  eigenvalues of Frobenius on Kottwitz's `V` up to one common scalar.
  Theorem 5.7(ii) asserts an exact equality of normalized local factors, so
  a statement or proof built on this identity must still determine `α`.

Part (iii) belongs to the Harris–Berkovich branch (task
`b91b0934-0122-4c05-b359-4e7ed64bbe3d`); see
[`harris-cohomology-coverage.md`](harris-cohomology-coverage.md).

### 3.3 Hodge–Tate property of the cohomology (geometric origin)

Not stated. The intended statement: at every place of `F` above `ℓ`, the
`λ`-adic cohomology of the CM Shimura variety with Harris's coefficient system
`W` is Hodge–Tate. Its Hodge–Tate twists on the `π`-isotypic part are the
twists required by `HasHodgeTateDecompositionAt`. The statement needs the
Galois-representation packaging of the cohomology and its isotypic parts
(Task 5484 item 4). Harris 1999 pp.313–314 cites only the geometric origin of
`W` for this input. The original source of the Hodge–Tate decomposition is
Faltings, *p-adic Hodge theory*, J. Amer. Math. Soc. 1 (1988), Chapter III,
Theorem 4.1, printed p.298 (registered as
`provided-1991b7d5032d5fe94ca932ccbeccf293bafd80aa29a350ed2fda545cf46b9440`,
SHA256 `2eb8b02f9e3e7662e1e79229488ee7e98240e23f221f1c9aaa7bec79cf329024`;
PDF page = printed page − 253). Let `K` be complete for a discrete valuation,
of characteristic `0`, with perfect residue field of characteristic `p`
(Introduction, 1(b), printed p.255). For a smooth proper `K`-scheme `X` and a
divisor `D` with normal crossings, the theorem gives
`Gal(K̄/K)`-equivariant isomorphisms
`H^n_et((X − D) ⊗ K̄, ℚ_p) ⊗ Ĉ ≅ ⊕_{a+b=n} H^a(X, Ω^b(dlog ∞)) ⊗ Ĉ(−b)`,
with `Ĉ` the completion of `K̄`. This display corrects the source in one
place. Theorem 4.1 on printed p.298 prints the twist as `Ĉ(−a)`, with the same
indices `H^a` and `Ω^b`; the two displays for the proper case earlier on that
page also print `(−a)`. The Introduction, 1(b), printed p.255, states the
proper case of the same theorem (citing Chapter III, Theorem 4.1) with
`Ĉ(−b)` and says that `(−b)` denotes the Tate twist. It adds that a version
holds for complements of normal-crossings divisors. This note follows the
Introduction and reads `(−a)` on p.298 as a misprint: for `n = 1` the printed
`(−a)` would twist `H^1(X, O_X)` instead of the differentials `H^0(X, Ω^1)`.
The theorem concerns constant `ℚ_p` coefficients.
Harris says only that the systems `W` "come from tensor powers of the
cohomology of the universal abelian scheme". Deducing the decomposition for
the cohomology with coefficients in `W` from Faltings' theorem for schemes
built from that abelian scheme is part of the unstated input.

### 3.4 Proofs

The proofs of all statements in section 1 are separate obligations. So are
the transfer of `π_c` to the unitary group (Clozel 1991 §4, Proposition 4.11,
printed pp.129–130; Clozel 1993 Prop. 2.3), the assembly of Taylor's `U_λ` into a compatible
family over one coefficient field, Clozel's totally real base change
(Corollaire 5.4.2), and Harris's reduction of Thm 1.2 to cuspidal `π`. No
task owns these yet.

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
(prerequisites from Tasks 5424 and 5484):

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

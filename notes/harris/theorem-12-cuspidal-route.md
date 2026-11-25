# Harris 1998, Theorem 1.2 in the cuspidal case

The proof status of the declarations below was checked against the Library.

The published target is
[`Langlands.GaloisRepresentation.Harris1998Theorem12CuspidalStatement`](../../Langlands/Galois/Harris1998ExistenceStatement.md).
The conditional reduction is
[`Harris1998Theorem12CuspidalReductionStatement`](../../Langlands/Galois/Harris1998CuspidalReductionStatement.md).
Its consequent is that exact target with all four universes. At field universes
zero the two representation-carrier universes are still independent. Identifying
them gives the `.{0, 0, uV, uV}` instance used by the
[Proposition 4.8 reduction](proposition-48-route.md). The Library proves
neither the target nor the reduction.

The hypotheses are the actual CM composite `E = E₀ K₀`, regular algebraicity,
conjugate self-duality, and an actual square-integrable local component at a finite
place whose rational prime splits in `K₀`. In rank one the argument uses an algebraic
Hecke character. In rank at least two the geometric argument applies in even real
degree, and totally real quadratic base change and Galois patching handle odd real
degree. Each branch supplies a pure collection of the stated rank and with
almost-everywhere unramified matching. Each collection uses one coefficient number field with a
chosen complex embedding. A one-summand witness gives the published existential
finite sum of pure collections via
`isSumWeaklyAssociatedToSpectrum_unique_iff`. The numerical normalization has
weight `r` in rank `r+1`. The purity condition and
`unitaryEulerFromEigenvalues_eq_weight_substitution` remove the common positive
residue-cardinality factor and give the published unitary weak association.
[Arithmetic polynomial systems](../../Langlands/Galois/HarrisNormalizedSystem.md)

## Original sources and the parity issue

Harris 1998, pp. 183–186, defines the pure-sum convention and weak association,
states the hypotheses of Theorem 1.2, and uses unramified base change in
Definition 1.3. The proof paragraph on p. 185 attributes the geometric existence
under the stronger parity condition to Clozel, the refinements to Kottwitz and
Taylor, and the removal of the extra condition to unpublished work of Blasius.
Blasius §4.7, p. 12, announces the extension of his result to Clozel's cases
except for irreducibility. The printed passage gives no argument for the
parity step. The chosen proof route uses Clozel's split-place degree change
before Corollary 5.4.2 and the quadratic patching argument in Harris–Taylor,
VII.1.9, pp. 229–232. Sørensen's §1 Lemma 1 states the patching step separately.

Clozel 1993, §2.6, p. 772, uses the residual representation `J(π,2)`. A merely
square-integrable component need not give the required elliptic doubled
component. Its published `Clozel1993Theorem26Statement` uses supercuspidality.
The `Harris1999Theorem59iStatement` and `CMHarrisTheorem57Statement` also have
additional supercuspidal or transfer and occurrence hypotheses. The present
route uses comparison at unramified good places and the split-place transport
needed to keep the arithmetic auxiliary inside the scope of Theorem 1.2.

## Rank one

The determinant identifies the cuspidal rank-one class with an actual idele-class
character. The highest-weight infinitesimal character gives integral exponents
at complex places since the half-rank shift vanishes in this rank. Conjugate
self-duality gives `χ ∘ c = χ⁻¹`, and connected positive real ideles fixed by `c`
then give unitarity of `χ`. At an unramified place its uniformizer value is the
unique spherical eigenvalue. The statement is `HarrisRankOneHeckeSpectrumStatement`.

`AlgebraicUnitaryHeckeCharacterRealizationStatement` supplies common algebraic
values and one continuous Galois character over each completion of a single
number field. Serre's construction uses the algebraic finite part and a correction
at the coefficient prime. For purity, take a ray-class power of a good prime
and use the algebraic infinity type of the corresponding principal generator.
Opposite exponents in each CM embedding pair give weight zero at every conjugate.
The normalized finite quotient comparisons of the corrected character use the
geometric Frobenius convention and must give inertia triviality outside the
conductor and coefficient characteristic.

The reusable avatar and its finite normalized reciprocity inputs, including
the algebraic nonunitary characters needed for the CM central correction, are
stated as `AlgebraicHeckeCharacterAvatarStatement`,
`AlgebraicHeckeAvatarAssemblyStatement` and `FiniteHeckeAvatarLiftStatement`;
the Library proves the last (`finiteHeckeAvatarLift`) and not the first two.
The finite lift uses normalized Artin at each avatar kernel and a local
comparison for inertia and geometric Frobenius. The isolated
prescribed-kernel input `Langlands.Global.FiniteAbelianClassFieldExistenceStatement`
is proved in the Library (`finiteAbelianClassFieldExistence`).
[Avatar statements](../../Langlands/Galois/AlgebraicHeckeAvatarStatement.md),
[finite lift](../../Langlands/Galois/FiniteHeckeAvatarLift.md),
[Class-field theory audit](../reuse/nyll-global-cft-audit.md)

## The even-real-degree branch

1. The rational prime splitting in `K₀` gives two conjugate CM places over
   the place of `E₀`, and conjugate self-duality transports square-integrability
   between them. `ClozelOnePlaceExistenceStatement` supplies the one-place
   division configuration with Harris signature under the even-degree parity
   clause. The transfer must match the distinguished real place to the chosen
   embedding `e`. The prescribed embedding, the actual local split model, and
   the square-integrable conjugate transport are part of the geometric program.
   `CMType.clozelReflexField_inducedFromImaginaryQuadratic` gives the composite
   reflex calculation. The `HarrisSignatureCharts` reflex calculation uses a
   second real place in rank two. Clozel's printed rank bound in §5 comes from
   his reflex calculation, while the even-real-degree case has that second
   place. The exact one-place arithmetic existence result
   (`ClozelOnePlaceExistenceStatement`) is open (the Library derives it from `UnitaryLocalProfileRealizationStatement`: `clozelOnePlaceExistence_of_localProfile`).
2. Clozel 1991, pp. 129–130 Proposition 4.11 and §5.2–5.3, gives the route from
   Jacquet–Langlands transfer to cohomological stable unitary descent and the
   similitude extension. The proof needs actual occurrence in the middle-degree
   Hecke multiplicity with the same algebraic model and compatible central
   character. At unramified places compare the Kottwitz polynomial with the
   normalized `GL(n)` polynomial. The actual power family uses the common
   positive absolute value of Kottwitz's signed integer. Purity separates
   the degree terms and the CM central twist gives weight `n−1`. The monic
   root of an actual polynomial power descends over a characteristic-zero
   coefficient field by successive coefficients at the top of the polynomial.
   `CMHarrisKottwitzLambdaAdicStatement` expresses Kottwitz's proposition on
   `cmHarrisLambdaHeckeMultiplicityObjects`; its exact proof is open. The published
   `cmHarrisKottwitzLambdaAdic_of_traceComparison` derives this theorem from
   `CMHarrisKottwitzTraceComparisonStatement`. The virtual Frobenius trace
   identity and the comparisons with actual cohomology in that premise remain
   open. The Library's λ-adic cohomology of Harris's CM Shimura tower with
   coefficient systems (level and finite-adelic actions, isotypic parts and
   their Galois representations) and its unramified parameters and
   Kottwitz polynomials `P(π_p, E_v)` are reused.
   [Kottwitz trace deduction](../../Langlands/Shimura/PEL/HarrisTaylorCMKottwitzDeduction.md)
3. `CMHarrisLambdaCohomologyHodgeTateStatement` gives the published underlying
   `ℚ_ℓ`-linear finite-level comparison. The labels, the multiplicity projector,
   and the dimensions of its graded pieces still require an actual comparison.
   Harris 1999, pp. 313–314, uses coefficient systems of geometric origin from
   tensors of the universal abelian scheme's cohomology. For a prescribed
   embedding the regular highest-weight entries with the degree shifts give
   `n` distinct pieces, with the geometric multiplicity in each. Compare
   Harris–Taylor VII.1.9, pp. 227–228, which starts with the coefficient
   prime split in the imaginary quadratic field. The input here requires
   the chosen label for every coefficient prime. A proof must apply the
   geometric comparison at the other coefficient primes as well.

These transfer, model, occurrence, central normalization and labelled
geometric comparisons are missing. Their endpoint is `HarrisEvenGeometricPowerStatement`,
which asks for an actual completion-valued `HarrisPowerSystem` and regular
`HarrisLabelledWeights` for the same representations. The Kottwitz trace
calculation alone is insufficient for this endpoint. The geometric model
and labelled comparison keep the virtual Euler characteristic from being
used as a Galois representation. The compatible-family and comparison
statements of the Library are reused, within the broader Harris–Berkovich
cohomological framework.
[Coverage of the published comparison statements](../henniart/galois-family-coverage.md)

## Removing multiplicity over one coefficient field

The original `TaylorMultiplicityRemovalStatement` uses a decomposition over
`ℚ_ℓ` with the same weights at all coefficient labels. The present proof route
uses the companion `TaylorLabelledMultiplicityRemovalStatement` with
`HasLabelledHodgeTateAt`, the identity coefficient label after pullback to its
completion. Density and the closed monic-power locus extend the power identity
to the algebraic monodromy. The selected Hodge–Tate weights force the maximal
torus weights of the semisimplification to have multiplicity `a`. One can either
use the Sen operator as in Harris 1997, p. 103, or use Tate's twist invariants
and the Hodge–Tate grading on bounded-degree translated coordinate functions,
which preserves the monodromy's vanishing ideal. For disconnected monodromy the
stabilizer `N` of the Borel and maximal torus has `H⁰ ∩ N = T`. The average of
an orbit of other weights differs from a vertex weight. Generic torus translation
and the all-element power condition therefore make the extremal weight action
scalar. Removing the induced isotypic orbit iterates to a semisimple finite
extension model with the same labelled twists once.

The trace of the multiplicity-one model is the geometric trace divided by `a`,
so it lies in the original completion. `RegularHodgeTateCoefficientDescentStatement`
uses the trace pairing on the finite-dimensional image algebra and Tate's
twist invariants. On a simple component, the nonzero labelled graded piece has
dimension equal to the Schur index, and the division endomorphism algebra acts
on it over the base completion. Its dimension divides the piece's dimension,
forcing both the index and center degree to be one. This gives the actual model
over each original completion. `HarrisEvenMultiplicityReductionStatement`
collects these models into `HarrisEvenNormalizedExistenceStatement`. It keeps
one number field, one finite exceptional set and actual unramified matching.

## Removing the auxiliary quadratic extension

The arithmetic supply uses totally positive square classes of the real field
with prescribed split places and fresh odd valuation to ensure disjointness
from any specified finite extension. If a candidate square root lay in that
extension, its half-integral valuation would contradict unramifiedness at the
fresh prime. Two independent classes also give three
quadratic fields with a biquadratic composite. Outside the branch locus, every
place splits in at least one of them. The same imaginary quadratic factor is
retained upstairs and the real degree doubles.

The narrow split-place comparison of Arthur–Clozel III.5.1 identifies the weak
isobaric lift with a singleton cuspidal lift and transports the actual local
component. The weak lift is supplied by III.4.2(c). A proper normalized
induction cannot have the split square-integrable component. Strong multiplicity
one transports conjugate self-duality and the complex comparison transports
regular algebraicity. `HarrisParityBaseChangeStatement` assembles the weak lift,
the split-place comparison, the complex-place comparison and the complex
parameter bridge.
The arithmetic normalization scales each Satake root by `q^(r/2)` and hence
commutes with raising to the residue degree, since `q_w = q_v^f`.

The complex-place input is the standalone totally complex B7 proposition.
Clause C of `Langlands.Automorphic.Unramified.CyclicStrongBaseChangeSupportStatement`
gives the third conjunct of B7 after totally complex specialization. For
actual unitary isobaric data related by weak lifting along a prime-degree
cyclic extension, it asserts equivalence of the aggregate parameter relation
at a lower complex place and the transported relation at each actual upper
place. The planned conditional derivation of canonical B7 uses this
equivalence, the singleton and permutation comparisons, and the
regular-orbit induction comparison. The general strong-lift assertion of
Arthur–Clozel III.5.1 (pp. 212–213) at complex places and its translation to
the Library's aggregate predicate remain an external proof input (see the design decisions of the
[exact-stabilizer route](proposition-48-exact-stabilizer-route.md)).
The named premise first appeared in the Library at commit
`032961776f43ccd672c6266d265a9c644faeba13`. Its separate finite-place clause
uses the σ-lift vocabulary of
`Langlands.BaseChange.IsSigmaLiftOnSupercuspidals`. The R2 complex-place comparison requires
a supercuspidal pair, whereas Harris's parity input permits a square-integrable
component at the prescribed split place.
[Canonical B7 statements](../../Langlands/Automorphic/Unramified/CyclicWeakBaseChangeComplexPlaceStatement.md),
[strong-lift support and parameters](../../Langlands/Automorphic/Unramified/CyclicStrongBaseChangeSupportStatement.md),
[finite-place σ-lift vocabulary](../../Langlands/BaseChange/SigmaLiftOnSupercuspidals.md)

At a fixed coefficient place the upper representations over the common
spectral algebraic closure agree on composita by the Frobenius comparison,
and their semisimplifications are invariant under the quotient action. Apply
the quadratic patching lemma for the rich family. The fixed biquadratic triple
is used to bound one exceptional set and generate one number field containing
all the corresponding arithmetic polynomials, because a split place supplies
a degree-one comparison. Density puts the trace of the patched representation
in the base completion, whose image is closed. Use the finite coefficient
model, transport the label from an upper field, and descend by the same regular
Hodge–Tate argument. `HarrisOddNormalizedExistenceReductionStatement` gives the
odd output through these explicit inputs and the even-degree result.

## The named inputs and their status

All declaration names in the table are relative to `Langlands.GaloisRepresentation`
unless their namespace is given. The reduction and the two branch reductions are
conditional statements whose proofs are open. The original conclusion
still requires the exact proofs of all its premises. In particular, even-degree
geometry is an open input.

| Declaration or gap | Scope and proof status |
| --- | --- |
| `HarrisRankOneHeckeSpectrumStatement` | Actual spectrum of the supplied regular algebraic conjugate self-dual GL(1) class. Open. |
| `AlgebraicUnitaryHeckeCharacterRealizationStatement` | Uniform weight-zero λ-adic realization of the algebraic unitary character. Open; it is part of the avatar and finite reciprocity inputs described above. |
| `HarrisEvenGeometricPowerStatement` | Transfer, middle-degree occurrence, uniform arithmetic power, and regular labelled cohomology on the same family. Open; the missing comparisons are described above. |
| `Langlands.Shimura.FiniteUnitary.ClozelOnePlaceExistenceStatement` | Exact one-place algebra and involution. Open (the Library has the conditional `clozelOnePlaceExistence_of_localProfile`, from `UnitaryLocalProfileRealizationStatement`). |
| `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.CMHarrisKottwitzLambdaAdicStatement` | Exact Kottwitz multiplicity space. Open (the Library has the conditional `cmHarrisKottwitzLambdaAdic_of_traceComparison`, from `CMHarrisKottwitzTraceComparisonStatement`). |
| `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.CMHarrisLambdaCohomologyHodgeTateStatement` and the labelled graded comparison | The underlying comparison statement is in the Library and its proof is open; the reduction to the actual cohomology comparison and the missing labelled interface belong to the geometric comparisons described above. |
| `HodgeTate.TateTwistInvariantsStatement` | Degree-zero fixed field and nonzero twist vanishing of the completed algebraic closure. Open. |
| `TaylorLabelledMultiplicityRemovalStatement` | Local multiplicity extraction with one label and actual finite coefficient extension. Open. |
| `RegularHodgeTateCoefficientDescentStatement` | Actual model over the original completion with the same labelled weights. Open. |
| `HarrisEvenMultiplicityReductionStatement` | Conditional even collection assembly from the three named inputs. Open. |
| `Langlands.Global.Harris.HarrisParityAuxiliaryFieldsStatement` | Totally real quadratic supply and biquadratic cover. Proved: `harrisParityAuxiliaryFields`. |
| `Langlands.Global.Harris.ConjugateSelfDualUnitaryCentralCharacterStatement` | Central-character transport. Proved: `conjugateSelfDualUnitaryCentralCharacter`. |
| `Langlands.Automorphic.Unramified.CyclicPrimeIsobaricBaseChangeTCStatement` | Arthur–Clozel III.4.2(c) existence and uniqueness for the totally complex weak lift. Open (the Library has the conditional `cyclicPrimeIsobaricBaseChangeTC_of_cuspidal`). |
| `Langlands.Automorphic.Unramified.QuadraticWeakBaseChangeSplitSquareIntegrableStatement` | III.5.1 at a split square-integrable place and singleton cuspidality of the lift. Open (the Library has the conditional `quadraticWeakBaseChangeSplitSquareIntegrable_of_strongSupport`, from `CyclicStrongBaseChangeSupportStatement`). |
| `Langlands.Automorphic.Unramified.CyclicWeakBaseChangeComplexPlaceTCStatement` | Canonical B7 in its totally complex form. Open; the Library states no conditional derivation of it. |
| `Langlands.Automorphic.Unramified.CyclicStrongBaseChangeSupportStatement`, clause C | The aggregate complex-place comparison from Arthur–Clozel III.5.1. An unproved external input. |
| `Langlands.Automorphic.CuspidalComplexParameterBridgeTCStatement` | Actual infinitesimal character comparison and regular algebraicity. Proved: `Langlands.Automorphic.cuspidalComplexParameterBridgeTC`. |
| `HarrisParityBaseChangeStatement` | Conditional assembly of the four automorphic comparisons for the lifted class. Proved: `harrisParityBaseChange`. |
| `QuadraticPatchingStatement` | Patching and uniqueness for a rich family of actual quadratic restrictions. Proved: `quadraticPatching`. |
| `QuadraticFrobeniusPatchingStatement` | Invariance and agreement from the arithmetic root-power identities and recovery at split places. Proved: `quadraticFrobeniusPatching`. |
| `AbsoluteGeometricFrobeniusDensityStatement` | Krull density of good geometric Frobenius conjugates, from finite Chebotarev and completion compatibility. Proved: `absoluteGeometricFrobeniusDensity`. |
| `FiniteCoefficientModelStatement` | Finite local model over a field in the spectral algebraic closure, containing the given finite intermediate field, from rational trace. Proved: `finiteCoefficientModel`. |
| `HarrisOddNormalizedExistenceReductionStatement` | Conditional odd collection assembly from even existence and the supplied automorphic and patching results. Open. |
| `Harris1998Theorem12CuspidalReductionStatement` | Exact conditional cuspidal reduction. Open. |
| `Harris1998Theorem12CuspidalStatement` | Final unconditional assembly. Open. |

## Registered originals

- `harris-1998-local-langlands`, pp. 183–186.
- `clozel-1991-selfdual-galois`, Proposition 2.3 and prescribed-place remark,
  pp. 105–106, Proposition 4.11, pp. 129–130, (5.2)–(5.3), Theorem 5.3 and
  Corollary 5.4.2 pp. 131–133, §5.2–5.3 and Theorem 5.7 pp. 133–144.
- `clozel-1993-kottwitz-cohomology`, Theorem 2.6 and doubling argument p. 772.
- `blasius-1990-automorphic-forms-galois-examples`, *Automorphic Forms and Galois
  Representations: Some Examples*, pp. 1–13, particularly Theorem 4.2 and §4.7,
  pp. 10, 12. Printed page 12 is one-based PDF page 24.
  [Volume II editor scan](https://www.jmilne.org/math/Books/AA1988b.pdf)
- `kottwitz-1992-lambda-adic-simple-shimura`, Theorem 1 pp. 654–657 and §5 p. 661.
- `harris-1997-drinfeld-cohomology`, Taylor sketch pp. 102–103 and transfer p. 104.
- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, proof of
  Theorem 5.7(i), pp. 313–314.
- `provided-1991b7d5032d5fe94ca932ccbeccf293bafd80aa29a350ed2fda545cf46b9440`,
  Faltings 1988, Chapter III, Theorem 4.1, p. 298.
- `harris-taylor-2001-geometry-cohomology-simple-shimura`, VII.1.9, pp. 227–232.
- `sorensen-patching-lemma`, §1, Definition 1 and Lemma 1, author manuscript.
  [Author copy](https://mathweb.ucsd.edu/~csorense/patch.pdf)
- `arthur-clozel-1989-base-change`, I.5 pp. 48–49, III.4.2 pp. 202–203 and
  III.5.1 pp. 212–213.
- `clozel-milne-automorphic-forms-shimura-varieties-l-functions-i-1990`, Clozel's
  *Motifs et formes automorphes*, Definitions 1.8 and 3.12, pp. 89–90 and 111.
- `serre-abelian-l-adic-1989`, Chapter II §§2.3, 2.5 and 2.7,
  pp. II-10–II-12, II-18–II-20 and II-23–II-24.
- `serre-1977-linear-representations`, §12.2, pp. 92–94.
- `tate-1967-p-divisible-groups`, §3.3, Theorems 1–2, p. 176.
  [Scanned original](https://www.math.purdue.edu/~tongliu/teaching/598/p-divisible.pdf)

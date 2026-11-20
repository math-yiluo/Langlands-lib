# Harris 1998, Theorem 1.2 in the cuspidal case

Worker 773 and Worker 853 prepared this route for Task 6698
(`cd19dd55-136e-42e9-b062-5a23b2c7a6b2`). The declaration and proof status
below refers to Library `168b7fb5bf8d14e1be7bf425cb6cd43c1995d50d`.
Shared graph revision 586 records the proof route under
`proof.harris-global-galois-existence`.

The published target is
[`Langlands.GaloisRepresentation.Harris1998Theorem12CuspidalStatement`](../../Langlands/Galois/Harris1998ExistenceStatement.md).
The conditional reduction is
[`Harris1998Theorem12CuspidalReductionStatement`](../../Langlands/Galois/Harris1998CuspidalReductionStatement.md).
Its consequent is that exact target with all four universes. At field universes
zero the two representation-carrier universes are still independent. Identifying
them gives the `.{0, 0, uV, uV}` instance used by the Proposition 4.8 reduction in
Task 6413 (`bca10e59-d4e2-40a4-be9b-5d70eaa1acd2`). The owner of the exact original
proof is Task 7874 (`a2d0f23a-d026-467f-998d-8e1b9cd12b4d`).

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

Task 7875 (`f508c2ec-5e33-4087-abcb-a493b26ccbb9`) owns the reusable avatar
and its finite normalized reciprocity inputs, including the algebraic nonunitary
characters needed for the CM central correction. It has published
`AlgebraicHeckeCharacterAvatarStatement`, `AlgebraicHeckeAvatarAssemblyStatement`
and `FiniteHeckeAvatarLiftStatement`. Task 7345
(`d60e084d-9218-49be-9468-da445fab6919`) audited the class-field interfaces.
The finite lift uses normalized Artin at each avatar kernel and a local
comparison for inertia and geometric Frobenius. Task 7904
(`e5c80696-f292-40b6-b926-6bcd4a6bce5b`) owns the proof plan for the isolated
prescribed-kernel input `Langlands.Global.FiniteAbelianClassFieldExistenceStatement`.
The current class-formation quotient leaves prescribed-kernel existence and
normalized Frobenius identification on ideles open.
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
   place. Task 7862 (`32049389-5976-4c11-b29f-689ff00e4006`) owns the exact
   one-place arithmetic existence result.
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
   `cmHarrisLambdaHeckeMultiplicityObjects`. Task 7863
   (`8a28eeaa-d329-4955-97f9-754852c627cc`) owns its exact proof. The published
   `cmHarrisKottwitzLambdaAdic_of_traceComparison` derives this theorem from
   `CMHarrisKottwitzTraceComparisonStatement`. The virtual Frobenius trace
   identity and the comparisons with actual cohomology in that premise remain
   open. The constructions of Task 5484 (`a88c0cf4-5010-4c43-921a-d9f53bcf6acb`) and
   the unramified polynomial objects of Task 5424
   (`90fec325-2a43-439a-b699-ee0d8dcfd52c`) are reused.
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

Task 7864 (`28558a33-d44c-404f-939e-a3f1bfa41108`) owns these missing transfer,
model, occurrence, central normalization and labelled geometric comparisons
and their proof planning. The endpoint is `HarrisEvenGeometricPowerStatement`,
which asks for an actual completion-valued `HarrisPowerSystem` and regular
`HarrisLabelledWeights` for the same representations. The Kottwitz trace
calculation alone is insufficient for this endpoint. The geometric model
and labelled comparison keep the virtual Euler characteristic from being
used as a Galois representation. Task 34
(`bd93b48c-db25-4739-89f5-97cabc0f6491`) supplied the published compatible-family
and comparison statements. The broader framework belongs to
`b91b0934-0122-4c05-b359-4e7ed64bbe3d`.
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
Clause C of the draft `Langlands.Automorphic.Unramified.CyclicStrongBaseChangeSupportStatement`
gives the third conjunct of B7 after totally complex specialization. For
actual unitary isobaric data related by weak lifting along a prime-degree
cyclic extension, it asserts equivalence of the aggregate parameter relation
at a lower complex place and the transported relation at each actual upper
place. Task 7340 uses this equivalence, the singleton and permutation
comparisons, and the regular-orbit induction comparison to derive canonical
B7 conditionally. The general strong-lift assertion of Arthur–Clozel III.5.1
(pp. 212–213) at complex places and its translation to the Library's aggregate
predicate remain an external proof input under the operator's B7 ruling.
Task 7889 owns the strong-lift statement draft, using Task 7513
(`b4232035-f988-4ae7-84e0-3f644a479933`) for the published σ-lift vocabulary
in its separate finite-place clause. The R2 complex-place comparison requires
a supercuspidal pair, whereas Harris's parity input permits a square-integrable
component at the prescribed split place.
[Canonical B7 statements](../../Langlands/Automorphic/Unramified/CyclicWeakBaseChangeComplexPlaceStatement.md),
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

## The named inputs and their owners

All declaration names in the table are relative to `Langlands.GaloisRepresentation`
unless their namespace is given. The reduction and the two branch reductions are
published conditional statements with open proof tasks. The original conclusion
still requires the exact proofs of all its premises. In particular, even-degree
geometry is an open input with its own planning task.

| Declaration or gap | Scope and owner |
|---|---|
| `HarrisRankOneHeckeSpectrumStatement` | Actual spectrum of the supplied regular algebraic conjugate self-dual GL(1) class. Task 8076 (`060a607e-cab0-4a79-9c19-c50b6968ca45`) |
| `AlgebraicUnitaryHeckeCharacterRealizationStatement` | Uniform weight-zero λ-adic realization of the algebraic unitary character. Task 8077 (`8093ec6f-ed6e-409c-9e11-0fa0af0b1260`). The broader avatar and finite reciprocity program is Task 7875 (`f508c2ec-5e33-4087-abcb-a493b26ccbb9`). |
| `HarrisEvenGeometricPowerStatement` | Transfer, middle-degree occurrence, uniform arithmetic power, and regular labelled cohomology on the same family. Task 7864 (`28558a33-d44c-404f-939e-a3f1bfa41108`) owns the missing comparisons and their proof decomposition. |
| `Langlands.Shimura.FiniteUnitary.ClozelOnePlaceExistenceStatement` | Exact one-place algebra and involution proof, Task 7862 (`32049389-5976-4c11-b29f-689ff00e4006`). |
| `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.CMHarrisKottwitzLambdaAdicStatement` | Exact Kottwitz multiplicity-space proof, Task 7863 (`8a28eeaa-d329-4955-97f9-754852c627cc`). |
| `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.CMHarrisLambdaCohomologyHodgeTateStatement` and the labelled graded comparison | Underlying comparison statement is published and its proof remains open. The geometric comparison program Task 7864 (`28558a33-d44c-404f-939e-a3f1bfa41108`) owns the reduction to the actual cohomology comparison and the missing labelled interface. |
| `HodgeTate.TateTwistInvariantsStatement` | Degree-zero fixed field and nonzero twist vanishing of the completed algebraic closure. Task 7978 (`28be7ac6-cae5-43ca-a1ab-4fbfe10a5530`) |
| `TaylorLabelledMultiplicityRemovalStatement` | Local multiplicity extraction with one label and actual finite coefficient extension. Task 7997 (`56ae86cc-a5a8-47c5-bd11-809a242aeb0c`) |
| `RegularHodgeTateCoefficientDescentStatement` | Actual model over the original completion with the same labelled weights. Task 8075 (`c91668fe-5ea6-474e-9b14-cc9bd1474ff6`) |
| `HarrisEvenMultiplicityReductionStatement` | Conditional even collection assembly from the three named inputs. Task 8078 (`e4229a6a-2be3-44c4-a2d8-a46609c255b4`) |
| `Langlands.Global.Harris.HarrisParityAuxiliaryFieldsStatement` | Totally real quadratic supply and biquadratic cover. Task 7919 (`b861d3e8-af91-480f-840f-246620037eb6`) |
| `Langlands.Global.Harris.ConjugateSelfDualUnitaryCentralCharacterStatement` | Central-character transport. Statement owner Task 7822 (`364f76f1-154a-4269-9b0b-4cd6dc277a09`). Task 8014 (`72fdcf4b-aa1d-4c82-a60a-fdd66ed14bca`) |
| `Langlands.Automorphic.Unramified.CyclicPrimeIsobaricBaseChangeTCStatement` | Arthur–Clozel III.4.2(c) existence and uniqueness for the totally complex weak lift. Proof Task 7860 (`835f1bf4-f1d3-4a52-ac52-54475877d275`). |
| `Langlands.Automorphic.Unramified.QuadraticWeakBaseChangeSplitSquareIntegrableStatement` | III.5.1 at a split square-integrable place and singleton cuspidality of the lift. Task 7968 (`77f4211e-5a47-4f28-aef7-858306db19f3`) |
| `Langlands.Automorphic.Unramified.CyclicWeakBaseChangeComplexPlaceTCStatement` | Task 7479 (`abcbb7a8-e133-45df-b7cf-6413542ec954`) published canonical B7 and its totally complex form. Task 7340 (`0407c885-1c0b-496b-a8bf-829f3c1a7038`) owns the conditional derivation. |
| `Langlands.Automorphic.Unramified.CyclicStrongBaseChangeSupportStatement`, clause C | Task 7889 (`daa579fe-3dfe-42c0-98d3-87cc6da1bc8c`) owns the draft statement of the open aggregate complex-place input under the general III.5.1 program of Task 7343 (`d6ca8ef3-60ca-4650-a436-8b5a00655394`). |
| `Langlands.Automorphic.CuspidalComplexParameterBridgeTCStatement` | Actual infinitesimal character comparison and regular algebraicity. Task 7870 (`a97be363-c387-4cc1-b0d8-75e4761b29a1`) published `Langlands.Automorphic.cuspidalComplexParameterBridgeTC`, artifact `059c3673-af5d-4313-8777-42e5f877949a`. |
| `HarrisParityBaseChangeStatement` | Conditional assembly of the four automorphic comparisons for the lifted class. Task 7971 (`225355e9-9b94-4cd7-bf6c-e9d8e60874c9`) |
| `QuadraticPatchingStatement` | Patching and uniqueness for a rich family of actual quadratic restrictions. Task 7920 (`ec9a652c-b05e-4bc7-a62e-cee2e9b08970`) |
| `QuadraticFrobeniusPatchingStatement` | Invariance and agreement from the arithmetic root-power identities and recovery at split places. Task 7967 (`97c25937-0d6a-4902-9289-fba8bf52875d`) |
| `AbsoluteGeometricFrobeniusDensityStatement` | Krull density of good geometric Frobenius conjugates, from finite Chebotarev and completion compatibility. Task 7917 (`294ffeaa-9096-4ce6-9d78-56e243b84a91`), proof candidate `6abde398-db7e-4a07-8287-33f19c14db4c` awaiting Library publication at this pin. |
| `FiniteCoefficientModelStatement` | Finite local model over a field in the spectral algebraic closure, containing the given finite intermediate field, from rational trace. Task 7918 (`4d7bf80a-8544-48ea-b6e9-5c73730858f4`) |
| `HarrisOddNormalizedExistenceReductionStatement` | Conditional odd collection assembly from even existence and the supplied automorphic and patching results. Task 7972 (`2c9724b1-d9aa-422c-87e1-c2d892e30572`) |
| `Harris1998Theorem12CuspidalReductionStatement` | Exact conditional cuspidal reduction. Task 8079 (`fca5291b-2d81-4ea7-bcfe-8ebf46b16757`) |
| `Harris1998Theorem12CuspidalStatement` | Final unconditional assembly, Task 7874 (`a2d0f23a-d026-467f-998d-8e1b9cd12b4d`). |

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

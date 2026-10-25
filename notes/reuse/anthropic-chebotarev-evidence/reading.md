# Complete source reading record


## 25 October, rotation verification and definitions/Euler log

Fresh root check 36e1cd6c-0f83-4099-8a9c-309f1370f503 passed with 0 errors/0 warnings, independent audit_u/audit_v, unchanged type fingerprint 3947a480b5b576718094cd7dba79d66c903b9e17396b4d9146cfba4c005318fc and only propext/Classical.choice/Quot.sound. No task candidates exist. This is development evidence, not acceptance.

Read complete original NormClass, CompletedRayL, RayCharacterData, NormResidueCharacter, EuclideanIdealLattice, ClassGroupLSeries, and continuous-log solution. NormClass uses determinant congruence and positivity of the norm for totally positive principal generators to descend the absolute-norm character to the narrow ray group. NormResidueCharacter constructs Dirichlet pullbacks, parity from the value at -1, and proves norm classes lie in the actual cyclotomic automorphism image via arithFrobAt. It does not assume class-field reciprocity or the desired global realization theorem. Its image containment is one-sided at this stage. CompletedRayL is an explicit gamma/discriminant factor times the partial ideal-class L-series; ray coefficients count actual nonzero ideals in a narrow ray class. RayCharacterData defines explicit parity, finite primitivity and trace/Gauss conditions, with Type0 carriers in the original.

The continuous-log proof constructs -log(1-chi(P) NP^-s), using absolute ideal summability, unique factorization of integral ideals and finite Euler products exhausted by norm. The chosen log is continuous on the real half-line s>1; the prime terms have norm <=1/2 for s>=1 and log remainder is bounded by sum NP^-2. This proves nonvanishing for s>1 and a uniformly bounded logarithmic prime-sum error; it does not itself prove nonvanishing at s=1. Original private exports are packaging only, not extra mathematical premises.

## All shorter solutions and original theorem wrappers

Read all fourteen original theorem wrappers and all ten previously unread short solutions. The wrappers expose precisely their solution statements, using p2m_exact_reverting, with some global negative attributes (the cleaned draft removed those). The splitting solution proves trivial inertia by injectivity of roots-of-unity reduction away from m; its chosen Frobenius fixes the primitive root and hence is the identity, bounding all residue elements by roots of X^q-X. The degree formula then yields the full number of primes and equal residue norms. This is cyclotomic, not the arbitrary-Galois base-prime adapter.

The sign proof pairs complex embeddings and takes the product over real places. The entire-continuation solution only uses the nontrivial-character entire F clause of completedRayL_fe, multiplied by an entire reciprocal gamma/exponential factor. It does not consume the functional equation or primitivity/Gauss hypotheses. This suggests that a future focused port could expose only the continuation branch after a declaration-level dependency audit; the present 41-module closure still includes all analytic implementation.

The ideal-sum proofs regroup actual nonzero ideals by norm, use Mathlib ideal-count asymptotics and its Dedekind-zeta residue. The prime-sum proof proves finite Euler products, exhausts via finite sets of prime factors, and sandwiches log(zeta) between the prime sum and that sum plus a constant from zeta(2). The tail proof bounds all primes of residue degree at least two by [K:Q] times sum over rational primes of p^-2, using actual rational-prime fibres.

The log-branch lemma is not a principal-log substitution: it constructs a local normalized log around a nonzero limit and proves the difference from the supplied continuous log is a constant integral multiple of 2*pi*i, via the intermediate value theorem.

The 846-line cyclotomic divergence proof applies character orthogonality, compares the splitting prime sum in K with all prime sums in L, and proves nonvanishing of each nontrivial pulled-back character at 1 by contradiction: a zero repeats across a whole fibre of character pullback, of cardinal at least the annihilator A, cancelling the principal logarithmic pole, contrary to the positive splitting lower bound. It then bounds nonprincipal logarithms, identifies the norm-character image with the actual cyclotomic Galois image by cardinality, and forces divergence in every allowed residue class. The 120-line extraction proof subtracts bounded degree>=2 and finite excluded-norm contributions to obtain a rational prime norm p outside any given finite S, with the desired action on a primitive root. No circular Chebotarev use is visible in these shorter solutions. The large analytic implementation remains to read.

## Analytic implementation, original lines 1–2450

Read all lines 1–2450. The first 1,038 lines develop finite-dimensional Poisson summation explicitly: periodicization by integer translates, Ioc cube tiling, Fourier-coefficient identification with Euclidean Fourier integrals, and coordinate transport with the actual lattice covolume factor. Hypotheses include summable local sup norms and summable dual Fourier values; later Gaussian bounds discharge them. The code proves Gaussian translate summability, trace decomposition by real/complex embeddings, and identifies the Euclidean dual ideal lattice with the trace-dual ideal after conjugation and factor-two dilation at complex places. A separate sqrt(2) dilation gives covolume NI*sqrt(abs(discriminant)), checked by an explicit diagonal determinant. Residue calibration uses Mathlib classwise ideal-count asymptotics. Several TcFold sections are empty wrappers retained from source assembly; they add no assertions. From line 2310 onward the ray theta construction begins with explicit weighted ideals and parity, currently read only through the start of prinFI_zero. No new substantive bridge to the Library finite-prime target occurs in this prefix.

## Analytic implementation, original lines 2451–5650

Read all lines 2451–5650. The finite character is proved invariant under congruence modulo a proper modulus using an inverse modulo the modulus, parity, and zero extensions outside the coprime ideals; the bottom case is equality and the top case is handled separately. Gauss datum transport is constructed with actual fractional ideals and integral representatives. Finite Gauss sums are shown independent of the datum by reindexing quotient units and matching the sign/ideal prefactor. Finite-character orthogonality is proved by multiplication by a nontrivial unit value.

The odd-Gaussian Fourier formula is derived by differentiating the Fourier transform and inducting over an orthonormal set of real-place factors. Both polynomial-times-Gaussian integrability and summability are discharged explicitly. Weighted coset Poisson then interchanges finite sums with the summable Fourier series. Ray-ideal cosets are matched to O_K/f using an actual coprime generator; uWeight_add_mem carries the finite character into the lattice coset formula with zero cases addressed.

Placewise positive scaling is treated via explicit diagonal determinants. The positive orthant carries density product(t_w^-1), zero outside the orthant. Pullback by expMapBasis gives constant 2^(-r2)*[K:Q]*regulator. A box with intervals [0,2) in nonradial coordinates tiles under squares of fundamental-unit absolute values. Actual units are enumerated as torsion times integral powers of a fundamental system; unfolding includes torsionOrder, not a free-action assertion. The ordinary class Dirichlet series is absolutely summable for Re(s)>1 by Mathlib classwise ideal asymptotics and regrouping norm fibres. Reading reaches inversion invariance at line5650; the Mellin/continuation assembly is still unread.

## Analytic original lines 5651–7750
- Fundamental-domain fold/refold uses actual free-unit action and unit invariance; high/low halves overlap only on norm-one boundary, proved measure zero via a proper log-coordinate hyperplane.
- Radial integration gives polarVolume = foldConst * 2^unitRank / degree; exponential Gaussian tail dominates every radial power. Dominated differentiation is proved locally uniformly with log and shifted-power bounds.
- A minimum nonzero lattice norm and summable Gaussian majorant yield high-half tail bound C exp(-gamma * torusNorm^(1/degree)).
- Fractional-ideal nonzero points are bijective to class-constrained integral ideals times actual units; torsion multiplicity is explicit. Product embedding norm equals ideal norm times fractional-ideal norm. Gamma-majorant integration reduces the absolute Mellin sum to the convergent class zeta sum for Re(s)>1, discharging integrability.
- Trace dual points identify Fourier characters with the actual trace additive character. CRT valuation selection constructs a coprime generator for each fractional ideal at every nonzero modulus, with separate top-modulus case.
- Seam construction defines the level ideal of the trace additive character and starts proving strict enlargement when the associated datum is not coprime.

## Analytic original lines 7751–9900
- Noncoprime additive-character datum strictly enlarges its level ideal; primitivity supplies a totally positive character-nontrivial multiplier congruent to one at that level. Gauss sum invariant under the multiplier then vanishes. This is used only for primitive-character FE identification.
- General inversion (rayFoldMellinIntegrand_inv_gen) uses coprime-generator/coset decomposition and scaled odd-Gaussian Poisson; it does not assume primitivity. It separates the zero frequency as finite chiFin sum times explicit polar coefficient. Odd parity (nonempty S) makes this coefficient zero.
- Primitive inversion additionally identifies the dual sum with the conjugate-character series using Gauss datum and normalization by sqrt(norm modulus); inverse ray scales and covolume constants are explicit.
- Unfolding rayFoldMellin to integral ideals verifies absolute integral/sum interchange, exact torsion multiplicity, and orbit gamma factors. Gamma factors are GammaR(s), GammaR(s+1), GammaC(s)/2; the tc2 normalization cancels the complex-place powers of two and torsion count.
- Complex-power products/inverses used in gamma assembly are over positive real bases; argument-cut side conditions are discharged. Ordinary class group finite sums reassemble the absolutely convergent ideal series.

## Analytic original lines 9901–12126: completed full reading
- Ray-class coefficient fibers are finite actual ideals of fixed norm; sum regrouping equates the ideal Dirichlet sum with the defined rayClassLSeries for Re(s)>1, including a separate zero coefficient proof.
- Polar cancellation tc2Cancel for nontrivial chi: nonempty parity set kills the odd polynomial at zero; otherwise nontrivial finite character gives quotient-unit orthogonality. If finite character is trivial, the moving lemma extends integral principal triviality to fractional principals and constructs a nontrivial ordinary class-group character; its finite character sum cancels the pole.
- Modulus top is handled separately with full-lattice Poisson and both zero-frequency and omitted-zero corrections; the same parity/class-character argument cancels both possible poles. Modulus bottom gives completedRayL zero for s!=0 by its discriminant-modulus factor; it is a degenerate branch, not an analytic theorem for a nonzero modulus.
- Despite names `Holes`, `hole_*`, and `SKELETON`, every used analytic ingredient here has a full implementation: Gaussian decay gives all-s integrability and dominated differentiability of the high and dual tails; radial powers integrate to polarVolume/z. No hole or assumption is inserted by those names.
- Final continuation functions are finite sums of high/dual entire integrals plus explicit rational polar functions. They agree with the actual completion on Re(s)>1. Cancellation proves entire continuation when chi!=1. Primitive functional equation is proved first in Re(s)>1 from inversion, then extended on connected C\{0,1} by the holomorphic identity theorem. No nonzero Gauss-factor cancellation is assumed.
- All41 original modules/18,672 lines are now fully read. Successful private compile/standard-axiom inspection remains machine evidence, not independent semantic acceptance or target proof.

## Final ledger

The earlier progress clauses above describe intermediate reading extents. The final ledger below supersedes them: no original source remains unread.

```json
{
  "fully_read": [
    "P2M.Util",
    "Definitions.Def_TaylorWiles_Primes",
    "Definitions.Def_FrobeniusDensity_DegOneAsymptotic",
    "Definitions.Def_FrobeniusDensity_BadPrimes",
    "Definitions.Def_FrobeniusDensity_PrimeSums",
    "Definitions.Def_NumberField_PrimeNormSums",
    "Definitions.Def_NarrowRayClassGroup",
    "P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension",
    "P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isGalois",
    "Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois",
    "Definitions.Def_LanglandsTunnell_NormClass",
    "Definitions.Def_NumberField_CompletedRayL",
    "Definitions.Def_NumberField_RayCharacterData",
    "Definitions.Def_NumberField_NormResidueCharacter",
    "Definitions.Def_NumberField_EuclideanIdealLattice",
    "Definitions.Def_FrobeniusDensity_ClassGroupLSeries",
    "P2M.Sol.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries",
    "P2M.Sol.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one",
    "P2M.Sol.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one",
    "P2M.Sol.S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal",
    "P2M.Sol.S_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto",
    "P2M.Sol.S_FrobeniusDensity_idealSum_ne_top",
    "P2M.Sol.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test",
    "P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO",
    "P2M.Sol.S_FrobeniusDensity_tailSum_le",
    "P2M.Sol.S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension",
    "P2M.Sol.S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension",
    "Theorems.Thm_NumberField_exists_continuousOn_exp_eq_rayClassLSeries",
    "Theorems.Thm_M4aTorus_completedRayL_fe",
    "Theorems.Thm_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one",
    "Theorems.Thm_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one",
    "Theorems.Thm_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal",
    "Theorems.Thm_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto",
    "Theorems.Thm_FrobeniusDensity_idealSum_ne_top",
    "Theorems.Thm_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test",
    "Theorems.Thm_FrobeniusDensity_primeSum_toReal_add_log_isBigO",
    "Theorems.Thm_FrobeniusDensity_tailSum_le",
    "Theorems.Thm_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension",
    "Theorems.Thm_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension",
    "Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension",
    "P2M.Sol.S_M4aTorus_completedRayL_fe"
  ],
  "partial_ranges": {},
  "note": "All 41 original closure modules have been read in full (18,672 lines). These extents record source reading, not independent semantic acceptance.",
  "adapted_fully_read": [
    "Theorems.Thm_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto",
    "Theorems.Thm_FrobeniusDensity_idealSum_ne_top",
    "Theorems.Thm_FrobeniusDensity_primeSum_toReal_add_log_isBigO",
    "Theorems.Thm_FrobeniusDensity_tailSum_le",
    "Theorems.Thm_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test",
    "Theorems.Thm_M4aTorus_completedRayL_fe",
    "Theorems.Thm_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal",
    "Theorems.Thm_NumberField_exists_continuousOn_exp_eq_rayClassLSeries",
    "Theorems.Thm_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one",
    "Theorems.Thm_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension",
    "Theorems.Thm_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension",
    "Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension",
    "Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois",
    "Theorems.Thm_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one",
    "Definitions.Def_NumberField_RayCharacterData"
  ],
  "adapted_reading_note": "All Theorems wrappers read in cleaned variant; RayCharacterData read in universes variant. Original wrappers differ only by recorded generalization, resets and wrapper substitution; do not conflate with additional original proof-source reading. P2M.Util and Galois solution reread in full. Analytic original partial ledger unchanged; extra adapted snippets read at late existential assembly and patched rayOrbit summability."
}
```

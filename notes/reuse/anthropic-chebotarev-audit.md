# Anthropic Chebotarev: realization and canonical completion audit

This note is dated 25 October 2026.

**Verdict: adapt.** The complete selected source closure was read: **41 modules, 18,672 original lines**, recomputed from imports and original hashes. A privately adapted closure compiles on the project's pinned versions, generalizes the root from Type 0 to independent field universes, and no longer invokes the upstream proof wrapper or global negative instance/simp resets. A complete private adapter compiles with the unchanged conclusion `Langlands.Global.ChebotarevPrimeRealizationStatement.{u,v}`, with no added hypothesis. A separate private lemma proves that a nonidentity absolute Frobenius gives nontrivial canonical completion degree. All inspected successful roots use only `propext`, `Classical.choice` and `Quot.sound`.

This note and its [reproducible evidence](anthropic-chebotarev-evidence/index.md) are an audit; they do not put the external mathematics into the Library. The experimental Lean is retained as evidence text and private drafts. A mathematical port needs definitions and Prop targets in the Library, Lake builds and exact-target checks. No complete nonsplit-prime proof, finite-character rigidity theorem, or Chebotarev conjunction is claimed here.

## Pins, exact scope and original statement

The registered source is `anthropic-flt-complete-lean-source-6e837e75`, content SHA256 `a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`, [Anthropic FLT commit 6e837e75355538c7f80bab5b956861e86c4eacc2](https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2). Its retained directory and notice hashes are in [provenance](anthropic-chebotarev-evidence/provenance.md). The original pins Lean 4.33.1 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. Checks here use only the project environment, Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

The root is `NumberField.exists_prime_isArithFrobAt_of_isGalois` in `Theorems/Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean`. In the original source its full mathematical type is:

```lean
(K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
[Algebra K L] [IsGalois K L] (σ : L ≃ₐ[K] L) (S : Finset ℕ) :
  ∃ p : ℕ, p.Prime ∧ p ∉ S ∧
    ∃ P : Ideal (𝓞 L), P.IsMaximal ∧ (p : 𝓞 L) ∈ P ∧ IsArithFrobAt ℤ σ P
```

Both original carriers are Type 0. The source conclusion avoids finitely many rational primes and states absolute arithmetic Frobenius over ℤ; it contains no explicit unramifiedness. The privately generalized version changes only carrier generality to `(K : Type audit_u) (L : Type audit_v)`, retaining the hypotheses and predicate. All original module and declaration names remain unchanged. The [inventory](anthropic-chebotarev-evidence/inventory.md) records every path, line count, import and original/stage SHA256. Its closure terminates at Lean and Mathlib and is not a minimal declaration dependency graph; it includes 12,126 lines in `P2M/Sol/S_M4aTorus_completedRayL_fe.lean`.

The checked workspace base is Library `b5df466b356db508f072a2481307ed641ffa76a7`. The restoration check used refreshed base `6066ffe8da8e977f40af9c75eda35cdbe1989d74`, with all nine compared files unchanged. Both exact targets, LocalDegree and the four named cyclotomic/norm-character modules were read. Nine relevant files byte-match that immutable Library; [comparison evidence](anthropic-chebotarev-evidence/library.md) records their hashes. A bounded exact-name search found the targets and conditional consumers, with no same-named realization proof; this is not a claim that differently named reusable results cannot exist.

## What the source proof actually does

The [complete reading record](anthropic-chebotarev-evidence/reading.md) covers every original definition, theorem wrapper, solution and utility. The main dependencies are:

- The narrow ray class group and norm character are built from actual ideals, principal congruences and positivity. `NormResidueCharacter` proves a one-sided inclusion into the actual cyclotomic automorphism image using Mathlib's existing Frobenius at a given prime; it does not assume the desired prime-realization theorem or global reciprocity.
- The continuous logarithm of the ray L-series on real `s > 1` follows from the Euler product and a uniformly bounded logarithmic prime-sum error. The ordinary ideal-count and Dedekind-zeta asymptotics give the principal pole. A separate local-log argument controls the continuous branch near 1; it is not an unjustified substitution of the principal complex logarithm.
- The analytic implementation proves Poisson summation with actual lattice covolumes and trace-dual lattices, weighted odd-Gaussian transforms, ideal/unit orbit unfolding, torsion multiplicity, regulator factors and dominated differentiation. Nontrivial-character entire continuation uses general inversion and polar cancellation. Cancellation comes from odd parity, finite-character orthogonality, or descent to a nontrivial ordinary class-group character via a moving lemma. It does **not** require primitive characters. Modulus top is handled separately with both polar corrections; modulus bottom is a degenerate zero branch away from 0.
- The stronger primitive-character functional equation uses Gauss data and a holomorphic identity theorem on ℂ minus 0 and 1. The downstream continuation solution consumes only the entire-continuation clause for nontrivial characters. A future declaration-level extraction might therefore omit the stronger functional-equation branch, but the present audited and compiled closure includes all of it. Names such as `hole_T2`, `hole_top`, `Holes` and `SKELETON` label fully implemented source ingredients, not admitted facts.
- The cyclotomic splitting argument makes inertia trivial away from the conductor, shows the chosen Frobenius fixes a primitive root, and bounds residue cardinality using roots of `X^q-X`. Character orthogonality and the positive splitting lower bound rule out a zero at 1 for every nontrivial pulled-back character: such a zero would repeat over a whole character fibre and cancel the principal logarithmic pole. This yields divergence in every allowed residue class. Bounded residue-degree-at-least-two tails and finite exclusions then give a rational-prime norm outside any given finite set.
- Finally, the arbitrary-Galois argument chooses an auxiliary prime congruent to 1 modulo `orderOf σ * [L:ℚ]!`, enlarges by its cyclotomic field, adjusts an automorphism through the restriction kernel, applies the cyclotomic realization in the cyclic fixed-field extension, and contracts the resulting ideal. The 435-line final solution was read in full. No circular use of the desired global realization theorem was identified in this reading.

These findings support the reuse verdict, but the author's reading is not an independent semantic acceptance of a future port.

## Compatibility and universes

All edits are retained as exact cumulative [compatibility](anthropic-chebotarev-evidence/compatibility.md), [universe](anthropic-chebotarev-evidence/universes.md), and [cleanup](anthropic-chebotarev-evidence/cleaned.md) patches. No theorem or module was renamed.

The compatibility patch replaces a brittle normalized-factor simplification with `Multiset.mem_toFinset.mpr`; uses `change` to expose integral-element/field coercions; changes four `Finset.prod_le_prod` applications to `prod_le_prod₀`; updates the measurable-product interface; and supplies explicit ENNReal summand domains and `lt_top_of_tsum_ne_top` for finite bounds. Raising a heartbeat limit did not solve the elaboration failure; the final patch contains no such increase.

The universe experiment changes bare carrier binders and explicitly separates K, L and auxiliary L′. Two existential index types in the analytic class-group assembly must live in K's universe because their witnesses are `ClassGroup (𝓞 K)`. A fresh universal `Type*` at those existential positions was too general; pinning them to `audit_u` fixes the issue. The final root has independent `audit_u` and `audit_v`. No transport through small models is needed for this tested closure.

The cleanup removes global `attribute [-instance]` / `[-simp]` lines and replaces all fourteen `p2m_exact_reverting` calls by ordinary `apply`/`assumption`, with explicit cyclotomic modulus arguments where needed. Namespace, alias and reactivation utilities remain, as does the unused wrapper implementation inside `P2M.Util`. This is not a claim to have eliminated all P2M machinery. The generalized and cleaned source-root type fingerprints are identical.

## The first endpoint: actual base prime and relative Frobenius

The unchanged Library [ChebotarevStatement.lean](../../Langlands/Global/Arithmetic/ChebotarevStatement.lean) quantifies independent K/L universes, a finite set of `HeightOneSpectrum (𝓞 K)`, and every automorphism. It requires a base prime outside that set, a height-one prime above it with actual `LiesOver`, explicit `Algebra.IsUnramifiedAt (𝓞 K)`, and the arithmetic predicate `(RingOfIntegers.mapAlgHom σ).IsArithFrobAt`.

The following names are **private experiments**, not Library APIs. Their complete source and target text are in [bridge evidence](anthropic-chebotarev-evidence/bridges.md).

| Obligation | Implemented bridge |
|---|---|
| Rational lying-over | `ChebotarevAudit.liesOver_of_prime_mem` applies `Ideal.liesOver_span_iff` to a maximal Q containing prime p, proving Q lies over `Ideal.span {(p : ℤ)}`. |
| Height-one conversion | `realization` uses `Q.bot_lt_of_maximal (RingOfIntegers.not_isField L)` for Q ≠ ⊥. `Ideal.IsIntegral.under_ne_bot` makes its base contraction nonzero. Primality and actual lying-over are supplied by existing instances; no invented prime carrier is substituted. |
| Finite base avoidance | `outside_finite_set` replaces the finite base set S by its image under `w ↦ (w.asIdeal.under ℤ).absNorm`. For a base prime over p this absolute norm is p, so avoidance descends exactly. |
| Unramifiedness | Exclude `(NumberField.discr L).natAbs.primeFactors`, a finite set since the discriminant is nonzero. `unramified_of_not_dvd_discr` uses `NumberField.not_dvd_discr_iff_forall_mem` to obtain absolute unramifiedness at Q, then `Algebra.IsUnramifiedAt.of_restrictScalars ℤ Q` gives the required relative property. No unproved ramification-index tower assertion is inserted. |
| Base residue cardinality | `base_card_eq_prime` applies absolute Frobenius to integral base elements. Since σ fixes K, every residue x satisfies x^p = x. The audited polynomial-root bound gives cardinality ≤ p; the injective map from the integer residue field gives ≥ p, hence equality. |
| Exact relative action | `relative_frobenius` rewrites the integer and base quotient cardinalities to p. The integral action agrees definitionally with `RingOfIntegers.mapAlgHom σ`; the same congruence is therefore the Library's exact arithmetic predicate, with no inverse/geometric convention change. |
| Assembly | `ChebotarevAudit.realization` takes the union of the two excluded rational-prime sets and applies the adapted external root. Its compiled type is exactly `Langlands.Global.ChebotarevPrimeRealizationStatement.{u,v}`. No Chebotarev premise is added. |

The experiment demonstrates feasibility of every adapter above. It leaves no demonstrated logical gap at this particular first endpoint, but it does not make the external analytic infrastructure part of the Library.

## Secondary endpoint: nontrivial canonical completion degree

The unchanged [CyclicNonsplitPrimeStatement](../../Langlands/Global/Arithmetic/CyclicNonsplitPrimeStatement.lean) requires a prime outside any finite base set and an actual lies-over prime whose canonical completed finrank differs from 1. It has no explicit unramifiedness clause.

`ChebotarevAudit.localDegree_ne_one` is checked for arbitrary finite Galois number-field extensions, independent universes, actual base/extension height-one primes with `LiesOver`, and a nonidentity σ satisfying absolute `IsArithFrobAt ℤ σ`. It needs neither cyclicity nor unramifiedness. `IsGaloisGroup.of_isFractionRing` supplies the integral Galois action. The Frobenius belongs to the ideal stabilizer; Mathlib's `Ideal.card_stabilizer_eq` gives its cardinality as e·f, and the Library's `Langlands.Global.AdelicFunctoriality.localDegree_eq` identifies e·f with the canonical completion degree. If that degree were 1, the stabilizer would be a subsingleton, contradicting σ ≠ 1.

This avoids needing uniqueness of unramified Frobenius for the secondary bridge. The private experiment stops at that lemma: selection of a nonidentity automorphism from `1 < Module.finrank F E`, application of the realization theorem outside the finite set, and exact assembly of `CyclicNonsplitPrimeStatement` are outside the experiment; the final target must not acquire a Chebotarev assumption. The Library now proves `CyclicNonsplitPrimeStatement`, as `cyclicNonsplitPrimeStatement` (`Langlands/Global/Arithmetic/CyclicNonsplitPrimeProof.lean`).

## Machine evidence, attribution and limitations

[Seventeen exact terminal records](anthropic-chebotarev-evidence/checks.md) preserve successes, failed elaboration attempts, source hashes, full printed types and axiom lists. The unmodified closure fails on the Library's pin. The successful Type 0 compatibility check is [check 04](anthropic-chebotarev-evidence/check-04.md); the universe check is [check 06](anthropic-chebotarev-evidence/check-06.md); cleanup is [check 08](anthropic-chebotarev-evidence/check-08.md). Final bridge checks are [check 13](anthropic-chebotarev-evidence/check-13.md), [check 14](anthropic-chebotarev-evidence/check-14.md), and [check 15](anthropic-chebotarev-evidence/check-15.md). Consolidated check [check 16](anthropic-chebotarev-evidence/check-16.md) prints the full root and all seven adapter types/axioms, with zero errors/warnings and unchanged source-root fingerprint `3947a480b5b576718094cd7dba79d66c903b9e17396b4d9146cfba4c005318fc`.

All successful inspected roots use the three standard axioms. Failed-check `sorryAx` output is Lean error recovery, not authored or accepted proof holes. One timed-out check was cancelled before it started; it supplies no mathematical result. Exact terminal reports survive, but not every failed intermediate source snapshot. The final successful trees are reconstructible and their hashes were verified by reconstructing the trees from the recorded inputs and patches.

`proof_accepted` is false throughout. Development inspection did not ask for a formal statement-target check, so `target_matches: false` and `statement_returns_prop: false` in those records must not be read as either acceptance or a theorem-type mismatch. The readable complete types and encoded-expression fingerprints/lengths are retained; transient raw expression files were deleted with service scratch space and are unavailable. The theorem annotated with the unchanged Library proposition compiled; the Library's own proof of that proposition is named in the last section.

The [provenance record](anthropic-chebotarev-evidence/provenance.md) gives the read LICENSE/NOTICE, attribution-table limits and preserved hashes. None of these 41 paths has a specific ATTRIBUTION.md row or explicit author header; absence from the table does not establish original authorship. All repository notices are preserved and modified files are marked. A registered 25 October snapshot of the unchanged upstream head, all eleven issue/PR bodies and their nonempty comment threads identified no Chebotarev defect. Build memory-map reports and PR 11's stale comparator-work-directory problem are recorded separately; this is a bounded errata review, not an absence guarantee.

## Smallest proposed port modules

This is a dependency order for the mathematical work, not a bulk-port instruction. Each new definition module needs a check of its correspondence with the source; each new proof module needs its Prop target stated in the Library first.

1. **Foundations and interfaces.** State the necessary narrow-ray, norm-character, partial L-series, completed L-series and Euclidean ideal-lattice definitions, grouped by their actual dependencies. State only the required proposition interfaces; first perform a declaration-level partition to determine whether the primitive functional-equation branch can be excluded. The import inventory alone does not justify that omission.
2. **Analytic support, split into separate modules.** Prove lattice Poisson/covolume transport; weighted Gaussian and coset transforms; unit-domain tiling and ideal/unit unfolding; integrability/entire Mellin-tail estimates; and general inversion plus polar cancellation. Each has a distinct mathematical interface in the 12,126-line solution and deserves its own target. Then assemble the nontrivial-character entire-continuation statement used by `NumberField.exists_differentiable_eq_rayClassLSeries_of_ne_one`. Retaining the stronger functional equation requires separate primitive Gauss-data and identity-theorem modules.
3. **Prime-sum and cyclotomic route.** Group the small ideal-sum/pole and bounded-log lemmas, then prove the degree-at-least-two tail bound. Separately treat the cyclotomic splitting/norm-character comparison and the 846-line character-fibre nonvanishing/divergence argument. Assemble `NumberField.exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension` and `NumberField.exists_prime_isArithFrobAt_of_isCyclotomicExtension` from their targets.
4. **General Galois realization.** Treat the auxiliary cyclotomic extension, restriction-kernel adjustment and ideal contraction in the final 435-line solution. State a Prop target with the generalized root's exact hypotheses and conclusion, then prove it. Preserve independent universes and all attribution. Namespace/alias cleanup beyond the tested patch is an additional refactor requiring validation.
5. **First endpoint adapter.** Group the small lying-over, avoidance, discriminant and residue-cardinality adapters into one module, then prove the existing `Langlands.Global.ChebotarevPrimeRealizationStatement`. The private implementation provides a concrete feasibility reference, not a substitute for Lake builds in the Library.
6. **Existing nonsplit proof boundary.** Reuse the checked decomposition-group/local-degree argument for `CyclicNonsplitPrimeStatement`. Keep its final local-degree assembly and the independent first-inequality/almost-split route, with its inequality and descent results, intact.

Finite-character rigidity and infinite-image global Weil rigidity remain outside this audit. Equality of characters needs a separate arbitrary-carrier finite-group faithfulness theorem before actual representation equivalence follows; the specialized full-End-span Brauer–Nesbitt result does not supply it. The realization adapter proves no conjunction involving that missing result.

## In the Library

The Library now proves both endpoints: `Langlands.Global.ChebotarevPrimeRealizationStatement`, as
`chebotarevPrimeRealizationStatement` (`Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`),
and `CyclicNonsplitPrimeStatement`, as `cyclicNonsplitPrimeStatement`
(`Langlands/Global/Arithmetic/CyclicNonsplitPrimeProof.lean`).

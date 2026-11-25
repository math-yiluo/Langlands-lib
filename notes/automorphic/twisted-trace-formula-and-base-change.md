# The twisted trace formula and cyclic base change: geometric side, matching near the identity, cyclic algebras

This note describes the parts of `Langlands/TraceFormula/` and `Langlands/BaseChange/` that carry the
twisted trace formula of cyclic base change for `GL_n`: the abstract simple twisted trace formula
with its geometric side, the orbital terms and their invariance, the `GL_n` statements, and the
local matching of test functions near the identity, for cyclic field extensions and for cyclic
algebras that are not fields. Both directories hold much else (the discrete spectral comparison of
Arthur–Clozel, the fundamental lemma and its reductions, globalization), which is only named here.

## The mathematics

Let `G` be a unimodular locally compact group, `Γ` a discrete subgroup, `θ` an automorphism of `G`
preserving `Γ`, `R` the right regular representation on `L²(Γ\G)` and `I_θ φ = φ ∘ θ⁻¹`. For a test
function `f`, `R(f) ∘ I_θ` is the integral operator with kernel `K(x, y) = Σ_{γ∈Γ} f(x⁻¹ γ θ(y))`;
when it is trace class, its trace is `∫_{Γ\G} K(x, x) dx` (Brislawn, *Traceable integral kernels on
countably generated measure spaces*, 1991, Corollary 3.2), and unfolding the diagonal over the
`θ`-twisted classes of `Γ` gives the geometric side Σ vol((Γ ∩ C_γ)\C_γ) · TO_γ(f), a sum of volumes
times twisted orbital integrals over the classes meeting the support (Getz–Hahn, *An Introduction to
Automorphic Representations*, §18.5, Corollary 18.5.1). For G = Res_{L/K} GL_n with `θ` induced by a
generator `σ` of a cyclic extension L/K, the comparison of this twisted formula with the simple
trace formula of `GL_n` over `K` is the method of cyclic base change (Arthur–Clozel, *Simple Algebras,
Base Change, and the Advanced Theory of the Trace Formula*, 1989). Its local input is the matching
of test functions: `φ` on `GL_n(E)` and `f` on `GL_n(F)` are concordant if their twisted and
ordinary orbital integrals agree at norm-associated regular semisimple classes and `f` vanishes off
norms (Arthur–Clozel I.3.1; Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n`
en caractéristique non nulle*, 2011, I.2.5).

## Layout

| Files | Content |
| --- | --- |
| `Langlands/TraceFormula/TwistedOrbital.lean` | twisted conjugation, twisted centralizers, classes, orbit functions, twisted orbital integrals, the twisted kernel and its diagonal, the operator `I_θ` |
| `Langlands/TraceFormula/TwistedKernelOperator.lean` | `R(f) ∘ I_θ` as an integral operator on `Γ\G` with a continuous square-integrable kernel |
| `Langlands/TraceFormula/AbstractTwistedKernelDiagonalTraceStatement.lean`, `Langlands/TraceFormula/AbstractTwistedKernelDiagonalTraceProof.lean` | the trace as the integral of the diagonal |
| `Langlands/TraceFormula/TwistedGeometricUnfolding.lean`, `TwistedGeometricSide.lean` | the unfolding and the geometric side |
| `Langlands/TraceFormula/AbstractSimpleTwistedStatement.lean`, `AbstractSimpleTwistedProof.lean` | the abstract simple twisted trace formula |
| `Langlands/TraceFormula/TwistedOrbitalTermInvariance.lean`, `TwistedGeometricConjugation.lean`, `TwistedOrbitalConjugation.lean`, `ExtendTwistedGeometricMeasures.lean`, `TwistedOrbitClosedEmbedding.lean`, `TwistedOrbitHomeomorph.lean`, `TwistedOrbitalProduct.lean` | invariance of the orbital terms, closed twisted orbits, measures on centralizers, products |
| `Langlands/TraceFormula/GeneralLinear*Statement.lean` and their reductions, `SingleOrbit*.lean`, `SimpleTraceGeometricExpansionSum.lean` | the statements for `GL_n` and Res_{L/K} GL_n and the theorems derived from them |
| `Langlands/BaseChange/OrbitalIntegral.lean` | ordinary and `σ`-orbital integrals, associated measures, concordance |
| `Langlands/BaseChange/NearIdentityMatchingStatement.lean`, `NearIdentityMatching.lean` | matching near the identity for a cyclic field extension |
| `Langlands/BaseChange/CyclicAlgebraNearIdentityMatchingStatement.lean`, `CyclicAlgebraNearIdentityMatching.lean`, `CyclicAlgebraFullMatchingStatement.lean`, `CyclicAlgebraFullMatching.lean`, `CyclicAlgebraBaseChange.lean` | the same for cyclic algebras, and full matching |
| `Langlands/BaseChange/FinitePlaceFullMatchingStatement.lean` | full matching at a finite place |

## The abstract simple twisted trace formula

In namespace `Langlands.TraceFormula`, for `G` a Hausdorff, locally compact, second-countable group
with a Haar measure `μG`, `Γ` a discrete subgroup, a measure `ν` on `Γ\G` compatible with `μG` and
counting measure (`Langlands.QuotientIntegration.IsCompatible`), `θ : G ≃ₜ* G` preserving `Γ` whose
induced map of `Γ\G` preserves `ν`, and `π` the right regular action on `L²(Γ\G, ν)`:

- `twistedConj θ x δ = x⁻¹ δ θ(x)`, `twistedCentralizer θ δ`, `IsTwistedConjugate`,
  `twistedOrbitalIntegral θ δ ν f = ∫ f(x⁻¹ δ θ(x)) dν(x)` over `twistedCentralizer θ δ \ G` (no
  normalization of `ν` built in), `twistedKernel`, `twistedKernelDiagonal`, and
  `twistOperator Γ θ hθ ν hν`, the operator `φ ↦ φ ∘ θ̄⁻¹` (`TwistedOrbital.lean`).
- `twistedKernelOperator_ae_eq` (`TwistedKernelOperator.lean`): `R(f) ∘ I_θ` is the integral operator
  with the continuous kernel `twistedQuotientKernel`.
- `abstractTwistedKernelDiagonalTrace` proves `AbstractTwistedKernelDiagonalTraceStatement`, and
  `integrable_twistedKernelDiagonal_and_operatorTrace_eq` its strong form: if `R(f) ∘ I_θ` is trace
  class (`f : C_c(G, ℂ)`), the diagonal of the kernel is `ν`-integrable and its integral is the trace.
  Neither the right invariance of `μG` nor `MeasurePreserving θ μG μG` is used, and `Γ\G` need not be
  compact. The analytic input is Brislawn's theorem,
  `Langlands.Analysis.OperatorIdeals.traceClassContinuousKernelDiagonal`.
- `abstractSimpleTwistedTraceFormula` proves `AbstractSimpleTwistedTraceFormulaStatement`
  (`AbstractSimpleTwistedProof.lean`): under a support condition (finitely many twisted classes
  `r i` meet the support, with compatible measures on the centralizers and their quotients), the
  trace of `R(f) ∘ I_θ` is Σ_i vol((Γ ∩ C_{r i})\C_{r i}) · TO_{r i}(f). It is
  `abstractSimpleTwistedTraceFormula_of_kernelDiagonalTrace` (`TwistedGeometricSide.lean`, the geometric
  side, with `hasSum_twistedOrbitalIntegral_of_isCompatible` and
  `integral_twistedKernelDiagonal_expansion`) applied to the kernel-diagonal theorem. When `Γ\G` is
  compact the support condition holds for every `f`
  (`exists_isCompact_twistedSupport_of_compactSpace`).
- `twistedOrbitalTerm` and `twistedOrbitalTerm_eq_of_isCompatible`,
  `twistedOrbitalTerm_eq_of_isTwistedConjugate` (`TwistedOrbitalTermInvariance.lean`): the term
  `vol((Γ ∩ C)\C) · O_γ(φ)` does not depend on the compatible measures nor on the representative of
  the class, for any continuous endomorphism `θ`; `orbitalTerm_eq_of_isCompatible`,
  `orbitalTerm_eq_of_isConjugate` are the untwisted case.

## The statements for `GL_n`

For number fields `K, L : Type u`, `σ : L ≃ₐ[K] L` with `Langlands.BaseChange.IsCyclicAlgebra σ l`,
on the Library's group-scheme automorphic `L²` spaces:

- `GeneralLinearSimpleTraceFormulaStatement` (`GeneralLinearSimpleTraceFormulaStatement.lean`): the
  simple trace formula of Deligne and Kazhdan for `GL_n` over `K`, for `f = f₁ ⋆ f₂` with R_cusp(f₁),
  R_cusp(f₂) Hilbert–Schmidt, `f₂` with vanishing integrals along the unipotent radicals of proper
  parabolics and the support regular elliptic at a finite place. Stated, not proved.
- `GeneralLinearSimpleTwistedTraceFormulaStatement`: its twisted counterpart for Res_{L/K} GL_n.
  Stated, not proved.
- `GeneralLinearBaseChangeTraceComparisonStatement`: if the orbital integrals of `φ` on Res_{L/K} GL_n
  match those of `f` on `GL_n` at norms up to a constant `c` and those of `f` vanish off norms, then
  `tr(R(φ) ∘ I_θ) = c · tr R(f)`. Stated, not proved.
- Proved from named hypotheses: `generalLinearTensorSimpleTraceFormula_of_simpleTraceFormula` and
  `generalLinearTensorSimpleTracePieces_of_simpleTraceFormula`
  (`GeneralLinearTensorSimpleTraceFormulaReduction.lean`) derive the simple trace formula for finite
  sums of tensor test functions (`GeneralLinearTensorSimpleTraceFormulaStatement`,
  `GeneralLinearTensorSimpleTracePiecesStatement`) from `GeneralLinearSimpleTraceFormulaStatement` and
  `GeneralLinearRadicalIntegralVanishingStatement`, through the Dixmier–Malliavin factorization of
  tensor test functions (see [the Dixmier–Malliavin theorem](../analysis/dixmier-malliavin.md)).
  `GeneralLinearSingleOrbitTraceStatement` and `GeneralLinearSingleOrbitTwistedTraceStatement`
  (`SingleOrbitSimpleTrace.lean`, `SingleOrbitSimpleTwistedTrace.lean`) are proved
  (`generalLinearSingleOrbitTrace`, `generalLinearSingleOrbitTwistedTrace`); their contents assume
  the simple trace formulas and reduce them, on a test function isolating one rational class, to one
  orbital term.

## Matching near the identity

In namespace `Langlands.BaseChange`, `AreConcordant σ l μF μE φ f` (`OrbitalIntegral.lean`) says that
`f` vanishes off norms (`VanishesOffNorms`) and that at every norm-associated pair `(δ, γ)` with `γ`
regular semisimple the `σ`-orbital integral of `φ` at `δ` and the orbital integral of `f` at `γ`
agree for the associated measures (`ConcordAt`), following Henniart–Lemaire I.2.5.

- `nearIdentityMatching` proves `NearIdentityMatchingStatement`
  (`NearIdentityMatchingStatement.lean`, `NearIdentityMatching.lean`): for a nonarchimedean local field
  `F : Type u` of characteristic zero, a field `E : Type v` with the module topology over `F`,
  `σ : E ≃ₐ[F] E` with `IsCyclicAlgebra σ l`, and any Haar measures `μF`, `μE` on `GL_n(F)`, `GL_n(E)`:
  there is a neighbourhood `U` of `1` in `GL_n(E)` such that every Schwartz–Bruhat `φ` supported in
  `U` has a concordant `f`, and a neighbourhood `V` of `1` in `GL_n(F)` such that every `f` supported
  in `V` has a concordant `φ`. `exists_concordant_ordinary_of_support_normCongruence` and
  `exists_concordant_twisted_of_support_normCongruence` give the two directions with an explicit
  radius and an explicit transferred function.
- `cyclicAlgebraNearIdentityMatching` proves `CyclicAlgebraNearIdentityMatchingStatement`: the same
  with `E` a commutative ring (a finite reduced cyclic `F`-algebra, a product of copies of a cyclic
  field extension), by reduction to the field case through the coordinates `E ≃ₐ[F] (Fin (m + 1) → L)`.
- `cyclicAlgebraBaseChange` proves `CyclicAlgebraBaseChangeStatement` (`CyclicAlgebraBaseChange.lean`):
  in characteristic zero, the scalar extension of a cyclic algebra is again cyclic of the same degree.

## What is stated and not proved

- `FinitePlaceFullMatchingStatement` (`FinitePlaceFullMatchingStatement.lean`): matching for all test
  functions at a finite place (Arthur–Clozel I.3.1), with `f` vanishing off norms in the direction from
  `GL_n(F)`; and `CyclicAlgebraFullMatchingStatement`, its form for cyclic algebras, which
  `cyclicAlgebraFullMatching_of_finitePlaceFullMatching` derives from it.
- `GeneralLinearSimpleTraceFormulaStatement`, `GeneralLinearSimpleTwistedTraceFormulaStatement`,
  `GeneralLinearBaseChangeTraceComparisonStatement`, `GeneralLinearRadicalIntegralVanishingStatement`
  (above), and the fundamental lemma `FundamentalLemmaStatement`
  (`Langlands/BaseChange/FundamentalLemmaStatement.lean`), whose reductions
  (`fundamentalLemmaBlockReduction`, `fundamentalLemmaEllipticReduction`,
  `fundamentalLemmaGlobalizationReduction`, …) and unit case (`unitFundamentalLemma`) are proved.
- Many statements of the discrete spectral comparison (for example
  `CyclicDiscreteTraceComparisonStatement`, Arthur–Clozel (17.8), and
  `CyclicNormOneDiscreteTraceComparisonStatement`, (17.7), in `Langlands/TraceFormula/CyclicNormOneTraceComparisonStatement.lean`) have no proof.

## Conventions

- Twisted conjugation is `x⁻¹ δ θ(x)`, a right action; `I_θ` is composition with `θ̄⁻¹`; the kernel
  of `R(f) ∘ I_θ` is `Σ_γ f(x⁻¹ γ θ(y))`, in agreement with Getz–Hahn's `K_f(g, θ(h))`.
- Orbital integrals are over the left coset spaces `C \ G` with supplied measures; the statements
  quantify over all compatible measures, and the orbital terms are independent of them
  (`twistedOrbitalTerm_eq_of_isCompatible`).
- Concordance is formed with Haar measures `μF`, `μE` of the user's choice and the associated
  measures on centralizers of Henniart–Lemaire I.2.5; test functions are the Library's
  `SchwartzBruhat` functions on `GeneralLinear n F` and `GeneralLinear n E`.

## Why it is built this way

- The trace formula is proved for an abstract group with a discrete subgroup and an automorphism,
  in two halves (the analytic identity for the trace, the geometric unfolding), each with only the
  hypotheses it uses; the adelic and `GL_n` statements are specializations stated separately.
- The fields carry `IsNonarchimedeanLocalField` and the matching statements quantify over all Haar
  measures, so that they can be applied at every finite place of a number field.

## Origin of the text

`Langlands/TraceFormula/TwistedGeometricUnfolding.lean` (in part) and
`Langlands/BaseChange/CongruenceTwistedDescent.lean`, `Langlands/BaseChange/NearIdentityConcordance.lean`
and `Langlands/BaseChange/NearIdentityMatching.lean` are ported from the repository
leanprover-community/riemann-hypothesis (commit `f1f6d65`); their pages name the source files, and
`licenses/RiemannHypothesis/SOURCE.md` describes the source and the terms of its use. The other
files of this note are the Library's own; their pages give the literature.

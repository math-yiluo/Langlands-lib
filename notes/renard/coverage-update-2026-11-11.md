# Renard 2026: coverage update, 11 November 2026

This note continues the
[coverage update of 10 November 2026](coverage-update-2026-11-10.md) and the
[whole-book ledger](coverage.md). It records the statement modules that entered
the Library between that update and 11 November 2026, and audit findings,
including three source issues. It declares no section, chapter or book complete. A
published statement is not a proof; every row keeps the proof status
explicit.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF page numbers equal printed page numbers plus six. Library facts refer to
commit `63d9b857523edf47443b7bf30844159e526d00b0` unless stated otherwise; the
last column of the table gives the proofs the Library has now.

## New statement publications

Each module below is a statement module of the Library. For none of them was
there a theorem or proof term of the statement's type in the Library at the
commit above: the statement names occurred only in their own statement files
(and, as module names, in import lines of two other statement files).

The first five rows are the modules that the previous update listed as stated
after its commit.

| Source assertion | Library module and entry declaration | Proof in the Library |
| --- | --- | --- |
| V.5.5, Proposition and Corollary, printed pp.127–128 / PDF pp.133–134: projection on a closed convex cone | `Langlands.Analysis.RenardConeProjectionStatements`, `Langlands.Renard.ConeProjectionStatements` | proved: `coneProjectionStatements` (`Langlands/Analysis/RenardConeProjectionProof.lean`) |
| VI.7.2, second Lemma, printed pp.182–183 / PDF pp.188–189: `R ⊣ I` for `Cusp(G)`, exactness, faithfulness, finite type, injectivity of `V → IR(V)` | `Langlands.Representation.CuspidalSupport.BernsteinCuspAdjunctionStatement`, `Langlands.CuspidalSupport.BernsteinCuspAdjunctionStatement` | not proved; derived from further hypotheses by `bernsteinCuspAdjunction_of_wholeDecomposition` (`Langlands/Representation/CuspidalSupport/BernsteinCuspAdjunctionAssembly.lean`) |
| VI.7.3, Proposition, printed p.185 / PDF p.191: `i_P^G` and `r_P^G` on Bernstein blocks | `Langlands.Representation.CuspidalSupport.BernsteinInductionRestrictionStatement`, `Langlands.CuspidalSupport.BernsteinInductionRestrictionStatement` | not proved; `BernsteinInductionRestrictionAssemblyStatement` (`Langlands/Representation/CuspidalSupport/BernsteinInductionRestrictionAssembly.lean`) states that it follows from the decomposition and block-characterization statements, and the Library proves that implication (`bernsteinInductionRestriction_of_decomposition_and_characterization`) |
| VI.5.4, Theorem, printed pp.173–175 / PDF pp.179–181: the length and Hom-dimension bounds | `Langlands.Representation.CuspidalSupport.BernsteinSupercuspidalInductionBoundsStatement`, `Langlands.CuspidalSupport.BernsteinSupercuspidalInductionBoundsStatement` | not proved |
| V.2.7, Corollary and Notations, printed p.109 / PDF p.115: unramified orbits in `Irr(G)` are complex algebraic tori | `Langlands.Representation.CuspidalSupport.RationalInertiaOrbitTorusStatement`, `Langlands.CuspidalSupport.RationalInertiaOrbitTorusStatement` | proved: `rationalInertiaOrbitTorus` (`Langlands/Representation/CuspidalSupport/RationalInertiaOrbitTorusProof.lean`) |
| I.2.3, opening paragraphs and closing Remark, printed pp.16–18 / PDF pp.22–24: the unital right adjoint and the comparison of forgetful functors | `Langlands.Algebra.RenardForgetfulFunctorStatements`, `Langlands.Algebra.RenardForgetfulFunctor.RenardForgetfulFunctorStatements` | proved: `renardForgetfulFunctorStatements` (`Langlands/Algebra/RenardForgetfulFunctorProof.lean`) |
| IV.2.1, (IV.2.1.1)–(IV.2.1.2), printed p.97 / PDF p.103: normalized compact induction and its duality for closed cocompact `H` | `Langlands.Representation.Unitary.CompactQuotientNormalizedInductionDualityStatement`, `Langlands.Renard.CompactRepresentation.CompactQuotientNormalizedInductionDualityStatement` | proved: `compactQuotientNormalizedInductionDuality` (`Langlands/Representation/Unitary/CompactQuotientNormalizedInductionDualityProof.lean`) |
| IV.2.3, (IV.2.3.1)–(IV.2.3.2) and the following paragraph, printed pp.98–99 / PDF pp.104–105: unitary induction for general cocompact `H` | `Langlands.Representation.Unitary.CompactQuotientUnitaryInductionStatement`, `Langlands.Renard.CompactRepresentation.CompactQuotientUnitaryInductionStatement` | proved: `compactQuotientUnitaryInduction` (`Langlands/Representation/Unitary/CompactQuotientUnitaryInductionProof.lean`) |
| IV.3.1, Remark, printed p.99 / PDF p.105: smooth vectors of the Hilbert completion | `Langlands.Representation.MatrixCoefficient.CentralL2SmoothVectorsStatement`, `Langlands.Renard.CompactRepresentation.CentralL2SmoothVectorsStatement` | proved: `centralL2SmoothVectors` (`Langlands/Representation/MatrixCoefficient/CentralL2SmoothVectorsProof.lean`) |
| IV.3.3, Remark after the Corollary, printed p.102 / PDF p.108: square integrability modulo a cocompact central subgroup | `Langlands.Representation.Compact.CocompactCentralSquareIntegrableStatements`, `Langlands.Renard.CompactRepresentation.CocompactCentralSquareIntegrableStatements` | proved: `cocompactCentralSquareIntegrable` (`Langlands/Representation/Compact/CocompactCentralSquareIntegrableProof.lean`) |
| V.3.17, Lemma, printed p.114 / PDF p.120, extended from the reduced roots `Σ_∅` to all relative roots `Σ′_∅`: the roots positive on the coroot chamber of `P = MN` are the roots of `A_∅` in `N` | `Langlands.Representation.LanglandsClassification.CorootChamberUnipotentRootsStatement`, `Langlands.GroupScheme.CorootChamberUnipotentRootsStatement` | proved: `corootChamberUnipotentRoots` (`Langlands/Representation/LanglandsClassification/CorootChamberUnipotentRoots.lean`) |
| V.5.3, printed pp.123–125 / PDF pp.129–131, **partial** (see the V.5 findings): `H₀ = H(K₀, K)`, the product Lemmas, the Corollary, the finiteness Lemma in module form, the Theorem `H(G, K) = Σ H₀ A D_j H₀` and the Remark | `Langlands.Representation.Hecke.IwahoriHeckeDecompositionStatement`, `Langlands.Hecke.IwahoriHeckeDecompositionStatement` | proved: `iwahoriHeckeDecomposition` (`Langlands/Representation/Hecke/IwahoriHeckeDecompositionProof.lean`) |
| VI.4.2, the paragraphs after the Proposition, printed pp.152–153 / PDF pp.158–159: the right `H(G, ρ)`-module structures and the `A`-linearity of the adjunction (VI.4.2.5)–(VI.4.2.6) | `Langlands.Representation.CuspidalSupport.RationalNormKernelHeckeModuleStatement`, `Langlands.CuspidalSupport.RationalNormKernelHeckeModuleStatement` | proved: `rationalNormKernelHeckeModule` (`Langlands/Representation/CuspidalSupport/RationalNormKernelHeckeModuleProof.lean`) |
| VI.4.3, (VI.4.3.1)–(VI.4.3.3), printed pp.154–155 / PDF pp.160–161: structure of `H(G, ρ)` (the spaces `F_x(ρ)`, support in `N`, units) | `Langlands.Representation.CuspidalSupport.RationalNormKernelHeckeStructureStatement`, `Langlands.CuspidalSupport.RationalNormKernelHeckeStructureStatement` | proved: `rationalNormKernelHecke_structure` (`Langlands/Representation/CuspidalSupport/RationalNormKernelHeckeStructureProof.lean`) |
| VI.4.4, preliminaries and Lemma, printed pp.155–158 / PDF pp.161–164: the groups `H`, `H̃`, `N`, `ρ_T` and (VI.4.4.3) | `Langlands.Representation.CuspidalSupport.RationalSummandStabilizerLemmaStatement`, `Langlands.CuspidalSupport.RationalSummandStabilizerLemmaStatement` | proved: `rationalSummandStabilizerLemma` (`Langlands/Representation/CuspidalSupport/RationalSummandStabilizerLemmaProof.lean`) |
| VI.4.4, the group `T` and the Remark after it, printed pp.156–157 / PDF pp.162–163: finite index, `X(G)(π)` as annihilator of `T`, `ℂ[T/⁰G] ≅ ℂ[Λ(G)]^{X(G)(π)}` | `Langlands.Representation.CuspidalSupport.RationalTwistStabilizerKernelStatement`, `Langlands.CuspidalSupport.RationalTwistStabilizerKernelStatement` | proved: `rationalTwistStabilizerKernel` (`Langlands/Representation/CuspidalSupport/RationalTwistStabilizerKernelProof.lean`) |
| VI.4.4, Proposition, last sentence, printed p.159 / PDF p.165: the centre of `A` is the algebra of polynomial functions on `Irr(G)[π]` | `Langlands.Representation.CuspidalSupport.RationalSummandCenterVarietyStatement`, `Langlands.CuspidalSupport.RationalSummandCenterVarietyStatement` | proved: `rationalSummandCenterVariety` (`Langlands/Representation/CuspidalSupport/RationalSummandCenterVarietyProof.lean`) |
| VI.4.4, the sentence closing the proof of the Corollary, printed p.159 / PDF p.165: `M(G)[π]` is equivalent to right modules over a left and right noetherian algebra | `Langlands.Representation.CuspidalSupport.RationalInertiaBlockNoetherianModulesStatement`, `Langlands.CuspidalSupport.RationalInertiaBlockNoetherianModulesStatement` | not proved |
| VI.7.1, Proposition and Theorem, printed pp.180–181 / PDF pp.186–187: `Sc` is surjective with finite fibres; the components of `Ω(G)` are quotients `X(M)/W` with finitely generated domain coordinate algebras, indexed by `B(G)` | `Langlands.Representation.CuspidalSupport.BernsteinCuspidalDataVarietyStatements`, `Langlands.CuspidalSupport.BernsteinCuspidalDataVarietyStatements` | not proved |
| VI.9.6, equivalence of (VI.9.6.1) and (VI.9.6.2), printed pp.201–202 / PDF pp.207–208 | `Langlands.Representation.Exponents.LeviSecondAdjointnessContragredientEquivalenceStatement`, `Langlands.Aubert.General.RepresentedParabolic.LeviSecondAdjointnessContragredientEquivalenceStatement` | proved: `leviSecondAdjointnessContragredientEquivalence` (`Langlands/Representation/Exponents/LeviSecondAdjointnessContragredientEquivalenceProof.lean`) |
| VI.10.4, Theorem and Remarks 1–2, printed p.212 / PDF p.218: `ℨ_Ω` is the algebra of polynomial functions on `Ω`, `ℨ(G)` that of functions on `Ω(G)` polynomial on components, `e_Ω = 1_Ω` | `Langlands.Representation.CuspidalSupport.BernsteinCenterFunctionsStatements`, `Langlands.CuspidalSupport.BernsteinCenterFunctionsStatements` | not proved |
| VII.3.4, explicit form and Proposition, and VII.3.5 (i), printed pp.235–240 / PDF pp.241–246: integral normalization of `J_{Q\|P}(σ)` and the composition law | `Langlands.Representation.Intertwining.PQIntegralIntertwiningStatements`, `Langlands.Aubert.General.RepresentedParabolic.PQIntegralIntertwiningOperatorStatement` and `PQIntertwiningCompositionStatement` | `PQIntegralIntertwiningOperatorStatement` proved: `pqIntegralIntertwiningOperator` (`Langlands/Representation/Intertwining/PQIntegralIntertwiningOperatorProof.lean`); `PQIntertwiningCompositionStatement` proved: `pqIntertwiningComposition` (`Langlands/Representation/Intertwining/PQIntertwiningCompositionProof.lean`), which applies `pqIntertwiningComposition_of_reductions` (`Langlands/Representation/Intertwining/PQIntertwiningCompositionReduction.lean`) to the proofs of its four premises |
| VII.3.5 (ii) and (iii), printed pp.237–240 / PDF pp.243–246: intertwining operators and induction in stages | `Langlands.Representation.Intertwining.PQIntertwiningLeviStatements`, `Langlands.Aubert.General.RepresentedParabolic.PQIntertwiningInnerLeviStatement` and `PQIntertwiningOuterLeviStatement` | `PQIntertwiningInnerLeviStatement` proved: `pqIntertwiningInnerLevi` (`Langlands/Representation/Intertwining/PQIntertwiningInnerLeviProof.lean`); `PQIntertwiningOuterLeviStatement` proved: `pqIntertwiningOuterLevi` (`Langlands/Representation/Intertwining/PQIntertwiningOuterLeviProof.lean`) |

For the V.5.3 module see the source issues below. In the V.3.17 module,
`relativeRoots i` is Renard's `Σ′_∅`, and its explanation treats the coroot
coefficients of negative roots.

## Source issues

- **V.3.24, printed p.117 / PDF p.123.** Renard asserts that
  `S = C_∅^+ / C_{A_G}` is isomorphic to `ℕ^d` with `d = |Δ_∅|`, and reuses
  this in the proof of the finiteness Lemma of V.5.3 (printed p.125). This is
  false in general: for the diagonal torus of `SL_3`, `S` is
  `{(p, q) ∈ ℕ² | p ≡ q mod 3}` in simple-root coordinates, whose
  indecomposable elements `(3,0)`, `(1,1)`, `(0,3)` satisfy
  `(3,0) + (0,3) = 3·(1,1)`. The monoid is finitely generated (Gordan's
  lemma); the V.5.3 argument can be run on a finite orthant mapping onto it.
  The V.5.3 statement module records this route; V.3.24 itself is not stated.
- **V.5.3, finiteness Lemma, printed pp.124–125 / PDF pp.130–131.** Renard's
  `M` is the subalgebra generated by the `a_{zf}`, and he asserts that it is a
  finitely generated `A`-module; his computation treats only products
  `a_{z₁} a_{z₂ f}`, which gives finite generation of the `A`-module generated
  by the individual `a_{zf}`. The two differ in general (for
  `G_m` over `ℚ₃`, `K = 1 + 3ℤ₃`, `F_∅ = {-1}`, they are `A ⊕ Aε` and `Aε`).
  The published module states the module form and records the algebra form as an
  outstanding obligation; no corrected version is proposed. Renard's
  definition of `A` (generated by `a_z`, `z ∈ C_∅`) is read with `z ∈ C_∅^+`,
  as in the Corollary.
- **VI.7.4, Remark, printed p.186 / PDF p.192.** "L'idempotent `e_𝔰` n'est pas
  un élément de l'algèbre de Hecke `H(G)`" is false as a universal statement:
  for `G = GL_1`, the block of a character `χ` has projector given by
  convolution with `χ̄ · 1_{O^×} / vol(O^×) ∈ H(G)`, and for compact
  (anisotropic) `G` every `e_𝔰` lies in `H(G)`. It is read as a caution that
  `e_𝔰` need not lie in `H(G)`, and is not stated.

## Section findings

These findings update the previous note. Rows not mentioned keep their status
there.

- **I.2.** The I.2.3 unital right adjoint and closing Remark are stated
  (above). The I.2.1 caveat (e) ("no canonical vector-space structure on
  `Hom_A`, `⊗_A` without unit") is expository motivation, not a formal
  assertion.
- **IV.** (IV.2.1.1)–(IV.2.1.2), IV.2.3 for general cocompact `H`, and the
  IV.3.1 and IV.3.3 remarks are stated (above). The IV.3.1 Remark uses the
  smooth reading of `L²₀`: Renard's `𝒞^∞(G)` is the space of locally constant
  functions (II.1.2), and the literal `L²₀` can contain non-smooth vectors;
  the statement's Markdown records the example.
- **V.3.** V.3.17 is stated (above), extended to `Σ′_∅`. V.3.24 is a source
  issue (above).
- **V.5.** V.5.3 is stated with partial coverage (above): the finite-dimensional
  `H₀ = H(K₀, K)`, both product Lemmas, the Corollary, the finiteness Lemma in
  module form, the Theorem and the Remark, for actual groups with available
  corrected Kaletha–Prasad data and a compact open `K` normal in `K₀` with
  the published V.5.2 (ii) property. The algebra form of the finiteness
  Lemma is outstanding (above).
- **VI.4.** The VI.4.3 structure of `H(G, ρ)`, the VI.4.4 Lemma, the group
  `T` with its Remark and the last sentence of the VI.4.4 Proposition are
  stated (above), as are the closing sentence of the VI.4.4 Corollary and the
  right module structures of VI.4.2. Not stated: the
  identification of the quasi-inverse in (VI.4.1.4) with `M ↦ M ⊗_R V_Π` (it
  needs a balanced tensor product over the noncommutative ring `R`, which
  Mathlib does not provide).
- **VI.7.** The VI.7.1 Proposition and Theorem are stated (above), in the
  standard-family framework, with `Sc` read through the induction-occurrence
  support relation. The VI.7.1 Example (supercuspidal inertia classes are
  inertial supports, `[π] = Irr(G)[π]`) is not stated separately; its variety
  assertion is the published V.2.7 Corollary statement. The VI.7.4 Remark is
  a source issue (above).
- **VI.9.** The equivalence of (VI.9.6.1) and (VI.9.6.2) is stated (above).
  The Library's `ChainUnitAdjunction` records a naturality condition that
  the source's (VI.9.6.2) ⇒ (VI.9.6.1) argument does not state.
- **VI.10.** The VI.10.4 Theorem and Remarks 1–2 are stated (above). The
  intermediate assertions `ℨ_Ω ⊂ ℨ_D^{W(D)}`, `ℨ_Ω = ℨ_D^{W(D)}`, the bimodule
  centralizer Lemma and the identification of (VI.10.4.1) with `i_P^G` through
  (VI.10.4.2) are not stated.
- **VII.3.** VII.3.4 in explicit integral form and all three parts of the
  VII.3.5 Proposition are stated (above). The 'longueur' remark of VII.3.5
  (`d(P, Q)` is the length of the `w ∈ W(A_M)` with `w · P = Q`) is not stated
  and remains open: for nonminimal `M` the book defines no length function on
  `W(A_M)`, which in general need not be a Coxeter group, and the remark is not
  used in the proof. This is a limitation of the source and of the framework,
  not a claim that no length function exists; for example, for
  `M = GL_2 × GL_2` in `GL_4` the group `W(A_M)` has order 2 and its Coxeter
  length agrees with `d(P, Q)`.

## Remaining work recorded here

The ledger's section table still predates the dated updates. Open statement
items named above or in the previous updates: the algebra form of the V.5.3
finiteness Lemma; (VI.4.1.4); the
VI.10.4 intermediate assertions; V.4.6. None of the statement modules of the
table was proved at the commit above; the table gives their present proofs.

The V.4.6 Lemma was stated after the commit above. The [Chapter VI item
ledger](item-ledger-vi.md) records the later modules.

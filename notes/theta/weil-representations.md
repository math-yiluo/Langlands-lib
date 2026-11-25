# The Heisenberg group, Weil representations and Kudla's splitting

This note describes `Langlands/Theta/` (namespaces `Langlands.HeisenbergGroup`, `Langlands.Theta`,
`Langlands.Theta.Real`) together with the linear algebra it rests on in
`Langlands/LinearAlgebra/EpsilonHermitian/`, `Langlands/LinearAlgebra/Symplectic.lean`,
`Langlands/Group/Classical/` and `Langlands/Group/Unitary/`.

## The mathematics

For a non-degenerate symplectic space W over a nonarchimedean local field F of any
characteristic with 2 invertible, and a non-trivial character `ψ` of `F`, the
Heisenberg group `H(W) = W × F` has, by the theorem of Stone and von Neumann, a unique smooth
irreducible representation with central character `ψ`. The symplectic group acts on `H(W)`, and the
pairs `(g, M)` with `M ∘ ρ(h) = ρ(g·h) ∘ M` form the metaplectic group, an extension of `Sp(W)` by
`ℂˣ`, whose second projection is the Weil representation. In the Schrödinger model of a
polarization the operators are explicit: on the Siegel parabolic they are geometric, at the Weyl
elements they are partial Fourier transforms; their composition defines the Leray cocycle, computed
by the Weil index of quadratic forms, the Leray invariant of three Lagrangians and the Rao function.
For a dual pair `(G, H)` in `Sp(W)` one looks for a splitting `s` of the metaplectic cover over
`G × H` and restricts `ω_ψ ∘ s`; for the unitary pairs Kudla constructed such splittings from a
character `χ` of `Eˣ` whose restriction to `Fˣ` is a power of the quadratic character of E/F. The
theta correspondence and Howe duality describe how `ω_ψ ∘ s` decomposes.

The Library follows W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (cited
GKT), and every page of `Langlands/Theta/` outside `Real/` begins with the section or statement of
GKT it formalizes. Further sources named on the pages: Mœglin–Vignéras–Waldspurger, *Correspondances
de Howe sur un corps p-adique* (Stone–von Neumann), Kudla, *Splitting metaplectic covers of dual
reductive pairs* (1994), Ranga Rao (1993), Harris–Kudla–Sweet (1996), Mínguez (2008) for type II.
`Langlands/Theta/Real/` is the archimedean case, which GKT leaves out.

## Layout and the chapters of GKT

| GKT | Library | Content |
| --- | --- | --- |
| ch. 1 | `Langlands/Theta/Heisenberg/` | the Heisenberg group of a bilinear form (`Basic.lean`), central character and normalizing operators (`Representation.lean`), self-dual subgroups and the induced model (`SelfDual.lean`, `SelfDualSubgroup.lean`, `InducedModel.lean`), the Schrödinger model, its unitarity, irreducibility and admissibility, partial Fourier transforms and intertwiners, Stone–von Neumann (`StoneVonNeumann.lean`) |
| ch. 2 | `Langlands/Theta/Metaplectic/` (`Defs.lean`, `Exact.lean`, `InducedOperator.lean`, `StandardOperator.lean`, `SiegelParabolic.lean`, `SiegelLevi.lean`, `WeylElement.lean`, `Block.lean`, `Transport.lean`) | the metaplectic group of pairs, its exactness, the operators `M_A(g)`, the standard Weil operator `r(g)`, the Siegel parabolic and Levi, the Weyl element, the composition rule and block compatibility |
| ch. 3 | `Langlands/Theta/WeilIndex/` | characters of second degree and the Weil index, dimension one, the unramified case, the norm form of a quadratic extension, the invariants (determinant, Hilbert symbols) |
| ch. 4, App. B | `Langlands/LinearAlgebra/EpsilonHermitian/`, `Langlands/Group/Classical/`, `Langlands/Theta/Metaplectic/RaoFunction.lean` | `ε`-Hermitian forms over a division ring with involution, isotropic subspaces, Witt's theorem, Lagrangians and standard bases, the Leray invariant, Rao's five-term decomposition, the determinant; the Siegel parabolic, Bruhat and generalized Bruhat decompositions; the Rao function |
| ch. 10 | `Langlands/Theta/DualPair/TypeI.lean`, `Langlands/Theta/DualPair/Unitary/Form.lean`, `Langlands/Theta/DualPair/Unitary/TypeI.lean` | the symplectic space `W ⊗ V` of a type I pair, the unitary pair |
| ch. 11 | `Langlands/Theta/DualPair/TensorInvariants.lean`, `Langlands/Theta/DualPair/Unitary/` (`Pair.lean`, `Splitting.lean`, `LeraySplitting.lean`, `LeraySplittingFactor.lean`) | Gauss integrals of Hermitian forms (Proposition 11.3); the Leray splitting of `U(ν, ν)` (Theorem 11.6, Corollary 11.7, Case `3₊`, `W` split) |
| ch. 12 | `Langlands/Theta/DualPair/LerayCharacter.lean`, `Langlands/Theta/DualPair/TypeIIFourier.lean`, `Langlands/Theta/DualPair/Unitary/` (`Schrodinger.lean`, `SiegelParabolic.lean`, `WeylElement.lean`, `StandardOperator.lean`, `LerayScalar.lean`) | the splitting scalar, the type II splitting (Proposition 12.21), the formulas of Proposition 12.27 and the scalar at the Weyl element (Proposition 12.29) for the unitary pair |
| ch. 13 | `Langlands/Theta/Correspondence/ThetaLift.lean`, `Langlands/Theta/Correspondence/Unitary.lean` | the big theta lift, Howe duality (Theorem 13.21) as properties, the statement for the unitary pairs |
| ch. 18 | `Langlands/Theta/DualPair/TypeII.lean`, `Langlands/Theta/Correspondence/TypeII.lean` | the type II pair `(GL_m, GL_n)` and its Weil representation (Proposition 12.35, §18.5.2), the statement of Howe duality for it (Theorem 18.19) |
| outside GKT | `Langlands/Theta/Real/` | the real Schrödinger representation, the real metaplectic double cover and its Weil representation |

The chapters 5–9 of GKT (the explicit cocycles and the Rao cocycle, canonicity of the metaplectic
group, splittings of subgroups in general, topology and measure, the Weil representation as a
chapter of its own) and 14–17 have no files; the Library proves the statements of chapters 11 and 12
that it needs from chapter 2 directly (the scalar of a composition comes from Schur's lemma, not from
an explicit cocycle).

Layering: `Langlands/HarmonicAnalysis/` (bicharacters, Schwartz–Bruhat functions, Fourier transform)
→ `Heisenberg/` → `Metaplectic/` → `DualPair/` → `Correspondence/`; `WeilIndex/` and the
`ε`-Hermitian linear algebra join in `Metaplectic/RaoFunction.lean` and in `DualPair/`. `Real/`
uses, of the book's part, only `Heisenberg/Schrodinger.lean` and `Metaplectic/Defs.lean` (for
`RealMetaplecticGroup.toPairs`), besides `Langlands/LinearAlgebra/Symplectic.lean`, the archimedean
smooth vectors of `Langlands/Representation/Archimedean/SmoothVectors.lean` and analysis in
`Langlands/Analysis/`.

## Main definitions and theorems

**Heisenberg group** (`Langlands/Theta/Heisenberg/`). `HeisenbergGroup B` for a bilinear form `B`
on a module over a commutative ring with `⅟2`, with the action `HeisenbergGroup.isometryAction` of
isometries. Stone–von Neumann (`StoneVonNeumann.lean`), for `F : Type u` a nonarchimedean local
field (any characteristic) with `[Invertible (2 : F)]`, `W` finite-dimensional with its module
topology, `B` alternating and non-degenerate, `ψ : AddChar F ℂ` continuous and non-trivial:
`HeisenbergGroup.exists_isIrreducible_isSmooth` (a smooth irreducible representation with central
character `ψ` exists, in the universe of `W`), `HeisenbergGroup.nonempty_equiv` (any two are
isomorphic, in any universes) and `HeisenbergGroup.equiv_eq_smul` (the isomorphism is unique up to
a scalar). `HeisenbergGroup.schrodingerSB` is the Schrödinger representation on Schwartz–Bruhat
functions, smooth, irreducible and admissible (`SchrodingerIrreducible.lean`).

**Weil index** (`Langlands/Theta/WeilIndex/`, `F : Type` nonarchimedean local with `2 ≠ 0`).
`IsCharacterOfSecondDegree`, `weilIndex` (the constant `γ(f)` of a character of second degree,
GKT Definition 3.4), `weilIndexOne ψ = γ(ψ)` and `normalizedWeilIndex a ψ = γ(a, ψ)`;
`weilIndexOne_pow_eight`, `weilIndex_pow_eight`; `weilIndex_mul_norm` (the norm form of a
quadratic extension: γ(ψ ∘ tN) = η(t) γ(ψ ∘ N)); `weilIndexOne_scale_eq_one` (the unramified
case); `quadraticDet` and the invariants of quadratic spaces (`Invariants.lean`).

**Metaplectic group** (`Langlands/Theta/Metaplectic/`). For a representation `ρ` of
`HeisenbergGroup B` on `S`, `MetaplecticGroup ρ` is the subgroup of pairs `(g, M)` of
`isometryGroup B × (S ≃ₗ[ℂ] S)` with `M ∘ ρ(h) = ρ(g·h) ∘ M` (GKT (2.2)); `MetaplecticGroup.proj`
and `MetaplecticGroup.weil` are the projection and the Weil representation. For `ρ` smooth
irreducible with central character `ψ` over a nonarchimedean local field: `MetaplecticGroup.ker_proj`
(the kernel is the scalars), `MetaplecticGroup.proj_surjective` (`B` alternating non-degenerate,
`ψ` continuous non-trivial), `MetaplecticGroup.exists_scalar_mul_eq`. `standardOperator` is the
standard Weil operator `r(g)` of a polarization (GKT Definition 2.9) and `exists_standardOperator_comp`
gives `r(g₁) r(g₂) = c · r(g₁g₂)` with `|c| = 1`. `MetaplecticGroup.Splitting` is a splitting of a
homomorphism into `isometryGroup B` through the metaplectic group, with its Weil representation.

**Dual pairs** (`Langlands/Theta/DualPair/`).
- Type II: `typeIIWeil F m n`, the representation `(g, h)·Φ(x) = |det g|^{n/2} |det h|^{-m/2} Φ(h⁻¹ x g)`
  of `GL_m(F) × GL_n(F)` on Schwartz–Bruhat functions of `M_{n×m}(F)`; `typeIISplitting` (GKT
  Proposition 12.21) and `weil_typeIISplitting`: its Weil representation is `typeIIWeil F m n`
  (Proposition 12.35), for `F` with `⅟2`.
- **Kudla's splitting for the unitary pair `(U(ν, ν), U(Q))`** (`DualPair/Unitary/`), for `F : Type`
  a nonarchimedean local field of **characteristic zero**, E/F quadratic with conjugation `c`
  (`IsQuadraticInvolution c δ`), `Q` an invertible Hermitian `α × α` matrix over `E`, `ψ` a
  non-trivial unitary character of `F` and `χ : Eˣ →* Circle` continuous with
  χ|_{Fˣ} = χ_{E/F}^{|α|} (the hypothesis `hres`, GKT (11.2)): `IsLerayWeil c ψ χ Q μ κ ω` says
  that a representation `ω` of `U(ν, ν)` on Schwartz–Bruhat functions of `M_{α×ν}(E)` acts on the
  Siegel parabolic by the explicit operators and at the Weyl element by `κ` times the Fourier
  transform for the Haar measure `μ`; `exists_isLerayWeil` (such `κ` and `ω` exist for every `μ`),
  `IsLerayWeil.unique` (they are unique), `IsLerayWeil.isSmooth`, `IsLerayWeil.lintegral_enorm_sq`
  (unitarity), `IsLerayWeil.normalizes`. `leraySplitting` is the Leray splitting
  `g ↦ (g ⊗ 1, lerayWeil g)` in the metaplectic group of pairs (GKT Theorem 11.6, Corollary 11.7,
  Definition 11.13, Case `3₊`, `W` split); `leraySplittingFactor` is the function `β` of GKT (11.3),
  with `lerayWeil_eq_leraySplittingFactor_smul` and `standardOperator_comp_eq_leraySplittingFactor`
  (Theorem 11.6 in cocycle form: the Leray cocycle restricted to `U(ν, ν)` is the coboundary of `β`).
  `pairWeil` and `pairSplitting` (`DualPair/Unitary/Pair.lean`) extend it to `U(ν, ν) × U(Q)`, with
  `U(Q)` acting geometrically.
- `splittingScalar F χ m z = χ(z) |N_{E/F} z|^{m/2}` (`DualPair/LerayCharacter.lean`), and the
  tensor form of a type I pair `tensorHermitianForm` (`DualPair/TypeI.lean`).

**Theta lifts** (`Langlands/Theta/Correspondence/ThetaLift.lean`). `MetaplecticGroup.Splitting.bigTheta`
is Θ_{ψ,s}(π) = (ω_{ψ,s} ⊗ π^∨)_G (GKT Definition 13.17); `ThetaMultiplicityOne ω` and
`ThetaInjective ω` are parts (1) and (2) of Howe duality (Theorem 13.21) stated without `Θ` and `θ`,
and `HoweDuality ω` their conjunction; `finrank_hom_eq_finrank_bigTheta` (Corollary 13.8) relates
dim Hom_{G×H}(ω, π ⊠ σ) to dim Hom_H(Θ(π), σ) for admissible `π`.

**The real branch** (`Langlands/Theta/Real/`, namespace `Langlands.Theta.Real`, except
`RealMetaplecticGroup` in `Langlands.Theta`). `Real.schrodingerL2` (the Schrödinger representation of
the real Heisenberg group on `L²(ℝˡ)`), `RealMetaplecticGroup l` (triples `(s, U, V)` with `s`
symplectic, `U` unitary on `L²`, `V` invertible on Schwartz space, normalizing the Schrödinger
operators and normalized on vacuum vectors); `RealMetaplecticGroup.proj_surjective`,
`RealMetaplecticGroup.card_ker_proj` (the kernel has two elements),
`RealMetaplecticGroup.isCoveringMap_proj`, `RealMetaplecticGroup.contDiff_weil_comp` (smooth vectors
along smooth families), `RealMetaplecticGroup.oneParameter`, and `RealMetaplecticGroup.toPairs`, which
places the real group in the metaplectic group of pairs of the Schwartz model.
`Langlands/Theta/Real/Deprecated.lean` keeps deprecated aliases in `Langlands.Theta` for the
declarations of the branch.

## What is stated and not proved

- `HoweDualityTypeIIStatement` (`Correspondence/TypeII.lean`, Mínguez's theorem for
  `(GL_m(F), GL_n(F))`, `F : Type`) and the full `HoweDualityTypeII` are `Prop`s with no proof;
  `howeDualityTypeIIStatement_iff` restates the first as `ThetaMultiplicityOne`, and
  `thetaMultiplicityOne_typeIISplitting` derives Howe duality (1) for the Weil representation of the
  type II splitting **from** `HoweDualityTypeIIStatement`.
- `HoweDualityUnitarySplitStatement` (`Correspondence/Unitary.lean`): Howe duality for
  `pairWeil` of `U(ν, ν) × U(Q)` (characteristic zero, `W` split), stated, not proved; the non-split
  case and the other cases of GKT are not covered.
- The finite length of `Θ(π)` (GKT Theorem 13.19) is not formalized.
- Over `ℝ`: the cover `RealMetaplecticGroup l` → Sp_{2l}(ℝ) is not proved to be non-split, and the
  uniqueness of the group and of its Weil representation, a Lie group structure, the formulas on all
  generators and the Maslov cocycle are not in the Library (page of `Real/Metaplectic/Defs.lean`).

## Conventions

- **Polarizations.** In `HeisenbergGroup.schrodingerSB` and `Metaplectic/` the functions live on the
  file's `X`; the file's `(X, Y)` is GKT's `(Y, X)`. For `g` an isometry, the blocks
  `standardA`, `standardB`, `standardC`, `standardD` are those of `g⁻¹ = [[a, b], [c, d]]`, as in GKT
  (2.17).
- **The unitary pair.** `U(ν, ν)` acts on row vectors by `w ↦ w g⁻¹` (a right action, where GKT acts
  on the left), and `U(Q)` by left multiplication. The Library's form `hermitianSymplecticForm` is half
  of GKT's; `hermitianTracePairing` is GKT's, and `hermitianSchrodinger_scale_comp` says that GKT's
  Schrödinger model for `ψ` is the Library's for `ψ(2 ·)` (`DualPair/Unitary/LeraySplitting.lean`).
- **Measures.** GKT fixes the Haar measure in the Fourier transform at the Weyl element by
  unitarity; the Library states the formulas for every Haar measure `μ` and lets the scalar `κ` absorb
  the normalization (`IsLerayWeil`), and `IsLerayWeil.unique` shows that `κ` is then determined.
- **The quadratic character.** The condition on `χ` is written with the Library's
  `LocalClassField.normResidueSign F E`, the quadratic character of E/F by the norm residue symbol.
- **Weil index.** `weilIndexOne ψ = γ(ψ ∘ q₁)` with `q₁(x) = x²`; GKT's `f_b = ψ ∘ ½ q_b` is
  `x ↦ ψ(q x)` with `q = ½ q_b`.

## Why it is built this way

- The metaplectic group is defined as the group of pairs of a model (GKT 2.1.2), which needs no
  cocycle, no Weil index and no topology; the scalars that GKT computes by explicit cocycles are
  obtained here from Schur's lemma for the irreducible model (`MetaplecticGroup.exists_scalar_mul_eq`),
  and the splitting factor `β` is chosen as such a scalar.
- The Leray splitting of `U(ν, ν)` is constructed by generators and relations (the Siegel parabolic
  and the Weyl element generate, the relations of the big cell are checked on the explicit
  operators, `Langlands/Group/BigCellHom.lean` extends), which gives the formulas of GKT
  Proposition 12.27 directly.
- The real branch is kept apart from the book's part: smoothness, test functions, the Weil index and
  the topology of the group are different notions over `ℝ`; the two branches share the Heisenberg
  group, the Schrödinger operators and the symplectic notions, and meet in the group of pairs
  (`RealMetaplecticGroup.toPairs`).

## Origin of the text

Text is ported from the repository leanprover-community/riemann-hypothesis (commit `f1f6d65`) in
the real branch `Langlands/Theta/Real/`, in parts of `Langlands/Theta/Heisenberg/` (`Basic.lean`,
`InducedModel.lean`, `SelfDual.lean`, `SelfDualSubgroup.lean`, `StoneVonNeumann.lean`), in the
unitary block (`DualPair/Unitary/Form.lean`, `Schrodinger.lean`, `SiegelParabolic.lean`,
`Splitting.lean`, `WeylElement.lean`), in `DualPair/TypeII.lean`, `DualPair/LerayCharacter.lean`,
`DualPair/TensorInvariants.lean`, `Correspondence/TypeII.lean` and `WeilIndex/NormForm.lean`; the
other files are written on GKT. Each page says what it takes from the source, and
`licenses/RiemannHypothesis/SOURCE.md` lists the files and describes the terms of use.

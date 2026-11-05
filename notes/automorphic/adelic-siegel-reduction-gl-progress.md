# Adelic Siegel reduction: the published GL(n) chain and remaining general obligations

Worker 1377 wrote this note on 5 November 2026 against Library commit
`81bddf38b8069213a7ace261e56ea16dd84f3721`. It maps the published matrix-level
reduction theory for the actual adelic group `AdelicGL F n` to its sources. It
also records what the general target
`Langlands.Global.AdelicSiegelFactors.AdelicGoodSiegelReductionStatement` in
`Langlands/Global/AdelicSiegelFiniteVolume.lean` still needs. That target is
assigned to task `6adbbc46-4bb2-4c01-843a-d8ded48189f2`, revision 2, and it is
**not proved**. None of the modules below proves it, and none proves a
scheme-level instance of it for the general linear group.

## Sources

- T. A. Springer, *Reduction theory over global fields*, Proc. Indian Acad.
  Sci. (Math. Sci.) 104 (1994), 207–216. It is registered as
  `springer-1994-reduction-global-fields`, SHA-256
  `774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`, file
  `/home/taskhub/pilot/literature/Reduction theory over global fields (Springer, 1994).pdf`.
  The printed page is the PDF page plus 206. The sections used are:
  §§1.5–1.9 on heights (pp.209–210); Prop. 1.10 and Cor. 1.11 on GL(2) and
  SL(2) (pp.210–211); §2.1 and Remark 2.2 on Siegel sets
  `𝒮(c) = K·S(c)·P(𝔸)^0` (pp.211–212); the rank induction in §§2.3–2.4
  (p.212); adapted representations in §2.5 and Prop. 2.6 (p.213); and §3, the
  proof of the main results (pp.214–216).
- Getz–Hahn, *An Introduction to Automorphic Representations* (2024). It is
  registered as `getz-hahn-2024-automorphic-representations`, SHA-256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`. The
  sections used are Theorem 2.7.1 (Iwasawa decomposition, printed p.71, PDF
  p.88), Theorem 2.7.2 (reduction, p.72), and Theorem 2.4.3 with Example 2.2
  (maximal compact subgroups, p.59). The registered October 2026 author errata
  `getz-hahn-2024-errata-2026-10` was read: it goes from Chapter 1 directly to
  Chapter 3, so it corrects nothing in Chapter 2.

## Conventions in the GL(n) chain

Every module keeps an arbitrary number field `F`, an arbitrary universe and an
arbitrary rank `n`, including `n = 0` unless a theorem says otherwise. The
group is `AdelicGL F n = GL (Fin n) (Adeles F)` on the actual full adeles.
Heights use maximum coordinate norms at every place: normalized finite norms,
and archimedean norms raised to the place multiplicity (`height`,
`finiteNorm` and `infiniteNorm` in `PrimitiveAdelicHeight`). Chamber
inequalities use the normalized idele absolute value `IdeleAbsoluteValue.full`.
The reduction theorems for GL(2) and GL(n) act by rational matrices on the
right (`g * γ = k * b`). The Siegel-shape theorem converts this to the
rational-left convention of the general target by inversion.

## Published modules and main declarations

All declarations below are in namespace `Langlands.Global.PrimitiveAdelicHeight`
unless another namespace is named. Their paired Markdown files give the proof
routes.

**Heights and minima.**
- `PrimitiveAdelicHeight`: vectors, rational vectors, primitivity and `height`.
- `PrimitiveAdelicContent`: the content idele and normalized vector.
- `PrimitiveAdelicNormalization`: compact `normalizedSet` and
  `exists_content_mul_normalized`.
- `PrimitiveAdelicBounded`: `exists_isCompact_bounded_representatives`.
- `PrimitiveAdelicMinimum`: `rationalHeight F n g v = height F n (g.val *ᵥ rational F n v)`.
  `finite_rationalHeight_le` shows that only finitely many such height values
  of nonzero rational vectors lie below any real bound. `exists_min_rationalHeight`
  shows that a minimum is attained when `0 < n`.
- `PrimitiveAdelicBasis`: a rational basis change that puts a minimizing
  vector in the first column (`minimumAdaptedMatrix`).

**Rank two.**
- `Langlands.Global.MixedSpaceDirichlet`: simultaneous Dirichlet approximation
  in the mixed space (`exists_dirichlet_infiniteAdeles`).
- `PrimitiveAdelicGauss`: `exists_rankTwoVector_height_le`. There is
  `C > 0` such that for every idele `x` and adele `u`, some nonzero rational
  `(l, m)` gives a vector of height at most `C √|x|` under the matrix with rows
  `(x, u)` and `(0, 1)`.
- `PrimitiveAdelicGL2`: `exists_rationalHeight_le_sqrt_det`, a Hermite bound
  `C √|det g|`. Also `exists_reduction`, which gives
  `g * γ = k * b` with `k` integral at the finite places, entries bounded by
  one at infinity and determinant of local norm one everywhere, and `b` upper
  triangular with `|t₁| ≤ c |t₂|`.

**Rank n.**
- `PrimitiveAdelicGLn`: `exists_reduction_GL n`, which states
  `∃ c B, 0 < c ∧ 1 ≤ B ∧ ∀ g, ∃ γ k b, g * rational γ = k * b ∧
  IsBoundedUnimodular F n B k ∧ IsReducedTriangular F n c b`.
- `Langlands.LinearAlgebra.TriangularUnitary`:
  `exists_upperTriangular_mul_unitary` (QR factorization over any `RCLike`
  field) and entry and diagonal bounds for the factors.
- `PrimitiveAdelicUnipotent`: `exists_isCompact_unitriangular_reduction`.
  There is a compact set `Ω` of unitriangular adelic matrices such that every
  unitriangular adelic `N` satisfies `μ N ∈ Ω` for some rational unitriangular
  `μ`.
- `AdelicGLStandardCompact`: `standardCompact F n`. Its elements are unitary
  at the infinite places (`standardInfiniteCompact`) and lie in
  `FiniteAdelicGL.standardIntegral` at the finite places. The module proves
  `isCompact_standardCompact` and
  `exists_upperTriangular_mul_mem_standardCompact`.
- `AdelicGLSiegelShape`: `siegelSetGL F n Ω_N C c` is the set of `h` with
  `h = N · diag(ω) · diag(a(r)) · κ`. Here `N ∈ Ω_N`, every `ω i ∈ C`,
  `a(r)` consists of the positive real ideles `PositiveRealIdeles.full F (r i)`,
  `κ ∈ standardCompact F n`, and `|a_{i+1}| ≤ c |a_i|` for consecutive indices.
  `exists_rational_mul_mem_siegelSetGL` gives a compact unitriangular `Ω_N`, a
  compact `C` of norm-one ideles and `c > 0` such that every `g` has a rational
  `γ` with `rational γ * g ∈ siegelSetGL F n Ω_N C c`.
- `AdelicGLStandardCompactMaximal`: `isMaximalCompact_standardCompact`. It
  also proves `isMaximalCompactSubgroup_generalLinear`, which transports this
  to `AdelicGroupPoints.IsMaximalCompactSubgroup` for the scheme
  `GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)` through
  `GeneralLinearGroupPoints.adelicHomeomorph`.
- `AdelicGLIwasawa`: `upperTriangular_mul_standardCompact`, the equality
  `upper triangular subgroup · standardCompact F n = univ`.

**Scheme-level adapters for the general target** (namespace
`Langlands.Global.AdelicSiegelFactors`).
- `AdelicSiegelNormOne`:
  `IsSiegelAlgebraicSetup.rational_mul_weakSiegelProduct_subset_normOne`.
- `AdelicSiegelCoverCriteria`: `IsSiegelAlgebraicSetup.isSiegelCover_iff_forward`
  and `IsSiegelAlgebraicSetup.exists_isSiegelCover_of_strictCover`. These
  reduce `IsSiegelCover` to forward rational-left coverage once the setup and
  the Iwasawa compact are supplied.

## Differences from Springer's printed route

- **Rank induction.** Springer §2.3 prints the reduction property `R(c)` with
  rational elements `γ ∈ P_i(k)`. At each column, the Lean induction instead
  minimizes over all nonzero rational vectors, the minimality used in the
  proof of Prop. 1.10.
- **Rank-two step.** Springer §1.10 proves the minimality inequality
  `|x| ≤ ‖(λ + μu)x e₁ + μ e₂‖` and specializes it to `μ = 1` in his (3). The
  Lean proof does not follow that specialization. Adapting it to max norms
  over an arbitrary number field would have required a covering-radius bound
  uniform in the field. Instead, the Lean proof combines a two-dimensional
  Dirichlet approximation in the mixed space, a compact norm-one fundamental
  set and compact denominators. This gives the `C √|x|` bound above, which
  Springer does not state literally.
- **Compact subgroup and action.** Springer's `𝒮(c) = K·S(c)·P(𝔸)^0` uses an
  arbitrary compact set `K` and covers `G(𝔸)^0` by `𝒮(c)·G(k)`, with rational
  elements on the right. The implemented Siegel shape fixes
  `K = standardCompact F n` and puts the rational element on the left. A QR factorization
  at each infinite place moves the bounded factor `k` of the reduction theorem
  into the standard compact subgroup.

## What the GL(n) chain does not supply

1. **The scheme-level GL_N instance.** No module assembles an instance of
   `IsSiegelAlgebraicSetup` and `IsSiegelCover` for the general linear group
   scheme. Much of the algebraic layer is already published, however. Below,
   `i = GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of k)` over an
   arbitrary field `k`; the paths are under `Langlands/GroupScheme/`.
   - **Standard subgroups.** `Langlands.GroupScheme.generalLinearStandardParabolic`
     (`Rational/GeneralLinearStandardParabolicProof`) proves
     `GeneralLinearStandardParabolicStatement`. Fix a generic cocharacter `ν`
     of the diagonal torus with strictly decreasing coordinates. Then the
     simple relative roots are the adjacent characters. For every block shape
     `B` and `J = GeneralLinear.blockSimpleRoots k B`, the functors
     `standardParabolic i ν J`, `standardLevi i ν J` and
     `standardUnipotent i ν J` equal `blockShapeParabolic`, `blockShapeLevi`
     and `blockShapeUnipotent` on every test scheme. The helper module
     `Rational/GeneralLinearStandardBlocksProof` proves these equalities as
     `GeneralLinear.standardParabolic_blockSimpleRoots`,
     `standardLevi_blockSimpleRoots` and `standardUnipotent_blockSimpleRoots`.
     The rational points of each standard subgroup are the comap of the
     matrix block subgroup under the canonical point map
     (`GeneralLinear.blockShapeParabolicPoints_eq_comap` and its Levi and
     unipotent analogues in `Rational/GeneralLinearCanonicalPointsProof`).
     The reference note `notes/renard/standard-parabolic-progress.md`
     documents this layer.
   - **Scheme representatives.** `Rational/StandardRepresentability` proves
     that the closed subgroups `Standard.parabolicScheme`,
     `Standard.leviScheme` and `Standard.unipotentScheme` represent the same
     standard functors on every test scheme
     (`Standard.isRepresentedBy_parabolicHom`, `isRepresentedBy_leviHom` and
     `isRepresentedBy_unipotentHom`).
   - **Torus and roots.** `generalLinearRationalStatement`
     (`Rational/GeneralLinearProof`) shows four things. The diagonal torus is
     a maximal split torus, and its relative roots are the characters
     `eᵢ - eⱼ`. These roots form a relative root system. The dynamic
     centralizer of every generic cocharacter is `torusCentralizer i`.
     `GeneralLinear.isGenericCocharacter_diagonalTorus_iff` characterizes
     genericity as injectivity of the weights.
   - **Other structure.** `generalLinearBorel` (`Absolute/GeneralLinearBorelProof`)
     shows that for strictly decreasing weights the block parabolic is a Borel
     subgroup, forming a Borel pair with the diagonal torus.
     `generalLinearCharacters` (`Rational/CharactersProof`) shows that the
     scalar torus is a split component of GL_n when `n ≥ 1`.
     `GeneralLinear.reductiveStatement` (`Reductive/GeneralLinearProof`) shows
     that GL_n is connected reductive.
     `Dynamic.isGeometricUnipotentRadical_of_unitriangular_inputs`
     (`Dynamic/UnipotentStructure`) gives the geometric-unipotent-radical
     predicate for a smooth affine group and a cocharacter whose parabolic,
     unipotent and centralizer functors are represented. Its other inputs are
     the published theorems `unitriangularUnipotent` and
     `unipotentClosedSubgroup` and reductivity of the represented
     centralizer.

   What remains for the GL_N instance is comparison and assembly:
   - Each clause of `IsSiegelAlgebraicSetup` at `J = ∅` must be proved,
     using the results above where they apply. A search of `81bddf38` found
     no GL_N-specific result for four clauses: `IsMinimalParabolicSubgroup`,
     `IsRationalLeviSubgroup`, the relative roots of
     `torusToStandardParabolic`, and the derived-subgroup clause (SL_N with
     its maximal split torus). Generic minimality of the standard parabolic
     is the subject of task `bc8072c0-8a2b-4636-ab3c-7f04a4afb6a5`.
   - The all-test identifications must be compared with the actual adelic
     points `AdelicGroupPoints F (Standard.unipotentScheme i ν ∅)` and
     `AdelicGroupPoints F (Standard.leviScheme i ν ∅)`. The comparison runs
     through `GeneralLinearGroupPoints.adelicHomeomorph` against the
     unitriangular and diagonal matrix sets of the GL(n) chain.
   - `positiveMap` for the diagonal torus must be compared with the diagonal
     positive real ideles `PositiveRealIdeles.full` used in `siegelSetGL`.

   The full scheme-level GL_N instance remains open, and so does the general
   theorem.
2. **Positive-torus compatibility.** No module proves `IsPositiveTorusCompatible`
   for the transported `standardCompact`.
3. **General connected reductive G.** Springer §3 goes through several steps:
   - restriction of scalars to `ℚ` (§3.1);
   - split groups, with semisimple-rank-one groups classified as `H × T` for
     `H ∈ {GL(2), SL(2), PGL(2)}` (§§3.2–3.3);
   - rank induction through Levi subgroups of maximal parabolics (§§2.3–2.4);
   - representations adapted to maximal parabolics, and the Bruhat-decomposition
     argument of Prop. 2.6 (§§2.5–2.6);
   - Galois descent, both for compactness in the anisotropic case (§3.5) and
     for the final semisimple-rank-one case (§3.6).

   The heights above are exactly the vector heights used for an adapted
   representation `ρ : G → GL(V)` once `ρ(g)` is transported to `AdelicGL`.
   The algebraic inputs, however, have not been proved. These are the generic
   minimal parabolic (task `bc8072c0-8a2b-4636-ab3c-7f04a4afb6a5`),
   centralizer reductivity and the derived/central split product, and they
   are owned by the structural program. Compactness of `M(F)\M(𝔸)^1` for the
   anisotropic minimal Levi `M` is also open; it is not a consequence of the
   GL(n) chain.

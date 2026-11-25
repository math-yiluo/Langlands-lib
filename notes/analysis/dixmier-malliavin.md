# The Dixmier–Malliavin theorem and linear Lie groups

This note describes the Library's Dixmier–Malliavin theorem: its proof in
`Langlands/Analysis/DixmierMalliavin/`, the layer of linear Lie groups it is proved on
(`Langlands/Geometry/Manifold/LinearLieGroup/`), its statement in the Library's archimedean notions
(`Langlands/Representation/Archimedean/DixmierMalliavin.lean`), its adelic forms
(`Langlands/Global/`) and the statements that use it.

## The mathematics

Dixmier and Malliavin proved that on a real Lie group `G` every smooth compactly supported function
is a finite sum of convolutions `φ ⋆ ψ` of smooth compactly supported functions, and that every
smooth vector of a representation is a finite sum of vectors `π(φ)v` (J. Dixmier and P. Malliavin,
*Factorisations de fonctions et de vecteurs indéfiniment différentiables*, Bull. Sci. Math. (2) 102
(1978), Théorème 3.1). The proof rests on a lemma in one variable: for a sequence `M_p`, the Dirac
measure at `0` is a convergent series `∑ c_p g^{(p)}` of derivatives of one smooth function plus a
smooth function, both supported in `[0, ε]`, with `∑ |c_p| M_p < ∞`. Applied along the one-parameter
subgroups exp(tX) of a basis of the Lie algebra and integrated in coordinates of the second kind,
it factors `f`. In the theory of automorphic forms the theorem turns a statement about
convolutions `f₁ ⋆ f₂` (trace class of `R(f₁ ⋆ f₂)`, the simple trace formula for `f₁ ⋆ f₂`) into
one about all smooth test functions.

The Library proves the factorization of functions, for Lie groups with a closed linear
realization, which covers GL_n(ℝ), GL_n(ℂ) and the archimedean points G(F_∞) of every connected
reductive group over a number field; the files of this note contain no factorization of smooth
vectors.

## Layout

| Layer | Files | Content |
| --- | --- | --- |
| one variable | `Langlands/Analysis/DixmierMalliavin/ExponentialKernel.lean`, `KernelProduct.lean`, `KernelBounds.lean`, `SmoothWeakLimit.lean`, `Line.lean` | the one-variable lemma (`Line.lean`); the other files are internal to its proof |
| linear Lie groups | `Langlands/Geometry/Manifold/LinearLieGroup/Exponential.lean`, `Basic.lean`, `Units.lean`, `ClosedSubgroup.lean`, `ProductCoordinates.lean`, `HaarDensity.lean`, `Realization.lean` | Lie subgroups of the units of a finite-dimensional normed real algebra with exponential charts, the unit group, von Neumann's closed-subgroup theorem, coordinates of the second kind and the density of Haar measure in them, closed linear realizations |
| the theorem on linear groups | `Langlands/Analysis/DixmierMalliavin/DirectionalSeries.lean`, `IteratedKernel.lean`, `LinearGroup.lean`, `Product.lean` | series of directional derivatives, the iterated kernels, the theorem for `IsExpLieAlgebra`, the theorem on a product with a totally disconnected factor |
| the Library's notions | `Langlands/Representation/Archimedean/DixmierMalliavin.lean` | the theorem for `smoothCompactKernels` and `gardingKernelConvolution` |
| adelic points | `Langlands/Global/InfiniteAdelicLinearRealization.lean`, `Langlands/Global/AdelicDixmierMalliavin.lean`, `Langlands/Global/ArchimedeanGLDixmierMalliavin.lean`, `Langlands/TraceFormula/CompactSmoothAdelicGLTestConvolution.lean` | a closed linear realization of `G(F_∞)`; the theorem for adelic test functions, for `GL_n(F_∞)`, and for the tensor test functions of `GL_n(𝔸)` |

Imports go upward in the table: the one-variable files import Mathlib and each other only; the
linear Lie groups import Mathlib and `Langlands/Analysis/SmoothLinearDeterminant.lean`; the theorem
uses both and the convolution integral `Langlands.Hecke.convolutionIntegral`.

## Linear Lie groups

In namespace `Langlands.LinearLieGroup`, for a finite-dimensional normed real algebra `𝔸`:

- `IsExpLieAlgebra G 𝔤` (`Basic.lean`), for a subgroup `G` of `𝔸ˣ` and a subspace `𝔤` of `𝔸`:
  `exp X ∈ G` for `X ∈ 𝔤`, and near `0` `exp X ∈ G` implies `X ∈ 𝔤`. From it, charts
  `g exp X` and a Lie group structure on `G` modelled on `𝔤`; the charted space is a definition, not
  an instance, and statements install it locally.
- `isExpLieAlgebra_of_isClosed` (`ClosedSubgroup.lean`, von Neumann): every closed subgroup of `𝔸ˣ`
  has the exponential Lie algebra `lieSubmodule G hG`; with the Lie–Trotter formula
  `tendsto_exp_mul_exp_pow`.
- `IsClosedLinearRealization I ρ` (`Realization.lean`), for a Lie group `G` in Mathlib's sense and
  `ρ : G →* 𝔸ˣ`: `ρ` is a closed embedding, smooth, and a map from some `Fin m → ℝ` to `G` is smooth
  when its composite with `ρ` is. `isClosedLinearRealization_id`: the identity of `𝔸ˣ` is one. This
  is the hypothesis under which the results on `IsExpLieAlgebra` apply to a Lie group given in the
  Library's notions.

## Main theorems

- **The one-variable lemma** `Langlands.Analysis.DixmierMalliavin.exists_dirac_eq_tsum_iteratedDeriv_add`
  (`Langlands/Analysis/DixmierMalliavin/Line.lean`, Dixmier–Malliavin, Lemme 2.5): for every sequence
  `M` and `ε > 0` there are coefficients `c` with `∑ |c p| M p < ∞` and smooth `g`, `h` supported in
  `[0, ε]` such that `F(0) = ∑ c_p ∫ F^{(p)} g + ∫ F h` for every smooth `F` whose derivatives are
  bounded by `M` on `[0, ε]`.
- `Langlands.LinearLieGroup.IsExpLieAlgebra.exists_eq_sum_convolutionIntegral`
  (`Langlands/Analysis/DixmierMalliavin/LinearGroup.lean`): for `G` with `IsExpLieAlgebra G 𝔤`, a left
  Haar measure `μ`, a neighbourhood `U` of `1` and `f : G → ℂ` smooth with compact support, there are
  `n` and `φ ψ : Fin n → G → ℂ`, smooth, `φ i` compactly supported in `U`,
  `tsupport (ψ i) ⊆ tsupport f`, with `f = ∑ i, Langlands.Hecke.convolutionIntegral μ (φ i) (ψ i)`.
- `Langlands.Archimedean.exists_eq_sum_gardingKernelConvolution`
  (`Langlands/Representation/Archimedean/DixmierMalliavin.lean`): for a Lie group `G` (charted on a
  normed real space `E`, `LieGroup 𝓘(ℝ, E) ∞ G`, Hausdorff, locally compact, Borel) with a closed
  linear realization `ρ : G →* 𝔸ˣ` (`𝔸` complete, finite-dimensional), a left Haar measure `μ`, a
  neighbourhood `U` of `1` and `f : smoothCompactKernels E G`, there are `n` and
  `φ ψ : Fin n → smoothCompactKernels E G` with `tsupport (φ i) ⊆ U`, `tsupport (ψ i) ⊆ tsupport f`
  and `f = ∑ i, gardingKernelConvolution μ (φ i) (ψ i)`;
  `Langlands.Archimedean.exists_eq_sum_gardingKernelConvolution_units` is the case `G = 𝔸ˣ`.
- `Langlands.Analysis.DixmierMalliavin.exists_eq_sum_convolutionIntegral_prod`
  (`Langlands/Analysis/DixmierMalliavin/Product.lean`): on `A × B`, `A` with a closed linear realization
  and `B` locally compact, Hausdorff and second countable, a compactly supported continuous `f`
  smooth in the first variable and right invariant under a compact open subgroup `V` of `B` is a
  finite sum of convolutions of such functions, the right factors being left invariant under `V`.
- `Langlands.Global.InfiniteAdelicGroupPoints.exists_isClosedLinearRealization`
  (`Langlands/Global/InfiniteAdelicLinearRealization.lean`): for a connected reductive group scheme
  `G` over a number field `F`, `G(F_∞)` with the Library's manifold structure has a closed linear
  realization (through a faithful matrix representation, `matrixRealization`).
- `Langlands.Global.AdelicGroupPoints.IsAdelicTestFunction.exists_eq_sum_convolution`
  (`Langlands/Global/AdelicDixmierMalliavin.lean`): for `G` affine, locally of finite type and connected
  reductive over a number field, every test function `f` on `G(𝔸_F)` (`IsAdelicTestFunction`) is a
  finite sum `∑ i, ∫ φ i a * ψ i (a⁻¹ g) d(Measure.haar)` with `φ i`, `ψ i` test functions.
- `Langlands.Global.ArchimedeanGL.SmoothCompactKernel.exists_eq_sum_convolution`
  (`Langlands/Global/ArchimedeanGLDixmierMalliavin.lean`): the same for `GL_n(F_∞)` and
  `SmoothCompactKernel K n`, with supports in `U` and in `tsupport κ`.
- `Langlands.TraceFormula.CompactSmoothAdelicGLTest.exists_eq_sum_convolution_subgroupIndicator`
  (`Langlands/TraceFormula/CompactSmoothAdelicGLTestConvolution.lean`): a tensor `a ⊗ b` of a smooth
  compactly supported archimedean function and a finite test function on `GL_n(𝔸_E)` is
  ∑ᵢ (αᵢ ⊗ 1_K) ⋆ (α'ᵢ ⊗ b) for a compact open `K` fixing `b` on the left: the finite component `b`
  is kept on the right factors.

## Uses: what is proved from named hypotheses

The theorem passes from convolutions to smooth test functions in three trace-class and
trace-formula statements:

- `Langlands.QuotientIntegration.compactQuotientSmoothTraceClass_of_convolution` and
  `Langlands.QuotientIntegration.compactQuotientProductSmoothTraceClass_of_convolution`
  (`Langlands/Analysis/Local/CompactQuotientSmoothTraceClassReduction.lean`):
  `CompactQuotientSmoothTraceClassStatement` and `CompactQuotientProductSmoothTraceClassStatement`
  (`Langlands/Analysis/Local/CompactQuotientSmoothTraceClassStatement.lean`) are proved **from**
  `CompactQuotientConvolutionTraceClassStatement`
  (`Langlands/Analysis/Local/CompactQuotientConvolutionTraceClassStatement.lean`), which is stated and
  not proved; so the smooth forms are proved only from that hypothesis.
- `Langlands.Automorphic.GroupSchemeFunctions.groupSchemeFullAEL2CuspidalSmoothTraceClass_of_convolution`
  (`Langlands/Automorphic/GroupSchemeFullAEL2CuspidalSmoothTraceClassReduction.lean`) derives
  `GroupSchemeFullAEL2CuspidalSmoothTraceClassStatement` (trace class of R_cusp(f) for every adelic
  test function, under the hypothesis, inside the statement, that R_cusp(f) is Hilbert–Schmidt for
  every test function) from `IntegratedActionConvolutionStatement`, which is proved
  (`Langlands.Analysis.integratedActionConvolution`,
  `Langlands/Representation/Unitary/IntegratedConvolutionProof.lean`); the smooth statement therefore
  holds, by the composite of the two theorems.
- `Langlands.TraceFormula.CompactSmoothAdelicGLTest.tensor_eq_sum_convolution` is used by
  `Langlands.TraceFormula.generalLinearTensorSimpleTraceFormula_of_simpleTraceFormula`
  (`Langlands/TraceFormula/GeneralLinearTensorSimpleTraceFormulaReduction.lean`), which derives the
  simple trace formula of `GL_n` for tensor test functions from
  `GeneralLinearSimpleTraceFormulaStatement` and `GeneralLinearRadicalIntegralVanishingStatement`; see
  [the twisted trace formula and cyclic base change](../automorphic/twisted-trace-formula-and-base-change.md).

## Conventions

- Convolution is `(φ ⋆ ψ)(x) = ∫ φ(a) ψ(a⁻¹ x) dμ(a)` for a **left** Haar measure
  (`Langlands.Hecke.convolutionIntegral`, `gardingKernelConvolution`).
- `smoothCompactKernels E G` are the smooth compactly supported complex functions for Mathlib's
  manifold structure modelled on `𝓘(ℝ, E)`; on `IsExpLieAlgebra` groups the charts are the
  exponential ones, and `IsClosedLinearRealization` transports between the two.

## Why it is built this way

- The proof is carried on its own vehicle, `IsExpLieAlgebra`, a small theory of linear Lie groups
  with exponential charts, because the coordinates of the second kind and the density of Haar
  measure in them are explicit there; the theorem is then stated on the Library's
  `smoothCompactKernels` and convolution, reached through `IsClosedLinearRealization`.
- The closed-subgroup theorem makes the hypothesis hold for `G(F_∞)` of every connected reductive
  group, so the adelic theorem needs no restriction to `GL_n`.
- The product form keeps the finite component: the consumers need the right factors to keep the
  invariance (and, for the trace formula, the finite component) of the function factored.
- The Library states the theorem for groups with a closed linear realization, not for every real Lie
  group as Dixmier and Malliavin do; that is what the applications need.

## Origin of the text

Most files of `Langlands/Analysis/DixmierMalliavin/` and `Langlands/Geometry/Manifold/LinearLieGroup/`
(all but `Realization.lean`) and `Langlands/Global/ArchimedeanGLDixmierMalliavin.lean` are ported from
the repository leanprover-community/riemann-hypothesis (commit `f1f6d65`); each page names its
source, and `licenses/RiemannHypothesis/SOURCE.md` describes the source and the terms of its use.

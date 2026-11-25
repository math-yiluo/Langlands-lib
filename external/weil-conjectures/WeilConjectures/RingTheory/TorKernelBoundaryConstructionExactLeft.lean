/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.TorKernelBoundaryConstruction
import WeilConjectures.RingTheory.TorKernelBoundaryConstructionExactLeftKernel
import WeilConjectures.RingTheory.TorKernelBoundaryConstructionExactLeftRange

@[expose] public section
universe u
open CategoryTheory
open scoped TensorProduct
namespace CategoryTheory

/-- Exactness of the constructed boundary at Tor.

Source: Stacks Project, Algebra, Tags 00M0 and 00LZ; Homology, Tag 0111.

Proof: Put K = ker(q), and let P be the projective resolution of N used by
`torKernelBoundary`, with augmentation epsilon. Choose free resolutions A, B, C
of K, F, N in an augmentation-compatible degreewise split short exact sequence
0 -> A -> B -> C -> 0. Tensor with M; the splitting identities ensure that this
is still a short exact sequence of complexes. The homology sequence is exact.
The augmentations and right exactness of tensor identify H0(A tensor M) with
K tensor M and H0(B tensor M) with F tensor M.

Choose an augmentation-compatible comparison a : P -> C. In degree zero,
lift a0 to B0 through the split quotient, and compose with B's augmentation
to obtain e0 : P0 -> F. Choose lifts b0 : P0 -> B0 and b1 : P1 -> B1 of a0 and a1
through the split quotient maps. The chain map identity for a implies that
dB b1 - b0 dP factors uniquely through A0; call the factor t : P1 -> A0.
Writing i : K -> F, augmentation compatibility and epsilonB dB = 0 give
i epsilonA t = -e0 dP, so epsilonA t is the negative of the kernel restriction
of e0 dP. For a cycle z of P tensor M, (b1 tensor 1)(z) lifts
(a1 tensor 1)(z), and its differential is (alpha0 tensor 1)(t tensor 1)(z),
since (dP tensor 1)(z) = 0. The snake formula therefore sends its class to
[(t tensor 1)(z)]. Applying epsilonA identifies this with the negative of
the explicit cycle boundary for e0. The chosen lift e in `torKernelLift`
differs from e0 by a map k : P0 -> K. The two explicit cycle boundaries differ
by (k tensor 1)(dP tensor 1)(z), which is zero. Boundaries also map to zero by
`torKernelTensor_boundary`, so this comparison descends to homology. Thus the
transported homology connecting map is the negative of `torKernelBoundary`
for the snake convention just described. Negation changes neither the kernel
nor the image of a linear map, so both adjacent exact pairs remain exact
when the connecting map is replaced by `torKernelBoundary`.

Resolution comparison identifies H1(C tensor M) with Tor1(N,M) and
H1(B tensor M) with Tor1(F,M); augmentation-compatible maps identify the
preceding map with Tor1(q,M). Exactness at H1(C tensor M) therefore transports
to the displayed pair. In particular a class killed by the constructed boundary
comes from H1(B tensor M), and every such image is killed by the boundary.
No projectivity of F is required.
(blueprint: lem-sc-p1-tor-kernel-boundary-construction-exact-left) -/
theorem tor_kernel_boundary_construction_exact_left
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    (F N : ModuleCat.{u} R) (q : F →ₗ[R] N) (hq : Function.Surjective q) :
    Function.Exact (((Tor' (ModuleCat.{u} R) 1).map
      (ModuleCat.ofHom q)).app M).hom (torKernelBoundary M F N q hq) := by
  intro y
  constructor
  · exact tor_kernel_boundary_construction_exact_left_kernel R M F N q hq y
  · rintro ⟨x, rfl⟩
    exact tor_kernel_boundary_construction_exact_left_range R M F N q hq x

end CategoryTheory

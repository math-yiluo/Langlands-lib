/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.TorKernelBoundaryConstruction
import WeilConjectures.RingTheory.TorKernelBoundaryConstructionExactLeft
import WeilConjectures.RingTheory.TorKernelBoundaryConstructionExactRight

/-!
# Exactness for the constructed kernel connecting map

Source: Stacks Project, Algebra, Tags 00M0 and 00LZ.
-/

@[expose] public section
universe u
open CategoryTheory
open scoped TensorProduct
namespace CategoryTheory

/-- Exactness of the explicit cycle boundary, without any naturality assertion.

Source: Stacks Project, Algebra, Tag 00M0 (proof of the Tor exact sequence),
Tag 00LZ (comparison of resolutions), and Homology, Tag 0111 (connecting map).

Proof: Put K = ker(q). Choose a horseshoe resolution of the short exact sequence
0 → K → F → N → 0, with degreewise split rows, using free resolutions of K and N.
After tensoring with M the rows remain split exact. The homology long exact
sequence gives exactness at H₁ of the right resolution and H₀ of the left one.
Identify H₀ of the left and middle resolutions with K tensor M and F tensor M
by their augmentations and right exactness of tensor. Compare the chosen
projective resolution P of N used in torKernelBoundary with the right horseshoe
resolution by an augmentation-compatible chain map. Lift its degree-zero map to
the middle resolution using the splitting. Composing with the middle augmentation
gives a lift e₀ : P₀ → F of P's augmentation. The snake connecting map on a tensor
cycle z uses a degree-one lift b₁ of the comparison map and a degree-zero lift b₀.
The difference d_B b₁ - b₀ d_P factors through the left degree-zero term A₀.
After its augmentation to K, this factor is the negative of the kernel
restriction of e₀ d₁, because the middle augmentation kills d_B. On cycles,
the b₀ d_P term vanishes after tensoring, so this factor computes the connecting
map. Thus, with this snake convention, the transported connecting map is the
negative of the explicit cycle boundary for e₀. The lift e used in
torKernelBoundary differs from e₀ by a map k : P₀ → K. The difference of the
explicit degree-one boundaries is k d₁; after tensoring this vanishes on cycles.
Negation preserves both kernel and image, so the two exact pairs hold for
torKernelBoundary as well. Resolution comparison identifies the preceding
homology map with Tor₁(q,M); augmentation compatibility identifies the following
homology map with the kernel inclusion tensor 1. Transport the exact pairs
along these isomorphisms. The two component lemmas below isolate the respective
positions of this argument; their Lean proofs remain open.

This holds also for zero modules, identity surjections (zero kernel), and
nonprojective F: the free resolutions, not F, supply the projectivity.
(blueprint: lem-sc-p1-tor-kernel-boundary-construction-exact) -/
theorem tor_kernel_boundary_construction_exact
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    (F N : ModuleCat.{u} R) (q : F →ₗ[R] N) (hq : Function.Surjective q) :
    Function.Exact (((Tor' (ModuleCat.{u} R) 1).map
      (ModuleCat.ofHom q)).app M).hom (torKernelBoundary M F N q hq) ∧
    Function.Exact (torKernelBoundary M F N q hq)
      ((LinearMap.ker q).subtype.rTensor M) := by
  exact ⟨tor_kernel_boundary_construction_exact_left R M F N q hq,
    tor_kernel_boundary_construction_exact_right R M F N q hq⟩

end CategoryTheory

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.TorKernelBoundaryConstruction
import WeilConjectures.RingTheory.TorKernelBoundaryNaturalityOf

@[expose] public section
universe u
open CategoryTheory
open scoped TensorProduct
namespace CategoryTheory

/-- The constructed boundary vanishes on the image of Tor of the quotient map.

Source: Stacks Project, Algebra, Tags 00LZ and 00M0 (naturality of Tor boundaries).

Proof: Apply naturality of the constructed boundary to the square from the
identity presentation F -> F to the given presentation q : F -> N. The map
on middle modules is the identity, the map on quotient modules is q, and the
map ker(id_F) -> ker(q) is zero. Compatibility with the kernel inclusions
holds because every element of ker(id_F) is zero. Naturality gives
boundary_q(Tor(q,M)(x)) = (0 tensor 1)(boundary_id(x)) = 0.
(blueprint: lem-sc-p1-tor-kernel-boundary-construction-exact-left-range) -/
theorem tor_kernel_boundary_construction_exact_left_range
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    (F N : ModuleCat.{u} R) (q : F →ₗ[R] N) (hq : Function.Surjective q) :
    ∀ x, torKernelBoundary M F N q hq
      ((((Tor' (ModuleCat.{u} R) 1).map
        (ModuleCat.ofHom q)).app M).hom x) = 0 := by
  intro x
  have h := tor_kernel_boundary_naturality_of R M F F F N
    (LinearMap.id : F →ₗ[R] F) q Function.surjective_id hq
    LinearMap.id q (0 : LinearMap.ker (LinearMap.id : F →ₗ[R] F) →ₗ[R] LinearMap.ker q)
    (by simp) (by
      intro z
      have hz : (z : F) = 0 := z.property
      simp [hz]) x
  simpa using h

end CategoryTheory

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.RingTheory.TorKernelBoundaryConstructionExact
import WeilConjectures.RingTheory.TorKernelBoundaryNaturalityOf

@[expose] public section

universe u

open CategoryTheory
open scoped TensorProduct

namespace CategoryTheory

/-!
# The Tor boundary for kernels, natural in presentations

Source: Stacks Project, Algebra, Tag 00M0 and Section 00LY.
(blueprint: lem-sc-p1-tor-kernel-boundary-natural)
-/

/-- Choose the low-degree boundary simultaneously for all surjective presentations,
with exactness at Tor one and at the tensor of the kernel, and naturality in the
first variable. No projectivity or minimality of the presentation is assumed.

Source: Stacks Project, Algebra, Tag 00M0 and Section 00LY.

Proof: For each surjection q, use the short exact sequence with left term ker q,
its subtype inclusion, and q. Lift this sequence to a degreewise split short exact
sequence of free resolutions, and tensor with M. The homology connecting map,
followed by the augmentation identification H_0(ker q resolution tensor M) =
ker q tensor M, defines the boundary. The homology long exact sequence gives the
two exactness assertions. For a commuting square (a,b) and its induced kernel
map c, lift the entire morphism of short exact sequences to their resolutions.
Inductively lift the free right terms across the target surjections and correct the
middle lift in the left terms; repeat on the short exact sequences of kernels.
The split rows and projectivity of the free terms supply these compatible lifts.
On a cycle z, the connecting map lifts z to y in the middle resolution and writes
d y as the image of w in the kernel resolution. The images of y,w under the lifted
square are admissible choices for the image of z. Thus the connecting maps commute
with the square. Independence of lifts up to chain homotopy identifies the induced
map on first homology with Tor'(b,M); the augmentations identify the map on degree
zero homology with c tensor 1. These identifications give the displayed naturality.
(blueprint: lem-sc-p1-tor-kernel-boundary-natural) -/
theorem exists_tor_kernel_boundary_natural
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R) :
    ∃ δ : ∀ (F N : ModuleCat.{u} R) (q : F →ₗ[R] N),
        Function.Surjective q →
          (((Tor' (ModuleCat.{u} R) 1).obj N).obj M) →ₗ[R]
            (LinearMap.ker q ⊗[R] M),
      (∀ (F N : ModuleCat.{u} R) (q : F →ₗ[R] N) (hq : Function.Surjective q),
        Function.Exact (((Tor' (ModuleCat.{u} R) 1).map
          (ModuleCat.ofHom q)).app M).hom (δ F N q hq) ∧
        Function.Exact (δ F N q hq) ((LinearMap.ker q).subtype.rTensor M)) ∧
      (∀ (F N F' N' : ModuleCat.{u} R) (q : F →ₗ[R] N) (q' : F' →ₗ[R] N')
          (hq : Function.Surjective q) (hq' : Function.Surjective q')
          (a : F →ₗ[R] F') (b : N →ₗ[R] N')
          (c : LinearMap.ker q →ₗ[R] LinearMap.ker q'),
        q'.comp a = b.comp q →
        (∀ x : LinearMap.ker q, (c x : F') = a (x : F)) →
        ∀ t : (((Tor' (ModuleCat.{u} R) 1).obj N).obj M),
          δ F' N' q' hq' ((((Tor' (ModuleCat.{u} R) 1).map
            (ModuleCat.ofHom b)).app M).hom t) =
          c.rTensor M (δ F N q hq t)) := by
  refine ⟨torKernelBoundary M, ?_, tor_kernel_boundary_naturality_of R M⟩
  intro F N q hq
  exact tor_kernel_boundary_construction_exact R M F N q hq

end CategoryTheory

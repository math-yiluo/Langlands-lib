/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.TorKernelBoundaryConstruction
import WeilConjectures.RingTheory.TorKernelBoundaryHorseshoeComparison
import all WeilConjectures.AlgebraicGeometry.TorLongExactFirstVariable

/-!
# Exactness on the left of the constructed Tor boundary

The private resolution and degree-zero homology helpers are imported with `import all` from
`WeilConjectures.AlgebraicGeometry.TorLongExactFirstVariable`; the connecting-map
comparison is proved
in `WeilConjectures.RingTheory.TorKernelBoundaryHorseshoeComparison`.

Source: Stacks Project, Algebra, Tags 065P, 00M0 and 00LZ; Homology, Tag 0111.
-/

@[expose] public section
universe u
open CategoryTheory
open scoped TensorProduct
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- Kernel-to-range inclusion for the constructed Tor boundary.

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
(blueprint: lem-sc-p1-tor-kernel-boundary-construction-exact-left-kernel) -/
theorem tor_kernel_boundary_construction_exact_left_kernel
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    (F N : ModuleCat.{u} R) (q : F →ₗ[R] N) (hq : Function.Surjective q) :
    ∀ y, torKernelBoundary M F N q hq y = 0 →
      y ∈ Set.range (((Tor' (ModuleCat.{u} R) 1).map
        (ModuleCat.ofHom q)).app M).hom := by
  classical
  let i := (LinearMap.ker q).subtype
  have hi : Function.Injective i := Subtype.val_injective
  have hiq : Function.Exact i q := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact x.property
  obtain ⟨A, B, C, a, b, w, ha, hb, hs⟩ := resolutionSES i q hi hq hiq
  let T := (MonoidalCategory.tensoringRight (ModuleCat R)).obj M
  let S := (ShortComplex.mk a b w).map (T.mapHomologicalComplex (ComplexShape.down ℕ))
  have hS : S.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    exact ((hs n).some.map T).shortExact
  have hcompare := tor_kernel_boundary_horseshoe_comparison R M F N q hq
    A B C a b w ha hb hs hS
  let eB := B.isoLeftDerivedObj T 1
  let eC := C.isoLeftDerivedObj T 1
  let eA := homologyZeroIso A T
  have hnat : (((Tor' (ModuleCat R) 1).map (ModuleCat.ofHom q)).app M) ≫
      eC.hom = eB.hom ≫ HomologicalComplex.homologyMap S.g 1 :=
    B.isoLeftDerivedObj_hom_naturality (ModuleCat.ofHom q) C b hb T 1
  have hex : Function.Exact (HomologicalComplex.homologyMap S.g 1).hom
      (hS.δ 1 0 (by simp)).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₃ 1 0 (by simp))
  intro y hy
  have hz : (hS.δ 1 0 (by simp)).hom (eC.hom.hom y) = 0 := by
    apply (ModuleCat.mono_iff_injective eA.hom).mp inferInstance
    have hh := congrArg (fun f ↦ f.hom y) hcompare
    change eA.hom.hom ((hS.δ 1 0 (by simp)).hom (eC.hom.hom y)) = _ at hh
    change eA.hom.hom ((hS.δ 1 0 (by simp)).hom (eC.hom.hom y)) =
      -(torKernelBoundary M F N q hq y) at hh
    simpa only [hy, neg_zero, map_zero] using hh
  obtain ⟨x, hx⟩ := (hex (eC.hom.hom y)).mp hz
  refine ⟨eB.inv.hom x, ?_⟩
  apply (ModuleCat.mono_iff_injective eC.hom).mp inferInstance
  have hh := congrArg (fun f ↦ f.hom (eB.inv.hom x)) hnat
  change (eC.hom.hom ((((Tor' (ModuleCat R) 1).map
    (ModuleCat.ofHom q)).app M).hom (eB.inv.hom x))) = _ at hh
  rw [hh]
  have he : eB.hom.hom (eB.inv.hom x) = x :=
    congrArg (fun f ↦ f.hom x) eB.inv_hom_id
  change (HomologicalComplex.homologyMap S.g 1).hom
    (eB.hom.hom (eB.inv.hom x)) = eC.hom.hom y
  rw [he]
  exact hx

end CategoryTheory

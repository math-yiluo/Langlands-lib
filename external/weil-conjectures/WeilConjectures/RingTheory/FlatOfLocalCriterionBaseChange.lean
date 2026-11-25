/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import WeilConjectures.RingTheory.LocalizedBaseChangeQuotientFlat
import WeilConjectures.RingTheory.LocalizedBaseChangeIdealKernelSpan
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import WeilConjectures.Mathlib.RingTheory.Filtration

/-!
# Another variant of the local criterion of flatness

Source: Stacks Project, Algebra, Tag 00MO, with the ideal-tensor description of Tor
in Tag 00M6 (blueprint: lem-weil-pbc-flat-another-variant-local-criterion).
-/

@[expose] public section

universe u v w z t

open scoped TensorProduct

namespace Module

/-- The local criterion after a localization of base change, Stacks Project, Algebra,
Tag 00MO (blueprint: lem-weil-pbc-flat-another-variant-local-criterion).

The algebra maps are the four maps of the square, and the scalar towers express its
commutativity. The quotient is represented by `(R ⧸ I) ⊗[R] M`, canonically `M / IM`
via `TensorProduct.quotTensorEquivQuotSMul`. Tensor symmetry identifies `S' ⊗[S] M`
with the node's `M ⊗[S] S'`. The additive map `θ` is specified on all pure tensors;
these values uniquely determine the canonical map, so no choice of map is imposed.

Proof (Tag 00MO, with Tag 00M6):
1. Put `A = S ⊗[R] R'` and `N = R' ⊗[R] M`. Tensor cancellation
   (`lem-weil-pbc-module-tensor-cancel-base-change`) identifies `M'` with the localization
   of `N` at `W`. Images of a finite set of generators of `M` generate `M'` over `S'`.
2. Tensor quotient base change (`lem-weil-pbc-tensor-quotient-base-change`) identifies
   `R'/I'` with the base change of `R/I`. Flat module base change
   (`lem-weil-pbc-flat-module-base-change`) makes `(M/IM) ⊗[R/I] (R'/I')` flat.
   The quotient tensor relations (`lem-weil-pbc-tensor-over-quotient-ring`) identify
   this module with `N/I'N`.
3. The Tor surjections `lem-weil-pbc-tor-one-surjective-flat-middle` and
   `lem-weil-pbc-tor-one-surjective-change-rings`, together with
   `lem-weil-pbc-tor-ideal-kernel-naturality`, identify a surjection from the base
   change of the original multiplication kernel onto the multiplication kernel for `N`.
   The original kernel is annihilated by `I`, by `def-weil-pbc-tor-modules` and
   `lem-weil-pbc-tensor-over-quotient-ring`.
4. Localization is exact (`lem-weil-pbc-localization-module-exact`). Its compatibility
   with tensor products (`lem-weil-pbc-localization-tensor-over-base`) identifies the
   localized kernel with the multiplication kernel for `M'`. The surjection in step 3
   maps each generator to a scalar multiple of `θ(k)`, zero by the kernel hypothesis.
   Thus this localized kernel vanishes.
5. The same exactness and tensor compatibility make `M'/I'M'` flat over `R'/I'`.
   Locality implies `I'` is proper. Apply `lem-weil-pbc-flat-variant-local-criterion`
   to the finite `S'`-module `M'`, its flat quotient, and its zero multiplication kernel.
-/
theorem flat_of_local_criterion_baseChange
    {R : Type u} {S : Type v} {R' : Type w} {S' : Type z}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing R'] [IsLocalRing S']
    [IsNoetherianRing R] [IsNoetherianRing S]
    [IsNoetherianRing R'] [IsNoetherianRing S']
    [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap R R')]
    [IsLocalHom (algebraMap S S')] [IsLocalHom (algebraMap R' S')]
    (I : Ideal R) (hI : I ≠ ⊤)
    (M : Type t) [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] [Module.Finite S M]
    (hloc : ∃ (q : S ⊗[R] R' →+* S') (W : Submonoid (S ⊗[R] R')),
      (∀ (s : S) (r' : R'), q (s ⊗ₜ[R] r') =
        algebraMap S S' s * algebraMap R' S' r') ∧
      (letI := q.toAlgebra; IsLocalization W S'))
    (hquot : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M))
    (θ : I ⊗[R] M →+ (I.map (algebraMap R R')) ⊗[R'] (S' ⊗[S] M))
    (hθ : ∀ (a : I) (x : M), θ (a ⊗ₜ[R] x) =
      (⟨algebraMap R R' a, Ideal.mem_map_of_mem (algebraMap R R') a.property⟩ :
        I.map (algebraMap R R')) ⊗ₜ[R'] ((1 : S') ⊗ₜ[S] x))
    (hker : ∀ k : I ⊗[R] M,
      TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype) k = 0 → θ k = 0) :
    Module.Flat R' (S' ⊗[S] M) := by
  let J := I.map (algebraMap R R')
  let N := S' ⊗[S] M
  have hquot' : Module.Flat (R' ⧸ J) ((R' ⧸ J) ⊗[R'] N) :=
    flat_quotient_localized_baseChange I M hloc hquot
  have : Module.Flat (R' ⧸ J) (N ⧸ J • (⊤ : Submodule R' N)) :=
    Module.Flat.of_linearEquiv
      ((TensorProduct.quotTensorEquivQuotSMul N J).extendScalarsOfSurjective
        Ideal.Quotient.mk_surjective).symm
  have hspan : Submodule.span S'
      ((fun k : I ⊗[R] M ↦ TensorProduct.comm R' J N (θ k)) ''
        (LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)) :
          Set (I ⊗[R] M))) ≤ ⊥ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, hk, rfl⟩
    have hk' := hker k (LinearMap.mem_ker.mp hk)
    simp [hk']
  have hmul : Function.Injective
      (TensorProduct.lift ((LinearMap.lsmul R' N).comp J.subtype)) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    have hmem := mem_span_ideal_kernel_localized_baseChange I M hloc hquot θ hθ z hz
    have heq : TensorProduct.comm R' J N z = 0 := hspan hmem
    exact (TensorProduct.comm R' J N).injective (heq.trans (map_zero _).symm)
  have hinj : Function.Injective (J.subtype.lTensor N) := by
    intro x y hxy
    apply (TensorProduct.comm R' N J).injective
    apply hmul
    have hcomm :
        (TensorProduct.lift ((LinearMap.lsmul R' N).comp J.subtype)).comp
            (TensorProduct.comm R' N J).toLinearMap =
          (TensorProduct.rid R' N).toLinearMap.comp (J.subtype.lTensor N) := by
      ext n j
      simp
    change ((TensorProduct.lift ((LinearMap.lsmul R' N).comp J.subtype)).comp
      (TensorProduct.comm R' N J).toLinearMap) x =
        ((TensorProduct.lift ((LinearMap.lsmul R' N).comp J.subtype)).comp
          (TensorProduct.comm R' N J).toLinearMap) y
    rw [hcomm]
    exact congrArg (TensorProduct.rid R' N) hxy
  have hIS : J.map (algebraMap R' S') ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    exact (Ideal.map_mono ((Ideal.map_mono (IsLocalRing.le_maximalIdeal hI)).trans
      (IsLocalRing.map_maximalIdeal_le (algebraMap R R')))).trans
        (IsLocalRing.map_maximalIdeal_le (algebraMap R' S'))
  exact Module.Flat.of_flat_quotient_of_lTensor_injective (S := S') J hIS hinj

end Module

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.Topology.LocalAtTarget
import WeilConjectures.RingTheory.PolynomialQuotientDimensionAtPointHeightDifference

/-!
# Local fibre dimension under a comparison localization

Source: Stacks Project, Algebra, Tag 00SY, localization comparison; Tag 00P2.
(blueprint: lem-weil-pbc-syntomic-equation-count-comparison-dimension).
-/

set_option autoImplicit false

@[expose] public section
universe u v
namespace Algebra
private theorem dimAt_inducing_le {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {g : X → Y}
    (hg : Topology.IsInducing g) (x : X) :
    topologicalKrullDimAt x ≤ topologicalKrullDimAt (g x) := by
  refine le_iInf₂ fun U hx ↦ ?_
  let V : TopologicalSpace.Opens X := ⟨g ⁻¹' U, U.isOpen.preimage hg.continuous⟩
  exact (iInf₂_le V hx).trans
    ((hg.restrictPreimage (U : Set Y)).topologicalKrullDim_le)

private theorem dimAt_homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (e x) := by
  apply le_antisymm (dimAt_inducing_le e.isEmbedding.toIsInducing x)
  simpa using dimAt_inducing_le e.symm.isEmbedding.toIsInducing (e x)

private theorem dimAt_embedding_of_open_subset_range {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {g : X → Y}
    (hg : Topology.IsEmbedding g) (x : X) (W : Set Y) (hW : IsOpen W)
    (hx : g x ∈ W) (hsub : W ⊆ Set.range g) :
    topologicalKrullDimAt x = topologicalKrullDimAt (g x) := by
  have hsurj : Function.Surjective (W.restrictPreimage g) := by
    intro y
    obtain ⟨z, hz⟩ := hsub y.property
    exact ⟨⟨z, by change g z ∈ W; rw [hz]; exact y.property⟩, Subtype.ext hz⟩
  let e := (hg.restrictPreimage W).toHomeomorphOfSurjective hsurj
  have he := dimAt_homeomorph e (⟨x, hx⟩ : g ⁻¹' W)
  exact ((hW.preimage hg.continuous).topologicalKrullDimAt_eq hx).symm.trans
    (he.trans (hW.topologicalKrullDimAt_eq hx))

private theorem fibre_dim_base {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    (q : PrimeSpectrum T) (p : PrimeSpectrum R)
    (hp : q.comap (algebraMap R T) = p) :
    topologicalKrullDimAt
      (PrimeSpectrum.preimageEquivFiber R T (q.comap (algebraMap R T)) ⟨q, rfl⟩) =
    topologicalKrullDimAt (PrimeSpectrum.preimageEquivFiber R T p ⟨q, hp⟩) := by
  subst p
  rfl

private theorem comparison_fibre_dimension
    {R T S : Type*} [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S] (π : T →ₐ[R] S) (q : PrimeSpectrum S) (u : T)
    (hsurj : Function.Surjective π) (hu : π u ∉ q.asIdeal)
    (hbij : Function.Bijective
      (IsLocalization.Away.mapₐ (Localization.Away u) (Localization.Away (π u)) π u)) :
    topologicalKrullDimAt
      (PrimeSpectrum.preimageEquivFiber R T
        ((q.comap π.toRingHom).comap (algebraMap R T)) ⟨q.comap π.toRingHom, rfl⟩) =
    topologicalKrullDimAt
      (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S)) ⟨q, rfl⟩) := by
  let p := q.comap (algebraMap R S)
  let X := PrimeSpectrum.comap (algebraMap R T) ⁻¹' {p}
  let Y := PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}
  have hcomm (z : PrimeSpectrum S) :
      (z.comap π.toRingHom).comap (algebraMap R T) = z.comap (algebraMap R S) := by
    rw [← PrimeSpectrum.comap_comp_apply]
    congr 1
    exact π.comp_algebraMap
  let g : Y → X := fun z ↦ ⟨z.val.comap π.toRingHom, by
    change (z.val.comap π.toRingHom).comap (algebraMap R T) ∈ ({p} : Set (PrimeSpectrum R))
    rw [hcomm]
    exact z.property⟩
  have hg : Topology.IsEmbedding g := by
    apply Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal |>.mp
    exact (PrimeSpectrum.isEmbedding_comap_of_surjective S π.toRingHom hsurj).comp
      Topology.IsEmbedding.subtypeVal
  let W : Set X := {z | u ∉ z.val.asIdeal}
  have hW : IsOpen W :=
    (PrimeSpectrum.basicOpen u).isOpen.preimage continuous_subtype_val
  have hkill : ∀ a, π a = 0 → ∃ m, u ^ m * a = 0 :=
    (IsLocalization.Away.map_injective_iff (Localization.Away (π u)) π.toRingHom u).mp
      hbij.injective
  have hsub : W ⊆ Set.range g := by
    intro z hz
    have hker : RingHom.ker π.toRingHom ≤ z.val.asIdeal := by
      intro a ha
      obtain ⟨m, hm⟩ := hkill a ha
      have hmem : u ^ m * a ∈ z.val.asIdeal := hm ▸ z.val.asIdeal.zero_mem
      exact (z.val.isPrime.mul_mem_iff_mem_or_mem.mp hmem).resolve_left
        (fun h ↦ hz (z.val.isPrime.mem_of_pow_mem m h))
    have hr : z.val ∈ Set.range (PrimeSpectrum.comap π.toRingHom) := by
      rw [range_comap_of_surjective S π.toRingHom hsurj]
      exact hker
    obtain ⟨y, hy⟩ := hr
    have hyp : y ∈ Y := by
      change y.comap (algebraMap R S) ∈ ({p} : Set (PrimeSpectrum R))
      rw [← hcomm, hy]
      exact z.property
    exact ⟨⟨y, hyp⟩, Subtype.ext hy⟩
  have hdim := dimAt_embedding_of_open_subset_range hg (⟨q, rfl⟩ : Y) W hW hu hsub
  have he := (dimAt_homeomorph (PrimeSpectrum.preimageHomeomorphFiber R T p)
    (g ⟨q, rfl⟩)).symm.trans
    (hdim.symm.trans (dimAt_homeomorph (PrimeSpectrum.preimageHomeomorphFiber R S p)
      ⟨q, rfl⟩))
  change topologicalKrullDimAt
    (PrimeSpectrum.preimageEquivFiber R T p (g ⟨q, rfl⟩)) =
    topologicalKrullDimAt
    (PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩) at he
  exact (fibre_dim_base (q.comap π.toRingHom) p (hcomm q)).trans he

/-- Dimension calculation for a comparison quotient at the canonical fibre prime.
Source: Stacks Project, Algebra, Tags 00SY and 00P2.
(blueprint: lem-weil-pbc-syntomic-equation-count-comparison-dimension).
The localization comparison preserves local fibre dimension. The equation count must
already equal the codimension of the target fibre; an arbitrary list of c equations
need not have codimension c.
Proof: injectivity after localization kills every kernel element by a power of u.
Thus D(u) lies in the image of the closed spectrum embedding. Restrict to the base
fibre, obtaining a homeomorphism over an open neighbourhood of the chosen point.
Local dimension is invariant under this homeomorphism and under passage to opens. -/
theorem equationCount_comparison_dimension
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) {n c : ℕ} {f : Fin c → MvPolynomial (Fin n) R}
    (π : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) →ₐ[R] S)
    (u : MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
    (hsurj : Function.Surjective π) (hu : π u ∉ q.asIdeal)
    (hbij : Function.Bijective
      (IsLocalization.Away.mapₐ (Localization.Away u) (Localization.Away (π u)) π u))
    (hdim : topologicalKrullDimAt
      (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S)) ⟨q, rfl⟩) =
        (n - c : ℕ)) :
    topologicalKrullDimAt
      (PrimeSpectrum.preimageEquivFiber R
        (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
        ((q.comap π.toRingHom).comap
          (algebraMap R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))))
        ⟨q.comap π.toRingHom, rfl⟩) = (n - c : ℕ) := by
  exact (comparison_fibre_dimension π q u hsurj hu hbij).trans hdim
end Algebra

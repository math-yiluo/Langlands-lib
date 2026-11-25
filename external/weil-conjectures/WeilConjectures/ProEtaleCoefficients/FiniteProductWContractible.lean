/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProEtale.WContractible

/-! Finite products of w-contractible rings.
(blueprint: det-pe-hypercover-product-wcontractible) -/

@[expose] public section

set_option autoImplicit false

universe u

open Topology TopologicalSpace

section

variable {I : Type u} [Finite I] (D : I → Type u) [∀ i, CommRing (D i)]
  [∀ i, IsWContractibleRing (D i)]
omit [Finite I] [∀ i, IsWContractibleRing (D i)] in
private theorem sigma_closed (i : I) (p : PrimeSpectrum (D i)) :
    IsClosed ({Sigma.mk i p} : Set (Σ i, PrimeSpectrum (D i))) ↔ IsClosed ({p} : Set _) := by
  constructor
  · intro h
    convert h.preimage (continuous_sigmaMk (i := i)) using 1
    ext x
    exact ⟨fun h ↦ congrArg (Sigma.mk i) h,
      fun h ↦ (sigma_mk_injective (i := i) (β := fun i ↦ PrimeSpectrum (D i))) h⟩
  · intro h
    apply isClosed_sigma_iff.mpr
    intro j
    by_cases e : j = i
    · subst j
      convert h using 1
      ext x
      change (@Sigma.mk I (fun i ↦ PrimeSpectrum (D i)) i x) = Sigma.mk i p ↔ x = p
      exact ⟨fun h ↦ (sigma_mk_injective (i := i) (β := fun i ↦ PrimeSpectrum (D i))) h,
        fun h ↦ congrArg (Sigma.mk i) h⟩
    · have hempty : Sigma.mk j ⁻¹' ({Sigma.mk i p} : Set (Σ i, PrimeSpectrum (D i))) = ∅ := by
        ext q
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        intro h
        exact e (congrArg Sigma.fst h)
      rw [hempty]
      exact isClosed_empty
private theorem sigma_wlocal : WLocalSpace (Σ i, PrimeSpectrum (D i)) := by
  let e := PrimeSpectrum.sigmaToPiHomeo D
  have : SpectralSpace (Σ i, PrimeSpectrum (D i)) := e.symm.spectralSpace
  refine { eq_of_specializes := ?_, isClosed_closedPoints := ?_ }
  · classical
    let : TopologicalSpace I := ⊥
    have : DiscreteTopology I := ⟨rfl⟩
    rintro ⟨i, x⟩ ⟨j, c⟩ ⟨k, c'⟩ hc hc' h h'
    have hij : i = j := by
      have hs := h.map (continuous_sigma (fun _ ↦ continuous_const) :
        Continuous (Sigma.fst : (Σ i, PrimeSpectrum (D i)) → I))
      exact specializes_iff_eq.mp hs
    have hik : i = k := by
      have hs := h'.map (continuous_sigma (fun _ ↦ continuous_const) :
        Continuous (Sigma.fst : (Σ i, PrimeSpectrum (D i)) → I))
      exact specializes_iff_eq.mp hs
    subst j k
    have hc := (sigma_closed D i c).mp hc
    have hc' := (sigma_closed D i c').mp hc'
    have hi := (IsEmbedding.sigmaMk (i := i) (σ := fun i ↦ PrimeSpectrum (D i)))
    have h1 : x ⤳ c := hi.isInducing.specializes_iff.mp h
    have h2 : x ⤳ c' := hi.isInducing.specializes_iff.mp h'
    exact congrArg (Sigma.mk i) (WLocalSpace.eq_of_specializes hc hc' h1 h2)
  · apply isClosed_sigma_iff.mpr
    intro i
    convert (WLocalSpace.isClosed_closedPoints (X := PrimeSpectrum (D i))) using 1
    ext p
    exact sigma_closed D i p
private theorem pi_wlocal : IsWLocalRing (∀ i, D i) := by
  let e := PrimeSpectrum.sigmaToPiHomeo D
  let := sigma_wlocal D
  refine ⟨{ eq_of_specializes := ?_, isClosed_closedPoints := ?_ }⟩
  · intro x c c' hc hc' h h'
    apply e.symm.injective
    apply WLocalSpace.eq_of_specializes
      (c := e.symm c) (c' := e.symm c')
    · convert hc.preimage e.continuous using 1
      ext x
      exact e.eq_symm_apply
    · convert hc'.preimage e.continuous using 1
      ext x
      exact e.eq_symm_apply
    · exact h.map e.symm.continuous
    · exact h'.map e.symm.continuous
  · have heq : closedPoints (PrimeSpectrum (∀ i, D i)) =
        e.symm ⁻¹' closedPoints (Σ i, PrimeSpectrum (D i)) := by
      ext p
      simp only [Set.mem_preimage, mem_closedPoints_iff]
      constructor
      · intro h
        convert h.preimage e.continuous using 1
        ext x
        exact e.eq_symm_apply
      · intro h
        convert h.preimage e.symm.continuous using 1
        ext x
        exact ⟨fun h ↦ congrArg e.symm h, fun h ↦ e.symm.injective h⟩
    rw [heq]
    exact WLocalSpace.isClosed_closedPoints.preimage e.symm.continuous

private theorem pi_wstrict : IsWStrictlyLocalRing (∀ i, D i) := by
  have := pi_wlocal D
  refine ⟨fun m hm ↦ ?_⟩
  obtain ⟨⟨i, q⟩, hq⟩ := (PrimeSpectrum.sigmaToPi_bijective D).2 ⟨m, hm.isPrime⟩
  have heq : q.asIdeal.comap (Pi.evalRingHom D i) = m := congrArg PrimeSpectrum.asIdeal hq
  have hqmax : q.asIdeal.IsMaximal := by
    have hmax : (q.asIdeal.comap (Pi.evalRingHom D i)).IsMaximal := heq.symm ▸ hm
    have hx := Ideal.map_eq_top_or_isMaximal_of_surjective (Pi.evalRingHom D i)
      (RingHom.surjective _) hmax
    rw [Ideal.map_comap_of_surjective _ (RingHom.surjective _)] at hx
    exact hx.resolve_left q.isPrime.ne_top
  have := IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization q.asIdeal
  have hs : IsStrictlyHenselianLocalRing
      (Localization.AtPrime (q.asIdeal.comap (Pi.evalRingHom D i))) :=
    IsStrictlyHenselianLocalRing.of_ringEquiv
    (RingEquiv.ofBijective (Localization.AtPrime.mapPiEvalRingHom q.asIdeal)
      (Localization.AtPrime.mapPiEvalRingHom_bijective q.asIdeal)).symm
  cases heq
  exact hs

private noncomputable def sigmaClosedPointsEquiv :
    (Σ i, closedPoints (PrimeSpectrum (D i))) ≃
      closedPoints (Σ i, PrimeSpectrum (D i)) where
  toFun x := ⟨⟨x.1, x.2.1⟩, (sigma_closed D x.1 x.2.1).mpr x.2.2⟩
  invFun x := ⟨x.1.1, ⟨x.1.2, (sigma_closed D x.1.1 x.1.2).mp x.2⟩⟩
  left_inv := fun ⟨_, ⟨_, _⟩⟩ ↦ rfl
  right_inv := fun ⟨⟨_, _⟩, _⟩ ↦ rfl

private theorem pi_extremallyDisconnected :
    ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum (∀ i, D i))) := by
  let := sigma_wlocal D
  let := pi_wlocal D
  have (i : I) : ExtremallyDisconnected (closedPoints (PrimeSpectrum (D i))) := by
    have := IsWContractibleRing.extremallyDisconnected_connectedComponents (R := D i)
    exact extremallyDisconnected_of_homeo WLocalSpace.closedPointsHomeomorph.symm
  let e := sigmaClosedPointsEquiv D
  have hc : Continuous e := by
    apply continuous_sigma
    intro i
    apply Continuous.subtype_mk
    change Continuous (fun a : closedPoints (PrimeSpectrum (D i)) ↦
      @Sigma.mk I (fun i ↦ PrimeSpectrum (D i)) i a.val)
    exact continuous_sigmaMk.comp continuous_subtype_val
  have he : IsHomeomorph e := isHomeomorph_iff_continuous_bijective.mpr ⟨hc, e.bijective⟩
  have : ExtremallyDisconnected (closedPoints (Σ i, PrimeSpectrum (D i))) :=
    extremallyDisconnected_of_homeo (he.homeomorph e)
  have : ExtremallyDisconnected (ConnectedComponents (Σ i, PrimeSpectrum (D i))) :=
    extremallyDisconnected_of_homeo WLocalSpace.closedPointsHomeomorph
  let h := PrimeSpectrum.sigmaToPiHomeo D
  have hf : ∀ y, IsConnected (h ⁻¹' {y}) := by
    intro y
    have heq : h ⁻¹' {y} = {h.symm y} := by
      ext x
      exact h.eq_symm_apply.symm
    rw [heq]
    exact isConnected_singleton
  exact extremallyDisconnected_of_homeo
    (h.isQuotientMap.isCoinducing.connectedComponentsHomeomorph hf)

end

/-- Finite products, including the empty product, preserve w-contractibility.

Source: Stacks Project, Tag 09A1, finite-disjoint-union argument.
(blueprint: det-pe-hypercover-product-wcontractible)

Proof: Mathlib's `PrimeSpectrum.sigmaToPiHomeo` identifies the spectrum of the product
with the disjoint union of the factor spectra. Closed singletons are detected in each
summand, and the continuous index map to the discrete index type shows that every
specialization stays in its summand. Hence the disjoint union, and then the product
spectrum, is w-local. Every maximal ideal of the product comes from a maximal ideal
of a factor. Its localization is isomorphic to that factor localization by
`Localization.AtPrime.mapPiEvalRingHom_bijective`, so it is strictly henselian.
The closed-point space of the disjoint union is the disjoint union of the closed-point
spaces. In a w-local space the closed-point space is homeomorphic to the component
space. Thus extremal disconnectedness follows from the sigma-space instance and
homeomorphism invariance. The empty index type satisfies the same argument.
-/
theorem isWContractibleRing_pi_of_finite
    (I : Type u) [Finite I] (D : I → Type u) [∀ i, CommRing (D i)]
    [∀ i, IsWContractibleRing (D i)] :
    IsWContractibleRing (∀ i, D i) := by
  have := pi_wstrict D
  exact ⟨pi_extremallyDisconnected D⟩

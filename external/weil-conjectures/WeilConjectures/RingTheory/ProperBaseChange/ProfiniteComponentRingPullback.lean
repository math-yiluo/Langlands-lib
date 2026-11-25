/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import WeilConjectures.RingTheory.ProEtale.WLocal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.ProperBaseChange.ThmPeIndetaleRefinementPart1Supplement2
import WeilConjectures.RingTheory.ProEtale.WContractible

/-! # Profinite change of components of a w-local affine ring

Source: Stacks Project, Tags 097D, 096C, 096T, 0968, 096A, 0906 and 0A0D
(blueprint: lem-weil-pbc-profinite-component-ring-pullback).

The topological pullback is expressed as a subspace of `Spec C × T`. Both homeomorphisms
are tied to the structure map and to the projection to `T`; the localization condition
concerns the induced homomorphism itself.
-/

@[expose] public section

universe u

namespace Algebra

/-- Profinite base change of the component space of a w-local affine spectrum.
Source: Stacks, Tags 097D and 096C, with local-ring identification from 096T and the
principal-localization refinement of 0A0D
(blueprint: lem-weil-pbc-profinite-component-ring-pullback).

Proof in words:
1. The affine spectrum is qcqs and spectral (lem-weil-pbc-affine-scheme-qcqs and
   lem-weil-pbc-qcqs-scheme-spectral). Its components are separated by clopens
   (lem-weil-pbc-quasicompact-components-clopen-intersection). Their quotient is
   compact, Hausdorff and totally disconnected. The closed points map bijectively to
   it by w-locality; this continuous bijection is closed and hence a homeomorphism.
   Compactness uses lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact.
2. Take the actual ring of locally constant functions `T → C`. Its spectrum is
   `T × Spec C` by lem-weil-pbc-locally-constant-prime-spectrum, and the coefficient
   map is projection to `Spec C`.
3. The locus `u(t) = component(x)` is closed and is a union of components. Apply
   lem-weil-pbc-closed-component-spectrum-restriction to obtain a quotient ring `D`
   with this spectrum, preserving local rings. Constants give its `C`-algebra structure.
4. The fibres over `T` are exactly the nonempty connected components. The induced
   continuous bijection from the component quotient to `T` is closed by compactness,
   hence a homeomorphism. Its compatibility over the original quotient follows from
   the graph equation.
5. A point `(x,t)` of the closed graph is closed exactly when `x` is closed. Thus the
   closed points are the inverse image of the closed points downstairs. They form the
   graph of the continuous section selecting the unique closed point in each component,
   and map homeomorphically to `T`. Each component has exactly one of them, so `D` is w-local.
6. Evaluation at `t` and constants give inverse maps on the local rings of the locally
   constant-function ring and `C`: the clopen level set of a function at `t` has an
   idempotent characteristic function outside the relevant prime. That idempotent
   becomes one after localization, identifying the function with its constant value.
   Composing with the quotient's local-ring identification gives exactly the induced
   map `C_p → D_q` (def-weil-pbc-localization-at-prime).
7. Apply theorem-pro-etale-refinements-weakly-etale to the map identifying local rings with
   w-local target. This supplies the finite-products-of-principal-localizations
   presentation of definition-ind-etale-pro-etale-weakly, which is also ind-etale.
8. If `u` is surjective, lift the component of any point `x` to `t`; the graph point
   `(x,t)` lifts `x`. This includes the empty-spectrum case. -/
theorem exists_profinite_component_ring_pullback (C : Type u) [CommRing C] [IsWLocalRing C] :
    CompactSpace (ConnectedComponents (PrimeSpectrum C)) ∧
    T2Space (ConnectedComponents (PrimeSpectrum C)) ∧
    TotallyDisconnectedSpace (ConnectedComponents (PrimeSpectrum C)) ∧
    IsHomeomorph
      (fun x : closedPoints (PrimeSpectrum C) ↦ ConnectedComponents.mk x.val) ∧
    ∀ (T : Type u) [TopologicalSpace T] [CompactSpace T] [T2Space T]
      [TotallyDisconnectedSpace T] (u : C(T, ConnectedComponents (PrimeSpectrum C))),
      ∃ (D : Type u) (_ : CommRing D) (_ : Algebra C D)
        (e : PrimeSpectrum D ≃ₜ
          {z : PrimeSpectrum C × T // ConnectedComponents.mk z.1 = u z.2})
        (eπ : ConnectedComponents (PrimeSpectrum D) ≃ₜ T),
        (∀ q : PrimeSpectrum D, (e q).val.1 = PrimeSpectrum.comap (algebraMap C D) q) ∧
        (∀ q : PrimeSpectrum D, eπ (ConnectedComponents.mk q) = (e q).val.2) ∧
        (∀ p : ConnectedComponents (PrimeSpectrum D),
          u (eπ p) = (PrimeSpectrum.continuous_comap (algebraMap C D)).connectedComponentsMap p) ∧
        IsIndPrincipalZariski C D ∧ IndEtale C D ∧
        (∀ q : PrimeSpectrum D,
          Function.Bijective (Localization.localRingHom
            (q.asIdeal.comap (algebraMap C D)) q.asIdeal (algebraMap C D) rfl)) ∧
        IsWLocalRing D ∧
        closedPoints (PrimeSpectrum D) =
          PrimeSpectrum.comap (algebraMap C D) ⁻¹' closedPoints (PrimeSpectrum C) ∧
        IsHomeomorph (fun q : closedPoints (PrimeSpectrum D) ↦ (e q.val).val.2) ∧
        (Function.Surjective u → Function.Surjective (PrimeSpectrum.comap (algebraMap C D))) := by
  classical
  have hcompact : CompactSpace (ConnectedComponents (PrimeSpectrum C)) := inferInstance
  have ht2 : T2Space (ConnectedComponents (PrimeSpectrum C)) := inferInstance
  have htd : TotallyDisconnectedSpace (ConnectedComponents (PrimeSpectrum C)) := inferInstance
  have hclosed := WLocalSpace.isHomeomorph_connectedComponents_closedPoints
    (PrimeSpectrum C)
  refine ⟨hcompact, ht2, htd, ?_, ?_⟩
  · simpa [Function.comp_def] using hclosed
  · intro T _ _ _ _ u
    let D := WContractification.PullbackProfinite C T u
    let pb := WContractification.PullbackProfinite.isPullback C T u
    let e0 := WContractification.PullbackProfinite.fiberHomeo C T u
    have hswap :
        (Homeomorph.prodComm T (PrimeSpectrum C) ''
            {q : T × PrimeSpectrum C | u q.1 = ConnectedComponents.mk q.2}) =
          {z : PrimeSpectrum C × T | ConnectedComponents.mk z.1 = u z.2} := by
      ext z
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact hq.symm
      · intro hz
        exact ⟨(z.2, z.1), hz.symm, rfl⟩
    let eswap :
        {q : T × PrimeSpectrum C // u q.1 = ConnectedComponents.mk q.2} ≃ₜ
          {z : PrimeSpectrum C × T // ConnectedComponents.mk z.1 = u z.2} :=
      ((Homeomorph.prodComm T (PrimeSpectrum C)).image
        {q : T × PrimeSpectrum C | u q.1 = ConnectedComponents.mk q.2}).trans
        (Homeomorph.setCongr hswap)
    let e : PrimeSpectrum D ≃ₜ
        {z : PrimeSpectrum C × T // ConnectedComponents.mk z.1 = u z.2} := e0.trans eswap
    let hlift := ConnectedComponents.isHomeomorph_lift_of_isPullback pb
    let eπ : ConnectedComponents (PrimeSpectrum D) ≃ₜ T :=
      IsHomeomorph.homeomorph _ hlift
    let _ : IsWLocalRing D := by
      have hwl : WLocalSpace (PrimeSpectrum D) :=
        ConnectedComponents.wlocalSpace_of_isPullback pb
      exact ⟨hwl⟩
    have hlocal' : ∀ (q : Ideal D) [q.IsPrime], Function.Bijective
        (Localization.localRingHom (q.comap (algebraMap C D)) q
          (algebraMap C D) rfl) := by
      intro q
      exact (Algebra.IndZariski.bijectiveOnStalks C D).bijective_localRingHom q
    have hprincipal : IsIndPrincipalZariski C D :=
      Algebra.isIndPrincipalZariski_of_bijective_localRingHom C D hlocal'
    have hlocal : ∀ q : PrimeSpectrum D, Function.Bijective
        (Localization.localRingHom (q.asIdeal.comap (algebraMap C D)) q.asIdeal
          (algebraMap C D) rfl) := by
      intro q
      exact hlocal' q.asIdeal
    have hind : IndEtale C D := Algebra.IndEtale.of_indZariski C D
    have hclosedpts :=
      ConnectedComponents.preimage_closedPoints_eq_closedPoints_of_isPullback pb
    have hsurj : Function.Surjective u →
        Function.Surjective (PrimeSpectrum.comap (algebraMap C D)) := by
      intro hu
      simpa [D, WContractification.PullbackProfinite.projSpec] using
        WContractification.PullbackProfinite.projSpec_surjective C T u hu
    refine ⟨D, inferInstance, inferInstance, e, eπ, ?_, ?_, ?_, hprincipal, hind,
      hlocal, inferInstance, ?_, ?_, hsurj⟩
    · intro q
      change (eswap (e0 q)).val.1 = _
      change (e0 q).val.2 = _
      exact WContractification.PullbackProfinite.snd_fiberHomeo C T u q
    · intro q
      change (IsHomeomorph.homeomorph _ hlift) (ConnectedComponents.mk q) = _
      rw [IsHomeomorph.homeomorph_apply]
      exact Continuous.connectedComponentsLift_apply_coe _ q
    · intro p
      change u (eπ p) =
        (PrimeSpectrum.continuous_comap (algebraMap C D)).connectedComponentsMap p
      obtain ⟨q, rfl⟩ := p.exists_rep
      change u (eπ (ConnectedComponents.mk q)) = _
      rw [show eπ (ConnectedComponents.mk q) =
        WContractification.PullbackProfinite.projT C T u q by
          change (IsHomeomorph.homeomorph _ hlift) (ConnectedComponents.mk q) = _
          rw [IsHomeomorph.homeomorph_apply]
          exact Continuous.connectedComponentsLift_apply_coe _ q]
      change u (WContractification.PullbackProfinite.projT C T u q) =
        (PrimeSpectrum.continuous_comap (algebraMap C D)).connectedComponentsMap
          (ConnectedComponents.mk q)
      rw [Continuous.connectedComponentsMap_mk]
      rw [← WContractification.PullbackProfinite.fst_fiberHomeo C T u q]
      change u (e0 q).val.1 =
        ConnectedComponents.mk (WContractification.PullbackProfinite.projSpec C T u q)
      rw [← WContractification.PullbackProfinite.snd_fiberHomeo C T u q]
      exact (e0 q).property
    · simpa [D, WContractification.PullbackProfinite.projSpec] using hclosedpts.symm
    · have hcp := WLocalSpace.isHomeomorph_connectedComponents_closedPoints
        (PrimeSpectrum D)
      have hcomp := eπ.isHomeomorph.comp hcp
      have heq : (fun q : closedPoints (PrimeSpectrum D) ↦ (e q.val).val.2) =
          (fun q : closedPoints (PrimeSpectrum D) ↦ eπ (ConnectedComponents.mk q.val)) := by
        funext q
        change (eswap (e0 q.val)).val.2 = eπ (ConnectedComponents.mk q.val)
        change (e0 q.val).val.1 = eπ (ConnectedComponents.mk q.val)
        rw [show eπ (ConnectedComponents.mk q.val) =
          WContractification.PullbackProfinite.projT C T u q.val by
            change (IsHomeomorph.homeomorph _ hlift) (ConnectedComponents.mk q.val) = _
            rw [IsHomeomorph.homeomorph_apply]
            exact Continuous.connectedComponentsLift_apply_coe _ q.val]
        exact (WContractification.PullbackProfinite.fst_fiberHomeo C T u q.val).symm
      rw [heq]
      exact hcomp

end Algebra

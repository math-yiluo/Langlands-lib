/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProEtale.WLocal
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Topology.ExtremallyDisconnected
import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale

/-! # Faithfully flat weakly étale algebras over a w-contractible ring split

Source: blueprint, chap-The-pro-etale-site / theorem-enough-affine-weakly-contractible-objects,
node `lemma-w-contractible-affines-projective` (blueprint: lemma-w-contractible-affines-projective);
Stacks Project, Tag 0982.
-/

@[expose] public section

universe u v

namespace RingHom

private theorem wContractible_of_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsWContractibleRing R]
    (e : R ≃+* S) : IsWContractibleRing S := by
  have : IsWLocalRing S := IsWLocalRing.of_surjective (f := e.toRingHom) e.surjective
  have : IsWStrictlyLocalRing S := by
    refine ⟨fun m hm ↦ ?_⟩
    have : (m.comap e.toRingHom).IsMaximal :=
      (Ideal.isMaximal_comap_iff_of_bijective e.toRingHom e.bijective).mpr hm
    have := IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization
      (m.comap e.toRingHom)
    have hM : (m.comap e.toRingHom).primeCompl.map e.toMonoidHom = m.primeCompl := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
        change e (e.symm x) ∉ m
        rwa [e.apply_symm_apply]
    exact IsStrictlyHenselianLocalRing.of_ringEquiv
      (IsLocalization.ringEquivOfRingEquiv
        (Localization.AtPrime (m.comap e.toRingHom)) (Localization.AtPrime m) e hM)
  have := IsWContractibleRing.extremallyDisconnected_connectedComponents (R := R)
  let h := PrimeSpectrum.homeomorphOfRingEquiv e
  have hc : ∀ y, IsConnected (h ⁻¹' {y}) := by
    intro y
    have heq : h ⁻¹' {y} = {h.symm y} := by
      ext x
      change h x = y ↔ x = h.symm y
      exact ⟨fun hx ↦ h.injective (hx.trans (h.apply_symm_apply y).symm),
        fun hx ↦ hx ▸ h.apply_symm_apply y⟩
    rw [heq]
    exact isConnected_singleton
  exact ⟨extremallyDisconnected_of_homeo
    (h.isQuotientMap.isCoinducing.connectedComponentsHomeomorph hc)⟩

private theorem retraction_same_universe
    {R B : Type u} [CommRing R] [CommRing B] [IsWContractibleRing R]
    (f : R →+* B) (hfaithful : f.FaithfullyFlat) (hweak : f.WeaklyEtale) :
    ∃ r : B →+* R, r.comp f = RingHom.id R := by
  obtain ⟨E, _, g, _hg, hge, hcomp⟩ := RingHom.WeaklyEtale.exists_indEtale_comp hweak
  let : Algebra R E := (g.comp f).toAlgebra
  have : Algebra.IndEtale R E := (RingHom.IndEtale.algebraMap_iff R E).mp hcomp
  have : Module.FaithfullyFlat R E :=
    (RingHom.faithfullyFlat_algebraMap_iff).mp
      (RingHom.FaithfullyFlat.stableUnderComposition f g hfaithful hge)
  obtain ⟨s, hs⟩ := IsWContractibleRing.exists_retraction R E
  exact ⟨s.comp g, (RingHom.comp_assoc _ _ _).trans hs⟩

/-- A w-local ring `R` whose space of connected components of `Spec R` is extremally disconnected
and whose localizations at all maximal ideals are strictly henselian (that is, a w-contractible
ring, with the definition unpacked) splits every faithfully flat weakly étale ring map out of it.
Source: blueprint `lemma-w-contractible-affines-projective` (blueprint:
lemma-w-contractible-affines-projective); Stacks Project, Tag 0982, implication (3) to (1).

Proof: the hypotheses say exactly `IsWContractibleRing R`. By `WeaklyEtale.exists_indEtale_comp`
the weakly étale map `f : R → B` factors through a faithfully flat map `g : B → E` with
`g ∘ f` ind-étale; `E` is then faithfully flat over `R`, and `IsWContractibleRing.exists_retraction`
gives a retraction `s : E → R` of `g ∘ f`, so `s ∘ g` retracts `f`. The universes of `R` and `B`
are first equalised with `ULift`. -/
theorem exists_retraction_of_wlocal_geometric_criterion
    {R : Type u} [CommRing R] [IsWLocalRing R]
    [ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum R))]
    (hstrict : ∀ (m : Ideal R) [m.IsMaximal],
      IsStrictlyHenselianLocalRing (Localization.AtPrime m))
    {B : Type v} [CommRing B] (f : R →+* B)
    (hfaithful : f.FaithfullyFlat) (hweak : f.WeaklyEtale) :
    ∃ r : B →+* R, r.comp f = RingHom.id R := by
  have : IsWStrictlyLocalRing R :=
    { toIsWLocalRing := inferInstance
      isStrictlyHenselianLocalRing_localization := fun m _ ↦ hstrict m }
  have : IsWContractibleRing R :=
    { extremallyDisconnected_connectedComponents := inferInstance }
  let R' := ULift.{v} R
  let B' := ULift.{u} B
  let eR : R ≃+* R' := ULift.ringEquiv.symm
  let eB : B ≃+* B' := ULift.ringEquiv.symm
  have : IsWContractibleRing R' := wContractible_of_ringEquiv eR
  let f' : R' →+* B' := f.ulift
  have hff : f'.FaithfullyFlat := by
    refine RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr ⟨?_, ?_⟩
    · exact RingHom.Flat.ulift_iff.mpr hfaithful.flat
    · intro p
      obtain ⟨q, hq⟩ := RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hfaithful |>.2
        (PrimeSpectrum.comap eR.toRingHom p)
      refine ⟨PrimeSpectrum.comap eB.symm.toRingHom q, ?_⟩
      apply (PrimeSpectrum.isHomeomorph_comap_of_bijective
        (f := eR.toRingHom) eR.bijective).injective
      calc
        PrimeSpectrum.comap eR.toRingHom
            (PrimeSpectrum.comap f' (PrimeSpectrum.comap eB.symm.toRingHom q)) =
            PrimeSpectrum.comap f q := by
          rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
          rfl
        _ = PrimeSpectrum.comap eR.toRingHom p := hq
  have hw : f'.WeaklyEtale := by
    let : Algebra R B := f.toAlgebra
    let : Algebra R' B' := ULift.algebra' R B'
    have : Algebra.WeaklyEtale R B := hweak
    exact (Algebra.WeaklyEtale.ulift_iff).mpr this
  obtain ⟨s, hs⟩ := retraction_same_universe f' hff hw
  refine ⟨eR.symm.toRingHom.comp (s.comp eB.toRingHom), ?_⟩
  ext x
  exact congrArg ULift.down (RingHom.congr_fun hs (ULift.up x))

end RingHom

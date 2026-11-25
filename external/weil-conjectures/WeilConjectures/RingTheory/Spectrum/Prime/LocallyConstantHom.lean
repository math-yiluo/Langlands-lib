/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant

/-!

# Ring maps out of `LocallyConstant T R`

Let `T` be a profinite space and `R` a ring. A ring map `φ : LocallyConstant T R →+* B` induces
a continuous map `Spec B → T` (`LocallyConstant.specMap`), the first component of
`Spec B → Spec (LocallyConstant T R) ≃ₜ T × Spec R`. Conversely
`LocallyConstant.liftPrimeSpectrum` builds a ring map from a continuous map `Spec B → T`.
This file shows that the two constructions are inverse to each other
(`LocallyConstant.liftPrimeSpectrum_specMap`,
`LocallyConstant.specMap_liftPrimeSpectrum`), so that ring maps `LocallyConstant T R →+* B`
extending `ψ : R →+* B` are continuous maps `Spec B → T`, naturally in `T`
(`LocallyConstant.specMap_comp_comapRingHom`).

-/

@[expose] public section

open PrimeSpectrum

namespace LocallyConstant

variable {T : Type*} [TopologicalSpace T] {R : Type*} [CommRing R]

/-- On prime spectra, the precomposition with `g` is `(t, p) ↦ (g t, p)`. -/
lemma comap_comapRingHom_toPrimeSpectrum {T' : Type*} [TopologicalSpace T'] (g : C(T', T))
    (tp : T' × PrimeSpectrum R) :
    PrimeSpectrum.comap (comapRingHom (Z := R) g) (toPrimeSpectrum tp) =
      toPrimeSpectrum (g tp.1, tp.2) :=
  rfl

variable [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] {B : Type*} [CommRing B]

/-- The continuous map `Spec B → T` induced by a ring map `φ : LocallyConstant T R →+* B`. -/
noncomputable def specMap (φ : LocallyConstant T R →+* B) : C(PrimeSpectrum B, T) :=
  ⟨fun p ↦ (homeomorphPrimeSpectrum.symm (PrimeSpectrum.comap φ p)).1,
    continuous_fst.comp (homeomorphPrimeSpectrum.symm.continuous.comp (continuous_comap φ))⟩

lemma comap_eq_toPrimeSpectrum_specMap (φ : LocallyConstant T R →+* B) (p : PrimeSpectrum B) :
    PrimeSpectrum.comap φ p =
      toPrimeSpectrum (specMap φ p, PrimeSpectrum.comap (φ.comp (algebraMap R _)) p) := by
  have h := (homeomorphPrimeSpectrum (T := T) (R := R)).apply_symm_apply
    (PrimeSpectrum.comap φ p)
  rw [homeomorphPrimeSpectrum_apply, ← Prod.mk.eta (p := homeomorphPrimeSpectrum.symm _),
    homeomorphPrimeSpectrum_symm_snd] at h
  rw [PrimeSpectrum.comap_comp_apply]
  exact h.symm

/-- `specMap` of `liftPrimeSpectrum ψ σ` is `σ`. -/
@[simp]
lemma specMap_liftPrimeSpectrum (ψ : R →+* B) (σ : C(PrimeSpectrum B, T)) :
    specMap (liftPrimeSpectrum ψ σ) = σ := by
  ext p
  change (homeomorphPrimeSpectrum.symm _).1 = _
  rw [comap_liftPrimeSpectrum, ← homeomorphPrimeSpectrum_apply,
    Homeomorph.symm_apply_apply]

/-- Every ring map `φ : LocallyConstant T R →+* B` is `liftPrimeSpectrum` of its restriction
to the constants and of `specMap φ`. -/
lemma liftPrimeSpectrum_specMap (φ : LocallyConstant T R →+* B) :
    liftPrimeSpectrum (φ.comp (algebraMap R _)) (specMap φ) = φ := by
  ext f
  refine PrimeSpectrum.eq_of_forall_algebraMap_localization_eq fun p ↦ ?_
  rw [algebraMap_localization_liftPrimeSpectrum]
  set c := f (specMap φ p)
  have hU : IsClopen (⇑f ⁻¹' {c}) := f.isLocallyConstant.isClopen_fiber c
  set e := charFn R hU.compl
  have hfe : f - algebraMap R _ c = (f - algebraMap R _ c) * e := by
    ext t
    by_cases ht : t ∈ ⇑f ⁻¹' {c}
    · have : f t = c := ht
      simp only [coe_mul, coe_sub, Pi.mul_apply, Pi.sub_apply, algebraMap_apply_apply, this,
        sub_self, zero_mul]
    · simp [e, charFn_apply_of_mem hU.compl ht]
  have he : IsIdempotentElem (φ e) := by
    refine (?_ : IsIdempotentElem e).map φ
    change e * e = e
    ext t
    by_cases ht : t ∈ (⇑f ⁻¹' {c})ᶜ <;>
      simp [e, charFn_apply_of_mem, charFn_apply_of_notMem, ht]
  have hep : φ e ∈ p.asIdeal := by
    change e ∈ (PrimeSpectrum.comap φ p).asIdeal
    rw [comap_eq_toPrimeSpectrum_specMap, mem_toPrimeSpectrum_asIdeal,
      charFn_apply_of_notMem hU.compl (by simp [c])]
    exact zero_mem _
  symm
  rw [← sub_eq_zero, RingHom.comp_apply, ← map_sub, ← map_sub, hfe, map_mul, map_mul,
    he.algebraMap_localization_atPrime_of_mem hep, mul_zero]

/-- Ring maps out of `LocallyConstant T R` are determined by their restriction to the
constants and their `specMap`. -/
lemma ringHom_ext_of_specMap {φ φ' : LocallyConstant T R →+* B}
    (h₁ : φ.comp (algebraMap R _) = φ'.comp (algebraMap R _))
    (h₂ : specMap φ = specMap φ') :
    φ = φ' := by
  rw [← liftPrimeSpectrum_specMap φ, ← liftPrimeSpectrum_specMap φ', h₁, h₂]

/-- `specMap` is natural in `T`. -/
lemma specMap_comp_comapRingHom {T' : Type*} [TopologicalSpace T'] [CompactSpace T']
    [T2Space T'] [TotallyDisconnectedSpace T'] (g : C(T', T))
    (φ : LocallyConstant T' R →+* B) :
    specMap (φ.comp (comapRingHom g)) = g.comp (specMap φ) := by
  ext p
  change (homeomorphPrimeSpectrum.symm _).1 = g (specMap φ p)
  rw [PrimeSpectrum.comap_comp_apply, comap_eq_toPrimeSpectrum_specMap φ,
    comap_comapRingHom_toPrimeSpectrum,
    ← homeomorphPrimeSpectrum_apply, Homeomorph.symm_apply_apply]

end LocallyConstant

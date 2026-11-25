/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FlatLocalCompletionIso
import WeilConjectures.RingTheory.RegularLocalMaximal
import WeilConjectures.RingTheory.RegularPermanence
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Completion maps of G-rings are regular

Source: Stacks Project, More on Algebra, Lemma Tag 0AH2 (Matsumura, Theorem 79)
(blueprint: lem-weil-pbc-g-ring-completion-regular).
-/

@[expose] public section

universe u

namespace AdicCompletion

/-- The canonical map from a G-ring to its completion along any ideal is regular.
Source: Stacks Project, More on Algebra, Lemma Tag 0AH2
(blueprint: lem-weil-pbc-g-ring-completion-regular).

Proof:
1. The G-ring hypothesis gives Noetherianity (`theorem-finite-etale-covers-proper-henselian--2`).
The completion is
   Noetherian (`lem-weil-pbc-adic-completion-noetherian`), and its canonical map is flat
   (`lem-weil-pbc-noetherian-completion-flat`). The ideal is finitely generated.
2. By `lem-weil-pbc-regular-local-maximal`, it suffices to check regularity after localizing
   at every maximal ideal m' of the completion. Write m for its inverse image and B for
   the localization at m' (`def-weil-pbc-localization-at-prime`).
3. The projection to A/I is surjective with kernel I times the completion, and the
   completion is complete for that extended ideal (`lem-weil-pbc-adic-completion-mod-ideal`).
   That ideal lies in m' by `lem-weil-pbc-adic-complete-jacobson-radical`.
4. Every element b of the completion has a representative a in A modulo the projection's
   kernel. If b lies in m', then so does the image of a; since I lies in m, this proves
   m' is the extension of m. The same representatives give surjectivity on the residue
   fields of A_m and B; injectivity follows from locality.
5. The localized map φ from A_m to B is flat and local between Noetherian local rings
   (`lem-weil-pbc-flat-local-ring-maps`). Mapping the equality of step 4 into B shows
   that φ extends the maximal ideal of A_m to the maximal ideal of B
   (`def-weil-pbc-localization-at-prime`).
6. The localized map induces an isomorphism e between the maximal-ideal-adic completions
   of A_m and B, commuting with their canonical maps
   (`lem-weil-pbc-flat-local-completion-iso`, `def-weil-pbc-adic-completion`).
7. Compose B's completion map with e⁻¹ to obtain g : B → completion(A_m). The commuting
   square in step 6 proves g ∘ φ is exactly the completion map of A_m. It is regular
   by `theorem-finite-etale-covers-proper-henselian--2`.
8. The map g is flat: B's completion map is flat and e⁻¹ is bijective. It is also local,
   as both factors are local homomorphisms. Therefore it is faithfully flat, and its
   spectrum map is surjective (`lem-weil-pbc-local-completion-faithfully-flat`).
9. Descend regularity to A_m to B by `lem-weil-pbc-regular-permanence`. As m' was arbitrary,
   step 2 proves regularity of the original completion map. -/
theorem isRegular_of_isGRing (A : Type u) [CommRing A] (I : Ideal A) (hA : IsGRing A) :
    RingHom.IsRegular (algebraMap A (AdicCompletion I A)) := by
  have : IsNoetherianRing A := hA.1
  have : IsNoetherianRing (AdicCompletion I A) := isNoetherianRing I
  apply (RingHom.isRegular_iff_localRingHom_prime_and_maximal
    (algebraMap A (AdicCompletion I A))).2.mpr
  intro q hq
  let p := q.comap (algebraMap A (AdicCompletion I A))
  have hfg : I.FG := I.fg_of_isNoetherianRing
  have hcomplete := isAdicComplete_self I hfg
  have hIq : Ideal.map (algebraMap A (AdicCompletion I A)) I ≤ q :=
    (IsAdicComplete.le_jacobson_bot _).trans (sInf_le ⟨bot_le, hq⟩)
  have hker : RingHom.ker (evalOneₐ I).toRingHom ≤ q := by
    rw [ker_evalOneₐ_eq_map I hfg]
    exact hIq
  have happrox : ∀ b : AdicCompletion I A, ∃ a : A,
      b - algebraMap A (AdicCompletion I A) a ∈ RingHom.ker (evalOneₐ I).toRingHom := by
    intro b
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalOneₐ I b)
    refine ⟨a, ?_⟩
    change evalOneₐ I (b - algebraMap A (AdicCompletion I A) a) = 0
    rw [map_sub, show evalOneₐ I (algebraMap A (AdicCompletion I A) a) =
      Ideal.Quotient.mk I a from congrArg (fun f : A →+* A ⧸ I => f a)
        (evalOneₐ_comp_algebraMap_eq_mk I), ha, sub_self]
  have hmap : Ideal.map (algebraMap A (AdicCompletion I A)) p = q := by
    apply le_antisymm (Ideal.map_comap_le)
    intro b hb
    obtain ⟨a, ha⟩ := happrox b
    have hap : a ∈ p := by
      change algebraMap A (AdicCompletion I A) a ∈ q
      simpa only [sub_sub_cancel] using q.sub_mem hb (hker ha)
    have hd : b - algebraMap A (AdicCompletion I A) a ∈
        Ideal.map (algebraMap A (AdicCompletion I A)) I := by
      rwa [← ker_evalOneₐ_eq_map I hfg]
    have hIp : I ≤ p := Ideal.map_le_iff_le_comap.mp hIq
    simpa only [sub_add_cancel] using
      (Ideal.map (algebraMap A (AdicCompletion I A)) p).add_mem (Ideal.map_mono hIp hd)
        (Ideal.mem_map_of_mem _ hap)
  let R := Localization.AtPrime p
  let B := Localization.AtPrime q
  let φ : R →+* B :=
    Localization.localRingHom p q (algebraMap A (AdicCompletion I A)) rfl
  have hflat : φ.Flat := RingHom.Flat.localRingHom
    (RingHom.flat_algebraMap_iff.mpr inferInstance) q p rfl
  have hmax : Ideal.map φ (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal B := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      show φ.comp (algebraMap A R) =
        (algebraMap (AdicCompletion I A) B).comp (algebraMap A (AdicCompletion I A)) by
        apply RingHom.ext
        intro x
        exact Localization.localRingHom_to_map p q _ rfl x,
      ← Ideal.map_map, hmap, Localization.AtPrime.map_eq_maximalIdeal]
  have hres : Function.Bijective (Ideal.quotientMap (IsLocalRing.maximalIdeal B) φ
      (IsLocalRing.maximalIdeal_comap φ).ge) := by
    refine ⟨Ideal.quotientMap_injective' (IsLocalRing.maximalIdeal_comap φ).le, ?_⟩
    intro y
    obtain ⟨b, hb⟩ := q.algebraMap_residueField_surjective y
    obtain ⟨a, ha⟩ := happrox b
    refine ⟨Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (algebraMap A R a), ?_⟩
    rw [Ideal.quotientMap_mk, Localization.localRingHom_to_map, ← hb]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    change algebraMap (AdicCompletion I A) B
      (algebraMap A (AdicCompletion I A) a) - algebraMap (AdicCompletion I A) B b ∈ _
    rw [← map_sub]
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    apply Ideal.mem_map_of_mem
    simpa only [neg_sub] using q.neg_mem (hker ha)
  let Rhat := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let Bhat := AdicCompletion (IsLocalRing.maximalIdeal B) B
  obtain ⟨φhat, _, hbij, hcomm⟩ := RingHom.flat_local_completion_iso φ hflat hmax hres
  let e : Rhat ≃+* Bhat := RingEquiv.ofBijective φhat hbij
  let g : B →+* Rhat := e.symm.toRingHom.comp (algebraMap B Bhat)
  let : Algebra R B := φ.toAlgebra
  let : Algebra B Rhat := g.toAlgebra
  have htriangle : g.comp φ = algebraMap R Rhat := by
    rw [show g.comp φ = e.symm.toRingHom.comp
      ((algebraMap B Bhat).comp φ) from rfl, ← hcomm]
    apply RingHom.ext
    intro x
    exact e.symm_apply_apply _
  let : IsScalarTower R B Rhat := IsScalarTower.of_algebraMap_eq' htriangle.symm
  have hgflat : g.Flat := RingHom.Flat.comp
    (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat B Bhat))
    (RingHom.Flat.of_bijective e.symm.bijective)
  have : Module.Flat B Rhat := hgflat
  have : IsLocalHom e.symm.toRingHom := e.symm.surjective.isLocalHom
  have : IsLocalHom g := by
    dsimp only [g]
    infer_instance
  have : Module.FaithfullyFlat B Rhat := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact RingHom.isRegular_of_isRegular_comp (C := Rhat) (hA.2 p) hgflat
    PrimeSpectrum.comap_surjective_of_faithfullyFlat

end AdicCompletion

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.FlatCompletion
import WeilConjectures.RingTheory.RegularPermanence
import WeilConjectures.RingTheory.GRingMaximalIdealComparison
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# Checking the G-ring condition at maximal ideals

Source: Stacks Project, More on Algebra, Lemma 07PT
(blueprint: lem-weil-pbc-g-ring-maximal-ideal-criterion).
-/

@[expose] public section

universe w

/-- A Noetherian ring is a G-ring iff all maximal local completion maps are regular.
Source: Stacks Project, More on Algebra, Lemma 07PT
(blueprint: lem-weil-pbc-g-ring-maximal-ideal-criterion).

Proof plan, following the nine steps of the node:
1. A maximal ideal is prime, so the forward direction is immediate from
   theorem-finite-etale-covers-proper-henselian--2.
2. Conversely, for a prime p choose a maximal ideal m containing p. Put A = R_m and
   c : A → completion(A). Localization-at-prime and lem-weil-pbc-flat-local-ring-maps
   give Noetherian local rings A and R_p.
3. The lemmas lem-weil-pbc-adic-completion-noetherian,
   lem-weil-pbc-local-completion-local-ring and lem-weil-pbc-adic-completion-mod-ideal
   make completion(A) Noetherian complete local. By
   lem-weil-pbc-local-completion-faithfully-flat, choose a prime p' over pA.
4. Put B = completion(A)_(p'). By lem-weil-pbc-complete-local-g-ring applied to
   completion(A), its local completion map c_B : B → completion(B) is regular.
5. By lem-weil-pbc-flat-local-ring-maps, c induces a flat local map phi : R_p → B.
   Localization-at-prime identifies A_(pA) with R_p, and phi composed with A → R_p
   equals c followed by the localization lambda : completion(A) → B.
6. The map c is regular by hypothesis, lambda by lem-weil-pbc-localization-regular,
   and c_B by step 4. The targets B and completion(B) are Noetherian by step 5 and
   lem-weil-pbc-adic-completion-noetherian; their fibres are quotients of localizations,
   hence Noetherian. Twice apply lem-weil-pbc-regular-composition to obtain regularity
   of c_B composed with lambda composed with c.
7. By lem-weil-pbc-regular-through-localization, the resulting map
   c_B composed with phi : R_p → completion(B) is regular.
8. Complete phi to phi_hat : completion(R_p) → completion(B). This is flat by
   lem-weil-pbc-flat-completion, and local by lem-weil-pbc-local-completion-local-ring
   and compatibility with the completion maps. Thus
   lem-weil-pbc-flat-local-hom-faithfully-flat makes its map on spectra surjective.
9. Apply lem-weil-pbc-regular-permanence to R_p → completion(R_p) → completion(B):
   the composite is regular by step 7 and the second map is flat and surjective on
   spectra by step 8. The first map is therefore regular. Since p was arbitrary,
   theorem-finite-etale-covers-proper-henselian--2 gives IsGRing R. -/
theorem isGRing_iff_maximalIdeal
    (R : Type w) [CommRing R] [IsNoetherianRing R] :
    IsGRing R ↔
      ∀ (m : Ideal R) [m.IsMaximal],
        RingHom.IsRegular
          (algebraMap (Localization.AtPrime m)
            (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime m))
              (Localization.AtPrime m))) := by
  constructor
  · intro hR m
    exact hR.2 m
  · intro h
    refine ⟨inferInstance, ?_⟩
    intro p hp
    obtain ⟨B, hB, hBlocal, hBnoeth, φ, hflat, hlocal, hregular⟩ :=
      exists_flat_local_regular_completion_comparison R h p
    let A := Localization.AtPrime p
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let Bhat := AdicCompletion (IsLocalRing.maximalIdeal B) B
    obtain ⟨φhat, _, hcomm, hflatHat⟩ :=
      flat_adicCompletion_of_flat_local A B φ hflat hlocal
    have hlocalHat : IsLocalHom φhat := by
      apply ((IsLocalRing.local_hom_TFAE φhat).out 1 3).mpr
      rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hcomm]
      apply Ideal.map_le_iff_le_comap.mpr
      intro x hx
      exact map_nonunit (algebraMap B Bhat) (φ x) (hlocal x hx)
    let : Algebra Ahat Bhat := φhat.toAlgebra
    let : Algebra A Bhat := (φhat.comp (algebraMap A Ahat)).toAlgebra
    let : IsScalarTower A Ahat Bhat := IsScalarTower.of_algebraMap_eq' rfl
    have : IsLocalHom (algebraMap Ahat Bhat) := hlocalHat
    have : Module.Flat Ahat Bhat := hflatHat
    have : Module.FaithfullyFlat Ahat Bhat :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    apply RingHom.isRegular_of_isRegular_comp (C := Bhat)
    · change (φhat.comp (algebraMap A Ahat)).IsRegular
      rw [hcomm]
      exact hregular
    · exact hflatHat
    · exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Smooth.Flat
import WeilConjectures.RingTheory.RegularityRkGoesUp
import WeilConjectures.RingTheory.SmoothFibreRegularLocal
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Regularity ascends along smooth ring maps

Source: Stacks Project, Algebra, Lemma 07NF
(blueprint: lem-weil-pbc-regular-ring-smooth-ascent).
-/

@[expose] public section

universe u v

namespace Algebra

/-- A smooth algebra over a regular ring is regular.
Source: Stacks Project, Algebra, Lemma 07NF
(blueprint: lem-weil-pbc-regular-ring-smooth-ascent).

Proof:
1. R is Noetherian by def-weil-regular-scheme. Smoothness gives finite presentation and
   hence finite type by def-weil-pbc-smooth-ring-map, so S is Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian (Stacks 00FN).
2. The map R → S is flat by lem-weil-pbc-smooth-ring-map-flat (Stacks 00TA).
3. For each prime p of R, the residue-field fibre is smooth by base change (Stacks 00T4).
   Every prime localization of this fibre is regular local by
   lem-weil-pbc-smooth-fibre-regular-local (Stacks 00TT). Thus the fibres satisfy (R_k)
   for every nonnegative integer k.
4. R satisfies every (R_k) by regularity. Applying lem-weil-pbc-regularity-rk-goes-up
   (Stacks 033A) to the Noetherian rings R and S, the flat map, and these fibre properties
   shows that S satisfies every (R_k).
5. Each prime localization of S has finite dimension since it is Noetherian local.
   Choose k at least that dimension and apply (R_k) to see that it is regular local.
   Together with Noetherianity of S, this is regularity by def-weil-regular-scheme
   (Stacks 00OD).
-/
theorem isRegularRing_of_smooth
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Smooth R S] [IsRegularRing R] : IsRegularRing S := by
  have : IsNoetherianRing S := FiniteType.isNoetherianRing R S
  have hS (k : ℕ) : Ring.IsSerreR S k := by
    apply RingHom.regularity_rk_goes_up k
      (RingHom.flat_algebraMap_iff.mpr (Smooth.flat R S))
    · intro p hp
      obtain ⟨hsmooth, hregular⟩ :=
        smooth_fibre_regular_local (R := R) (S := S) ⟨p, hp⟩
      have : Smooth p.ResidueField (p.Fiber S) := hsmooth
      have : IsNoetherianRing (p.Fiber S) :=
        FiniteType.isNoetherianRing p.ResidueField (p.Fiber S)
      refine ⟨inferInstance, ?_⟩
      intro Q hQ _
      exact hregular ⟨Q, hQ⟩
    · intro p hp _
      infer_instance
  apply isRegularRing_iff.mpr
  intro q hq
  exact hS q.height.toNat q (le_of_eq
    (ENat.natCast_toNat q.height_ne_top_of_isPrime).symm)

end Algebra

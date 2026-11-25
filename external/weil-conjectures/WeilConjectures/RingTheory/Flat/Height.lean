/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Heights of primes along flat ring maps

Let `R → S` be a flat map of noetherian rings and `p` a prime of `R`. For a prime `Q` of the fibre
ring `p.Fiber S = κ(p) ⊗[R] S` with contraction `q` to `S`, we show `ht q = ht p + ht Q`
(Stacks, Tag 00ON, in the form used in the proof of Tag 0339).

## Main results

- `Ideal.height_comap_includeRight_eq_height_add`: `ht q = ht p + ht Q`.
-/

@[expose] public section

open IsLocalRing Algebra.TensorProduct

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The contraction of a prime `Q` of the fibre ring `p.Fiber S` to `S` lies over `p`. -/
lemma Fiber.comap_includeRight_liesOver (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber S))
    [Q.IsPrime] : (Q.comap (includeRight : S →ₐ[R] p.Fiber S)).LiesOver p := by
  infer_instance

/-- **Height formula at a prime of the fibre ring.** Let `R → S` be a flat map of noetherian rings,
`p` a prime of `R`, `Q` a prime of the fibre ring `p.Fiber S = κ(p) ⊗[R] S` and `q` its contraction
to `S`. Then `ht q = ht p + ht Q`. (blueprint:
`proposition-proper-direct-image-constructible-complexes`) -/
theorem height_comap_includeRight_eq_height_add [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Flat R S] (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber S)) [Q.IsPrime] :
    (Q.comap (includeRight : S →ₐ[R] p.Fiber S)).height = p.height + Q.height := by
  set q := Q.comap (includeRight : S →ₐ[R] p.Fiber S)
  have := Fiber.comap_includeRight_liesOver p Q
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have hloc : IsLocalHom (algebraMap Rp Sq) :=
    inferInstanceAs (IsLocalHom (Localization.localRingHom p q (algebraMap R S) _))
  have : (maximalIdeal Sq).LiesOver (maximalIdeal Rp) :=
    ⟨(((local_hom_TFAE (algebraMap Rp Sq)).out 1 5 rfl rfl).mp hloc).symm⟩
  have key := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal Rp)
    (maximalIdeal Sq)
  set I := (maximalIdeal Rp).map (algebraMap Rp Sq)
  have hI : I = p.map (algebraMap R Sq) := by
    change (maximalIdeal (Localization (p.primeCompl))).map (algebraMap Rp Sq) = _
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  have hIle : I ≤ maximalIdeal Sq := by
    exact ((local_hom_TFAE (algebraMap Rp Sq)).out 1 3 rfl rfl).mp hloc
  have : Nontrivial (Sq ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal Sq).ne_top hIle)
  have : IsLocalRing (Sq ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have h1 : ((maximalIdeal Sq).height : WithBot ℕ∞) = q.height := by
    rw [maximalIdeal_height_eq_ringKrullDim, IsLocalization.AtPrime.ringKrullDim_eq_height q]
  have h2 : ((maximalIdeal Rp).height : WithBot ℕ∞) = p.height := by
    rw [maximalIdeal_height_eq_ringKrullDim, IsLocalization.AtPrime.ringKrullDim_eq_height p]
  have h3 : (((maximalIdeal Sq).map (Ideal.Quotient.mk I)).height : WithBot ℕ∞) = Q.height := by
    rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective,
      maximalIdeal_height_eq_ringKrullDim, ← IsLocalization.AtPrime.ringKrullDim_eq_height Q
        (Localization.AtPrime Q),
      ringKrullDim_eq_of_ringEquiv (Fiber.localizationAlgEquivQuotient p Q).toRingEquiv, hI]
  have := congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) key
  simp only [WithBot.coe_add, h1, h2, h3] at this
  exact_mod_cast this

end Ideal

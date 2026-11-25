/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SerreConditions
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import WeilConjectures.RingTheory.RegularLocalOfFlatWithRegularClosedFiber

/-!
# Ascent of Serre regularity in codimension

Source: Stacks Project, Algebra, Lemma Tag 033A (lemma-Rk-goes-up)
(blueprint: lem-weil-pbc-regularity-rk-goes-up).

## Main statement

- `regularity_rk_goes_up`: property `(R_k)` ascends along a flat map with
  Noetherian fibres satisfying `(R_k)`.
-/

@[expose] public section

universe u v

namespace RingHom

/-- For a flat homomorphism of Noetherian rings, `(R_k)` ascends when every
fibre is Noetherian and satisfies `(R_k)`. Source: Stacks Project, Algebra,
Lemma Tag 033A (blueprint: lem-weil-pbc-regularity-rk-goes-up).

Proof:
1. Fix a prime `q` of `S` of height at most `k`, and put `p = φ⁻¹(q)`,
   where `φ = algebraMap R S`.
   The induced map `Rₚ → S_q` is a flat local map of Noetherian local rings
   (`lem-weil-pbc-flat-local-ring-maps`).
2. The flat dimension formula gives
   `dim S_q = dim Rₚ + dim (S_q / p S_q)`, so both summands are at most `k`
   (`lem-weil-pbc-flat-height-formula`).
3. The height bound and `(R_k)` for `R` imply that `Rₚ` is regular
   (`def-weil-pbc-serre-conditions-rk-sk`).
4. The fibre ring is Noetherian (`lem-weil-pbc-fibre-ring-noetherian`).
   The prime corresponding to `q` (`lem-weil-pbc-fibre-ring-primes-bijection`)
   has localization isomorphic to `S_q / p S_q`
   (`lem-weil-pbc-fibre-ring-local-ring-iso`, Stacks Remark 0H9M).
   Its height is at most `k` by step 2 and invariance of dimension under
   isomorphism. The fibre hypothesis therefore makes this quotient regular.
5. The maximal ideal of `Rₚ` is `p Rₚ`
   (`def-weil-pbc-localization-at-prime`); its extension to `S_q` is `p S_q`,
   since denominators outside `p` map to units. Thus this quotient is the
   closed fibre of `Rₚ → S_q`.
6. Regularity of the base and closed fibre implies regularity of `S_q`
   (`lem-weil-pbc-flat-over-regular-with-regular-fibre`, Stacks Tag 031E).
   Since `q` was arbitrary, `S` satisfies `(R_k)`.

The algebra structure on `S` is the instance `[Algebra R S]`, and the ring map
of the source is `algebraMap R S`; the fibre rings `p.Fiber S` are formed with it.
-/
theorem regularity_rk_goes_up {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S] (k : ℕ)
    (hflat : (algebraMap R S).Flat)
    (hfibres : ∀ (p : Ideal R) [p.IsPrime],
      ∃ (_ : IsNoetherianRing (p.Fiber S)), Ring.IsSerreR (p.Fiber S) k)
    (hR : Ring.IsSerreR R k) : Ring.IsSerreR S k := by
  classical
  intro q hq hheight
  let p := q.comap (algebraMap R S)
  have hp : p.IsPrime := Ideal.comap_isPrime _ q
  have : Module.Flat R S := flat_algebraMap_iff.mp hflat
  have : q.LiesOver p := ⟨rfl⟩
  have hpheight : p.height ≤ (k : ℕ∞) := by
    have hdim := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p q
    exact (hdim ▸ le_self_add).trans hheight
  have : IsRegularLocalRing (Localization.AtPrime p) := hR p hpheight
  obtain ⟨hnoeth, hfibre⟩ := hfibres p
  let := hnoeth
  obtain ⟨Q, hQ⟩ : ∃ Q : PrimeSpectrum (p.Fiber S),
      Q.asIdeal.comap Algebra.TensorProduct.includeRight = q := by
    let x : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {⟨p, hp⟩} :=
      ⟨⟨q, hq⟩, rfl⟩
    refine ⟨PrimeSpectrum.preimageEquivFiber R S ⟨p, hp⟩ x, ?_⟩
    exact congrArg (fun x ↦ x.1.asIdeal)
      ((PrimeSpectrum.preimageEquivFiber R S ⟨p, hp⟩).left_inv x)
  let f := Localization.localRingHom p q (algebraMap R S) rfl
  let J := (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map f
  have hJ : J = (p.map (algebraMap R S)).map
      (algebraMap S (Localization.AtPrime q)) := by
    dsimp only [J]
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p, Ideal.map_map, Ideal.map_map]
    apply congrArg (fun g : R →+* Localization.AtPrime q ↦ p.map g)
    ext x
    exact Localization.localRingHom_to_map p q (algebraMap R S) rfl x
  have transport (r t : Ideal S) [r.IsPrime] [t.IsPrime] (h : r = t) :
      (Localization.AtPrime r ⧸ (p.map (algebraMap R S)).map
        (algebraMap S (Localization.AtPrime r))) ≃+*
      (Localization.AtPrime t ⧸ (p.map (algebraMap R S)).map
        (algebraMap S (Localization.AtPrime t))) := by
    subst t
    exact RingEquiv.refl _
  have e : Localization.AtPrime Q.asIdeal ≃+* (Localization.AtPrime q ⧸ J) :=
    (Ideal.Fiber.algEquivAux₂ p Q.asIdeal).toRingEquiv |>.trans
      ((transport _ _ hQ).trans (Ideal.quotientEquivAlgOfEq S hJ.symm).toRingEquiv)
  have hQheight : Q.asIdeal.height ≤ (k : ℕ∞) := by
    have hd := ringKrullDim_quotient_le J
    rw [← ringKrullDim_eq_of_ringEquiv e,
      IsLocalization.AtPrime.ringKrullDim_eq_height Q.asIdeal,
      IsLocalization.AtPrime.ringKrullDim_eq_height q] at hd
    exact (WithBot.coe_le_coe.mp hd).trans hheight
  have : IsRegularLocalRing (Localization.AtPrime Q.asIdeal) := hfibre Q.asIdeal hQheight
  have hclosed : IsRegularLocalRing (Localization.AtPrime q ⧸ J) :=
    IsRegularLocalRing.of_ringEquiv e
  exact IsRegularLocalRing.of_flat_of_regular_closedFiber f
    (hflat.localRingHom q p rfl) hclosed

end RingHom

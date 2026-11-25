/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import WeilConjectures.RingTheory.RegularLocalOfFlatWithRegularClosedFiber

/-!
# Regularity ascends along regular maps

Source: Stacks Project, Algebra, Lemma 031E, and More on Algebra, proof of Lemma 07QI.
-/

@[expose] public section

universe u v

namespace RingHom

/-- A flat map with regular fibres from a regular ring to a Noetherian ring has
regular target. Source: Stacks Project, Algebra, Lemma 031E, applied at each
prime, as in More on Algebra, proof of Lemma 07QI
(blueprint: lem-weil-pbc-regular-map-ascent).

Proof: At a prime q of S put p = q ∩ R. Regularity of R makes R_p regular local.
The closed fibre of R_p → S_q is a prime localization of the fibre at p, hence
regular local. The local map is flat. Lemma 031E makes S_q regular local.
Noetherianity of S and this assertion for every q give regularity of S.
The zero target has no primes, so the argument also covers the zero ring. -/
theorem isRegularRing_of_flat_of_regular_fibers
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsRegularRing R] [IsNoetherianRing S]
    (hflat : (algebraMap R S).Flat)
    (hfibres : ∀ (p : Ideal R) [p.IsPrime], IsRegularRing (p.Fiber S)) :
    IsRegularRing S := by
  rw [isRegularRing_iff]
  intro q hq
  let p := q.comap (algebraMap R S)
  have hp : p.IsPrime := Ideal.comap_isPrime _ q
  have : Module.Flat R S := flat_algebraMap_iff.mp hflat
  have : q.LiesOver p := ⟨rfl⟩
  have : IsRegularRing (p.Fiber S) := hfibres p
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
  have transport (r t : Ideal S) [r.IsPrime] [t.IsPrime] (hrt : r = t) :
      (Localization.AtPrime r ⧸ (p.map (algebraMap R S)).map
        (algebraMap S (Localization.AtPrime r))) ≃+*
      (Localization.AtPrime t ⧸ (p.map (algebraMap R S)).map
        (algebraMap S (Localization.AtPrime t))) := by
    subst t
    exact RingEquiv.refl _
  have e : Localization.AtPrime Q.asIdeal ≃+* (Localization.AtPrime q ⧸ J) :=
    (Ideal.Fiber.algEquivAux₂ p Q.asIdeal).toRingEquiv |>.trans
      ((transport _ _ hQ).trans (Ideal.quotientEquivAlgOfEq S hJ.symm).toRingEquiv)
  have hclosed : IsRegularLocalRing (Localization.AtPrime q ⧸ J) :=
    IsRegularLocalRing.of_ringEquiv e
  exact IsRegularLocalRing.of_flat_of_regular_closedFiber f
    (hflat.localRingHom q p rfl) hclosed

end RingHom

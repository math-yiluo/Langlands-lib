/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Height formula at a prime of a fibre ring

Source: Stacks Project, Algebra, Tags 0339, 0337, 00ON and Remark 0H9M.
(blueprint: proposition-proper-direct-image-constructible-complexes).
-/

@[expose] public section

universe u v

namespace RingHom

/-- Height splits into a base term and a fibre term for a flat map.
Source: Stacks Project, Algebra, proof of Tag 0339, Tag 00ON and Remark 00E6.
(blueprint: proposition-proper-direct-image-constructible-complexes).

Proof: Localize at p and q = Q.comap includeRight. The induced flat local
map R_p -> S_q gives a going-down algebra. Apply the height formula of Tag 00ON
to the maximal ideals of these two Noetherian local rings. Their heights equal
their Krull dimensions, hence p.height and q.height. The image of the maximal
ideal of R_p is p S_q, since the denominators outside p are units. The image
of the maximal ideal of S_q in its quotient is the quotient's maximal ideal,
whose height equals its dimension. Remark 0H9M identifies this closed fibre
with (p.Fiber S)_Q; the isomorphism preserves Krull dimension, which equals
Q.height. Substitute these equalities into the height formula. -/
theorem height_eq_add_of_flat_fiber {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra R S] (hflat : (algebraMap R S).Flat)
    (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber S)) [Q.IsPrime] :
    (Q.comap Algebra.TensorProduct.includeRight.toRingHom).height = p.height + Q.height := by
  let : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
  let q : Ideal S := Q.comap Algebra.TensorProduct.includeRight.toRingHom
  have : q.IsPrime := Ideal.IsPrime.comap _
  have : q.LiesOver p := Ideal.LiesOver.of_eq_comap p
    Algebra.TensorProduct.includeRight rfl
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  have hf : (algebraMap Rp Sq).Flat := hflat.localRingHom q p (q.over_def p)
  have : Module.Flat Rp Sq := RingHom.flat_algebraMap_iff.mp hf
  let I : Ideal Sq := (IsLocalRing.maximalIdeal Rp).map (algebraMap Rp Sq)
  have hI : I ≠ ⊤ := (IsLocalRing.map_maximalIdeal_lt_top (algebraMap Rp Sq)).ne
  have : Fact (I ≠ ⊤) := ⟨hI⟩
  have : Nontrivial (Sq ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing (Sq ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hheight := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (IsLocalRing.maximalIdeal Rp) (IsLocalRing.maximalIdeal Sq)
  have hmap := IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hIeq : I = p.map (algebraMap R Sq) := by
    dsimp [I]
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map]
    congr 1
    exact (IsScalarTower.algebraMap_eq R Rp Sq).symm
  let e := (Ideal.Fiber.algEquivAux₂ p Q).toRingEquiv
  have hquot : (p.map (algebraMap R S)).map (algebraMap S Sq) =
      p.map (algebraMap R Sq) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S Sq]
  let e' : Localization.AtPrime Q ≃+* (Sq ⧸ p.map (algebraMap R Sq)) :=
    e.trans (Ideal.quotientEquivAlgOfEq R hquot).toRingEquiv
  have hdim : ringKrullDim (Sq ⧸ I) = Q.height := by
    have hi := (Ideal.quotientEquivAlgOfEq R hIeq).toRingEquiv.ringKrullDim
    exact hi.trans (e'.ringKrullDim.symm.trans
      (IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q)))
  rw [hmap] at hheight
  have hheight' := congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hheight
  simp only [WithBot.coe_add] at hheight'
  rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdim,
    IsLocalization.AtPrime.ringKrullDim_eq_height q Sq,
    IsLocalization.AtPrime.ringKrullDim_eq_height p Rp] at hheight'
  exact WithBot.coe_eq_coe.mp hheight'


end RingHom

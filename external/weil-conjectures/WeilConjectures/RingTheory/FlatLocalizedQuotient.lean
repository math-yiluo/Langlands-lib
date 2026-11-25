/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Localization

/-! # Flatness of localized quotient maps

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FE (lemma-resolve-special),
final paragraph; quotient base change and localization.
(blueprint: lem-weil-pbc-flat-localized-quotient).
-/

@[expose] public section

universe u v

namespace RingHom

/-- Flatness of a local map descends to the corresponding localizations of quotient rings.

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FE (lemma-resolve-special),
final paragraph, the flat powered-parameter quotient map.
(blueprint: lem-weil-pbc-flat-localized-quotient).

Proof: Put q equal to the inverse image of q₀ in S, and p equal to its inverse image
in R. The composite R → R_p → S_q is flat, since localization and the second map
are flat. Quotient base change therefore makes S_q/JS_q flat over R/J.
Localization commutes with quotient, identifying this quotient with (S/JS)_{q₀}
as an R/J-algebra. Since every element outside p₀ is inverted in this target,
flatness over R/J is equivalent to flatness over (R/J)_{p₀}. This also covers
J=0 and zero-dimensional local rings; the existence of q₀ excludes the unit ideal. -/
theorem flat_localized_quotient_of_flat_localRingHom
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (J : Ideal R) (q₀ : PrimeSpectrum (S ⧸ J.map (algebraMap R S)))
    (hflat : (Localization.localRingHom
      ((q₀.asIdeal.comap (Ideal.Quotient.mk (J.map (algebraMap R S)))).under R)
      (q₀.asIdeal.comap (Ideal.Quotient.mk (J.map (algebraMap R S))))
      (algebraMap R S) rfl).Flat) :
    letI := Localization.AtPrime.algebraOfLiesOver
      (q₀.asIdeal.under (R ⧸ J)) q₀.asIdeal
    RingHom.Flat (algebraMap (Localization.AtPrime (q₀.asIdeal.under (R ⧸ J)))
      (Localization.AtPrime q₀.asIdeal)) := by
  let q := q₀.asIdeal.comap (Ideal.Quotient.mk (J.map (algebraMap R S)))
  let p := q.under R
  let Sq := Localization.AtPrime q
  let Rp := Localization.AtPrime p
  let := Localization.AtPrime.algebraOfLiesOver p q
  have hflocal : (algebraMap Rp Sq).Flat := hflat
  have hfR : (algebraMap R Sq).Flat := by
    rw [IsScalarTower.algebraMap_eq R Rp Sq]
    exact (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat Rp p.primeCompl)).comp
      hflocal
  let : Module.Flat R Sq := RingHom.flat_algebraMap_iff.mp hfR
  let K := J.map (algebraMap R S)
  let T := Sq ⧸ K.map (algebraMap S Sq)
  have hmap : K.map (algebraMap S Sq) = J.map (algebraMap R Sq) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S Sq]
  let : Algebra (R ⧸ J) T := Ideal.Quotient.algebraQuotientOfLEComap
    (by rw [hmap]; exact Ideal.le_comap_map)
  have : IsScalarTower R (R ⧸ J) T := IsScalarTower.of_algebraMap_eq' (by
    ext r
    rfl)
  let eT := Algebra.TensorProduct.quotIdealMapEquivQuotTensor Sq J
  let eJ := Ideal.quotientEquivAlgOfEq R hmap
  let eJR := eJ.toLinearEquiv.extendScalarsOfSurjective
    (Ideal.Quotient.mk_surjective (I := J))
  have hT : Module.Flat (R ⧸ J) T :=
    Module.Flat.of_linearEquiv (eJR.trans eT.toLinearEquiv)
  have hlocal : IsLocalization q₀.asIdeal.primeCompl T := by
    have ht : IsLocalization
        (Algebra.algebraMapSubmonoid (S ⧸ K) q.primeCompl) T := inferInstance
    have hc : Algebra.algebraMapSubmonoid (S ⧸ K) q.primeCompl =
        q₀.asIdeal.primeCompl :=
      Ideal.map_primeCompl_comap_of_surjective _ Ideal.Quotient.mk_surjective _
    rw [hc] at ht
    exact ht
  let e : T ≃ₐ[S ⧸ K] Localization.AtPrime q₀.asIdeal :=
    IsLocalization.algEquiv q₀.asIdeal.primeCompl _ _
  have : IsScalarTower (R ⧸ J) (S ⧸ K) T := IsScalarTower.of_algebraMap_eq' (by
    ext r
    rfl)
  let eR : T ≃ₐ[R ⧸ J] Localization.AtPrime q₀.asIdeal :=
    e.restrictScalars (R ⧸ J)
  have hL : Module.Flat (R ⧸ J) (Localization.AtPrime q₀.asIdeal) :=
    Module.Flat.of_linearEquiv eR.toLinearEquiv.symm
  let := Localization.AtPrime.algebraOfLiesOver
    (q₀.asIdeal.under (R ⧸ J)) q₀.asIdeal
  exact RingHom.flat_algebraMap_iff.mpr
    ((Module.flat_iff_of_isLocalization
      (Localization.AtPrime (q₀.asIdeal.under (R ⧸ J)))
      (q₀.asIdeal.under (R ⧸ J)).primeCompl
      (Localization.AtPrime q₀.asIdeal)).mpr hL)

end RingHom

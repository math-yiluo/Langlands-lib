/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import WeilConjectures.RingTheory.CohenRing
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import WeilConjectures.RingTheory.CohenPowerSeriesPresentation
import WeilConjectures.RingTheory.CohenPowerSeriesParameterExtension
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.Algebra.Ring.ULift
import Mathlib.Algebra.CharP.Algebra
import WeilConjectures.RingTheory.FlatOverRegular
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence

/-!
# Compatible Cohen presentations of complete local homomorphisms

Source: Stacks Project, Lemma 07NN and the proof of Proposition 07NQ
(blueprint: lem-weil-pbc-complete-local-map-cohen-presentation).
-/

@[expose] public section

universe u v

namespace RingHom

private theorem flat_and_regular_fibre_of_parameters
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsRegularLocalRing R] [IsRegularLocalRing S]
    (f : R →+* S) [IsLocalHom f] (t : List R) (z : List S)
    (ht : IsLocalRing.IsRegularSystemOfParameters t)
    (hz : IsLocalRing.IsRegularSystemOfParameters (t.map f ++ z)) :
    f.Flat ∧ IsRegularLocalRing (S ⧸ (IsLocalRing.maximalIdeal R).map f) := by
  have hs := IsRegularLocalRing.isRegular_and_quotients_of_generators
    S (t.map f ++ z).length hz.2.symm (t.map f ++ z) hz
  have hweak : RingTheory.Sequence.IsWeaklyRegular S (t.map f) :=
    ((RingTheory.Sequence.isWeaklyRegular_append_iff S (t.map f) z).mp
      hs.1.toIsWeaklyRegular).1
  have hreg : RingTheory.Sequence.IsRegular S (t.map f) := by
    apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal ?_).mpr hweak
    intro x hx
    exact hz.1 ▸ Ideal.subset_span (List.mem_append_left z hx)
  have hflat := flat_of_regular_parameters f t.length t ht.2.symm rfl ht.1 hreg
  have hquot := (hs.2.1 (t.map f).length (by simp)).1
  rw [List.take_left] at hquot
  have hideal : Ideal.ofList (t.map f) = (IsLocalRing.maximalIdeal R).map f := by
    rw [← ht.1]
    exact (Ideal.map_ofList f t).symm
  rw [hideal] at hquot
  exact ⟨hflat, hquot⟩

/-- A complete local homomorphism admits compatible power-series presentations with a flat
map carrying parameters into parameters and regular closed fibre. Source: Stacks, Lemma 07NN;
the first parameter in positive residue characteristic is chosen as in Proposition 07NQ
(blueprint: lem-weil-pbc-complete-local-map-cohen-presentation).

Proof:
1. Use `lem-weil-pbc-cohen-power-series-presentation` to present A and B by power-series
rings R and S₀ over fields or Cohen rings. By
`lem-weil-pbc-power-series-field-cohen-regular-complete` they are regular, complete and local;
the surjection S₀ → B has kernel J contained in the maximal ideal.
2. Lift fq to φ : R → S₀ using `lem-weil-pbc-field-cohen-power-series-formally-smooth` and
`lem-weil-pbc-fs-adic-lift-into-complete`. The kernel J is closed, since completeness of B
makes the intersection of its maximal-ideal powers zero. The lift maps maximal ideals into
maximal ideals.
3. Adjoin variables Y to S₀ and let S = Λ_B[[Y,Z]]. Set v(Y) = 0 and set
u(X_i) = φ(X_i) + Y_i, using `lem-weil-pbc-power-series-adic-evaluation`.
The uniqueness clause of that lemma gives vu = fq; quotienting the Y variables uses
`lem-weil-pbc-power-series-quotient-variables`.
4. The images of the parameters of R, followed by the Z variables, generate the maximal
ideal of S: they generate each φ(X_i), hence each Y_i. Their number equals dim S. In the
Cohen case the list starts with p. Thus the images extend to a regular system of parameters.
5. By `lem-weil-pbc-regular-local-generators-regular-sequence`, the initial segment is a
regular sequence and its quotient is regular local. Apply `lem-weil-pbc-flat-over-regular`
to obtain flatness. The quotient is S modulo the extension of the maximal ideal of R.
This includes the empty parameter list.
-/
theorem exists_complete_local_map_cohen_presentation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (f : A →+* B) [IsLocalHom f] :
    ∃ (ΛA ΛB : Type (max u v)) (_ : CommRing ΛA) (_ : CommRing ΛB) (n m : ℕ),
      let R := MvPowerSeries (Fin n) ΛA
      let S := MvPowerSeries (Fin m) ΛB
      ∃ (_ : IsRegularLocalRing R) (_ : IsRegularLocalRing S),
        IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
        IsAdicComplete (IsLocalRing.maximalIdeal S) S ∧
        (CharZero (IsLocalRing.ResidueField A) → IsField ΛA ∧ IsField ΛB) ∧
        (∀ p : ℕ, p.Prime → CharP (IsLocalRing.ResidueField A) p →
          IsCohenRing p ΛA ∧ IsCohenRing p ΛB) ∧
        ∃ (q : R →+* A) (v : S →+* B) (u : R →+* S),
          Function.Surjective q ∧ IsLocalHom q ∧
          Function.Surjective v ∧ IsLocalHom v ∧ IsLocalHom u ∧
          v.comp u = f.comp q ∧ u.Flat ∧
          IsRegularLocalRing (S ⧸ (IsLocalRing.maximalIdeal R).map u) ∧
          ∃ (t : List R) (z : List S),
            IsLocalRing.IsRegularSystemOfParameters t ∧
            IsLocalRing.IsRegularSystemOfParameters (t.map u ++ z) ∧
            (∀ p : ℕ, p.Prime → CharP (IsLocalRing.ResidueField A) p →
              t.head? = some (p : R)) := by
  classical
  let e : A ≃+* ULift.{v} A := ULift.ringEquiv.symm
  let : IsLocalRing (ULift.{v} A) := e.isLocalRing
  let : IsNoetherianRing (ULift.{v} A) := isNoetherianRing_of_ringEquiv A e
  have hc := (IsAdicComplete.congr_ringEquiv (IsLocalRing.maximalIdeal A) e).mpr
    (inferInstance : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
  rw [IsLocalRing.map_ringEquiv_maximalIdeal] at hc
  let := hc
  obtain ⟨n, ΛA, hcomm, hlocal, hregular, hcomplete, q₀, hq, hqlocal, _, hcases⟩ :=
    IsLocalRing.cohen_power_series_presentation (ULift.{v} A)
  let := hcomm
  let := hlocal
  let := hregular
  let := hqlocal
  let q := e.symm.toRingHom.comp q₀
  have hqsurj : Function.Surjective q := e.symm.surjective.comp hq
  have hqlocal' : IsLocalHom q := IsLocalHom.of_surjective q hqsurj
  have hglocal : IsLocalHom (f.comp q) := RingHom.isLocalHom_comp f q
  have : IsLocalHom e.symm.toRingHom :=
    IsLocalHom.of_surjective _ e.symm.surjective
  let er := IsLocalRing.ResidueField.map e.symm.toRingHom
  rcases hcases with ⟨hfield, hchar, ⟨ec, _⟩, _, ht⟩ |
    ⟨p, hchar, hcohen, _, _, ht⟩
  · let := hchar
    have hΛchar : CharZero ΛA := ec.toRingHom.charZero
    let t : List (MvPowerSeries (Fin n) ΛA) := List.ofFn (fun i : Fin n ↦ MvPowerSeries.X i)
    obtain ⟨ΛB, hBcomm, m, hSregular, hScomplete, hBfield, _, v, u, hv, hvlocal,
      hulocal, hcomp, z, hz⟩ :=
      MvPowerSeries.exists_cohen_power_series_parameter_extension n 0
        (fun _ ↦ ⟨hfield, hΛchar⟩) (by simp) (f.comp q) t (by simp [t])
    let := hBcomm
    let := hSregular
    let := hulocal
    have hff := flat_and_regular_fibre_of_parameters u t z ht hz
    refine ⟨ΛA, ΛB, hcomm, hBcomm, n, m, hregular, hSregular,
      hcomplete, hScomplete, (fun _ ↦ ⟨hfield, hBfield rfl⟩), ?_,
      q, v, u, hqsurj, hqlocal', hv, hvlocal, hulocal, hcomp, hff.1, hff.2,
      t, z, ht, hz, ?_⟩
    · intro p hp hcp
      have : CharZero (IsLocalRing.ResidueField A) :=
        charZero_of_injective_ringHom er.injective
      exact False.elim (hp.ne_zero (CharP.eq _ hcp (CharP.ofCharZero _)))
    · intro p hp hcp
      have : CharZero (IsLocalRing.ResidueField A) :=
        charZero_of_injective_ringHom er.injective
      exact False.elim (hp.ne_zero (CharP.eq _ hcp (CharP.ofCharZero _)))
  · let := hchar
    have hp : p.Prime := hcohen.1
    let t : List (MvPowerSeries (Fin n) ΛA) :=
      (p : MvPowerSeries (Fin n) ΛA) :: List.ofFn (fun i : Fin n ↦ MvPowerSeries.X i)
    have ht' : IsLocalRing.IsRegularSystemOfParameters t := by simpa [t] using ht
    obtain ⟨ΛB, hBcomm, m, hSregular, hScomplete, _, hBcohen, v, u, hv, hvlocal,
      hulocal, hcomp, z, hz⟩ :=
      MvPowerSeries.exists_cohen_power_series_parameter_extension n p
        (fun h ↦ False.elim (hp.ne_zero h)) (fun _ ↦ hcohen)
        (f.comp q) t (by simp [t, hp.ne_zero])
    let := hBcomm
    let := hSregular
    let := hulocal
    have hff := flat_and_regular_fibre_of_parameters u t z ht' hz
    have hcharA : CharP (IsLocalRing.ResidueField A) p :=
      charP_of_injective_ringHom er.injective p
    refine ⟨ΛA, ΛB, hcomm, hBcomm, n, m, hregular, hSregular,
      hcomplete, hScomplete, ?_, ?_,
      q, v, u, hqsurj, hqlocal', hv, hvlocal, hulocal, hcomp, hff.1, hff.2,
      t, z, ht', hz, ?_⟩
    · intro hzero
      let := hzero
      exact False.elim (hp.ne_zero (CharP.eq _ hcharA (CharP.ofCharZero _)))
    · intro r _ hcr
      have hr : r = p := CharP.eq _ hcr hcharA
      subst r
      exact ⟨hcohen, hBcohen hp.ne_zero⟩
    · intro r _ hcr
      have hr : r = p := CharP.eq _ hcr hcharA
      subst r
      rfl

end RingHom

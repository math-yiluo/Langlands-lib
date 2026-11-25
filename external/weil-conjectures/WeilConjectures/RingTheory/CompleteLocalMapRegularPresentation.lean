/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import WeilConjectures.RingTheory.CompleteLocalMapCohenPresentation

/-!
# Compatible regular presentations of a map of complete local rings

Source: Stacks Project, More on Algebra, Lemma 07NN
(lemma-embed-map-Noetherian-complete-local-rings),
statement and proof (blueprint: lem-weil-pbc-complete-local-map-regular-presentation).
-/

@[expose] public section

universe u v

namespace RingHom

/-- Every local map of complete Noetherian local rings has compatible regular presentations.

Source: Stacks Project, More on Algebra, Lemma 07NN, statement and proof
(blueprint: lem-weil-pbc-complete-local-map-regular-presentation).

Proof:
1. Apply lem-weil-pbc-cohen-power-series-presentation to A and B to obtain surjective local
   maps q : R → A and v₀ : S₀ → B from complete regular power series rings. The residue fields
   have the same characteristic because f induces a field homomorphism. The coefficient ring
   of R has residue field A/m_A, so q induces the required residue-field isomorphism.
2. By lem-weil-pbc-field-cohen-power-series-formally-smooth, R is adically formally smooth
   over the integers. The kernel J of v₀ lies in m_S₀ and is closed, since
   lem-weil-pbc-complete-local-quotient makes S₀/J separated. The map fq is continuous and
   lem-weil-pbc-fs-adic-lift-into-complete lifts it to φ : R → S₀. Its bound on maximal ideals
   makes φ local (equivalently, use locality of fq and the preimage of m_B under v₀).
3. Set S = S₀[[y₁, …, yₙ]] using def-weil-pbc-multivariate-power-series. Grouping variables
   and lem-weil-pbc-power-series-field-cohen-regular-complete make S complete regular local.
   Evaluation at y = 0 followed by v₀ gives a surjective local v, by
   lem-weil-pbc-power-series-quotient-variables. By lem-weil-pbc-power-series-adic-evaluation,
   define u with the coefficient map of φ and u(xᵢ) = φ(xᵢ) + yᵢ. Images of the generators of
   m_R lie in m_S (including p in the Cohen case), so u is local. Uniqueness of evaluation
   into complete B gives vu = fq, since these maps agree on coefficients and variables.
4. Put aᵢ = φ(xᵢ) ∈ m_S₀. The substitutions yᵢ ↦ aᵢ + yᵢ and yᵢ ↦ yᵢ - aᵢ are inverse
   continuous automorphisms by lem-weil-pbc-power-series-adic-evaluation and its uniqueness.
   Apply the first to the standard parameters of S, given by
   lem-weil-pbc-power-series-field-cohen-regular-complete. The resulting system contains all
   u(xᵢ), and also u(p) = p in the Cohen case. Thus the parameters of R extend to those of S.
5. Reorder that system to put the images of the parameters of R first. They are a regular
   sequence by lem-weil-pbc-regular-local-generators-regular-sequence. Therefore
   lem-weil-pbc-flat-over-regular proves that u is flat.
6. Those images generate m_R S. The quotient clause of
   lem-weil-pbc-regular-local-generators-regular-sequence shows that S/m_R S is regular
   local. When d = 0 the ideal is zero and the quotient is S. -/
theorem exists_complete_local_map_regular_presentation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (f : A →+* B) [IsLocalHom f] :
    ∃ (R S : Type (max u v)) (_ : CommRing R) (_ : CommRing S)
      (_ : IsRegularLocalRing R) (_ : IsRegularLocalRing S),
      IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
      IsAdicComplete (IsLocalRing.maximalIdeal S) S ∧
      ∃ (q : R →+* A) (v : S →+* B) (u : R →+* S),
        Function.Surjective q ∧ IsLocalHom q ∧
        Function.Surjective v ∧ IsLocalHom v ∧ IsLocalHom u ∧
        v.comp u = f.comp q ∧
        (∃ e : (R ⧸ IsLocalRing.maximalIdeal R) ≃+* (A ⧸ IsLocalRing.maximalIdeal A),
          ∀ r : R,
            e (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) r) =
              Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (q r)) ∧
        (∃ (t : List R) (z : List S),
          IsLocalRing.IsRegularSystemOfParameters t ∧
          IsLocalRing.IsRegularSystemOfParameters (t.map u ++ z)) ∧
        u.Flat ∧ IsRegularLocalRing (S ⧸ (IsLocalRing.maximalIdeal R).map u) := by
  obtain ⟨ΛA, ΛB, cA, cB, n, m, hR, hS, hcR, hcS, hchar, hcohen,
    hdata⟩ := exists_complete_local_map_cohen_presentation f
  obtain ⟨q, v, u, hq, hq_local, hv, hv_local, hu_local, hcomm,
    hflat, hfiber, hparams⟩ := hdata
  obtain ⟨t, z, ht, hz, hp⟩ := hparams
  let R := MvPowerSeries (Fin n) ΛA
  let S := MvPowerSeries (Fin m) ΛB
  let : CommRing ΛA := cA
  let : CommRing ΛB := cB
  let : CommRing R := inferInstance
  let : CommRing S := inferInstance
  let : IsRegularLocalRing R := hR
  let : IsRegularLocalRing S := hS
  let : IsLocalHom q := hq_local
  let qres := IsLocalRing.ResidueField.map q
  have hsurj : Function.Surjective qres := by
    intro a
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
    obtain ⟨r, rfl⟩ := hq a
    exact ⟨IsLocalRing.residue R r, rfl⟩
  have hres : ∃ e : (R ⧸ IsLocalRing.maximalIdeal R) ≃+*
      (A ⧸ IsLocalRing.maximalIdeal A),
      ∀ r : R, e (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) r) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (q r) := by
    exact ⟨RingEquiv.ofBijective qres ⟨qres.injective, hsurj⟩, fun _ ↦ rfl⟩
  exact ⟨R, S, inferInstance, inferInstance, hR, hS, hcR, hcS,
    q, v, u, hq, hq_local, hv, hv_local, hu_local, hcomm, hres,
    ⟨t, z, ht, hz⟩, hflat, hfiber⟩

end RingHom

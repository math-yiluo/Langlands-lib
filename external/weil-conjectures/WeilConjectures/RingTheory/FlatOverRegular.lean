/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.AlgebraicGeometry.FlatLocalCriterionNonzerodivisor
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Flatness over a regular local ring

Source: Stacks Project, Algebra, Lemma 10.128.2 (Tag 07DY)
(blueprint: lem-weil-pbc-flat-over-regular).
-/

@[expose] public section

universe u v

namespace RingHom

private theorem flat_of_quotient_nonzerodivisor {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (φ : R →+* S) [IsLocalHom φ] (x : R)
    (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hR : IsSMulRegular R x) (hS : IsSMulRegular S (φ x))
    (hquot : (Ideal.quotientMap (I := Ideal.span {x}) (Ideal.span {φ x}) φ
      (by simpa only [Ideal.map_span, Set.image_singleton] using
        (Ideal.le_comap_map (f := φ) (I := Ideal.span {x})))).Flat) : φ.Flat := by
  let := φ.toAlgebra
  let := Submodule.pointwiseDistribMulAction (α := R) (R := R) (M := S)
  let I := Ideal.span ({x} : Set R)
  let J := Ideal.span ({φ x} : Set S)
  let ψ : R ⧸ I →+* S ⧸ J := Ideal.quotientMap J φ
    (by simpa only [I, J, Ideal.map_span, Set.image_singleton] using
      (Ideal.le_comap_map (f := φ) (I := I)))
  let := ψ.toAlgebra
  have : IsScalarTower R (R ⧸ I) (S ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ rfl
  have heq : (x • (⊤ : Submodule R S)) = J.restrictScalars R := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_top_eq_map]
    congr 1
    simp only [Ideal.map_span, Set.image_singleton, J]
    rfl
  let e : QuotSMulTop x S ≃ₗ[R] S ⧸ J :=
    (Submodule.quotEquivOfEq _ _ heq).trans (Submodule.Quotient.restrictScalarsEquiv R J)
  let e' : QuotSMulTop x S ≃ₗ[R ⧸ I] S ⧸ J :=
    e.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  have hq : Module.Flat (R ⧸ I) (S ⧸ J) := hquot
  let := hq
  have hflat : Module.Flat (R ⧸ I) (QuotSMulTop x S) := Module.Flat.of_linearEquiv e'
  have hxreg : x ∈ nonZeroDivisors R := by
    constructor
    · intro r hr
      exact hR (by simpa only [smul_eq_mul, mul_zero] using hr)
    · intro r hr
      exact hR (by simpa only [smul_eq_mul, mul_zero, mul_comm] using hr)
  exact RingTheory.flat_of_localCriterion_nonzerodivisor R S S x hx hxreg
    (by
      change Function.Injective (fun s : S ↦ φ x * s)
      exact hS) hflat

private theorem regular_quotient_tail {R : Type u} [CommRing R] (r : R) (rs : List R)
    (h : RingTheory.Sequence.IsRegular R (r :: rs)) :
    RingTheory.Sequence.IsRegular (R ⧸ Ideal.span {r})
      (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) := by
  let := Submodule.pointwiseDistribMulAction (α := R) (R := R) (M := R)
  have heq : r • (⊤ : Submodule R R) = (Ideal.span {r}) := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  let e : QuotSMulTop r R ≃ₗ[R] R ⧸ Ideal.span {r} :=
    Submodule.quotEquivOfEq _ _ heq
  let e' : QuotSMulTop r R ≃ₗ[R ⧸ Ideal.span {r}] R ⧸ Ideal.span {r} :=
    e.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  exact (e'.isRegular_congr _).mp ((RingTheory.Sequence.isRegular_cons_iff' R r rs).mp h).2

/-- A local homomorphism of Noetherian local rings is flat if a regular system of parameters
of the regular local source maps to a regular sequence in the target.
Source: Stacks Project, Algebra, Lemma 10.128.2 (Tag 07DY)
(blueprint: lem-weil-pbc-flat-over-regular).

Proof: Let `R_i` and `S_i` be the quotients by the first `i` parameters and their images.
The map induces local homomorphisms `R_i → S_i` of Noetherian local rings
(def-weil-pbc-noetherian-ring). These quotients are nonzero: the final quotient of `S` is
nonzero by regularity (def-weil-pbc-regular-sequence), and all earlier quotients surject onto
it; the source quotients map to them. Their maximal ideals are the images of the original
maximal ideals, and the successive quotients are by the next parameter.
At the final index, `R_d = R / m_R` is a field, so `S_d` is flat over `R_d`
(lem-weil-pbc-module-over-field-flat). Regularity of `R` and generation of its maximal ideal
by `d = dim R` parameters imply that these parameters form a regular sequence in `R`
(lem-weil-pbc-regular-local-generators-regular-sequence, def-weil-regular-scheme).
Thus each next parameter is a nonzerodivisor both on the source quotient and on the target
quotient, the latter by the assumed regular sequence (def-weil-pbc-regular-sequence).
Apply the local criterion modulo a nonzerodivisor to `R_{i-1} → S_{i-1}`, with the finite
`S_{i-1}`-module `S_{i-1}` and this parameter in the maximal ideal
(lem-weil-pbc-flat-local-criterion-nonzerodivisor). Flatness of `S_i` over `R_i` gives
flatness of `S_{i-1}` over `R_{i-1}`. Descending induction ends at `S` flat over `R`,
i.e. the given map is flat (def-weil-pbc-flat-ring-map). If `d = 0`, the field base case
already gives the conclusion. -/
theorem flat_of_regular_parameters {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsRegularLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
    (φ : R →+* S) [IsLocalHom φ] (d : ℕ) (x : List R)
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) (hx : x.length = d)
    (hgen : Ideal.ofList x = IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsRegular S (x.map φ)) : φ.Flat := by
  induction d generalizing R S with
  | zero =>
    have hxnil : x = [] := List.length_eq_zero_iff.mp hx
    have hm : IsLocalRing.maximalIdeal R = ⊥ := by
      rw [← hgen, hxnil, Ideal.ofList_nil]
    exact RingHom.Flat.of_isField (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm) φ
  | succ d ih =>
    cases x with
    | nil => simp at hx
    | cons r rs =>
      have hrs : IsLocalRing.IsRegularSystemOfParameters (r :: rs) :=
        ⟨hgen, by rw [hx, hd]⟩
      have hp := IsRegularLocalRing.isRegular_and_quotients_of_generators
        R (d + 1) hd (r :: rs) hrs
      have hrmem : r ∈ IsLocalRing.maximalIdeal R :=
        hgen ▸ Ideal.subset_span List.mem_cons_self
      let I := Ideal.span ({r} : Set R)
      let J := Ideal.span ({φ r} : Set S)
      have hI : I = Ideal.ofList ((r :: rs).take 1) := by
        simp only [List.take_succ_cons, List.take_zero, Ideal.ofList_singleton, I]
      have hRq := hp.2.1 1 (by omega)
      rw [← hI] at hRq
      let := hRq.1
      have hdim : ringKrullDim (R ⧸ I) = (d : WithBot ℕ∞) := by simpa using hRq.2
      have hJ : J ≤ IsLocalRing.maximalIdeal S := by
        apply Ideal.span_le.mpr
        intro s hs
        have hs' : s = φ r := Set.mem_singleton_iff.mp hs
        subst s
        exact map_nonunit φ r hrmem
      have hJne : J ≠ ⊤ :=
        ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top hJ
      let := Ideal.Quotient.nontrivial_iff.mpr hJne
      let := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      let ψ : R ⧸ I →+* S ⧸ J := Ideal.quotientMap J φ
        (by simpa only [I, J, Ideal.map_span, Set.image_singleton] using
          (Ideal.le_comap_map (f := φ) (I := I)))
      let : IsLocalHom (Ideal.Quotient.mk J) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      let : IsLocalHom ψ := by
        constructor
        intro a ha
        obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact (Ideal.Quotient.mk I).isUnit_map
          (isUnit_of_map_unit φ t (isUnit_of_map_unit (Ideal.Quotient.mk J) (φ t) ha))
      have hgenq : Ideal.ofList (rs.map (Ideal.Quotient.mk I)) =
          IsLocalRing.maximalIdeal (R ⧸ I) := by
        rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
          Ideal.Quotient.mk_surjective, ← hgen, Ideal.ofList_cons, Ideal.map_sup]
        have hzero : (Ideal.span {r}).map (Ideal.Quotient.mk I) = ⊥ :=
          Ideal.map_quotient_self I
        rw [hzero, bot_sup_eq, Ideal.map_ofList]
      have hregq : RingTheory.Sequence.IsRegular (S ⧸ J)
          ((rs.map (Ideal.Quotient.mk I)).map ψ) := by
        have ht := regular_quotient_tail (φ r) (rs.map φ) (by simpa using hreg)
        convert ht using 1
        simp only [List.map_map]
        rfl
      have hlenq : (rs.map (Ideal.Quotient.mk I)).length = d := by
        simp only [List.length_cons] at hx
        simpa using Nat.succ.inj hx
      have hflatq : ψ.Flat := ih ψ (rs.map (Ideal.Quotient.mk I)) hdim hlenq hgenq hregq
      have hheadR := (RingTheory.Sequence.isRegular_cons_iff R r rs).mp hp.1
      have hheadS := (RingTheory.Sequence.isRegular_cons_iff S (φ r) (rs.map φ)).mp
        (by simpa using hreg)
      exact flat_of_quotient_nonzerodivisor φ r hrmem hheadR.1 hheadS.1 hflatq

end RingHom

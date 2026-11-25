/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.CohenRing
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Ring.ULift
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.MvPowerSeries.Inverse
import WeilConjectures.RingTheory.PowerSeriesParameterPerturbation
import WeilConjectures.RingTheory.CohenPowerSeriesPresentation
import WeilConjectures.RingTheory.FieldCohenPowerSeriesFormallySmooth
import WeilConjectures.RingTheory.FormallySmoothAdicLiftIntoComplete
import WeilConjectures.RingTheory.PowerSeriesQuotientVariables

/-!
# Extending a Cohen power series parameter list along a local map

Source: Stacks Project, More on Algebra, Lemma 07NN, proof, lifting and adjoining variables.
(blueprint: lem-weil-pbc-cohen-power-series-parameter-extension)
-/

@[expose] public section

universe u v

namespace MvPowerSeries

private theorem local_lift_of_formally_smooth
    {R : Type u} {S : Type v} {B : Type*} [CommRing R] [CommRing S] [CommRing B]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal S) S]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (hR : Algebra.FormallySmoothAdic ℤ R (IsLocalRing.maximalIdeal R))
    (v : S →+* B) (hv : Function.Surjective v) (g : R →+* B) [IsLocalHom g] :
    ∃ φ : R →+* S, IsLocalHom φ ∧ v.comp φ = g := by
  let J := RingHom.ker v
  let I := IsLocalRing.maximalIdeal S
  have : IsLocalHom v := IsLocalHom.of_surjective v hv
  have hmax : I.map v = IsLocalRing.maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective v hv
  have hJI : J ≤ I := by
    intro x hx
    change x ∈ IsLocalRing.maximalIdeal S
    rw [← IsLocalRing.maximalIdeal_comap v]
    change v x ∈ IsLocalRing.maximalIdeal B
    rw [show v x = 0 from hx]
    exact Ideal.zero_mem _
  have hclosed : J = ⨅ (k : ℕ) (_ : 1 ≤ k), J ⊔ I ^ k := by
    apply le_antisymm
    · exact le_iInf fun k ↦ le_iInf fun _ ↦ le_sup_left
    · intro x hx
      change v x = 0
      have he : (fun _ : Unit ↦ v x) = (fun _ : Unit ↦ (0 : B)) := by
        apply IsHausdorff.funext' (IsLocalRing.maximalIdeal B)
        intro k _
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        cases k with
        | zero => simp
        | succ k =>
          have hm := Ideal.mem_iInf.mp (Ideal.mem_iInf.mp hx (k + 1)) (by omega)
          have hp : (IsLocalRing.maximalIdeal B) ^ (k + 1) = (I ^ (k + 1)).map v := by
            rw [Ideal.map_pow, hmax]
          rw [hp]
          change x ∈ ((I ^ (k + 1)).map v).comap v
          rw [Ideal.comap_map_of_surjective v hv, ← RingHom.ker_eq_comap_bot, sup_comm]
          exact hm
      exact congrFun he ()
  let e : (S ⧸ J) ≃ₐ[ℤ] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := v.toIntAlgHom) hv
  let gq := e.symm.toAlgHom.comp g.toIntAlgHom
  obtain ⟨φ, hφ, hbound⟩ := hR.exists_lift_into_complete
    (IsLocalRing.maximalIdeal R) I J 1 le_rfl (by simpa only [pow_one] using hJI)
    hclosed gq 1 le_rfl (by
      intro x hx
      obtain ⟨y, hy⟩ := hv (g x)
      have hym : y ∈ I := by
        change y ∈ IsLocalRing.maximalIdeal S
        rw [← IsLocalRing.maximalIdeal_comap v]
        change v y ∈ IsLocalRing.maximalIdeal B
        rw [hy]
        exact map_nonunit g x (by simpa using hx)
      change e.symm (g x) ∈ I.map (Ideal.Quotient.mk J)
      rw [← hy]
      change (Ideal.quotientKerAlgEquivOfSurjective (f := v.toIntAlgHom) hv).symm
        (v.toIntAlgHom y) ∈ I.map (Ideal.Quotient.mk J)
      rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
      exact Ideal.mem_map_of_mem _ hym)
  refine ⟨φ.toRingHom, ?_, ?_⟩
  · constructor
    intro x hx
    by_contra hunit
    have hm : φ x ∈ I := hbound x (by simpa using hunit)
    exact hm hx
  · ext x
    have he := congrArg e (AlgHom.congr_fun hφ x)
    change v (φ x) = e (e.symm (g x)) at he
    simpa using he

private theorem power_series_maximalIdeal
    {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] (n : ℕ) :
    IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) Λ) =
      (IsLocalRing.maximalIdeal Λ).map C ⊔ Ideal.span (Set.range (X : Fin n → _)) := by
  have hm : IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) Λ) =
      (IsLocalRing.maximalIdeal Λ).comap constantCoeff := by
    ext f
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_iff_constantCoeff]
  have hk := (quotient_first_variables_kernels Λ n n le_rfl).2
  rw [hm]
  apply le_antisymm
  · intro f hf
    have hdiff : f - C (constantCoeff f) ∈ RingHom.ker (constantCoeff (σ := Fin n)) := by
      simp
    rw [hk] at hdiff
    have hc := Ideal.mem_map_of_mem (C : Λ →+* MvPowerSeries (Fin n) Λ)
      (show constantCoeff f ∈ IsLocalRing.maximalIdeal Λ from hf)
    simpa using (Submodule.mem_sup.mpr ⟨_, hc, _, hdiff, add_sub_cancel _ _⟩)
  · apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simpa using ha
    · rw [← hk]
      exact Ideal.comap_mono bot_le

/-- Extend the canonical parameters of a fixed power series source along a local map.
This is the construction part of Stacks Project, More on Algebra, Lemma 07NN: it does not
assert flatness or regularity of the closed fibre.
(blueprint: lem-weil-pbc-cohen-power-series-parameter-extension)

Proof:
1. Choose a Cohen power series presentation `v₀ : S₀ → B`. The residue map of the given
   local map is injective, so the coefficient characteristics agree: in case `c = 0`
   both coefficient rings are fields, and otherwise both are Cohen rings for `c`.
2. Write `J = ker v₀`. Surjectivity and locality imply `J ≤ m₀` and
   `map v₀ (m₀ ^ k) = mB ^ k`. Thus `J` is closed in the maximal-ideal topology:
   an element of every `J + m₀ ^ k` maps into every `mB ^ k`, hence maps to zero
   by separatedness of the complete ring `B`.
3. Formal smoothness over the integers of the given field or Cohen power series ring,
   and the complete-target lifting lemma with `I = m₀`, `t = r = 1`, lift the given
   map to a local map `φ : R → S₀`. Identify `S₀ / J` with `B` using `v₀`.
4. If `S₀ = ΛB[[Z₁,...,Zₑ]]`, take `S = ΛB[[Y₁,...,Yₙ,Z₁,...,Zₑ]]` and let `v`
   kill the `Y` variables and agree with `v₀` on `S₀`. Evaluation in the complete
   ring `S` gives `h` agreeing with `φ` on coefficients and sending `Xᵢ` to
   `φ(Xᵢ) + Yᵢ`. The power series evaluation uniqueness theorem gives `v h = g`.
   The maximal ideal generators show that `v` and `h` are local; `v` is surjective
   because the map killing `Y` is surjective.
5. Put `z = [Z₁,...,Zₑ]`. The list `t.map h ++ z` generates the maximal ideal:
   it contains the `Z` variables and, in the Cohen case, `c`; these generate the
   ideal containing each `φ(Xᵢ)`. Subtracting from `h(Xᵢ)` then gives each `Yᵢ`.
   Its length is `n + e` in the field case and `n + e + 1` in the Cohen case,
   exactly the dimension of `S`. It is therefore a regular system of parameters.
   This calculation also applies when either variable set is empty. -/
theorem exists_cohen_power_series_parameter_extension
    {Λ : Type u} [CommRing Λ] (n c : ℕ)
    [IsRegularLocalRing (MvPowerSeries (Fin n) Λ)]
    (hzero : c = 0 → IsField Λ ∧ CharZero Λ)
    (hpos : c ≠ 0 → IsCohenRing c Λ)
    {B : Type v} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (g : MvPowerSeries (Fin n) Λ →+* B) [IsLocalHom g]
    (t : List (MvPowerSeries (Fin n) Λ))
    (ht : t = if c = 0 then List.ofFn (fun i : Fin n ↦ (X i : MvPowerSeries (Fin n) Λ))
      else (c : MvPowerSeries (Fin n) Λ) :: List.ofFn (fun i : Fin n ↦ X i)) :
    ∃ (ΛB : Type (max u v)) (_ : CommRing ΛB) (m : ℕ)
      (_ : IsRegularLocalRing (MvPowerSeries (Fin m) ΛB)),
      IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin m) ΛB))
        (MvPowerSeries (Fin m) ΛB) ∧
      (c = 0 → IsField ΛB) ∧ (c ≠ 0 → IsCohenRing c ΛB) ∧
      ∃ (v : MvPowerSeries (Fin m) ΛB →+* B)
        (h : MvPowerSeries (Fin n) Λ →+* MvPowerSeries (Fin m) ΛB),
        Function.Surjective v ∧ IsLocalHom v ∧ IsLocalHom h ∧ v.comp h = g ∧
        ∃ z : List (MvPowerSeries (Fin m) ΛB),
          IsLocalRing.IsRegularSystemOfParameters (t.map h ++ z) := by
  classical
  have hsmooth : Algebra.FormallySmoothAdic ℤ (MvPowerSeries (Fin n) Λ)
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) Λ)) := by
    apply (field_cohen_power_series_formally_smooth.{u, v} n _ ?_).1
    by_cases hc : c = 0
    · obtain ⟨hfield, hchar⟩ := hzero hc
      let := hfield.toField
      refine Or.inl ⟨hfield, hchar, ?_⟩
      simp only [power_series_maximalIdeal, IsLocalRing.maximalIdeal_eq_bot,
        Ideal.map_bot, bot_sup_eq]
    · obtain ⟨hp, hd, hv, hm, _⟩ := hpos hc
      let := hd
      let := hv
      refine Or.inr ⟨c, hpos hc, ?_⟩
      rw [power_series_maximalIdeal, hm, Ideal.map_span, Set.image_singleton,
        ← Ideal.span_insert]
  have hcharB : CharP (IsLocalRing.ResidueField B) c := by
    by_cases hc : c = 0
    · subst c
      obtain ⟨hfield, hchar⟩ := hzero rfl
      let := hfield.toField
      let := hchar
      let a : Λ →+* IsLocalRing.ResidueField B :=
        (IsLocalRing.residue B).comp (g.comp C)
      have : CharZero (IsLocalRing.ResidueField B) :=
        charZero_of_injective_ringHom a.injective
      exact CharP.ofCharZero _
    · obtain ⟨hp, hd, hv, hm, _⟩ := hpos hc
      let := hd
      let := hv
      have hcΛ : (c : Λ) ∈ IsLocalRing.maximalIdeal Λ := by
        rw [hm]
        exact Ideal.subset_span (Set.mem_singleton _)
      have hcR : (c : MvPowerSeries (Fin n) Λ) ∈
          IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) Λ) := by
        intro hunit
        exact hcΛ (by simpa using isUnit_constantCoeff _ hunit)
      apply (CharP.charP_iff_prime_eq_zero hp).mpr
      have hmem := map_nonunit g _ hcR
      have hz := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
      simpa only [map_natCast] using hz
  let eB : B ≃+* ULift.{u} B := ULift.ringEquiv.symm
  let : IsLocalRing (ULift.{u} B) := eB.isLocalRing
  let : IsNoetherianRing (ULift.{u} B) := isNoetherianRing_of_ringEquiv B eB
  have hcompB := (IsAdicComplete.congr_ringEquiv (IsLocalRing.maximalIdeal B) eB).mpr
    (inferInstance : IsAdicComplete (IsLocalRing.maximalIdeal B) B)
  rw [IsLocalRing.map_ringEquiv_maximalIdeal] at hcompB
  let := hcompB
  have : IsLocalHom eB.toRingHom := IsLocalHom.of_surjective _ eB.surjective
  let erB := IsLocalRing.ResidueField.map eB.toRingHom
  let := hcharB
  have hcharUB : CharP (IsLocalRing.ResidueField (ULift.{u} B)) c :=
    charP_of_injective_ringHom erB.injective c
  obtain ⟨e, ΛB, hcomm, hlocal, hregular, hcomplete, v₀, hv₀, hvlocal, _, hcases⟩ :=
    IsLocalRing.cohen_power_series_presentation (ULift.{u} B)
  let := hcomm
  let := hlocal
  let := hregular
  let := hcomplete
  let v := eB.symm.toRingHom.comp v₀
  have hvsurj : Function.Surjective v := eB.symm.surjective.comp hv₀
  have hvlocal' : IsLocalHom v := IsLocalHom.of_surjective v hvsurj
  have hcoeff : (c = 0 → IsField ΛB) ∧ (c ≠ 0 → IsCohenRing c ΛB) := by
    rcases hcases with ⟨hfield, hchar, _⟩ | ⟨p, hchar, hcohen, _⟩
    · let := hchar
      have hc : c = 0 := CharP.eq _ hcharUB (CharP.ofCharZero _)
      exact ⟨fun _ ↦ hfield, fun h ↦ False.elim (h hc)⟩
    · have hp : p = c := CharP.eq _ hchar hcharUB
      subst p
      exact ⟨fun h ↦ False.elim (hcohen.1.ne_zero h), fun _ ↦ hcohen⟩
  obtain ⟨φ, hφlocal, hφ⟩ := local_lift_of_formally_smooth
    (by convert hsmooth using 1; exact Subsingleton.elim _ _) v hvsurj g
  let := hφlocal
  obtain ⟨hSregular, hScomplete, π, h, hπ, hπlocal, hhlocal, hπh, z, hz⟩ :=
    exists_power_series_parameter_perturbation n e c hzero hpos hcoeff.1 hcoeff.2 φ t ht
  let := hSregular
  let := hπlocal
  refine ⟨ΛB, hcomm, n + e, hSregular, hScomplete, hcoeff.1, hcoeff.2,
    v.comp π, h, hvsurj.comp hπ, inferInstance, hhlocal, ?_, z, hz⟩
  rw [RingHom.comp_assoc, hπh, hφ]

end MvPowerSeries

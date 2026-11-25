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
import WeilConjectures.RingTheory.PowerSeriesAdicEvaluation
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.PowerSeriesQuotientVariables
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Perturbing a local map of power series rings by independent variables

Source: Stacks Project, More on Algebra, Lemma 07NN, final proof paragraph.
(blueprint: lem-weil-pbc-power-series-parameter-perturbation)
-/

@[expose] public section

universe u v

namespace MvPowerSeries

private theorem variable_mem_maximal {A : Type*} [CommRing A] [Nontrivial A]
    {d : ℕ} [IsLocalRing (MvPowerSeries (Fin d) A)] (i : Fin d) :
    (X i : MvPowerSeries (Fin d) A) ∈ IsLocalRing.maximalIdeal _ := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff]
  simp

private theorem adic_continuous_of_variables {A T : Type*} [CommRing A] [CommRing T]
    (d : ℕ) (f : MvPowerSeries (Fin d) A →+* T) (I : Ideal T)
    (hf : ∀ i, f (X i) ∈ I) :
    ∀ N : ℕ, ∃ M : ℕ,
      ∀ F ∈ (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) A))) ^ M,
        f F ∈ I ^ N := by
  have hle : (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) A))).map f ≤ I := by
    rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hf i
  intro N
  refine ⟨N, fun F hF ↦ ?_⟩
  have h := Ideal.mem_map_of_mem f hF
  rw [Ideal.map_pow] at h
  exact (pow_le_pow_left' hle N) h

private theorem maximal_ideal_decomposition {A : Type*} [CommRing A] [IsLocalRing A]
    (d : ℕ) : IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) A) =
      (IsLocalRing.maximalIdeal A).map C ⊔ Ideal.span (Set.range (X : Fin d → _)) := by
  have hk := (quotient_first_variables A d d le_rfl).2.2.2.2.1
  have hm : IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) A) =
      (IsLocalRing.maximalIdeal A).comap constantCoeff := by
    ext f
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_iff_constantCoeff]
  rw [hm]
  apply le_antisymm
  · intro f hf
    have hdiff : f - C (constantCoeff f) ∈ RingHom.ker (constantCoeff (σ := Fin d)) := by
      simp
    rw [hk] at hdiff
    have hc := Ideal.mem_map_of_mem (C : A →+* MvPowerSeries (Fin d) A)
      (show constantCoeff f ∈ IsLocalRing.maximalIdeal A from hf)
    simpa using (Submodule.mem_sup.mpr ⟨_, hc, _, hdiff, add_sub_cancel _ _⟩)
  · apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simpa using ha
    · rw [← hk]
      intro f hf
      change constantCoeff f ∈ IsLocalRing.maximalIdeal A
      rw [RingHom.mem_ker.mp hf]
      exact Ideal.zero_mem _

private theorem coefficient_maximal_map_le {A T : Type*} [CommRing A] [IsLocalRing A]
    [CommRing T] (c : ℕ) (hzero : c = 0 → IsField A)
    (hpos : c ≠ 0 → IsCohenRing c A) (α : A →+* T) (I : Ideal T)
    (hc : c ≠ 0 → (c : T) ∈ I) : (IsLocalRing.maximalIdeal A).map α ≤ I := by
  by_cases hcz : c = 0
  · let := (hzero hcz).toField
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot]
    exact bot_le
  · obtain ⟨_, hdom, hdvr, hmax, _⟩ := hpos hcz
    rw [hmax, Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro x ⟨a, ha, rfl⟩
    obtain rfl := Set.mem_singleton_iff.mp ha
    simpa using hc hcz

private theorem mapped_maximal_le {A T : Type*} [CommRing A] [IsLocalRing A]
    [CommRing T] (d : ℕ) (f : MvPowerSeries (Fin d) A →+* T) (I : Ideal T)
    (hc : (IsLocalRing.maximalIdeal A).map (f.comp C) ≤ I)
    (hx : ∀ i, f (X i) ∈ I) :
    (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) A)).map f ≤ I := by
  rw [maximal_ideal_decomposition, Ideal.map_sup, Ideal.map_map]
  apply sup_le hc
  rw [Ideal.map_le_iff_le_comap]
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact hx i

private theorem coefficient_local {A : Type*} [CommRing A] (c : ℕ)
    (hzero : c = 0 → IsField A) (hpos : c ≠ 0 → IsCohenRing c A) : IsLocalRing A := by
  by_cases hc : c = 0
  · let := (hzero hc).toField
    infer_instance
  · obtain ⟨_, hdom, hdvr, _⟩ := hpos hc
    let := hdom
    let := hdvr
    infer_instance

private theorem regular_complete_dimension {A : Type*} [CommRing A] (d c : ℕ)
    (hzero : c = 0 → IsField A) (hpos : c ≠ 0 → IsCohenRing c A) :
    ∃ (_ : IsRegularLocalRing (MvPowerSeries (Fin d) A)),
      IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) A))
        (MvPowerSeries (Fin d) A) ∧
      ringKrullDim (MvPowerSeries (Fin d) A) =
        ((if c = 0 then d else d + 1 : ℕ) : WithBot ℕ∞) := by
  classical
  have hcoeff : IsField A ∨ ∃ p, IsCohenRing p A := by
    by_cases hc : c = 0
    · exact Or.inl (hzero hc)
    · exact Or.inr ⟨c, hpos hc⟩
  rcases power_series_field_cohen_regular_complete d hcoeff with hf | hp
  · obtain ⟨hf, hn, hd, hl, hm, eqv, heqv, hcomp, hreg, hdim⟩ := hf
    have hc : c = 0 := by
      by_contra hc
      obtain ⟨_, hdom, hdvr, _⟩ := hpos hc
      let := hdom
      let := hdvr
      exact IsDiscreteValuationRing.not_isField A hf
    refine ⟨hreg, hcomp, ?_⟩
    simpa [hc] using hdim
  · obtain ⟨p, hp, hn, hd, hl, hm, eqv, heqv, hcomp, hreg, hdim⟩ := hp
    have hc : c ≠ 0 := by
      intro hc
      obtain ⟨_, hdom, hdvr, _⟩ := hp
      let := hdom
      let := hdvr
      exact IsDiscreteValuationRing.not_isField A (hzero hc)
    refine ⟨hreg, hcomp, ?_⟩
    simpa [hc] using hdim

/-- Adjoining independent variables makes the canonical source parameters part of
parameters of the target, with a split surjection back to the original target.
Source: Stacks Project, More on Algebra, Lemma 07NN, final proof paragraph.
(blueprint: lem-weil-pbc-power-series-parameter-perturbation)

Proof:
1. Set `S = ΛB[[Y₁,...,Yₙ,Z₁,...,Zₑ]]`. The field/Cohen power series theorem makes
   `S` complete and regular, with maximal ideal generated by `Y,Z` and, if `c ≠ 0`, `c`.
2. Delete `Y` using the power series quotient-variables theorem, and reindex the remaining
   variables by `Fin e`; this gives a split surjective local map `π : S → S₀`.
   The section `ι` is the inclusion of series involving only `Z`.
3. Apply adic evaluation with coefficient map `ι φ C` and values `ι (φ Xᵢ) + Yᵢ`.
   They lie in the maximal ideal because `φ` and `ι` are local. This constructs `h`.
   Both `π h` and `φ` are continuous and agree on coefficients and variables;
   uniqueness of adic evaluation in the complete ring `S₀` proves `π h = φ`.
4. The list `t.map h ++ [Z₁,...,Zₑ]` generates the maximal ideal: it contains
   all `Z` and, in the Cohen case, `c`. Thus it generates each `ι (φ Xᵢ)`, since
   these belong to the extension of the maximal ideal of `S₀`. Subtraction gives `Yᵢ`.
   The list has `n + e` entries in the field case and `n + e + 1` in the Cohen case,
   equal to the dimension of `S`, hence is a regular system of parameters.
   Generation also proves locality of `h`; deletion is local by its surjectivity.
   The same argument includes `n = 0` and `e = 0`. -/
theorem exists_power_series_parameter_perturbation
    {ΛA : Type u} {ΛB : Type v} [CommRing ΛA] [CommRing ΛB] (n e c : ℕ)
    [IsRegularLocalRing (MvPowerSeries (Fin n) ΛA)]
    [IsRegularLocalRing (MvPowerSeries (Fin e) ΛB)]
    [IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin e) ΛB))
      (MvPowerSeries (Fin e) ΛB)]
    (hzeroA : c = 0 → IsField ΛA ∧ CharZero ΛA)
    (hposA : c ≠ 0 → IsCohenRing c ΛA)
    (hzeroB : c = 0 → IsField ΛB) (hposB : c ≠ 0 → IsCohenRing c ΛB)
    (φ : MvPowerSeries (Fin n) ΛA →+* MvPowerSeries (Fin e) ΛB) [IsLocalHom φ]
    (t : List (MvPowerSeries (Fin n) ΛA))
    (ht : t = if c = 0 then List.ofFn (fun i : Fin n ↦ (X i : MvPowerSeries (Fin n) ΛA))
      else (c : MvPowerSeries (Fin n) ΛA) :: List.ofFn (fun i : Fin n ↦ X i)) :
    ∃ (_ : IsRegularLocalRing (MvPowerSeries (Fin (n + e)) ΛB)),
      IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin (n + e)) ΛB))
        (MvPowerSeries (Fin (n + e)) ΛB) ∧
      ∃ (π : MvPowerSeries (Fin (n + e)) ΛB →+* MvPowerSeries (Fin e) ΛB)
        (h : MvPowerSeries (Fin n) ΛA →+* MvPowerSeries (Fin (n + e)) ΛB),
        Function.Surjective π ∧ IsLocalHom π ∧ IsLocalHom h ∧ π.comp h = φ ∧
        ∃ z : List (MvPowerSeries (Fin (n + e)) ΛB),
          IsLocalRing.IsRegularSystemOfParameters (t.map h ++ z) := by
  classical
  let := coefficient_local c (fun hc ↦ (hzeroA hc).1) hposA
  let := coefficient_local c hzeroB hposB
  obtain ⟨hreg, hcomplete, hdim⟩ := regular_complete_dimension (A := ΛB) (n + e) c
    hzeroB hposB
  let := hreg
  let := hcomplete
  let j : Fin e ↪ Fin (n + e) := Fin.natAddEmb n
  let π := (killCompl (R := ΛB) j).toRingHom
  let ι := (rename (R := ΛB) j).toRingHom
  have hπι (F : MvPowerSeries (Fin e) ΛB) : π (ι F) = F :=
    killCompl_rename_app F
  have hsurj : Function.Surjective π := fun F ↦ ⟨ι F, hπι F⟩
  let hπlocal : IsLocalHom π := IsLocalHom.of_surjective π hsurj
  let hιlocal : IsLocalHom ι := ⟨fun F hF ↦ by
    apply isUnit_iff_constantCoeff.mpr
    rw [← constantCoeff_rename (f := j) F]
    exact isUnit_iff_constantCoeff.mp hF⟩
  have hYzero (i : Fin n) : π (X (Fin.castAdd e i)) = 0 := by
    apply killCompl_X_eq_zero
    rintro ⟨k, hk⟩
    have hv := congrArg Fin.val hk
    simp only [j, Fin.natAddEmb_apply, Fin.val_natAdd, Fin.val_castAdd] at hv
    omega
  let b : Fin n → MvPowerSeries (Fin (n + e)) ΛB :=
    fun i ↦ ι (φ (X i)) + X (Fin.castAdd e i)
  have hb (i : Fin n) : b i ∈ IsLocalRing.maximalIdeal _ :=
    Ideal.add_mem _
      (map_nonunit ι _ (map_nonunit φ _ (variable_mem_maximal i)))
      (variable_mem_maximal (Fin.castAdd e i))
  obtain ⟨h, hC, hX, hcont, _⟩ := exists_unique_adic_evaluation
    (ι.comp (φ.comp C)) (IsLocalRing.maximalIdeal _) n b hb
  have hcomp : π.comp h = φ := by
    obtain ⟨E, EC, EX, Econt, Euniq, _⟩ := exists_unique_adic_evaluation
      (φ.comp C) (IsLocalRing.maximalIdeal _) n (fun i ↦ φ (X i))
      (fun i ↦ map_nonunit φ _ (variable_mem_maximal i))
    have hφ : φ = E := Euniq φ (fun _ ↦ rfl) (fun _ ↦ rfl)
      (adic_continuous_of_variables n φ _
        (fun i ↦ map_nonunit φ _ (variable_mem_maximal i)))
    rw [hφ]
    apply Euniq (π.comp h)
    · intro a
      change π (h (C a)) = φ (C a)
      rw [hC]
      exact hπι _
    · intro i
      change π (h (X i)) = φ (X i)
      rw [hX]
      simp only [b, map_add, hπι, hYzero, add_zero]
    · apply adic_continuous_of_variables
      intro i
      change π (h (X i)) ∈ IsLocalRing.maximalIdeal _
      rw [hX]
      exact map_nonunit π _ (hb i)
  let hhlocal : IsLocalHom h := by
    have : IsLocalHom (π.comp h) := hcomp.symm ▸ inferInstance
    exact isLocalHom_of_comp h π
  refine ⟨hreg, hcomplete, π, h, hsurj, hπlocal, hhlocal, hcomp,
    List.ofFn (fun k : Fin e ↦ (X (j k) : MvPowerSeries (Fin (n + e)) ΛB)), ?_⟩
  let z := List.ofFn (fun k : Fin e ↦ (X (j k) : MvPowerSeries (Fin (n + e)) ΛB))
  let J : Ideal (MvPowerSeries (Fin (n + e)) ΛB) := Ideal.span {x | x ∈ t.map h ++ z}
  have hXt (i : Fin n) : (X i : MvPowerSeries (Fin n) ΛA) ∈ t := by
    rw [ht]
    split_ifs <;> simp
  have hhXmem (i : Fin n) : h (X i) ∈ J := by
    apply Ideal.subset_span
    exact List.mem_append_left _ (List.mem_map.mpr ⟨X i, hXt i, rfl⟩)
  have hZmem (k : Fin e) : (X (j k) : MvPowerSeries (Fin (n + e)) ΛB) ∈ J := by
    apply Ideal.subset_span
    apply List.mem_append_right
    simp [z]
  have hcJ (hc : c ≠ 0) : (c : MvPowerSeries (Fin (n + e)) ΛB) ∈ J := by
    have hct : (c : MvPowerSeries (Fin n) ΛA) ∈ t := by simp [ht, hc]
    have hcmem : h (c : MvPowerSeries (Fin n) ΛA) ∈ J :=
      Ideal.subset_span (List.mem_append_left _ (List.mem_map.mpr ⟨_, hct, rfl⟩))
    simpa using hcmem
  have hιmax : (IsLocalRing.maximalIdeal (MvPowerSeries (Fin e) ΛB)).map ι ≤ J := by
    apply mapped_maximal_le
    · exact coefficient_maximal_map_le c hzeroB hposB (ι.comp C) J hcJ
    · intro k
      simpa [ι] using hZmem k
  have hYmem (i : Fin n) : (X (Fin.castAdd e i) : MvPowerSeries (Fin (n + e)) ΛB) ∈ J := by
    have himem : ι (φ (X i)) ∈ J := hιmax
      (Ideal.mem_map_of_mem ι (map_nonunit φ _ (variable_mem_maximal i)))
    have hsub := Ideal.sub_mem J (hhXmem i) himem
    rw [hX] at hsub
    simpa [b] using hsub
  constructor
  · apply le_antisymm
    · apply Ideal.span_le.mpr
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
        apply map_nonunit h
        rw [ht] at ha
        split_ifs at ha with hc
        · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
          exact variable_mem_maximal i
        · rcases List.mem_cons.mp ha with rfl | ha
          · have hcA := hposA hc
            obtain ⟨_, hdom, hdvr, hmA, _⟩ := hcA
            have hcmem : (c : ΛA) ∈ IsLocalRing.maximalIdeal ΛA := by
              rw [hmA]
              exact Ideal.subset_span (Set.mem_singleton _)
            have hseries : (c : MvPowerSeries (Fin n) ΛA) ∈
                IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) ΛA) := by
              rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
                isUnit_iff_constantCoeff]
              simpa using hcmem
            exact hseries
          · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
            exact variable_mem_maximal i
      · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
        exact variable_mem_maximal (j k)
    · change IsLocalRing.maximalIdeal _ ≤ J
      rw [maximal_ideal_decomposition]
      apply sup_le
      · exact coefficient_maximal_map_le c hzeroB hposB C J hcJ
      · apply Ideal.span_le.mpr
        rintro _ ⟨k, rfl⟩
        exact Fin.addCases hYmem hZmem k
  · simp only [List.length_append, List.length_map, List.length_ofFn]
    rw [hdim, ht]
    split_ifs <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end MvPowerSeries

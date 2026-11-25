/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.Algebra.Field.ULift
import WeilConjectures.RingTheory.PolynomialCoefficientKernelRescaling
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Polynomial parameters with stable multiplication kernels

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ, items 10--12.
(blueprint: lem-weil-pbc-popescu-polynomial-kernel-parameters).
-/

@[expose] public section

set_option autoImplicit false

universe u v w
namespace Algebra

private theorem span_range_mul_units {R : Type u} [CommRing R] {ι : Type v}
    (f s : ι → R) (hs : ∀ i, IsUnit (s i)) :
    Ideal.span (Set.range (fun i ↦ s i * f i)) = Ideal.span (Set.range f) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    obtain ⟨s', hs'⟩ := hs i
    have hmem := Ideal.subset_span (s := Set.range (fun i ↦ s i * f i)) ⟨i, rfl⟩
    have h := Ideal.mul_mem_left _ (↑(s'⁻¹) : R) hmem
    simpa [← hs', ← mul_assoc] using h

private theorem regular_of_geometric
    {k : Type u} {A : Type w} [Field k] [CommRing A] [Algebra k A]
    (h : IsGeometricallyRegular k A) : IsRegularRing A := by
  let K := ULift.{w} k
  let E : K ≃ₐ[k] k := ULift.algEquiv
  have : Module.Finite k K := Module.Finite.of_surjective E.symm.toLinearMap E.symm.surjective
  have : IsPurelyInseparable k K := E.symm.isPurelyInseparable
  have : IsRegularRing (TensorProduct k K A) := h.2 K
  exact IsRegularRing.of_ringEquiv
    ((Algebra.TensorProduct.congr E (AlgEquiv.refl : A ≃ₐ[k] A)).trans
      (Algebra.TensorProduct.lid k A)).toRingEquiv

private theorem exists_local_parameter_numerators
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] [IsRegularLocalRing (Localization.AtPrime p)]
    (d : ℕ) (hd : ringKrullDim (Localization.AtPrime p) = (d : WithBot ℕ∞)) :
    ∃ f : Fin d → R, (∀ i, f i ∈ p) ∧
      Ideal.span (Set.range (fun i ↦ algebraMap R (Localization.AtPrime p) (f i))) =
        p.map (algebraMap R (Localization.AtPrime p)) := by
  classical
  let A := Localization.AtPrime p
  let m := IsLocalRing.maximalIdeal A
  have hrank : m.spanFinrank = d := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
    rw [hd] at h
    exact_mod_cast h
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (show (m : Submodule A A).FG from m.fg_of_isNoetherianRing)
  have hsd : s.card = d := hcard.trans hrank
  let g : Fin d → A := fun i ↦ (s.equivFinOfCardEq hsd).symm i
  have hgrange : Set.range g = (s : Set A) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ((s.equivFinOfCardEq hsd).symm i).2
    · intro hx
      exact ⟨(s.equivFinOfCardEq hsd) ⟨x, hx⟩, by simp [g]⟩
  choose f t hft using fun i ↦ IsLocalization.exists_mk'_eq p.primeCompl (g i)
  have hmem (i : Fin d) : f i ∈ p := by
    apply (IsLocalization.AtPrime.mk'_mem_maximal_iff A p (f i) (t i)).mp
    rw [hft i]
    change g i ∈ m
    rw [← hspan]
    exact Submodule.subset_span (hgrange ▸ Set.mem_range_self i)
  refine ⟨f, hmem, ?_⟩
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  change Ideal.span (Set.range (fun i ↦ algebraMap R A (f i))) = m
  have heq (i : Fin d) : algebraMap R A (f i) = algebraMap R A (t i) * g i := by
    rw [← hft i, mul_comm]
    exact (IsLocalization.mk'_spec A (f i) (t i)).symm
  simp_rw [heq]
  rw [span_range_mul_units g (fun i ↦ algebraMap R A (t i))
    (fun i ↦ IsLocalization.map_units A (t i)), hgrange]
  exact hspan

/-- Select polynomial representatives of the parameters and equalize the polynomial
multiplication kernels. Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ,
items `item-choose-pii` and `item-modify-pii`.
(blueprint: lem-weil-pbc-popescu-polynomial-kernel-parameters).

Proof: The field and its polynomial algebra are regular. Geometric regularity makes
L regular. The flat height formula applied to the local map with maximal ideal
extending to the maximal ideal of L gives dimension d for the source localization.
Choose d generators of its maximal ideal and write them as fractions. Their numerators
are in the contracted prime and still generate, since their denominators are units.
Their images generate the maximal ideal of L and are a regular sequence there.
All permutations of the source parameters are regular. Multiplying them by distinct
polynomial variables gives a regular sequence over the localized source polynomial
ring. Induct on the index i. Powers of the earlier terms followed by the current term
are regular after localization. Ogoma on the quotient by the earlier e-th powers
supplies a factor outside the contracted prime that equalizes the first and square
kernels before localization. Multiply only the current parameter by this factor.
Earlier kernels are unchanged, and the localized parameter ideals and regularity
are unchanged because the factor is a unit. For d=0 the parameter families are empty;
the dimension formula makes both maximal ideals zero and all kernel claims vacuous. -/
theorem exists_popescu_polynomial_kernel_parameters
    {k : Type u} {Λ : Type w}
    [Field k] [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ]
    (q : PrimeSpectrum Λ) (hreg : IsGeometricallyRegular k Λ)
    (d : ℕ) (hd : d =
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).spanFinrank)
    (e : ℕ) (he : 0 < e)
    (m₀ : ℕ) (φ₀ : MvPolynomial (Fin m₀) k →ₐ[k] Λ)
    (ψ₀ : Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) →+*
      Localization.AtPrime q.asIdeal)
    (hψ₀ : ψ₀.comp (algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom))) =
      (algebraMap Λ (Localization.AtPrime q.asIdeal)).comp φ₀.toRingHom)
    (hideal₀ : q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal)) =
      (q.asIdeal.comap φ₀.toRingHom).map
        ((algebraMap Λ (Localization.AtPrime q.asIdeal)).comp φ₀.toRingHom))
    (hflat₀ : ψ₀.Flat) :
    let P := MvPolynomial (Fin m₀) k
    let p₀ := q.asIdeal.comap φ₀.toRingHom
    let L := Localization.AtPrime q.asIdeal
    ∃ uP : Fin d → P,
      (∀ i, uP i ∈ p₀) ∧
      Ideal.span (Set.range (fun i ↦ algebraMap P (Localization.AtPrime p₀) (uP i))) =
        p₀.map (algebraMap P (Localization.AtPrime p₀)) ∧
      RingTheory.Sequence.IsRegular L
        (List.ofFn (fun i ↦ algebraMap Λ L (φ₀ (uP i)))) ∧
      (∀ (i : Fin d)
        (x : MvPolynomial (Fin d) P ⧸ Ideal.span
          {y | ∃ j : Fin d, j.val < i.val ∧
            y = (MvPolynomial.C (uP j) * MvPolynomial.X j) ^ e}),
        (MvPolynomial.C (uP i) * MvPolynomial.X i) • x = 0 ↔
          (MvPolynomial.C (uP i) * MvPolynomial.X i) ^ 2 • x = 0) := by
  classical
  let P := MvPolynomial (Fin m₀) k
  let p := q.asIdeal.comap φ₀.toRingHom
  let A := Localization.AtPrime p
  let L := Localization.AtPrime q.asIdeal
  have : IsRegularRing Λ := regular_of_geometric hreg
  have : IsRegularLocalRing L := inferInstance
  have : IsRegularLocalRing A := inferInstance
  have hmap : (IsLocalRing.maximalIdeal A).map ψ₀ = IsLocalRing.maximalIdeal L := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p A, Ideal.map_map, hψ₀]
    exact hideal₀.symm.trans (IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal L)
  have : IsLocalHom ψ₀ :=
    ((IsLocalRing.local_hom_TFAE ψ₀).out 3 1).mp (le_of_eq hmap)
  let : Algebra A L := ψ₀.toAlgebra
  have : Module.Flat A L := hflat₀
  have : (IsLocalRing.maximalIdeal L).LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap ψ₀).symm⟩
  have hheight := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal L)
  change (IsLocalRing.maximalIdeal L).height = (IsLocalRing.maximalIdeal A).height +
    ((IsLocalRing.maximalIdeal L).map
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map ψ₀))).height at hheight
  rw [hmap, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at hheight
  have hdimL : ringKrullDim L = (d : WithBot ℕ∞) := by
    rw [hd]
    exact IsRegularLocalRing.spanFinrank_maximalIdeal.symm
  have hdimA : ringKrullDim A = (d : WithBot ℕ∞) := by
    rw [← hdimL, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
      ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hheight]
  obtain ⟨f, hf, hspan⟩ := exists_local_parameter_numerators p d hdimA
  have hparameters : IsLocalRing.IsRegularSystemOfParameters
      (List.ofFn (fun i ↦ algebraMap P A (f i))) := by
    refine ⟨?_, ?_⟩
    · simpa only [List.mem_ofFn', Set.ofPred_mem_eq]
        using hspan.trans (IsLocalization.AtPrime.map_eq_maximalIdeal p A)
    · simpa using hdimA.symm
  have hperm : ∀ l : List A,
      (List.ofFn (fun i ↦ algebraMap P A (f i))).Perm l →
        RingTheory.Sequence.IsRegular A l := by
    intro l hl
    exact ((IsRegularLocalRing.isRegular_and_quotients_of_generators
      A d hdimA _ hparameters).2.2 l hl).2
  obtain ⟨s, hs, hkernel⟩ :=
    RingTheory.Sequence.exists_polynomial_coefficient_kernel_rescaling p d f hperm e he
  let uP : Fin d → P := fun i ↦ s i * f i
  have hspan' : Ideal.span (Set.range (fun i ↦ algebraMap P A (uP i))) =
      p.map (algebraMap P A) := by
    simp only [uP, map_mul]
    rw [span_range_mul_units (fun i ↦ algebraMap P A (f i))
      (fun i ↦ algebraMap P A (s i))
      (fun i ↦ IsLocalization.map_units A (⟨s i, hs i⟩ : p.primeCompl))]
    exact hspan
  have hspanL : Ideal.span (Set.range (fun i ↦ algebraMap Λ L (φ₀ (uP i)))) =
      IsLocalRing.maximalIdeal L := by
    have hmapped := congrArg (Ideal.map ψ₀) hspan'
    rw [Ideal.map_span, ← Set.range_comp', Ideal.map_map, hψ₀] at hmapped
    have heq (x : P) : ψ₀ (algebraMap P A x) = algebraMap Λ L (φ₀ x) :=
      DFunLike.congr_fun hψ₀ x
    simp_rw [heq] at hmapped
    exact hmapped.trans
      (hideal₀.symm.trans (IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal L))
  have hparametersL : IsLocalRing.IsRegularSystemOfParameters
      (List.ofFn (fun i ↦ algebraMap Λ L (φ₀ (uP i)))) := by
    refine ⟨?_, ?_⟩
    · simpa only [List.mem_ofFn', Set.ofPred_mem_eq] using hspanL
    · simpa using hdimL.symm
  refine ⟨uP, (fun i ↦ p.mul_mem_left (s i) (hf i)), hspan', ?_, hkernel⟩
  exact (IsRegularLocalRing.isRegular_and_quotients_of_generators
    L d hdimL _ hparametersL).1

end Algebra

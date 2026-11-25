/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoverFiberCount

/-!
# The rank of a finite totally ramified extension of discrete valuation rings

Let `R ⟶ S` be a finite extension of discrete valuation rings with the same residue field (the
residue map of `R` is surjective onto a field `K` and factors through `S`) in which a uniformizer
`U` of `R` becomes `w Ξ^e` for a unit `w` and a uniformizer `Ξ` of `S`. Then `S` is a flat (hence
free) `R`-module of rank `e` (`IsDiscreteValuationRing.flat_and_finrank_eq_of_algebraMap_eq`): the
sum of ramification indices times inertia degrees over the maximal ideal of `R` has the single
term `e · 1`.

This is used for the degree of the punctured diagonal in blueprint
`lemma-tangent-cones-on-cover` (ii).
-/

@[expose] public section

open IsLocalRing

namespace IsDiscreteValuationRing

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDiscreteValuationRing R]
  [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S] [Module.Finite R S]

omit [Module.Finite R S] in
/-- In a finite extension `R ⟶ S` of discrete valuation rings in which a uniformizer of `R`
becomes a unit times a power of a uniformizer of `S`, the algebra map is injective. -/
lemma algebraMap_injective_of_algebraMap_eq {U : R} (hU : Ideal.span {U} = maximalIdeal R)
    {Ξ w : S} (hΞ : Ideal.span {Ξ} = maximalIdeal S) (hw : IsUnit w) {e : ℕ}
    (he : algebraMap R S U = w * Ξ ^ e) : Function.Injective (algebraMap R S) := by
  rw [injective_iff_map_eq_zero]
  by_contra! h
  obtain ⟨a, ha, ha0⟩ := h
  have hker : RingHom.ker (algebraMap R S) ≠ ⊥ := fun h ↦ ha0 (by
    rw [← RingHom.mem_ker, h, Ideal.mem_bot] at ha
    exact ha)
  have hmax := IsPrime.to_maximal_ideal (hpi := RingHom.ker_isPrime (algebraMap R S)) hker
  have hUker : U ∈ RingHom.ker (algebraMap R S) := by
    rw [IsLocalRing.eq_maximalIdeal hmax, ← hU]
    exact Ideal.mem_span_singleton_self U
  rw [RingHom.mem_ker, he] at hUker
  rcases Nat.eq_zero_or_pos e with rfl | hpos
  · rw [pow_zero, mul_one] at hUker
    exact hw.ne_zero hUker
  have hΞ0 : Ξ = 0 := pow_eq_zero_iff (n := e) (by omega) |>.mp ((hw.mul_right_eq_zero).mp hUker)
  rw [hΞ0, Ideal.span_singleton_eq_bot.mpr rfl] at hΞ
  exact IsDiscreteValuationRing.not_a_field S hΞ.symm

/-- **The rank of a finite totally ramified extension of discrete valuation rings.** Let
`R ⟶ S` be a finite extension of discrete valuation rings, `evR : R ⟶ K` a surjection onto a
field factoring as `evS ∘ algebraMap` with `ker evS` the maximal ideal of `S`, and suppose a
uniformizer `U` of `R` becomes `w Ξ^e` for a unit `w` and a uniformizer `Ξ` of `S`, `e ≥ 1`.
Then `S` is flat over `R` of rank `e`. -/
theorem flat_and_finrank_eq_of_algebraMap_eq {K : Type*} [Field K] (evR : R →+* K)
    (hevR : Function.Surjective evR) (evS : S →+* K) (hS : evS.comp (algebraMap R S) = evR)
    (hkerS : RingHom.ker evS = maximalIdeal S) {U : R} (hU : Ideal.span {U} = maximalIdeal R)
    {Ξ w : S} (hΞ : Ideal.span {Ξ} = maximalIdeal S) (hw : IsUnit w) {e : ℕ} (he1 : 1 ≤ e)
    (he : algebraMap R S U = w * Ξ ^ e) :
    Module.Flat R S ∧ Module.finrank R S = e := by
  have hinj := algebraMap_injective_of_algebraMap_eq hU hΞ hw he
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  have : Module.Flat R S := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
      ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    infer_instance
  refine ⟨this, ?_⟩
  have hcomap : (maximalIdeal S).comap (algebraMap R S) = maximalIdeal R := by
    refine ((maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
    rw [← hU, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, he,
      ← hΞ]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self Ξ) e
      (by omega))
  have hliesOver : (maximalIdeal S).LiesOver (maximalIdeal R) := ⟨hcomap.symm⟩
  have huniq (q : Ideal S) (hq : q.IsPrime) (hlo : q.LiesOver (maximalIdeal R)) :
      q = maximalIdeal S := by
    refine IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) q ?_)
    rw [← Ideal.over_def q (maximalIdeal R)]
    exact maximalIdeal.isMaximal R
  have hset : (maximalIdeal R).primesOver S = {maximalIdeal S} :=
    Set.ext fun q ↦ ⟨fun hq ↦ huniq q hq.1 hq.2, fun h ↦ h ▸ ⟨inferInstance, hliesOver⟩⟩
  let : Fintype ((maximalIdeal R).primesOver S) :=
    (hset ▸ Set.finite_singleton (maximalIdeal S)).fintype
  rw [← Ideal.sum_ramification_inertia_eq_finrank (maximalIdeal R) S,
    Fintype.sum_eq_single ⟨maximalIdeal S, inferInstance, hliesOver⟩ fun q hq ↦
      (hq (Subtype.ext (huniq q.1 q.2.1 q.2.2))).elim]
  have hinert := RingHom.PointsOver.inertiaDeg_ker_eq_one_of_surjective hevR ⟨evS, hS⟩
  rw [hkerS] at hinert
  have hne : maximalIdeal S ≠ ⊥ := fun h ↦ IsDiscreteValuationRing.not_a_field S h
  have hmap : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ^ e := by
    rw [← hU, Ideal.map_span, Set.image_singleton, he, ← hΞ, Ideal.span_singleton_pow,
      Ideal.span_singleton_mul_left_unit hw]
  rw [hinert, mul_one,
    Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (maximalIdeal R) (maximalIdeal S)
    (by rw [hmap]; exact pow_ne_zero _ hne), hmap,
    multiplicity_pow_self_of_prime (Ideal.prime_of_isPrime hne inferInstance)]

end IsDiscreteValuationRing

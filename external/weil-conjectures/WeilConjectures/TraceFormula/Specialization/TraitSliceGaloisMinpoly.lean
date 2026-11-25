/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisSepClosed
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModel

/-!

# Minimal polynomials over `K((t))` of separable elements over `k'((t))`

Let `F ⊆ L` be fields such that `F` is separably closed in `L`. For every element `β` of an
extension `E` of `L` which is separable over `F`, the minimal polynomial of `β` over `L` is that
over `F` (`minpoly.map_algebraMap_of_isSeparable`): its coefficients are symmetric functions of
roots of a separable polynomial over `F`, hence separable over `F`, hence in `F`. Equivalently
`[L(β) : L] = [F(β) : F]`, i.e. `L ⊗_F F(β)` is a field.

For the slice of SGA 4½, [Th. finitude], Lemme 3.3 (`F = k'((t))`, `L = K((t))`,
`AlgebraicGeometry.separableClosure_traitLaurentField_eq_bot`) this is the linear disjointness of
`K((t))` and `k'((t))^sep` over `k'((t))`
(`AlgebraicGeometry.minpoly_traitLaurentField_eq_map`): the ring `K((t)) ⊗_{k'((t))} k'((t))^sep`
is a field.

-/

@[expose] public section

open Polynomial

/-- **Minimal polynomials do not change under extensions in which the base is separably closed**:
if every element of `L` separable over `F` lies in `F`, then for `β` separable over `F` the minimal
polynomial of `β` over `L` is the image of that over `F`. -/
theorem minpoly.map_algebraMap_of_isSeparable {F L E : Type*} [Field F] [Field L] [Field E]
    [Algebra F L] [Algebra L E] [Algebra F E] [IsScalarTower F L E]
    (hL : ∀ c : L, IsSeparable F c → c ∈ (algebraMap F L).range) {β : E}
    (hβ : IsSeparable F β) :
    (minpoly F β).map (algebraMap F L) = minpoly L β := by
  have hβi : IsIntegral F β := hβ.isIntegral
  have hβL : IsIntegral L β := hβi.tower_top
  refine minpoly.map_algebraMap hβi ?_
  set h := minpoly L β
  set Ω := AlgebraicClosure E
  have hdvd : h ∣ (minpoly F β).map (algebraMap F L) :=
    minpoly.dvd L β (by rw [aeval_map_algebraMap, minpoly.aeval])
  have hsplit : (h.map (algebraMap L Ω)).Splits := IsAlgClosed.splits _
  have hroots : ∀ r ∈ (h.map (algebraMap L Ω)).roots, r ∈ separableClosure F Ω := by
    intro r hr
    have hne : h.map (algebraMap L Ω) ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hβL)
    have hr' : Polynomial.aeval r (minpoly F β) = 0 := by
      have h1 := (mem_roots hne).mp hr
      have h2 : h.map (algebraMap L Ω) ∣ ((minpoly F β).map (algebraMap F L)).map
          (algebraMap L Ω) := Polynomial.map_dvd _ hdvd
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at h2
      rw [← eval_map_algebraMap]
      exact (dvd_iff_isRoot.mp (dvd_trans (dvd_iff_isRoot.mpr h1) h2))
    rw [mem_separableClosure_iff]
    exact Separable.of_dvd hβ (minpoly.dvd F r hr')
  have hlifts : h.map (algebraMap L Ω) ∈ lifts (algebraMap (separableClosure F Ω) Ω) := by
    rw [hsplit.eq_prod_roots_of_monic ((minpoly.monic hβL).map _), lifts_iff_liftsRing]
    refine Subring.multiset_prod_mem _ _ fun q hq ↦ ?_
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hq
    refine sub_mem ((lifts_iff_liftsRing _ _).mp (X_mem_lifts _))
      ((lifts_iff_liftsRing _ _).mp (C'_mem_lifts ⟨⟨r, hroots r hr⟩, rfl⟩))
  rw [lifts_iff_coeff_lifts]
  intro n
  apply hL
  obtain ⟨s, hs⟩ := (lifts_iff_coeff_lifts _).mp hlifts n
  rw [coeff_map] at hs
  apply IsSeparable.of_algHom F (IsScalarTower.toAlgHom F L Ω)
  rw [IsScalarTower.coe_toAlgHom', ← hs]
  exact mem_separableClosure_iff.mp s.2

universe u

namespace AlgebraicGeometry

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

/-- The embedding `Frac k'⟦t⟧ ⟶ Ω_K` (`AlgebraicGeometry.traitFractionFieldMap`) factors through
the embedding `Frac k'⟦t⟧ ⟶ Frac K⟦t⟧` of fraction fields. -/
lemma traitFractionFieldMap_eq_comp :
    traitFractionFieldMap k' K = (algebraMap (FractionRing (PowerSeries K))
      (traitGenericField K)).comp (traitLaurentFieldMap k' K) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (PowerSeries k')) (RingHom.ext fun a ↦ ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, traitLaurentFieldMap_algebraMap]
  rw [traitFractionFieldMap, IsFractionRing.lift_algebraMap, RingHom.comp_apply,
    ← IsScalarTower.algebraMap_apply]

variable [IsSepClosed k'] [IsAlgClosed K]

/-- **`K((t))` and `k'((t))^sep` are linearly disjoint over `k'((t))`**: for `k'` separably
closed and `K` algebraically closed of transcendence degree `≤ 1` over `k'`, the minimal polynomial
over `Frac K⟦t⟧` of an element `β` of an extension `E` of `Frac K⟦t⟧` which is separable over
`Frac k'⟦t⟧` is its minimal polynomial over `Frac k'⟦t⟧`. -/
theorem minpoly_traitLaurentField_eq_map (htr : Algebra.trdeg k' K ≤ 1) {E : Type*} [Field E]
    [Algebra (FractionRing (PowerSeries K)) E] (β : E) :
    letI := (traitLaurentFieldMap k' K).toAlgebra
    letI : Algebra (FractionRing (PowerSeries k')) E :=
      ((algebraMap (FractionRing (PowerSeries K)) E).comp (traitLaurentFieldMap k' K)).toAlgebra
    IsSeparable (FractionRing (PowerSeries k')) β →
      (minpoly (FractionRing (PowerSeries k')) β).map (traitLaurentFieldMap k' K) =
        minpoly (FractionRing (PowerSeries K)) β := by
  let := (traitLaurentFieldMap k' K).toAlgebra
  let : Algebra (FractionRing (PowerSeries k')) E :=
    ((algebraMap (FractionRing (PowerSeries K)) E).comp (traitLaurentFieldMap k' K)).toAlgebra
  have : IsScalarTower (FractionRing (PowerSeries k')) (FractionRing (PowerSeries K)) E :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  intro hβ
  exact minpoly.map_algebraMap_of_isSeparable
    (fun c hc ↦ mem_range_traitLaurentFieldMap_of_isSeparable htr c hc) hβ

end AlgebraicGeometry

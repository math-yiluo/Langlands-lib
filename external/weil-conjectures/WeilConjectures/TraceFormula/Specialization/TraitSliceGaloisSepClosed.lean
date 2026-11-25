/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.RatFunc.Basic
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSlice
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisField

/-!

# `k'((t))` is separably closed in `K((t))`

Let `k'` be a separably closed field and `K` an algebraically closed extension of transcendence
degree `≤ 1`, for instance the field `K = k'(x)^alg` of the generic slices
(`AlgebraicGeometry.traitSliceField`, `AlgebraicGeometry.trdeg_traitSliceField_le_one`). The
coefficientwise map `k'⟦t⟧ ⟶ K⟦t⟧` induces an embedding of fraction fields
`F = Frac k'⟦t⟧ ⟶ F_K = Frac K⟦t⟧` (`AlgebraicGeometry.traitLaurentFieldMap`). We prove that
every element of `F_K` separable over `F` lies in `F`
(`AlgebraicGeometry.mem_range_traitLaurentFieldMap_of_isSeparable`), i.e. the separable closure
of `F` in `F_K` is `F` (`AlgebraicGeometry.separableClosure_traitLaurentField_eq_bot`, and
`AlgebraicGeometry.separableClosure_traitSliceLaurentField_eq_bot` for `K = k'(x)^alg`).

Equivalently, `F_K ⊗_F F^sep` is a field and the restriction of Galois groups
`Gal(F_K^sep / F_K) ⟶ Gal(F^sep / F)` (both are inertia groups, the residue fields being separably
closed) is surjective: this is the surjectivity part of SGA 4½, [Th. finitude], Lemme 3.3, for
the slice `Spec K⟦t⟧ ⟶ 𝔸¹_S`. The proof reduces to the power series statement
`PowerSeries.exists_pow_mem_range_map_of_isRoot`: a simple root in `K⟦t⟧` of a polynomial over
`k'⟦t⟧` is purely inseparable over `k'⟦t⟧`; an element both separable and purely inseparable
over `F` lies in `F`.

-/

@[expose] public section

universe u

open Polynomial

namespace AlgebraicGeometry

section TraitLaurentField

variable (k' : Type u) [Field k'] (K : Type u) [Field K] [Algebra k' K]

/-- The coefficientwise map `k'⟦t⟧ ⟶ K⟦t⟧ ⟶ Frac K⟦t⟧` is injective. -/
lemma injective_algebraMap_fractionRing_comp_map :
    Function.Injective ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
      (PowerSeries.map (algebraMap k' K))) :=
  (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K))).comp
    (PowerSeries.map_injective _ (algebraMap k' K).injective)

/-- The embedding `F = Frac k'⟦t⟧ ⟶ F_K = Frac K⟦t⟧` of the fraction fields of the traits induced
by the coefficientwise map. -/
noncomputable def traitLaurentFieldMap :
    FractionRing (PowerSeries k') →+* FractionRing (PowerSeries K) :=
  IsFractionRing.lift (injective_algebraMap_fractionRing_comp_map k' K)

/-- The embedding of fraction fields extends the coefficientwise map. -/
lemma traitLaurentFieldMap_algebraMap (a : PowerSeries k') :
    traitLaurentFieldMap k' K (algebraMap _ _ a) =
      algebraMap _ _ (PowerSeries.map (algebraMap k' K) a) :=
  IsFractionRing.lift_algebraMap _ a

variable {k' K} [IsSepClosed k'] [IsAlgClosed K]

/-- **`k'((t))` is separably closed in `K((t))`**: for `k'` separably closed and `K`
algebraically closed of transcendence degree `≤ 1` over `k'`, every element of `Frac K⟦t⟧`
separable over `Frac k'⟦t⟧` lies in `Frac k'⟦t⟧`. -/
theorem mem_range_traitLaurentFieldMap_of_isSeparable (htr : Algebra.trdeg k' K ≤ 1)
    (α : FractionRing (PowerSeries K))
    (hα : letI := (traitLaurentFieldMap k' K).toAlgebra
      IsSeparable (FractionRing (PowerSeries k')) α) :
    α ∈ (traitLaurentFieldMap k' K).range := by
  let := (traitLaurentFieldMap k' K).toAlgebra
  have hα₀ : IsSeparable (FractionRing (PowerSeries k')) α := hα
  set ψ := algebraMap (FractionRing (PowerSeries k')) (FractionRing (PowerSeries K)) with hψ
  have hFL : ∀ x, ψ x = traitLaurentFieldMap k' K x := fun _ ↦ rfl
  set κ := algebraMap (PowerSeries k') (FractionRing (PowerSeries k'))
  have hκ : Function.Injective κ := IsFractionRing.injective _ _
  set φ := algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  set ι := PowerSeries.map (algebraMap k' K)
  have hsq : ψ.comp κ = φ.comp ι := by
    ext a : 1
    exact traitLaurentFieldMap_algebraMap k' K a
  -- clear the denominator of `α` by a power of `t`
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := PowerSeries K) α
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨w, hw, hbw⟩ := PowerSeries.exists_eq_X_pow_mul_isUnit hb0
  set v := b.order.toNat
  set s := κ (PowerSeries.X ^ v)
  have hs : ψ s = φ (PowerSeries.X ^ v) := by
    rw [hFL, traitLaurentFieldMap_algebraMap, map_pow, PowerSeries.map_X]
  have hs0 : s ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hκ]
    exact pow_ne_zero _ PowerSeries.X_ne_zero
  have hX' : φ (PowerSeries.X ^ v) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hφ]
    exact pow_ne_zero _ PowerSeries.X_ne_zero
  have hw' : φ w ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hφ]
    exact hw.ne_zero
  set a' := a * ↑hw.unit⁻¹
  set α' := φ a'
  have haw : α' * φ w = φ a := by
    rw [← map_mul]
    congr 1
    simp [a', mul_assoc]
  have hαα' : α' = ψ s * α := by
    rw [← hab, hs, hbw, map_mul, eq_comm, mul_div_assoc', div_eq_iff (mul_ne_zero hX' hw'),
      ← haw]
    ring
  -- `α'` is separable over `F = Frac k'⟦t⟧`
  have hsep : IsSeparable (FractionRing (PowerSeries k')) α' := by
    rw [← mem_separableClosure_iff, hαα']
    exact mul_mem (IntermediateField.algebraMap_mem _ s) (mem_separableClosure_iff.mpr hα₀)
  -- a polynomial over `k'⟦t⟧` with the simple root `a'`
  set μ := minpoly (FractionRing (PowerSeries k')) α'
  obtain ⟨c, hc, hcf⟩ := IsLocalization.integerNormalization_spec
    (nonZeroDivisors (PowerSeries k')) μ
  set f := IsLocalization.integerNormalization (nonZeroDivisors (PowerSeries k')) μ
  have hc0 : ψ (κ c) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ ψ.injective, map_eq_zero_iff _ hκ]
    exact nonZeroDivisors.ne_zero hc
  have hmapf : (f.map ι).map φ = C (ψ (κ c)) * μ.map ψ := by
    rw [Polynomial.map_map, ← hsq, ← Polynomial.map_map, hcf, Algebra.smul_def,
      Polynomial.map_mul, Polynomial.algebraMap_apply, Polynomial.map_C]
  have hroot : (f.map ι).IsRoot a' := by
    rw [IsRoot.def, ← map_eq_zero_iff _ hφ, PowerSeries.map_eval_eq, hmapf]
    rw [eval_mul, hψ, eval_map_algebraMap, minpoly.aeval, mul_zero]
  have hder : (f.map ι).derivative.eval a' ≠ 0 := by
    rw [Ne, ← map_eq_zero_iff _ hφ, PowerSeries.map_eval_eq, ← derivative_map, hmapf]
    simp only [derivative_C_mul, eval_mul, eval_C, derivative_map, hψ,
      eval_map_algebraMap, mul_eq_zero, not_or]
    exact ⟨hc0, hsep.aeval_derivative_ne_zero (minpoly.aeval _ α')⟩
  -- `α'` is purely inseparable over `F`
  obtain ⟨m, d, hd⟩ := PowerSeries.exists_pow_mem_range_map_of_isRoot (ringExpChar k') htr
    hroot hder
  have : ExpChar (FractionRing (PowerSeries k')) (ringExpChar k') :=
    expChar_of_injective_ringHom (f := κ.comp PowerSeries.C)
      (by rw [RingHom.coe_comp]; exact hκ.comp PowerSeries.C_injective) _
  have hperf : α' ∈ perfectClosure (FractionRing (PowerSeries k')) _ := by
    rw [mem_perfectClosure_iff_pow_mem (ringExpChar k')]
    refine ⟨m, κ d, ?_⟩
    change ψ (κ d) = _
    rw [hFL, traitLaurentFieldMap_algebraMap, hd, map_pow]
  have hbot : α' ∈ (⊥ : IntermediateField (FractionRing (PowerSeries k')) _) := by
    rw [← separableClosure_inf_perfectClosure]
    exact ⟨mem_separableClosure_iff.mpr hsep, hperf⟩
  obtain ⟨z, hz⟩ := IntermediateField.mem_bot.mp hbot
  refine ⟨z / s, ?_⟩
  rw [map_div₀, ← hFL, ← hFL]
  change ψ z / ψ s = α
  rw [hz, hαα', mul_div_cancel_left₀ _ ((_root_.map_ne_zero _).mpr hs0)]


/-- **The separable closure of `k'((t))` in `K((t))` is trivial.** -/
theorem separableClosure_traitLaurentField_eq_bot (htr : Algebra.trdeg k' K ≤ 1) :
    letI := (traitLaurentFieldMap k' K).toAlgebra
    separableClosure (FractionRing (PowerSeries k')) (FractionRing (PowerSeries K)) = ⊥ := by
  let := (traitLaurentFieldMap k' K).toAlgebra
  refine eq_bot_iff.mpr fun α hα ↦ IntermediateField.mem_bot.mpr ?_
  exact mem_range_traitLaurentFieldMap_of_isSeparable htr α (mem_separableClosure_iff.mp hα)

end TraitLaurentField

/-- The field `K = k'(x)^alg` of the generic slices has transcendence degree `≤ 1` over `k'`. -/
lemma trdeg_traitSliceField_le_one (k' : Type u) [Field k'] :
    Algebra.trdeg k' (traitSliceField k') ≤ 1 := by
  have h1 : Algebra.trdeg k' (RatFunc k') = 1 := by
    have := trdeg_add_eq (R := k') (S := Polynomial k') (A := RatFunc k')
    have h0 : Algebra.trdeg (Polynomial k') (RatFunc k') = 0 := by
      have := IsLocalization.isAlgebraic (RatFunc k') (nonZeroDivisors (Polynomial k'))
      exact trdeg_eq_zero
    rw [Polynomial.trdeg_of_isDomain, h0, add_zero] at this
    exact this.symm
  have := trdeg_add_eq (R := k') (S := RatFunc k') (A := traitSliceField k')
  rw [h1, trdeg_eq_zero (R := RatFunc k'), add_zero] at this
  exact this.symm.le

/-- **`k'((t))` is separably closed in `K((t))` for the generic slices** `K = k'(x)^alg`
(`AlgebraicGeometry.traitSliceField`), `k'` separably closed. -/
theorem separableClosure_traitSliceLaurentField_eq_bot (k' : Type u) [Field k'] [IsSepClosed k'] :
    letI := (traitLaurentFieldMap k' (traitSliceField k')).toAlgebra
    separableClosure (FractionRing (PowerSeries k'))
      (FractionRing (PowerSeries (traitSliceField k'))) = ⊥ :=
  separableClosure_traitLaurentField_eq_bot (trdeg_traitSliceField_le_one k')

end AlgebraicGeometry

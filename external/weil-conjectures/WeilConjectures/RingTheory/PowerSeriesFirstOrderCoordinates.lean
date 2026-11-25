/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.TrivSqZeroExt.Basic
import WeilConjectures.RingTheory.PowerSeriesQuadraticIdeal
import Mathlib.RingTheory.MvPowerSeries.Derivative

/-!
# Constant and linear coordinates on truncated power series

Source: Stacks Project, More on Algebra, Tag 07EI, construction of f₁.
(blueprint: lem-weil-pbc-power-series-first-order-coordinates).
-/

@[expose] public section

universe u v

namespace MvPowerSeries

/-- Constant and linear coefficients identify power series modulo the square of the
variables' ideal with a trivial square-zero extension. The variables' ideal is precisely
the subspace with zero first coordinate.
Source: Stacks Project, More on Algebra, Tag 07EI, construction of f₁.
(blueprint: lem-weil-pbc-power-series-first-order-coordinates)

Proof: Send a series f to (constantCoeff f, fun i ↦ coeff (Finsupp.single i 1) f).
The Cauchy product gives multiplication (c,v)(c',v') = (cc',cv' + c'v), so this
is a ring homomorphism to the trivial square-zero extension. It is surjective:
(c,v) is the image of C(c) + sum_i C(v_i) X_i. Its kernel is N². Indeed products
of two variables have zero constant and linear coefficients, so N² lies in the
kernel. Conversely order the finite variable set. For every monomial of total
degree at least two, choose its first two variable factors, allowing repetition.
Group the coefficients according to this pair and remove those two factors.
This gives finitely many well-defined series f_ij and the equality
f = sum_ij X_i X_j f_ij whenever the constant and linear terms of f vanish.
Thus f belongs to N². The first isomorphism theorem supplies e. Every element
of N has zero constant coefficient; conversely a class with zero first coordinate
has representative sum_i C(v_i) X_i, which belongs to N. This proves the stated
ideal membership criterion. For an empty variable set N = 0 and the constant
coefficient map itself is an isomorphism. -/
theorem exists_firstOrder_coordinates (σ : Type u) [Finite σ] (K : Type v) [Field K] :
    let T := MvPowerSeries σ K
    let N : Ideal T := Ideal.span (Set.range (fun i ↦ (X i : T)))
    ∃ e : (T ⧸ N ^ 2) ≃+* TrivSqZeroExt K (σ → K),
      ∀ q : T ⧸ N ^ 2, q ∈ N.map (Ideal.Quotient.mk (N ^ 2)) ↔ (e q).fst = 0 := by
  classical
  let := Fintype.ofFinite σ
  let T := MvPowerSeries σ K
  let N : Ideal T := Ideal.span (Set.range (fun i ↦ (X i : T)))
  have hmul (i : σ) (f g : T) :
      coeff (Finsupp.single i 1) (f * g) =
        constantCoeff f * coeff (Finsupp.single i 1) g +
          constantCoeff g * coeff (Finsupp.single i 1) f := by
    have hc (p : T) : constantCoeff (pderiv (R := K) i p) = coeff (Finsupp.single i 1) p := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
      simp only [zero_add, Finsupp.zero_apply, Nat.cast_zero, mul_one]
    have h := congrArg (constantCoeff (σ := σ)) ((pderiv (R := K) i).leibniz f g)
    simpa only [map_add, smul_eq_mul, map_mul, hc] using h
  let jet : T →+* TrivSqZeroExt K (σ → K) :=
    { toFun := fun f ↦ ⟨constantCoeff f, fun i ↦ coeff (Finsupp.single i 1) f⟩
      map_one' := by
        apply TrivSqZeroExt.ext
        · simp
        · funext i
          simp [coeff_one]
      map_mul' := fun f g ↦ by
        apply TrivSqZeroExt.ext
        · exact map_mul constantCoeff f g
        · funext i
          simpa only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mk,
            TrivSqZeroExt.snd_mk, op_smul_eq_smul, Pi.add_apply, Pi.smul_apply,
            smul_eq_mul] using hmul i f g
      map_zero' := by
        apply TrivSqZeroExt.ext
        · simp
        · funext i
          simp
      map_add' := fun f g ↦ by
        apply TrivSqZeroExt.ext
        · exact map_add constantCoeff f g
        · funext i
          exact map_add (coeff (Finsupp.single i 1)) f g }
  have hN : N ≤ RingHom.ker (constantCoeff (σ := σ) (R := K)) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact constantCoeff_X i
  have hN2 : N ^ 2 ≤ RingHom.ker jet := by
    rw [pow_two, Ideal.mul_le]
    intro f hf g hg
    have hf0 : constantCoeff f = 0 := hN hf
    have hg0 : constantCoeff g = 0 := hN hg
    change jet (f * g) = 0
    rw [map_mul]
    apply TrivSqZeroExt.ext
    · change constantCoeff f * constantCoeff g = 0
      simp [hf0]
    · change constantCoeff f • (fun i ↦ coeff (Finsupp.single i 1) g) +
        (MulOpposite.op (constantCoeff g)) • (fun i ↦ coeff (Finsupp.single i 1) f) = 0
      simp [hf0, hg0]
  let normal (x : TrivSqZeroExt K (σ → K)) : T :=
    C x.fst + ∑ i : σ, C (x.snd i) * X i
  have hnormal (x : TrivSqZeroExt K (σ → K)) : jet (normal x) = x := by
    apply TrivSqZeroExt.ext
    · change constantCoeff (normal x) = x.fst
      simp [normal, constantCoeff_X]
    · funext i
      change coeff (Finsupp.single i 1) (normal x) = x.snd i
      simp [normal, map_sum, coeff_C_mul, coeff_index_single_X, coeff_C]
  let jq : (T ⧸ N ^ 2) →+* TrivSqZeroExt K (σ → K) :=
    Ideal.Quotient.lift (N ^ 2) jet (fun f hf ↦ hN2 hf)
  have hjq : Function.Bijective jq := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro q hq
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
      rw [Ideal.Quotient.eq_zero_iff_mem]
      apply mem_span_X_sq_of_coeff_eq_zero σ K f
      · exact congrArg TrivSqZeroExt.fst hq
      · intro i
        exact congrFun (congrArg TrivSqZeroExt.snd hq) i
    · intro x
      exact ⟨Ideal.Quotient.mk (N ^ 2) (normal x), hnormal x⟩
  let e := RingEquiv.ofBijective jq hjq
  refine ⟨e, fun q ↦ ?_⟩
  constructor
  · intro hq
    obtain ⟨f, hf, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hq
    exact hN hf
  · intro hq
    have hn : normal (e q) ∈ N := by
      dsimp only [normal]
      rw [hq, map_zero, zero_add]
      apply Submodule.sum_mem
      intro i _
      exact Ideal.mul_mem_left N _ (Ideal.subset_span ⟨i, rfl⟩)
    have he : Ideal.Quotient.mk (N ^ 2) (normal (e q)) = q := by
      apply e.injective
      exact hnormal (e q)
    rw [← he]
    exact Ideal.mem_map_of_mem _ hn

end MvPowerSeries

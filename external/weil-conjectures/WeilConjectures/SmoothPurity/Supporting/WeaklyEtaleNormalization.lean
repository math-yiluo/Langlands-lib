/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import WeilConjectures.RingTheory.Excellent
public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Algebra.Pi
import WeilConjectures.RingTheory.ProEtale.WeakDimension
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions

set_option linter.privateModule false

/-!
# Normalization tensor decomposition for a local weakly etale map

Source: Silvio Greco, *Two theorems on excellent rings*, Nagoya Math. J. 60 (1976),
Lemma 5.5 proof, first two sentences (blueprint: lem-exc-weakly-etale-normalization-tensor).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct
open Algebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private theorem generic_fractions
    (C D : Type*) [CommRing C] [IsDomain C] [CommRing D] [Algebra C D]
    [Algebra.WeaklyEtale C D] :
    IsFractionRing D (FractionRing C ⊗[C] D) ∧ IsReduced D := by
  let T := FractionRing C ⊗[C] D
  let : CommRing T := inferInstance
  let : Algebra D T := Algebra.TensorProduct.rightAlgebra
  let S := Algebra.algebraMapSubmonoid D (nonZeroDivisors C)
  have hS : S ≤ nonZeroDivisors D := by
    rintro _ ⟨s, hs, rfl⟩
    apply mem_nonZeroDivisors_iff_right.mpr
    intro d hd
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors (M := D) hs (by
      simpa [Algebra.smul_def, mul_comm] using hd)
  have : IsLocalization S T := inferInstance
  have hinj : Function.Injective (algebraMap D T) := IsLocalization.injective T hS
  have habs : Ring.AbsolutelyFlat T :=
    Ring.AbsolutelyFlat.of_flat_lmul' (FractionRing C) T
      (Algebra.WeaklyEtale.flat_lmul' (FractionRing C) T)
  have htfae : Ring.AbsolutelyFlat T ↔
      IsReduced T ∧ ∀ P : Ideal T, P.IsPrime → P.IsMaximal :=
    (Ring.AbsolutelyFlat.tfae T).out 1 2
  have : IsReduced T := (htfae.mp habs).1
  have hred : IsReduced D := isReduced_of_injective (algebraMap D T) hinj
  refine ⟨?_, hred⟩
  apply IsLocalization.of_le S (nonZeroDivisors D) hS
  intro d hd
  have hr : IsRegular (algebraMap D T d) := by
    simpa only [IsLocalization.mk'_one] using
      (IsLocalization.isRegular_mk' (S := T) (M := S)
        (fun s hs ↦ isRegular_iff_mem_nonZeroDivisors.mpr (hS hs))
        (r := d) (m := (1 : S))).mpr (isRegular_iff_mem_nonZeroDivisors.mpr hd)
  obtain ⟨b, hb⟩ := Ring.AbsolutelyFlat.exists_eq_mul_self_mul (algebraMap D T d)
  apply isUnit_iff_exists_inv.mpr
  refine ⟨b, ?_⟩
  apply hr.left
  simpa only [mul_one, mul_assoc] using hb.symm

private theorem tensor_normalization_cancel
    (R A K D : Type*) [CommRing R] [CommRing A] [CommRing K] [CommRing D]
    [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K] [Algebra R D] :
    ∃ e : ((A ⊗[R] D) ⊗[A] K) ≃+* K ⊗[R] D,
      ∀ a d k, e ((a ⊗ₜ[R] d) ⊗ₜ[A] k) = (algebraMap A K a * k) ⊗ₜ[R] d := by
  let ec := Algebra.TensorProduct.comm A (A ⊗[R] D) K
  let eb := Algebra.TensorProduct.cancelBaseChange R A K K D
  let e := ec.toRingEquiv.trans eb.toRingEquiv
  refine ⟨e, ?_⟩
  intro a d k
  change eb (ec ((a ⊗ₜ[R] d) ⊗ₜ[A] k)) = _
  simp [ec, eb, Algebra.smul_def]

private theorem tensor_clear_denominator
    (R K D : Type*) [CommRing R] [CommRing K] [CommRing D]
    [Algebra R K] [Algebra R D] (x : K) (a s : R)
    (h : algebraMap R K s * x = algebraMap R K a) (d : D) :
    x ⊗ₜ[R] (algebraMap R D s * d) = (1 : K) ⊗ₜ[R] (algebraMap R D a * d) := by
  rw [← Algebra.smul_def s d, ← Algebra.smul_def a d]
  rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul]
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  rw [Algebra.smul_def, Algebra.smul_def, h]
  rw [mul_one]

private theorem normalization_comparison
    (C D : Type*) [CommRing C] [IsDomain C] [CommRing D] [Algebra C D]
    [Algebra.WeaklyEtale C D] :
    ∃ e : (integralClosure C (FractionRing C) ⊗[C] D) ≃ₐ[D]
        integralClosure D (FractionRing D),
      ∀ (c : integralClosure C (FractionRing C)) (a s : C), s ≠ 0 →
        algebraMap C (FractionRing C) s * c.val = algebraMap C (FractionRing C) a →
        ∀ d : D,
          algebraMap D (FractionRing D) (algebraMap C D s) * (e (c ⊗ₜ[C] d)).val =
            algebraMap D (FractionRing D) (algebraMap C D a * d) := by
  let K := FractionRing C
  let : Field K := inferInstance
  let : Algebra C K := inferInstance
  let A : Type _ := integralClosure C K
  let : CommRing A := inferInstance
  let : Algebra C A := inferInstance
  let : Algebra A K := inferInstance
  have : IsScalarTower C A K := inferInstance
  let H := A ⊗[C] D
  let : CommRing H := inferInstance
  let : Algebra A H := inferInstance
  let : Algebra D H := Algebra.TensorProduct.rightAlgebra
  let U := H ⊗[A] K
  let : CommRing U := inferInstance
  let : Algebra H U := inferInstance
  let : Algebra D U := inferInstance
  let T := K ⊗[C] D
  let : CommRing T := inferInstance
  let : Algebra D T := Algebra.TensorProduct.rightAlgebra
  have : IsFractionRing D T := (generic_fractions C D).1
  have : IsFractionRing A K := integralClosure.isFractionRing_of_finite_extension K K
  have : Algebra.IsAlgebraic A K :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := K)).mpr inferInstance
  have : IsIntegrallyClosedIn H U :=
    Algebra.WeaklyEtale.isIntegrallyClosedIn_tensorProduct A H K
  have : Algebra.IsIntegral D H := by
    let e : H ≃ₐ[D] D ⊗[C] A :=
      AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm C A D).toRingEquiv)
        (fun d ↦ by
          change (Algebra.TensorProduct.comm C A D) (1 ⊗ₜ[C] d) = d ⊗ₜ[C] 1
          simp)
    exact e.isIntegral_iff.mpr inferInstance
  have : IsIntegralClosure H D U := IsIntegralClosure.of_isIntegrallyClosedIn
  obtain ⟨e₀, he₀⟩ := tensor_normalization_cancel C A K D
  let e₁ : U ≃ₐ[D] T := AlgEquiv.ofRingEquiv (f := e₀) (by
    intro d
    change e₀ ((1 ⊗ₜ[C] d) ⊗ₜ[A] (1 : K)) = (1 : K) ⊗ₜ[C] d
    rw [he₀]
    simp)
  let e₂ : U ≃ₐ[D] FractionRing D :=
    e₁.trans (IsLocalization.algEquiv (nonZeroDivisors D) T (FractionRing D))
  let e : H ≃ₐ[D] integralClosure D (FractionRing D) :=
    (IsIntegralClosure.equiv D H U (integralClosure D U)).trans e₂.mapIntegralClosure
  refine ⟨e, ?_⟩
  intro c a s hs hsc d
  have hc : algebraMap C A s * c = algebraMap C A a := by
    apply Subtype.ext
    exact hsc
  have hH : algebraMap D H (algebraMap C D s) * (c ⊗ₜ[C] d) =
      algebraMap D H (algebraMap C D a * d) := by
    change ((1 : A) ⊗ₜ[C] algebraMap C D s) * (c ⊗ₜ[C] d) =
      (1 : A) ⊗ₜ[C] (algebraMap C D a * d)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact tensor_clear_denominator C A D c a s hc d
  have he := congrArg e hH
  rw [map_mul, e.commutes, e.commutes] at he
  exact congrArg Subtype.val he

end

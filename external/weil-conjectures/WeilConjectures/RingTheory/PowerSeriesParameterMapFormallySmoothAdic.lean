/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import WeilConjectures.RingTheory.CohenRing
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.RingTheory.MvPowerSeries.Basic
import WeilConjectures.RingTheory.FormallySmoothAdicSmallKernelCriterion
import WeilConjectures.RingTheory.PowerSeriesParameterPreservingRingLift
import WeilConjectures.RingTheory.ClosedFiberDefectDerivationExtension

/-! # Formal smoothness of parameter-preserving power-series maps

Source: Stacks Project, Tag 07NQ, final lifting argument after the base-change reduction.
(blueprint: lem-weil-pbc-power-series-parameter-map-fs-adic)
-/

@[expose] public section

universe u v

open IsLocalRing

namespace MvPowerSeries

/-- A map between field or Cohen power-series rings carrying parameters into parameters
is adically formally smooth if its closed fibre is. No arbitrary complete local rings or
flat maps occur in this criterion: it is the coordinate lifting step of Tag 07NQ.

Source: Stacks Project, Tag 07NQ, proof of (2) implies (3), last paragraphs from
"Choose elements y" through the correction psi' = psi - D'.
(blueprint: lem-weil-pbc-power-series-parameter-map-fs-adic)

Proof:
1. For a continuous square-zero lifting problem T -> N/J over R, the quotient map
makes J a T-module because J^2 = 0. If the map kills m_T^e then m_T^e J = 0.
Filter J by J_a = {j : m_T^a j = 0}. The successive quotients are annihilated by m_T.
Descend from N/J_e to N/J_0. A lift killing m_T^b modulo a square-zero kernel kills
m_T^(2b), so every stage remains continuous. The action on the next kernel is the
original action since changing representatives by J has zero product with J.
2. Thus assume m_T J = 0, making J a vector space over the residue field K of T.
Tag 07NM gives coordinates t,y (with p omitted as a variable in the Cohen case).
Tag 07NL gives an unrestricted lift over Q or Z. In characteristic zero N is a
Q-algebra: integers are units modulo J, and a unit modulo a square-zero ideal lifts
to a unit. Keep the coefficient map and change the t-variable values to their
prescribed images from R; the variable images are nilpotent, so evaluation uses
finite truncations. The new lift agrees on all parameters of R, including p.
3. Its defect on R is a derivation into J, annihilating the parameters. The universal
property of differentials and the exact quotient differential sequence make it
factor through Omega_(k/Z), where k is the residue field of R: the R-action on J
factors through k, and the differentials of the parameters generate the conormal
image. Tensor this k-linear map with K.
4. Formal smoothness of the closed fibre gives injectivity of
Omega_(k/Z) tensor_k K -> Omega_(T/m_R T / Z) tensor_T K by Tag 07EL.
Extend the defect functional along this injection by extending a vector-space basis.
Compose with the differential of T -> T/m_R T to obtain a derivation D' on T
whose restriction to R is the defect. Subtract D' from the unrestricted lift.
Leibniz and J^2 = 0 prove multiplicativity; derivations kill 1. The correction
vanishes modulo J and cancels the defect on R, so the corrected lift is R-linear.
Apply this at every stage of the filtration in step 1. This solves all lifting problems.
Empty parameter lists and the case J = 0 require no parameter correction.
-/
theorem formallySmoothAdic_of_parameters_closedFiber
    (ΛR : Type u) (ΛT : Type v) [CommRing ΛR] [CommRing ΛT] (n m : ℕ)
    [IsRegularLocalRing (MvPowerSeries (Fin n) ΛR)]
    [IsRegularLocalRing (MvPowerSeries (Fin m) ΛT)]
    (i : MvPowerSeries (Fin n) ΛR →+* MvPowerSeries (Fin m) ΛT) [IsLocalHom i]
    (t : List (MvPowerSeries (Fin n) ΛR))
    (y : List (MvPowerSeries (Fin m) ΛT))
    (ht : IsRegularSystemOfParameters t)
    (hy : IsRegularSystemOfParameters (t.map i ++ y))
    (hcoeff : (IsField ΛR ∧ IsField ΛT ∧ CharZero ΛR ∧ CharZero ΛT) ∨
      ∃ p : ℕ, p.Prime ∧ IsCohenRing p ΛR ∧ IsCohenRing p ΛT ∧
        t.head? = some (p : MvPowerSeries (Fin n) ΛR)) :
    let R := MvPowerSeries (Fin n) ΛR
    let T := MvPowerSeries (Fin m) ΛT
    letI : Algebra R T := i.toAlgebra
    let L : Ideal T := (maximalIdeal R).map i
    letI : Algebra (R ⧸ maximalIdeal R) (T ⧸ L) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map :
        maximalIdeal R ≤ L.comap (algebraMap R T))
    Algebra.FormallySmoothAdic (R ⧸ maximalIdeal R) (T ⧸ L)
        ((maximalIdeal T).map (Ideal.Quotient.mk L)) →
      Algebra.FormallySmoothAdic R T (maximalIdeal T) := by
  dsimp only
  let R := MvPowerSeries (Fin n) ΛR
  let T := MvPowerSeries (Fin m) ΛT
  let : Algebra R T := i.toAlgebra
  intro hclosed
  apply Algebra.formallySmoothAdic_of_smallKernel_lifts R T (maximalIdeal T)
  intro D _ _ J hJ g hg hsmall
  obtain ⟨f, hf, hft⟩ := exists_parameterPreserving_ringLift ΛR ΛT n m i t y
    hy hcoeff D J hJ g hg
  obtain ⟨δ, hδone, hδmem, hδmul, hδbase⟩ :=
    Algebra.exists_closedFiber_defect_derivation R T t ht.1 hclosed
      D J hJ g f hf hft hsmall
  have hδprod (x z : T) : δ x * δ z = 0 := by
    have hmem : δ x * δ z ∈ J ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (hδmem x) (hδmem z)
    simpa only [hJ, Ideal.mem_bot] using hmem
  let l : T →ₐ[R] D :=
    { toFun := fun x ↦ f x - δ x
      map_zero' := by simp
      map_one' := by simp [hδone]
      map_add' := fun x z ↦ by simp only [map_add]; ring
      map_mul' := fun x z ↦ by
        simp only [map_mul, hδmul]
        linear_combination -(hδprod x z)
      commutes' := fun r ↦ by
        change f (algebraMap R T r) - δ (algebraMap R T r) = algebraMap R D r
        rw [hδbase]
        ring }
  refine ⟨l, ?_⟩
  ext x
  change Ideal.Quotient.mk J (f x - δ x) = g x
  rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr (hδmem x), sub_zero]
  exact RingHom.congr_fun hf x

end MvPowerSeries

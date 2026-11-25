/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RamificationInertia.Inertia

import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.RingTheory.DvrNormalizedCompositumLocalDiagram
import WeilConjectures.RingTheory.DvrAbhyankarLocalMaximalIdeal

/-! # Abhyankar's index-one conclusion for normalized tensor factors

Source: Stacks Project, Tags 0BRM, 09EM and 09E7.
(blueprint: lem-sbc-dvr-abhyankar-normalized-factor-index-one) -/

@[expose] public section
universe u
open scoped TensorProduct
namespace RingTheory

private theorem isSeparable_of_isUnit_finrank
    (k l : Type u) [Field k] [Field l] [Algebra k l] [FiniteDimensional k l]
    (h : IsUnit (Module.finrank k l : k)) : Algebra.IsSeparable k l := by
  apply (isSeparable_iff_finInsepDegree_eq_one k l).2
  have aux (q : ℕ) [hq : ExpChar k q] : Field.finInsepDegree k l = 1 := by
    obtain ⟨r, hr⟩ := finInsepDegree_eq_pow k l q
    cases hq with
    | zero => simpa using hr
    | @prime q hp hchar =>
      have hnot : ¬ q ∣ Module.finrank k l := by
        intro hd
        have hz : (Module.finrank k l : k) = 0 := by
          obtain ⟨d, hd⟩ := hd
          rw [hd, Nat.cast_mul, CharP.cast_eq_zero, zero_mul]
        exact h.ne_zero hz
      have hdiv : Field.finInsepDegree k l ∣ Module.finrank k l :=
        ⟨Field.finSepDegree k l, by rw [mul_comm, Field.finSepDegree_mul_finInsepDegree]⟩
      cases r with
      | zero => simpa using hr
      | succ r => exact False.elim (hnot ((dvd_pow_self _ (Nat.succ_ne_zero r)).trans
          (hr ▸ hdiv)))
  exact aux (ringExpChar k)

private theorem ramificationIdx_eq_one_of_map_maximalIdeal
    (A S : Type u) [CommRing A] [IsLocalRing A] [CommRing S] [Algebra A S]
    (Q : Ideal S) [Q.IsPrime]
    (hQ : Q.comap (algebraMap A S) = IsLocalRing.maximalIdeal A)
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A (Localization.AtPrime Q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q)) : Q.ramificationIdx A = 1 := by
  rw [Ideal.ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom,
    ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff]
  simpa only [Ideal.under_def, hQ] using hmax

/-- Sufficient divisibility of the base index kills tame ramification.

Source: Stacks Project, Tags 0BRM (lemma-abhyankar), 09EM and 09E7.
(blueprint: lem-sbc-dvr-abhyankar-normalized-factor-index-one)

Proof: The field map E -> F and injective A -> F identify the two B-maps,
so B embeds in A. Since A is finite and normal, it is the normalization of B
in its fraction field. The field F is a factor of E tensor Frac(A) over
Frac(B), by inverting the nonzero elements of B. The finite normalization C
is Dedekind; at the contraction R of Q its localization is a DVR. This
contraction lies over the closed point of B. Its ramification index divides r,
which is invertible in B. Its residue degree also divides r, so its inseparable
degree (a power of the residue characteristic) is one. Thus C_R/B is tame.
The maximal-ideal power identity gives base ramification index n, divisible
by r and hence by the index at R. Apply 0BRM to C_R/B and Frac(A)/Frac(B).
Integrality transitivity and localization of integral closure (09EM) identify
the resulting local normalized tensor factor with S_Q. Its adic formal
smoothness gives ramification index one by 09E7. The length definition of
ramificationIdx agrees with this DVR index. No bound for a partially
ramified base extension is used. -/
theorem dvr_abhyankar_normalized_factor_ramificationIdx_eq_one
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (n : ℕ) (hnpos : 0 < n) (r : ℕ) (hrpos : 0 < r) (hr : IsUnit (r : B))
    (hrn : r ∣ n)
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra B A] [Module.Finite B A]
    (hindex : (IsLocalRing.maximalIdeal B).map (algebraMap B A) =
      IsLocalRing.maximalIdeal A ^ n)
    (E : Type u) [Field E] [Algebra (FractionRing B) E]
    (hE : FiniteDimensional (FractionRing B) E ∧ Algebra.IsSeparable (FractionRing B) E) :
    letI : Algebra B E :=
      ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
    let C := integralClosure B E
    Module.Finite B C →
    (∀ (R : Ideal C) (hR : R.IsPrime),
      letI := hR
      R.comap (algebraMap B C) = IsLocalRing.maximalIdeal B →
        R.ramificationIdx B ∣ r ∧ R.inertiaDeg B ∣ r) →
    let D := E ⊗[B] A
    ∀ (P : Ideal D) (hP : P.IsMaximal),
    let := hP
    let F := D ⧸ P
    let alpha : A →+* F := (Ideal.Quotient.mk P).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[B] D).toRingHom
    letI := alpha.toAlgebra
    Function.Injective alpha →
    let S := integralClosure A F
    Module.Finite A S →
    ∀ (Q : Ideal S) (hQ : Q.IsPrime),
    let := hQ
    Q.comap (algebraMap A S) = IsLocalRing.maximalIdeal A →
      Q.ramificationIdx A = 1 := by
  have _ := hrpos
  let : Algebra B E :=
    ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
  let C := integralClosure B E
  dsimp only
  intro hC hdiv P hP
  let := hP
  let D := E ⊗[B] A
  let F := D ⧸ P
  let : Field F := Ideal.Quotient.field P
  let alpha : A →+* F := (Ideal.Quotient.mk P).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[B] D).toRingHom
  let := alpha.toAlgebra
  intro hinj hfinite Q hQ hQover
  let := hfinite
  let := hQ
  let : FiniteDimensional (FractionRing B) E := hE.1
  let : Algebra.IsSeparable (FractionRing B) E := hE.2
  have : IsScalarTower B (FractionRing B) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite B C := hC
  have htame : ∀ (R : Ideal C) (hR : R.IsPrime),
      let := hR
      R.comap (algebraMap B C) = IsLocalRing.maximalIdeal B →
      let := Localization.AtPrime.algebraOfLiesOver (R.under B) R
      IsUnit (R.ramificationIdx B : B) ∧ R.ramificationIdx B ∣ n ∧
        Algebra.IsSeparable (R.under B).ResidueField R.ResidueField := by
    dsimp only
    intro R hR hRover
    let := hR
    let := Localization.AtPrime.algebraOfLiesOver (R.under B) R
    obtain ⟨he, hf⟩ := hdiv R hR hRover
    refine ⟨isUnit_of_dvd_unit (Nat.cast_dvd_cast he) hr, he.trans hrn, ?_⟩
    apply isSeparable_of_isUnit_finrank
    rw [← Ideal.inertiaDeg_def]
    have hu : IsUnit (R.inertiaDeg B : B) :=
      isUnit_of_dvd_unit (Nat.cast_dvd_cast hf) hr
    simpa only [map_natCast] using hu.map (algebraMap B (R.under B).ResidueField)
  let iE : E →+* F := (Ideal.Quotient.mk P).comp
    (Algebra.TensorProduct.includeLeft : E →ₐ[B] D).toRingHom
  have hcomm : ∀ b : B, iE (algebraMap B E b) =
      algebraMap A F (algebraMap B A b) := by
    intro b
    change Ideal.Quotient.mk P
      (Algebra.TensorProduct.includeLeft (algebraMap B E b)) =
      Ideal.Quotient.mk P (Algebra.TensorProduct.includeRight (algebraMap B A b))
    rw [AlgHom.commutes, AlgHom.commutes]
  have hinjBE : Function.Injective (algebraMap B E) :=
    (algebraMap (FractionRing B) E).injective.comp
      (IsFractionRing.injective B (FractionRing B))
  have hinjBA : Function.Injective (algebraMap B A) := by
    intro x y hxy
    apply hinjBE
    apply iE.injective
    rw [hcomm, hcomm, hxy]
  have : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).2 hinjBA
  have hgen : Algebra.adjoin A (Set.range iE) = ⊤ := by
    apply top_unique
    intro z hz
    clear hz
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction x using TensorProduct.inductionOn with
    | tmul e a =>
      have he : iE e ∈ Algebra.adjoin A (Set.range iE) :=
        Algebra.subset_adjoin ⟨e, rfl⟩
      have ha := (Algebra.adjoin A (Set.range iE)).algebraMap_mem a
      convert (Algebra.adjoin A (Set.range iE)).mul_mem he ha using 1
      change Ideal.Quotient.mk P (e ⊗ₜ[B] a) =
        Ideal.Quotient.mk P (e ⊗ₜ[B] (1 : A)) *
          Ideal.Quotient.mk P ((1 : E) ⊗ₜ[B] a)
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => simpa only [map_add] using
        (Algebra.adjoin A (Set.range iE)).add_mem hx hy
  obtain ⟨R, hR, hBU, hU, hT, aUE, hfracUE, hBUE, aTF, hfracTF, hATF,
      j, hj, hjB, hjE, he, hedvd, hindexU, hsep⟩ :=
    dvr_normalized_compositum_local_diagram B n A E htame F iE hcomm hgen Q hQover
  let := hR
  let U := Localization.AtPrime R
  let T := Localization.AtPrime Q
  let := hBU
  let := hU
  let := hT
  let := aUE
  let := hfracUE
  let := hBUE
  let := aTF
  let := hfracTF
  let := hATF
  have : IsLocalHom (algebraMap A T) := by
    apply ((IsLocalRing.local_hom_TFAE _).out 5 1).mp
    rw [IsScalarTower.algebraMap_eq A (integralClosure A F) T, ← Ideal.comap_comap]
    rw [show (IsLocalRing.maximalIdeal T).comap
      (algebraMap (integralClosure A F) T) = Q from
      Localization.AtPrime.under_maximalIdeal (I := Q)]
    exact hQover
  have hmax := dvr_abhyankar_local_map_maximalIdeal B n hnpos A hindex U
    (R.ramificationIdx B) he hedvd hindexU hsep E F iE hcomm hgen T j hj hjB hjE
  exact ramificationIdx_eq_one_of_map_maximalIdeal A (integralClosure A F) Q hQover hmax

end RingTheory

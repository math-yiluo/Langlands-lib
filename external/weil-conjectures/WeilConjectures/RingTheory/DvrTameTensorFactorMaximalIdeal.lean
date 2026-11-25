/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RamificationInertia.Inertia

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import WeilConjectures.RingTheory.DvrTameTensorFactorRamificationBound

/-! # A local consequence of tame DVR base change

Source: Stacks Project, Tags 032L, 0BRM and 09E7.
(blueprint: lem-sbc-dvr-tame-tensor-factor-maximal-ideal) -/

@[expose] public section
universe u
open scoped TensorProduct
namespace RingTheory

/-- Maximal ideal equality after tame DVR base change.

Source: Stacks Project, Tags 032L, 0BRM and 09E7.
(blueprint: lem-sbc-dvr-tame-tensor-factor-maximal-ideal)

Proof: Finite faithfulness gives an injection B -> A and a finite extension
Frac(A)/Frac(B); normality of A identifies A with the normalization of B in
Frac(A). The maximal-ideal identity gives ramification index n. The kernel of
A -> F is prime and contracts to zero in B, since B embeds in E and the map
from the field E to the nonzero tensor quotient F is injective. Incomparability
for the integral extension B -> A then makes that kernel zero. Inverting the
nonzero elements identifies F with a field factor of E tensor_Frac(B) Frac(A).
The normalization C of B in E is finite by Stacks 032L (the separable trace
argument); it is a Dedekind domain, so C localized at a prime over m_B is a DVR.
At each such prime, the two divisibility bounds and the unit n imply that the
ramification index and the residue degree are prime to the residue characteristic.
The inseparable residue degree is a power of that characteristic and divides
the residue degree, hence is one; in characteristic zero separability is automatic.
Apply Abhyankar's lemma 0BRM to these tame DVRs and Frac(A)/Frac(B): their
ramification indices divide n, the base-change index. Integrality over A and B
in F agrees by transitivity and the integral extension A/B. Localization of
normalization therefore identifies S_Q with the normalized field factor of
0BRM. Finiteness of S over A, its normality, and the fact that Q lies over m_A
ensure that S_Q is a DVR. Abhyankar gives adic formal smoothness of A -> S_Q;
Stacks 09E7 identifies its two consequences as index one and residue separability.
Index one means that a uniformizer of A generates the maximal ideal of S_Q.
Thus extension of m_A is precisely m_(S_Q). This uses only the index-one part
of the criterion; no formal unramifiedness conclusion is assumed. -/
theorem dvr_tame_tensor_factor_map_maximalIdeal
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (n : ℕ) (hnpos : 0 < n) (hn : IsUnit (n : B))
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra B A] [Module.Finite B A] [FaithfulSMul B A]
    (hindex : (IsLocalRing.maximalIdeal B).map (algebraMap B A) =
      IsLocalRing.maximalIdeal A ^ n)
    (E : Type u) [Field E] [Algebra (FractionRing B) E]
    (hE : FiniteDimensional (FractionRing B) E ∧ Algebra.IsSeparable (FractionRing B) E) :
    letI : Algebra B E :=
      ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
    let C := integralClosure B E
    (∀ (R : Ideal C) (hR : R.IsPrime),
      letI := hR
      R.comap (algebraMap B C) = IsLocalRing.maximalIdeal B →
        R.ramificationIdx B ∣ n ∧ R.inertiaDeg B ∣ n) →
    let D := E ⊗[B] A
    ∀ (P : Ideal D) (hP : P.IsMaximal),
    let := hP
    let F := D ⧸ P
    let alpha : A →+* F := (Ideal.Quotient.mk P).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[B] D).toRingHom
    letI := alpha.toAlgebra
    let S := integralClosure A F
    Module.Finite A S →
    ∀ (Q : Ideal S) (hQ : Q.IsPrime),
    let := hQ
    Q.comap (algebraMap A S) = IsLocalRing.maximalIdeal A →
      (IsLocalRing.maximalIdeal A).map (algebraMap A (Localization.AtPrime Q)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
  dsimp only
  let : Algebra B E :=
    ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
  have : IsScalarTower B (FractionRing B) E := .of_algebraMap_eq' rfl
  have : FiniteDimensional (FractionRing B) E := hE.1
  have : Algebra.IsSeparable (FractionRing B) E := hE.2
  have hC : Module.Finite B (integralClosure B E) :=
    IsIntegralClosure.finite B (FractionRing B) E (integralClosure B E)
  intro hbounds P hP
  let := hP
  let F := (E ⊗[B] A) ⧸ P
  let alpha : A →+* F := (Ideal.Quotient.mk P).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[B] E ⊗[B] A).toRingHom
  let := alpha.toAlgebra
  let beta : E →+* F := (Ideal.Quotient.mk P).comp
    (Algebra.TensorProduct.includeLeft : E →ₐ[B] E ⊗[B] A).toRingHom
  have hcomp : alpha.comp (algebraMap B A) = beta.comp (algebraMap B E) := by
    ext b
    exact congrArg (Ideal.Quotient.mk P)
      (DFunLike.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
        (R := B) (A := E) (B := A)) b).symm
  have hinj : Function.Injective alpha := by
    apply (RingHom.injective_iff_ker_eq_bot alpha).mpr
    apply Ideal.eq_bot_of_under_eq_bot (R := B)
    rw [Ideal.under_def, RingHom.comap_ker, hcomp]
    apply (RingHom.injective_iff_ker_eq_bot _).mp
    exact beta.injective.comp ((algebraMap (FractionRing B) E).injective.comp
      (IsFractionRing.injective B (FractionRing B)))
  intro hfinite Q hQ
  let := hQ
  intro hclosed
  have : Module.Finite A (integralClosure A F) := hfinite
  have hle := dvr_tame_tensor_factor_ramificationIdx_le B n hnpos n hnpos hn A
    hindex E hE hC hbounds P hP hinj hfinite Q hQ hclosed
  have hone : Q.ramificationIdx A = 1 := by
    have : IsNoetherianRing (integralClosure A F) :=
      IsNoetherianRing.of_finite A (integralClosure A F)
    have hpos := Ideal.ramificationIdx_pos A Q
    simp only [Nat.gcd_self, Nat.div_self hnpos] at hle
    omega
  rw [Ideal.ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom,
    ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff] at hone
  simpa only [Ideal.under_def, hclosed] using hone


end RingTheory

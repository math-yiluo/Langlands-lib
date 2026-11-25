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
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RamificationInertia.Inertia

import Mathlib.RingTheory.Unramified.LocalRing
import WeilConjectures.RingTheory.DvrTameTensorFactorMaximalIdeal
import WeilConjectures.RingTheory.DvrTameTensorFactorResidueSeparable

/-! # The tame ramification step for a finite normalization

Source: Stacks Project, Tags 0BRM, 09E7, 00UW and 02FM.
(blueprint: lem-sbc-dvr-tame-tensor-factor-unramified) -/

@[expose] public section
universe u
open scoped TensorProduct
namespace RingTheory

/-- A DVR base extension with sufficiently divisible index kills tame ramification.

Source: Stacks Project, Tags 0BRM, 09E7, 00UW and 02FM.
(blueprint: lem-sbc-dvr-tame-tensor-factor-unramified)

Proof: Since A is finite and faithful over B and both rings are DVRs, their
fraction fields form a finite extension. The displayed maximal-ideal power
identity shows that its ramification index is n.
The normalization C of B in E is finite, normal, and one-dimensional by the
separable trace-pairing theorem and integral dimension preservation, hence its
localizations at the primes above the closed point are DVRs. The assumed bounds
make their ramification indices and residue degrees
divide n. Since n is a unit in B,
the indices are prime to the residue characteristic and the residue extensions
are separable. Apply Abhyankar's lemma 0BRM to each of these DVRs and
Frac(A)/Frac(B). The map A -> F is injective, since its kernel contracts to
zero in B and A is integral over B. Thus F is a field factor after extending
the generic tensor product to Frac(A). Since A is integral over B, integrality
over A in F is equivalent to integrality over B; localization of integral closure
identifies the chosen S_Q with a normalized tensor factor from 0BRM.
Every such factor over the closed point of A has index one and separable residue
extension, by 09E7. The assumed finite
normalization makes the local maps essentially of finite type. The local
unramified criterion (00UW, 02FM) then gives formal unramifiedness. This
statement takes normalization finiteness and the divisibility bounds as inputs
and applies to any finite faithful DVR extension with the displayed ideal identity.
It neither constructs a root algebra nor proves the Galois divisibility bounds
or finiteness of the generic tensor factor's normalization. -/
theorem dvr_tame_tensor_factor_formallyUnramified
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
      Algebra.FormallyUnramified A (Localization.AtPrime Q) := by
  dsimp only
  let : Algebra B E :=
    ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
  intro hbounds P hP
  let := hP
  let F := (E ⊗[B] A) ⧸ P
  let alpha : A →+* F := (Ideal.Quotient.mk P).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[B] E ⊗[B] A).toRingHom
  let := alpha.toAlgebra
  intro hfinite Q hQ
  let := hQ
  intro hclosed
  have hmax := dvr_tame_tensor_factor_map_maximalIdeal B n hnpos hn A hindex E hE
    hbounds P hP hfinite Q hQ hclosed
  have hlocal : IsLocalHom (algebraMap A (Localization.AtPrime Q)) :=
    ((IsLocalRing.local_hom_TFAE _).out 3 1).mp (le_of_eq hmax)
  have hsep := dvr_tame_tensor_factor_residue_isSeparable B n hnpos hn A hindex E hE
    hbounds P hP hfinite Q hQ hclosed hlocal
  have : Module.Finite A (integralClosure A F) := hfinite
  have : Algebra.EssFiniteType A (Localization.AtPrime Q) :=
    Algebra.EssFiniteType.comp A (integralClosure A F) (Localization.AtPrime Q)
  exact Algebra.FormallyUnramified.of_map_maximalIdeal hmax

end RingTheory

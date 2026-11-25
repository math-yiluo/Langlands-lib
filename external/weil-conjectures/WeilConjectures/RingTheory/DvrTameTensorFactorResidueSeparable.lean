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

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import WeilConjectures.RingTheory.DvrAbhyankarLocalResidue
import WeilConjectures.RingTheory.DvrNormalizedCompositumLocalDiagram

/-! # A local consequence of tame DVR base change

Source: Stacks Project, Tags 032L, 0BRM and 09E7.
(blueprint: lem-sbc-dvr-tame-tensor-factor-residue-separable) -/

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

/-- Residue separability after tame DVR base change.

Source: Stacks Project, Tags 032L, 0BRM and 09E7.
(blueprint: lem-sbc-dvr-tame-tensor-factor-residue-separable)

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
The residue-separability consequence of 09E7 is separability for the residue
map induced by A -> S_Q. The explicit local-hom proof only supplies that map's
Lean algebra structure; it adds no ramification hypothesis. This is only the
residue-field conclusion and makes no assertion about the maximal ideal. -/
theorem dvr_tame_tensor_factor_residue_isSeparable
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
      ∀ (hloc : IsLocalHom (algebraMap A (Localization.AtPrime Q))),
      letI := hloc
      Algebra.IsSeparable (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField (Localization.AtPrime Q)) := by
  let : Algebra B E :=
    ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
  let C := integralClosure B E
  dsimp only
  intro hdiv P hP
  let := hP
  let D := E ⊗[B] A
  let F := D ⧸ P
  let : Field F := Ideal.Quotient.field P
  let alpha : A →+* F := (Ideal.Quotient.mk P).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[B] D).toRingHom
  let := alpha.toAlgebra
  intro hfinite Q hQ hQover hloc
  let := hfinite
  let := hQ
  let : FiniteDimensional (FractionRing B) E := hE.1
  let : Algebra.IsSeparable (FractionRing B) E := hE.2
  have : IsScalarTower B (FractionRing B) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite B C := IsIntegralClosure.finite B (FractionRing B) E C
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
    refine ⟨isUnit_of_dvd_unit (Nat.cast_dvd_cast he) hn, he, ?_⟩
    apply isSeparable_of_isUnit_finrank
    rw [← Ideal.inertiaDeg_def]
    have hu : IsUnit (R.inertiaDeg B : B) :=
      isUnit_of_dvd_unit (Nat.cast_dvd_cast hf) hn
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
  let := hloc
  exact dvr_abhyankar_local_residue_isSeparable B n hnpos A hindex U
    (R.ramificationIdx B) he hedvd hindexU hsep E F iE hcomm hgen T j hj hjB hjE


end RingTheory

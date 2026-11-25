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

import Mathlib.RingTheory.Flat.TorsionFree
import WeilConjectures.RingTheory.DvrAbhyankarNormalizedFactor
import WeilConjectures.RingTheory.DvrNormalizedTensorFactorLift
import WeilConjectures.AlgebraicGeometry.Morphisms.DvrUniformizerRootAlgebra

/-! # A numerical bound for tame DVR tensor factors

Source: Stacks Project, Tags 0BRM, 09EV, 09EM, 09E7 and 032L.
(blueprint: lem-sbc-dvr-tame-tensor-factor-ramification-bound) -/

@[expose] public section
universe u
open scoped TensorProduct
namespace RingTheory

/-- Quantitative tame ramification bound for a normalized tensor factor.

Source: Stacks Project, Tags 0BRM (Abhyankar), 09EV (uniformizer roots),
09EM (normalized tensor factors), 09E7 (index-one criterion), and 032L.
(blueprint: lem-sbc-dvr-tame-tensor-factor-ramification-bound)

Proof: The assumed injection A -> F, and the field inclusion E -> F, embed
B in A compatibly. Since A is finite and normal over B it is the normalization
of B in Frac(A). Inverting B minus zero identifies F with a field factor of
E tensor_Frac(B) Frac(A). Hence F/Frac(A) is finite separable. Clearing
denominators in a monic algebraic equation shows every element of F is a
fraction of elements of S,
so Frac(S) = F. The finite normalization S is Dedekind, and Q is nonzero
because it contracts to m_A; thus S_Q is a DVR. The same argument makes C a Dedekind domain.

Set t = r/gcd(r,n), which is positive and divides r. Adjoin a t-th root of a
uniformizer of A. For t = 1 use A itself; otherwise 09EV gives a DVR A'
with fraction field K', ramification index t over A, and therefore index
n*t = lcm(r,n) over B. The extension K'/Frac(A) is separable since t is a
unit. The root ring A' is also the normalization of B in K': it is integral
over B and normal, so any element of K' integral over B belongs to A'.
Choose a field factor F' of F tensor_Frac(A) K', with the induced compatible
embeddings of F and K'. Normalize S in F'; this is finite by 032L since
F'/F is finite separable. Choose a prime above Q by lying over and write T
for its local DVR. Its contraction in A' is the maximal ideal: it lies over
m_A in the integral local extension A'/A. Thus A' maps locally into T.
Its contraction R in C lies above m_B. The index e of C_R/B divides r;
its residue extension is separable since its inseparable degree is a power
of the residue characteristic and divides the residue degree, which divides
the unit r. Thus C_R/B is tame, and e divides n*t.

Apply 0BRM to C_R/B and K'/Frac(B), at the prime whose base DVR is A'.
Integrality over A, B and C agrees by transitivity, so T is the corresponding
normalized tensor factor of 09EM. By 09E7 its index over A' is one.
Multiplicativity in the towers A -> A' -> T and A -> S_Q -> T gives
 t = e(T/A) = e(T/S_Q) * e(S_Q/A).
Consequently e(S_Q/A) divides t and is at most t. The DVR index equals the
length of S_Q/m_A S_Q, which is Q.ramificationIdx A. -/
theorem dvr_tame_tensor_factor_ramificationIdx_le
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (n : ℕ) (hnpos : 0 < n) (r : ℕ) (hrpos : 0 < r) (hr : IsUnit (r : B))
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
      Q.ramificationIdx A ≤ r / Nat.gcd r n := by
  classical
  dsimp only
  let : Algebra B E :=
    ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
  intro hC hbounds P hP
  let := hP
  let F := (E ⊗[B] A) ⧸ P
  let alpha : A →+* F := (Ideal.Quotient.mk P).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[B] E ⊗[B] A).toRingHom
  let := alpha.toAlgebra
  intro hinj hS Q hQ hclosed
  let := hQ
  let : Module.Finite A (integralClosure A F) := hS
  let t := r / Nat.gcd r n
  have htpos : 0 < t := Nat.div_pos (Nat.le_of_dvd hrpos (Nat.gcd_dvd_left r n))
    (Nat.gcd_pos_of_pos_left n hrpos)
  have hrt : r ∣ n * t := by
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_right r n
    refine ⟨k, ?_⟩
    calc
      n * t = (Nat.gcd r n * k) * t := congrArg (· * t) hk
      _ = (Nat.gcd r n * t) * k := by ring
      _ = r * k := by rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left r n)]
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible A
  let f := (Polynomial.X : Polynomial A) ^ t - Polynomial.C pi
  let A₁ := AdjoinRoot f
  obtain ⟨hdom, hdvr, hmax⟩ :=
    AlgebraicGeometry.Scheme.dvr_uniformizer_root_algebra A pi hpi t htpos
  let : IsDomain A₁ := hdom
  let : IsDiscreteValuationRing A₁ := hdvr
  have hf : f.Monic := Polynomial.monic_X_pow_sub_C pi htpos.ne'
  let : Module.Finite A A₁ := hf.finite_adjoinRoot
  have hAinj : Function.Injective (algebraMap A A₁) := by
    apply AdjoinRoot.of.injective_of_degree_ne_zero
    rw [Polynomial.degree_eq_natDegree hf.ne_zero, Polynomial.natDegree_X_pow_sub_C]
    exact_mod_cast htpos.ne'
  let : FaithfulSMul A A₁ := (faithfulSMul_iff_algebraMap_injective A A₁).mpr hAinj
  have hroot : AdjoinRoot.root f ^ t = algebraMap A A₁ pi := by
    simpa only [f, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, sub_eq_zero, ← AdjoinRoot.algebraMap_eq] using
      (AdjoinRoot.eval₂_root f)
  have hidx₁ : (IsLocalRing.maximalIdeal A).map (algebraMap A A₁) =
      IsLocalRing.maximalIdeal A₁ ^ t := by
    rw [hpi.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hmax,
      Ideal.span_singleton_pow, hroot]
  let : IsScalarTower B A A₁ := inferInstance
  let : Module.Finite B A₁ := Module.Finite.trans A A₁
  have hidxB : (IsLocalRing.maximalIdeal B).map (algebraMap B A₁) =
      IsLocalRing.maximalIdeal A₁ ^ (n * t) := by
    rw [IsScalarTower.algebraMap_eq B A A₁, ← Ideal.map_map, hindex,
      Ideal.map_pow, hidx₁, ← pow_mul, Nat.mul_comm t n]
  obtain ⟨P₁, hP₁, hinj₁, hS₁, i, Q₁, hQ₁, hover, hclosed₁, hflat⟩ :=
    dvr_normalized_tensor_factor_lift B A E hE P hP hinj hS Q hQ hclosed A₁
  let := hP₁
  let F₁ := (E ⊗[B] A₁) ⧸ P₁
  let alpha₁ : A₁ →+* F₁ := (Ideal.Quotient.mk P₁).comp
    (Algebra.TensorProduct.includeRight : A₁ →ₐ[B] E ⊗[B] A₁).toRingHom
  let := alpha₁.toAlgebra
  let : Algebra A F₁ := (alpha₁.comp (algebraMap A A₁)).toAlgebra
  let : IsScalarTower A A₁ F₁ := .of_algebraMap_eq' rfl
  let S₁ := integralClosure A₁ F₁
  let := hQ₁
  let : Module.Finite A₁ S₁ := hS₁
  let : Algebra (integralClosure A F) S₁ := i.toRingHom.toAlgebra
  let : IsScalarTower A (integralClosure A F) S₁ := .of_algHom i
  let : Module.Flat (integralClosure A F) S₁ := hflat
  let : Q₁.LiesOver Q := ⟨hover.symm⟩
  let : Q₁.LiesOver (IsLocalRing.maximalIdeal A₁) := ⟨hclosed₁.symm⟩
  have hone : Q₁.ramificationIdx A₁ = 1 :=
    dvr_abhyankar_normalized_factor_ramificationIdx_eq_one B (n * t)
      (Nat.mul_pos hnpos htpos) r hrpos hr hrt A₁ hidxB E hE
      hC hbounds P₁ hP₁ hinj₁ hS₁ Q₁ hQ₁ hclosed₁
  have he : (IsLocalRing.maximalIdeal A₁).ramificationIdx A = t := by
    let : (IsLocalRing.maximalIdeal A₁).LiesOver (IsLocalRing.maximalIdeal A) :=
      ⟨(IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_under_of_isIntegral_of_isMaximal
          (IsLocalRing.maximalIdeal A₁))).symm⟩
    let : IsDiscreteValuationRing (Localization.AtPrime (IsLocalRing.maximalIdeal A₁)) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A₁
        (IsDiscreteValuationRing.not_a_field A₁) _
    rw [Ideal.ramificationIdx_eq (IsLocalRing.maximalIdeal A),
      IsScalarTower.algebraMap_eq A A₁ (Localization.AtPrime (IsLocalRing.maximalIdeal A₁)),
      ← Ideal.map_map, hidx₁, Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal,
      IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, ENat.toNat_natCast]
  let : Module.IsTorsionFree A₁ F₁ :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr hinj₁
  let : Module.IsTorsionFree A₁ S₁ := inferInstance
  let : Module.Flat A₁ S₁ := inferInstance
  have htotal : Q₁.ramificationIdx A = t := by
    rw [Ideal.ramificationIdx_tower (IsLocalRing.maximalIdeal A₁) Q₁, hone, mul_one, he]
  have hdvd : Q.ramificationIdx A ∣ t := by
    rw [← htotal]
    exact Ideal.ramificationIdx_below_dvd Q Q₁
  exact Nat.le_of_dvd htpos hdvd


end RingTheory

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Unramified.LocalRing
import WeilConjectures.AlgebraicGeometry.Morphisms.DvrUniformizerRootAlgebra
import WeilConjectures.RingTheory.DvrGaloisNormalizationRamificationDvd
import WeilConjectures.RingTheory.DvrRootTensorFactorIntegralClosureFinite
import WeilConjectures.RingTheory.DvrTameTensorFactorUnramified

/-! # The algebraic tame root calculation in a generic tensor factor

Source: Stacks Project, Tags 09EV, 09EB, 0BRM and 09E7.
(blueprint: lem-sbc-dvr-galois-root-factor-uniformizer) -/

@[expose] public section

universe u
open scoped TensorProduct
namespace RingTheory

private theorem maximalIdeal_eq_span_of_unramified
    {R T : Type u} [CommRing R] [CommRing T] [IsLocalRing R] [IsLocalRing T]
    [Algebra R T] [IsLocalHom (algebraMap R T)] [Algebra.FormallyUnramified R T]
    [Algebra.EssFiniteType R T]
    (t : R) (ht : IsLocalRing.maximalIdeal R = Ideal.span {t}) :
    IsLocalRing.maximalIdeal T = Ideal.span {algebraMap R T t} := by
  rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R), ht,
    Ideal.map_span, Set.image_singleton]

/-- The root generates the maximal ideal of an integral-closure local factor.

Source: Stacks Project, Tags 09EV, 09EB, 0BRM and 09E7.
(blueprint: lem-sbc-dvr-galois-root-factor-uniformizer)

Proof: Write K = Frac(B), A = B[t]/(t^n-pi), and F = (E tensor_B A)/P.
For n > 1, 09EV makes A a DVR with uniformizer t, fraction field K1, and
ramification index n over B. For n = 1 evaluation identifies A with B.
Since pi is invertible in E, E tensor_B A is E tensor_K K1. It is a finite
product of fields, as E/K is finite separable. Thus F is one such field.
The integral closure of B in E has DVR local rings at its primes above (pi).
By 09EB their ramification index and residue degree divide [E:K], hence n.
Invertibility of n forces the ramification index to be prime to the residue
characteristic and the residue inseparable degree to be one. Apply 0BRM to
these tame DVR extensions and K1/K: every local ring of the integral closure
of A in F above (t) is adically formally smooth over A. By 09E7 its index is
one. Since t is a uniformizer of A, its image generates the local maximal ideal.
All maps used here are the structural maps induced by the right tensor inclusion. No finiteness
of a scheme normalization is assumed. Degree-one extensions and n = 1 give
the same index-one conclusion. -/
theorem dvr_galois_root_factor_uniformizer
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (pi : B) (hpi : Irreducible pi) (n : ℕ) (hnpos : 0 < n)
    (hn : IsUnit (n : B))
    (E : Type u) [Field E] [Algebra (FractionRing B) E]
    (hE : FiniteDimensional (FractionRing B) E ∧
      IsGalois (FractionRing B) E ∧ Module.finrank (FractionRing B) E ∣ n) :
    letI : Algebra B E :=
      ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
    let A := AdjoinRoot ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)
    let D := E ⊗[B] A
    ∀ (P : Ideal D) (hP : P.IsMaximal),
    letI := hP
    let F := D ⧸ P
    let alpha : A →+* F := (Ideal.Quotient.mk P).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[B] D).toRingHom
    letI := alpha.toAlgebra
    let S := integralClosure A F
    ∀ (Q : Ideal S) (hQ : Q.IsPrime),
    letI := hQ
    Q.comap (algebraMap A S) = Ideal.span
      {AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)} →
    let t := algebraMap S (Localization.AtPrime Q)
      (algebraMap A S
        (AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)))
    IsLocalRing.maximalIdeal (Localization.AtPrime Q) = Ideal.span {t} := by
  dsimp only
  let : IsGalois (FractionRing B) E := hE.2.1
  let : Algebra B E :=
    ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
  let f := (Polynomial.X : Polynomial B) ^ n - Polynomial.C pi
  let A := AdjoinRoot f
  let D := E ⊗[B] A
  intro P hP
  let := hP
  let F := D ⧸ P
  let alpha : A →+* F := (Ideal.Quotient.mk P).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[B] D).toRingHom
  let := alpha.toAlgebra
  let S := integralClosure A F
  intro Q hQ hcontract
  let := hQ
  have hroot :=
    AlgebraicGeometry.Scheme.dvr_uniformizer_root_algebra B pi hpi n hnpos
  -- Project the instances without dependent elimination over the tensor/localization goal.
  have hdomA := hroot.choose
  have hdvrA := hroot.choose_spec.choose
  have hmaxA := hroot.choose_spec.choose_spec
  let : Module.Finite B A :=
    (Polynomial.monic_X_pow_sub_C pi hnpos.ne').finite_adjoinRoot
  let : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr (by
    apply AdjoinRoot.of.injective_of_degree_ne_zero
    rw [Polynomial.degree_eq_natDegree (Polynomial.monic_X_pow_sub_C pi hnpos.ne').ne_zero,
      Polynomial.natDegree_X_pow_sub_C]
    exact_mod_cast hnpos.ne')
  have hrel : AdjoinRoot.root f ^ n = algebraMap B A pi := by
    simpa only [f, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, sub_eq_zero, ← AdjoinRoot.algebraMap_eq] using
      AdjoinRoot.eval₂_root f
  have hindex : (IsLocalRing.maximalIdeal B).map (algebraMap B A) =
      IsLocalRing.maximalIdeal A ^ n := by
    rw [hpi.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hmaxA,
      Ideal.span_singleton_pow, hrel]
  let : Module.Finite A S :=
    dvr_root_tensor_factor_integralClosure_finite B A E
      ⟨hE.1, inferInstance⟩ P hP
  have hc : Q.comap (algebraMap A S) = IsLocalRing.maximalIdeal A :=
    hcontract.trans hmaxA.symm
  let : Algebra.FormallyUnramified A (Localization.AtPrime Q) :=
    dvr_tame_tensor_factor_formallyUnramified B n hnpos hn A hindex
      E ⟨hE.1, inferInstance⟩ (dvr_galois_normalization_ramification_dvd B E n hE)
      P hP inferInstance Q hQ hc
  let : IsLocalHom (algebraMap A (Localization.AtPrime Q)) := by
    apply ((IsLocalRing.local_hom_TFAE _).out 5 1).mp
    change (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).comap
      ((algebraMap S (Localization.AtPrime Q)).comp (algebraMap A S)) =
        IsLocalRing.maximalIdeal A
    rw [← Ideal.comap_comap]
    change ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).comap
      (algebraMap S (Localization.AtPrime Q))).comap (algebraMap A S) = _
    have hloc : (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).comap
        (algebraMap S (Localization.AtPrime Q)) = Q :=
      Localization.AtPrime.under_maximalIdeal
    exact (congrArg (Ideal.comap (algebraMap A S)) hloc).trans hc
  exact maximalIdeal_eq_span_of_unramified (T := Localization.AtPrime Q)
    (AdjoinRoot.root f) hmaxA

end RingTheory

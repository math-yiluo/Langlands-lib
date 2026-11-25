/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.LocalizationLocalization

@[expose] public section

universe u v
open scoped TensorProduct
namespace AdicCompletion

-- The ideal-membership argument also works for n = 0; keep the given signature.
set_option linter.unusedVariables false in
/-- The quotient tensor product embeds into the product of its local factors.
Source: Stacks Project, Tag 07N9, quotient-product argument.
(blueprint: lem-weil-pbc-local-tensor-quotient-component-map)

Identify the source with B/I, where B = Rₚ ⊗[R] S and I = mⁿB, and construct
the component maps by tensor-product lifting followed by quotient maps.
Every maximal ideal of B contracts to m by finiteness over Rₚ, so its
localization is canonically S_q for a prime q over p. Ideal membership is
detected at these maximal localizations, proving injectivity. The formula
on pure tensors follows from the quotient-tensor equivalence and tensor lift. -/
theorem tensor_quotient_component_map
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime]
    (n : ℕ) (hn : 0 < n) :
    let A := Localization.AtPrime p
    let m := IsLocalRing.maximalIdeal A
    ∃ φ : ((Localization.AtPrime p ⧸ (m ^ n)) ⊗[R] S) →ₗ[R]
        (∀ q : p.primesOver S,
          (Localization.AtPrime q.1 ⧸ (m ^ n).map
            (Localization.localRingHom p q.1 (algebraMap R S)
              (Ideal.LiesOver.over (P := q.1) (p := p))))) ,
      Function.Injective φ ∧
        ∀ (r : A) (s : S) (q : p.primesOver S),
          φ ((Ideal.Quotient.mk (m ^ n) r) ⊗ₜ[R] s) q =
            Ideal.Quotient.mk ((m ^ n).map
              (Localization.localRingHom p q.1 (algebraMap R S)
                (Ideal.LiesOver.over (P := q.1) (p := p))))
              (Localization.localRingHom p q.1 (algebraMap R S)
                (Ideal.LiesOver.over (P := q.1) (p := p)) r *
                algebraMap S (Localization.AtPrime q.1) s) := by
  classical
  let A := Localization.AtPrime p
  let m := IsLocalRing.maximalIdeal A
  let B := A ⊗[R] S
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := S)
  let I := (m ^ n).map (algebraMap A B)
  let f (q : p.primesOver S) : A →ₐ[R] Localization.AtPrime q.1 :=
    { toRingHom := Localization.localRingHom p q.1 (algebraMap R S)
        (Ideal.LiesOver.over (P := q.1) (p := p))
      commutes' := fun r ↦ by
        change Localization.localRingHom p q.1 (algebraMap R S)
          (Ideal.LiesOver.over (P := q.1) (p := p)) (algebraMap R A r) = _
        rw [Localization.localRingHom_to_map]
        exact (IsScalarTower.algebraMap_apply R S (Localization.AtPrime q.1) r).symm }
  let ψ (q : p.primesOver S) : B →ₐ[R] Localization.AtPrime q.1 :=
    Algebra.TensorProduct.lift (f q) (IsScalarTower.toAlgHom R S _)
      (fun _ _ ↦ Commute.all _ _)
  have hψ (q : p.primesOver S) :
      (ψ q).toRingHom.comp (algebraMap A B) = (f q).toRingHom := by
    ext a
    simp [ψ, B]
  have hI (q : p.primesOver S) : I.map (ψ q).toRingHom = (m ^ n).map (f q) := by
    dsimp only [I]
    rw [Ideal.map_map, hψ]
    rfl
  let g (q : p.primesOver S) :
      B ⧸ I →ₐ[R] Localization.AtPrime q.1 ⧸ (m ^ n).map (f q) :=
    Ideal.quotientMapₐ _ (ψ q) (Ideal.map_le_iff_le_comap.mp (hI q).le)
  let e := Algebra.TensorProduct.quotientTensorEquiv (R := R) R S A (m ^ n)
  let φ : (A ⧸ m ^ n) ⊗[R] S →ₗ[R]
      (∀ q : p.primesOver S, Localization.AtPrime q.1 ⧸ (m ^ n).map (f q)) :=
    (LinearMap.pi fun q ↦ (g q).toLinearMap).comp e.toLinearMap
  refine ⟨φ, ?_, ?_⟩
  · have hlocal (b : B) (hb : ∀ q, ψ q b ∈ I.map (ψ q).toRingHom) : b ∈ I := by
      apply Ideal.mem_of_localization_maximal
      intro P hP
      let q := P.comap (algebraMap S B)
      have hq : q.IsPrime := Ideal.comap_isPrime _ P
      let := hq
      have hPA : P.comap (algebraMap A B) = m :=
        IsLocalRing.eq_maximalIdeal
          (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) P)
      have hqover : q.LiesOver p := by
        constructor
        change p = (P.comap (algebraMap S B)).comap (algebraMap R S)
        rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq R S B,
          IsScalarTower.algebraMap_eq R A B, ← Ideal.comap_comap, hPA]
        exact (IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p) p).symm
      let := hqover
      let q' : p.primesOver S := ⟨q, inferInstance, inferInstance⟩
      let T := Localization.AtPrime P
      have : IsLocalization.AtPrime T q :=
        IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
          (Algebra.algebraMapSubmonoid S p.primeCompl) T P
      let eq : T ≃ₐ[S] Localization.AtPrime q :=
        IsLocalization.algEquiv q.primeCompl T _
      have hcomp : eq.toRingHom.comp (algebraMap B T) = (ψ q').toRingHom := by
        apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid S p.primeCompl)
        ext s
        change eq (algebraMap B T (algebraMap S B s)) = ψ q' (1 ⊗ₜ[R] s)
        rw [← IsScalarTower.algebraMap_apply S B T, eq.commutes]
        dsimp only [ψ]
        rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        rfl
      have heval : eq (algebraMap B T b) = ψ q' b := RingHom.congr_fun hcomp b
      have hmem := hb q'
      rw [← hcomp, ← Ideal.map_map, ← heval] at hmem
      obtain ⟨t, ht, he⟩ :=
        (Ideal.mem_map_iff_of_surjective eq.toRingHom eq.surjective).mp hmem
      exact eq.injective he ▸ ht
    intro x y hxy
    apply e.injective
    apply sub_eq_zero.mp
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (e x - e y)
    rw [← hb, Ideal.Quotient.eq_zero_iff_mem]
    apply hlocal b
    intro q
    have hz : g q (Ideal.Quotient.mk I b) = 0 := by
      rw [hb, map_sub]
      exact sub_eq_zero.mpr (congrFun hxy q)
    change Ideal.Quotient.mk ((m ^ n).map (f q)) (ψ q b) = 0 at hz
    rw [hI]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  · intro r s q
    change g q (e ((Ideal.Quotient.mk (m ^ n) r) ⊗ₜ[R] s)) = _
    rw [Algebra.TensorProduct.quotientTensorEquiv_apply_tmul]
    change Ideal.Quotient.mk ((m ^ n).map (f q)) (ψ q (r ⊗ₜ[R] s)) = _
    rw [Algebra.TensorProduct.lift_tmul]
    rfl

end AdicCompletion

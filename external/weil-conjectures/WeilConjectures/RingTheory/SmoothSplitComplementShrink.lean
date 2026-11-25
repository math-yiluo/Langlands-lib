/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Etale.Kaehler

/-!
# Freeness of a smooth differential complement after shrinking

Source: Stacks Project, Tags 07C6 and 0GWM.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- A free summand of the coordinate module determines the rank of the differential
complement, which is free after a further principal shrink around the chosen prime.
Source: Stacks Project, Tag 07C6, proof, and Tag 0GWM.
(blueprint: lem-weil-pbc-smooth-split-complement-shrink)

Proof: Let B = A[1/a]. The displayed splitting makes the differential module a
finite projective B-module. Localize at the prime of B corresponding to p; the
complement is finite free over this local ring. The given basis of M and the
splitting show, by reducing modulo its maximal ideal and adding dimensions, that
its rank is n-c. Finite projective modules are finitely presented. Spread this
finite basis using Tag 0GWM. Write the resulting localization element of B as
 t/a^k, where t lies outside p. Inverting a*t in A gives the same further open.
Localization of differentials identifies the spread module with the differentials
of A[1/(a*t)]. Smoothness persists under this principal localization. This also
covers c=n (the complement has rank zero), and c=0. -/
theorem exists_smooth_split_complement_shrink
    (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    (a : A) (p : Ideal A) [p.IsPrime] (ha : a ∉ p)
    (n c : ℕ) (hc : c ≤ n)
    (M : Type w) [AddCommGroup M] [Module (Localization.Away a) M]
    (b : Module.Basis (Fin c) (Localization.Away a) M)
    (hsm : Smooth R (Localization.Away a))
    (hsplit : Nonempty ((M × KaehlerDifferential R (Localization.Away a))
      ≃ₗ[Localization.Away a] (Fin n → Localization.Away a))) :
    ∃ t : A, t ∉ p ∧ Smooth R (Localization.Away (a * t)) ∧
      Nonempty (Module.Basis (Fin (n - c)) (Localization.Away (a * t))
        (KaehlerDifferential R (Localization.Away (a * t)))) := by
  classical
  let B := Localization.Away a
  let N := KaehlerDifferential R B
  have : Smooth R B := hsm
  let pB : Ideal B := p.map (algebraMap A B)
  have hdis : Disjoint (Submonoid.powers a : Set A) (p : Set A) := by
    rw [Set.disjoint_left]
    intro x hx hxp
    obtain ⟨k, rfl⟩ := hx
    exact ha ((inferInstance : p.IsPrime).mem_of_pow_mem k hxp)
  have : pB.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers a) B p inferInstance hdis
  let K := Localization.AtPrime pB
  let Np := LocalizedModule pB.primeCompl N
  have : Module.Free K Np := Module.free_of_flat_of_isLocalRing
  let bn := Module.finBasis K Np
  let ibc := IsLocalizedModule.isBaseChange pB.primeCompl K
    (LocalizedModule.mkLinearMap pB.primeCompl N)
  let bt := bn.map ibc.equiv.symm
  let bm := b.baseChange K
  have : Module.Finite K (K ⊗[B] M) := Module.Finite.of_basis bm
  have : Module.Free K (K ⊗[B] M) := Module.Free.of_basis bm
  have : Module.Free K (K ⊗[B] N) := Module.Free.of_basis bt
  obtain ⟨e⟩ := hsplit
  let et := (TensorProduct.prodRight B K K M N).symm.trans
    (LinearEquiv.baseChange B K _ _ e)
  let bcoord := (Pi.basisFun B (Fin n)).baseChange K
  have hrank : c + Module.finrank K Np = n := by
    have h := et.finrank_eq
    rw [Module.finrank_prod, Module.finrank_eq_card_basis bm,
      Module.finrank_eq_card_basis bt, Module.finrank_eq_card_basis bcoord] at h
    simpa using h
  have hr : Module.finrank K Np = n - c := by omega
  let bn' := bn.reindex (finCongr hr)
  obtain ⟨s, hs, bs, hbs⟩ :=
    Module.FinitePresentation.exists_basis_localizedModule_powers pB.primeCompl
      (LocalizedModule.mkLinearMap pB.primeCompl N) K bn'
  let t := (IsLocalization.Away.sec a s).1
  have hts : Associated (algebraMap A B t) s :=
    IsLocalization.Away.associated_sec_fst a s
  have ht : t ∉ p := by
    intro htp
    exact hs ((pB.mem_iff_of_associated hts).mp (Ideal.mem_map_of_mem _ htp))
  let D := Localization.Away s
  have : Smooth B D := Smooth.of_isLocalization_Away s
  have : Smooth R D := Smooth.comp R B D
  have : IsLocalization.Away (a * t) D :=
    IsLocalization.Away.mul_of_associated a t s hts
  let C := Localization.Away (a * t)
  let : Algebra B C :=
    (IsLocalization.Away.awayToAwayRight (S := B) (P := C) a t).toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' <| by
    ext x
    exact (IsLocalization.Away.awayToAwayRight_eq (S := B) (P := C) a t x).symm
  have : IsScalarTower R B C := IsScalarTower.to₁₃₄ R A B C
  let eDC := IsLocalization.algEquiv (Submonoid.powers (a * t)) D C
  have hcomm : eDC.toRingHom.comp (algebraMap B D) = algebraMap B C := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    ext x
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply A B D,
      ← IsScalarTower.algebraMap_apply A B C]
    exact eDC.commutes x
  let eDCB : D ≃ₐ[B] C :=
    { eDC.toRingEquiv with commutes' := RingHom.congr_fun hcomm }
  have : IsLocalization.Away s C :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers s) eDCB
  have : FormallyEtale B C := FormallyEtale.of_isLocalization (Rₘ := C)
    (Submonoid.powers s)
  have : Smooth B C := Smooth.of_isLocalization_Away s
  have : Smooth R C := Smooth.comp R B C
  let : Algebra D C := eDCB.toRingHom.toAlgebra
  have : IsScalarTower B D C := IsScalarTower.of_algebraMap_eq' hcomm.symm
  let eb : (C ⊗[D] LocalizedModule.Away s N) ≃ₗ[C] (C ⊗[B] N) :=
    (LinearEquiv.baseChange D C _ _ (LocalizedModule.equivTensorProduct
      (Submonoid.powers s) N)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange B D C C N)
  exact ⟨t, ht, inferInstance,
    ⟨((bs.baseChange C).map eb).map
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B C)⟩⟩


end Algebra

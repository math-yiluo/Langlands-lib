/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

/-! # Essential finite type for a DVR in a finite separable fraction extension

Source: Stacks Project, Tags 09E8 and 032L.
(blueprint: lem-sbc-dvr-finite-separable-fraction-ess-finite-type) -/

@[expose] public section
universe u
namespace RingTheory

/-- A local DVR in a finite separable extension of the base fraction field is
essentially of finite type over the base.

Source: Stacks Project, Tag 09E8 (the normalized local DVRs), using Tag 032L.
(blueprint: lem-sbc-dvr-finite-separable-fraction-ess-finite-type)

Proof: Let C be the integral closure of B in E. The trace-pairing theorem 032L
makes C finite over B; it is Dedekind and has fraction field E. Since U is
integrally closed in E and contains B, every B-integral element of E belongs
to U, so C maps injectively into U. Contract the maximal ideal of U to P in C.
A base uniformizer lies in P and is nonzero, so P is nonzero and C_P is a DVR.
Its local map to U induces the identity on the common fraction field E.
Maximality of a valuation ring among local subrings of its fraction field
makes C_P -> U an isomorphism. Since C is finite over B and C_P is its
localization, C_P is essentially of finite type over B; transfer this to U. -/
theorem dvr_finite_separable_fraction_essFiniteType
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (U : Type u) [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    [Algebra B U] [IsLocalHom (algebraMap B U)]
    (E : Type u) [Field E] [Algebra (FractionRing B) E]
    [Algebra B E] [IsScalarTower B (FractionRing B) E]
    [FiniteDimensional (FractionRing B) E] [Algebra.IsSeparable (FractionRing B) E]
    [Algebra U E] [IsFractionRing U E] [IsScalarTower B U E] :
    Algebra.EssFiniteType B U := by
  classical
  let C := integralClosure B E
  let : Module.Finite B C := IsIntegralClosure.finite B (FractionRing B) E C
  let : IsFractionRing C E :=
    IsIntegralClosure.isFractionRing_of_finite_extension B (FractionRing B) E C
  let eU : U ≃+* (algebraMap U E).range :=
    RingEquiv.ofBijective (algebraMap U E).rangeRestrict
      ⟨fun _ _ h ↦ (IsFractionRing.injective U E) (congrArg Subtype.val h),
        RingHom.rangeRestrict_surjective _⟩
  let fc : C →+* (algebraMap U E).range := C.val.toRingHom.codRestrict _ (fun c ↦ by
    exact IsIntegrallyClosed.algebraMap_eq_of_integral (c.property.tower_top (A := U)))
  let f : C →+* U := eU.symm.toRingHom.comp fc
  have hf (c : C) : algebraMap U E (f c) = (c : E) := by
    change ((eU (eU.symm (fc c)) : (algebraMap U E).range) : E) = (c : E)
    rw [eU.apply_symm_apply]
    rfl
  let : Algebra C U := f.toAlgebra
  have : IsScalarTower B C U := IsScalarTower.of_algebraMap_eq (fun b ↦ by
    apply IsFractionRing.injective U E
    change algebraMap U E (algebraMap B U b) = algebraMap U E (f (algebraMap B C b))
    rw [← IsScalarTower.algebraMap_apply B U E, hf]
    rfl)
  let : FaithfulSMul B C := (faithfulSMul_iff_algebraMap_injective B C).mpr (by
    intro x y h
    apply IsFractionRing.injective B (FractionRing B)
    apply (algebraMap (FractionRing B) E).injective
    have heq := congrArg (fun c : C ↦ (c : E)) h
    change algebraMap B E x = algebraMap B E y at heq
    simpa only [← IsScalarTower.algebraMap_apply B (FractionRing B) E] using heq)
  let P : Ideal C := (IsLocalRing.maximalIdeal U).comap f
  let : P.IsPrime := Ideal.IsPrime.comap f
  have hP : P ≠ ⊥ := by
    obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible B
    have hpC : algebraMap B C p ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective B C)).mpr hp.ne_zero
    have hpP : algebraMap B C p ∈ P := by
      change algebraMap C U (algebraMap B C p) ∈ IsLocalRing.maximalIdeal U
      rw [← IsScalarTower.algebraMap_apply B C U]
      exact map_nonunit _ p (by
        rw [hp.maximalIdeal_eq]
        exact Ideal.mem_span_singleton_self p)
    intro h
    exact hpC (by simpa [h] using hpP)
  let S := Localization.AtPrime P
  let : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hP S
  let g : S →+* U := IsLocalization.lift (fun s : P.primeCompl ↦
    show IsUnit (f s) from by
      have hs := s.2
      change ¬ ¬ IsUnit (f (s : C)) at hs
      exact not_not.mp hs)
  have hg (c : C) : g (algebraMap C S c) = f c := IsLocalization.lift_eq _ _
  have hglocal : IsLocalHom g := by
    constructor
    intro z hz
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl z
    apply (IsLocalization.AtPrime.isUnit_mk'_iff S P x s).mpr
    intro hx
    have hxunit : IsUnit (f x) := by
      rw [← hg, ← IsLocalization.mk'_spec S x s, map_mul]
      exact hz.mul (g.isUnit_map (IsLocalization.map_units S s))
    exact hx hxunit
  let := hglocal
  let : Algebra S E := ((algebraMap U E).comp g).toAlgebra
  have : IsScalarTower C S E := IsScalarTower.of_algebraMap_eq (fun c ↦ by
    change (c : E) = algebraMap U E (g (algebraMap C S c))
    rw [hg, hf])
  let : IsFractionRing S E :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl S E
  have hbij : Function.Bijective ((algebraMap U E).rangeRestrict.comp g) :=
    bijective_rangeRestrict_comp_of_valuationRing g (algebraMap U E) rfl
  have hgsurj : Function.Surjective g := by
    intro t
    obtain ⟨s, hs⟩ := hbij.2 ((algebraMap U E).rangeRestrict t)
    exact ⟨s, (IsFractionRing.injective U E) (congrArg Subtype.val hs)⟩
  let ga : S →ₐ[B] U :=
    { toRingHom := g
      commutes' := fun b ↦ by
        change g (algebraMap B S b) = algebraMap B U b
        rw [IsScalarTower.algebraMap_apply B C S, hg]
        exact (IsScalarTower.algebraMap_apply B C U b).symm }
  let : Algebra.EssFiniteType B S := Algebra.EssFiniteType.comp B C S
  exact Algebra.EssFiniteType.of_surjective ga hgsurj

end RingTheory

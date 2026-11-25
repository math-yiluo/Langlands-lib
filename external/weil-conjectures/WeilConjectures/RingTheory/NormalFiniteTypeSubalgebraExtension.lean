/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.RingTheory.FiniteTypeZDomainNormalizationFinite

/-!
# Normal finite-type subalgebras containing a given finite-type subalgebra

Source: Stacks Project, Algebra, Tag 033C, third paragraph, and Tag 0335.
(blueprint: lem-weil-pbc-normal-finite-type-subalgebra-extension).
-/

@[expose] public section

universe u

namespace Subalgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Every finitely generated integer subalgebra of an integrally closed domain
is contained in a finitely generated, integrally closed integer subalgebra.

Source: Stacks Project, Algebra, Tag 033C, third paragraph; Tag 0335.
(blueprint: lem-weil-pbc-normal-finite-type-subalgebra-extension).

Proof: let K be the fraction field of C and normalize C in K. The normalization
is finite over C by finiteness of normalization for finite-type domains over Z
(Tag 0335), hence finite type over Z. Embed K in the fraction field of R using
C's inclusion. Every element of the normalization is integral over C, and hence
its image is integral over R. Since R is integrally closed, that image comes
from R. The induced injective map of the normalization into R has image A,
a Z-subalgebra containing C. Its image is isomorphic to the normalization,
so A is finitely generated and integrally closed. No algebraicity assumption
on R over C is needed: only C's own fraction field is normalized.
-/
theorem exists_fg_integrallyClosed_extension
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (C : Subalgebra ℤ R) (hC : C.FG) :
    ∃ A : Subalgebra ℤ R, C ≤ A ∧ A.FG ∧ IsIntegrallyClosed A := by
  classical
  let K := FractionRing C
  let N := integralClosure C K
  have : Algebra.FiniteType ℤ C := (Subalgebra.fg_iff_finiteType C).mp hC
  have : Module.Finite C N := RingTheory.finiteTypeZDomain_integralClosure_finite C K
  have : Algebra.FiniteType ℤ N :=
    Algebra.FiniteType.trans (R := ℤ) (S := C) (A := N)
      (inferInstanceAs (Algebra.FiniteType ℤ C))
      (inferInstanceAs (Algebra.FiniteType C N))
  have : IsIntegrallyClosed N :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  let L := FractionRing R
  let k : C →ₐ[C] L := Algebra.ofId C L
  have hk : Function.Injective k :=
    (IsFractionRing.injective R L).comp Subtype.val_injective
  let l : K →ₐ[C] L := IsFractionRing.liftAlgHom hk
  let j : N →ₐ[C] L := l.comp N.val
  let r : R →ₐ[ℤ] L := IsScalarTower.toAlgHom ℤ R L
  have hr : Function.Injective r := IsFractionRing.injective R L
  have hjmem : ∀ n : N, j n ∈ r.range := by
    intro n
    apply (AlgHom.mem_range r).mpr
    have hn : IsIntegral C (j n) := n.property.map l
    exact IsIntegrallyClosed.algebraMap_eq_of_integral (hn.tower_top (A := R))
  let q : N →ₐ[ℤ] r.range := (j.restrictScalars ℤ).codRestrict r.range hjmem
  let h : N →ₐ[ℤ] R := (AlgEquiv.ofInjective r hr).symm.toAlgHom.comp q
  have hh : ∀ n : N, r (h n) = j n := by
    intro n
    change r ((AlgEquiv.ofInjective r hr).symm (q n)) = j n
    have he := (AlgEquiv.ofInjective r hr).apply_symm_apply (q n)
    exact congrArg Subtype.val he
  have hinj : Function.Injective h := by
    intro x y hxy
    apply Subtype.ext
    apply l.toRingHom.injective
    exact (hh x).symm.trans ((congrArg r hxy).trans (hh y))
  refine ⟨h.range, ?_, ?_, ?_⟩
  · intro x hx
    let c : C := ⟨x, hx⟩
    refine (AlgHom.mem_range h).mpr ⟨algebraMap C N c, ?_⟩
    apply hr
    rw [hh]
    rw [j.commutes]
    rfl
  · have : Algebra.FiniteType ℤ h.range :=
      Algebra.FiniteType.of_surjective h.rangeRestrict h.rangeRestrict_surjective
    exact (Subalgebra.fg_iff_finiteType h.range).mpr inferInstance
  · exact IsIntegrallyClosed.of_equiv (AlgEquiv.ofInjective h hinj).toRingEquiv

end Subalgebra

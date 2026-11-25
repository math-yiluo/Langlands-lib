/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology
public import WeilConjectures.RingTheory.RegularLocalRing.Smooth
public import WeilConjectures.RingTheory.SmoothAtPrimeDifferentialsDimension

/-!
# Auxiliary results for the ring-level Bertini argument

- `Algebra.Smooth.isDomain_of_connectedSpace`: a smooth algebra over a field with connected
  spectrum is a domain.
- `KaehlerDifferential.rank_eq_of_algEquiv`: the rank of the module of differentials is
  invariant under isomorphisms of algebras.
- `Algebra.Smooth.natCast_le_ringKrullDim`: the rank of the differentials of a smooth domain over
  a field is at most its Krull dimension.
-/

@[expose] public section

universe u

open AlgebraicGeometry
open scoped TensorProduct

/-- (E) A smooth algebra over a field with connected spectrum is a domain: its local rings are
regular, hence domains, so its spectrum is irreducible, and it is reduced.
(blueprint: `lemma-curve-preserving-finite-cover--1`) -/
theorem Algebra.Smooth.isDomain_of_connectedSpace {k A : Type u} [Field k] [CommRing A]
    [Algebra k A] [Algebra.Smooth k A] [ConnectedSpace (PrimeSpectrum A)] : IsDomain A := by
  have := Algebra.FiniteType.isNoetherianRing k A
  have : IsReduced A := Algebra.Smooth.isReduced_of_field k A
  have : ConnectedSpace (Spec (.of A)) := ‹ConnectedSpace (PrimeSpectrum A)›
  have : IrreducibleSpace (Spec (.of A)) :=
    irreducibleSpace_of_isDomain_stalk _ fun x ↦
      have := Algebra.Smooth.isRegularLocalRing_localization k A x.asIdeal
      (Spec.stalkIso (.of A) x).commRingCatIsoToRingEquiv.injective.isDomain _
  have : IrreducibleSpace (PrimeSpectrum A) := ‹IrreducibleSpace (Spec (.of A))›
  exact PrimeSpectrum.isDomain_of_irreducibleSpace A

/-- The rank of the module of Kähler differentials is invariant under isomorphisms of
algebras. -/
theorem KaehlerDifferential.rank_eq_of_algEquiv {k : Type*} {R R' : Type u} [CommRing k]
    [CommRing R] [CommRing R'] [Algebra k R] [Algebra k R'] (e : R ≃ₐ[k] R') :
    Module.rank R Ω[R⁄k] = Module.rank R' Ω[R'⁄k] := by
  let : Algebra R R' := e.toRingHom.toAlgebra
  let : Algebra R' R := e.symm.toRingHom.toAlgebra
  have : IsScalarTower k R R' := .of_algebraMap_eq fun x ↦ (e.commutes x).symm
  have : IsScalarTower k R' R := .of_algebraMap_eq fun x ↦ (e.symm.commutes x).symm
  let f := KaehlerDifferential.map k k R R'
  let g := KaehlerDifferential.map k k R' R
  have hgf (x : Ω[R⁄k]) : g (f x) = x := by
    have hx : x ∈ Submodule.span R (Set.range (KaehlerDifferential.D k R)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      simp only [f, g, KaehlerDifferential.map_D]
      congr 1
      exact e.symm_apply_apply a
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
    | smul r y _ hy =>
      rw [LinearMap.map_smul, ← algebraMap_smul R' r (f y), LinearMap.map_smul, hy,
        ← algebraMap_smul R]
      congr 1
      exact e.symm_apply_apply r
  have hfg (x : Ω[R'⁄k]) : f (g x) = x := by
    have hx : x ∈ Submodule.span R' (Set.range (KaehlerDifferential.D k R')) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      simp only [f, g, KaehlerDifferential.map_D]
      congr 1
      exact e.apply_symm_apply a
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
    | smul r y _ hy =>
      rw [LinearMap.map_smul, ← algebraMap_smul R r (g y), LinearMap.map_smul, hy,
        ← algebraMap_smul R']
      congr 1
      exact e.apply_symm_apply r
  let j : Ω[R⁄k] ≃+ Ω[R'⁄k] :=
    { toFun := f
      invFun := g
      left_inv := hgf
      right_inv := hfg
      map_add' := map_add f }
  refine rank_eq_of_equiv_equiv e j e.bijective fun r m ↦ ?_
  simp only [j, AddEquiv.coe_mk, Equiv.coe_fn_mk, LinearMap.map_smul]
  exact (algebraMap_smul R' r (f m)).symm

/-- The rank of the module of differentials of a smooth domain over a field is at most its Krull
dimension: at the generic point, the dimension of the fibre of the differentials is the local
dimension of the spectrum. (blueprint: `lemma-curve-preserving-finite-cover--1`) -/
theorem Algebra.Smooth.natCast_le_ringKrullDim {k A : Type u} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.Smooth k A] {n : ℕ}
    (h : Module.rank A Ω[A⁄k] = n) : (n : WithBot ℕ∞) ≤ ringKrullDim A := by
  let q : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
  have : Algebra.Smooth A (Localization.Away (1 : A)) := .of_isLocalization_Away 1
  have hq : IsSmoothAtPrime k q := ⟨1, q.asIdeal.ne_top_iff_one.mp q.2.ne_top,
    Algebra.Smooth.comp k A (Localization.Away (1 : A))⟩
  obtain ⟨-, hdim⟩ := finiteDimensional_and_finrank_kaehlerDifferential_eq_of_isSmoothAtPrime q hq
  have hrank : Module.rank (⊥ : Ideal A).ResidueField
      ((⊥ : Ideal A).ResidueField ⊗[A] Ω[A⁄k]) = n := by
    rw [IsFractionRing.rank_right_eq A (⊥ : Ideal A).ResidueField,
      IsLocalizedModule.rank_eq (nonZeroDivisors A) le_rfl
        (TensorProduct.mk A (⊥ : Ideal A).ResidueField Ω[A⁄k] 1), h]
  have hfin : Module.finrank (⊥ : Ideal A).ResidueField
      ((⊥ : Ideal A).ResidueField ⊗[A] Ω[A⁄k]) = n := by
    rw [Module.finrank, hrank, Cardinal.toNat_natCast]
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ← hfin]
  refine hdim.le.trans ((iInf₂_le ⊤ trivial).trans ?_)
  exact Topology.IsInducing.subtypeVal.topologicalKrullDim_le

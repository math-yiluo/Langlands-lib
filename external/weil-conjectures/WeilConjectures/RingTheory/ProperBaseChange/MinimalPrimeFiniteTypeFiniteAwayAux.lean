/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Defs
import WeilConjectures.RingTheory.Finite.FiniteTypeAlgebraFiniteSpectrum
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.FiniteStability

/-! An explicit finite spanning family after shrinking at a minimal prime.
(blueprint: lem-weil-pbc-minimal-prime-finite-type-algebra-finite-away-aux)
-/

@[expose] public section

universe u v

private theorem integral_of_nil_quotient
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (J : Ideal B) (hJ : J ≤ nilradical B) [Module.Finite A (B ⧸ J)]
    (x : B) : _root_.IsIntegral A x := by
  obtain ⟨P, hP, he⟩ := _root_.IsIntegral.of_finite A (Ideal.Quotient.mk J x)
  have hz : Polynomial.aeval x P ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Polynomial.aeval ((Ideal.Quotient.mkₐ A J) x) P = 0 at he
    rw [Polynomial.aeval_algHom_apply] at he
    exact he
  obtain ⟨n, hn⟩ := mem_nilradical.mp (hJ hz)
  exact ⟨P ^ n, hP.pow n, by
    change Polynomial.aeval x (P ^ n) = 0
    rw [map_pow, hn]⟩

private theorem integral_at_minimal
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : Ideal R) (hp : p ∈ minimalPrimes R)
    [p.IsPrime]
    (hfinite : {q : PrimeSpectrum S | Ideal.comap (algebraMap R S) q.asIdeal = p}.Finite) :
    Algebra.IsIntegral (Localization.AtPrime p)
      (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) := by
  let Rp := Localization.AtPrime p
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let J := (IsLocalRing.maximalIdeal Rp).map (algebraMap Rp Sp)
  have hfin : Finite (PrimeSpectrum (p.Fiber S)) := by
    apply (PrimeSpectrum.preimageEquivFiber R S ⟨p, inferInstance⟩).finite_iff.mp
    exact Set.Finite.to_subtype (hfinite.subset fun q hq ↦
      congrArg PrimeSpectrum.asIdeal hq)
  let : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
  have : Module.Finite p.ResidueField (p.Fiber S) :=
    (Algebra.finiteType_finiteSpectrum p.ResidueField (p.Fiber S) hfin).2.1
  have : Module.Finite Rp (p.Fiber S) := Module.Finite.trans p.ResidueField _
  let e : p.Fiber S ≃ₐ[Rp] Sp ⧸ J :=
    ((Ideal.Fiber.algEquivQuotient p).restrictScalars R).extendScalarsOfIsLocalization
      Rp p.primeCompl
  have : Module.Finite Rp (Sp ⧸ J) := Module.Finite.of_surjective
    e.toLinearMap e.surjective
  have : Ring.KrullDimLE 0 Rp := Ring.KrullDimLE.of_isLocalization p hp Rp
  have hJ : J ≤ nilradical Sp := by
    rw [Ideal.map_le_iff_le_comap, ← Ring.KrullDimLE.nilradical_eq_maximalIdeal]
    exact fun x hx ↦ IsNilpotent.map hx _
  exact ⟨integral_of_nil_quotient J hJ⟩

namespace RingHom

/-- The coefficient-lifting and monic-polynomial argument for generic finiteness produces
an explicit finite spanning family after one principal localization.  This is the strict
finite-spanning intermediate form used by the generic-finiteness theorem.

Source: Stacks Project, Algebra, Tag 02ML, `lemma-generically-finite`.  The proof chooses
finite algebra generators, obtains monic equations in the localization at the minimal
prime from finite-dimensionality of the fibre, clears their finitely many denominators,
and reduces monomials by those equations.

(blueprint: lem-weil-pbc-minimal-prime-finite-type-algebra-finite-away-aux).

Proof: The finite-spectrum fibre theorem gives finite-dimensionality over the residue field.
Lift monic annihilating equations through the prime localization, use local nilpotence of the
extended minimal prime to obtain powers that vanish, clear the finitely many denominators and
annihilators by multiplying an element outside the prime, and reduce monomials by the resulting
monic equations. -/
theorem exists_finite_span_awayMap_of_finite_fiber_minimalPrime
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.FiniteType) (p : Ideal R) (hp : p ∈ minimalPrimes R)
    (hfinite : {q : PrimeSpectrum S | Ideal.comap φ q.asIdeal = p}.Finite) :
    ∃ g : R, g ∉ p ∧
      letI : Algebra (Localization.Away g) (Localization.Away (φ g)) :=
        (Localization.awayMap φ g).toAlgebra
      ∃ n : ℕ, ∃ b : Fin n → Localization.Away (φ g),
        Submodule.span (Localization.Away g) (Set.range b) = ⊤ := by
  classical
  let : Algebra R S := φ.toAlgebra
  have : Algebra.FiniteType R S := hφ
  have : p.IsPrime := hp.1.1
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  have : Algebra.IsIntegral (Localization.AtPrime p) Sp := integral_at_minimal p hp hfinite
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  have hmult (x : S) : ∃ m : R, m ∉ p ∧ _root_.IsIntegral R (m • x) := by
    obtain ⟨m, hm⟩ := _root_.IsIntegral.exists_multiple_integral_of_isLocalization p.primeCompl
      (algebraMap S Sp x) (Algebra.IsIntegral.isIntegral (R := Localization.AtPrime p) _)
    obtain ⟨t, ht, htx⟩ := IsLocalization.exists_isIntegral_smul_of_isIntegral_map
      (Sₘ := Sp) p.primeCompl (x := (m : R) • x) (by
        simpa only [Submonoid.smul_def, Algebra.smul_def, map_mul,
          IsScalarTower.algebraMap_apply R S Sp] using hm)
    exact ⟨t * m, p.primeCompl.mul_mem ht m.property, by simpa [mul_smul] using htx⟩
  choose m hm hi using hmult
  let g := ∏ x ∈ s, m x
  have hg : g ∉ p := by
    simpa only [g, Ideal.IsPrime.prod_mem_iff, not_exists, not_and] using
      (fun x (_ : x ∈ s) ↦ hm x)
  refine ⟨g, hg, ?_⟩
  let Rg := Localization.Away g
  let Sg := Localization.Away (φ g)
  let : Algebra Rg Sg := (Localization.awayMap φ g).toAlgebra
  have : IsScalarTower R Rg Sg :=
    isScalarTower_localizationAlgebra (Submonoid.powers g) S
  have hgen (x : S) (hx : x ∈ s) : _root_.IsIntegral Rg (algebraMap S Sg x) := by
    have hu : IsUnit (algebraMap R Rg (m x)) := isUnit_of_dvd_unit
      (map_dvd (algebraMap R Rg) (Finset.dvd_prod_of_mem m hx))
      (IsLocalization.Away.algebraMap_isUnit g)
    obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp hu
    have hix : _root_.IsIntegral Rg (algebraMap S Sg (m x • x)) :=
      ((hi x).map (IsScalarTower.toAlgHom R S Sg)).tower_top
    have he : algebraMap S Sg x =
        algebraMap Rg Sg c * algebraMap S Sg (m x • x) := by
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R S Sg,
        IsScalarTower.algebraMap_apply R Rg Sg, ← mul_assoc, ← map_mul, mul_comm c,
        hc, map_one, one_mul]
    rw [he]
    exact isIntegral_algebraMap.mul hix
  let t : Finset Sg := s.image (algebraMap S Sg)
  have ht : Algebra.adjoin Rg (t : Set Sg) = ⊤ := by
    let T := Algebra.adjoin Rg (t : Set Sg)
    have hle : Algebra.adjoin R (s : Set S) ≤
        (T.restrictScalars R).comap (IsScalarTower.toAlgHom R S Sg) := by
      apply Algebra.adjoin_le
      intro x hx
      exact Algebra.subset_adjoin (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    have hmem (x : S) : algebraMap S Sg x ∈ T := hle (hs ▸ Algebra.mem_top)
    apply Algebra.eq_top_iff.mpr
    intro z
    obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ :=
      IsLocalization.exists_mk'_eq (Submonoid.powers (φ g)) z
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    apply T.mul_mem (hmem x)
    have he : IsLocalization.mk' (M := Submonoid.powers (φ g)) Sg 1 ⟨φ g ^ n, n, rfl⟩ =
        algebraMap Rg Sg (IsLocalization.mk' (M := Submonoid.powers g) Rg 1 ⟨g ^ n, n, rfl⟩) := by
      rw [IsLocalization.algebraMap_mk' (S := S)]
      simp only [map_one, map_pow]
      rfl
    rw [he]
    exact T.algebraMap_mem _
  have hti (x : Sg) (hx : x ∈ t) : _root_.IsIntegral Rg x := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hgen y hy
  have hfg : (⊤ : Submodule Rg Sg).FG := by
    simpa only [ht, Algebra.top_toSubmodule] using
      (fg_adjoin_of_finite t.finite_toSet hti)
  exact Submodule.fg_iff_exists_fin_generating_family.mp hfg

end RingHom

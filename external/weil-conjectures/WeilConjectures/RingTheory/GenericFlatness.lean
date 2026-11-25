/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.RingHom.Flat

import WeilConjectures.Mathlib.RingTheory.FinitePresentation
import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Generic flatness for finite type algebras over arbitrary domains

Source: Stacks Project, Tags 051T and 051S.
(blueprint: lem-sbc-finite-type-algebra-generic-flatness)
-/

@[expose] public section

universe u

namespace RingHom

private theorem exists_fg_subideal_localized (P Q : Type u)
    [CommRing P] [CommRing Q] [Algebra P Q] (S : Submonoid P)
    [IsLocalization S Q] [IsNoetherianRing Q] (I : Ideal P) :
    ∃ J : Ideal P, J.FG ∧ J ≤ I ∧ J.map (algebraMap P Q) = I.map (algebraMap P Q) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (I.map (algebraMap P Q)))
  have hgen (y : s) : ∃ x : I × S, y.val * algebraMap P Q x.2 = algebraMap P Q x.1 :=
    (IsLocalization.mem_map_algebraMap_iff S Q).mp
      (hs ▸ Ideal.subset_span y.property)
  choose x hx using hgen
  let J : Ideal P := Ideal.span (Set.range fun y : s ↦ (x y).1.val)
  have hJI : J ≤ I := Ideal.span_le.mpr (by rintro _ ⟨y, rfl⟩; exact (x y).1.property)
  refine ⟨J, Submodule.fg_def.mpr ⟨_, Set.finite_range _, rfl⟩, hJI, ?_⟩
  apply le_antisymm (Ideal.map_mono hJI)
  rw [← hs]
  apply Ideal.span_le.mpr
  intro y hy
  apply (IsLocalization.mem_map_algebraMap_iff S Q).mpr
  exact ⟨⟨⟨(x ⟨y, hy⟩).1, Ideal.subset_span ⟨⟨y, hy⟩, rfl⟩⟩,
    (x ⟨y, hy⟩).2⟩, hx ⟨y, hy⟩⟩

private theorem exists_finitePresentation_torsion_cover (R B : Type u)
    [CommRing R] [CommRing B] [IsDomain R] [Algebra R B] [Algebra.FiniteType R B] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A),
      Algebra.FinitePresentation R A ∧ ∃ f : A →ₐ[R] B,
        Function.Surjective f ∧ ∀ x : A, f x = 0 → ∃ r : R, r ≠ 0 ∧ r • x = 0 := by
  classical
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R B)
  let P := MvPolynomial (Fin n) R
  let Q := MvPolynomial (Fin n) (FractionRing R)
  let : Algebra P Q := MvPolynomial.algebraMvPolynomial
  let S : Submonoid P := (nonZeroDivisors R).map MvPolynomial.C
  let I : Ideal P := RingHom.ker g.toRingHom
  obtain ⟨J, hfg, hJI, hmap⟩ := exists_fg_subideal_localized P Q S I
  let A := P ⧸ J
  have : Algebra.FinitePresentation R P :=
    Algebra.FinitePresentation.mvPolynomial_of_finitePresentation (Fin n)
  have : Algebra.FinitePresentation R A := Algebra.FinitePresentation.quotient hfg
  let f : A →ₐ[R] B := Ideal.Quotient.liftₐ J g fun p hp ↦ hJI hp
  refine ⟨A, inferInstance, inferInstance, inferInstance, f, ?_, ?_⟩
  · intro b
    obtain ⟨p, rfl⟩ := hg b
    exact ⟨Ideal.Quotient.mk J p, rfl⟩
  · intro x hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hp : p ∈ I := hx
    have hpmap : algebraMap P Q p ∈ J.map (algebraMap P Q) := by
      rw [hmap]
      exact Ideal.mem_map_of_mem _ hp
    obtain ⟨m, hm, hmp⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff S Q J p).mp hpmap
    obtain ⟨r, hr, rfl⟩ := hm
    refine ⟨r, nonZeroDivisors.ne_zero hr, ?_⟩
    change r • (Ideal.Quotient.mkₐ R J) p = 0
    rw [← map_smul, MvPolynomial.smul_eq_C_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmp

private theorem exists_flat_away_of_finitePresentation (R A : Type u)
    [CommRing R] [CommRing A] [IsDomain R] [Algebra R A]
    [Algebra.FinitePresentation R A] :
    ∃ a : R, a ≠ 0 ∧ Module.Flat R (Localization.Away (algebraMap R A a)) := by
  obtain ⟨R₀, A₀, _, _, _, _, hfg, hfp, hp⟩ :=
    Algebra.FinitePresentation.exists_fg_subalgebra_isPushout R A
  have : Algebra.FiniteType ℤ R₀ := R₀.fg_iff_finiteType.mp hfg
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  have : Algebra.FinitePresentation R₀ A₀ := hfp
  have : Algebra.IsPushout R₀ R A₀ A := hp
  obtain ⟨a₀, ha₀, hflat⟩ := Module.exists_flat_localizedModule_powers (R := R₀) (S := A₀) A₀
  let C := Localization.Away (algebraMap R₀ A₀ a₀)
  let D := Localization.Away (algebraMap R A (a₀ : R))
  have : IsScalarTower R₀ A₀ C := inferInstance
  have : IsLocalizedModule (Submonoid.powers a₀)
      ((Algebra.linearMap A₀ C).restrictScalars R₀) :=
    IsLocalizedModule.restrictScalars_powers a₀ (Algebra.linearMap A₀ C)
  have : Module.Flat R₀ (LocalizedModule (Submonoid.powers a₀) A₀) := hflat
  have : Module.Flat R₀ C := .of_linearEquiv
    (IsLocalizedModule.linearEquiv (Submonoid.powers a₀)
      ((Algebra.linearMap A₀ C).restrictScalars R₀)
      (LocalizedModule.mkLinearMap (Submonoid.powers a₀) A₀))
  have : IsScalarTower R A D := inferInstance
  have : IsScalarTower R₀ R D := inferInstance
  have : IsScalarTower A₀ A D := inferInstance
  have : IsScalarTower R₀ A₀ D := .to₁₂₄ R₀ A₀ A D
  have hcoe : algebraMap R₀ R a₀ = (a₀ : R) := rfl
  have hu : IsUnit (algebraMap A₀ D (algebraMap R₀ A₀ a₀)) := by
    rw [← IsScalarTower.algebraMap_apply R₀ A₀ D,
      IsScalarTower.algebraMap_apply R₀ R D, IsScalarTower.algebraMap_apply R A D]
    rw [hcoe]
    exact IsLocalization.Away.algebraMap_isUnit _
  let : Algebra C D := (IsLocalization.Away.lift (algebraMap R₀ A₀ a₀) hu).toAlgebra
  have : IsScalarTower A₀ C D := .of_algebraMap_eq fun x ↦
    (IsLocalization.Away.lift_eq (algebraMap R₀ A₀ a₀) hu x).symm
  have : IsScalarTower R₀ C D := .to₁₃₄ R₀ A₀ C D
  have : IsScalarTower R₀ A D := .to₁₃₄ R₀ R A D
  have : IsLocalization (Algebra.algebraMapSubmonoid A (.powers (algebraMap R₀ A₀ a₀))) D := by
    simpa only [Algebra.algebraMapSubmonoid_powers,
      ← IsScalarTower.algebraMap_apply R₀ A₀ A,
      IsScalarTower.algebraMap_apply R₀ R A, hcoe] using
      (inferInstance : IsLocalization.Away (algebraMap R A (a₀ : R)) D)
  have : Algebra.IsPushout A₀ A C D :=
    Algebra.isPushout_of_isLocalization (.powers (algebraMap R₀ A₀ a₀)) C A D
  have : Algebra.IsPushout A₀ C A D := Algebra.IsPushout.symm inferInstance
  have : Algebra.IsPushout R₀ A₀ R A := Algebra.IsPushout.symm inferInstance
  have : Algebra.IsPushout R₀ C R D :=
    (Algebra.IsPushout.comp_iff R₀ A₀ R A).mpr inferInstance
  have : Algebra.IsPushout R₀ R C D := Algebra.IsPushout.symm inferInstance
  exact ⟨a₀, by exact_mod_cast ha₀, .of_linearEquiv
    (Algebra.IsPushout.equiv R₀ R C D).symm.toLinearEquiv⟩

/-- A finite type algebra over a domain is flat after one nonzero base element is inverted.
The conclusion uses any model of the localization of the target algebra.

Source: Stacks Project, Tag 051T, with M equal to the algebra itself; Tag 051S.
Proof: choose a surjection P = R[t₁,...,tₙ] → B and let K be the fraction field
of R. The relation ideal in K[t₁,...,tₙ] is finitely generated by Noetherianity.
Clear denominators to lift finitely many generators into the relation ideal in P.
Let B' be the quotient by their ideal. The surjection B' → B becomes an
isomorphism after extending scalars to K. Its finite presentation descends to
a subring R₀ of R generated over the integers by finitely many coefficients.
This is a Noetherian domain. Noetherian generic freeness for the finite type
R₀-algebra B'₀ yields a nonzero element a₀ such that (B'₀)_a₀ is free over
(R₀)_a₀. Base change to R shows B'_a is free over R_a, where a is the image
of a₀ and remains nonzero. The kernel of B'_a → B_a is zero after extension
to K. A free module over the domain R_a injects into its extension to K, so
that kernel was already zero. Thus B_a is free over R_a and flat over R,
since R_a is flat over R. Any localization T in the statement is canonically
isomorphic as a B-algebra to B_a, transporting this flatness. If B = 0, take
a = 1; the localized zero algebra is flat. The element inverted is in R,
not an arbitrary target element, and no Noetherian assumption on R is needed.

(blueprint: lem-sbc-finite-type-algebra-generic-flatness) -/
theorem exists_nonzero_flat_localizationAway {R B : Type u}
    [CommRing R] [CommRing B] [IsDomain R] (φ : R →+* B) (hφ : φ.FiniteType) :
    ∃ a : R, a ≠ 0 ∧ ∀ (T : Type u) [CommRing T] [Algebra B T]
      [IsLocalization.Away (φ a) T], ((algebraMap B T).comp φ).Flat := by
  let : Algebra R B := φ.toAlgebra
  have : Algebra.FiniteType R B := hφ
  obtain ⟨A, _, _, hfp, f, hf, htors⟩ := exists_finitePresentation_torsion_cover R B
  have : Algebra.FinitePresentation R A := hfp
  obtain ⟨a, ha, hflat⟩ := exists_flat_away_of_finitePresentation R A
  refine ⟨a, ha, ?_⟩
  intro T _ _ _
  let C := Localization.Away (algebraMap R A a)
  have : Module.Flat R C := hflat
  let : Algebra R T := ((algebraMap B T).comp φ).toAlgebra
  have : IsScalarTower R B T := .of_algebraMap_eq' rfl
  have hfa : f (algebraMap R A a) = φ a := f.commutes a
  have : IsLocalization.Away (f (algebraMap R A a)) T := by rw [hfa]; infer_instance
  let q : C →+* T := IsLocalization.Away.map C T f.toRingHom (algebraMap R A a)
  have hinj : Function.Injective q := by
    apply (IsLocalization.Away.map_injective_iff T f.toRingHom (algebraMap R A a)).mpr
    intro x hx
    obtain ⟨r, hr, hrx⟩ := htors x hx
    have hz : algebraMap A C x = 0 := by
      apply (smul_eq_zero_iff_right hr).mp
      change r • (IsScalarTower.toAlgHom R A C) x = 0
      rw [← map_smul, hrx, map_zero]
    obtain ⟨m, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R A a)) C x).mp hz
    obtain ⟨n, hn⟩ := m.property
    exact ⟨n, by simpa only [← hn] using hm⟩
  have hsurj : Function.Surjective q := by
    apply (IsLocalization.Away.map_surjective_iff C T f.toRingHom
      (algebraMap R A a)).mpr
    intro b
    obtain ⟨x, rfl⟩ := hf b
    exact ⟨x, 0, by simp⟩
  have hcomm : q.comp ((algebraMap A C).comp (algebraMap R A)) =
      (algebraMap B T).comp φ := by
    ext r
    change q (algebraMap A C (algebraMap R A r)) = algebraMap B T (φ r)
    dsimp only [q, IsLocalization.Away.map]
    rw [IsLocalization.map_eq]
    exact congrArg (algebraMap B T) (f.commutes r)
  rw [← hcomm]
  apply RingHom.Flat.comp
  · change (algebraMap R C).Flat
    exact RingHom.flat_algebraMap_iff.mpr hflat
  · exact RingHom.Flat.of_bijective ⟨hinj, hsurj⟩

end RingHom

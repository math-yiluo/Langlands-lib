/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs

import WeilConjectures.RingTheory.DvrUnitRootAtPrime
import Mathlib.RingTheory.Ideal.GoingUp

/-! # Local DVR square for a root of a unit

Source: Stacks Project, Tag 0BRM, first claim of the proof.
(blueprint: lem-sbc-dvr-unit-root-local-square) -/

@[expose] public section

universe u
namespace RingTheory

/-- The ring construction in the unit-root argument, with a rational root presentation.

Source: Stacks Project, Tag 0BRM, first claim of the proof.
(blueprint: lem-sbc-dvr-unit-root-local-square)

Proof: Put C = A[X]/(X^e-v) and D = T[X]/(X^e-v_T). The positive exponent
makes both defining polynomials monic, so the algebras are finite free and
faithfully flat. The root is a unit since its e-th power is a unit, and e is
invertible; hence the derivative e*X^(e-1) is a unit in each algebra. Both
algebras are therefore finite etale over their bases. Choose a maximal ideal
q of D above the maximal ideal of T, and let p be its inverse image in C.
The composite A -> T -> D contracts q to the maximal ideal of A because
A -> T is local. Since C is finite over A, p is maximal. Set A' = C_p and
T' = D_q. Localization of the map C -> D gives A' -> T'; the square commutes
and all three maps are local. An etale localization over a DVR is a regular
local domain of dimension one, hence a DVR: flatness preserves the base
uniformizer as a nonzerodivisor, and the etale closed fibre is a field, so
that uniformizer generates the maximal ideal. The residue extension of A'
over A is finite separable. Faithful flatness of the local map T -> T'
gives injectivity. The root r in A' satisfies the defining power relation.
Every element of D is a polynomial in its root with coefficients in T.
Every element of D_q is a quotient of two such elements with denominator
outside q, whose image is a unit and thus nonzero in T'. Clearing this
denominator gives the final polynomial relation. For e=1 this is the
identity square and the usual constant-polynomial presentation. No
ramification or residue-separability hypothesis on T/A is used. -/
theorem dvr_unit_root_local_square
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (e : ℕ) (hepos : 0 < e) (he : IsUnit (e : A)) (v : Aˣ)
    (T : Type u) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra A T] [IsLocalHom (algebraMap A T)] :
    ∃ (A' : Type u) (_ : CommRing A') (_ : IsDomain A')
      (_ : IsDiscreteValuationRing A') (aAA' : Algebra A A'),
    letI := aAA'
    ∃ (hAA' : IsLocalHom (algebraMap A A')) (r : A'),
    letI := hAA'
    r ^ e = algebraMap A A' (v : A) ∧
    Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A') ∧
    ∃ (T' : Type u) (_ : CommRing T') (_ : IsDomain T')
      (_ : IsDiscreteValuationRing T') (aTT' : Algebra T T') (aA'T' : Algebra A' T'),
    letI := aTT'
    letI := aA'T'
    ∃ (_ : IsLocalHom (algebraMap T T')) (_ : IsLocalHom (algebraMap A' T')),
    (∀ a : A, algebraMap T T' (algebraMap A T a) =
      algebraMap A' T' (algebraMap A A' a)) ∧
    Function.Injective (algebraMap T T') ∧
    ∀ x : T', ∃ p q : Polynomial T,
      q.eval₂ (algebraMap T T') (algebraMap A' T' r) ≠ 0 ∧
      x * q.eval₂ (algebraMap T T') (algebraMap A' T' r) =
        p.eval₂ (algebraMap T T') (algebraMap A' T' r) := by
  classical
  let P := (Polynomial.X : Polynomial A) ^ e - Polynomial.C (v : A)
  let vT : Tˣ := v.map (algebraMap A T)
  let Q := (Polynomial.X : Polynomial T) ^ e - Polynomial.C (vT : T)
  let C := AdjoinRoot P
  let D := AdjoinRoot Q
  have hQ : Q.Monic := Polynomial.monic_X_pow_sub_C _ hepos.ne'
  let : Module.Finite T D := hQ.finite_adjoinRoot
  let : FaithfulSMul T D := (faithfulSMul_iff_algebraMap_injective T D).mpr (by
    apply AdjoinRoot.of.injective_of_degree_ne_zero
    rw [Polynomial.degree_eq_natDegree hQ.ne_zero, Polynomial.natDegree_X_pow_sub_C]
    exact_mod_cast hepos.ne')
  obtain ⟨q, hqmax, hq⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (IsLocalRing.maximalIdeal T) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective T D)]
      exact bot_le)
  let : q.IsMaximal := hqmax
  let φ : C →+* D := AdjoinRoot.map (algebraMap A T) P Q (by
    simp [P, Q, vT])
  have hφ (a : A) : φ (algebraMap A C a) =
      algebraMap T D (algebraMap A T a) := by
    exact AdjoinRoot.map_of (algebraMap A T) P Q _ a
  let p : Ideal C := q.comap φ
  have hp : p.comap (algebraMap A C) = IsLocalRing.maximalIdeal A := by
    ext a
    change φ (algebraMap A C a) ∈ q ↔ a ∈ IsLocalRing.maximalIdeal A
    rw [hφ]
    change algebraMap A T a ∈ q.under T ↔ _
    rw [hq]
    exact SetLike.ext_iff.mp (IsLocalRing.maximalIdeal_comap (algebraMap A T)) a
  obtain ⟨hdomA', hdvrA', hAA', hsep, hinjA'⟩ := dvr_unit_root_atPrime A e hepos he v p hp
  have heT : IsUnit (e : T) := by
    simpa only [map_natCast] using he.map (algebraMap A T)
  obtain ⟨hdomT', hdvrT', hTT', hsepT', hinj⟩ :=
    dvr_unit_root_atPrime T e hepos heT vT q hq
  let A' := Localization.AtPrime p
  let T' := Localization.AtPrime q
  let := hdomA'
  let := hdvrA'
  let := hAA'
  let := hdomT'
  let := hdvrT'
  let := hTT'
  let f : A' →+* T' := Localization.localRingHom p q φ rfl
  let : Algebra A' T' := f.toAlgebra
  have hA'T' : IsLocalHom (algebraMap A' T') :=
    Localization.isLocalHom_localRingHom p q φ rfl
  have hf (c : C) : algebraMap A' T' (algebraMap C A' c) =
      algebraMap D T' (φ c) := Localization.localRingHom_to_map p q φ rfl c
  let r : A' := algebraMap C A' (AdjoinRoot.root P)
  have hr : r ^ e = algebraMap A A' (v : A) := by
    have hroot : AdjoinRoot.root P ^ e = algebraMap A C (v : A) := by
      simpa only [P, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, sub_eq_zero, ← AdjoinRoot.algebraMap_eq] using
        AdjoinRoot.eval₂_root P
    change (algebraMap C A' (AdjoinRoot.root P)) ^ e = _
    rw [← map_pow, hroot, ← IsScalarTower.algebraMap_apply A C A']
  have hsquare (a : A) : algebraMap T T' (algebraMap A T a) =
      algebraMap A' T' (algebraMap A A' a) := by
    rw [IsScalarTower.algebraMap_apply A C A', hf, hφ,
      ← IsScalarTower.algebraMap_apply T D T']
  have hrT : algebraMap A' T' r = algebraMap D T' (AdjoinRoot.root Q) := by
    rw [show r = algebraMap C A' (AdjoinRoot.root P) from rfl, hf]
    exact congrArg (algebraMap D T') (AdjoinRoot.map_root (algebraMap A T) P Q _)
  refine ⟨A', inferInstance, hdomA', hdvrA', inferInstance, hAA', r, hr, hsep,
    T', inferInstance, hdomT', hdvrT', inferInstance, inferInstance, hTT', hA'T',
    hsquare, hinj, ?_⟩
  intro x
  obtain ⟨a, b, hb⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  obtain ⟨pa, hpa⟩ := AdjoinRoot.mk_surjective a
  obtain ⟨pb, hpb⟩ := AdjoinRoot.mk_surjective (b : D)
  have heval (w : Polynomial T) :
      w.eval₂ (algebraMap T T') (algebraMap A' T' r) =
        algebraMap D T' (AdjoinRoot.mk Q w) := by
    rw [hrT]
    rw [IsScalarTower.algebraMap_eq T D T', ← Polynomial.hom_eval₂]
    congr 1
    exact AdjoinRoot.aeval_eq w
  refine ⟨pa, pb, ?_, ?_⟩
  · rw [heval, hpb]
    exact (IsLocalization.map_units T' b).ne_zero
  · rw [heval, heval, hpa, hpb, ← hb]
    exact IsLocalization.mk'_spec T' a b

end RingTheory

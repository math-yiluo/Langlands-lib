/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import WeilConjectures.RingTheory.DvrUnitRootAtPrime
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Ideal.GoingUp

/-! # A weakly unramified local unit-root cover of a DVR diagram

Source: Stacks Project, Tag 0BRM, the first claim in its proof.
(blueprint: lem-sbc-dvr-unit-root-generation) -/

@[expose] public section

universe u
namespace RingTheory

private theorem unit_root_etale
    (R : Type u) [CommRing R] (e : ℕ) (hepos : 0 < e)
    (he : IsUnit (e : R)) (v : Rˣ) :
    Algebra.Etale R (AdjoinRoot ((Polynomial.X : Polynomial R) ^ e -
      Polynomial.C (v : R))) := by
  let P := (Polynomial.X : Polynomial R) ^ e - Polynomial.C (v : R)
  let B := AdjoinRoot P
  have hmonic : P.Monic := Polynomial.monic_X_pow_sub_C _ hepos.ne'
  have hroot : AdjoinRoot.root P ^ e = algebraMap R B (v : R) := by
    simpa only [P, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, sub_eq_zero, ← AdjoinRoot.algebraMap_eq] using
      AdjoinRoot.eval₂_root P
  have hunit : IsUnit (AdjoinRoot.root P) := by
    apply (isUnit_pow_iff hepos.ne').mp
    rw [hroot]
    exact v.isUnit.map (algebraMap R B)
  have hderiv : IsUnit (Polynomial.aeval (AdjoinRoot.root P) P.derivative) := by
    have heB : IsUnit (algebraMap R B (e : R)) := he.map (algebraMap R B)
    simpa only [P, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_C, sub_zero, map_mul, Polynomial.aeval_C,
      map_pow, Polynomial.aeval_X] using heB.mul (hunit.pow (e - 1))
  exact show Algebra.Etale R B by
    let E : StandardEtalePair R := ⟨P, hmonic, P.derivative, ⟨1, 0, 1, by simp⟩⟩
    have hm : E.HasMap (AdjoinRoot.root P) :=
      ⟨by simp [E, AdjoinRoot.aeval_eq], hderiv⟩
    let equiv : E.Ring ≃ₐ[R] B := .ofAlgHom
      (E.lift (AdjoinRoot.root P) hm)
      (AdjoinRoot.liftAlgHom P (Algebra.ofId R E.Ring) E.X E.hasMap_X.1)
      (AdjoinRoot.algHom_ext (by
        simp only [AlgHom.comp_apply, AdjoinRoot.liftAlgHom_root,
          StandardEtalePair.lift_X]
        rfl))
      (StandardEtalePair.hom_ext (by
        simp only [AlgHom.comp_apply, StandardEtalePair.lift_X, AlgHom.id_apply]
        exact AdjoinRoot.liftAlgHom_root _ _ _ _))
    exact Algebra.Etale.of_equiv equiv

private theorem root_localization_fraction_adjoin
    (T F R U L : Type u) [CommRing T] [Field F] [CommRing R]
    [CommRing U] [IsDomain U] [Field L] [Algebra T F] [Algebra F L]
    [Algebra R L] [Algebra U L] [IsFractionRing U L]
    (P : Polynomial T) (hP : P.Monic) [Algebra (AdjoinRoot P) U]
    (M : Submonoid (AdjoinRoot P)) [IsLocalization M U]
    (g : AdjoinRoot P →+* L)
    (hg : ∀ b, g b = algebraMap U L (algebraMap (AdjoinRoot P) U b))
    (hc : ∀ t, g (AdjoinRoot.of P t) = algebraMap F L (algebraMap T F t))
    (r : R) (hr : g (AdjoinRoot.root P) = algebraMap R L r) :
    Algebra.adjoin R (Set.range (algebraMap F L)) = ⊤ := by
  let x := g (AdjoinRoot.root P)
  let E := IntermediateField.adjoin F ({x} : Set L)
  have hx : IsIntegral F x := by
    apply IsIntegral.map_of_comp_eq (algebraMap T F) g
      (RingHom.ext fun t ↦ (hc t).symm) (AdjoinRoot.isIntegral_root' hP)
  have hE : E.toSubalgebra = Algebra.adjoin F ({x} : Set L) :=
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hx.isAlgebraic
  have hB (b : AdjoinRoot P) : g b ∈ E := by
    induction b using AdjoinRoot.induction_on with
    | ih p =>
      induction p using Polynomial.induction_on' with
      | add p q hp hq => simpa only [map_add] using E.add_mem hp hq
      | monomial n a =>
        simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
          AdjoinRoot.mk_C, AdjoinRoot.mk_X, hc]
        exact E.mul_mem (E.algebraMap_mem _) (E.toSubalgebra.pow_mem
          (IntermediateField.subset_adjoin F _ (Set.mem_singleton x)) n)
  have hU (z : U) : algebraMap U L z ∈ E := by
    obtain ⟨b, s, hz⟩ := IsLocalization.exists_mk'_eq M z
    have heq : algebraMap U L z = g b / g s := by
      have hmul := congrArg (algebraMap U L) (IsLocalization.mk'_spec U b s)
      rw [hz] at hmul
      rw [map_mul, ← hg, ← hg] at hmul
      apply (eq_div_iff ?_).mpr hmul
      rw [hg]
      simpa only [map_zero] using (IsFractionRing.injective U L).ne
        (IsUnit.ne_zero (IsLocalization.map_units U s))
    rw [heq]
    exact E.div_mem (hB b) (hB s)
  have htop : E = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective U z
    exact E.div_mem (hU a) (hU b)
  let S := Algebra.adjoin R (Set.range (algebraMap F L))
  have hle : E.toSubalgebra.toSubring ≤ S.toSubring := by
    rw [hE]
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem y hy =>
      obtain rfl := Set.mem_singleton_iff.mp hy
      rw [show x = algebraMap R L r from hr]
      exact S.algebraMap_mem r
    | algebraMap f => exact Algebra.subset_adjoin ⟨f, rfl⟩
    | add a b ha hb ia ib => exact S.add_mem ia ib
    | mul a b ha hb ia ib => exact S.mul_mem ia ib
  apply top_unique
  intro z _
  apply hle
  rw [htop]
  trivial

/-- Adjoining a root of a unit simultaneously above the two DVRs of a local diagram.

Source: Stacks Project, Tag 0BRM, the paragraph beginning with the claim that the
unit can be assumed to be an e-th power.
(blueprint: lem-sbc-dvr-unit-root-generation)

Proof: Form C = A[X]/(X^e-v). Its root is a unit, and e is a unit, so its derivative
is a unit. Thus C is finite etale over A. Form D = T tensor_A C, which is finite
etale over T. Choose a maximal ideal of D above the maximal ideal of T and contract
it to a prime of C. Localize D and C at these primes, obtaining T' and A'. These
are DVR domains: an etale local extension of a DVR is regular of dimension one.
Both maps are local and their square commutes. Since A -> A' is essentially
etale, the extension of its maximal ideal is the maximal ideal of A'. The image r
of X satisfies r^e = v. Take F' = Frac(T').
The
injection T -> T' extends uniquely to a field map iF from F = Frac(T), and the
localization map A' -> T' -> F' is compatible with A. The field F' is the selected
field factor of F[X]/(X^e-v). Hence it is generated as an F-algebra by the root:
the root is algebraic, so this algebra is already a field. Since r belongs to A',
F' is generated as an A'-algebra by iF(F). This construction does not use any
ramification or residue-separability assumption on T/A. For e = 1 use A, T and F
itself, with r = v. -/
theorem dvr_unit_root_weakly_unramified_diagram
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (e : ℕ) (hepos : 0 < e) (he : IsUnit (e : A)) (v : Aˣ)
    (T : Type u) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra A T] [IsLocalHom (algebraMap A T)]
    (F : Type u) [Field F] [Algebra A F] [Algebra T F]
    [IsFractionRing T F] [IsScalarTower A T F] :
    ∃ (A' : Type u) (_ : CommRing A') (_ : IsDomain A')
      (_ : IsDiscreteValuationRing A') (aAA' : Algebra A A'),
    letI := aAA'
    ∃ (hAA' : IsLocalHom (algebraMap A A')) (r : A'),
    letI := hAA'
    r ^ e = algebraMap A A' (v : A) ∧
    (IsLocalRing.maximalIdeal A).map (algebraMap A A') = IsLocalRing.maximalIdeal A' ∧
    ∃ (T' : Type u) (_ : CommRing T') (_ : IsDomain T')
      (_ : IsDiscreteValuationRing T') (aTT' : Algebra T T') (aA'T' : Algebra A' T'),
    letI := aTT'
    letI := aA'T'
    ∃ (_ : IsLocalHom (algebraMap T T')) (_ : IsLocalHom (algebraMap A' T')),
    (∀ a : A, algebraMap T T' (algebraMap A T a) =
      algebraMap A' T' (algebraMap A A' a)) ∧
    ∃ (F' : Type u) (_ : Field F') (aA'F' : Algebra A' F') (aT'F' : Algebra T' F'),
    letI := aA'F'
    letI := aT'F'
    ∃ (_ : IsFractionRing T' F') (_ : IsScalarTower A' T' F') (iF : F →+* F'),
    (∀ a : A, iF (algebraMap A F a) = algebraMap A' F' (algebraMap A A' a)) ∧
    (∀ t : T, iF (algebraMap T F t) = algebraMap T' F' (algebraMap T T' t)) ∧
    Algebra.adjoin A' (Set.range iF) = ⊤ := by
  classical
  let P := (Polynomial.X : Polynomial T) ^ e - Polynomial.C (algebraMap A T (v : A))
  let B := AdjoinRoot P
  let PA := (Polynomial.X : Polynomial A) ^ e - Polynomial.C (v : A)
  let C := AdjoinRoot PA
  have hmonic : P.Monic := Polynomial.monic_X_pow_sub_C _ hepos.ne'
  let : Module.Finite T B := hmonic.finite_adjoinRoot
  let : FaithfulSMul T B := (faithfulSMul_iff_algebraMap_injective T B).mpr (by
    apply AdjoinRoot.of.injective_of_degree_ne_zero
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, Polynomial.natDegree_X_pow_sub_C]
    exact_mod_cast hepos.ne')
  obtain ⟨q, hqmax, hq⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (IsLocalRing.maximalIdeal T) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective T B)]
      exact bot_le)
  let : q.IsMaximal := hqmax
  let φ : C →+* B := AdjoinRoot.map (algebraMap A T) PA P (by simp [PA, P])
  have hφ (a : A) : φ (algebraMap A C a) =
      algebraMap T B (algebraMap A T a) :=
    AdjoinRoot.map_of (algebraMap A T) PA P _ a
  let p : Ideal C := q.comap φ
  have hp : p.comap (algebraMap A C) = IsLocalRing.maximalIdeal A := by
    ext a
    change φ (algebraMap A C a) ∈ q ↔ a ∈ IsLocalRing.maximalIdeal A
    rw [hφ]
    change algebraMap A T a ∈ q.under T ↔ _
    rw [hq]
    exact SetLike.ext_iff.mp (IsLocalRing.maximalIdeal_comap (algebraMap A T)) a
  obtain ⟨da, dva, hAA', _, _⟩ := dvr_unit_root_atPrime A e hepos he v p hp
  let vT : Tˣ := v.map (algebraMap A T)
  have heT : IsUnit (e : T) := by
    simpa only [map_natCast] using he.map (algebraMap A T)
  obtain ⟨dt, dvt, hTT', _, hinj⟩ := dvr_unit_root_atPrime T e hepos heT vT q hq
  let A' := Localization.AtPrime p
  let T' := Localization.AtPrime q
  let : IsDomain A' := da
  let : IsDiscreteValuationRing A' := dva
  let := hAA'
  let : IsDomain T' := dt
  let : IsDiscreteValuationRing T' := dvt
  let := hTT'
  let f : A' →+* T' := Localization.localRingHom p q φ rfl
  let : Algebra A' T' := f.toAlgebra
  have hA'T' : IsLocalHom (algebraMap A' T') :=
    Localization.isLocalHom_localRingHom p q φ rfl
  have hf (c : C) : algebraMap A' T' (algebraMap C A' c) =
      algebraMap B T' (φ c) := Localization.localRingHom_to_map p q φ rfl c
  let r : A' := algebraMap C A' (AdjoinRoot.root PA)
  have hr : r ^ e = algebraMap A A' (v : A) := by
    have hroot : AdjoinRoot.root PA ^ e = algebraMap A C (v : A) := by
      simpa only [PA, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, sub_eq_zero, ← AdjoinRoot.algebraMap_eq] using
        AdjoinRoot.eval₂_root PA
    change (algebraMap C A' (AdjoinRoot.root PA)) ^ e = _
    rw [← map_pow, hroot, ← IsScalarTower.algebraMap_apply A C A']
  have hsq (a : A) : algebraMap T T' (algebraMap A T a) =
      algebraMap A' T' (algebraMap A A' a) := by
    rw [IsScalarTower.algebraMap_apply A C A', hf, hφ,
      ← IsScalarTower.algebraMap_apply T B T']
  have hroot : algebraMap B T' (AdjoinRoot.root P) = algebraMap A' T' r := by
    rw [show r = algebraMap C A' (AdjoinRoot.root PA) from rfl, hf]
    exact congrArg (algebraMap B T') (AdjoinRoot.map_root (algebraMap A T) PA P _).symm
  have : Algebra.Etale A C := unit_root_etale A e hepos he v
  have : Algebra.FormallyUnramified A A' := Algebra.FormallyUnramified.comp A C A'
  have : Algebra.EssFiniteType A A' := Algebra.EssFiniteType.comp A C A'
  have hm : (IsLocalRing.maximalIdeal A).map (algebraMap A A') =
      IsLocalRing.maximalIdeal A' := Algebra.FormallyUnramified.map_maximalIdeal
  let M := q.primeCompl
  let L := FractionRing T'
  let j : T →+* L := (algebraMap T' L).comp (algebraMap T T')
  have hj : Function.Injective j := (IsFractionRing.injective T' L).comp hinj
  let iF : F →+* L := IsFractionRing.lift (K := F) (L := L) (g := j) hj
  have hi (t : T) : iF (algebraMap T F t) =
      algebraMap T' L (algebraMap T T' t) :=
    IsFractionRing.lift_algebraMap hj t
  let : Algebra F L := iF.toAlgebra
  let g : B →+* L := (algebraMap T' L).comp (algebraMap B T')
  have hc (t : T) : g (AdjoinRoot.of P t) =
      algebraMap F L (algebraMap T F t) := by
    change g (AdjoinRoot.of P t) = iF (algebraMap T F t)
    rw [hi]
    exact congrArg (algebraMap T' L) (IsScalarTower.algebraMap_apply T B T' t).symm
  have hgr : g (AdjoinRoot.root P) = algebraMap A' L r := by
    exact congrArg (algebraMap T' L) hroot
  have hgen : Algebra.adjoin A' (Set.range iF) = ⊤ :=
    root_localization_fraction_adjoin T F A' T' L P
      (Polynomial.monic_X_pow_sub_C _ hepos.ne') M g (fun _ ↦ rfl) hc r hgr
  refine ⟨A', inferInstance, da, dva, inferInstance, hAA', r, hr, hm, T', inferInstance,
    dt, dvt, inferInstance, inferInstance, hTT', hA'T', hsq, L, inferInstance,
    inferInstance, inferInstance, inferInstance,
    inferInstance, iF, ?_, hi, hgen⟩
  intro a
  rw [IsScalarTower.algebraMap_apply A T F, hi, hsq]
  rfl

end RingTheory

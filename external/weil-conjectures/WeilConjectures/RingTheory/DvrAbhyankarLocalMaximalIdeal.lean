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

import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.RingTheory.DvrUnitRootWeaklyUnramifiedDiagram
import WeilConjectures.RingTheory.DvrUniformizerRootCompositumMaximalIdeal

/-! # The local maximal-ideal conclusion of Abhyankar's lemma

Source: Stacks Project, Tags 0BRM, 09EM and 09E7.
(blueprint: lem-sbc-dvr-abhyankar-local-maximal-ideal) -/

@[expose] public section

universe u
namespace RingTheory

/-- A tame local DVR extension becomes weakly unramified after divisible base change.

Source: Stacks Project, Tag 0BRM, with the normalization diagram of 09EM and
its weak-unramifiedness consequence in 09E7.
(blueprint: lem-sbc-dvr-abhyankar-local-maximal-ideal)

Proof: Faithfulness, finiteness and normality identify A with the integral
closure of B in Frac(A). The maximal-ideal identities give base index n and
tame index e. The unit condition on e and residue separability are exactly
tameness. The maps from E and A into F extend to the two fraction fields;
the generation hypothesis makes F a field factor of E tensor Frac(A) over
Frac(B). The local map j selects a center of this factor over U. A DVR T
with fraction field F dominating U and A is the corresponding localization
of the normalization: the normalization is contained in the integrally
closed T, and localization at its center is a DVR contained in T with the
same fraction field. Such an inclusion of valuation rings is an equality,
since T is not a field and the only proper coarsening of a discrete rank-one
valuation is the trivial valuation. Apply 0BRM with e dividing n. Explicitly,
write a B-uniformizer as v times the n-th power of an A-uniformizer and
adjoin an e-th root of the unit v by a finite etale extension of A. This
reduces to a base field containing an e-th root of the B-uniformizer. In
that root extension, its quotient by a U-uniformizer is an e-th root of a
unit, so the normalized extension of U is etale. Multiplicativity of
indices gives index one over the root base. Tag 09EQ preserves adic formal
smoothness under the remaining normalized base change, and the finite etale
unit-root extension permits descent as in 0BRM. Thus A -> T is adically
formally smooth. Tag 09E7 gives weak unramifiedness: the image of an
A-uniformizer generates the maximal ideal of T. This is the displayed
maximal-ideal equality. -/
theorem dvr_abhyankar_local_map_maximalIdeal
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (n : ℕ) (hnpos : 0 < n)
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra B A] [Module.Finite B A] [FaithfulSMul B A]
    (hindex : (IsLocalRing.maximalIdeal B).map (algebraMap B A) =
      IsLocalRing.maximalIdeal A ^ n)
    (U : Type u) [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    [Algebra B U] [IsLocalHom (algebraMap B U)]
    (e : ℕ) (he : IsUnit (e : B)) (hedvd : e ∣ n)
    (hindexU : (IsLocalRing.maximalIdeal B).map (algebraMap B U) =
      IsLocalRing.maximalIdeal U ^ e)
    (hsep : Algebra.IsSeparable (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField U))
    (E : Type u) [Field E] [Algebra (FractionRing B) E]
    [Algebra B E] [IsScalarTower B (FractionRing B) E]
    [FiniteDimensional (FractionRing B) E] [Algebra.IsSeparable (FractionRing B) E]
    [Algebra U E] [IsFractionRing U E] [IsScalarTower B U E]
    (F : Type u) [Field F] [Algebra A F] (iE : E →+* F)
    (hcomm : ∀ b : B, iE (algebraMap B E b) =
      algebraMap A F (algebraMap B A b))
    (hgen : Algebra.adjoin A (Set.range iE) = ⊤)
    (T : Type u) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra A T] [IsLocalHom (algebraMap A T)]
    [Algebra T F] [IsFractionRing T F] [IsScalarTower A T F]
    (j : U →+* T) (hj : IsLocalHom j)
    (hjB : ∀ b : B, j (algebraMap B U b) =
      algebraMap A T (algebraMap B A b))
    (hjE : ∀ c : U, algebraMap T F (j c) = iE (algebraMap U E c)) :
    (IsLocalRing.maximalIdeal A).map (algebraMap A T) = IsLocalRing.maximalIdeal T := by
  classical
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hassoc : Associated (t ^ n) (algebraMap B A pi) := by
    apply Ideal.span_singleton_eq_span_singleton.mp
    rw [← Ideal.span_singleton_pow, ← ht.maximalIdeal_eq, ← hindex,
      hpi.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  obtain ⟨v, hv⟩ := hassoc
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos hedvd hnpos
  have heA : IsUnit (e : A) := by
    simpa only [map_natCast] using he.map (algebraMap B A)
  obtain ⟨A', hringA', hdomA', hdvrA', aAA', hAA', r, hr, hmaxAA',
    T', hringT', hdomT', hdvrT', aTT', aA'T', hTT', hA'T', hsquare,
    F', hfieldF', aA'F', aT'F', hfracT'F', hA'T'F', iF, hiFA, hiFT, hgenF'⟩ :=
    dvr_unit_root_weakly_unramified_diagram A e hepos heA v T F
  let : Algebra B A' := ((algebraMap A A').comp (algebraMap B A)).toAlgebra
  have : IsScalarTower B A A' := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A T' := ((algebraMap A' T').comp (algebraMap A A')).toAlgebra
  have : IsScalarTower A A' T' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A T T' := IsScalarTower.of_algebraMap_eq (fun a ↦ (hsquare a).symm)
  have : IsLocalHom (algebraMap A T') := by
    change IsLocalHom ((algebraMap A' T').comp (algebraMap A A'))
    infer_instance
  let : Algebra A F' := ((algebraMap A' F').comp (algebraMap A A')).toAlgebra
  have : IsScalarTower A A' F' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A T' F' := IsScalarTower.to₁₃₄ A A' T' F'
  let fF : F →ₐ[A] F' := { toRingHom := iF, commutes' := hiFA }
  let iE' : E →+* F' := iF.comp iE
  obtain ⟨d, hd⟩ := hedvd
  have hroot : (r * algebraMap A A' t ^ d) ^ e = algebraMap B A' pi := by
    rw [mul_pow, hr, ← pow_mul, Nat.mul_comm d e, ← hd, ← map_pow, ← map_mul]
    rw [mul_comm, hv]
    rfl
  have hcomm' : ∀ b : B, iE' (algebraMap B E b) =
      algebraMap A' F' (algebraMap B A' b) := by
    intro b
    change iF (iE (algebraMap B E b)) = _
    rw [hcomm, hiFA, IsScalarTower.algebraMap_apply B A A']
  have hgen' : Algebra.adjoin A' (Set.range iE') = ⊤ := by
    let S := Algebra.adjoin A' (Set.range iE')
    have hle : Algebra.adjoin A (Set.range iE) ≤
        (S.restrictScalars A).comap fF := by
      apply Algebra.adjoin_le
      rintro _ ⟨x, rfl⟩
      exact Algebra.subset_adjoin ⟨x, rfl⟩
    apply top_unique
    rw [← hgenF']
    apply Algebra.adjoin_le
    rintro _ ⟨x, rfl⟩
    exact hle (hgen ▸ (show x ∈ (⊤ : Subalgebra A F) from trivial))
  let j' : U →+* T' := (algebraMap T T').comp j
  have hj' : IsLocalHom j' := by
    let : IsLocalHom j := hj
    exact inferInstanceAs (IsLocalHom ((algebraMap T T').comp j))
  have hjB' : ∀ b : B, j' (algebraMap B U b) =
      algebraMap A' T' (algebraMap B A' b) := by
    intro b
    change algebraMap T T' (j (algebraMap B U b)) = _
    rw [hjB, hsquare, IsScalarTower.algebraMap_apply B A A']
  have hjE' : ∀ c : U, algebraMap T' F' (j' c) = iE' (algebraMap U E c) := by
    intro c
    change algebraMap T' F' (algebraMap T T' (j c)) =
      iF (iE (algebraMap U E c))
    rw [← hiFT, hjE]
  have hmaxA'T' := dvr_uniformizer_root_compositum_map_maximalIdeal
    B pi hpi A' U e he (r * algebraMap A A' t ^ d) hroot hindexU hsep
    E F' iE' hcomm' hgen' T' j' hj' hjB' hjE'
  have hinjTT' : Function.Injective (algebraMap T T') := by
    intro x y hxy
    apply IsFractionRing.injective T F
    apply iF.injective
    rw [hiFT, hiFT, hxy]
  have : Module.IsTorsionFree T T' :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinjTT'
  have : Module.FaithfullyFlat T T' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hmap : ((IsLocalRing.maximalIdeal A).map (algebraMap A T)).map
      (algebraMap T T') = IsLocalRing.maximalIdeal T' := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A T T',
      IsScalarTower.algebraMap_eq A A' T', ← Ideal.map_map, hmaxAA', hmaxA'T']
  have hcontract := congrArg (Ideal.comap (algebraMap T T')) hmap
  simpa only [Ideal.comap_map_eq_self_of_faithfullyFlat,
    IsLocalRing.maximalIdeal_comap] using hcontract

end RingTheory

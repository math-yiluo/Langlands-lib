/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.Module.SpanRankOperations

/-!
# Coordinates on a split first-order local quotient

Source: Stacks Project, More on Algebra, Tag 07EI, construction of f₁.
(blueprint: lem-weil-pbc-local-first-order-coordinates).
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- A residue section identifies the first-order quotient with a trivial square-zero
extension, compatibly with reduction to the residue field.
Source: Stacks Project, More on Algebra, Tag 07EI, construction of f₁;
Algebra, Tag 00DV, Nakayama's lemma.
(blueprint: lem-weil-pbc-local-first-order-coordinates)

Proof: Put K = A/m and V = m/m². The residue section makes A and A/m² into
K-algebras. The canonical map j : V → A/m² is injective and K-linear, and its
image has square zero. Nakayama identifies dim_K V with m.spanFinrank; choose
coordinates V ≃ K^d. The map (c,v) ↦ s(c) + j(v) is multiplicative since the
image of j has square zero. It is surjective: for a in A subtract s(residue(a));
the difference belongs to m and therefore comes from V. It is injective:
reduction first determines c, and the injectivity of j then determines v.
The inverse is the required equivalence. Its first coordinate is reduction.
For d = 0 this gives A/m² = K, with no nonzero cotangent part. -/
theorem exists_firstOrder_coordinates (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (s : ResidueField A →+* A)
    (hs : (residue A).comp s = RingHom.id _) :
    ∃ e : (A ⧸ maximalIdeal A ^ 2) ≃+*
        TrivSqZeroExt (ResidueField A) (Fin (maximalIdeal A).spanFinrank → ResidueField A),
      ∀ a : A, (e (Ideal.Quotient.mk (maximalIdeal A ^ 2) a)).fst = residue A a := by
  let W := Fin (maximalIdeal A).spanFinrank → (ResidueField A)
  let : Module (ResidueField A) (maximalIdeal A).Cotangent := inferInstance
  let : SMul (ResidueField A) (maximalIdeal A).Cotangent :=
    (inferInstance : Module (ResidueField A) (maximalIdeal A).Cotangent).toSMul
  let : IsScalarTower A (ResidueField A) (maximalIdeal A).Cotangent := inferInstance
  let : Algebra (ResidueField A) A := s.toAlgebra
  have hsa (c : (ResidueField A)) : residue A (s c) = c := RingHom.congr_fun hs c
  let : IsScalarTower (ResidueField A) A (maximalIdeal A).Cotangent :=
    IsScalarTower.of_algebraMap_smul fun c v ↦ by
      change s c • v = c • v
      calc
        s c • v = (residue A (s c) : (ResidueField A)) • v :=
          (IsScalarTower.algebraMap_smul (R := A) (A := (ResidueField A)) (s c) v).symm
        _ = c • v := by rw [hsa]
  let : IsScalarTower (ResidueField A) A (A ⧸ (maximalIdeal A) ^ 2) := inferInstance
  let b := Module.finBasisOfFinrankEq (ResidueField A) (CotangentSpace A)
    (spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := A)).symm
  let j : W →ₗ[(ResidueField A)] (A ⧸ maximalIdeal A ^ 2) :=
    ((maximalIdeal A).cotangentToQuotientSquare.restrictScalars (ResidueField A)).comp
      b.equivFun.symm.toLinearMap
  have hj : Function.Injective j :=
    (maximalIdeal A).cotangentToQuotientSquare_injective.comp b.equivFun.symm.injective
  have hjmul (x y : W) : j x * j y = 0 := by
    obtain ⟨a, ha⟩ := (maximalIdeal A).toCotangent_surjective (b.equivFun.symm x)
    obtain ⟨b', hb⟩ := (maximalIdeal A).toCotangent_surjective (b.equivFun.symm y)
    change (maximalIdeal A).cotangentToQuotientSquare (b.equivFun.symm x) *
      (maximalIdeal A).cotangentToQuotientSquare (b.equivFun.symm y) = 0
    rw [← ha, ← hb, Ideal.toCotangent_to_quotient_square,
      Ideal.toCotangent_to_quotient_square]
    change Ideal.Quotient.mk ((maximalIdeal A) ^ 2) (a : A) *
      Ideal.Quotient.mk ((maximalIdeal A) ^ 2) (b' : A) = 0
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_two]
    exact Ideal.mul_mem_mul a.property b'.property
  let F : TrivSqZeroExt (ResidueField A) W →ₐ[ResidueField A]
      (A ⧸ maximalIdeal A ^ 2) := TrivSqZeroExt.liftEquivOfComm ⟨j, hjmul⟩
  let r : (A ⧸ maximalIdeal A ^ 2) →+* ResidueField A :=
    Ideal.Quotient.factor (Ideal.pow_le_self two_ne_zero)
  have hrj (x : W) : r (j x) = 0 := by
    obtain ⟨a, ha⟩ := (maximalIdeal A).toCotangent_surjective (b.equivFun.symm x)
    change r ((maximalIdeal A).cotangentToQuotientSquare (b.equivFun.symm x)) = 0
    rw [← ha, Ideal.toCotangent_to_quotient_square]
    exact (residue_eq_zero_iff (a : A)).mpr a.property
  have hrF (x : TrivSqZeroExt (ResidueField A) W) : r (F x) = x.fst := by
    change r (algebraMap (ResidueField A) (A ⧸ maximalIdeal A ^ 2) x.fst + j x.snd) = x.fst
    rw [map_add, hrj, add_zero]
    exact hsa x.fst
  have hF : Function.Bijective F := by
    constructor
    · intro x y h
      have hfst : x.fst = y.fst := by rw [← hrF x, ← hrF y, h]
      have hsnd : x.snd = y.snd := by
        apply hj
        change algebraMap (ResidueField A) (A ⧸ maximalIdeal A ^ 2) x.fst + j x.snd =
          algebraMap (ResidueField A) (A ⧸ maximalIdeal A ^ 2) y.fst + j y.snd at h
        rw [hfst] at h
        exact add_left_cancel h
      exact TrivSqZeroExt.ext hfst hsnd
    · intro q
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
      have ha : a - s (residue A a) ∈ (maximalIdeal A) := by
        rw [← residue_eq_zero_iff, map_sub, hsa, sub_self]
      refine ⟨⟨residue A a, b.equivFun ((maximalIdeal A).toCotangent ⟨_, ha⟩)⟩, ?_⟩
      change algebraMap (ResidueField A) (A ⧸ maximalIdeal A ^ 2) (residue A a) +
        (maximalIdeal A).cotangentToQuotientSquare (b.equivFun.symm (b.equivFun _)) = _
      rw [b.equivFun.symm_apply_apply, Ideal.toCotangent_to_quotient_square]
      change Ideal.Quotient.mk ((maximalIdeal A) ^ 2) (s (residue A a)) +
        Ideal.Quotient.mk ((maximalIdeal A) ^ 2) (a - s (residue A a)) = _
      rw [← map_add, add_sub_cancel]
  let e := (RingEquiv.ofBijective F.toRingHom hF).symm
  refine ⟨e, fun a ↦ ?_⟩
  rw [← hrF (e (Ideal.Quotient.mk ((maximalIdeal A) ^ 2) a))]
  change r ((RingEquiv.ofBijective F.toRingHom hF)
    ((RingEquiv.ofBijective F.toRingHom hF).symm _)) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

end IsLocalRing

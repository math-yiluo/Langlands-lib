/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Ramification indices as orders of vanishing, trivial inertia over algebraically closed fields

## Main statements

- `Ideal.inertiaDeg_eq_one_of_isAlgClosed`: over an algebraically closed field `k`, the inertia
  degrees of a finite extension of finite type `k`-algebras at maximal ideals are `1`.
- `Ideal.ramificationIdx_eq_ord`: if `p` generates the ideal `(s)` in a localization `S` of `B`
  at `q`, the ramification index of `q` over `p` is the order of vanishing of `s` in `S`.
-/

@[expose] public section

namespace Ideal

/-- Over an algebraically closed field `k`, the inertia degree of a maximal ideal `q` of a finite
`A`-algebra `B` of finite type over `k` is `1`: both residue fields are `k`. -/
theorem inertiaDeg_eq_one_of_isAlgClosed {k A B : Type*} [Field k] [IsAlgClosed k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    [Algebra.FiniteType k B] [Module.Finite A B] (p : Ideal A) [p.IsMaximal] (q : Ideal B)
    [q.IsMaximal] [q.LiesOver p] : q.inertiaDeg A = 1 := by
  rw [inertiaDeg_eq_of_isMaximal p q]
  let : Field (A ⧸ p) := Quotient.field p
  let : Field (B ⧸ q) := Quotient.field q
  have : Module.Finite k (B ⧸ q) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ q)
  have hsurj := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := B ⧸ q)).2
  have hsurj' : Function.Surjective (algebraMap (A ⧸ p) (B ⧸ q)) := by
    intro z
    obtain ⟨c, rfl⟩ := hsurj z
    exact ⟨algebraMap k (A ⧸ p) c, by rw [← IsScalarTower.algebraMap_apply]⟩
  rw [← (LinearEquiv.ofBijective (Algebra.linearMap (A ⧸ p) (B ⧸ q))
    ⟨(algebraMap (A ⧸ p) (B ⧸ q)).injective, hsurj'⟩).finrank_eq, Module.finrank_self]

/-- If the prime `p` of `A` generates the principal ideal `(s)` of the localization `S` of `B`
at `q`, then the ramification index of `q` over `p` is the order of vanishing `ord_S(s)`, the
length of `S / (s)`. -/
theorem ramificationIdx_eq_ord {A B S : Type*} [CommRing A] [CommRing B] [CommRing S]
    [Algebra A B] [Algebra B S] [Algebra A S] [IsScalarTower A B S] (p : Ideal A) (q : Ideal B)
    [q.IsPrime] [q.LiesOver p] [IsLocalization.AtPrime S q] (s : S)
    (hs : p.map (algebraMap A S) = Ideal.span {s}) :
    q.ramificationIdx A = (Ring.ord S s).toNat := by
  rw [ramificationIdx_eq p q, Ring.ord]
  let Sq := Localization.AtPrime q
  let e : Sq ≃ₐ[B] S := IsLocalization.algEquiv q.primeCompl Sq S
  let : Algebra Sq S := e.toRingHom.toAlgebra
  have hI : (p.map (algebraMap A Sq)).map e.toRingHom = Ideal.span {s} := by
    rw [Ideal.map_map, ← hs]
    congr 1
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [IsScalarTower.algebraMap_apply A B Sq, IsScalarTower.algebraMap_apply A B S]
    exact e.commutes _
  have e' : (Sq ⧸ p.map (algebraMap A Sq)) ≃ₗ[Sq] (S ⧸ Ideal.span {s}) :=
    { Ideal.quotientEquiv _ _ e.toRingEquiv hI.symm with
      map_smul' := fun r x ↦ by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        change Ideal.Quotient.mk (Ideal.span {s}) (e (r * x)) =
          Ideal.Quotient.mk (Ideal.span {s}) (e r) * Ideal.Quotient.mk (Ideal.span {s}) (e x)
        rw [map_mul, map_mul] }
  rw [e'.length_eq]
  have : IsScalarTower Sq S (S ⧸ Ideal.span {s}) := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  exact congrArg ENat.toNat (Module.length_eq_of_surjective e.surjective)

end Ideal

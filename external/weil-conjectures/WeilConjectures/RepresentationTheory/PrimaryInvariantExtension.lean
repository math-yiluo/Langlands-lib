/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.PGroup
import Mathlib.RepresentationTheory.Invariants

/-!
# Extending a stable subgroup in a finite primary representation

Source: Stacks Project, Tags 0GIZ and 0GJ0
(blueprint: lem-sc-primary-invariant-extension).
-/

@[expose] public section

universe u v

namespace Representation

/-- A proper stable subgroup of a finite primary module can be enlarged by a
nonzero trivial quotient killed by the prime.

Proof: Form the nonzero finite quotient A = V / W with its induced Q-action.
It remains ℓ-primary. A nonzero element has order divisible by ℓ, so ℓ divides
its cardinality. The fixed-point counting theorem for p-group actions, with
zero as one fixed point, supplies a second fixed point. Hence the invariant
subgroup I is nonzero and ℓ-primary. Its cardinality is divisible by ℓ, and
Cauchy's theorem gives an element y of order ℓ in I. Let L consist of all
invariants in A killed by ℓ; it contains y, so is nonzero. The inverse image W'
of L strictly contains W. Every element of L is fixed, so W' is stable and
ρ g x - x lies in W for x in W'. The condition ℓ L = 0 likewise gives ℓ x ∈ W.
This is an explicit elementary proof of the finite-module case underlying
the filtration assertion of Tag 0GIZ, using Mathlib's fixed-point count and
Cauchy's theorem, instead of the augmentation-ideal hint in that source.

Source: Stacks Project, Etale Cohomology, Lemma 0GIZ (lemma-action-l-group),
the filtration assertion, and Lemma 0GJ0 (lemma-pullback-filtered-modules).
(blueprint: lem-sc-primary-invariant-extension). -/
theorem exists_primary_invariant_extension
    (Q : Type u) [Group Q] (ℓ : ℕ) (hℓ : ℓ.Prime) (hQ : IsPGroup ℓ Q)
    (V : Type v) [AddCommGroup V] [instVModule : Module ℤ V] [Finite V]
    (ρ : Representation ℤ Q V) (hV : IsPGroup ℓ (Multiplicative V))
    (W : AddSubgroup V) (hW : ∀ g : Q, ∀ x : V, x ∈ W → ρ g x ∈ W)
    (hne : W ≠ ⊤) :
    ∃ W' : AddSubgroup V, W < W' ∧
      (∀ g : Q, ∀ x : V, x ∈ W' → ρ g x ∈ W') ∧
      (∀ x : V, x ∈ W' → ℓ • x ∈ W ∧ ∀ g : Q, ρ g x - x ∈ W) := by
  classical
  let : Fact ℓ.Prime := ⟨hℓ⟩
  let N : Submodule ℤ V :=
    { W with
      smul_mem' := by
        intro n x hx
        change instVModule.smul n x ∈ W
        rw [int_smul_eq_zsmul instVModule]
        exact W.zsmul_mem hx n }
  have hN : ∀ g : Q, N ≤ N.comap (ρ g) := hW
  let A := V ⧸ N
  let : Module ℤ A := Submodule.Quotient.module N
  let ρA : Representation ℤ Q A := ρ.quotient N hN
  let q : V →ₗ[ℤ] A := N.mkQ
  have hq : Function.Surjective q := Submodule.mkQ_surjective N
  let : Finite A := Finite.of_surjective q hq
  have hA : IsPGroup ℓ (Multiplicative A) :=
    hV.of_surjective q.toAddMonoidHom.toMultiplicative hq
  have hneN : N ≠ ⊤ := by
    intro h
    apply hne
    exact congrArg Submodule.toAddSubgroup h
  let : Nontrivial A := Submodule.Quotient.nontrivial_iff.mpr hneN
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  have hdvd : ℓ ∣ Nat.card A := by
    exact (hA.dvd_orderOf (g := Multiplicative.ofAdd a) ha).trans
      (orderOf_dvd_natCard (Multiplicative.ofAdd a))
  let : MulAction Q A := MulAction.compHom A ρA
  have hzero : (0 : A) ∈ MulAction.fixedPoints Q A := fun g ↦ map_zero (ρA g)
  obtain ⟨b, hb, hb0⟩ := hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point A hdvd hzero
  let I := ρA.invariants
  have hbinv : b ∈ I := hb
  let bI : I := ⟨b, hbinv⟩
  have hbI : bI ≠ 0 := by
    intro h
    exact hb0 (congrArg Subtype.val h).symm
  have hI : IsPGroup ℓ (Multiplicative I) :=
    hA.of_injective I.subtype.toAddMonoidHom.toMultiplicative Subtype.coe_injective
  have hdvdI : ℓ ∣ Nat.card I := by
    exact (hI.dvd_orderOf (g := Multiplicative.ofAdd bI) hbI).trans
      (orderOf_dvd_natCard (Multiplicative.ofAdd bI))
  obtain ⟨y, hy⟩ := exists_prime_addOrderOf_dvd_card' ℓ hdvdI
  have hy0 : (y : A) ≠ 0 := by
    intro h
    have : y = 0 := Subtype.ext h
    rw [this, addOrderOf_zero] at hy
    exact hℓ.ne_one hy.symm
  have hykill : ℓ • (y : A) = 0 := by
    have h : ℓ • y = 0 := by rw [← hy]; exact addOrderOf_nsmul_eq_zero y
    exact congrArg Subtype.val h
  let L : AddSubgroup A :=
    { carrier := {x | ℓ • x = 0 ∧ ∀ g : Q, ρA g x = x}
      zero_mem' := by simp
      add_mem' := by
        intro x z hx hz
        exact ⟨by simp [smul_add, hx.1, hz.1], fun g ↦ by
          rw [map_add, hx.2 g, hz.2 g]⟩
      neg_mem' := by
        intro x hx
        exact ⟨by simp [smul_neg, hx.1], fun g ↦ by rw [map_neg, hx.2 g]⟩ }
  have hyL : (y : A) ∈ L := ⟨hykill, y.property⟩
  let W' := L.comap q.toAddMonoidHom
  have hle : W ≤ W' := by
    intro x hx
    have hqx : q x = 0 := (Submodule.Quotient.mk_eq_zero N).mpr hx
    change q x ∈ L
    rw [hqx]
    exact L.zero_mem
  have hlt : W < W' := by
    refine lt_of_le_of_ne hle ?_
    intro heq
    obtain ⟨x, hx⟩ := hq y
    have hx' : x ∈ W' := by change q x ∈ L; rwa [hx]
    have hxW : x ∈ W := heq.symm ▸ hx'
    have : q x = 0 := (Submodule.Quotient.mk_eq_zero N).mpr hxW
    exact hy0 (hx.symm.trans this)
  have hact (g : Q) (x : V) : q (ρ g x) = ρA g (q x) := rfl
  refine ⟨W', hlt, ?_, ?_⟩
  · intro g x hx
    change q (ρ g x) ∈ L
    change q x ∈ L at hx
    rw [hact, hx.2 g]
    exact hx
  · intro x hx
    change q x ∈ L at hx
    refine ⟨?_, fun g ↦ ?_⟩
    · apply (Submodule.Quotient.mk_eq_zero N).mp
      change q (ℓ • x) = 0
      rw [map_nsmul]
      exact hx.1
    · apply (Submodule.Quotient.mk_eq_zero N).mp
      change q (ρ g x - x) = 0
      rw [map_sub, hact, hx.2 g, sub_self]

end Representation

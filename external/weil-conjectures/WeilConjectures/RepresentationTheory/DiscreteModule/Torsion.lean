/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteModule.CohomologicalDimension
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Cohomology of torsion discrete modules

Let `G` be a compact group such that `H²(K, 𝔽_ℓ) = 0` for every prime `ℓ` and every open
subgroup `K` of `G`. Then `Hⁿ(G, M) = 0` for every `n ≥ 2` and every torsion discrete
`G`-module `M`.

A finite module is an iterated extension of `ℓ`-primary modules (for varying `ℓ`), whose `H²`
vanishes by `DiscreteModule.subsingleton_H_two`; a torsion module is the union of its finite
stable subgroups; and a dimension shift through coinduced modules gives all degrees `n ≥ 2`.

## Main statements

- `DiscreteModule.subsingleton_H_two_of_finite_of_forall_prime`: the finite case in degree `2`.
- `DiscreteModule.subsingleton_H_of_two_le_of_isTorsion`: the criterion for torsion modules.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Action

namespace DiscreteModule

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section sub

variable (X : DiscreteModule.{w} G) (S : AddSubgroup X.obj.V)
  (hS : ∀ g : G, ∀ x ∈ S, (X.obj.ρ g).asHom.hom x ∈ S)

/-- The inclusion of the discrete submodule given by a stable subgroup. -/
def subι : sub X S hS ⟶ X :=
  ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom S.subtype
      comm _ := rfl }

@[simp]
lemma subι_apply (x : (sub X S hS).obj.V) : (subι X S hS).hom.hom.hom x = x.1 :=
  rfl

/-- The short complex `S ⟶ X ⟶ X / S` of a stable subgroup. -/
def subShortComplex : ShortComplex (DiscreteModule.{w} G) :=
  ShortComplex.mk (subι X S hS) (quotientπ X S hS) (by
    ext x
    exact (QuotientAddGroup.eq_zero_iff _).2 x.2)

lemma subShortExact : (subShortComplex X S hS).ShortExact :=
  shortExact_of_forget Subtype.val_injective (QuotientAddGroup.mk_surjective (s := S))
    fun y hy ↦ ⟨⟨y, (QuotientAddGroup.eq_zero_iff (N := S) y).1 hy⟩, rfl⟩

end sub

/-- The image of a torsion module under the projection onto a quotient is torsion. -/
lemma isOfFinAddOrder_quotient {X : DiscreteModule.{w} G} (hX : ∀ x : X.obj.V, IsOfFinAddOrder x)
    (S : AddSubgroup X.obj.V) (hS : ∀ g : G, ∀ x ∈ S, (X.obj.ρ g).asHom.hom x ∈ S)
    (q : (quotient X S hS).obj.V) : IsOfFinAddOrder q := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨N, hN, hNy⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (hX y)
  exact isOfFinAddOrder_iff_nsmul_eq_zero.2
    ⟨N, hN, congrArg (QuotientAddGroup.mk (s := S)) hNy⟩

/-- A function with finite range into a torsion group is killed by a positive integer. -/
lemma exists_pos_nsmul_eq_zero_of_finite {A : Type*} [AddCommGroup A] {s : Set A}
    (hs : s.Finite) (h : ∀ a ∈ s, IsOfFinAddOrder a) :
    ∃ N : ℕ, 0 < N ∧ ∀ a ∈ s, N • a = 0 := by
  refine ⟨∏ a ∈ hs.toFinset, addOrderOf a, Finset.prod_pos fun a ha ↦
    (h a (hs.mem_toFinset.1 ha)).addOrderOf_pos, fun a ha ↦ ?_⟩
  exact addOrderOf_dvd_iff_nsmul_eq_zero.1
    (Finset.dvd_prod_of_mem _ (hs.mem_toFinset.2 ha))

lemma isOfFinAddOrder_coker₁ [CompactSpace G] {X : DiscreteModule.{w} G}
    (hX : ∀ x : X.obj.V, IsOfFinAddOrder x) (c : (coker₁ X).obj.V) : IsOfFinAddOrder c := by
  refine isOfFinAddOrder_quotient (fun f ↦ ?_) _ _ c
  obtain ⟨N, hN, hNf⟩ := exists_pos_nsmul_eq_zero_of_finite (finite_range_smoothFunctions f)
    (by rintro _ ⟨x, rfl⟩; exact hX _)
  exact isOfFinAddOrder_iff_nsmul_eq_zero.2
    ⟨N, hN, Subtype.ext (funext fun x ↦ hNf _ ⟨x, rfl⟩)⟩

section main

variable [CompactSpace G]

/-- `H²(G, X) = 0` for a finite discrete module `X`, if `H²(K, 𝔽_ℓ) = 0` for every prime `ℓ`
and every open subgroup `K`: by induction on `#X`, using the `ℓ`-torsion subgroup of `X` for a
prime `ℓ` dividing `#X`. -/
theorem subsingleton_H_two_of_finite_of_forall_prime
    (h2 : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (K : Subgroup G), IsOpen (K : Set G) →
      Subsingleton (H K (trivialZMod.{w} K ℓ) 2))
    (n : ℕ) (X : DiscreteModule.{w} G) [Finite X.obj.V] (hn : Nat.card X.obj.V = n) :
    Subsingleton (H G X 2) := by
  induction n using Nat.strong_induction_on generalizing X with
  | _ n ih =>
  by_cases htriv : Subsingleton X.obj.V
  · exact subsingleton_H_of_subsingleton X 2
  rw [not_subsingleton_iff_nontrivial] at htriv
  have hcard : Nat.card X.obj.V ≠ 1 := fun h ↦ (Finite.one_lt_card_iff_nontrivial.2 htriv).ne' h
  let ℓ := (Nat.card X.obj.V).minFac
  have hℓ : Fact ℓ.Prime := ⟨Nat.minFac_prime hcard⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' ℓ (Nat.minFac_dvd (Nat.card X.obj.V))
  let S := (nsmulAddMonoidHom (α := X.obj.V) ℓ).ker
  have hS : ∀ g : G, ∀ y ∈ S, (X.obj.ρ g).asHom.hom y ∈ S := by
    intro g y hy
    rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at hy ⊢
    rw [← map_nsmul, hy, map_zero]
  refine subsingleton_ext_of_shortExact (subShortExact X S hS)
    (subsingleton_H_two ℓ (h2 ℓ) _ fun y ↦ ⟨1, Subtype.ext ?_⟩) ?_
  · have := y.2
    rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at this
    rw [pow_one]
    exact this
  have : Finite (quotient X S hS).obj.V :=
    Finite.of_surjective _ (QuotientAddGroup.mk_surjective (s := S))
  refine ih _ ?_ (quotient X S hS) rfl
  rw [← hn, AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup S]
  have h1 : 1 < Nat.card S := by
    have hxS : x ∈ S := by
      rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, ← hx]
      exact addOrderOf_nsmul_eq_zero x
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [addOrderOf_zero] at hx
      exact hℓ.out.one_lt.ne hx
    have : Nontrivial S := ⟨⟨0, ⟨x, hxS⟩, fun h ↦ hx0 (congrArg Subtype.val h).symm⟩⟩
    exact Finite.one_lt_card_iff_nontrivial.2 this
  have h2 : 0 < Nat.card (X.obj.V ⧸ S) := Nat.card_pos
  change Nat.card (X.obj.V ⧸ S) < _
  nlinarith

/-- `H²(G, M) = 0` for a torsion discrete module `M`, if `H²(K, 𝔽_ℓ) = 0` for every prime `ℓ`
and every open subgroup `K`: `M` is the union of its finite stable subgroups. -/
theorem subsingleton_H_two_of_isTorsion
    (h2 : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (K : Subgroup G), IsOpen (K : Set G) →
      Subsingleton (H K (trivialZMod.{w} K ℓ) 2))
    (M : DiscreteModule.{w} G) (hM : ∀ x : M.obj.V, IsOfFinAddOrder x) :
    Subsingleton (H G M 2) := by
  refine subsingleton_H_two_of_forall_finite M fun T hT ↦ ?_
  let U : Set M.obj.V := ⋃ t ∈ T, Set.range fun g : G ↦ (M.obj.ρ g).asHom.hom t
  have hU : U.Finite := hT.biUnion fun t _ ↦ finite_range_of_forall_mul_eq _
    (M.obj.stabilizer t) (M.isOpen_stabilizer t) fun x u hu ↦ by
      rw [ρ_mul_apply, mem_stabilizer.1 hu]
  have hstab : ∀ g : G, ∀ x ∈ AddSubgroup.closure U,
      (M.obj.ρ g).asHom.hom x ∈ AddSubgroup.closure U := by
    intro g x hx
    refine (AddSubgroup.closure_le (K := (AddSubgroup.closure U).comap (M.obj.ρ g).asHom.hom)).2
      ?_ hx
    intro u hu
    obtain ⟨t, ht, h, rfl⟩ : ∃ t ∈ T, ∃ h : G, (M.obj.ρ h).asHom.hom t = u := by simpa [U] using hu
    exact AddSubgroup.subset_closure (Set.mem_biUnion ht ⟨g * h, by simp⟩)
  refine ⟨_, hstab, fun t ht ↦ AddSubgroup.subset_closure (Set.mem_biUnion ht ⟨1, by simp⟩), ?_⟩
  have : Finite U := hU.to_subtype
  have : Finite (AddSubgroup.closure U) := AddCommGroup.finite_of_fg_isAddTorsion _ fun x ↦ by
    obtain ⟨N, hN, hNx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (hM x.1)
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨N, hN, Subtype.ext hNx⟩
  have : Finite (sub M _ hstab).obj.V := this
  exact subsingleton_H_two_of_finite_of_forall_prime h2 _ _ rfl

/-- **A degree-two criterion for torsion modules.** Let `G` be a profinite (more generally,
compact) group such that `H²(K, 𝔽_ℓ) = 0` for every prime `ℓ` and every open subgroup `K` of
`G`. Then `Hⁿ(G, M) = 0` for every `n ≥ 2` and every torsion discrete `G`-module `M`. -/
theorem subsingleton_H_of_two_le_of_isTorsion
    (h2 : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (K : Subgroup G), IsOpen (K : Set G) →
      Subsingleton (H K (trivialZMod.{w} K ℓ) 2))
    (M : DiscreteModule.{w} G) (hM : ∀ x : M.obj.V, IsOfFinAddOrder x) {n : ℕ} (hn : 2 ≤ n) :
    Subsingleton (H G M n) := by
  induction n, hn using Nat.le_induction generalizing M with
  | base => exact subsingleton_H_two_of_isTorsion h2 M hM
  | succ n hn ih =>
    exact subsingleton_ext_succ_of_shortExact (shortExact₁ M) (subsingleton_H_coind₁ _ n)
      (ih _ (isOfFinAddOrder_coker₁ hM))

end main

end DiscreteModule

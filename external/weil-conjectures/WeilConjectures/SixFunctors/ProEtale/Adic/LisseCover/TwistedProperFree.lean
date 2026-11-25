/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedSection
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Free modules on twisted sheaves of sets

This file contains the linear-algebra input of proper base change in degree zero for twisted
sheaves of sets (blueprint `proposition-proper-base-change-degree-zero`).

Let `f : V ⟶ Y` be a morphism of schemes and `c` a descent cocycle on the constant sheaf `S_V`
(`AlgebraicGeometry.IsDescentCocycle`). For a semiring `Λ`, the bijections `c z` induce
`Λ`-linear automorphisms of the free module `S →₀ Λ`
(`AlgebraicGeometry.IsDescentCocycle.freeCocycle`), forming again a descent cocycle
(`AlgebraicGeometry.IsDescentCocycle.free`): the sheaf `Λ[F_c]` of the free `Λ`-modules on the
twisted sheaf of sets `F_c`. A twisted section `σ` of `F_c` gives the twisted section
`x ↦ [σ x]` of `Λ[F_c]` (`AlgebraicGeometry.IsTwistedSection.single_one`), and a twisted section
of `Λ[F_c]` all of whose values are basis vectors comes from a twisted section of `F_c`
(`AlgebraicGeometry.IsTwistedSection.exists_of_free`).

We also record that the image in `T` of a level set of a locally constant function on `V ×_Y T`
invariant under the equivalence relation `(V ×_Y T) ×_T (V ×_Y T)` is open and closed when
`f` is a pro-étale cover (`AlgebraicGeometry.isClopen_image_fiber_of_isLocallyConstant`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section Finsupp

/-- A family of maps `g x : S → S` depending locally constantly on `x` induces a family of maps
`Finsupp.mapDomain (g x)` on `S →₀ Λ` depending locally constantly on `x`; used for the free
cocycle of blueprint `proposition-proper-base-change-degree-zero`. -/
lemma isLocallyConstant_mapDomain {X : Type*} [TopologicalSpace X] {S Λ : Type*}
    [AddCommMonoid Λ] {g : X → S → S} (hg : ∀ s, IsLocallyConstant fun x ↦ g x s)
    (m : S →₀ Λ) : IsLocallyConstant fun x ↦ Finsupp.mapDomain (g x) m := by
  induction m using Finsupp.induction_linear with
  | zero =>
    simp only [Finsupp.mapDomain_zero]
    exact IsLocallyConstant.const 0
  | add m₁ m₂ h₁ h₂ =>
    simp only [Finsupp.mapDomain_add]
    exact h₁.add h₂
  | single s b =>
    simp only [Finsupp.mapDomain_single]
    exact (hg s).comp (Finsupp.single · b)

/-- An element of `S →₀ Λ` is a basis vector `[s] = single s b` if and only if its image under
`Finsupp.mapDomain e` for a bijection `e` is; used in blueprint
`proposition-proper-base-change-degree-zero`. -/
lemma exists_mapDomain_eq_single_iff {S Λ : Type*} [AddCommMonoid Λ] {e : S → S}
    (he : Function.Bijective e) (m : S →₀ Λ) (b : Λ) :
    (∃ s, Finsupp.mapDomain e m = Finsupp.single s b) ↔ ∃ s, m = Finsupp.single s b := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨s', rfl⟩ := he.2 s
    exact ⟨s', Finsupp.mapDomain_injective he.1 (by rw [hs, Finsupp.mapDomain_single])⟩
  · rintro ⟨s, rfl⟩
    exact ⟨e s, Finsupp.mapDomain_single⟩

end Finsupp

variable {Y V : Scheme.{u}} {f : V ⟶ Y} {S : Type*} {c : ↥(pullback f f) → S → S}

namespace IsDescentCocycle

/-- **The free cocycle.** The `Λ`-linear automorphism `Finsupp.mapDomain (c z)` of the free
module `S →₀ Λ` induced by the bijection `c z`; these form the descent cocycle of the sheaf of
free `Λ`-modules on the twisted sheaf of sets defined by `c`
(blueprint `proposition-proper-base-change-degree-zero`). -/
noncomputable def freeCocycle (hc : IsDescentCocycle f c) (Λ : Type*) [Semiring Λ]
    (z : ↥(pullback f f)) : (S →₀ Λ) ≃ₗ[Λ] (S →₀ Λ) :=
  Finsupp.domLCongr (Equiv.ofBijective (c z) (hc.bijective z))

lemma coe_freeCocycle (hc : IsDescentCocycle f c) (Λ : Type*) [Semiring Λ]
    (z : ↥(pullback f f)) : ⇑(hc.freeCocycle Λ z) = Finsupp.mapDomain (c z) := by
  funext m
  simp [freeCocycle, Finsupp.equivMapDomain_eq_mapDomain]

/-- **The free cocycle is a descent cocycle** (blueprint
`proposition-proper-base-change-degree-zero`). -/
lemma free (hc : IsDescentCocycle f c) (Λ : Type*) [Semiring Λ] :
    IsDescentCocycle f (fun z ↦ ⇑(hc.freeCocycle Λ z)) where
  isLocallyConstant m := by
    simp only [coe_freeCocycle]
    exact isLocallyConstant_mapDomain hc.isLocallyConstant m
  bijective z := (hc.freeCocycle Λ z).bijective
  diagonal v := by
    rw [coe_freeCocycle, hc.diagonal]
    funext m
    exact Finsupp.mapDomain_id
  cocycle w := by
    rw [coe_freeCocycle, coe_freeCocycle, coe_freeCocycle, hc.cocycle]
    funext m
    exact Finsupp.mapDomain_comp

end IsDescentCocycle

/-- A twisted section `σ` of the sheaf of sets defined by `c` gives the twisted section
`x ↦ [σ x]` of the sheaf of free `Λ`-modules defined by the free cocycle
(blueprint `proposition-proper-base-change-degree-zero`). -/
lemma IsTwistedSection.single_one (hc : IsDescentCocycle f c) (Λ : Type*) [Semiring Λ]
    {T : Scheme.{u}} {π : T ⟶ Y} {σ : ↥(pullback f π) → S} (hσ : IsTwistedSection f c π σ) :
    IsTwistedSection f (fun z ↦ ⇑(hc.freeCocycle Λ z)) π (fun x ↦ Finsupp.single (σ x) 1) :=
  ⟨hσ.1.comp (Finsupp.single · 1), fun w ↦ by
    simp only
    rw [IsDescentCocycle.coe_freeCocycle, Finsupp.mapDomain_single, ← hσ.2 w]⟩

/-- A twisted section of the sheaf of free `Λ`-modules defined by the free cocycle all of whose
values are basis vectors `[s]` comes from a twisted section of the sheaf of sets defined by `c`
(blueprint `proposition-proper-base-change-degree-zero`). -/
lemma IsTwistedSection.exists_of_free (hc : IsDescentCocycle f c) {Λ : Type*} [Semiring Λ]
    [Nontrivial Λ] {T : Scheme.{u}} {π : T ⟶ Y} {τ : ↥(pullback f π) → S →₀ Λ}
    (hτ : IsTwistedSection f (fun z ↦ ⇑(hc.freeCocycle Λ z)) π τ)
    (h : ∀ x, ∃ s, τ x = Finsupp.single s 1) :
    ∃ σ, IsTwistedSection f c π σ ∧ ∀ x, τ x = Finsupp.single (σ x) 1 := by
  choose σ hσ using h
  have inj := Finsupp.single_left_injective (α := S) (one_ne_zero (α := Λ))
  refine ⟨σ, ⟨?_, fun w ↦ inj ?_⟩, hσ⟩
  · rw [IsLocallyConstant.iff_isOpen_fiber]
    intro s
    have e : σ ⁻¹' {s} = τ ⁻¹' {Finsupp.single s 1} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hσ x]
      exact inj.eq_iff.symm
    rw [e]
    exact hτ.1.isOpen_fiber _
  · simp only
    rw [← hσ, hτ.2 w, hσ]
    simp only
    rw [IsDescentCocycle.coe_freeCocycle, Finsupp.mapDomain_single]

/-- **Descent of clopen level sets.** Let `f : V ⟶ Y` be weakly étale, surjective and
quasi-compact and `π : T ⟶ Y`. For a locally constant function `τ` on `V ×_Y T` which takes the
same value at the two components of every point of `(V ×_Y T) ×_T (V ×_Y T)`, the image in `T`
of every level set of `τ` is open and closed, open subsets descending along the pro-étale cover
`V ×_Y T ⟶ T` (blueprint `proposition-proper-base-change-degree-zero`). -/
lemma isClopen_image_fiber_of_isLocallyConstant [WeaklyEtale f] [Surjective f]
    [QuasiCompact f] {T : Scheme.{u}} (π : T ⟶ Y) {A : Type*}
    (τ : ↥(pullback f π) → A) (hτ : IsLocallyConstant τ)
    (hinv : ∀ w : ↥(pullback (pullback.snd f π) (pullback.snd f π)),
      τ ((pullback.fst (pullback.snd f π) (pullback.snd f π)).base w) =
        τ ((pullback.snd (pullback.snd f π) (pullback.snd f π)).base w)) (a : A) :
    IsClopen ((pullback.snd f π).base '' (τ ⁻¹' {a})) := by
  classical
  set q := pullback.snd f π
  -- the level sets of `τ` are saturated
  have hsat (a : A) : q.base ⁻¹' (q.base '' (τ ⁻¹' {a})) = τ ⁻¹' {a} := by
    refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
    rintro x₁ ⟨x₂, hx₂, hq⟩
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := q) x₁ x₂
      hq.symm
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx₂ ⊢
    rw [← hw₁, hinv w, hw₂, hx₂]
  have hcov : Presieve.ofArrows (fun _ : Unit ↦ pullback f π) (fun _ ↦ q) ∈
      Scheme.proetalePrecoverage T := by
    rw [Presieve.ofArrows_pUnit]
    exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) inferInstance
  have hopen (a : A) : IsOpen (q.base '' (τ ⁻¹' {a})) :=
    Scheme.isOpen_of_isOpen_preimage_of_mem_proetalePrecoverage _ hcov _ fun _ ↦ by
      rw [hsat]
      exact hτ.isOpen_fiber a
  refine ⟨?_, hopen _⟩
  have : (q.base '' (τ ⁻¹' {a}))ᶜ = ⋃ b ∈ ({a}ᶜ : Set A), q.base '' (τ ⁻¹' {b}) := by
    ext t
    obtain ⟨x₁, rfl⟩ := q.surjective t
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
    constructor
    · intro h
      exact ⟨τ x₁, fun h' ↦ h ⟨x₁, h', rfl⟩, x₁, rfl, rfl⟩
    · rintro ⟨b, hb, x₂, hx₂, hq⟩ ⟨x₃, hx₃, hq'⟩
      have h₂ : x₁ ∈ τ ⁻¹' {b} := by
        rw [← hsat]
        exact ⟨x₂, hx₂, hq⟩
      have h₃ : x₁ ∈ τ ⁻¹' {a} := by
        rw [← hsat]
        exact ⟨x₃, hx₃, hq'⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at h₂ h₃
      exact hb (h₂.symm.trans h₃)
  rw [← isOpen_compl_iff, this]
  exact isOpen_biUnion fun b _ ↦ hopen b

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Order.Directed
import WeilConjectures.RingTheory.ArtinianCoefficientDescent
import Mathlib.Algebra.Algebra.Subalgebra.Directed

/-!
# Flat Artinian subalgebras essentially of finite type

Source: Stacks Project, Smoothing Ring Maps, Lemma 16.11.1 (Tag 07FG)
(blueprint: lem-weil-pbc-popescu-artinian-flat-subalgebras).
-/

@[expose] public section

universe u v w

namespace Algebra

/-- An Artinian local algebra in positive characteristic with finite first cotangent homology
of its residue field is a directed union of flat Artinian local subalgebras essentially of
finite type. The final clause spells out the colimit universal property for the inclusion
maps, using compatible families of algebra maps into any test algebra in `Type (max u v w)`.

Source: Stacks Project, Smoothing Ring Maps, Lemma 16.11.1 (Tag 07FG)
(blueprint: lem-weil-pbc-popescu-artinian-flat-subalgebras).

Proof:
1. The coefficient presentation theorem (Tag 07FG, the coefficient-field claim) gives a
   residue-field section, finite maximal-ideal generators and finite coefficients containing
   the image of k in the polynomial image. It also gives generation by all residue coefficients.
2. The coefficient descent theorem (Tag 07FG, the final presentation argument) enlarges the
   finite coefficient set so every further finite enlargement has all the required properties.
3. Index the explicitly constructed subalgebras by finite residue coefficient sets. Monotonicity
   of field and algebra generation gives directedness, with union of finite sets as upper bound.
   Every ideal generator is in the empty stage and every residue coefficient in a singleton
   stage. The presentation's generation clause therefore makes their supremum top, and
   Mathlib's directed-supremum formula gives coverage of Lambda.
4. For compatible maps on the family, Mathlib's Subalgebra.iSupLift constructs the map on the
   top subalgebra. Compose with the inverse of topEquiv. Its restrictions are the given maps
   by iSupLift_mk. Every element belongs to a stage, so agreement there proves uniqueness. -/
theorem exists_directed_artinian_flat_subalgebras
    (k : Type u) [Field k] (Λ : Type v) [CommRing Λ] [Algebra k Λ]
    [IsArtinianRing Λ] [IsLocalRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hH : Module.Finite (IsLocalRing.ResidueField Λ)
      (H1Cotangent k (IsLocalRing.ResidueField Λ))) :
    ∃ S : Set (Subalgebra k Λ),
      DirectedOn (· ≤ ·) S ∧
      (∀ x : Λ, ∃ A ∈ S, x ∈ A) ∧
      (∀ A ∈ S, ∃ hA : IsLocalRing A,
        IsArtinianRing A ∧ RingHom.Flat A.val.toRingHom ∧
        Ideal.map A.val.toRingHom (@IsLocalRing.maximalIdeal A _ hA) =
          IsLocalRing.maximalIdeal Λ ∧ EssFiniteType k A) ∧
      (∀ (T : Type (max u v w)) [CommRing T] [Algebra k T]
        (f : ∀ A : S, A.1 →ₐ[k] T),
        (∀ (A B : S) (h : A.1 ≤ B.1),
          (f B).comp (Subalgebra.inclusion h) = f A) →
        ∃! g : Λ →ₐ[k] T, ∀ A : S, g.comp A.1.val = f A) := by
  classical
  obtain ⟨σ, t, c, hσ, ht, hc, hgen⟩ :=
    exists_artinian_coefficient_presentation k Λ p hp hH
  obtain ⟨c0, _, hgood⟩ := exists_artinian_coefficient_descent k Λ σ t c hσ ht hc
  let A : Finset (IsLocalRing.ResidueField Λ) → Subalgebra k Λ :=
    fun s => artinianCoefficientSubalgebra k Λ σ t (c0 ∪ s)
  have hmono : Monotone A := by
    intro s s' hss'
    apply Algebra.adjoin_mono
    apply Set.union_subset_union_right
    apply Set.image_mono
    exact IntermediateField.adjoin.mono k _ _ (by
      intro x hx
      exact Finset.mem_union.mpr ((Finset.mem_union.mp hx).imp (fun h => h) (fun h => hss' h)))
  have hdir : Directed (· ≤ ·) A := by
    intro s s'
    exact ⟨s ∪ s', hmono Finset.subset_union_left, hmono Finset.subset_union_right⟩
  have htop : (⨆ s, A s) = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply Algebra.adjoin_le
    intro x hx
    rcases hx with hx | ⟨b, rfl⟩
    · apply (le_iSup A ∅)
      exact Algebra.subset_adjoin (Or.inl hx)
    · apply (le_iSup A {b})
      apply Algebra.subset_adjoin
      apply Or.inr
      refine ⟨b, ?_, rfl⟩
      exact IntermediateField.subset_adjoin k _ (by simp)
  let S : Set (Subalgebra k Λ) := Set.range A
  have hcover : ∀ x : Λ, ∃ B ∈ S, x ∈ B := by
    intro x
    have hx : x ∈ (⨆ s, A s) := by rw [htop]; trivial
    rw [← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed hdir] at hx
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
    exact ⟨A s, ⟨s, rfl⟩, hs⟩
  have hSdir : DirectedOn (· ≤ ·) S := by
    rintro B ⟨s, rfl⟩ C ⟨s', rfl⟩
    obtain ⟨s'', h₁, h₂⟩ := hdir s s'
    exact ⟨A s'', ⟨s'', rfl⟩, h₁, h₂⟩
  refine ⟨S, hSdir, hcover, ?_, ?_⟩
  · rintro B ⟨s, rfl⟩
    exact hgood (c0 ∪ s) Finset.subset_union_left
  · intro T _ _ f hf
    have : Nonempty S := ⟨⟨A ∅, ⟨∅, rfl⟩⟩⟩
    have hdir' : Directed (· ≤ ·) (fun B : S => B.1) := by
      intro B C
      obtain ⟨D, hD, hBD, hCD⟩ := hSdir B.1 B.2 C.1 C.2
      exact ⟨⟨D, hD⟩, hBD, hCD⟩
    have htop' : (⊤ : Subalgebra k Λ) ≤ ⨆ B : S, B.1 := by
      intro x _
      obtain ⟨B, hB, hx⟩ := hcover x
      exact le_iSup (fun B : S => B.1) ⟨B, hB⟩ hx
    let gtop : (⊤ : Subalgebra k Λ) →ₐ[k] T :=
      Subalgebra.iSupLift (fun B : S => B.1) hdir' f
        (fun B C h => (hf B C h).symm) ⊤ htop'
    let g : Λ →ₐ[k] T := gtop.comp Subalgebra.topEquiv.symm.toAlgHom
    have hg : ∀ B : S, g.comp B.1.val = f B := by
      intro B
      ext x
      change gtop ⟨(x : Λ), _⟩ = f B x
      exact Subalgebra.iSupLift_mk (fun B : S => B.1) x (by trivial)
    refine ⟨g, hg, ?_⟩
    intro g' hg'
    ext x
    obtain ⟨B, hB, hx⟩ := hcover x
    let b : S := ⟨B, hB⟩
    have h₁ := DFunLike.congr_fun (hg' b) ⟨x, hx⟩
    have h₂ := DFunLike.congr_fun (hg b) ⟨x, hx⟩
    exact h₁.trans h₂.symm

end Algebra

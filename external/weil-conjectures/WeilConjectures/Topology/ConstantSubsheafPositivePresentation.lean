/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Topology.AbelianOpenExtensionByZero
import WeilConjectures.Topology.ConstantSubsheafPositiveRefinement

/-! # Positive constant compact-open components

Source: Stacks Project, Cohomology, Lemma 0A38, first proof paragraph.
(blueprint: lem-sc-constant-subsheaf-positive-presentation)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

/-- Refine a finite compact-open presentation into positive constant components.
Source: Stacks Project, Cohomology, Lemma 0A38, first proof paragraph.
(blueprint: lem-sc-constant-subsheaf-positive-presentation)

Proof: Apply positive clopen refinement to the given finite family and its map g.
This gives positive components f and a factorization l ≫ Sigma.desc f = g.
Since g is epi, Mathlib's epi_of_epi_fac makes Sigma.desc f epi. Retain the
compactness, positivity and unit-value equations from the refinement. -/
theorem constantSubsheaf_positive_presentation
    (X : TopCat.{u}) (K C : Sheaf AddCommGrpCat X) (ι : K ⟶ C) [Mono ι]
    (isoC : C ≅ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
    (hgen : ∃ (n : ℕ) (U : Fin n → Opens X)
      (_ : ∀ i, IsCompact ((U i : Opens X) : Set X)),
      ∃ g : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K, Epi g) :
    ∃ (n : ℕ) (A : Fin n → Opens X),
      (∀ i, IsCompact (A i : Set X)) ∧
      ∃ (c : Fin n → ℕ), (∀ i, 0 < c i) ∧
      ∃ (f : ∀ i, (abelianOpenExtensionByZero (A i)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ K),
        Epi (Sigma.desc f) ∧ ∀ i,
        (ι ≫ isoC.hom).hom.app (op (A i))
      ((f i).hom.app (op (A i)) (abelianOpenExtensionSection (A i)
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) (A i) le_rfl
      ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        ((Functor.const (Opens ((Opens.toTopCat X).obj (A i)))ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app
        (op ((Opens.map (A i).inclusion').obj (A i))) (ULift.up 1)))) =
      (toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).app
      (op (A i)) (ULift.up (c i : ℤ)) := by
  obtain ⟨m, U, hU, g, hg⟩ := hgen
  obtain ⟨n, A, hA, c, hc, f, ⟨l, hl⟩, hv⟩ :=
    constantSubsheaf_positive_refinement X K C ι isoC m U hU g
  have : Epi g := hg
  exact ⟨n, A, hA, c, hc, f, epi_of_epi_fac hl, hv⟩

end TopCat.Sheaf

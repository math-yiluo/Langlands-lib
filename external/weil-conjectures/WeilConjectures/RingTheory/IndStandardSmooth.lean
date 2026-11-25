/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Smooth.StandardSmooth
import WeilConjectures.RingTheory.FilteredColimitOfFactorization
import WeilConjectures.RingTheory.SmoothStandardSmoothRetract
import WeilConjectures.RingTheory.IndSmoothFinitePresentationFactorization

/-!
# Filtered colimits of standard smooth algebras

Source: Stacks Project, Smoothing Ring Maps, Lemma 16.3.5, Tag 07CI
(blueprint: lem-weil-pbc-colimit-standard-smooth-algebras).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace Algebra

/-- A filtered colimit of smooth `R`-algebras is a filtered colimit of standard smooth
`R`-algebras. `ObjectProperty.ind` supplies a small nonempty filtered index category,
a diagram of commutative `R`-algebras and a colimit presentation of `Λ`.
Algebras and index categories live in universe `max u v`, as in
theorem-finite-etale-covers-proper-henselian--2, so that the index of step 4 (finitely
presented algebras over `R` with maps to `Λ`) is small.

Source: Stacks Project, Smoothing Ring Maps, Lemma 16.3.5, Tag 07CI
(blueprint: lem-weil-pbc-colimit-standard-smooth-algebras).

Proof:
1. Let `E` be all standard smooth algebras in the given universe. Its members are
   finitely presented; the factorization criterion handles small representatives internally.
2. A map from a finitely presented algebra `A` to `Λ` factors through a smooth algebra `B`
   by `exists_smooth_factorization_of_ind_smooth`, which handles the underlying-ring
   colimit and finite-presentation factorization.
3. Apply lem-weil-pbc-smooth-retract-standard-smooth (Tag 07CH) to obtain `B → C → B`
   with composite the identity and `C` standard smooth. Associativity and the retraction
   identity give the required factorization `A → B → C → B → Λ` through a member of `E`.
4. Apply lem-weil-pbc-factorization-criterion-filtered-colimit (Tag 07C3) to `E` and these
   factorizations, and package its filtered diagram and colimit witness as
   `ObjectProperty.ind` of standard smoothness. -/
theorem ind_isStandardSmooth_of_ind_smooth
    (R : Type u) [CommRing R] (Λ : CommAlgCat.{max u v} R)
    (h : ObjectProperty.ind.{max u v} (fun B : CommAlgCat.{max u v} R ↦ Smooth R B) Λ) :
    ObjectProperty.ind.{max u v} (fun C : CommAlgCat.{max u v} R ↦ IsStandardSmooth R C)
      Λ := by
  classical
  let E : Set (CommAlgCat.{max u v} R) := {C | IsStandardSmooth R C}
  have hfp : ∀ C ∈ E, FinitePresentation R C := by
    intro C hC
    have : IsStandardSmooth R C := hC
    infer_instance
  have hfactor : ∀ (A : CommAlgCat.{max u v} R), FinitePresentation R A →
      ∀ (α : A ⟶ Λ), ∃ (C : CommAlgCat.{max u v} R), C ∈ E ∧
        ∃ (β : A ⟶ C) (γ : C ⟶ Λ), β ≫ γ = α := by
    intro A hA α
    have : FinitePresentation R A := hA
    obtain ⟨B, hB, hRB, hsm, β, δ, hδβ⟩ :=
      exists_smooth_factorization_of_ind_smooth α.hom h
    obtain ⟨C, hC, hRC, hstd, ι, ρ, hρι, _⟩ :=
      Smooth.exists_standardSmooth_retract R B
    refine ⟨CommAlgCat.of R C, hstd, CommAlgCat.ofHom (ι.comp β),
      CommAlgCat.ofHom (δ.comp ρ), ?_⟩
    apply CommAlgCat.hom_ext
    change (δ.comp ρ).comp (ι.comp β) = α.hom
    rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc ρ, hρι]
    simpa using hδβ
  obtain ⟨J, hJ, hfiltered, D, ι, hD, ⟨hc⟩⟩ :=
    CommAlgCat.exists_filtered_colimit_of_factorization R Λ E hfp hfactor
  exact ⟨J, hJ, hfiltered, ⟨D, ι, hc⟩, hD⟩

end Algebra

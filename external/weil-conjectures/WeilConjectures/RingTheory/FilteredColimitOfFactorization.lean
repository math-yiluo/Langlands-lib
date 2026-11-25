/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.RingTheory.ColimitFinitelyPresentedAlgebras
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Filtered colimits from a factorization criterion

Source: Stacks Project, Algebra, Lemma 10.127.4, Tag 07C3, implication (2) ⇒ (1)
(blueprint: lem-weil-pbc-factorization-criterion-filtered-colimit).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CommAlgCat

/-- If every map from a finitely presented `R`-algebra to `Λ` factors through a member
of a set `E` of finitely presented `R`-algebras, then `Λ` is a filtered colimit of
members of `E`. The natural transformation `ι` gives the compatible coprojections,
and `IsColimit` gives their universal property. The index category is small, in the
universe `max u v` of the algebras (as in theorem-finite-etale-covers-proper-henselian--2);
no smallness assumption on `E` is needed, since finitely presented algebras have only a
small set of isomorphism classes.

Source: Stacks Project, Algebra, Lemma 10.127.4, Tag 07C3, implication (2) ⇒ (1)
(blueprint: lem-weil-pbc-factorization-criterion-filtered-colimit).

Proof:
1. Choose `E' ⊆ E` containing exactly one member of each isomorphism class meeting `E`;
   it is small since finitely presented algebras form a small set of isomorphism classes.
   Let `P₀` be the set of quotients of finite polynomial algebras by finitely generated
   ideals, and put `P = P₀ ∪ E'`. Every finitely presented algebra is isomorphic to a
   member of `P`. The category `I` of pairs `(A, α : A → Λ)` with `A ∈ P` is small,
   filtered, and its forgetful diagram has colimit `Λ`, by
   theorem-finite-etale-covers-proper-henselian--2 (Tag 0BUF), with colimit understood
   as in def-weil-pbc-category-colimit.
2. Let `J` be the full subcategory on pairs `(B, γ)` with `B ∈ E'`. The hypothesis
   factors every `α` as `β ≫ γ` through a member of `E`, and composing with an
   isomorphism onto a member of `E'` gives an arrow from every object of `I` to an
   object of `J`. This subcategory is small.
3. Apply lem-weil-pbc-colimit-initial-full-subcategory to `Iᵒᵖ` and `Jᵒᵖ` (Tags 0BUC
   and 04E7). It says that `J` is filtered and the colimit of the restricted diagram
   maps isomorphically to `Λ`, compatibly with its coprojections.
4. Transport the colimit cocone along this isomorphism. Explicitly, if `L → Λ` is
   the comparison isomorphism and `L → M` the unique map to another cocone, composing
   with its inverse gives the unique map `Λ → M`. Thus the maps `γ` make `Λ` a
   colimit of the diagram of members of `E`, as in def-weil-pbc-category-colimit. -/
theorem exists_filtered_colimit_of_factorization
    (R : Type u) [CommRing R] (Λ : CommAlgCat.{max u v} R)
    (E : Set (CommAlgCat.{max u v} R))
    (hfp : ∀ B ∈ E, Algebra.FinitePresentation R B)
    (hfactor : ∀ (A : CommAlgCat.{max u v} R), Algebra.FinitePresentation R A →
      ∀ (α : A ⟶ Λ), ∃ (B : CommAlgCat.{max u v} R), B ∈ E ∧
        ∃ (β : A ⟶ B) (γ : B ⟶ Λ), β ≫ γ = α) :
    ∃ (J : Type (max u v)) (_ : SmallCategory J) (_ : IsFiltered J)
      (D : J ⥤ CommAlgCat.{max u v} R) (ι : D ⟶ (Functor.const J).obj Λ),
      (∀ j : J, D.obj j ∈ E) ∧ Nonempty (IsColimit (Cocone.mk Λ ι)) := by
  classical
  let FP : ObjectProperty (CommAlgCat.{max u v} R) :=
    fun A ↦ Algebra.FinitePresentation R A
  let FT : ObjectProperty (CommAlgCat.{max u v} R) := fun A ↦ Algebra.FiniteType R A
  have hFT : ObjectProperty.EssentiallySmall.{max u v} FT := by
    have : EssentiallySmall.{u} FT.FullSubcategory := inferInstance
    have : ObjectProperty.EssentiallySmall.{u} FT.ι.essImage := inferInstance
    have : ObjectProperty.EssentiallySmall.{max u v} FT.ι.essImage := by
      obtain ⟨Q, hQ, hrep⟩ :=
        ObjectProperty.EssentiallySmall.exists_small_le'.{u} FT.ι.essImage
      exact ⟨Q, small_lift.{_, v, u} (Subtype Q), hrep⟩
    exact ObjectProperty.EssentiallySmall.of_le (Q := FT.ι.essImage)
      (fun A hA ↦ ⟨⟨A, hA⟩, ⟨Iso.refl A⟩⟩)
  have hFPFT : FP ≤ FT := fun A hA ↦ @Algebra.FiniteType.of_finitePresentation
    R A _ _ _ hA
  have : ObjectProperty.EssentiallySmall.{max u v} FP :=
    ObjectProperty.EssentiallySmall.of_le hFPFT
  let EP : ObjectProperty (CommAlgCat.{max u v} R) := fun A ↦ A ∈ E
  have : ObjectProperty.EssentiallySmall.{max u v} EP :=
    ObjectProperty.EssentiallySmall.of_le (Q := FP) hfp
  obtain ⟨P₀, hP₀small, hP₀fp, hP₀rep⟩ :=
    ObjectProperty.EssentiallySmall.exists_small_le FP
  obtain ⟨E₀, hE₀small, hE₀E, hE₀rep⟩ :=
    ObjectProperty.EssentiallySmall.exists_small_le EP
  let P := P₀ ⊔ E₀
  have hPfp : ∀ A, P A → Algebra.FinitePresentation R A := by
    intro A hA
    rcases hA with hA | hA
    · exact hP₀fp A hA
    · exact hfp A (hE₀E A hA)
  have hPrep : ∀ A : CommAlgCat.{max u v} R, Algebra.FinitePresentation R A →
      ∃ B : P.FullSubcategory, Nonempty (A ≅ B.obj) := by
    intro A hA
    obtain ⟨B, hB, he⟩ := hP₀rep A hA
    exact ⟨⟨B, Or.inl hB⟩, he⟩
  obtain ⟨hIsmall, hIfiltered, ⟨hc⟩⟩ :=
    isFiltered_and_isColimit_finitelyPresentedAlgebras R Λ P hPfp hPrep
  let I := CostructuredArrow P.ι Λ
  let Q : ObjectProperty I := fun i ↦ E₀ i.left.obj
  let F := Q.ι
  have hreach : ∀ i : I, ∃ j : Q.FullSubcategory, Nonempty (i ⟶ F.obj j) := by
    intro i
    obtain ⟨B, hBE, β, γ, hβγ⟩ := hfactor i.left.obj (hPfp _ i.left.property) i.hom
    obtain ⟨B', hB', ⟨e⟩⟩ := hE₀rep B hBE
    let b : P.FullSubcategory := ⟨B', Or.inr hB'⟩
    let j : I := CostructuredArrow.mk (Y := b) (e.inv ≫ γ)
    refine ⟨⟨j, hB'⟩, ⟨CostructuredArrow.homMk
      (ObjectProperty.homMk (β ≫ e.hom)) ?_⟩⟩
    change (β ≫ e.hom) ≫ (e.inv ≫ γ) = i.hom
    simpa [Category.assoc] using hβγ
  have : IsFiltered Q.FullSubcategory :=
    IsFiltered.of_exists_of_isFiltered_of_fullyFaithful F hreach
  have : F.Final := Functor.final_of_exists_of_isFiltered_of_fullyFaithful F hreach
  let c := Cocone.fromCostructuredArrow P.ι (𝟭 I)
  have hc' : IsColimit (c.whisker F) :=
    (Functor.Final.isColimitWhiskerEquiv F c).symm hc
  have : Small.{max u v} Q.FullSubcategory := by
    exact small_of_injective (f := fun j : Q.FullSubcategory ↦ j.obj)
      (fun a b h ↦ by cases a; cases b; cases h; rfl)
  let e := Shrink.equivalence.{max u v} Q.FullSubcategory
  have : IsFiltered (Shrink.{max u v} Q.FullSubcategory) := IsFiltered.of_equivalence e
  let c' := (c.whisker F).whisker e.inverse
  refine ⟨Shrink.{max u v} Q.FullSubcategory, inferInstance, inferInstance,
    _, c'.ι, ?_, ?_⟩
  · intro j
    exact hE₀E _ (e.inverse.obj j).property
  · exact ⟨(Functor.Final.isColimitWhiskerEquiv e.inverse (c.whisker F)).symm hc'⟩

end CommAlgCat

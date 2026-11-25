/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalization
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # The localization telescope of integral continuous coefficients -/

@[expose] public section

universe u v w x
open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The sequential diagram obtained by repeatedly multiplying an object by ℓ.
Source: Bhatt--Scholze, Lemma 6.8.2, localization telescope.
(blueprint: def-weil-pbc-integral-localization-telescope). -/
abbrev integralLocalizationSequence {C : Type v} [Category.{w} C] [Preadditive C] (K : C) :
    ℕ ⥤ C :=
  Functor.ofSequence (fun _ ↦ ℓ • 𝟙 K)

/-- Additive functors carry the scalar telescope to the same scalar telescope.
Source: functoriality of scalar multiplication in a preadditive category.
(blueprint: def-weil-pbc-integral-localization-telescope). -/
noncomputable def integralLocalizationSequenceMapIso
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (F : A ⥤ B) [F.Additive] (K : A) :
    integralLocalizationSequence ℓ K ⋙ F ≅ integralLocalizationSequence ℓ (F.obj K) := by
  let α : integralLocalizationSequence ℓ K ⋙ F ⟶
      integralLocalizationSequence ℓ (F.obj K) :=
    NatTrans.ofSequence (fun _ ↦ 𝟙 _) (by
      intro n
      simp only [Functor.comp_map, integralLocalizationSequence,
        Functor.ofSequence_map_homOfLE_succ]
      change F.map (ℓ • 𝟙 K) ≫ 𝟙 (F.obj K) = 𝟙 (F.obj K) ≫ (ℓ • 𝟙 (F.obj K))
      rw [F.map_nsmul, F.map_id]
      simp)
  have : ∀ n, IsIso (α.app n) := fun n ↦ by
    change IsIso (𝟙 _)
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α


end AlgebraicGeometry.ProEtale.CondensedRing

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import WeilConjectures.WeilSheaf.Category

/-!
# Short exact sequences of Weil sheaves and distinguished triangles

A short exact sequence `0 → F₁ → F₂ → F₃ → 0` of Weil sheaves gives a distinguished triangle
`F₁ → F₂ → F₃ → F₁[1]` of Weil complexes (`AlgebraicGeometry.WeilSheaf.singleTriangle` and
`AlgebraicGeometry.WeilSheaf.singleTriangle_distinguished`): the inclusion of Weil sheaves into
pro-étale Weil sheaves is exact, and the triangle is the one attached to the short exact sequence
in the derived category of pro-étale Weil sheaves (`DerivedCategory.singleTriangle`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

namespace WeilSheaf

instance : Functor.PreservesZeroMorphisms (C := WeilSheaf k₀ l X)
    (WeilSheaf.objectProperty k₀ l X).ι :=
  ⟨fun _ _ ↦ rfl⟩

instance :
    PreservesFiniteLimits (C := WeilSheaf k₀ l X) (WeilSheaf.objectProperty k₀ l X).ι :=
  have := (WeilSheaf.objectProperty k₀ l X).preservesKernels_ι
  Functor.preservesFiniteLimits_of_preservesKernels _

instance :
    PreservesFiniteColimits (C := WeilSheaf k₀ l X) (WeilSheaf.objectProperty k₀ l X).ι :=
  have := (WeilSheaf.objectProperty k₀ l X).preservesCokernels_ι
  Functor.preservesFiniteColimits_of_preservesCokernels _

variable {S : ShortComplex (WeilSheaf k₀ l X)}

/-- A short exact sequence of Weil sheaves is short exact as a sequence of pro-étale Weil
sheaves. -/
lemma shortExact_map_ι (hS : S.ShortExact) :
    (S.map (WeilSheaf.objectProperty k₀ l X).ι).ShortExact :=
  hS.map_of_exact _

/-- The connecting morphism `F₃ ⟶ F₁[1]` of Weil complexes attached to a short exact sequence
`0 → F₁ → F₂ → F₃ → 0` of Weil sheaves. -/
noncomputable def singleδ (hS : S.ShortExact) :
    toComplex.obj S.X₃ ⟶ (toComplex.obj S.X₁)⟦(1 : ℤ)⟧ :=
  (WeilComplex.objectProperty k₀ l X).fullyFaithfulι.preimage
    ((shortExact_map_ι hS).singleδ ≫
      ((WeilComplex.objectProperty k₀ l X).ι.commShiftIso (1 : ℤ)).inv.app
        (toComplex.obj S.X₁))

lemma ι_map_singleδ (hS : S.ShortExact) :
    (WeilComplex.objectProperty k₀ l X).ι.map (singleδ hS) =
      (shortExact_map_ι hS).singleδ ≫
        ((WeilComplex.objectProperty k₀ l X).ι.commShiftIso (1 : ℤ)).inv.app
          (toComplex.obj S.X₁) :=
  (WeilComplex.objectProperty k₀ l X).fullyFaithfulι.map_preimage _

/-- The triangle `F₁ → F₂ → F₃ → F₁[1]` of Weil complexes attached to a short exact sequence
`0 → F₁ → F₂ → F₃ → 0` of Weil sheaves. -/
noncomputable def singleTriangle (hS : S.ShortExact) : Triangle (WeilComplex k₀ l X) :=
  Triangle.mk (toComplex.map S.f) (toComplex.map S.g) (singleδ hS)

lemma ι_mapTriangle_obj_singleTriangle_mor₃ (hS : S.ShortExact) :
    ((WeilComplex.objectProperty k₀ l X).ι.mapTriangle.obj (singleTriangle hS)).mor₃ =
      (shortExact_map_ι hS).singleδ := by
  calc _ = (WeilComplex.objectProperty k₀ l X).ι.map (singleδ hS) ≫
        ((WeilComplex.objectProperty k₀ l X).ι.commShiftIso (1 : ℤ)).hom.app
          (toComplex.obj S.X₁) := rfl
    _ = _ := by
      rw [ι_map_singleδ, Category.assoc, Iso.inv_hom_id_app]
      exact Category.comp_id _

/-- The triangle of Weil complexes attached to a short exact sequence of Weil sheaves is
distinguished. -/
lemma singleTriangle_distinguished (hS : S.ShortExact) :
    singleTriangle hS ∈ distTriang (WeilComplex k₀ l X) := by
  refine isomorphic_distinguished _ (shortExact_map_ι hS).singleTriangle_distinguished _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [singleTriangle]; rfl)
      (by simp [singleTriangle]; rfl) ?_)
  dsimp only [Iso.refl_hom]
  rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  exact ι_mapTriangle_obj_singleTriangle_mor₃ hS


section Exactness

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- A functor `Φ` between Weil sheaves which lifts a left exact functor `Ψ` of pro-étale Weil
sheaves along the inclusions is left exact: the inclusion of Weil sheaves preserves and reflects
finite limits. -/
lemma preservesFiniteLimits_of_comp_ι (Φ : WeilSheaf k₀ l X ⥤ WeilSheaf k₀ l Y)
    (Ψ : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l Y) [PreservesFiniteLimits Ψ]
    (e : Φ ⋙ (WeilSheaf.objectProperty k₀ l Y).ι ≅ (WeilSheaf.objectProperty k₀ l X).ι ⋙ Ψ) :
    PreservesFiniteLimits Φ := by
  have : PreservesFiniteLimits (Φ ⋙ (WeilSheaf.objectProperty k₀ l Y).ι) :=
    preservesFiniteLimits_of_natIso e.symm
  have : (WeilSheaf.objectProperty k₀ l Y).ι.Full := ObjectProperty.full_ι _
  have : (WeilSheaf.objectProperty k₀ l Y).ι.Faithful := ObjectProperty.faithful_ι _
  have : ReflectsFiniteLimits (C := WeilSheaf k₀ l Y) (WeilSheaf.objectProperty k₀ l Y).ι :=
    inferInstance
  exact preservesFiniteLimits_of_reflects_of_preserves Φ (WeilSheaf.objectProperty k₀ l Y).ι

/-- A functor `Φ` between Weil sheaves which lifts a right exact functor `Ψ` of pro-étale Weil
sheaves along the inclusions is right exact: the inclusion of Weil sheaves preserves and reflects
finite colimits. -/
lemma preservesFiniteColimits_of_comp_ι (Φ : WeilSheaf k₀ l X ⥤ WeilSheaf k₀ l Y)
    (Ψ : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l Y) [PreservesFiniteColimits Ψ]
    (e : Φ ⋙ (WeilSheaf.objectProperty k₀ l Y).ι ≅ (WeilSheaf.objectProperty k₀ l X).ι ⋙ Ψ) :
    PreservesFiniteColimits Φ := by
  have : PreservesFiniteColimits (Φ ⋙ (WeilSheaf.objectProperty k₀ l Y).ι) :=
    preservesFiniteColimits_of_natIso e.symm
  have : (WeilSheaf.objectProperty k₀ l Y).ι.Full := ObjectProperty.full_ι _
  have : (WeilSheaf.objectProperty k₀ l Y).ι.Faithful := ObjectProperty.faithful_ι _
  have : ReflectsFiniteColimits (C := WeilSheaf k₀ l Y) (WeilSheaf.objectProperty k₀ l Y).ι :=
    inferInstance
  exact preservesFiniteColimits_of_reflects_of_preserves Φ (WeilSheaf.objectProperty k₀ l Y).ι

variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

/-- The pullback of Weil sheaves is left exact. -/
instance : PreservesFiniteLimits (WeilSheaf.upperStar (k₀ := k₀) (l := l) φ) :=
  preservesFiniteLimits_of_comp_ι _ (ProEtaleWeilSheaf.upperStar k₀ l φ)
    (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _)

/-- The pullback of Weil sheaves is right exact. -/
instance : PreservesFiniteColimits (WeilSheaf.upperStar (k₀ := k₀) (l := l) φ) :=
  preservesFiniteColimits_of_comp_ι _ (ProEtaleWeilSheaf.upperStar k₀ l φ)
    (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _)

end Exactness

end WeilSheaf

end AlgebraicGeometry

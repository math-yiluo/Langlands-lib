/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.CategoryTheory.Idempotents.Pretriangulated
public import WeilConjectures.CategoryTheory.StageSystem.Triangulated
public import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.WeilSheaf.FieldCoefficientKaroubian

/-!
# The triangulated structure of `D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E)`

The transition functors `F ⊗_E - : D^b_{c,W}(X, E) ⥤ D^b_{c,W}(X, F)` of the stage system
`AlgebraicGeometry.FieldWeilComplex.stageSystem` are triangulated, and the associativity
constraints `G ⊗_F (F ⊗_E -) ≅ G ⊗_E -` commute with the shifts. Hence the `2`-colimit
`AlgebraicGeometry.WeilComplexTwoColimit k₀ l X` is a triangulated category
(`CategoryTheory.StageSystem.PairCategory.pretriangulated`,
`CategoryTheory.StageSystem.PairCategory.isTriangulated`), the distinguished triangles being the
triangles isomorphic to images of distinguished triangles at a finite stage, and its canonical
functor into its Karoubi envelope is an exact equivalence.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory

namespace ObjectProperty

variable {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [HasShift C₁ ℤ]
  [HasShift C₂ ℤ] [HasShift C₃ ℤ] (P₁ : ObjectProperty C₁) (P₂ : ObjectProperty C₂)
  (P₃ : ObjectProperty C₃) [P₁.IsStableUnderShift ℤ] [P₂.IsStableUnderShift ℤ]
  [P₃.IsStableUnderShift ℤ] {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃} {F₁₃ : C₁ ⥤ C₃}
  [F₁₂.CommShift ℤ] [F₂₃.CommShift ℤ] [F₁₃.CommShift ℤ]

set_option linter.flexible false in
/-- A natural transformation between functors of full subcategories induced by functors
commuting with the shifts, which is given componentwise by a natural transformation commuting
with the shifts, commutes with the shifts. -/
lemma natTransCommShift_liftFullSubcategory (h₁₂ : ∀ X, P₁ X → P₂ (F₁₂.obj X))
    (h₂₃ : ∀ X, P₂ X → P₃ (F₂₃.obj X)) (h₁₃ : ∀ X, P₁ X → P₃ (F₁₃.obj X))
    (γ : F₁₂ ⋙ F₂₃ ⟶ F₁₃) [NatTrans.CommShift γ ℤ]
    (α : P₁.liftFullSubcategory P₂ F₁₂ h₁₂ ⋙ P₂.liftFullSubcategory P₃ F₂₃ h₂₃ ⟶
      P₁.liftFullSubcategory P₃ F₁₃ h₁₃) (hα : ∀ K, (α.app K).hom = γ.app K.obj) :
    NatTrans.CommShift α ℤ := by
  have e : Functor.whiskerRight α P₃.ι = (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (P₂.liftFullSubcategoryCompιIso P₃ F₂₃ h₂₃).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (P₁.liftFullSubcategoryCompιIso P₂ F₁₂ h₁₂).hom F₂₃ ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft P₁.ι γ ≫
      (P₁.liftFullSubcategoryCompιIso P₃ F₁₃ h₁₃).inv := by
    ext K
    simp [liftFullSubcategoryCompιIso, hα]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
  have : NatTrans.CommShift (Functor.whiskerRight α P₃.ι) ℤ := by
    rw [e]
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ P₃.ι

end ObjectProperty

namespace Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

instance commShift_mapDerivedCategoryCompNatIso_hom {C D E : Type*} [Category C] [Category D]
    [Category E] [Abelian C] [Abelian D] [Abelian E] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E] {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (γ : F ⋙ G ≅ H) :
    NatTrans.CommShift (mapDerivedCategoryCompNatIso γ).hom ℤ := by
  dsimp only [mapDerivedCategoryCompNatIso, Iso.trans_hom, Iso.symm_hom]
  infer_instance

end Functor

end CategoryTheory

namespace AlgebraicGeometry

open PadicAlgCl

variable {l : ℕ} [Fact l.Prime] (k₀ : Type u) [Field k₀] [Finite k₀] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k₀))]

namespace FieldWeilComplex

section Transition

variable {Λ₁ Λ₂ Λ₃ : Type} [NormedField Λ₁] [IsUltrametricDist Λ₁]
  [NormedField Λ₂] [IsUltrametricDist Λ₂] [NormedField Λ₃] [IsUltrametricDist Λ₃]
  [Algebra ℚ_[l] Λ₁] [Algebra ℚ_[l] Λ₂] [Algebra ℚ_[l] Λ₃] [FiniteDimensional ℚ_[l] Λ₂]
  [FiniteDimensional ℚ_[l] Λ₃] {e₁ : Λ₁ →ₐ[ℚ_[l]] Λ₂} {e₂ : Λ₂ →ₐ[ℚ_[l]] Λ₃}
  (he₁ : Continuous e₁) (he₂ : Continuous e₂) (hc₁ : Continuous (algebraMap ℚ_[l] Λ₁))
  (hc₂ : Continuous (algebraMap ℚ_[l] Λ₂)) [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The extension of scalars `D^b_{c,W}(X, Λ₁) ⥤ D^b_{c,W}(X, Λ₂)` commutes with the shifts. -/
noncomputable instance extendScalars_commShift :
    (FieldWeilComplex.extendScalars he₁ hc₁ k₀ X).CommShift ℤ := by
  dsimp only [FieldWeilComplex.extendScalars]
  exact ObjectProperty.commShiftLiftFullSubcategory _ _ _ _

/-- The extension of scalars `D^b_{c,W}(X, Λ₁) ⥤ D^b_{c,W}(X, Λ₂)` is triangulated. -/
instance extendScalars_isTriangulated :
    (FieldWeilComplex.extendScalars he₁ hc₁ k₀ X).IsTriangulated := by
  dsimp only [FieldWeilComplex.extendScalars]
  exact ObjectProperty.isTriangulated_liftFullSubcategory _ _ _ _

/-- The associativity constraint `Λ₃ ⊗_{Λ₂} (Λ₂ ⊗_{Λ₁} -) ≅ Λ₃ ⊗_{Λ₁} -` of the extensions of
scalars of `D^b_{c,W}` commutes with the shifts. -/
instance extendScalarsCompIso_commShift :
    NatTrans.CommShift (FieldWeilComplex.extendScalarsCompIso he₁ he₂ hc₁ hc₂ k₀ X).hom ℤ :=
  ObjectProperty.natTransCommShift_liftFullSubcategory _ _ _ _ _ _
    (Functor.mapDerivedCategoryCompNatIso
      (ProEtaleFieldWeilSheaf.extendScalarsCompIso he₁ he₂ hc₁ hc₂ k₀ X)).hom _ (fun _ ↦ rfl)

end Transition

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

noncomputable instance stageSystem_T_commShift {E F : FiniteIntermediateField l} (h : E ≤ F) :
    ((stageSystem (l := l) k₀ X).T h).CommShift ℤ := by
  dsimp only [stageSystem, transition]
  infer_instance

instance stageSystem_T_isTriangulated {E F : FiniteIntermediateField l} (h : E ≤ F) :
    ((stageSystem (l := l) k₀ X).T h).IsTriangulated := by
  dsimp only [stageSystem, transition]
  infer_instance

instance stageSystem_assoc_commShift {E F G : FiniteIntermediateField l} (h : E ≤ F)
    (h' : F ≤ G) : NatTrans.CommShift ((stageSystem (l := l) k₀ X).assoc h h').hom ℤ :=
  extendScalarsCompIso_commShift k₀ X (continuous_inclusion_finiteIntermediateField h)
    (continuous_inclusion_finiteIntermediateField h') (continuous_algebraMap_intermediateField _)
    (continuous_algebraMap_intermediateField _)

end FieldWeilComplex

namespace WeilComplexTwoColimit

variable [Fact (ringChar k₀ ≠ l)] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `definition-weil-structure`: `D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E)` is
a pretriangulated category, the distinguished triangles being the triangles isomorphic to the
images of distinguished triangles of a finite stage `D^b_{c,W}(X, E)`. -/
noncomputable instance pretriangulated : Pretriangulated (WeilComplexTwoColimit k₀ l X) :=
  StageSystem.PairCategory.pretriangulated (S := FieldWeilComplex.stageSystem (l := l) k₀ X)

/-- Blueprint `definition-weil-structure`: `D^b_{c,W}(X, ℚ̄_ℓ)` is a triangulated category. -/
instance isTriangulated : IsTriangulated (WeilComplexTwoColimit k₀ l X) :=
  StageSystem.PairCategory.isTriangulated (S := FieldWeilComplex.stageSystem (l := l) k₀ X)

omit [Fact (ringChar k₀ ≠ l)] in
/-- The functors `D^b_{c,W}(X, E) ⥤ D^b_{c,W}(X, ℚ̄_ℓ)` of the finite stages are triangulated. -/
example (E : FiniteIntermediateField l) :
    ((FieldWeilComplex.stageSystem (l := l) k₀ X).ι E).IsTriangulated :=
  inferInstance

/-- Idempotent completeness of the common-stage Weil category.

`D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E)` (`AlgebraicGeometry.WeilComplexTwoColimit`) is
idempotent complete, and the canonical functor into its Karoubi envelope is an exact
equivalence: every stage `D^b_{c,W}(X, E)` is idempotent complete, an idempotent of the
`2`-colimit is represented, and splits, at a finite stage
(`CategoryTheory.StageSystem.PairCategory.isIdempotentComplete`), and the canonical functor of a
pretriangulated category into its Karoubi envelope is triangulated
(`CategoryTheory.Idempotents.toKaroubi.isTriangulated`). -/
theorem isIdempotentComplete_and_isEquivalence_toKaroubi_and_isTriangulated :
    IsIdempotentComplete (WeilComplexTwoColimit k₀ l X) ∧
      (Idempotents.toKaroubi (WeilComplexTwoColimit k₀ l X)).IsEquivalence ∧
      (Idempotents.toKaroubi (WeilComplexTwoColimit k₀ l X)).IsTriangulated :=
  ⟨(isIdempotentComplete_and_isEquivalence_toKaroubi k₀ l X).1,
    (isIdempotentComplete_and_isEquivalence_toKaroubi k₀ l X).2, inferInstance⟩

end WeilComplexTwoColimit

end AlgebraicGeometry

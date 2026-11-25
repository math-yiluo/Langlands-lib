/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMateReflect
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal

/-!
# Abstract inputs for transporting projection formulas along monoidal equivalences

* `CategoryTheory.Equivalence.isMonoidal_monoidalOfPostcompFunctor`: if `F ⋙ e.functor ≅ F'`
  with `e` a monoidal equivalence and `F'` monoidal, the monoidal structure on `F` transported
  along this isomorphism (`CategoryTheory.Equivalence.monoidalOfPostcompFunctor`) makes the
  isomorphism monoidal.
* `CategoryTheory.Functor.preservesFlat_of_comp_equivalence_iso`: flatness preservation descends
  along a monoidal equivalence.
* `CategoryTheory.Adjunction.ComparisonCompatible.trans_isoWhiskerRight`: the compatibility of
  comparisons (`CategoryTheory.Adjunction.ComparisonCompatible`) survives replacing the left
  adjoint `F` by an isomorphic functor, with the conjugated comparison.
* `CategoryTheory.Functor.comparisonCompatible_leftDerivedTensorComparison`: for a monoidal
  isomorphism `G₁ ⋙ G₂ ≅ F₁ ⋙ F₂` of exact strong monoidal functors, the tensor comparisons of
  the left derived functors are compatible.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u u₁ u₂ u₃ u₄

open CategoryTheory MonoidalCategory Limits Abelian

namespace CategoryTheory

/-! ### Monoidal structures transported along a monoidal equivalence -/

namespace Equivalence

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [MonoidalCategory C]
  [MonoidalCategory D] [MonoidalCategory E]

/-- For a monoidal equivalence `e` and an isomorphism `i : F ⋙ e.functor ≅ F'` with `F'`
monoidal, `i` is monoidal for the monoidal structure on `F` transported along `i`
(`CategoryTheory.Equivalence.monoidalOfPostcompFunctor`). -/
lemma isMonoidal_monoidalOfPostcompFunctor (e : C ≌ D) [e.functor.Monoidal] (F : E ⥤ C)
    {F' : E ⥤ D} [F'.Monoidal] (i : F ⋙ e.functor ≅ F') :
    letI := e.inverseMonoidal
    letI := e.monoidalOfPostcompFunctor F i
    NatTrans.IsMonoidal i.hom := by
  let := e.inverseMonoidal
  let j : F' ⋙ e.inverse ≅ F := Functor.isoWhiskerRight i.symm e.symm.functor ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F e.symm.counitIso ≪≫ F.rightUnitor
  let : F.Monoidal := Functor.Monoidal.transport j
  have : NatTrans.IsMonoidal j.hom := Functor.Monoidal.natTransIsMonoidal_of_transport j
  have hi : i.hom = Functor.whiskerRight j.inv e.functor ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft F' e.counit ≫ F'.rightUnitor.hom := by
    ext X
    simp [j]
  change NatTrans.IsMonoidal i.hom
  rw [hi]
  infer_instance

end Equivalence

/-! ### Flatness preservation along a monoidal equivalence -/

namespace Functor

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory C'] [MonoidalCategory D']

/-- If `F ⋙ e.functor ≅ G ⋙ F'` with `e` a monoidal equivalence and `G`, `F'` preserving flat
objects, then `F` preserves flat objects. -/
lemma preservesFlat_of_comp_equivalence_iso (e : D ≌ D') [e.functor.Monoidal] (F : C ⥤ D)
    (G : C ⥤ C') (F' : C' ⥤ D') [G.PreservesFlat] [F'.PreservesFlat]
    (i : F ⋙ e.functor ≅ G ⋙ F') : F.PreservesFlat where
  flat_obj {X} hX := by
    let := e.inverseMonoidal
    have : e.inverse.PreservesFlat := e.inverse.preservesFlat_of_isEquivalence
    have h₁ : ObjectProperty.flat (e.functor.obj (F.obj X)) :=
      ObjectProperty.prop_of_iso _ (i.app X).symm
        (PreservesFlat.flat_obj (F := F') (PreservesFlat.flat_obj (F := G) hX))
    exact ObjectProperty.prop_of_iso _ (e.unitIso.app (F.obj X)).symm
      (PreservesFlat.flat_obj (F := e.inverse) h₁)

end Functor

/-! ### Compatibility of comparisons under change of the left adjoint -/

namespace Adjunction

open _root_.CategoryTheory.Functor

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {F₀ F : D ⥤ C} {F' : D' ⥤ C'} {N_D : D ⥤ D'} {N_C : C ⥤ C'}
  {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D} {T_C' : C' ⥤ C' ⥤ C'} {T_D' : D' ⥤ D' ⥤ D'}
  {α : N_D ⋙ F' ≅ F₀ ⋙ N_C}
  {φ₀ : (postcompose₂.obj F₀).obj T_D ⟶ (((whiskeringLeft₂ C).obj F₀).obj F₀).obj T_C}
  {φ : (postcompose₂.obj F).obj T_D ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj T_C}
  {φ' : (postcompose₂.obj F').obj T_D' ⟶ (((whiskeringLeft₂ C').obj F').obj F').obj T_C'}
  {m_C : (postcompose₂.obj N_C).obj T_C ≅ (((whiskeringLeft₂ C').obj N_C).obj N_C).obj T_C'}
  {m_D : (postcompose₂.obj N_D).obj T_D ≅ (((whiskeringLeft₂ D').obj N_D).obj N_D).obj T_D'}

/-- The compatibility of comparisons survives replacing `F₀` by an isomorphic functor `F`,
with the comparison of `F` conjugate to the one of `F₀`. -/
lemma ComparisonCompatible.trans_isoWhiskerRight (H : ComparisonCompatible α φ₀ φ' m_C m_D)
    (e : F₀ ≅ F)
    (hφ : ∀ a b, (φ.app a).app b = e.inv.app ((T_D.obj a).obj b) ≫ (φ₀.app a).app b ≫
      (T_C.map (e.hom.app a)).app (F₀.obj b) ≫ (T_C.obj (F.obj a)).map (e.hom.app b)) :
    ComparisonCompatible (α ≪≫ isoWhiskerRight e N_C) φ φ' m_C m_D := by
  intro a b
  have h₁ := NatTrans.congr_app (m_C.hom.naturality (e.hom.app a)) (F₀.obj b)
  have h₂ := (m_C.hom.app (F.obj a)).naturality (e.hom.app b)
  dsimp at h₁ h₂
  have H' := H a b
  simp only [hφ, Functor.map_comp, Category.assoc, Iso.trans_inv, Iso.trans_hom,
    NatTrans.comp_app, isoWhiskerRight_inv, isoWhiskerRight_hom, whiskerRight_app,
    Functor.comp_obj]
  rw [h₂, reassoc_of% h₁, reassoc_of% H']
  erw [(T_C'.map (N_C.map (e.hom.app a))).naturality_assoc (α.hom.app b)]
  rfl

end Adjunction

/-! ### Compatibility of the tensor comparisons of left derived functors -/

namespace Functor

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  {E : Type u₃} [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E] [BraidedCategory E]
  [HasFunctorialFlatResolution E]
  {D' : Type u₄} [Category.{u + 1} D'] [Abelian D'] [IsGrothendieckAbelian.{u + 1} D']
  [MonoidalCategory D'] [MonoidalPreadditive D'] [MonoidalClosed D'] [BraidedCategory D']
  [HasFunctorialFlatResolution D']
  (F₁ : C ⥤ D) [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₁.PreservesFlat] [F₁.IsLeftAdjoint] [F₁.Monoidal]
  (F₂ : D ⥤ E) [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [F₂.PreservesFlat] [F₂.IsLeftAdjoint] [F₂.Monoidal]
  (G₁ : C ⥤ D') [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₁.PreservesFlat] [G₁.IsLeftAdjoint] [G₁.Monoidal]
  (G₂ : D' ⥤ E) [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  [G₂.PreservesFlat] [G₂.IsLeftAdjoint] [G₂.Monoidal]

/-- For a monoidal isomorphism `τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂` of exact strong monoidal functors, the
tensor comparisons of the left derived functors `LG₁`, `LF₂`, `LG₂`, `LF₁` are compatible
along `LF₁ ⋙ LF₂ ≅ LG₁ ⋙ LG₂` in the sense of
`CategoryTheory.Adjunction.ComparisonCompatible`. -/
lemma comparisonCompatible_leftDerivedTensorComparison (τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂)
    [NatTrans.IsMonoidal τ.hom] :
    Adjunction.ComparisonCompatible (leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ τ).symm
      G₁.leftDerivedTensorComparison F₂.leftDerivedTensorComparison
      (asIso G₂.leftDerivedTensorComparison) (asIso F₁.leftDerivedTensorComparison) := by
  intro a b
  have h := map_leftDerivedTensorComparison_comp_eq_of_iso F₁ F₂ G₁ G₂ τ a b
  dsimp
  rw [reassoc_of% h]
  simp only [Iso.hom_inv_id_app_assoc, ← tensorHom_def, tensorHom_comp_tensorHom,
    Iso.hom_inv_id_app]
  simp

/-- The variant of `CategoryTheory.Functor.comparisonCompatible_leftDerivedTensorComparison` for
the functor `D(G₁)` induced by `G₁` on derived categories and its tensor comparison
`CategoryTheory.Functor.mapDerivedCategoryTensorComparison`, along
`LF₁ ⋙ LF₂ ≅ LG₁ ⋙ LG₂ ≅ D(G₁) ⋙ LG₂`. -/
lemma comparisonCompatible_mapDerivedCategoryTensorComparison (τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂)
    [NatTrans.IsMonoidal τ.hom] :
    Adjunction.ComparisonCompatible ((leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ τ).symm ≪≫
        isoWhiskerRight G₁.leftDerivedFunctorIsoMapDerivedCategory G₂.leftDerivedFunctor)
      G₁.mapDerivedCategoryTensorComparison F₂.leftDerivedTensorComparison
      (asIso G₂.leftDerivedTensorComparison) (asIso F₁.leftDerivedTensorComparison) :=
  (comparisonCompatible_leftDerivedTensorComparison F₁ F₂ G₁ G₂ τ).trans_isoWhiskerRight _
    (fun a b ↦ by
      rw [mapDerivedCategoryTensorComparison_app_app, MonoidalCategory.tensorHom_def]
      rfl)

end Functor

end CategoryTheory

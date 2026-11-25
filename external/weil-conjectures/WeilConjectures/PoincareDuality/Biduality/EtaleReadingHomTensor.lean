/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.EquivalenceTensorIso
public import WeilConjectures.CategoryTheory.Monoidal.TensorIso

/-!
# Derived equivalences commuting with tensor products, in both variables

Let `F : C₁ ⥤ C₂` be an additive equivalence of monoidal Grothendieck abelian categories with
functorial flat resolutions, together with a tensor isomorphism `τ : F (A ⊗ B) ≅ F A ⊗ F B`
(`CategoryTheory.Functor.TensorIso`, no coherence required). Then `D(F)` has a tensor
isomorphism `D(F)(K ⊗ᴸ M) ≅ D(F) K ⊗ᴸ D(F) M`, natural in both variables
(`CategoryTheory.Functor.mapDerivedCategoryTensorIsoOfTensorIso`).

It is obtained as `CategoryTheory.Functor.mapDerivedCategoryTensorComparison`, deriving the
comparison `τ` on homotopy categories (`DerivedCategory.mapHomotopyCategoryTensorHom`) instead of
the comonoidal structure of a monoidal functor. (The isomorphism
`DerivedCategory.tensorLeftCompMapDerivedCategoryIsoOfTensorIso` is only natural in the second
variable.)
-/

@[expose] public section

universe u u₁ u₂

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.IsEquivalence] [F.Additive] (τ : F.TensorIso)

/-- The comparison `LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M` of bifunctors, for an additive equivalence `F`
with a tensor isomorphism `τ`, obtained by deriving the comparison induced by `τ` on homotopy
categories. -/
noncomputable def leftDerivedTensorComparisonOfTensorIso :
    leftDerivedDerivedTensor F ⟶ derivedTensorLeftDerived F :=
  haveI := F.preservesFlat_of_isEquivalence_of_tensorIso τ
  leftDerived₂NatTrans _ (derivedTensorLeftDerivedCounit F)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (leftDerivedDerivedTensorCounit F)
    (postcompose₂MapWhiskeringLeft₂ (DerivedCategory.mapHomotopyCategoryTensorHom F τ) Qh)

instance : IsIso (F.leftDerivedTensorComparisonOfTensorIso τ) := by
  dsimp only [leftDerivedTensorComparisonOfTensorIso]
  infer_instance

/-- The tensor isomorphism `D(F)(K ⊗ᴸ M) ≅ D(F) K ⊗ᴸ D(F) M`, natural in both variables, of the
derived functor of an additive equivalence `F` with a tensor isomorphism `τ`: the derived
comparison `CategoryTheory.Functor.leftDerivedTensorComparisonOfTensorIso`, transported along
`LF ≅ D(F)`. -/
noncomputable def mapDerivedCategoryTensorIsoOfTensorIso : F.mapDerivedCategory.TensorIso :=
  TensorIso.ofIso (asIso (F.leftDerivedTensorComparisonOfTensorIso τ))
    F.leftDerivedFunctorIsoMapDerivedCategory

end CategoryTheory.Functor

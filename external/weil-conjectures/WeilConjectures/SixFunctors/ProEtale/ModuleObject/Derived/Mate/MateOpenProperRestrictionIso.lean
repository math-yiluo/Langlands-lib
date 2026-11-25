/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenSquareRestriction
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # The specified open restriction mate is invertible
Source: blueprint proposition-composition-base-change-rf-shriek--1, proof (2).
-/

@[expose] public noncomputable section
set_option linter.privateModule false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem mate_component
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {H : A ⥤ C} {H' : B ⥤ D} (a : L ⊣ R) (b : L' ⊣ R')
    (θ : TwoSquare H L L' H') (M : B) :
    (mateEquiv a b θ).app M =
      b.homEquiv _ _ (θ.app (R.obj M) ≫ H'.map (a.counit.app M)) := by
  simp [mateEquiv, Adjunction.homEquiv_unit]

private theorem inverse_mate_eq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {H : A ⥤ C} {H' : B ⥤ D} (a : L ⊣ R) (b : L' ⊣ R')
    (θ : R ⋙ H ≅ H' ⋙ R') (e : H ⋙ L' ≅ L ⋙ H')
    (he : ∀ M, b.unit.app (H.obj M) ≫ R'.map (e.hom.app M) =
      H.map (a.unit.app M) ≫ θ.hom.app (L.obj M)) :
    ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ θ.hom)) = e.hom := by
  apply NatTrans.ext
  funext M
  apply (b.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ θ.hom) M).symm.trans (he M).symm

end AlgebraicGeometry.ProEtale.CondensedRing

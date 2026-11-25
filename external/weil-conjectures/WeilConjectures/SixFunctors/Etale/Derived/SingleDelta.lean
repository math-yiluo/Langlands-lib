/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.SixFunctors.Etale.Derived.Shift

/-!
# The derived pullback of the connecting morphism of a short exact sequence

A short exact sequence `0 ⟶ S₁ ⟶ S₂ ⟶ S₃ ⟶ 0` of étale sheaves on `Y` has a connecting morphism
`δ : S₃ ⟶ S₁[1]` in `D(Y_ét)` (`CategoryTheory.ShortComplex.ShortExact.singleδ`). For
`f : X ⟶ Y` the pullback `f^*` is exact, and the derived pullback `Lf^*` of `δ` is the
connecting morphism of the pulled back short exact sequence
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_singleδ`), through the identifications
`Lf^*(F[0]) ≅ (f^* F)[0]` (`AlgebraicGeometry.Etale.singleFunctorCompLeftDerivedUpperStarIso`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The derived pullback of the connecting morphism of a short exact sequence of étale sheaves is
the connecting morphism of the pulled back short exact sequence. -/
lemma leftDerivedUpperStar_map_singleδ {S : ShortComplex (Sheaf Y.smallEtaleTopology A)}
    (hS : S.ShortExact) :
    (L((f)^*[A])).map hS.singleδ ≫ ((L((f)^*[A])).commShiftIso (1 : ℤ)).hom.app _ ≫
        ((singleFunctorCompLeftDerivedUpperStarIso A f).hom.app S.X₁)⟦(1 : ℤ)⟧' =
      (singleFunctorCompLeftDerivedUpperStarIso A f).hom.app S.X₃ ≫
        (hS.map_of_exact (f)^*[A]).singleδ := by
  let ε := leftDerivedUpperStarIsoMapDerivedCategory A f
  have h := hS.mapShiftedHom_singleδ' (f)^*[A]
  rw [← cancel_epi (((f)^*[A].mapDerivedCategorySingleFunctor 0).hom.app S.X₃),
    Iso.hom_inv_id_app_assoc] at h
  have hcs : ((L((f)^*[A])).commShiftIso (1 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj S.X₁) =
      ε.hom.app _ ≫ (((f)^*[A]).mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _ ≫
        (ε.inv.app _)⟦(1 : ℤ)⟧' :=
    Functor.CommShift.ofIso_commShiftIso_hom_app _ _ _ _
  rw [hcs]
  simp only [singleFunctorCompLeftDerivedUpperStarIso,
    Functor.singleFunctorCompLeftDerivedFunctorIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  have hε := ε.hom.naturality hS.singleδ
  rw [reassoc_of% hε]
  erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  simp only [ShiftedHom.map, Category.assoc] at h
  erw [h]
  rfl

end AlgebraicGeometry.Etale

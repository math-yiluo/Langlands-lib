/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityCoefficientPullMate
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift

/-! # The nonflat coefficient/pullback comparison commutes with shifts -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

/-- An inverse mate of a shift-compatible comparison is shift-compatible. -/
lemma purity_commShift_pushHomOfComapIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.CommShift ℤ] [R.CommShift ℤ] [L'.CommShift ℤ] [R'.CommShift ℤ]
    [G.CommShift ℤ] [H.CommShift ℤ]
    (adj : L ⊣ R) (adj' : L' ⊣ R') [adj.CommShift ℤ] [adj'.CommShift ℤ]
    (e : H ⋙ R' ≅ R ⋙ G) [e.hom.CommShift ℤ] :
    (pushHomOfComapIso adj adj' e).CommShift ℤ := by
  change ((Functor.leftUnitor (G ⋙ L')).inv ≫
    Functor.whiskerRight adj.unit (G ⋙ L') ≫
    (Functor.associator (L ⋙ R) G L').inv ≫
    Functor.whiskerRight (Functor.associator L R G).hom L' ≫
    Functor.whiskerRight (Functor.whiskerLeft L e.inv) L' ≫
    Functor.whiskerRight (Functor.associator L H R').inv L' ≫
    (Functor.associator (L ⋙ H) R' L').hom ≫
    Functor.whiskerLeft (L ⋙ H) adj'.counit ≫
    (Functor.rightUnitor (L ⋙ H)).hom).CommShift ℤ
  infer_instance

end CategoryTheory.Adjunction

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (g : X ⟶ Y)

instance purity_commShift_derivedComapLeftDerivedUpperStarIso_hom :
    (derivedComapLeftDerivedUpperStarIso a g).hom.CommShift ℤ := by
  have : NatTrans.CommShift ((g)^*⟦Λ⟧).leftDerivedFunctorIsoMapDerivedCategory.hom ℤ :=
    commShift_leftDerivedUpperStarIsoMapDerivedCategory_hom Λ g
  have : NatTrans.CommShift ((g)^*⟦Λ'⟧).leftDerivedFunctorIsoMapDerivedCategory.hom ℤ :=
    commShift_leftDerivedUpperStarIsoMapDerivedCategory_hom Λ' g
  dsimp only [derivedComapLeftDerivedUpperStarIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
    Functor.mapDerivedCategorySquareIso]
  infer_instance

/-- Shift compatibility of the actual nonflat comparison, by its mate characterization. -/
instance purity_commShift_derivedUpperStarExtendScalarsIso_hom :
    (derivedUpperStarExtendScalarsIso a g).hom.CommShift ℤ := by
  rw [derivedUpperStarExtendScalarsIso_hom_eq_mate]
  exact Adjunction.purity_commShift_pushHomOfComapIso _ _ _

end AlgebraicGeometry.ProEtale.CondensedRing

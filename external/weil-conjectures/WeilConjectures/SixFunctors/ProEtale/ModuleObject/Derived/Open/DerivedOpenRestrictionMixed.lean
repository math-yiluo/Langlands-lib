/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageOpenCoherenceData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate

set_option linter.privateModule false

/-! Source: blueprint composition isomorphism and its canonicity and associativity. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
private lemma derived_iso_trans
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ≅ G) (d : G ≅ H) :
    Functor.mapDerivedCategoryNatIso (e ≪≫ d) =
      Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryNatIso d :=
  Iso.ext (Functor.mapDerivedCategoryNatIso_trans e d)

private lemma derived_iso_symm
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    Functor.mapDerivedCategoryNatIso e.symm = (Functor.mapDerivedCategoryNatIso e).symm :=
  Iso.ext (Functor.mapDerivedCategoryNatIso_symm e)

private lemma derived_triangle_assoc
    {C₀ C₁ C₂ C₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₂ ⥤ C₃)
    (FG : C₀ ⥤ C₂) (GH : C₁ ⥤ C₃) (FGH : C₀ ⥤ C₃)
    [F.Additive] [G.Additive] [H.Additive]
    [FG.Additive] [GH.Additive] [FGH.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    [PreservesFiniteLimits GH] [PreservesFiniteColimits GH]
    [PreservesFiniteLimits FGH] [PreservesFiniteColimits FGH]
    (eFG : FG ≅ F ⋙ G) (eGH : GH ≅ G ⋙ H)
    (eF_GH : FGH ≅ F ⋙ GH) (eFG_H : FGH ≅ FG ⋙ H)
    (h : eF_GH ≪≫ Functor.isoWhiskerLeft F eGH =
      eFG_H ≪≫ Functor.isoWhiskerRight eFG H) :
    (Functor.mapDerivedCategoryTriangleIso eF_GH).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory
          (Functor.mapDerivedCategoryTriangleIso eGH).hom =
      (Functor.mapDerivedCategoryTriangleIso eFG_H).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryTriangleIso eFG).hom
          H.mapDerivedCategory := by
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom, Iso.symm_hom,
    Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Category.assoc]
  rw [← Category.assoc (Functor.mapDerivedCategoryCompIso F GH).inv,
    ← Functor.mapDerivedCategoryNatIso_isoWhiskerLeft,
    Category.assoc, ← Category.assoc (Functor.mapDerivedCategoryCompIso FG H).inv,
    ← Functor.mapDerivedCategoryNatIso_isoWhiskerRight]
  simp only [← Category.assoc]
  rw [← Functor.mapDerivedCategoryNatIso_trans, h,
    Functor.mapDerivedCategoryNatIso_trans]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_assoc]

namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

attribute [local irreducible] upperStar lowerStar
  Functor.mapDerivedCategory Functor.rightDerivedFunctor upperStarComp lowerStarComp
  upperStarLowerStarAdjunction Scheme.instCategory

private noncomputable def ordinaryComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    upperStar Λ fg ≅ upperStar Λ g ⋙ upperStar Λ f :=
  eqToIso (congrArg (upperStar Λ) hfg) ≪≫ upperStarComp Λ f g

private noncomputable def exactComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    (upperStar Λ fg).mapDerivedCategory ≅
      (upperStar Λ g).mapDerivedCategory ⋙ (upperStar Λ f).mapDerivedCategory :=
  Functor.mapDerivedCategoryTriangleIso (ordinaryComp Λ f g fg hfg)

private noncomputable def exactSquare {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {j : Y' ⟶ Y} {f' : X' ⟶ Y'} {i : X' ⟶ X}
    (sq : CommSq i f' f j) :
    (upperStar Λ f).mapDerivedCategory ⋙ (upperStar Λ i).mapDerivedCategory ≅
      (upperStar Λ j).mapDerivedCategory ⋙ (upperStar Λ f').mapDerivedCategory :=
  (exactComp Λ i f (i ≫ f) rfl).symm ≪≫ exactComp Λ f' j (i ≫ f) sq.w

end AlgebraicGeometry.ProEtale.CondensedRing

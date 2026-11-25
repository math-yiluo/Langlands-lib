/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateOfNatIsoLeft
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionMapDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStarCoherence

/-!
# The commutation of `Rν_*` with the pushforwards is the mate of the base change morphism

For a morphism of schemes `p : X ⟶ Y`, the isomorphism `Rp_* ⋙ Rν_* ≅ Rν_* ⋙ Rp_*`
(`ProEtale.rightDerivedLowerStarCompComparisonLowerStarIso`), defined through K-injective
resolutions, is the mate of the base change morphism `Rν_* ⋙ Lp^* ⟶ Lp^* ⋙ Rν_*`
(`ProEtale.rightDerivedComparisonBaseChange`) under the derived adjunctions `Lp^* ⊣ Rp_*`
(`ProEtale.mateEquiv_rightDerivedComparisonBaseChange`).

Both are obtained from the commutation `ν^* ⋙ p^*_{proét} ≅ p^*_{ét} ⋙ ν^*` of the left
adjoints: the base change morphism is its mate under `D(ν^*) ⊣ Rν_*`, so the mate of the base
change morphism is its conjugate under the composite adjunctions
(`CategoryTheory.conjugateEquiv_comp_eq_mateEquiv_mateEquiv`), and the composition isomorphisms
of right derived functors are conjugates of the induced isomorphisms of the derived left adjoints
(`CategoryTheory.Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv`).
-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]

/-- The isomorphism of total right derived functors induced by the identity is the identity. -/
@[simp]
lemma rightDerivedFunctorNatIso_refl (F : C ⥤ D) [F.Additive] :
    rightDerivedFunctorNatIso (Iso.refl F) = Iso.refl _ := by
  ext1
  apply F.rightDerivedFunctor.rightDerived_ext F.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ))
  simp [rightDerivedFunctorNatIso, rightDerivedFunctorNatTrans]

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- **The commutation of `Rν_*` with the pushforwards is the mate of the base change
morphism**: the isomorphism `Rp_* ⋙ Rν_* ≅ Rν_* ⋙ Rp_*` is the mate of the base change morphism
`Rν_* ⋙ Lp^* ⟶ Lp^* ⋙ Rν_*` under the derived adjunctions `Lp^* ⊣ Rp_*` on pro-étale and on
étale sheaves. -/
theorem mateEquiv_rightDerivedComparisonBaseChange {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (mateEquiv (ProEtale.derivedUpperStarLowerStarAdjunction A p)
        (Etale.derivedUpperStarLowerStarAdjunction A p)
        (rightDerivedComparisonBaseChange A p)) =
      (rightDerivedLowerStarCompComparisonLowerStarIso A p).hom := by
  let eP := ProEtale.leftDerivedUpperStarIsoMapDerivedCategory A p
  let eE := Etale.leftDerivedUpperStarIsoMapDerivedCategory A p
  let aνX := (comparisonAdjunction A X).mapDerivedCategoryRightDerivedAdjunction
  let aνY := (comparisonAdjunction A Y).mapDerivedCategoryRightDerivedAdjunction
  let aP := (ProEtale.upperStarLowerStarAdjunction A p).mapDerivedCategoryRightDerivedAdjunction
  let aE := (Etale.upperStarLowerStarAdjunction A p).mapDerivedCategoryRightDerivedAdjunction
  let aC := ((Etale.upperStarLowerStarAdjunction A p).comp
    (comparisonAdjunction A X)).mapDerivedCategoryRightDerivedAdjunction
  -- the commutation of the left adjoints, read on the functors induced on derived categories
  let β : (Etale.upperStar A p).mapDerivedCategory ⋙ ν^*(X)[A].mapDerivedCategory ⟶
      ν^*(Y)[A].mapDerivedCategory ⋙ (ProEtale.upperStar A p).mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso _ _).hom ≫
      (Functor.mapDerivedCategoryNatIso (comparisonUpperStarUpperStarIso A p)).inv ≫
      (Functor.mapDerivedCategoryCompIso _ _).inv
  have h₁ : (mateEquiv (ProEtale.derivedUpperStarLowerStarAdjunction A p)
      (Etale.derivedUpperStarLowerStarAdjunction A p)
      (rightDerivedComparisonBaseChange A p)) =
      (mateEquiv aP aE (mateEquiv aνY aνX β)) := by
    have hP : ProEtale.derivedUpperStarLowerStarAdjunction A p = aP.ofNatIsoLeft eP.symm :=
      Adjunction.derivedAdjunction_eq_ofNatIsoLeft _
    have hE : Etale.derivedUpperStarLowerStarAdjunction A p = aE.ofNatIsoLeft eE.symm :=
      Adjunction.derivedAdjunction_eq_ofNatIsoLeft _
    have hX : derivedComparisonAdjunction A X = aνX :=
      Adjunction.derivedAdjunction_ofNatIsoLeft _
    have hY : derivedComparisonAdjunction A Y = aνY :=
      Adjunction.derivedAdjunction_ofNatIsoLeft _
    rw [hP, hE, mateEquiv_ofNatIsoLeft, mateEquiv_ofNatIsoLeft_right,
      rightDerivedComparisonBaseChange, hX, hY]
    congr 2
    ext K
    simp [mateEquiv_apply, β, derivedComparisonUpperStarUpperStarIso, eP, eE]
  have h₂ : (rightDerivedLowerStarCompComparisonLowerStarIso A p).hom =
      conjugateEquiv (aνY.comp aP) (aE.comp aνX) β := by
    have he : (lowerStarCompComparisonLowerStarIso p A).hom =
        conjugateEquiv ((comparisonAdjunction A Y).comp (ProEtale.upperStarLowerStarAdjunction A p))
          ((Etale.upperStarLowerStarAdjunction A p).comp (comparisonAdjunction A X))
          (comparisonUpperStarUpperStarIso A p).symm.hom := by
      rw [lowerStarCompComparisonLowerStarIso_eq]
      exact (congrArg Iso.inv ((conjugateIsoEquiv _ _).apply_symm_apply
        (lowerStarComparisonLowerStarIso A p).symm)).symm
    have hc := Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
      (ProEtale.upperStarLowerStarAdjunction A p) (comparisonAdjunction A Y)
      ((Etale.upperStarLowerStarAdjunction A p).comp (comparisonAdjunction A X))
      (lowerStarCompComparisonLowerStarIso p A) (comparisonUpperStarUpperStarIso A p).symm he
    have hr := Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
      (comparisonAdjunction A X) (Etale.upperStarLowerStarAdjunction A p)
      ((Etale.upperStarLowerStarAdjunction A p).comp (comparisonAdjunction A X))
      (Iso.refl _) (Iso.refl _) (by simp)
    have hr' : (Functor.rightDerivedFunctorCompIso ν_*(X)[A] (Etale.lowerStar A p)).hom =
        conjugateEquiv aC (aE.comp aνX)
          (Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
            (Functor.mapDerivedCategoryCompIso _ _).symm).inv := by
      have h : Functor.rightDerivedFunctorCompIso ν_*(X)[A] (Etale.lowerStar A p) =
          (Functor.rightDerivedFunctorCompIso' ν_*(X)[A] (Etale.lowerStar A p)
            (Iso.refl _)).symm := by
        simp [Functor.rightDerivedFunctorCompIso']
      rw [h, Iso.symm_hom]
      refine Iso.inv_ext ?_
      rw [hr, conjugateEquiv_comp, Iso.inv_hom_id, conjugateEquiv_id]
    rw [rightDerivedLowerStarCompComparisonLowerStarIso, Iso.trans_hom, hc, hr',
      conjugateEquiv_comp]
    congr 1
    simp only [β, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Category.assoc]
    rw [← Functor.mapDerivedCategoryNatIso_symm, Iso.refl_symm,
      Functor.mapDerivedCategoryNatIso_refl,
      Category.id_comp, Functor.mapDerivedCategoryNatIso_symm]
  rw [h₁, h₂, ← conjugateEquiv_comp_eq_mateEquiv_mateEquiv]

end AlgebraicGeometry.ProEtale

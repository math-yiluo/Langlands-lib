/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeOpenImmersionSheaf

/-!
# Restriction of scalars and the derived base change of the extension by zero

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings. For a cartesian square
`g' ≫ j = j' ≫ g''` of schemes with `j`, `j'` open immersions, the derived base change
isomorphism `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekBaseChangeIso :
Lg'^* ⋙ Dj'_! ≅ Dj_! ⋙ Lg''^*` is compatible with the coefficient comparisons
`AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso` and
`AlgebraicGeometry.Etale.derivedRestrictScalarsCompOpenImmersionLowerShriekIso`
(`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekBaseChangeIso_hom_app_restrictScalars`).

All these isomorphisms are induced by exact functors, so the statement is deduced from its
underived counterpart
`AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChangeMap_app_restrictScalars` by two
abstract lemmas: the passage to derived categories through `Functor.mapDerivedCategorySquareIso`
(`AlgebraicGeometry.Etale.mapDerivedCategorySquareIso_hom_app_comp_of_comm`), and the
replacement of the functors `D(g^*)` by the derived pullbacks `Lg^*`
(`AlgebraicGeometry.Etale.pasteTwoSquaresIso_hom_app_comp_map_of_comm_of_iso`).

This is used for the compatible systems of Frobenius coefficient morphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section DerivedPasting

variable {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Type*} [Category A₀] [Category A₁] [Category A₂]
  [Category A₃] [Category B₀] [Category B₁] [Category B₂] [Category B₃] [Abelian A₀] [Abelian A₁]
  [Abelian A₂] [Abelian A₃] [Abelian B₀] [Abelian B₁] [Abelian B₂] [Abelian B₃]
  [HasDerivedCategory A₀] [HasDerivedCategory A₁] [HasDerivedCategory A₂] [HasDerivedCategory A₃]
  [HasDerivedCategory B₀] [HasDerivedCategory B₁] [HasDerivedCategory B₂] [HasDerivedCategory B₃]
  {r₀ : A₀ ⥤ B₀} {r₁ : A₁ ⥤ B₁} {r₂ : A₂ ⥤ B₂} {r₃ : A₃ ⥤ B₃}
  {P : A₀ ⥤ A₁} {Q : A₁ ⥤ A₃} {S : A₀ ⥤ A₂} {T : A₂ ⥤ A₃}
  {p : B₀ ⥤ B₁} {q : B₁ ⥤ B₃} {s : B₀ ⥤ B₂} {t : B₂ ⥤ B₃}
  [r₀.Additive] [PreservesFiniteLimits r₀] [PreservesFiniteColimits r₀]
  [r₁.Additive] [PreservesFiniteLimits r₁] [PreservesFiniteColimits r₁]
  [r₂.Additive] [PreservesFiniteLimits r₂] [PreservesFiniteColimits r₂]
  [r₃.Additive] [PreservesFiniteLimits r₃] [PreservesFiniteColimits r₃]
  [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [p.Additive] [PreservesFiniteLimits p] [PreservesFiniteColimits p]
  [q.Additive] [PreservesFiniteLimits q] [PreservesFiniteColimits q]
  [s.Additive] [PreservesFiniteLimits s] [PreservesFiniteColimits s]
  [t.Additive] [PreservesFiniteLimits t] [PreservesFiniteColimits t]

/-- The isomorphisms `Functor.mapDerivedCategorySquareIso` induced on derived categories by
squares of exact functors preserve the compatibility of a square isomorphism
`β : P ⋙ Q ≅ S ⋙ T` with `b : p ⋙ q ≅ s ⋙ t` along the comparisons `αP`, `αQ`, `αS`, `αT`. -/
lemma mapDerivedCategorySquareIso_hom_app_comp_of_comm (αP : r₀ ⋙ p ≅ P ⋙ r₁)
    (αQ : r₁ ⋙ q ≅ Q ⋙ r₃) (αS : r₀ ⋙ s ≅ S ⋙ r₂) (αT : r₂ ⋙ t ≅ T ⋙ r₃)
    (β : P ⋙ Q ≅ S ⋙ T) (b : p ⋙ q ≅ s ⋙ t)
    (h : ∀ X, q.map (αP.hom.app X) ≫ αQ.hom.app (P.obj X) ≫ r₃.map (β.hom.app X) =
      b.hom.app (r₀.obj X) ≫ t.map (αS.hom.app X) ≫ αT.hom.app (S.obj X))
    (K : DerivedCategory A₀) :
    q.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso αP).hom.app K) ≫
        (Functor.mapDerivedCategorySquareIso αQ).hom.app (P.mapDerivedCategory.obj K) ≫
        r₃.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso β).hom.app K) =
      (Functor.mapDerivedCategorySquareIso b).hom.app (r₀.mapDerivedCategory.obj K) ≫
        t.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso αS).hom.app K) ≫
        (Functor.mapDerivedCategorySquareIso αT).hom.app (S.mapDerivedCategory.obj K) := by
  have hE (X : A₀) : (Functor.isoWhiskerLeft r₀ b ≪≫ pasteTwoSquaresIso αS αT).hom.app X =
      b.hom.app (r₀.obj X) ≫ t.map (αS.hom.app X) ≫ αT.hom.app (S.obj X) := by
    simp [pasteTwoSquaresIso_hom_app]
  have h₁ := Functor.mapDerivedCategorySquareIso_hom_app_comp αP αQ
    (Functor.isoWhiskerLeft r₀ b ≪≫ pasteTwoSquaresIso αS αT) (Iso.refl (p ⋙ q)) β.symm
    (fun X ↦ by
      rw [hE, ← h X]
      simp [← Functor.map_comp]) K
  have h₂ := Functor.mapDerivedCategorySquareIso_hom_app_comp αS αT
    (Functor.isoWhiskerLeft r₀ b ≪≫ pasteTwoSquaresIso αS αT) b (Iso.refl (S ⋙ T))
    (fun X ↦ by
      rw [hE]
      simp) K
  have e₁ : (Functor.mapDerivedCategoryTriangleIso (Iso.refl (p ⋙ q))).hom.app
      (r₀.mapDerivedCategory.obj K) =
      (Functor.mapDerivedCategoryCompIso p q).inv.app (r₀.mapDerivedCategory.obj K) := by
    simp [Functor.mapDerivedCategoryNatIso_refl]
  have e₂ : (Functor.mapDerivedCategorySquareIso b).hom.app (r₀.mapDerivedCategory.obj K) =
      (Functor.mapDerivedCategoryCompIso p q).hom.app (r₀.mapDerivedCategory.obj K) ≫
        (Functor.mapDerivedCategoryTriangleIso b).hom.app (r₀.mapDerivedCategory.obj K) := by
    simp
  have e₃ : (Functor.mapDerivedCategoryTriangleIso β.symm).hom.app K ≫
      (Functor.mapDerivedCategorySquareIso β).hom.app K =
      (Functor.mapDerivedCategoryTriangleIso (Iso.refl (S ⋙ T))).hom.app K := by
    simp [Functor.mapDerivedCategoryNatIso_symm, Functor.mapDerivedCategoryNatIso_refl]
  rw [e₁] at h₁
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso p q).inv.app (r₀.mapDerivedCategory.obj K)),
    e₂, Category.assoc, Iso.inv_hom_id_app_assoc, ← h₂, ← reassoc_of% h₁, ← Functor.map_comp,
    e₃]

end DerivedPasting


section Conjugation

variable {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*} [Category C₀] [Category C₁] [Category C₂]
  [Category C₃] [Category D₀] [Category D₁] [Category D₂] [Category D₃]
  {R₀ : C₀ ⥤ D₀} {R₁ : C₁ ⥤ D₁} {R₂ : C₂ ⥤ D₂} {R₃ : C₃ ⥤ D₃}
  {Lp Dp : C₀ ⥤ C₁} {Q : C₁ ⥤ C₃} {S : C₀ ⥤ C₂} {Lt Dt : C₂ ⥤ C₃}
  {lp dp : D₀ ⥤ D₁} {q : D₁ ⥤ D₃} {s : D₀ ⥤ D₂} {lt dt : D₂ ⥤ D₃}

/-- The compatibility of a square isomorphism `m : Dp ⋙ Q ≅ S ⋙ Dt` with `ml : dp ⋙ q ≅ s ⋙ dt`
along comparisons `σP`, `σQ`, `σS`, `σT` is preserved when the horizontal functors are replaced
by isomorphic ones, `φ : Lp ≅ Dp`, `φl : lp ≅ dp`, `ψ : Lt ≅ Dt` and `ψl : lt ≅ dt`, and all
isomorphisms are conjugated accordingly. -/
lemma pasteTwoSquaresIso_hom_app_comp_map_of_comm_of_iso (φ : Lp ≅ Dp) (φl : lp ≅ dp)
    (ψ : Lt ≅ Dt) (ψl : lt ≅ dt) (σP : R₀ ⋙ dp ≅ Dp ⋙ R₁) (σQ : R₁ ⋙ q ≅ Q ⋙ R₃)
    (σS : R₀ ⋙ s ≅ S ⋙ R₂) (σT : R₂ ⋙ dt ≅ Dt ⋙ R₃) (m : Dp ⋙ Q ≅ S ⋙ Dt)
    (ml : dp ⋙ q ≅ s ⋙ dt)
    (h : ∀ K, q.map (σP.hom.app K) ≫ σQ.hom.app (Dp.obj K) ≫ R₃.map (m.hom.app K) =
      ml.hom.app (R₀.obj K) ≫ dt.map (σS.hom.app K) ≫ σT.hom.app (S.obj K)) (K : C₀) :
    (pasteTwoSquaresIso (Functor.isoWhiskerLeft R₀ φl ≪≫ σP ≪≫ Functor.isoWhiskerRight φ.symm R₁)
        σQ).hom.app K ≫
      R₃.map ((Functor.isoWhiskerRight φ Q ≪≫ m ≪≫ Functor.isoWhiskerLeft S ψ.symm).hom.app K) =
    (Functor.isoWhiskerRight φl q ≪≫ ml ≪≫ Functor.isoWhiskerLeft s ψl.symm).hom.app (R₀.obj K) ≫
      (pasteTwoSquaresIso σS
        (Functor.isoWhiskerLeft R₂ ψl ≪≫ σT ≪≫ Functor.isoWhiskerRight ψ.symm R₃)).hom.app K := by
  have n₁ := σQ.hom.naturality (φ.inv.app K)
  have n₂ := ψl.inv.naturality (σS.hom.app K)
  simp only [Functor.comp_map] at n₁ n₂
  simp only [pasteTwoSquaresIso_hom_app, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% n₁, ← reassoc_of% n₂]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Iso.inv_hom_id_app_assoc, Functor.comp_obj]
  simp only [Functor.map_comp, CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc]
  rw [reassoc_of% (h K)]

end Conjugation


variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

/-- **Restriction of scalars and derived base change for the extension by zero**: for a
cartesian square `g' ≫ j = j' ≫ g''` of schemes with `j`, `j'` open immersions, the base change
isomorphism `Lg'^* ⋙ Dj'_! ≅ Dj_! ⋙ Lg''^*` is compatible with the coefficient comparisons
`AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso` and
`AlgebraicGeometry.Etale.derivedRestrictScalarsCompOpenImmersionLowerShriekIso`. This is an input
of the compatible systems of Frobenius coefficient morphisms. -/
lemma derivedOpenImmersionLowerShriekBaseChangeIso_hom_app_restrictScalars
    {U' U X' X : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {g'' : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j'] (hsq : IsPullback g' j' j g'')
    (K : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (pasteTwoSquaresIso (leftDerivedUpperStarRestrictScalarsIso ρ g')
        (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j')).hom.app K ≫
      (Sheaf.derivedRestrictScalars X'.smallEtaleTopology ρ).map
        ((derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ') hsq).hom.app K) =
    (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) hsq).hom.app
        ((Sheaf.derivedRestrictScalars U.smallEtaleTopology ρ).obj K) ≫
      (pasteTwoSquaresIso (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j)
        (leftDerivedUpperStarRestrictScalarsIso ρ g'')).hom.app K :=
  pasteTwoSquaresIso_hom_app_comp_map_of_comm_of_iso
    (leftDerivedUpperStarIsoMapDerivedCategory _ g')
    (leftDerivedUpperStarIsoMapDerivedCategory _ g')
    (leftDerivedUpperStarIsoMapDerivedCategory _ g'')
    (leftDerivedUpperStarIsoMapDerivedCategory _ g'')
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ g'))
    (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j')
    (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j)
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ g''))
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso _ hsq)
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso _ hsq)
    (mapDerivedCategorySquareIso_hom_app_comp_of_comm _ _ _ _ _ _
      (openImmersionLowerShriekBaseChangeMap_app_restrictScalars ρ hsq.toCommSq)) K

end AlgebraicGeometry.Etale

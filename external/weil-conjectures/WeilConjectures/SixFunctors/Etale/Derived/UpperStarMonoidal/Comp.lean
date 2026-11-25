/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp

/-!
# The composition isomorphism of derived pullbacks is monoidal

For `g₁ : T ⟶ S` and `g₂ : S ⟶ R`, the composition isomorphism
`L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` (`AlgebraicGeometry.Etale.leftDerivedUpperStarComp`) is
compatible with the tensor comparisons `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison`).

## Main results

- `AlgebraicGeometry.Etale.leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit`: on the image
  of a complex, the composition isomorphism is the composition isomorphism of the underived
  pullbacks, read through the counits of the derived pullbacks.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_comp`: the composition
  isomorphism commutes with the tensor comparisons.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

open _root_.DerivedCategory

variable {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R) (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂)

/-- On the image `Qh X` of a complex, the composition isomorphism
`L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` is the composition isomorphism `(g₁ ≫ g₂)^* ≅ g₂^* ⋙ g₁^*` of the
underived pullbacks, through the counits of the derived pullbacks:
```
  L(g₁ ≫ g₂)^*(Qh X) ──────────────▶ Lg₁^* Lg₂^* (Qh X)
          │ counit                        │ Lg₁^* counit ≫ counit
          ▼                               ▼
  Qh((g₁ ≫ g₂)^* X) ───────────────▶ Qh(g₁^* g₂^* X)
```
-/
@[reassoc]
lemma leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit
    (X : HomotopyCategory (Sheaf R.smallEtaleTopology A) (.up ℤ)) :
    (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app (Qh.obj X) ≫
        L((g₁)^*[A]).map ((g₂)^*[A].leftDerivedFunctorCounit.app X) ≫
        (g₁)^*[A].leftDerivedFunctorCounit.app (((g₂)^*[A].mapHomotopyCategory (.up ℤ)).obj X) =
      (g₁₂)^*[A].leftDerivedFunctorCounit.app X ≫
        Qh.map (Functor.mapHomotopyCategoryCompHom (g₂)^*[A] (g₁)^*[A] (g₁₂)^*[A]
          (upperStarComp A g₁ g₂ g₁₂ hg) X) := by
  have hfac (F : Sheaf R.smallEtaleTopology A ⥤ Sheaf T.smallEtaleTopology A) [F.Additive]
      [PreservesFiniteLimits F] [PreservesFiniteColimits F]
      (Y : HomotopyCategory (Sheaf R.smallEtaleTopology A) (.up ℤ)) :
      F.leftDerivedFunctorIsoMapDerivedCategory.hom.app (Qh.obj Y) ≫
        F.mapDerivedCategoryFactorsh.hom.app Y = F.leftDerivedFunctorCounit.app Y :=
    NatTrans.congr_app F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac Y
  have hfac₂ (Y : HomotopyCategory (Sheaf R.smallEtaleTopology A) (.up ℤ)) :
      (g₂)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app (Qh.obj Y) ≫
        (g₂)^*[A].mapDerivedCategoryFactorsh.hom.app Y =
          (g₂)^*[A].leftDerivedFunctorCounit.app Y :=
    NatTrans.congr_app (g₂)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac Y
  have hfac₁ (Y : HomotopyCategory (Sheaf S.smallEtaleTopology A) (.up ℤ)) :
      (g₁)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app (Qh.obj Y) ≫
        (g₁)^*[A].mapDerivedCategoryFactorsh.hom.app Y =
          (g₁)^*[A].leftDerivedFunctorCounit.app Y :=
    NatTrans.congr_app (g₁)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac Y
  have hnat := (g₁)^*[A].leftDerivedFunctorIsoMapDerivedCategory.inv.naturality
    ((g₂)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app (Qh.obj X) ≫
      (g₂)^*[A].mapDerivedCategoryFactorsh.hom.app X)
  have hcomp := Functor.mapDerivedCategoryCompIso_fach (g₂)^*[A] (g₁)^*[A] X
  have hnatiso := Functor.mapDerivedCategoryNatIso_fach (upperStarComp A g₁ g₂ g₁₂ hg) X
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← hfac₂, ← hfac₁, ← hfac, ← reassoc_of% hnat, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  simp only [Functor.mapHomotopyCategoryCompHom, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hnatiso, ← hcomp]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The inverse form of `leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit`. -/
@[reassoc]
lemma leftDerivedUpperStarComp_inv_app_Qh_obj_comp_counit
    (X : HomotopyCategory (Sheaf R.smallEtaleTopology A) (.up ℤ)) :
    (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).inv.app (Qh.obj X) ≫
        (g₁₂)^*[A].leftDerivedFunctorCounit.app X ≫
        Qh.map (Functor.mapHomotopyCategoryCompHom (g₂)^*[A] (g₁)^*[A] (g₁₂)^*[A]
          (upperStarComp A g₁ g₂ g₁₂ hg) X) =
      L((g₁)^*[A]).map ((g₂)^*[A].leftDerivedFunctorCounit.app X) ≫
        (g₁)^*[A].leftDerivedFunctorCounit.app (((g₂)^*[A].mapHomotopyCategory (.up ℤ)).obj X) := by
  rw [← leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit, Iso.inv_hom_id_app_assoc]

open Functor.LaxMonoidal Functor.OplaxMonoidal

/-- The naturality of the counit of `Lg^*`, with the composite functors unfolded. -/
@[reassoc]
lemma counit_naturality {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    {P Q : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ)} (f : P ⟶ Q) :
    L((g)^*[A]).map (Qh.map f) ≫ (g)^*[A].leftDerivedFunctorCounit.app Q =
      (g)^*[A].leftDerivedFunctorCounit.app P ≫
        Qh.map (((g)^*[A].mapHomotopyCategory (.up ℤ)).map f) :=
  (g)^*[A].leftDerivedFunctorCounit.naturality f


variable [(g₁)^*[A].PreservesFlat] [(g₂)^*[A].PreservesFlat] [(g₁₂)^*[A].PreservesFlat]

/-- The comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M` is natural in both variables. -/
@[reassoc]
lemma leftDerivedUpperStarTensorComparison_naturality {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    [(g)^*[A].PreservesFlat] {K K' M M' : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (f : K ⟶ K') (f' : M ⟶ M') :
    ((leftDerivedUpperStarTensorComparison A g).app K).app M ≫
        (L((g)^*[A]).map f ⊗ₘ L((g)^*[A]).map f') =
      L((g)^*[A]).map (f ⊗ₘ f') ≫ ((leftDerivedUpperStarTensorComparison A g).app K').app M' := by
  have h₁ := NatTrans.congr_app ((leftDerivedUpperStarTensorComparison A g).naturality f) M
  have h₂ := ((leftDerivedUpperStarTensorComparison A g).app K').naturality f'
  dsimp [derivedTensor] at h₁ h₂
  rw [tensorHom_def, tensorHom_def, Functor.map_comp, Category.assoc, ← reassoc_of% h₁, ← h₂]

-- One rewriting step unifies two instance paths to the tensor product of the homotopy category.
/-- The pointwise form of `leftDerivedUpperStarTensorComparison_comp` on images of complexes,
composed with the counit of the derived tensor bifunctor. -/
lemma leftDerivedUpperStarTensorComparison_comp_aux
    (X Y : HomotopyCategory (Sheaf R.smallEtaleTopology A) (.up ℤ)) :
    ((leftDerivedUpperStarTensorComparison A g₁₂).app (Qh.obj X)).app (Qh.obj Y) ≫
        ((g₁₂)^*[A].leftDerivedFunctorCounit.app X ⊗ₘ
          (g₁₂)^*[A].leftDerivedFunctorCounit.app Y) ≫
          μ Qh (((g₁₂)^*[A].mapHomotopyCategory (.up ℤ)).obj X)
            (((g₁₂)^*[A].mapHomotopyCategory (.up ℤ)).obj Y) =
      ((leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app (Qh.obj X ⊗ Qh.obj Y) ≫
        L((g₁)^*[A]).map (((leftDerivedUpperStarTensorComparison A g₂).app (Qh.obj X)).app
          (Qh.obj Y)) ≫
        ((leftDerivedUpperStarTensorComparison A g₁).app _).app _ ≫
        ((leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).inv.app (Qh.obj X) ⊗ₘ
          (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).inv.app (Qh.obj Y))) ≫
        ((g₁₂)^*[A].leftDerivedFunctorCounit.app X ⊗ₘ
          (g₁₂)^*[A].leftDerivedFunctorCounit.app Y) ≫
          μ Qh (((g₁₂)^*[A].mapHomotopyCategory (.up ℤ)).obj X)
            (((g₁₂)^*[A].mapHomotopyCategory (.up ℤ)).obj Y) := by
  have he (P Q : Sheaf R.smallEtaleTopology A) :
      δ (g₁₂)^*[A] P Q ≫ ((upperStarComp A g₁ g₂ g₁₂ hg).hom.app P ⊗ₘ
        (upperStarComp A g₁ g₂ g₁₂ hg).hom.app Q) =
      (upperStarComp A g₁ g₂ g₁₂ hg).hom.app (P ⊗ Q) ≫ (g₁)^*[A].map (δ (g₂)^*[A] P Q) ≫
        δ (g₁)^*[A] _ _ :=
    Etale.upperStarComp_hom_app_tensor_comp_δ A g₁ g₂ g₁₂ hg P Q
  have hE := Functor.mapHomotopyCategory_δ_comp_tensorHom he X Y
  rw [← cancel_mono (Qh.map (Functor.mapHomotopyCategoryCompHom (g₂)^*[A] (g₁)^*[A] (g₁₂)^*[A]
    (upperStarComp A g₁ g₂ g₁₂ hg) X ⊗ₘ Functor.mapHomotopyCategoryCompHom (g₂)^*[A] (g₁)^*[A]
      (g₁₂)^*[A] (upperStarComp A g₁ g₂ g₁₂ hg) Y))]
  -- the left hand side
  have hL := leftDerivedUpperStarTensorComparison_app_app_comp A g₁₂ X Y
  simp only [Category.assoc] at hL ⊢
  rw [reassoc_of% hL, ← Qh.map_comp, hE, Qh.map_comp,
    ← leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit_assoc A g₁ g₂ g₁₂ hg]
  -- the right hand side
  rw [← μ_natural, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc]
  rw [leftDerivedUpperStarComp_inv_app_Qh_obj_comp_counit,
    leftDerivedUpperStarComp_inv_app_Qh_obj_comp_counit, ← tensorHom_comp_tensorHom_assoc,
    leftDerivedUpperStarTensorComparison_naturality_assoc]
  have h₁ := leftDerivedUpperStarTensorComparison_app_app_comp A g₁
    (((g₂)^*[A].mapHomotopyCategory (.up ℤ)).obj X) (((g₂)^*[A].mapHomotopyCategory (.up ℤ)).obj Y)
  erw [h₁]
  have h₂ := L((g₁)^*[A]).congr_map (leftDerivedUpperStarTensorComparison_app_app_comp A g₂ X Y)
  simp only [Functor.map_comp] at h₂
  erw [reassoc_of% h₂]
  have hε := counit_naturality A g₁ (δ ((g₂)^*[A].mapHomotopyCategory (.up ℤ)) X Y)
  rw [reassoc_of% hε]
  have hc := (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.naturality (μ Qh X Y)
  dsimp only [Functor.comp_map] at hc
  rw [reassoc_of% hc, Functor.map_comp]

attribute [local instance] isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
  isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor

/-- The composite `L(g₁ ≫ g₂)^*(K ⊗ᴸ M) ≅ Lg₁^*Lg₂^*(K ⊗ᴸ M) ⟶ Lg₁^*(Lg₂^*K ⊗ᴸ Lg₂^*M) ⟶
Lg₁^*Lg₂^*K ⊗ᴸ Lg₁^*Lg₂^*M ≅ L(g₁ ≫ g₂)^*K ⊗ᴸ L(g₁ ≫ g₂)^*M` of the tensor comparisons of `Lg₂^*`
and `Lg₁^*`, read through the composition isomorphism. It is the tensor comparison of
`L(g₁ ≫ g₂)^*` (`leftDerivedUpperStarTensorComparison_eq_comp`). -/
noncomputable def leftDerivedUpperStarTensorComparisonComp :
    leftDerivedUpperStarDerivedTensor A g₁₂ ⟶ derivedTensorLeftDerivedUpperStar A g₁₂ :=
  (Functor.postcompose₂.map (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom).app (-⊗ᴸ-(R)[A]) ≫
    (Functor.postcompose₂.obj L((g₁)^*[A])).map (leftDerivedUpperStarTensorComparison A g₂) ≫
    (((Functor.whiskeringLeft₂ _).obj L((g₂)^*[A])).obj L((g₂)^*[A])).map
      (leftDerivedUpperStarTensorComparison A g₁) ≫
    (((Functor.whiskeringLeft₂ _).map (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).inv).app
      (L((g₂)^*[A]) ⋙ L((g₁)^*[A]))).app (-⊗ᴸ-(T)[A]) ≫
    (((Functor.whiskeringLeft₂ _).obj L((g₁₂)^*[A])).map
      (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).inv).app
      (-⊗ᴸ-(T)[A])

omit [(g₁₂)^*[A].PreservesFlat] in
lemma leftDerivedUpperStarTensorComparisonComp_app_app
    (K M : DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    ((leftDerivedUpperStarTensorComparisonComp A g₁ g₂ g₁₂ hg).app K).app M =
      (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app (K ⊗ M) ≫
        L((g₁)^*[A]).map (((leftDerivedUpperStarTensorComparison A g₂).app K).app M) ≫
        ((leftDerivedUpperStarTensorComparison A g₁).app _).app _ ≫
        ((leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).inv.app K ⊗ₘ
          (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).inv.app M) := by
  rw [tensorHom_def]
  rfl

/-- The tensor comparison of `L(g₁ ≫ g₂)^*` is that of `Lg₂^*` followed by that of `Lg₁^*`, read
through the composition isomorphism. -/
lemma leftDerivedUpperStarTensorComparison_eq_comp :
    leftDerivedUpperStarTensorComparison A g₁₂ =
      leftDerivedUpperStarTensorComparisonComp A g₁ g₂ g₁₂ hg := by
  refine Functor.leftDerived₂_ext _ (derivedTensorLeftDerivedUpperStarCounit A g₁₂)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _ ?_
  ext X Y
  have e₁ : ((derivedTensorLeftDerivedUpperStarCounit A g₁₂).app X).app Y =
      ((g₁₂)^*[A].leftDerivedFunctorCounit.app X ⊗ₘ (g₁₂)^*[A].leftDerivedFunctorCounit.app Y) ≫
        μ Qh (((g₁₂)^*[A].mapHomotopyCategory (.up ℤ)).obj X)
          (((g₁₂)^*[A].mapHomotopyCategory (.up ℤ)).obj Y) := by
    rw [tensorHom_def]
    dsimp [derivedTensorLeftDerivedUpperStarCounit, derivedTensor]
    rw [Category.assoc]
    rfl
  have := leftDerivedUpperStarTensorComparison_comp_aux A g₁ g₂ g₁₂ hg X Y
  rw [← leftDerivedUpperStarTensorComparisonComp_app_app] at this
  simp only [NatTrans.comp_app]
  rw [e₁]
  exact this

/-- **The composition isomorphism `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` is monoidal**: it commutes with
the tensor comparisons,
```
  L(g₁ ≫ g₂)^*(K ⊗ᴸ M) ──────────────────▶ L(g₁ ≫ g₂)^*K ⊗ᴸ L(g₁ ≫ g₂)^*M
          │                                           │
          ▼                                           ▼
  Lg₁^*Lg₂^*(K ⊗ᴸ M) ──▶ Lg₁^*(Lg₂^*K ⊗ᴸ Lg₂^*M) ──▶ Lg₁^*Lg₂^*K ⊗ᴸ Lg₁^*Lg₂^*M
```
-/
@[reassoc]
lemma leftDerivedUpperStarTensorComparison_comp
    (K M : DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    ((leftDerivedUpperStarTensorComparison A g₁₂).app K).app M ≫
        ((leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app K ⊗ₘ
          (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app M) =
      (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app (K ⊗ M) ≫
        L((g₁)^*[A]).map (((leftDerivedUpperStarTensorComparison A g₂).app K).app M) ≫
        ((leftDerivedUpperStarTensorComparison A g₁).app _).app _ := by
  rw [leftDerivedUpperStarTensorComparison_eq_comp A g₁ g₂ g₁₂ hg,
    leftDerivedUpperStarTensorComparisonComp_app_app]
  simp only [Category.assoc, tensorHom_comp_tensorHom, Iso.inv_hom_id_app]
  erw [id_tensorHom_id, Category.comp_id]

end Etale

end AlgebraicGeometry

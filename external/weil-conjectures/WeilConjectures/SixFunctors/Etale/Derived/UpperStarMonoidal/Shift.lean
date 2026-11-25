/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
import Mathlib.CategoryTheory.Sites.Point.IsMonoidalW

/-!
# The tensor comparison of the derived pullback commutes with shifts

For `g : Z ⟶ Y`, the comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison`) commutes with the shifts in
each variable.
-/

@[expose] public section

-- `GrothendieckTopology.W.monoidal` gives the monoidality of `W` directly; the instance going
-- through enough points of the site is tried first and makes the search time out.
attribute [-instance]
  CategoryTheory.instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

open _root_.DerivedCategory

/-- The counit `Qh ⋙ Lg^* ⟶ g^* ⋙ Qh` of the derived pullback commutes with the shifts. -/
instance commShift_leftDerivedFunctorCounit_upperStar :
    NatTrans.CommShift (g)^*[A].leftDerivedFunctorCounit ℤ := by
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).hom ℤ :=
    inferInstanceAs
      (NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.inv ℤ)
  rw [← (g)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  exact inferInstanceAs (NatTrans.CommShift (Functor.whiskerLeft Qh
    (leftDerivedUpperStarIsoMapDerivedCategory A g).hom ≫ _) ℤ)

section

variable [(g)^*[A].PreservesFlat]


/-- The tensor comparison `Lg^*(K ⊗ᴸ -) ⟶ Lg^*K ⊗ᴸ Lg^*(-)` for a fixed `K`. -/
noncomputable abbrev leftDerivedUpperStarTensorComparisonApp
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (-⊗ᴸ-(Y)[A]).obj K ⋙ L((g)^*[A]) ⟶ L((g)^*[A]) ⋙ (-⊗ᴸ-(Z)[A]).obj (L((g)^*[A]).obj K) :=
  (leftDerivedUpperStarTensorComparison A g).app K

lemma commShift_leftDerivedUpperStarTensorComparisonApp_of_iso
    {K K' : DerivedCategory (Sheaf Y.smallEtaleTopology A)} (e : K ≅ K')
    [NatTrans.CommShift (leftDerivedUpperStarTensorComparisonApp A g K') ℤ] :
    NatTrans.CommShift (leftDerivedUpperStarTensorComparisonApp A g K) ℤ := by
  have eq : leftDerivedUpperStarTensorComparisonApp A g K =
      Functor.whiskerRight ((-⊗ᴸ-(Y)[A]).map e.hom) L((g)^*[A]) ≫
        leftDerivedUpperStarTensorComparisonApp A g K' ≫
        Functor.whiskerLeft L((g)^*[A]) ((-⊗ᴸ-(Z)[A]).map (L((g)^*[A]).map e.inv)) := by
    have := (leftDerivedUpperStarTensorComparison A g).naturality e.hom
    ext M
    have := congr_app this M
    dsimp at this ⊢
    rw [reassoc_of% this, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp,
      e.hom_inv_id]
    simp
  have : NatTrans.CommShift ((-⊗ᴸ-(Y)[A]).map e.hom) ℤ :=
    inferInstanceAs (NatTrans.CommShift ((curriedTensor _).map e.hom) ℤ)
  have : NatTrans.CommShift ((-⊗ᴸ-(Z)[A]).map (L((g)^*[A]).map e.inv)) ℤ :=
    inferInstanceAs (NatTrans.CommShift ((curriedTensor _).map (L((g)^*[A]).map e.inv)) ℤ)
  rw [eq]
  infer_instance

attribute [local instance] isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
  isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor

lemma leftDerivedUpperStarTensorComparison_eq :
    leftDerivedUpperStarTensorComparison A g =
      Functor.leftDerived₂NatTrans _ (derivedTensorLeftDerivedUpperStarCounit A g)
        (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
        (leftDerivedUpperStarDerivedTensorCounit A g)
        (Functor.postcompose₂MapWhiskeringLeft₂
          (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh) :=
  rfl

/-- The defining property of the tensor comparison of `Lg^*`, on objects of the homotopy
category. -/
@[reassoc]
lemma leftDerivedUpperStarTensorComparison_app_app_fac
    (X M : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ)) :
    ((leftDerivedUpperStarTensorComparison A g).app (Qh.obj X)).app (Qh.obj M) ≫
        ((derivedTensorLeftDerivedUpperStarCounit A g).app X).app M =
      ((leftDerivedUpperStarDerivedTensorCounit A g).app X).app M ≫
        ((Functor.postcompose₂MapWhiskeringLeft₂
          (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh).app X).app
            M := by
  rw [leftDerivedUpperStarTensorComparison_eq]
  exact Functor.leftDerived₂NatTrans_app_app _ (derivedTensorLeftDerivedUpperStarCounit A g)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (leftDerivedUpperStarDerivedTensorCounit A g)
    (Functor.postcompose₂MapWhiskeringLeft₂
      (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh) X M

lemma commShift_leftDerivedUpperStarTensorComparisonApp_Qh_obj
    (X : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ))
    (hX : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat X) (hgX : kFlatUpperStar A g X) :
    NatTrans.CommShift (leftDerivedUpperStarTensorComparisonApp A g (Qh.obj X)) ℤ :=
  DerivedCategory.commShift_of_tensorLeft_fac (g)^*[A] L((g)^*[A])
    (g)^*[A].leftDerivedFunctorCounit X hX hgX _ (fun M ↦ by
      have := leftDerivedUpperStarTensorComparison_app_app_fac A g X M
      simp only [Functor.postcompose₂_obj_obj_obj_obj, Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
        curriedTensor_obj_obj, derivedTensorLeftDerivedUpperStarCounit, NatTrans.comp_app,
        Functor.comp_obj, Functor.whiskeringLeft₂_map_app_app_app_app,
        Functor.whiskeringLeft₂_obj_map_app_app_app, Functor.whiskeringLeft₂_obj_obj_map_app_app,
        Functor.LaxMonoidal.μNatTrans_app_app, leftDerivedUpperStarDerivedTensorCounit,
        Functor.postcompose₂_obj_map_app_app, Functor.postcompose₂_map_app_app_app,
        Functor.postcompose₂MapWhiskeringLeft₂_app_app, Category.assoc] at this ⊢
      exact this)

/-- For a fixed `K`, the tensor comparison `Lg^*(K ⊗ᴸ -) ⟶ Lg^*K ⊗ᴸ Lg^*(-)` commutes with
the shifts. -/
instance commShift_leftDerivedUpperStarTensorComparisonApp
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    NatTrans.CommShift (leftDerivedUpperStarTensorComparisonApp A g K) ℤ := by
  let Λ := (inferInstance : HasFunctorialFlatResolution (Sheaf Y.smallEtaleTopology A)).some.reduced
  let K₀ := DerivedCategory.Q.objPreimage K
  let R := Λ.resolutionFunctor.obj K₀
  have hR := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K₀
  have hgR := kFlatUpperStar_quotient_obj_resolutionFunctor_obj A g Λ K₀
  have := commShift_leftDerivedUpperStarTensorComparisonApp_Qh_obj A g
    ((HomotopyCategory.quotient _ _).obj R) ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hR) hgR
  let e : K ≅ Qh.obj ((HomotopyCategory.quotient _ _).obj R) :=
    (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      (asIso (DerivedCategory.Q.map (Λ.resolutionNatTrans.app K₀))).symm ≪≫
      (DerivedCategory.quotientCompQhIso _).symm.app R
  exact commShift_leftDerivedUpperStarTensorComparisonApp_of_iso A g e

/-- The tensor comparison `Lg^*(- ⊗ᴸ M) ⟶ Lg^*(-) ⊗ᴸ Lg^*M` for a fixed `M`. -/
noncomputable abbrev leftDerivedUpperStarTensorComparisonFlipApp
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (-⊗ᴸ-(Y)[A]).flip.obj M ⋙ L((g)^*[A]) ⟶
      L((g)^*[A]) ⋙ (-⊗ᴸ-(Z)[A]).flip.obj (L((g)^*[A]).obj M) :=
  (leftDerivedUpperStarTensorComparison A g).flipApp M

lemma commShift_leftDerivedUpperStarTensorComparisonFlipApp_of_iso
    {M M' : DerivedCategory (Sheaf Y.smallEtaleTopology A)} (e : M ≅ M')
    [NatTrans.CommShift (leftDerivedUpperStarTensorComparisonFlipApp A g M') ℤ] :
    NatTrans.CommShift (leftDerivedUpperStarTensorComparisonFlipApp A g M) ℤ := by
  have eq : leftDerivedUpperStarTensorComparisonFlipApp A g M =
      Functor.whiskerRight ((-⊗ᴸ-(Y)[A]).flip.map e.hom) L((g)^*[A]) ≫
        leftDerivedUpperStarTensorComparisonFlipApp A g M' ≫
        Functor.whiskerLeft L((g)^*[A]) ((-⊗ᴸ-(Z)[A]).flip.map (L((g)^*[A]).map e.inv)) := by
    ext K
    have := ((leftDerivedUpperStarTensorComparison A g).app K).naturality e.hom
    dsimp at this ⊢
    rw [reassoc_of% this, ← Functor.map_comp, ← Functor.map_comp, e.hom_inv_id]
    simp
  have : NatTrans.CommShift ((-⊗ᴸ-(Y)[A]).flip.map e.hom) ℤ :=
    inferInstanceAs (NatTrans.CommShift ((curriedTensor _).flip.map e.hom) ℤ)
  have : NatTrans.CommShift ((-⊗ᴸ-(Z)[A]).flip.map (L((g)^*[A]).map e.inv)) ℤ :=
    inferInstanceAs (NatTrans.CommShift ((curriedTensor _).flip.map (L((g)^*[A]).map e.inv)) ℤ)
  rw [eq]
  infer_instance

lemma commShift_leftDerivedUpperStarTensorComparisonFlipApp_Qh_obj
    (X : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ))
    (hX : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat X) (hgX : kFlatUpperStar A g X) :
    NatTrans.CommShift (leftDerivedUpperStarTensorComparisonFlipApp A g (Qh.obj X)) ℤ :=
  DerivedCategory.commShift_of_tensorRight_fac (g)^*[A] L((g)^*[A])
    (g)^*[A].leftDerivedFunctorCounit X hX hgX _ (fun M ↦ by
      have := leftDerivedUpperStarTensorComparison_app_app_fac A g M X
      simp only [Functor.postcompose₂_obj_obj_obj_obj, Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
        curriedTensor_obj_obj, derivedTensorLeftDerivedUpperStarCounit, NatTrans.comp_app,
        Functor.comp_obj, Functor.whiskeringLeft₂_map_app_app_app_app,
        Functor.whiskeringLeft₂_obj_map_app_app_app, Functor.whiskeringLeft₂_obj_obj_map_app_app,
        Functor.LaxMonoidal.μNatTrans_app_app, leftDerivedUpperStarDerivedTensorCounit,
        Functor.postcompose₂_obj_map_app_app, Functor.postcompose₂_map_app_app_app,
        Functor.postcompose₂MapWhiskeringLeft₂_app_app, Category.assoc, Functor.flip_obj_obj,
        flipFunctor_map_app_app] at this ⊢
      exact this)

/-- For a fixed `M`, the tensor comparison `Lg^*(- ⊗ᴸ M) ⟶ Lg^*(-) ⊗ᴸ Lg^*M` commutes with
the shifts. -/
instance commShift_leftDerivedUpperStarTensorComparisonFlipApp
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    NatTrans.CommShift (leftDerivedUpperStarTensorComparisonFlipApp A g M) ℤ := by
  let Λ := (inferInstance : HasFunctorialFlatResolution (Sheaf Y.smallEtaleTopology A)).some.reduced
  let M₀ := DerivedCategory.Q.objPreimage M
  let R := Λ.resolutionFunctor.obj M₀
  have hR := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le M₀
  have hgR := kFlatUpperStar_quotient_obj_resolutionFunctor_obj A g Λ M₀
  have := commShift_leftDerivedUpperStarTensorComparisonFlipApp_Qh_obj A g
    ((HomotopyCategory.quotient _ _).obj R) ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hR) hgR
  let e : M ≅ Qh.obj ((HomotopyCategory.quotient _ _).obj R) :=
    (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
      (asIso (DerivedCategory.Q.map (Λ.resolutionNatTrans.app M₀))).symm ≪≫
      (DerivedCategory.quotientCompQhIso _).symm.app R
  exact commShift_leftDerivedUpperStarTensorComparisonFlipApp_of_iso A g e

/-- The compatibility of the tensor comparison of `Lh^*` with a shift of the second factor,
in the form needed for pairings of Weil objects: if `Q : A₁ ⊗ᴸ B ⟶ M` intertwines the data
`ψ_{A₁} ⊗ ψ_B` and `ψ_M`, then `A₁ ⊗ᴸ B[n] ≅ (A₁ ⊗ᴸ B)[n] ⟶ M[n]` intertwines the shifted
data. -/
lemma leftDerivedUpperStarTensorIso_shift_right_comm (h : Y ⟶ Y) [(h)^*[A].PreservesFlat]
    {A₁ B M : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (ψA : L((h)^*[A]).obj A₁ ⟶ A₁) (ψB : L((h)^*[A]).obj B ⟶ B) (ψM : L((h)^*[A]).obj M ⟶ M)
    (Q : ((-⊗ᴸ-(Y)[A]).obj A₁).obj B ⟶ M)
    (hQ : L((h)^*[A]).map Q ≫ ψM = ((leftDerivedUpperStarTensorIso A h A₁ B).hom ≫
      ((-⊗ᴸ-(Y)[A]).map ψA).app _ ≫ ((-⊗ᴸ-(Y)[A]).obj A₁).map ψB) ≫ Q) (n : ℤ) :
    L((h)^*[A]).map ((((-⊗ᴸ-(Y)[A]).obj A₁).commShiftIso n).hom.app B ≫ Q⟦n⟧') ≫
        (L((h)^*[A]).commShiftIso n).hom.app M ≫ ψM⟦n⟧' =
      ((leftDerivedUpperStarTensorIso A h A₁ (B⟦n⟧)).hom ≫
        ((-⊗ᴸ-(Y)[A]).map ψA).app _ ≫
        ((-⊗ᴸ-(Y)[A]).obj A₁).map ((L((h)^*[A]).commShiftIso n).hom.app B ≫ ψB⟦n⟧')) ≫
        (((-⊗ᴸ-(Y)[A]).obj A₁).commShiftIso n).hom.app B ≫ Q⟦n⟧' := by
  have h₁ : L((h)^*[A]).map ((((-⊗ᴸ-(Y)[A]).obj A₁).commShiftIso n).hom.app B) ≫
      (L((h)^*[A]).commShiftIso n).hom.app _ ≫ (leftDerivedUpperStarTensorIso A h A₁ B).hom⟦n⟧' =
      (leftDerivedUpperStarTensorIso A h A₁ (B⟦n⟧)).hom ≫
        ((-⊗ᴸ-(Y)[A]).obj (L((h)^*[A]).obj A₁)).map ((L((h)^*[A]).commShiftIso n).hom.app B) ≫
        (((-⊗ᴸ-(Y)[A]).obj (L((h)^*[A]).obj A₁)).commShiftIso n).hom.app _ := by
    have := NatTrans.shift_app_comm (leftDerivedUpperStarTensorComparisonApp A h A₁) n B
    rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app] at this
    simp only [Category.assoc] at this
    exact this
  simp only [Category.assoc] at hQ
  have : NatTrans.CommShift ((-⊗ᴸ-(Y)[A]).map ψA) ℤ :=
    inferInstanceAs (NatTrans.CommShift ((curriedTensor _).map ψA) ℤ)
  have h₂ := NatTrans.shift_app_comm ((-⊗ᴸ-(Y)[A]).map ψA) n (L((h)^*[A]).obj B)
  have h₃ := (((-⊗ᴸ-(Y)[A]).obj A₁).commShiftIso n).hom.naturality ψB
  dsimp at h₂ h₃
  rw [Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality_assoc,
    ← Functor.map_comp, hQ]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₁, ← NatTrans.naturality_assoc, reassoc_of% h₃]
  dsimp only [Functor.comp_obj]
  rw [← reassoc_of% h₂]

end

end Etale

end AlgebraicGeometry

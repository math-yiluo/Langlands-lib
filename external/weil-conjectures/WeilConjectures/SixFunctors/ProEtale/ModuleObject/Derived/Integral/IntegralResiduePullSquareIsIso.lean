/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullSquareData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullFlatModel
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-! # Invertibility from a flat-resolution computation -/

@[expose] public section

universe u v

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance instEssentiallySmallProfinite_integralResiduePullSquareIsIso
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
private theorem exists_flat_colimit_model
    {C : Type*} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] (L : CochainComplex C ℤ) :
    ∃ (P : CochainComplex C ℤ) (π : P ⟶ L), QuasiIso π ∧
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P ∧
      ObjectProperty.flat.cochainComplexMinus.colimitsOfShape ℤ P := by
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ C))).reduced
  have hι : (ObjectProperty.flat.ι : _ ⥤ C).essImage ≤ ObjectProperty.flat := by
    rintro M ⟨N, ⟨e⟩⟩
    exact ObjectProperty.prop_of_iso _ e N.property
  exact ⟨_, Λ.resolutionNatTrans.app L, inferInstance,
    Λ.kFlat_resolutionFunctor_obj hι L,
    (Λ.colimitOfShapeFlatResolutionFunctorObj hι L).colimitsOfShape⟩

namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The inverse mate is invertible, by computation on flat K-flat resolutions.
Source: Bhatt--Scholze, Remark 6.8.15.
(blueprint: new-integral-residue-derived-pull-square-isIso)

Proof. Choose a flat K-flat representative for the input complex. The flat-model
identity expresses the canonical pull mate, followed by two invertible counits,
as the composite of two invertible counits with the localized ordinary pull
isomorphism. Cancel the invertible counits. Naturality transports invertibility
from the chosen representative to the original complex. -/
theorem integralResidue_pullSquare_isIso :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsIso (residueExchangePullHom ℓ E f) := by
  intro X Y f
  have hp (K : residueExchangeDerived (integralCoeff ℓ E) Y) :
      IsIso ((residueExchangePullHom ℓ E f).app K) := by
    obtain ⟨P, π, hπ, hP, hcolim⟩ :=
      exists_flat_colimit_model (DerivedCategory.Q.objPreimage K)
    let H := (HomotopyCategory.quotient _ (.up ℤ)).obj P
    let eP : DerivedCategory.Qh.obj H ≅ K :=
      (DerivedCategory.quotientCompQhIso _).app P ≪≫
        asIso (DerivedCategory.Q.map π) ≪≫ DerivedCategory.Q.objObjPreimageIso K
    obtain ⟨hX, heq⟩ := residueExchangePull_flatModel ℓ E f P hP hcolim
    have hY : IsIso ((residueExchangeReductionCounit ℓ E Y).app H) := by
      unfold residueExchangeReductionCounit
      dsimp only [H, id_eq]
      unfold residueExchangeReduction integralReduction
      exact (Mod.extendScalars
        (coefficientMap (integralReductionMap ℓ E) Y))
        |>.isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
    have hU (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        [MonObj Λ] [IsCommMonObj Λ] : IsIso (residueExchangeUpperStarCounit Λ f) := by
      unfold residueExchangeUpperStarCounit residueExchangeUpperStar
      dsimp only [id_eq]
      infer_instance
    have hOrd : IsIso (NatTrans.mapHomotopyCategory
        (pullIso (integralReductionMap ℓ E) f).hom (.up ℤ)) := by
      let e := pullIso (integralReductionMap ℓ E) f
      let eH : _ ≅ _ :=
        { hom := NatTrans.mapHomotopyCategory e.hom (.up ℤ)
          inv := NatTrans.mapHomotopyCategory e.inv (.up ℤ)
          hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp
          inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp }
      exact eH.isIso_hom
    have hL : IsIso ((residueExchangeReduction ℓ E X).map
        ((residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app H) ≫
      (residueExchangeReductionCounit ℓ E X).app
        ((((f)^*⟦integralCoeff ℓ E⟧).mapHomotopyCategory (.up ℤ)).obj H) ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
        (pullIso (integralReductionMap ℓ E) f).hom (.up ℤ)).app H)) := by
      have := hU (integralCoeff ℓ E)
      infer_instance
    have hR : IsIso ((residueExchangePullHom ℓ E f).app (DerivedCategory.Qh.obj H) ≫
      (residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
          ((residueExchangeReductionCounit ℓ E Y).app H) ≫
      (residueExchangeUpperStarCounit
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app
          (((Mod.extendScalars
            (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
              (.up ℤ)).obj H)) := by
      rw [← heq]
      exact hL
    have := hU (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E))
    have hTail : IsIso ((residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
          ((residueExchangeReductionCounit ℓ E Y).app H) ≫
      (residueExchangeUpperStarCounit
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app
          (((Mod.extendScalars
            (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
              (.up ℤ)).obj H)) := by infer_instance
    have : IsIso ((residueExchangePullHom ℓ E f).app (DerivedCategory.Qh.obj H)) :=
      IsIso.of_isIso_comp_right _ ((residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
          ((residueExchangeReductionCounit ℓ E Y).app H) ≫
      (residueExchangeUpperStarCounit
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app
          (((Mod.extendScalars
            (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
                (.up ℤ)).obj H))
    have hn := (residueExchangePullHom ℓ E f).naturality eP.hom
    have : IsIso (((residueExchangeUpperStar (integralCoeff ℓ E) f ⋙
        residueExchangeReduction ℓ E X).map eP.hom) ≫
          (residueExchangePullHom ℓ E f).app K) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((residueExchangeUpperStar (integralCoeff ℓ E) f ⋙
        residueExchangeReduction ℓ E X).map eP.hom) _
  exact NatIso.isIso_of_isIso_app (residueExchangePullHom ℓ E f)

end AlgebraicGeometry.ProEtale.CondensedRing

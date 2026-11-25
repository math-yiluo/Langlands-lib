/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullSquareData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullOrdinaryUnit
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.IntegralResiduePullFlatModelMateNormalized

/-! The counit-normalized mate calculation for the integral residue pull square.

Source: Bhatt--Scholze, Remark 6.8.15.
(blueprint: new-integral-residue-pull-flat-model-comparison-mate-normalized)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory
open CategoryTheory.Functor
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance instEssentiallySmallProfinite_integralIntegralResiduePullFlatModelMateNormalized
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

-- Private counit and mate calculations retained from the former flat-model proof.
section ProofCalculations
open CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section CachedInstances
variable (T : AlgebraicGeometry.Scheme.{u})
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
local notation "M" => Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab)
  (AlgebraicGeometry.ProEtale.condensedRingObj Λ T)
@[instance_reducible]
private noncomputable def cachedProofInstance1 : MonoidalCategory M := inferInstance
end CachedInstances
attribute [local instance]
  cachedProofInstance1 cachedProofInstance2 cachedProofInstance3 cachedProofInstance4
  cachedProofInstance5 cachedProofInstance6 cachedProofInstance7 cachedProofInstance8
  cachedProofInstance9 cachedProofInstance10 cachedProofInstance11 cachedProofInstance12

private theorem exactSquareFac
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    [Limits.PreservesFiniteLimits I] [Limits.PreservesFiniteColimits I]
    (e : F ⋙ G ≅ H ⋙ I) (N : HomotopyCategory A (.up ℤ)) :
    (mapDerivedCategoryCompIso F G ≪≫ mapDerivedCategoryNatIso e ≪≫
      (mapDerivedCategoryCompIso H I).symm).hom.app (DerivedCategory.Qh.obj N) ≫
        I.mapDerivedCategory.map (H.mapDerivedCategoryFactorsh.hom.app N) ≫
        I.mapDerivedCategoryFactorsh.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj N) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app N) ≫
        G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj N) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app N) := by
  have hF := mapDerivedCategoryCompIso_fach F G N
  have hH := mapDerivedCategoryCompIso_fach H I N
  rw [mapHomotopyCategoryCompIso_refl_hom_app] at hF hH
  erw [DerivedCategory.Qh.map_id, Category.comp_id] at hF hH
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [hH, mapDerivedCategoryNatIso_fach, ← hF]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem exactSquareFacInv
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : H ⋙ I ≅ F ⋙ G) (N : HomotopyCategory A (.up ℤ)) :
    (mapDerivedCategoryCompIso F G ≪≫ (mapDerivedCategoryNatIso e).symm ≪≫
      (mapDerivedCategoryCompIso H I).symm).hom.app (DerivedCategory.Qh.obj N) ≫
        I.mapDerivedCategory.map (H.mapDerivedCategoryFactorsh.hom.app N) ≫
        I.mapDerivedCategoryFactorsh.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj N) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app N) ≫
        G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj N) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app N) := by
  have h := exactSquareFac F G H I e.symm N
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    mapDerivedCategoryNatIso_symm] using h

private theorem liftedSquareFac
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (G G' : B ⥤ D) (H H' : A ⥤ C) (I : C ⥤ D)
    (eG : G' ≅ G) (eH : H' ≅ H) (q : F ⋙ G ≅ H ⋙ I)
    {N : A} {B₀ : B} {C₀ : C} {D₀ D₁ : D}
    (x : F.obj N ⟶ B₀) (u : G.obj B₀ ⟶ D₀)
    (v : H.obj N ⟶ C₀) (r : I.obj C₀ ⟶ D₁) (o : D₀ ⟶ D₁)
    (u' : G'.obj B₀ ⟶ D₀) (v' : H'.obj N ⟶ C₀)
    (hu : eG.hom.app B₀ ≫ u = u') (hv : eH.hom.app N ≫ v = v')
    (hq : q.hom.app N ≫ I.map v ≫ r = G.map x ≫ u ≫ o) :
    (isoWhiskerLeft F eG ≪≫ q ≪≫ isoWhiskerRight eH.symm I).hom.app N ≫
      I.map v' ≫ r =
      G'.map x ≫ u' ≫ o := by
  rw [← hu, ← hv]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    Functor.map_comp, Category.assoc]
  rw [← I.map_comp_assoc, Iso.inv_hom_id_app, I.map_id, Category.id_comp, hq]
  rw [← eG.hom.naturality_assoc]


private theorem transportedUnitFac
    {A B : Type*} [Category A] [Category B]
    {L : A ⥤ B} {R S : B ⥤ A} (ad : L ⊣ R) (e : R ≅ S)
    {X Z : A} {Y : B} (a : L.obj X ⟶ Y) (s : S.obj Y ≅ Z)
    (u : X ⟶ Z) (v : Z ⟶ R.obj Y)
    (hu : ad.unit.app X ≫ R.map a = u ≫ v)
    (hv : v ≫ e.hom.app Y = s.inv) :
    (ad.ofNatIsoRight e).unit.app X ≫ S.map a ≫ s.hom = u := by
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app]
  rw [Category.assoc, ← e.hom.naturality_assoc, ← Category.assoc, hu]
  simp only [Category.assoc]
  rw [reassoc_of% hv, Iso.inv_hom_id, Category.comp_id]




namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

private theorem reduction_unit_fac (T : Scheme.{u})
    (H : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) T)) (.up ℤ)) :
    (residueExchangeReductionAdjunction ℓ E T).unit.app (DerivedCategory.Qh.obj H) ≫
      (residueExchangeRestriction ℓ E T).map
        ((residueExchangeReductionCounit ℓ E T).app H) ≫
      (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategoryFactorsh.hom.app
          (((Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) T)).mapHomotopyCategory
            (.up ℤ)).obj H) =
      DerivedCategory.Qh.map
        (((Mod.extendRestrictAdjunction
          (coefficientMap (integralReductionMap ℓ E) T)).mapHomotopyCategory
            (.up ℤ)).unit.app H) := by
  unfold residueExchangeReductionAdjunction residueExchangeReductionCounit
    residueExchangeRestriction residueExchangeReduction integralReduction
  dsimp only [id_eq]
  exact mixedDerivedUnitFac
    (Mod.extendRestrictAdjunction (coefficientMap (integralReductionMap ℓ E) T)) H

/-- Exact restriction/pullback compatibility with the localization counits.
Source: Bhatt--Scholze, Remark 6.8.15.
(blueprint: new-integral-residue-restrict-pull-counit-factorization)
-/
theorem restrict_pull_fac {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) Y))
      (.up ℤ)) :
    (residueExchangeRestrictPullIso ℓ E f).hom.app (DerivedCategory.Qh.obj N) ≫
      (residueExchangeRestriction ℓ E X).map
        ((residueExchangeUpperStarCounit
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app N) ≫
      (Mod.comap (coefficientMap (integralReductionMap ℓ E) X)).mapDerivedCategoryFactorsh.hom.app
        ((((f)^*⟦Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)⟧).mapHomotopyCategory
          (.up ℤ)).obj N) =
      (residueExchangeUpperStar (integralCoeff ℓ E) f).map
        ((Mod.comap
          (coefficientMap (integralReductionMap ℓ E) Y)).mapDerivedCategoryFactorsh.hom.app N) ≫
        (residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app
          (((Mod.comap (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
            (.up ℤ)).obj N) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory
            (comapUpperStarIso (integralReductionMap ℓ E) f).inv (.up ℤ)).app N) := by
  unfold residueExchangeRestrictPullIso residueExchangeUpperStarCounit
    residueExchangeRestriction residueExchangeUpperStar
    leftDerivedUpperStarIsoMapDerivedCategory
  dsimp only [id_eq]
  have h := exactLeftSquareFac
    (Mod.comap (coefficientMap (integralReductionMap ℓ E) Y))
    ((f)^*⟦integralCoeff ℓ E⟧)
    ((f)^*⟦Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)⟧)
    (Mod.comap (coefficientMap (integralReductionMap ℓ E) X))
    (comapUpperStarIso (integralReductionMap ℓ E) f) N
  simpa only [derivedComapUpperStarIso, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.trans_assoc] using h

end AlgebraicGeometry.ProEtale.CondensedRing
end ProofCalculations

namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
-- The four concrete derived module functors occur in a single mate calculation.
/-- Compatibility of the scalar mate with the derived reduction and pullback counits.
Source: Bhatt--Scholze, Remark 6.8.15.
(blueprint: new-integral-residue-scalar-mate-counit)
-/
theorem scalar_mate_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    (residueExchangeReduction ℓ E X).map
        ((residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app P) ≫
      (residueExchangeReductionCounit ℓ E X).app
          ((((f)^*⟦integralCoeff ℓ E⟧).mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory
          (pullIso (integralReductionMap ℓ E) f).hom (.up ℤ)).app P) =
    (residueExchangePullHom ℓ E f).app (DerivedCategory.Qh.obj P) ≫
      (residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
          ((residueExchangeReductionCounit ℓ E Y).app P) ≫
      ((residueExchangeUpperStarCounit
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app
          (((Mod.extendScalars
            (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
              (.up ℤ)).obj P)) := by
  let F := (f)^*⟦integralCoeff ℓ E⟧
  let G := (f)^*⟦Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)⟧
  let TY := Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) Y)
  let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (integralReductionMap ℓ E) X)
  let SY := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (coefficientMap (integralReductionMap ℓ E) Y)
  let FP := (F.mapHomotopyCategory (.up ℤ)).obj P
  let TP := (TY.mapHomotopyCategory (.up ℤ)).obj P
  let ph := (NatTrans.mapHomotopyCategory
    (pullIso (integralReductionMap ℓ E) f).hom (.up ℤ)).app P
  let qh := (NatTrans.mapHomotopyCategory
    (comapUpperStarIso (integralReductionMap ℓ E) f).inv (.up ℤ)).app TP
  let ηX := ((Mod.extendRestrictAdjunction
    (coefficientMap (integralReductionMap ℓ E) X)).mapHomotopyCategory (.up ℤ)).unit.app FP
  let ηY := ((Mod.extendRestrictAdjunction
    (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory (.up ℤ)).unit.app P
  have hOrd := naturalOrdinaryFac
    (residueExchangeUpperStarCounit (integralCoeff ℓ E) f) ηY ηX
    ((SX.mapHomotopyCategory (.up ℤ)).map ph) qh
    (residueExchangePull_ordinary_unit ℓ E f P)
  have ho := SX.mapDerivedCategoryFactorsh.hom.naturality ph
  dsimp only [Functor.comp_map] at ho
  have hm := mateModel
    (residueExchangeReductionAdjunction ℓ E X)
    (residueExchangeReductionAdjunction ℓ E Y)
    (residueExchangeUpperStar (integralCoeff ℓ E) f)
    (residueExchangeUpperStar
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f)
    (residueExchangeRestrictPullIso ℓ E f).hom
    ((residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app P)
    ((residueExchangeReductionCounit ℓ E X).app FP)
    (DerivedCategory.Qh.map ph)
    ((residueExchangeReductionCounit ℓ E Y).app P)
    ((residueExchangeUpperStarCounit
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app TP)
    (SX.mapDerivedCategoryFactorsh.hom.app _)
    (SX.mapDerivedCategoryFactorsh.hom.app _)
    (SY.mapDerivedCategoryFactorsh.hom.app TP)
    ((residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app _)
    (DerivedCategory.Qh.map qh)
    (DerivedCategory.Qh.map ηX) (DerivedCategory.Qh.map ηY)
    (DerivedCategory.Qh.map ((SX.mapHomotopyCategory (.up ℤ)).map ph))
    (reduction_unit_fac ℓ E X FP) (reduction_unit_fac ℓ E Y P)
    ho (restrict_pull_fac ℓ E f TP) hOrd
  unfold residueExchangePullHom
  exact hm

/-- After cancellation of the exact residue pullback counit, the derived mate
calculation is the scalar-adjunction square. The proof expands the two derived
counits, transposes along `residueExchangeReductionAdjunction`, and applies
`residueExchangePull_ordinary_unit`; naturality of the localization counits
then gives the displayed normalized equation.
(blueprint: new-integral-residue-pull-flat-model-comparison-mate-normalized)
-/
theorem residueExchangePull_flatModel_mate_normalized
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ))
    (hC : IsIso ((residueExchangeUpperStarCounit
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app
      (((Mod.extendScalars
        (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
          (.up ℤ)).obj H))) :
    ((residueExchangeReduction ℓ E X).map
        ((residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app H) ≫
      (residueExchangeReductionCounit ℓ E X).app
        ((((f)^*⟦integralCoeff ℓ E⟧).mapHomotopyCategory (.up ℤ)).obj H) ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory
          (pullIso (integralReductionMap ℓ E) f).hom (.up ℤ)).app H)) ≫
      inv ((residueExchangeUpperStarCounit
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app
        (((Mod.extendScalars
          (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
            (.up ℤ)).obj H)) =
    (residueExchangePullHom ℓ E f).app (DerivedCategory.Qh.obj H) ≫
      (residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
        ((residueExchangeReductionCounit ℓ E Y).app H) := by
  let := hC
  let c := (residueExchangeUpperStarCounit
    (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app
    (((Mod.extendScalars
      (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
        (.up ℤ)).obj H)
  have hc : c ≫ inv c = 𝟙 _ := CategoryTheory.IsIso.hom_inv_id c
  have h := congrArg (fun z ↦ z ≫ inv c) (scalar_mate_counit ℓ E f H)
  simpa only [Category.assoc, c, hc, Functor.comp_obj, Category.comp_id] using h

end AlgebraicGeometry.ProEtale.CondensedRing

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientRestriction
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-! # Pullback comparison for the finite discrete coefficient realization -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local instance] coefficientProfiniteEssentiallySmall

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

variable
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))

/-- Conjugate restriction through the adjunctions to compare ordinary pullbacks.
Source: Bhatt--Scholze, Lemma 5.4.1 and the common sectionwise encoding
(blueprint: def-weil-pbc-canonical-finite-discrete-pullback).

Construction. Cancel the two encoding equivalences from the right restriction
comparison, then use conjugateIsoEquiv for the resulting composite adjunctions. -/
@[irreducible] noncomputable def finiteDiscreteCoefficientProEtalePullbackIso
    {S T : Scheme.{u}} (h : S ⟶ T) :
    ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h ⋙
        (finiteDiscreteCoefficientEquivalence B eR G hG S).functor ≅
      (finiteDiscreteCoefficientEquivalence B eR G hG T).functor ⋙
        upperStar (Profinite.continuousMapRingObj B) h := by
  let ES := finiteDiscreteCoefficientEquivalence B eR G hG S
  let ET := finiteDiscreteCoefficientEquivalence B eR G hG T
  let L := lowerStar (Profinite.continuousMapRingObj B) h
  let r := finiteDiscreteCoefficientRestrictionIso B eR G hG h
  let r' : L ⋙ ET.inverse ≅ ES.inverse ⋙
      ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h :=
    ((Functor.associator ES.functor L ET.inverse).symm ≪≫
      r.compInverseIso).isoInverseComp
  exact (conjugateIsoEquiv
    (ET.toAdjunction.comp (upperStarLowerStarAdjunction (Profinite.continuousMapRingObj B) h))
    ((ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).comp ES.toAdjunction)).symm r'

/-- The ordinary etale-to-internal-module pullback comparison before derivation.
(blueprint: def-weil-pbc-canonical-finite-discrete-pullback).
Compose the site inverse-image comparison with the internal coefficient comparison. -/
@[irreducible] noncomputable def finiteDiscreteCoefficientSheafPullbackIso
    {S T : Scheme.{u}} (h : S ⟶ T) :
    Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) S ⋙
          (finiteDiscreteCoefficientEquivalence B eR G hG S).functor) ≅
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) T ⋙
        (finiteDiscreteCoefficientEquivalence B eR G hG T).functor) ⋙
        upperStar (Profinite.continuousMapRingObj B) h :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (finiteDiscreteCoefficientProEtalePullbackIso B eR G hG h) ≪≫
    (Functor.associator _ _ _).symm

/-- Derive the canonical ordinary pullback comparison and restrict its source to D+.
Source: Bhatt--Scholze, Proposition 5.3.2 and Lemma 5.4.1
(blueprint: def-weil-pbc-canonical-finite-discrete-pullback).

Construction. Combine the two exact realization factors with mapDerivedCategoryCompIso.
Use mapDerivedCategoryPlusCompatibility to include the etale source in D. Derive the
ordinary comparison, separate the realization factors again, and replace the exact
internal pullback by its total left derived functor. Every isomorphism is specified. -/
@[irreducible] noncomputable def finiteDiscreteCoefficientPullbackIso
    : CoefficientPullbackFamily B (Profinite.continuousMapRingObj B)
      (fun T ↦ finiteDiscreteRealization B T
        (finiteDiscreteCoefficientEquivalence B eR G hG T)) := by
  intro S T h
  let ES := finiteDiscreteCoefficientEquivalence B eR G hG S
  let ET := finiteDiscreteCoefficientEquivalence B eR G hG T
  let A := ModuleCat.{u + 1} (ULift.{u + 1} B)
  let V (X : Scheme.{u}) := comparisonUpperStar A X
  let U := upperStar (Profinite.continuousMapRingObj B) h
  let t := finiteDiscreteCoefficientSheafPullbackIso B eR G hG h
  unfold finiteDiscreteRealization
  exact Functor.isoWhiskerLeft D+(Etale.upperStar A h)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerLeft DerivedCategory.Plus.ι
          (Functor.mapDerivedCategoryCompIso (V S) ES.functor)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Etale.upperStar A h).mapDerivedCategoryPlusCompatibility
      D(V S ⋙ ES.functor) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      (Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso t ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Functor.mapDerivedCategoryCompIso (V T) ET.functor).symm ≪≫
          Functor.associator _ _ _) D(U) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ D(V T) ⋙ D(ET.functor))
      (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.continuousMapRingObj B) h).symm

end AlgebraicGeometry.ProEtale.CondensedRing

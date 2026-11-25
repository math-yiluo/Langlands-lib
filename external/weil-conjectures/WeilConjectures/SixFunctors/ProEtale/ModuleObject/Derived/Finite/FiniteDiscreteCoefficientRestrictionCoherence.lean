/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientRestriction

/-! # Composition of the normalized coefficient restriction comparison -/

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

private theorem lowerStarComp_hom (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((lowerStarComp Λ f g).hom.app M).hom =
      (ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app M.X := by
  simp only [lowerStarComp, comapCondensedPushforwardHomComp]
  change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]
  rfl

private theorem restriction_hom {S T : Scheme.{u}} (h : S ⟶ T)
    (N : FiniteDiscreteProEtaleSheaves B S) :
    ((finiteDiscreteCoefficientRestrictionIso B eR G hG h).hom.app N).hom =
      (ProEtale.lowerStar Ab.{u + 1} h).map
        ((finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG S).hom.app N) ≫
      (finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG T).inv.app
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).obj N) := by
  unfold finiteDiscreteCoefficientRestrictionIso
  simp only [finiteDiscreteCoefficientRestrictionForgetIso]
  change 𝟙 _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ ≫ _ = _
  simp only [Category.id_comp]
  rfl

/-- The normalized restriction comparisons commute with restriction composition.
Source: Bhatt--Scholze, Lemma 5.4.1; naturality of the sectionwise encoding
(blueprint: lem-weil-pbc-finite-discrete-restriction-composition).

Proof. Forget module actions. Expand each normalized comparison as the restriction of
the encoding forget isomorphism followed by its inverse at the target. The middle
isomorphism and its inverse cancel after applying the second restriction. Move the
last inverse past the ordinary restriction composition map by naturality. On underlying
sheaves, internal restriction composition is the ordinary additive restriction
composition map. Its naturality at the first encoding component proves the equality.
Faithfulness of the internal-module forgetful functor finishes. -/
theorem finiteDiscreteCoefficientRestrictionIso_comp {S T U : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U)
    (N : FiniteDiscreteProEtaleSheaves B S) :
    (lowerStar (Profinite.continuousMapRingObj B) g).map
        ((finiteDiscreteCoefficientRestrictionIso B eR G hG f).hom.app N) ≫
      (finiteDiscreteCoefficientRestrictionIso B eR G hG g).hom.app
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).obj N) ≫
      (finiteDiscreteCoefficientEquivalence B eR G hG U).functor.map
        ((ProEtale.lowerStarComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) f g).hom.app N) =
    (lowerStarComp (Profinite.continuousMapRingObj B) f g).hom.app
        ((finiteDiscreteCoefficientEquivalence B eR G hG S).functor.obj N) ≫
      (finiteDiscreteCoefficientRestrictionIso B eR G hG (f ≫ g)).hom.app N := by
  apply (Mod.forget _).map_injective
  change (ProEtale.lowerStar Ab.{u + 1} g).map
      (((finiteDiscreteCoefficientRestrictionIso B eR G hG f).hom.app N).hom) ≫
    ((finiteDiscreteCoefficientRestrictionIso B eR G hG g).hom.app
      ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).obj N)).hom ≫
    ((finiteDiscreteCoefficientEquivalence B eR G hG U).functor.map
      ((ProEtale.lowerStarComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) f g).hom.app N)).hom =
    ((lowerStarComp (Profinite.continuousMapRingObj B) f g).hom.app
      ((finiteDiscreteCoefficientEquivalence B eR G hG S).functor.obj N)).hom ≫
    ((finiteDiscreteCoefficientRestrictionIso B eR G hG (f ≫ g)).hom.app N).hom
  rw [restriction_hom, restriction_hom, restriction_hom, lowerStarComp_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [← (ProEtale.lowerStar Ab.{u + 1} g).map_comp_assoc
    ((finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG T).inv.app
      ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).obj N))
    ((finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG T).hom.app
      ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).obj N)),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := (finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG U).inv.naturality
    ((ProEtale.lowerStarComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) f g).hom.app N)
  change _ ≫ _ = _ ≫
    ((finiteDiscreteCoefficientEquivalence B eR G hG U).functor.map
      ((ProEtale.lowerStarComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) f g).hom.app N)).hom at hn
  erw [← hn]
  have hcf :
      (sheafCompose (ProEt.topology U)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})).map
          ((ProEtale.lowerStarComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) f g).hom.app N) =
        (ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app
          ((sheafCompose (ProEt.topology S)
            (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})).obj N) := by
    rfl
  rw [hcf]
  have hnat := congrArg (fun k ↦ k ≫
        (finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG U).inv.app
          ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) (f ≫ g)).obj N))
        ((ProEtale.lowerStarComp Ab.{u + 1} f g).hom.naturality
          ((finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG S).hom.app N))
  simp only [Functor.comp_map, Category.assoc] at hnat
  convert hnat using 1
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing

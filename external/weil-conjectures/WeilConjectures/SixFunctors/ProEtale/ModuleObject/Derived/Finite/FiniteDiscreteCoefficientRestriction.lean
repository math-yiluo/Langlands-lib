/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientDerivedFunctorAPI
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement

/-! # Restriction comparison for the finite discrete coefficient realization -/

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

/-- The canonical additive comparison for restriction under the coefficient encoding. -/
noncomputable def finiteDiscreteCoefficientRestrictionForgetIso
    {S T : Scheme.{u}} (h : S ⟶ T) :
    (finiteDiscreteCoefficientEquivalence B eR G hG S).functor ⋙
        lowerStar (Profinite.continuousMapRingObj B) h ⋙ Mod.forget _ ≅
      ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h ⋙
        (finiteDiscreteCoefficientEquivalence B eR G hG T).functor ⋙ Mod.forget _ := by
  let E (X : Scheme.{u}) := finiteDiscreteCoefficientEquivalence B eR G hG X
  let U (X : Scheme.{u}) := sheafCompose (ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})
  let F := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h
  let H := ProEtale.lowerStar Ab.{u + 1} h
  let e : U S ⋙ H ≅ F ⋙ U T := Iso.refl _
  exact Functor.isoWhiskerLeft (E S).functor
      (eqToIso (lowerStar_comp_forget (Profinite.continuousMapRingObj B) h)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG S) H ≪≫
    e ≪≫ Functor.isoWhiskerLeft F
      (finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG T).symm

section ProofHelpers

private local instance (T : AlgebraicGeometry.Scheme.{u}) :
    ((AlgebraicGeometry.Scheme.ProEt.topology T).W (A := Ab.{u + 1})).IsMonoidal :=
  GrothendieckTopology.W.monoidal (J := AlgebraicGeometry.Scheme.ProEt.topology T)
    (A := Ab.{u + 1})

private local instance (T : AlgebraicGeometry.Scheme.{u}) :
    HasWeakSheafify (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1} :=
  HasSheafify.isRightAdjoint

private noncomputable local instance (T : AlgebraicGeometry.Scheme.{u}) :
    MonoidalCategory (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) :=
  Sheaf.monoidalCategory (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}

open CategoryTheory.ConstantInternalModuleSheafEncoding MonoidalCategory

private local instance : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} (ULift.{u + 1} B)) :=
  ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}

private noncomputable def encodingUnderlyingIso (T : Scheme.{u})
    (M : FiniteDiscreteInternalModules B T) :
    (sheafCompose (ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})).obj
      ((finiteDiscreteCoefficientEquivalence B eR G hG T).inverse.obj M) ≅ M.X := by
  unfold finiteDiscreteCoefficientEquivalence
  exact (sheafEncodingForgetIso (ProEt.topology T) (ULift.{u + 1} B) G hG).app
    ((Mod.comap (finiteDiscreteSchemeRingIso B T eR).hom).obj M)

attribute [local semireducible] finiteDiscreteCoefficientEquivalence

private theorem encodingUnderlyingIso_hom (T : Scheme.{u})
    (M : FiniteDiscreteInternalModules B T) :
    (encodingUnderlyingIso B eR G hG T M).hom.hom =
      (eqToIso (congrArg
        (fun P ↦ moduleLocalizationRight (ProEt.topology T)
          (A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B)) ⋙ P)
        (modulePresheafEncoding_forget (C := T.ProEt) (ULift.{u + 1} B) G hG))).hom.app
        ((Mod.comap (finiteDiscreteSchemeRingIso B T eR).hom).obj M) := by
  let U := sheafToPresheaf (ProEt.topology T) Ab.{u + 1}
  let ff := (Functor.FullyFaithful.ofFullyFaithful U).whiskeringRight
    (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      ((presheafToSheaf (ProEt.topology T) Ab.{u + 1}).obj
        (A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B))))
  let e := eqToIso (congrArg
    (fun P ↦ moduleLocalizationRight (ProEt.topology T)
      (A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B)) ⋙ P)
    (modulePresheafEncoding_forget (C := T.ProEt) (ULift.{u + 1} B) G hG))
  let H := sheafEncoding (ProEt.topology T) (ULift.{u + 1} B) G hG
  let W := sheafCompose (ProEt.topology T)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})
  exact congrArg (fun k ↦ k.app
    ((Mod.comap (finiteDiscreteSchemeRingIso B T eR).hom).obj M))
    (ff.map_preimage (X := H ⋙ W) (Y := Mod.forget _) e.hom)

private theorem encodingPushforward_underlying (T U : Scheme.{u}) (j : U ⟶ T)
    (M : FiniteDiscreteInternalModules B U) :
    (sheafCompose (ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})).map
      (encodingPushforwardIso B eR G hG T U j M).hom ≫
      (ProEtale.lowerStar Ab.{u + 1} j).map (encodingUnderlyingIso B eR G hG U M).hom =
    (encodingUnderlyingIso B eR G hG T
      ((lowerStar (Profinite.continuousMapRingObj B) j).obj M)).hom := by
  apply (sheafToPresheaf (ProEt.topology T) Ab.{u + 1}).map_injective
  apply NatTrans.ext
  funext V
  change ((sheafCompose (ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})).map
      (encodingPushforwardIso B eR G hG T U j M).hom).hom.app V ≫
      (encodingUnderlyingIso B eR G hG U M).hom.hom.app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V) =
    (encodingUnderlyingIso B eR G hG T
      ((lowerStar (Profinite.continuousMapRingObj B) j).obj M)).hom.hom.app V
  rw [encodingUnderlyingIso_hom, encodingUnderlyingIso_hom]
  simp only [encodingPushforwardIso, eqToIso.hom, eqToHom_app]
  let PT := (((presheafToFunctor (C := T.ProEtᵒᵖ) (ULift.{u + 1} B)).obj
    ((moduleLocalizationRight (ProEt.topology T)
      (A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B))).obj
      ((Mod.comap (finiteDiscreteSchemeRingIso B T eR).hom).obj
        ((lowerStar (Profinite.continuousMapRingObj B) j).obj M)))).obj V)
  let PU := (((presheafToFunctor (C := U.ProEtᵒᵖ) (ULift.{u + 1} B)).obj
    ((moduleLocalizationRight (ProEt.topology U)
      (A (C := U.ProEtᵒᵖ) (ULift.{u + 1} B))).obj
      ((Mod.comap (finiteDiscreteSchemeRingIso B U eR).hom).obj M))).obj
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V))
  let i : PT ≅ PU := Mod.isoMk (Iso.refl _) (by
    simp only [Iso.refl_hom, Category.comp_id, MonoidalCategory.whiskerLeft_id,
      Category.id_comp]
    exact push_action B eR T U j M V)
  have hi := (eqToIso hG).hom.naturality i.hom
  change (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}).map
      (G.map i.hom) ≫ (eqToIso hG).hom.app PU = (eqToIso hG).hom.app PT ≫ 𝟙 _ at hi
  simp only [eqToIso.hom, eqToHom_app, Category.comp_id] at hi
  convert hi using 1 <;> rfl

private theorem encodingUnderlyingIso_naturality (T : Scheme.{u})
    {M P : FiniteDiscreteInternalModules B T} (q : M ⟶ P) :
    (sheafCompose (ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})).map
        ((finiteDiscreteCoefficientEquivalence B eR G hG T).inverse.map q) ≫
      (encodingUnderlyingIso B eR G hG T P).hom =
    (encodingUnderlyingIso B eR G hG T M).hom ≫ q.hom := by
  exact (sheafEncodingForgetIso (ProEt.topology T) (ULift.{u + 1} B) G hG).hom.naturality
    ((Mod.comap (finiteDiscreteSchemeRingIso B T eR).hom).map q)

private theorem encodingForgetIso_unit (T : Scheme.{u})
    (N : FiniteDiscreteProEtaleSheaves B T) :
    (finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG T).hom.app N =
      (encodingUnderlyingIso B eR G hG T
        ((finiteDiscreteCoefficientEquivalence B eR G hG T).functor.obj N)).inv ≫
      (sheafCompose (ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})).map
        ((finiteDiscreteCoefficientEquivalence B eR G hG T).unitIso.inv.app N) := by
  let H := sheafEncoding (ProEt.topology T) (ULift.{u + 1} B) G hG
  let K := Mod.comapEquivalenceOfIsIso (finiteDiscreteSchemeRingIso B T eR).hom
  let U := sheafCompose (ProEt.topology T)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})
  let d := (K.counitIso.app (H.inv.obj N)).hom
  have hd : d.hom = 𝟙 _ := by
    dsimp only [d, K, Mod.comapEquivalenceOfIsIso, CategoryTheory.Equivalence.mk]
    change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp only [Category.id_comp]
  have hn := (sheafEncodingForgetIso (ProEt.topology T) (ULift.{u + 1} B) G hG).hom.naturality d
  change U.map (H.map d) ≫
      (sheafEncodingForgetIso (ProEt.topology T) (ULift.{u + 1} B) G hG).hom.app
        (H.inv.obj N) =
    (encodingUnderlyingIso B eR G hG T
      ((finiteDiscreteCoefficientEquivalence B eR G hG T).functor.obj N)).hom ≫ d.hom at hn
  rw [hd] at hn
  erw [Category.comp_id] at hn
  apply (cancel_epi (encodingUnderlyingIso B eR G hG T
    ((finiteDiscreteCoefficientEquivalence B eR G hG T).functor.obj N)).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  unfold finiteDiscreteCoefficientEquivalenceForgetIso
  change (encodingUnderlyingIso B eR G hG T
    ((finiteDiscreteCoefficientEquivalence B eR G hG T).functor.obj N)).hom ≫
      (sheafEncodingForgetIso (ProEt.topology T) (ULift.{u + 1} B) G hG).inv.app
        (H.inv.obj N) ≫ U.map (H.asEquivalence.counitIso.hom.app N) = _
  erw [← hn]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← U.map_comp]
  congr 1

private theorem encodingUnderlyingIso_comp_forget (T : Scheme.{u})
    (N : FiniteDiscreteProEtaleSheaves B T) :
    (encodingUnderlyingIso B eR G hG T
        ((finiteDiscreteCoefficientEquivalence B eR G hG T).functor.obj N)).hom ≫
      (finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG T).hom.app N =
    (sheafCompose (ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})).map
        ((finiteDiscreteCoefficientEquivalence B eR G hG T).unitIso.inv.app N) := by
  rw [encodingForgetIso_unit]
  exact Iso.hom_inv_id_assoc _ _

private theorem restrictionForget_hom {S T : Scheme.{u}} (h : S ⟶ T)
    (N : FiniteDiscreteProEtaleSheaves B S) :
    ((finiteDiscreteCoefficientRestrictionForgetIso B eR G hG h).app N).hom =
      (ProEtale.lowerStar Ab.{u + 1} h).map
        ((finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG S).hom.app N) ≫
      (finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG T).inv.app
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).obj N) := by
  simp only [finiteDiscreteCoefficientRestrictionForgetIso]
  change 𝟙 _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ ≫ _ = _
  simp only [Category.id_comp]
  rfl

end ProofHelpers

/-- The normalized additive restriction comparison is linear over the coefficient ring.
Source: Bhatt--Scholze, Proposition 5.3.2, sectionwise module encoding
(blueprint: lem-weil-pbc-finite-discrete-restriction-linearity).

Proof in words. Under the sectionwise encoding, the action of the sheafified constant
ring is the original module action; the equality hG identifies every underlying additive
map. Restriction evaluates at the base-changed object and therefore preserves this action.
The ring identifications at S and T are pulled back from the same eR. Naturality of the
constant-sheaf pullback comparison identifies the restriction of the ring identification
at S with that at T, followed by the coefficient unit condensedPushforwardHom. Thus the
additive comparison intertwines the two scalar actions, giving the displayed equation.
-/
theorem finiteDiscreteCoefficientRestrictionForgetIso_linear
    {S T : Scheme.{u}} (h : S ⟶ T) (N : FiniteDiscreteProEtaleSheaves B S) :
    let M := (lowerStar (Profinite.continuousMapRingObj B) h).obj
      ((finiteDiscreteCoefficientEquivalence B eR G hG S).functor.obj N)
    let P := (finiteDiscreteCoefficientEquivalence B eR G hG T).functor.obj
      ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).obj N)
    let e := (finiteDiscreteCoefficientRestrictionForgetIso B eR G hG h).app N
    Mod.act M.X ≫ e.hom = (condensedRingObj (Profinite.continuousMapRingObj B) T) ◁
      e.hom ≫ Mod.act P.X := by
  let ES := finiteDiscreteCoefficientEquivalence B eR G hG S
  let ET := finiteDiscreteCoefficientEquivalence B eR G hG T
  let F := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h
  let H := ProEtale.lowerStar Ab.{u + 1} h
  let US := sheafCompose (ProEt.topology S)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})
  let UT := sheafCompose (ProEt.topology T)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})
  let M := (lowerStar (Profinite.continuousMapRingObj B) h).obj (ES.functor.obj N)
  let P := ET.functor.obj (F.obj N)
  let e := (finiteDiscreteCoefficientRestrictionForgetIso B eR G hG h).app N
  let i := encodingPushforwardIso B eR G hG T S h (ES.functor.obj N)
  let k : ET.inverse.obj M ⟶ ET.inverse.obj P :=
    i.hom ≫ F.map (ES.unitIso.inv.app N) ≫ ET.unitIso.hom.app (F.obj N)
  let q : M ⟶ P := ET.inverse.preimage k
  have hk : ET.inverse.map q = k := ET.inverse.map_preimage k
  have hq : q.hom = e.hom := by
    apply (cancel_epi (encodingUnderlyingIso B eR G hG T M).hom).mp
    apply (cancel_mono
      ((finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG T).hom.app (F.obj N))).mp
    calc
      _ = UT.map k ≫ (encodingUnderlyingIso B eR G hG T P).hom ≫
          (finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG T).hom.app (F.obj N) := by
        erw [← Category.assoc, ← encodingUnderlyingIso_naturality, hk]
      _ = UT.map k ≫ UT.map (ET.unitIso.inv.app (F.obj N)) := by
        rw [encodingUnderlyingIso_comp_forget]
      _ = UT.map i.hom ≫ H.map (US.map (ES.unitIso.inv.app N)) := by
        dsimp only [k]
        rw [Functor.map_comp, Functor.map_comp]
        simp only [Category.assoc]
        rw [← UT.map_comp, Iso.hom_inv_id_app]
        erw [CategoryTheory.Functor.map_id, Category.comp_id]
        rfl
      _ = (encodingUnderlyingIso B eR G hG T M).hom ≫
          H.map ((finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG S).hom.app N) := by
        rw [← encodingUnderlyingIso_comp_forget B eR G hG S N, Functor.map_comp,
          ← Category.assoc, encodingPushforward_underlying]
      _ = _ := by
        erw [restrictionForget_hom]
        dsimp only [F, H]
        simp only [Category.assoc, Iso.inv_hom_id_app]
        erw [Category.comp_id]
  change Mod.act M.X ≫ e.hom = _
  rw [← hq]
  exact Mod.act_hom q

/-- The sectionwise encoding commutes with ordinary pro-etale restriction. -/
@[irreducible] noncomputable def finiteDiscreteCoefficientRestrictionIso
    {S T : Scheme.{u}} (h : S ⟶ T) :
    (finiteDiscreteCoefficientEquivalence B eR G hG S).functor ⋙
        lowerStar (Profinite.continuousMapRingObj B) h ≅
      ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h ⋙
        (finiteDiscreteCoefficientEquivalence B eR G hG T).functor :=
  NatIso.ofComponents (fun N ↦ Mod.isoMk
      ((finiteDiscreteCoefficientRestrictionForgetIso B eR G hG h).app N)
      (finiteDiscreteCoefficientRestrictionForgetIso_linear B eR G hG h N))
    (fun φ ↦ Mod.hom_ext _ _
      ((finiteDiscreteCoefficientRestrictionForgetIso B eR G hG h).hom.naturality φ))

end AlgebraicGeometry.ProEtale.CondensedRing

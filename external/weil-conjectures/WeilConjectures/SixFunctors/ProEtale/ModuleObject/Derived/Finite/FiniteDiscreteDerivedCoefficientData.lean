/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientDerivedFunctorAPI
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientCoherentPullbacks
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientDirectImageOrigin
import WeilConjectures.CategoryTheory.ProperBaseChange.FullyFaithfulMate
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs

/-! # Coherent inverse-image comparisons for the common coefficient encoding -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local instance] coefficientProfiniteEssentiallySmall

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- Pullback comparisons with invertible right mates and coherent composition. -/
structure CoefficientComparisonData
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T))) where
  pullback : CoefficientPullbackFamily B Λ F
  pushforward : ∀ {S T : Scheme.{u}} (h : S ⟶ T) [QuasiCompact h] [QuasiSeparated h],
    R+(Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h) ⋙
        F T ≅
      F S ⋙
        coefficientDerivedLowerStar Λ h
  unit : ∀ {S T : Scheme.{u}} (h : S ⟶ T) [QuasiCompact h] [QuasiSeparated h]
      (K : FiniteDiscreteEtalePlus B T),
    (F T).map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).unit.app K) ≫
      (pushforward h).hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).obj K) ≫
      (coefficientDerivedLowerStar Λ h).map
        ((pullback h).hom.app K) =
    (coefficientDerivedAdjunction Λ h).unit.app
      ((F T).obj K)
  counit : ∀ {S T : Scheme.{u}} (h : S ⟶ T) [QuasiCompact h] [QuasiSeparated h]
      (K : FiniteDiscreteEtalePlus B S),
    (coefficientDerivedUpperStar Λ h).map
        ((pushforward h).hom.app K) ≫
      (coefficientDerivedAdjunction Λ h).counit.app
        ((F S).obj K) =
    (pullback h).inv.app
        (R+(Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).obj K) ≫
      (F S).map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).counit.app K)
  square : CoefficientPullbackSquare B Λ F pullback

/-- Coherent inverse-image comparisons whose canonical right mates are invertible. -/
structure CoefficientPullbackData
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T))) where
  pullback : CoefficientPullbackFamily B Λ F
  rightMate : ∀ {S T : Scheme.{u}} (h : S ⟶ T) [QuasiCompact h] [QuasiSeparated h],
    IsIso (mateEquiv
      (Etale.derivedUpperStarLowerStarAdjunctionPlus
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) h)
      (coefficientDerivedAdjunction Λ h)
      (TwoSquare.mk _ _ _ _ (pullback h).inv))
  square : CoefficientPullbackSquare B Λ F pullback

/-- Form the direct-image isomorphisms by taking canonical mates. -/
noncomputable def CoefficientPullbackData.toComparisonData
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ]
    {F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T))} (P : CoefficientPullbackData B Λ F) :
    CoefficientComparisonData B Λ F where
  pullback := P.pullback
  pushforward h _ _ := by
    let := P.rightMate h
    exact asIso (mateEquiv
      (Etale.derivedUpperStarLowerStarAdjunctionPlus
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) h)
      (coefficientDerivedAdjunction Λ h)
      (TwoSquare.mk _ _ _ _ (P.pullback h).inv))
  unit h _ _ K := by
    let := P.rightMate h
    dsimp only [asIso_hom]
    rw [reassoc_of% (unit_mateEquiv
      (Etale.derivedUpperStarLowerStarAdjunctionPlus
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) h)
      (coefficientDerivedAdjunction Λ h)
      (TwoSquare.mk _ _ _ _ (P.pullback h).inv) K)]
    simp only [← Functor.map_comp, Iso.inv_hom_id_app]
    change (coefficientDerivedAdjunction Λ h).unit.app ((F _).obj K) ≫
      (coefficientDerivedLowerStar Λ h).map
        (𝟙 ((coefficientDerivedUpperStar Λ h).obj ((F _).obj K))) = _
    rw [(coefficientDerivedLowerStar Λ h).map_id]
    exact Category.comp_id _
  counit h _ _ K := by
    let := P.rightMate h
    exact mateEquiv_counit
      (Etale.derivedUpperStarLowerStarAdjunctionPlus
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) h)
      (coefficientDerivedAdjunction Λ h)
      (TwoSquare.mk _ _ _ _ (P.pullback h).inv) K
  square := P.square

/-- The comparison interface for the concrete finite-discrete realization family. -/
abbrev FiniteDiscreteCoefficientComparisonData
    (E : ∀ T : Scheme.{u},
      FiniteDiscreteProEtaleSheaves B T ≌ FiniteDiscreteInternalModules B T) :=
  CoefficientPullbackData B (Profinite.continuousMapRingObj B)
    (fun T ↦ finiteDiscreteRealization B T (E T))

private noncomputable def realizationFullyFaithful (T : Scheme.{u})
    (E : FiniteDiscreteProEtaleSheaves B T ≌ FiniteDiscreteInternalModules B T) :
    (finiteDiscreteRealization B T E).FullyFaithful := by
  let V := DerivedCategory.Plus.ι ⋙
    D(ν^*(T)[ModuleCat.{u + 1} (ULift.{u + 1} B)])
  have : V.Faithful := ⟨fun {K L} {f g} h ↦
    ObjectProperty.hom_ext _
      ((bijective_comparisonUpperStar_mapDerivedCategory_map
        K.obj L.obj L.property).1 h)⟩
  have : (finiteDiscreteRealization B T E).Faithful := by
    unfold finiteDiscreteRealization
    exact inferInstanceAs (V ⋙ D(E.functor)).Faithful
  exact Functor.FullyFaithful.ofFullyFaithful (finiteDiscreteRealization B T E)

omit [TopologicalSpace B] [IsTopologicalRing B] in
private theorem comparisonDataOfOrigin
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T)))
    (hF : ∀ T, (F T).FullyFaithful)
    (P : CoefficientCoherentPullbackData B Λ F)
    (himage : ∀ {S T : Scheme.{u}} (h : S ⟶ T) [QuasiCompact h] [QuasiSeparated h]
      (K : FiniteDiscreteEtalePlus B S),
      (F T).essImage ((coefficientDerivedLowerStar Λ h).obj ((F S).obj K))) :
    Nonempty (CoefficientPullbackData B Λ F) := by
  refine ⟨{ pullback := @P.pullback, square := @P.square, rightMate := ?_ }⟩
  intro S T h _ _
  exact isIso_mateEquiv_of_fullyFaithful_of_essImage
    (Etale.derivedUpperStarLowerStarAdjunctionPlus
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) h)
    (coefficientDerivedAdjunction Λ h)
    (hF T) (hF S) (P.pullback h).symm (himage h)

variable
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))

/-- The common sectionwise encoding intertwines pullback, with invertible canonical
right mates on qcqs morphisms.
Source: Bhatt--Scholze, Proposition 5.3.2 and Lemmas 5.4.1 and 5.4.3
(blueprint: lem-weil-pbc-finite-discrete-derived-coefficient-data).

Proof in words. First work with ordinary module-valued pro-etale sheaves. Restriction
commutes with the etale/pro-etale comparison pushforward. Conjugating its natural
isomorphism gives the inverse-image comparison. The restriction identity is coherent
with composition; conjugation, exact derivation, and the canonical composition
isomorphisms preserve this coherence. This proves the displayed square equation,
including the equality transport supplied by sq.w. Encode internal modules using the
same functor G on every object of every site. Its forgetful equality ensures that its
maps on sections and restrictions are the original additive maps. The constant ring
identifications are all pulled back from eR at the profinite point. Their monoidal
pullback compatibility therefore identifies the scalar actions in these comparisons.
Transport the comparison through the coefficient equivalences and apply the exact
functors on derived categories, identifying the total left derived internal pullback
with its levelwise functor. For a qcqs morphism, the canonical right mate is the
bounded-below direct-image comparison, transported through those same equivalences.
It is invertible by the finite coefficient direct-image comparison. Restriction to D+
and its inclusion into the full derived category preserve the mate equation. Empty
schemes and the zero ring cause no exception: all identities come from adjunctions. -/
theorem finiteDiscreteCoefficient_derivedComparisonData [DiscreteTopology B] [Finite B] :
    Nonempty (FiniteDiscreteCoefficientComparisonData B
      (finiteDiscreteCoefficientEquivalence B eR G hG)) := by
  obtain ⟨P⟩ := finiteDiscreteCoefficient_coherentPullbacks B eR G hG
  exact comparisonDataOfOrigin B (Profinite.continuousMapRingObj B)
    (fun T ↦ finiteDiscreteRealization B T (finiteDiscreteCoefficientEquivalence B eR G hG T))
    (fun T ↦ realizationFullyFaithful B T (finiteDiscreteCoefficientEquivalence B eR G hG T))
    P (fun h _ _ K ↦ finiteDiscreteCoefficient_directImage_origin B eR G hG h K)

end AlgebraicGeometry.ProEtale.CondensedRing

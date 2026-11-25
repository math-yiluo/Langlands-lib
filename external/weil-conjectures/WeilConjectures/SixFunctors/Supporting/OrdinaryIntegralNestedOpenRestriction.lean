/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryIntegralPullbackConstruction
public import WeilConjectures.SmoothPurity.OpenCompletedRestriction.OpenCompletedRestrictionIdentification
import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralOrdinaryPullbackComparison
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # Ordinary integral pullback and successive exact open restrictions

Source: Stacks Project, sites-modules.tex, Tag 03D8; derived.tex, Tag 06YY.
(blueprint: lem-fix-ordinary-integral-nested-open-restriction).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.ordinaryIntegralDerivedPull WeilConjectures.integralDerivedPullback

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

open Opposite

private theorem openFiniteDirect
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
      (inferInstance : WeaklyEtale j) trivial
    let b := a.sheafPushforwardContinuous (E := CommRingCat.{u + 1})
      (ProEt.topology U) (ProEt.topology X)
    b.unit.app (integralCoefficientCommRingSheaf l E X n) ≫
      (proEtaleSheafDirectImage j CommRingCat.{u + 1}).map
        ((OpenCompletedRestriction.coefficients l E j).finite n).inv =
      coefficientProEtaleDirectRingMap.{u, u} j
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  let c := OpenCompletedRestriction.coefficients l E j
  apply Sheaf.hom_ext
  unfold integralCoefficientCommRingSheaf constantSheaf
  apply sheafify_hom_ext (D := CommRingCat.{u + 1}) (ProEt.topology X) _ _
    (((proEtaleSheafDirectImage j CommRingCat.{u + 1}).obj
      ((constantSheaf (ProEt.topology U) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E (n + 1))))))).property
  apply NatTrans.ext
  funext V
  let B := CommRingCat.of
    (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
  let ηX := toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj B)
  let ηU := toSheafify (ProEt.topology U) ((Functor.const U.ProEtᵒᵖ).obj B)
  have hd := congrArg (fun α ↦ α.app V)
    ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
      ((Functor.const X.ProEtᵒᵖ).obj B)
      (((proEtaleBaseChange j).sheafPushforwardContinuous CommRingCat.{u + 1}
        (ProEt.topology X) (ProEt.topology U)).obj
        ((constantSheaf (ProEt.topology U) CommRingCat.{u + 1}).obj B))
      |>.apply_symm_apply (Functor.whiskerLeft (proEtaleBaseChange j).op ηU))
  have hn := ηX.naturality (a.counit.app V.unop).op
  change 𝟙 B ≫ ηX.app (op ((OpenCompletedRestriction.inclusion j).obj
      ((proEtaleBaseChange j).obj V.unop))) =
    ηX.app V ≫ (((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj B).obj.map
      (a.counit.app V.unop).op) at hn
  rw [Category.id_comp] at hn
  change ηX.app V ≫
    (((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj B).obj.map
      (a.counit.app V.unop).op ≫
        (c.finite n).inv.hom.app ((proEtaleBaseChange j).op.obj V)) = _
  rw [← Category.assoc]
  erw [← hn]
  erw [← c.constants n ((proEtaleBaseChange j).obj V.unop)]
  rw [Category.assoc]
  have hi := congrArg (fun q ↦ q.hom.app ((proEtaleBaseChange j).op.obj V))
    (c.finite n).hom_inv_id
  change (c.finite n).hom.hom.app ((proEtaleBaseChange j).op.obj V) ≫
    (c.finite n).inv.hom.app ((proEtaleBaseChange j).op.obj V) = 𝟙 _ at hi
  erw [hi]
  erw [Category.comp_id]
  exact hd.symm

private theorem openDirect
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
      (inferInstance : WeaklyEtale j) trivial
    let b := a.sheafPushforwardContinuous (E := CommRingCat.{u + 1})
      (ProEt.topology U) (ProEt.topology X)
    (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (b.unit.app (completedIntegralCommRingSheafUnrestricted l E X) ≫
        (proEtaleSheafDirectImage j CommRingCat.{u + 1}).map
          (OpenCompletedRestriction.coefficients l E j).completed.inv) =
      ordinaryIntegralDirectRingMap l E j := by
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  let b := a.sheafPushforwardContinuous (E := CommRingCat.{u + 1})
    (ProEt.topology U) (ProEt.topology X)
  let c := OpenCompletedRestriction.coefficients l E j
  let F := OpenCompletedRestriction.ringRestriction.{u, u} j
  let G := proEtaleSheafDirectImage j CommRingCat.{u + 1}
  let H := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  apply (ordinaryIntegralDirectRingMap_existsUnique l E j).unique
  · intro n
    have hc : c.completed.inv ≫ completedIntegralCommRingProjectionUnrestricted l E U n =
        F.map (completedIntegralCommRingProjectionUnrestricted l E X n) ≫
          (c.finite n).inv := by
      rw [← cancel_epi c.completed.hom]
      rw [Iso.hom_inv_id_assoc, ← Category.assoc, c.projections]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hn := b.unit.naturality (completedIntegralCommRingProjectionUnrestricted l E X n)
    change completedIntegralCommRingProjectionUnrestricted l E X n ≫
        b.unit.app (integralCoefficientCommRingSheaf l E X n) =
      b.unit.app (completedIntegralCommRingSheafUnrestricted l E X) ≫
        G.map (F.map (completedIntegralCommRingProjectionUnrestricted l E X n)) at hn
    have he : (b.unit.app (completedIntegralCommRingSheafUnrestricted l E X) ≫
        G.map c.completed.inv) ≫ G.map
          (completedIntegralCommRingProjectionUnrestricted l E U n) =
        completedIntegralCommRingProjectionUnrestricted l E X n ≫
          coefficientProEtaleDirectRingMap.{u, u} j
            (CommRingCat.of
              (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
      rw [Category.assoc, ← G.map_comp, hc, G.map_comp, ← Category.assoc]
      erw [← hn]
      rw [Category.assoc]
      exact congrArg
        (fun q ↦ completedIntegralCommRingProjectionUnrestricted l E X n ≫ q)
        (openFiniteDirect l E j n)
    exact congrArg H.map he
  · exact (ordinaryIntegralDirectRingMap_existsUnique l E j).exists.choose_spec

private noncomputable def openModuleIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ordinaryIntegralModulePull l E j ≅ OpenCompletedRestriction.ordinary l E j := by
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  let b := a.sheafPushforwardContinuous (E := CommRingCat.{u + 1})
    (ProEt.topology U) (ProEt.topology X)
  let c := (OpenCompletedRestriction.coefficients l E j).completed
  let F := OpenCompletedRestriction.ringRestriction.{u, u} j
  let G := proEtaleSheafDirectImage j CommRingCat.{u + 1}
  let ψ := b.unit.app (completedIntegralCommRingSheafUnrestricted l E X) ≫ G.map c.inv
  have h₁ : ψ ≫ G.map c.hom =
      b.unit.app (completedIntegralCommRingSheafUnrestricted l E X) := by
    dsimp only [ψ]
    rw [Category.assoc, ← G.map_comp, c.inv_hom_id, G.map_id]
    exact Category.comp_id _
  have hn := b.counit.naturality c.inv
  change F.map (G.map c.inv) ≫
      b.counit.app (completedIntegralCommRingSheafUnrestricted l E U) =
    b.counit.app (F.obj (completedIntegralCommRingSheafUnrestricted l E X)) ≫ c.inv at hn
  have ht := b.left_triangle_components (completedIntegralCommRingSheafUnrestricted l E X)
  change F.map (b.unit.app (completedIntegralCommRingSheafUnrestricted l E X)) ≫
    b.counit.app (F.obj (completedIntegralCommRingSheafUnrestricted l E X)) = 𝟙 _ at ht
  have h₂ : c.hom ≫ F.map ψ ≫
      b.counit.app (completedIntegralCommRingSheafUnrestricted l E U) = 𝟙 _ := by
    dsimp only [ψ]
    rw [F.map_comp, Category.assoc]
    erw [hn]
    have he := congrArg (fun q ↦ c.hom ≫ q ≫ c.inv) ht
    erw [Category.id_comp, c.hom_inv_id] at he
    simpa only [Category.assoc] using he
  let φ := (sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom
  let χ := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ψ
  let d := SheafOfModules.pushforwardPushforwardAdj a φ χ
    (by
      apply NatTrans.ext
      funext V
      exact congrArg (fun q ↦ (forget₂ CommRingCat RingCat).map (q.hom.app V)) h₁.symm)
    (by
      apply NatTrans.ext
      funext V
      exact congrArg (fun q ↦ (forget₂ CommRingCat RingCat).map (q.hom.app V)) h₂)
  let e : SheafOfModules.pushforward.{u + 1} χ ≅ ordinaryIntegralModulePush l E j :=
    SheafOfModules.pushforwardCongr (openDirect l E j)
  exact (ordinaryIntegralModuleAdjunction l E j).leftAdjointUniq (d.ofNatIsoRight e)

/-- The ordinary derived pullback along an open immersion is normalized exact restriction.
Source: Stacks Project, sites-modules.tex, Tag 03D8; derived.tex, Tag 06YY.
(blueprint: lem-fix-ordinary-integral-nested-open-restriction).
-/
private theorem ordinaryIntegralOpenRestrictionDerivedIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Nonempty (ordinaryIntegralDerivedPull l E j ≅
      OpenCompletedRestriction.derivedRestriction l E j) := by
  have := OpenCompletedRestriction.ordinaryAdditive l E j
  have := OpenCompletedRestriction.ordinaryLimits l E j
  have := OpenCompletedRestriction.ordinaryColimits l E j
  have := preservesFiniteLimits_of_natIso (openModuleIso l E j).symm
  have := (ordinaryIntegralModuleAdjunction l E j).leftAdjoint_preservesColimits
  let F := ordinaryIntegralModulePull l E j
  let W := HomotopyCategory.quasiIso (integralTowerModules l E X) (.up ℤ)
  let : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W F.mapDerivedCategory F.mapDerivedCategoryFactorsh
  let ε := ordinaryIntegralPullCounit l E j
  let : (ordinaryIntegralDerivedPull l E j).IsLeftDerivedFunctor ε W := by
    dsimp only [ε]
    unfold ordinaryIntegralPullCounit ordinaryIntegralDerivedPull
    infer_instance
  exact ⟨Functor.leftDerivedUnique F.mapDerivedCategory (ordinaryIntegralDerivedPull l E j)
    ε F.mapDerivedCategoryFactorsh.hom W ≪≫
      Functor.mapDerivedCategoryNatIso (openModuleIso l E j)⟩

/-- Ordinary derived pullback composes for arbitrary composable scheme morphisms.
Source: Stacks Project, sites-modules.tex, Tag 03D8; derived.tex, Tag 06YY.
(blueprint: lem-fix-ordinary-integral-nested-open-restriction).
-/
private theorem ordinaryIntegralDerivedPullbackComposition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z) :
    Nonempty (ordinaryIntegralDerivedPull l E (g ≫ f) ≅
      ordinaryIntegralDerivedPull l E f ⋙ ordinaryIntegralDerivedPull l E g) := by
  let R := PurCompactSupport.completed l E
  exact ⟨(IntegralOrdinary.pullIso l E (g ≫ f)).symm ≪≫
    PurCompactSupport.geometricPullComposition R g f
      (PurCompactSupport.completedPull_comp l E g f) ≪≫
    Functor.isoWhiskerRight (IntegralOrdinary.pullIso l E f) (PurCompactSupport.pull R g) ≪≫
    Functor.isoWhiskerLeft (ordinaryIntegralDerivedPull l E f)
      (IntegralOrdinary.pullIso l E g)⟩

/-- Ordinary uncompleted pullback along an open followed by an arbitrary morphism
is successive normalized exact restriction. No completeness hypothesis occurs here.

Source: Stacks Project, sites-modules.tex, lemma-push-pull-composition-modules
(Tag 03D8), and derived.tex, Tag 06YY; step 3 of
lem-fix-clopen-completed-restriction-comparison.
(blueprint: lem-fix-ordinary-integral-nested-open-restriction).

Proof: the normalized finite restriction isomorphisms preserve constant sections.
Naturality and the completed quotient-projection equations identify their adjoint
coefficient map with the ordinary direct coefficient map. Lift the site adjunction
to module sheaves; uniqueness of left adjoints identifies ordinary module pullback
along an open with exact restriction. Uniqueness of total left derived functors
then gives the derived identification. Transport the existing geometric pullback
compositor through IntegralOrdinary.pullIso to obtain ordinary derived pullback
composition. Apply it to A into V into W and A into U into V, then replace the two
open pullbacks by their exact restrictions. The argument includes empty opens,
identity inclusions and zero modules. -/
theorem ordinaryIntegralNestedOpenRestriction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W V : Scheme.{u}) (f : V ⟶ W) (U A : V.Opens) (hAU : A ≤ U) :
    Nonempty (ordinaryIntegralDerivedPull l E (A.ι ≫ f) ≅
      ordinaryIntegralDerivedPull l E f ⋙
        OpenCompletedRestriction.derivedRestriction l E U.ι ⋙
          OpenCompletedRestriction.derivedRestriction l E (V.homOfLE hAU)) := by
  obtain ⟨e₁⟩ := ordinaryIntegralDerivedPullbackComposition l E A.ι f
  obtain ⟨e₂⟩ := ordinaryIntegralDerivedPullbackComposition l E (V.homOfLE hAU) U.ι
  obtain ⟨e₃⟩ := ordinaryIntegralOpenRestrictionDerivedIso l E U.ι
  obtain ⟨e₄⟩ := ordinaryIntegralOpenRestrictionDerivedIso l E (V.homOfLE hAU)
  have he : ordinaryIntegralDerivedPull l E A.ι ≅
      ordinaryIntegralDerivedPull l E U.ι ⋙
        ordinaryIntegralDerivedPull l E (V.homOfLE hAU) := by
    simpa only [Scheme.homOfLE_ι] using e₂
  exact ⟨e₁ ≪≫ Functor.isoWhiskerLeft (ordinaryIntegralDerivedPull l E f)
    (he ≪≫ Functor.isoWhiskerRight e₃ _ ≪≫ Functor.isoWhiskerLeft _ e₄)⟩

end WeilConjectures

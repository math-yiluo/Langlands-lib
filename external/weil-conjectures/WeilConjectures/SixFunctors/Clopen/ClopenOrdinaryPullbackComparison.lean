/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.OpenCompletedRestriction.OpenCompletedRestrictionIdentification
public import WeilConjectures.SmoothPurity.IntegralAmbient.NormalizedIntegralPullbackTower

/-! # Exact open restriction of the strict finite pullback tower

Source: Stacks Project, sites-modules.tex, Tags 03D2 and 03D8.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

set_option backward.defeqAttrib.useBackward true
set_option allowUnsafeReducibility true
attribute [local reducible] IntegralOnSlice.Site IntegralOnSlice.topology
  IntegralOnSlice.restrict IntegralOnSlice.ring IntegralOnSlice.finite
  IntegralOnSlice.projection
  integralCoefficientCommRingSheaf integralCoefficientSheaf CategoryTheory.constantSheaf
  CategoryTheory.Functor.sheafPushforwardContinuous

private noncomputable def openRingAdj (V : Scheme.{u}) (U : V.Opens) :
    OpenCompletedRestriction.ringRestriction.{u, u} U.ι ⊣
      (proEtaleBaseChange U.ι).sheafPushforwardContinuous CommRingCat.{u + 1}
        (ProEt.topology V) (ProEt.topology U.toScheme) :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.ι
    (inferInstance : WeaklyEtale U.ι) trivial).sheafPushforwardContinuous
      (ProEt.topology U.toScheme) (ProEt.topology V)

private theorem finiteAdjunct
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (V : Scheme.{u}) (U : V.Opens)
    (c : OpenCompletedRestriction.Coefficients l E U.ι) (n : ℕ) :
    (openRingAdj V U).homEquiv _ _ (c.finite n).inv =
      coefficientProEtaleDirectRingMap.{u, u} U.ι
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  let A := CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
  apply ((sheafificationAdjunction (ProEt.topology V) CommRingCat.{u + 1}).homEquiv
    ((Functor.const V.ProEtᵒᵖ).obj A) _).injective
  dsimp only [A]
  rw [coefficientProEtaleDirectRingMap, Equiv.apply_symm_apply]
  change toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj A) ≫
    ((openRingAdj V U).homEquiv _ _ (c.finite n).inv).hom = _
  apply NatTrans.ext
  funext W
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.ι
    (inferInstance : WeaklyEtale U.ι) trivial
  change (toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj A)).app W ≫
    (integralCoefficientCommRingSheaf l E V n).obj.map (a.counit.app W.unop).op ≫
      (c.finite n).inv.hom.app ((proEtaleBaseChange U.ι).op.obj W) = _
  have hn := (toSheafify (ProEt.topology V)
    ((Functor.const V.ProEtᵒᵖ).obj A)).naturality (a.counit.app W.unop).op
  have hn' :
      (toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj A)).app W ≫
          (integralCoefficientCommRingSheaf l E V n).obj.map (a.counit.app W.unop).op =
        (toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj A)).app
          (op ((OpenCompletedRestriction.inclusion U.ι).obj
            ((proEtaleBaseChange U.ι).obj W.unop))) := by
    exact hn.symm.trans (Category.id_comp _)
  erw [← Category.assoc, hn']
  rw [← c.constants n ((proEtaleBaseChange U.ι).obj W.unop), Category.assoc]
  have hi := congrArg (fun f ↦ f.hom.app ((proEtaleBaseChange U.ι).op.obj W))
    (c.finite n).hom_inv_id
  exact (congrArg
    (fun f ↦ (toSheafify (ProEt.topology U.toScheme)
      ((Functor.const U.toScheme.ProEtᵒᵖ).obj A)).app
        ((proEtaleBaseChange U.ι).op.obj W) ≫ f) hi).trans (Category.comp_id _)

private theorem completedAdjunct
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (V : Scheme.{u}) (U : V.Opens)
    (c : OpenCompletedRestriction.Coefficients l E U.ι) :
    (openRingAdj V U).homEquiv _ _ c.completed.inv =
      IntegralAmbient.coefficientMap.{u, u} l E U.ι := by
  apply (IntegralAmbient.coefficientMap_existsUnique.{u, u} l E U.ι).unique ?_
    (IntegralAmbient.coefficientMap_existsUnique.{u, u} l E U.ι).exists.choose_spec
  intro n
  rw [← (openRingAdj V U).homEquiv_naturality_right c.completed.inv
    (completedIntegralCommRingProjectionUnrestricted.{u, u} l E U.toScheme n)]
  have hs : c.completed.inv ≫
      completedIntegralCommRingProjectionUnrestricted.{u, u} l E U.toScheme n =
      (OpenCompletedRestriction.ringRestriction.{u, u} U.ι).map
        (completedIntegralCommRingProjectionUnrestricted.{u, u} l E V n) ≫ (c.finite n).inv := by
    apply (cancel_epi c.completed.hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, c.projections, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [hs, (openRingAdj V U).homEquiv_naturality_left
    (completedIntegralCommRingProjectionUnrestricted.{u, u} l E V n) (c.finite n).inv,
    finiteAdjunct l E V U c n]

universe v₁ v₂ v₃ v₄ r
private noncomputable def restrictionAdjunction
    {C : Type v₁} [Category.{v₂} C] {D : Type v₃} [Category.{v₄} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} {G : D ⥤ C} [F.IsContinuous J K] [G.IsContinuous K J]
    (a : F ⊣ G) (R : Sheaf K RingCat.{r}) (S : Sheaf J RingCat.{r})
    (c : S ≅ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R) :
    SheafOfModules.pushforward.{r} c.hom ⊣ SheafOfModules.pushforward.{r}
      ((a.sheafPushforwardContinuous (E := RingCat.{r}) J K).homEquiv R S c.inv) := by
  let b := a.sheafPushforwardContinuous (E := RingCat.{r}) J K
  let ψ := b.homEquiv R S c.inv
  have H₁ : Functor.whiskerRight (NatTrans.op a.counit) R.obj =
      ψ.hom ≫ G.op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext W
    change R.obj.map (a.counit.app W.unop).op =
      R.obj.map (a.counit.app W.unop).op ≫ c.inv.hom.app (G.op.obj W) ≫
        c.hom.hom.app (G.op.obj W)
    simp
  have H₂ : c.hom.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext W
    apply (cancel_mono (c.hom.hom.app W)).mp
    dsimp
    rw [Category.id_comp]
    have hn := c.hom.hom.naturality (a.unit.app W.unop).op
    dsimp at hn
    rw [Category.assoc, Category.assoc, hn]
    have hh := congrArg (fun t ↦ t.app (F.op.obj W)) H₁
    dsimp at hh
    erw [← Category.assoc (ψ.hom.app (F.op.obj W))
      (c.hom.hom.app (G.op.obj (F.op.obj W)))
      (R.obj.map (F.map (a.unit.app W.unop)).op), ← hh]
    rw [← Functor.map_comp, ← op_comp]
    erw [a.left_triangle_components]
    change c.hom.hom.app W ≫ R.obj.map (𝟙 (F.op.obj W)) = c.hom.hom.app W
    rw [R.obj.map_id]
    exact Category.comp_id _
  exact SheafOfModules.pushforwardPushforwardAdj a c.hom ψ H₁ H₂

/-- Ordinary normalized open restriction is the ambient integral module pullback.

Source: Stacks Project, sites-modules.tex, Tags 03D2 and 03D7.
(blueprint: lem-sf-clopen-ordinary-pullback-comparison).

Proof: the composition/base-change adjunction on sites transposes the inverse
finite coefficient isomorphisms to the specified constant-section maps, by
naturality of sheafification. Projection compatibility and uniqueness identify
the transpose of the completed coefficient inverse with the ambient coefficient
map. Apply the ringed-site module adjunction and uniqueness of left adjoints.
This works for every open immersion, including the empty one. -/
theorem clopenOrdinaryPullbackComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (V : Scheme.{u}) (U : V.Opens) :
    Nonempty (OpenCompletedRestriction.ordinary l E U.ι ≅ IntegralAmbient.pull l E U.ι) := by
  let c := OpenCompletedRestriction.coefficients l E U.ι
  let H := sheafCompose (ProEt.topology U.toScheme)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.ι
    (inferInstance : WeaklyEtale U.ι) trivial
  let d := restrictionAdjunction a _ _ (H.mapIso c.completed)
  let e : OpenCompletedRestriction.ordinary l E U.ι ⊣ IntegralAmbient.push l E U.ι :=
    d.ofNatIsoRight (SheafOfModules.pushforwardCongr (by
      have h := completedAdjunct l E V U c
      exact congrArg
        (fun k ↦ (sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map k) h))
  exact ⟨e.leftAdjointUniq (IntegralAmbient.adjunction l E U.ι)⟩

end WeilConjectures

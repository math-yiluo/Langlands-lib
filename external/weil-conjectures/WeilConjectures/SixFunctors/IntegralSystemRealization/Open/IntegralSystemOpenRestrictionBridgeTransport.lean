/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import all WeilConjectures.CategoryTheory.SixFunctors.SystemProperOpenLambdaExchange
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralSystemOpenCompositorBridge

/-! Transport of the open-restriction factor through the canonical bridge. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

private theorem restriction_component
    {A B C : Type*} [Category A] [Category B] [Category C]
    (S : A ⥤ B) (J : B ⥤ C) (K : A ⥤ C) (P : C ⥤ B)
    (d : S ⋙ J ≅ K) (u : 𝟭 B ≅ J ⋙ P) (X : A) :
    (Functor.isoWhiskerRight d.symm P ≪≫ Functor.associator S J P ≪≫
      Functor.isoWhiskerLeft S u.symm ≪≫ Functor.rightUnitor S).hom.app X =
      P.map (d.inv.app X) ≫ u.inv.app (S.obj X) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.rightUnitor_hom_app, Category.id_comp]
  have hid : u.inv.app (S.obj X) ≫ 𝟙 (S.obj X) = u.inv.app (S.obj X) := by
    simpa only [Functor.id_obj] using Category.comp_id (u.inv.app (S.obj X))
  exact congrArg (fun z ↦ P.map (d.inv.app X) ≫ z) hid

private theorem open_unit_transport
    {A B : Type*} [Category A] [Category B]
    {L L' : A ⥤ B} {R R' : B ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (e : R ≅ R') (f : L ≅ L')
    (hf : f = (a.ofNatIsoRight e).leftAdjointUniq b) (X : A) :
    a.unit.app X ≫ e.hom.app (L.obj X) ≫ R'.map (f.hom.app X) = b.unit.app X := by
  subst f
  simpa only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc] using
    Adjunction.unit_leftAdjointUniq_hom_app (a.ofNatIsoRight e) b X

private theorem inverse_unit_component {C : Type*} [Category C]
    {A X Y Z : C} (u : A ≅ X) (v : A ≅ Z) (g : X ⟶ Y) (c : Y ⟶ Z)
    (hu : u.hom ≫ g ≫ c = v.hom) : u.inv = g ≫ c ≫ v.inv := by
  apply (cancel_epi u.hom).1
  rw [u.hom_inv_id]
  calc
    _ = v.hom ≫ v.inv := v.hom_inv_id.symm
    _ = _ := by rw [← hu]; simp only [Category.assoc]

private theorem inverse_factor_component {C : Type*} [Category C]
    {X Y X' Y' : C} (d : X ≅ Y) (e : X' ≅ Y') (k : Y ⟶ Y') (z : X ⟶ X')
    (hd : d.hom ≫ k = z ≫ e.hom) : d.inv ≫ z = k ≫ e.inv := by
  apply (cancel_epi d.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [hd]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem restriction_component_pasting {C : Type*} [Category C]
    {X Y Z A B D F G H : C}
    (m : X ⟶ Y) (u : Y ⟶ A) (e : A ⟶ B) (a : X ⟶ Z) (v : Y ⟶ D)
    (b : Z ⟶ D) (c : D ⟶ F) (w : F ⟶ A) (t : F ⟶ G) (w' : G ⟶ B)
    (k : Z ⟶ H) (d : H ⟶ G)
    (hu : u = v ≫ c ≫ w) (hp : m ≫ v = a ≫ b) (hv : t ≫ w' = w ≫ e)
    (hm : b ≫ c ≫ t = k ≫ d) : (m ≫ u) ≫ e = a ≫ k ≫ d ≫ w' := by
  rw [hu]
  simp only [Category.assoc]
  rw [← hv, reassoc_of% hp, reassoc_of% hm]

private theorem restriction_atomic_pasting {C : Type*} [Category C]
    {X Y Z A B D F G H : C}
    (m : X ⟶ Y) (u : Y ⟶ A) (e : A ⟶ B) (a : X ⟶ Z) (v : Y ⟶ D)
    (b : Z ⟶ D) (c : D ⟶ F) (w : F ⟶ A) (t : F ⟶ G) (w' : G ⟶ B)
    (k : Z ⟶ H) (d : H ⟶ G) (rho : X ⟶ A) (rho' : H ⟶ B)
    (hrho : rho = m ≫ u) (hrho' : rho' = d ≫ w')
    (hu : u = v ≫ c ≫ w) (hp : m ≫ v = a ≫ b) (hv : t ≫ w' = w ≫ e)
    (hm : b ≫ c ≫ t = k ≫ d) : rho ≫ e = a ≫ k ≫ rho' := by
  rw [hrho, hrho']
  exact restriction_component_pasting m u e a v b c w t w' k d hu hp hv hm

namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private abbrev Model (X : Scheme.{u}) :=
  ProEtale.SemilinearProperOpen.Derived (scalarRings l E) (scalarTransitions l E) X

attribute [local implicit_reducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition integralCoefficientCommRingSheaf
  integralCoefficientSheaf integralCoefficientSheafTransition
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  sheafCompose ProEtale.SemilinearProperOpen.derived RingHom.ulift
  SemilinearSections.moduleAbelian SemilinearSections.hasDerived coefficientSequenceHasDerived
  CommRingCat.hasForgetToRingCat

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf HasDerivedCategory.standard DerivedCategory.Q
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryNatIso
  Direct.adj Open.adj CanonicalBridge.pull CanonicalBridge.push
  CanonicalBridge.shriek ProEtale.SemilinearProperOpen.adj ProEtale.SemilinearProperOpen.jAdj
  ProEtale.SemilinearProperOpen.P ProEtale.SemilinearProperOpen.R
  ProEtale.SemilinearProperOpen.J pullbackTensorSequenceDerived
  Compositors.square Compositors.openComp ProEtale.SemilinearProperOpen.squareP
  ProEtale.SemilinearProperOpen.jComp OpenComparisons.unit restrictFactor
  ProEtale.SemilinearProperOpen.restrictFactor

private def modelP {U V : Scheme.{u}} (j : U ⟶ V) : Model l E V ⥤ Model l E U :=
  ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E) j

private def modelJ {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    Model l E U ⥤ Model l E V :=
  ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) j

private def modelAdj {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    modelJ l E j ⊣ modelP l E j :=
  ProEtale.SemilinearProperOpen.jAdj (scalarRings l E) (scalarTransitions l E) j

private def modelUnit {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    𝟭 (Model l E U) ≅ modelJ l E j ⋙ modelP l E j :=
  @asIso _ _ _ _ (modelAdj l E j).unit
    (ProEtale.SemilinearProperOpen.jAdj_unit_isIso
      (scalarRings l E) (scalarTransitions l E) j)

private def modelComp {U V W : Scheme.{u}} (s : U ⟶ V) (j : V ⟶ W) (k : U ⟶ W)
    [IsOpenImmersion s] [IsOpenImmersion j] [IsOpenImmersion k] (h : s ≫ j = k) :
    modelJ l E s ⋙ modelJ l E j ≅ modelJ l E k :=
  ProEtale.SemilinearProperOpen.jComp (scalarRings l E) (scalarTransitions l E) s j ≪≫
    ProEtale.SemilinearProperOpen.jCongr (scalarRings l E) (scalarTransitions l E) h

private def modelRestriction {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    modelJ l E k ⋙ modelP l E (pullback.fst p i) ≅
      modelJ l E (ProEtale.StrictTower.squareLift k r p i h) :=
  ProEtale.SemilinearProperOpen.restrictFactor
    (scalarRings l E) (scalarTransitions l E) k r p i h

private theorem modelRestriction_eq {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    modelRestriction l E k r p i h =
      Functor.isoWhiskerRight
        (modelComp l E (ProEtale.StrictTower.squareLift k r p i h)
          (pullback.fst p i) k (pullback.lift_fst k r h)).symm
        (modelP l E (pullback.fst p i)) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (modelJ l E (ProEtale.StrictTower.squareLift k r p i h))
        (modelUnit l E (pullback.fst p i)).symm ≪≫ Functor.rightUnitor _ := by
  unfold modelRestriction ProEtale.SemilinearProperOpen.restrictFactor
    modelComp modelUnit modelAdj modelP modelJ
  rfl

private def modelBridgeP (o : Operations l E) (b : CanonicalBridge l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) : (pull l E j : Model l E V ⥤ Model l E U) ≅ modelP l E j :=
  b.pull l E j

private def modelBridgeJ (o : Operations l E) (b : CanonicalBridge l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    (Operations.shriek l E o j : Model l E U ⥤ Model l E V) ≅ modelJ l E j :=
  b.shriek l E j

private theorem modelUnit_hom {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j] : (modelUnit l E j).hom = (modelAdj l E j).unit := by
  rfl

private def sourceAdj (o : Operations l E) {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j] :
    (Operations.shriek l E o j : Model l E U ⥤ Model l E V) ⊣
      (pull l E j : Model l E V ⥤ Model l E U) :=
  (o.extension j).adj

attribute [local implicit_reducible] sourceAdj

private theorem modelBridgeJ_eq (o : Operations l E) (b : CanonicalBridge l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    modelBridgeJ l E o b j =
      ((sourceAdj l E o j).ofNatIsoRight (modelBridgeP l E o b j)).leftAdjointUniq
        (modelAdj l E j) := by
  unfold modelBridgeJ modelBridgeP modelAdj sourceAdj CanonicalBridge.shriek
  rfl

section
attribute [local irreducible] modelP modelJ modelAdj modelUnit modelComp modelRestriction

private theorem modelRestriction_component {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Model l E U) :
    (modelRestriction l E k r p i h).hom.app M =
      (modelP l E (pullback.fst p i)).map
        ((modelComp l E (ProEtale.StrictTower.squareLift k r p i h)
          (pullback.fst p i) k (pullback.lift_fst k r h)).inv.app M) ≫
      (modelUnit l E (pullback.fst p i)).inv.app
        ((modelJ l E (ProEtale.StrictTower.squareLift k r p i h)).obj M) := by
  rw [modelRestriction_eq]
  exact restriction_component _ _ _ _ _ _ M

end

private theorem suppliedRestriction_component (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Model l E U) :
    (restrictFactor l E o c a k r p i h).hom.app M =
      (pull l E (pullback.fst p i)).map
        ((c.openComp l E (ProEtale.StrictTower.squareLift k r p i h) (pullback.fst p i) ≪≫
          openCongr l E o (pullback.lift_fst k r h)).inv.app M) ≫
      (a.unit l E o c (pullback.fst p i)).inv.app
        ((Operations.shriek l E o (ProEtale.StrictTower.squareLift k r p i h)).obj M) := by
  exact restrictFactor_formula l E c a k r p i h M

section
attribute [local irreducible] modelP modelJ modelAdj modelUnit modelBridgeP modelBridgeJ

private theorem model_unit_bridge (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] (M : Model l E U) :
    (a.unit l E o c j).hom.app M ≫
        (modelBridgeP l E o b j).hom.app ((Operations.shriek l E o j).obj M) ≫
        (modelP l E j).map ((modelBridgeJ l E o b j).hom.app M) =
      (modelUnit l E j).hom.app M := by
  rw [modelUnit_hom]
  unfold OpenComparisons.unit
  change (o.extension j).adj.unit.app M ≫ _ ≫ _ = _
  exact @open_unit_transport (Model l E U) (Model l E V)
    (inferInstanceAs (Category.{u + 2} (Model l E U)))
    (inferInstanceAs (Category.{u + 2} (Model l E V)))
    (Operations.shriek l E o j) (modelJ l E j) (pull l E j) (modelP l E j)
    (sourceAdj l E o j) (modelAdj l E j)
    (modelBridgeP l E o b j) (modelBridgeJ l E o b j)
    (modelBridgeJ_eq l E o b j) M

end

section
attribute [local implicit_reducible] modelP modelJ modelBridgeJ
attribute [local irreducible] modelComp

private theorem model_factor_bridge (o : Operations l E) (c : Compositors l E o)
    (b : CanonicalBridge l E o) {U V W : Scheme.{u}}
    (s : U ⟶ V) (j : V ⟶ W) (k : U ⟶ W)
    [IsOpenImmersion s] [IsOpenImmersion j] [IsOpenImmersion k] (h : s ≫ j = k)
    (M : Model l E U) :
    (c.openComp l E s j ≪≫ openCongr l E o h).hom.app M ≫
        (modelBridgeJ l E o b k).hom.app M =
      (modelBridgeJ l E o b j).hom.app ((Operations.shriek l E o s).obj M) ≫
        (modelJ l E j).map ((modelBridgeJ l E o b s).hom.app M) ≫
        (modelComp l E s j k h).hom.app M := by
  subst k
  simp only [modelBridgeJ, modelComp, modelJ, openCongr_refl,
    ProEtale.SemilinearProperOpen.jCongr, eqToIso_refl]
  dsimp only [Iso.trans, Iso.refl]
  simpa only [Category.comp_id] using
    integralSystemOpenCompositorBridge l E o c b s j M
end

section
attribute [local implicit_reducible] modelP modelJ modelBridgeP modelBridgeJ modelRestriction
attribute [local irreducible] modelComp modelAdj modelUnit

private theorem inverse_unit_bridge (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] (M : Model l E U) :
    (a.unit l E o c j).inv.app M =
      (modelBridgeP l E o b j).hom.app ((Operations.shriek l E o j).obj M) ≫
        (modelP l E j).map ((modelBridgeJ l E o b j).hom.app M) ≫
          (modelUnit l E j).inv.app M := by
  exact inverse_unit_component ((a.unit l E o c j).app M) ((modelUnit l E j).app M)
    _ _ (model_unit_bridge l E o c a b j M)

private theorem mapped_inverse_factor_bridge (o : Operations l E)
    (c : Compositors l E o) (b : CanonicalBridge l E o)
    {U V W : Scheme.{u}} (s : U ⟶ V) (j : V ⟶ W) (k : U ⟶ W)
    [IsOpenImmersion s] [IsOpenImmersion j] [IsOpenImmersion k] (h : s ≫ j = k)
    (M : Model l E U) :
    (modelP l E j).map ((c.openComp l E s j ≪≫ openCongr l E o h).inv.app M) ≫
        (modelP l E j).map
          ((modelBridgeJ l E o b j).hom.app ((Operations.shriek l E o s).obj M)) ≫
        (modelP l E j).map
          ((modelJ l E j).map ((modelBridgeJ l E o b s).hom.app M)) =
      (modelP l E j).map ((modelBridgeJ l E o b k).hom.app M) ≫
        (modelP l E j).map ((modelComp l E s j k h).inv.app M) := by
  let d := c.openComp l E s j ≪≫ openCongr l E o h
  let d' := modelComp l E s j k h
  let Q := modelP l E j
  let f := (modelBridgeJ l E o b j).hom.app ((Operations.shriek l E o s).obj M)
  let t := (modelJ l E j).map ((modelBridgeJ l E o b s).hom.app M)
  let g := (modelBridgeJ l E o b k).hom.app M
  have hd := model_factor_bridge l E o c b s j k h M
  have hi := inverse_factor_component (d.app M) (d'.app M) g (f ≫ t)
    (hd.trans (Category.assoc _ _ _).symm)
  calc
    _ = Q.map (d.inv.app M) ≫ Q.map (f ≫ t) :=
      congrArg (fun z ↦ Q.map (d.inv.app M) ≫ z) (Q.map_comp _ _).symm
    _ = Q.map (d.inv.app M ≫ f ≫ t) := (Q.map_comp _ _).symm
    _ = Q.map (g ≫ d'.inv.app M) := congrArg (fun z ↦ Q.map z) hi
    _ = _ := Q.map_comp _ _

private theorem inverse_unit_naturality {V W : Scheme.{u}} (j : V ⟶ W)
    [IsOpenImmersion j] {M N : Model l E V} (f : M ⟶ N) :
    (modelP l E j).map ((modelJ l E j).map f) ≫ (modelUnit l E j).inv.app N =
      (modelUnit l E j).inv.app M ≫ f := by
  exact (modelUnit l E j).inv.naturality f

private theorem pull_inverse_factor_naturality (o : Operations l E)
    (c : Compositors l E o) (b : CanonicalBridge l E o)
    {U V W : Scheme.{u}} (s : U ⟶ V) (j : V ⟶ W) (k : U ⟶ W)
    [IsOpenImmersion s] [IsOpenImmersion j] [IsOpenImmersion k] (h : s ≫ j = k)
    (M : Model l E U) :
    (pull l E j).map ((c.openComp l E s j ≪≫ openCongr l E o h).inv.app M) ≫
        (modelBridgeP l E o b j).hom.app
          ((Operations.shriek l E o j).obj ((Operations.shriek l E o s).obj M)) =
      (modelBridgeP l E o b j).hom.app ((Operations.shriek l E o k).obj M) ≫
        (modelP l E j).map ((c.openComp l E s j ≪≫ openCongr l E o h).inv.app M) := by
  exact (modelBridgeP l E o b j).hom.naturality
    ((c.openComp l E s j ≪≫ openCongr l E o h).inv.app M)

/-- The open-restriction factor is compatible with the canonical bridge.
Source: Stacks 03DI, 07A7 and 0F7B; blueprint fix-prop-coherence.
Proof: adjoint uniqueness transports the open unit, and isomorphism cancellation
transports its inverse. The existing open-compositor bridge compares the composite
open map, including equality transport of its factorization. Expand both restriction
factors as the pull of the inverse compositor followed by the inverse unit.
Naturality of the pull bridge and of the inverse unit then gives the equation.
(blueprint: lem-sf-integral-system-open-restriction-bridge-transport). -/
theorem openRestrictionBridge_transport (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : System l E U) :
    (restrictFactor l E o c a k r p i h).hom.app M ≫
        (b.shriek l E (ProEtale.StrictTower.squareLift k r p i h)).hom.app M =
      (b.pull l E (pullback.fst p i)).hom.app ((Operations.shriek l E o k).obj M) ≫
        (ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E)
          (pullback.fst p i)).map ((b.shriek l E k).hom.app M) ≫
        (ProEtale.SemilinearProperOpen.restrictFactor
          (scalarRings l E) (scalarTransitions l E) k r p i h).hom.app M := by
  exact restriction_atomic_pasting (C := Model l E (pullback p i))
    ((pull l E (pullback.fst p i)).map ((c.openComp l E (ProEtale.StrictTower.squareLift k r p i
      h) (pullback.fst p i) ≪≫ openCongr l E o (pullback.lift_fst k r h)).inv.app M))
    ((a.unit l E o c (pullback.fst p i)).inv.app ((Operations.shriek l E o
      (ProEtale.StrictTower.squareLift k r p i h)).obj M))
    ((modelBridgeJ l E o b (ProEtale.StrictTower.squareLift k r p i h)).hom.app M)
    ((modelBridgeP l E o b (pullback.fst p i)).hom.app ((Operations.shriek l E o k).obj M))
    ((modelBridgeP l E o b (pullback.fst p i)).hom.app ((Operations.shriek l E o (pullback.fst p
      i)).obj ((Operations.shriek l E o (ProEtale.StrictTower.squareLift k r p i h)).obj M)))
    ((modelP l E (pullback.fst p i)).map ((c.openComp l E (ProEtale.StrictTower.squareLift k r p i
      h) (pullback.fst p i) ≪≫ openCongr l E o (pullback.lift_fst k r h)).inv.app M))
    ((modelP l E (pullback.fst p i)).map ((modelBridgeJ l E o b (pullback.fst p i)).hom.app
      ((Operations.shriek l E o (ProEtale.StrictTower.squareLift k r p i h)).obj M)))
    ((modelUnit l E (pullback.fst p i)).inv.app ((Operations.shriek l E o
      (ProEtale.StrictTower.squareLift k r p i h)).obj M))
    ((modelP l E (pullback.fst p i)).map ((modelJ l E (pullback.fst p i)).map ((modelBridgeJ l E o
      b (ProEtale.StrictTower.squareLift k r p i h)).hom.app M)))
    ((modelUnit l E (pullback.fst p i)).inv.app ((modelJ l E (ProEtale.StrictTower.squareLift k r
      p i h)).obj M))
    ((modelP l E (pullback.fst p i)).map ((modelBridgeJ l E o b k).hom.app M))
    ((modelP l E (pullback.fst p i)).map ((modelComp l E (ProEtale.StrictTower.squareLift k r p i
      h) (pullback.fst p i) k (pullback.lift_fst k r h)).inv.app M))
    ((restrictFactor l E o c a k r p i h).hom.app M)
    ((modelRestriction l E k r p i h).hom.app M)
    (suppliedRestriction_component l E o c a k r p i h M)
    (modelRestriction_component l E k r p i h M)
    (inverse_unit_bridge l E o c a b (pullback.fst p i) ((Operations.shriek l E o
      (ProEtale.StrictTower.squareLift k r p i h)).obj M))
    (pull_inverse_factor_naturality l E o c b (ProEtale.StrictTower.squareLift k r p i h)
      (pullback.fst p i) k (pullback.lift_fst k r h) M)
    (inverse_unit_naturality l E (pullback.fst p i) ((modelBridgeJ l E o b
      (ProEtale.StrictTower.squareLift k r p i h)).hom.app M))
    (mapped_inverse_factor_bridge l E o c b (ProEtale.StrictTower.squareLift k r p i h)
      (pullback.fst p i) k (pullback.lift_fst k r h) M)

end

end WeilConjectures.IntegralSystemRealization

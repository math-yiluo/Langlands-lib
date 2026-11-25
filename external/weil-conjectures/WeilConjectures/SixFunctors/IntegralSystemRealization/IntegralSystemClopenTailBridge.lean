/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.IntegralSystemProperOpenBridgeWord
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemBridgePushComposition

/-! A factor identity used in proper/open transport. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

private theorem homEquiv_conjugate_transport
    {A B : Type*} [Category A] [Category B]
    {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : L₁ ≅ L₂)
    {X : A} {Y : B} (f : L₁.obj X ⟶ Y) :
    a.homEquiv X Y f ≫ (conjugateIsoEquiv a b e.symm).hom.app Y =
      b.homEquiv X Y (e.inv.app X ≫ f) := by
  rw [a.homEquiv_unit, b.homEquiv_unit]
  have hn := (conjugateIsoEquiv a b e.symm).hom.naturality f
  rw [Category.assoc, hn, ← Category.assoc]
  rw [conjugateIsoEquiv_apply_hom, unit_conjugateEquiv]
  rw [Category.assoc, ← R₂.map_comp]
  rfl

private theorem inverse_unit_transport
    {A B : Type*} [Category A] [Category B]
    {J J' : A ⥤ B} {P P' : B ⥤ A}
    (a : J ⊣ P) (a' : J' ⊣ P') (e : P ≅ P') (M : A)
    [IsIso (a.unit.app M)] [IsIso (a'.unit.app M)] :
    e.inv.app (J.obj M) ≫ inv (a.unit.app M) =
      P'.map (((a.ofNatIsoRight e).leftAdjointUniq a').hom.app M) ≫
        inv (a'.unit.app M) := by
  have h := (a.ofNatIsoRight e).unit_leftAdjointUniq_hom_app a' M
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc] at h
  apply (cancel_mono (a'.unit.app M)).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← h]
  simp only [← Category.assoc, IsIso.inv_hom_id,
    Iso.inv_hom_id_app, Category.id_comp]

private theorem clopen_transport
    {A B : Type*} [Category A] [Category B]
    {J J' : A ⥤ B} {P P' : B ⥤ A} {R R' : A ⥤ B}
    (a : J ⊣ P) (a' : J' ⊣ P') (d : P ⊣ R) (d' : P' ⊣ R')
    (e : P ≅ P') (M : A)
    [IsIso (a.unit.app M)] [IsIso (a'.unit.app M)] :
    d.homEquiv _ _ (inv (a.unit.app M)) ≫
        (conjugateIsoEquiv d d' e.symm).hom.app M =
      ((a.ofNatIsoRight e).leftAdjointUniq a').hom.app M ≫
        d'.homEquiv _ _ (inv (a'.unit.app M)) := by
  have ht := homEquiv_conjugate_transport d d' e (inv (a.unit.app M))
  rw [inverse_unit_transport a a' e M] at ht
  exact ht.trans (d'.homEquiv_naturality_left _ _)

private theorem clopen_transport_word
    {A B : Type*} [Category A] [Category B]
    {J J' : A ⥤ B} {P P' : B ⥤ A} {R R' : A ⥤ B}
    (a : J ⊣ P) (a' : J' ⊣ P') (d : P ⊣ R) (d' : P' ⊣ R')
    (e : P ≅ P') (M : A)
    [IsIso (a.unit.app M)] [IsIso a'.unit] :
    d.homEquiv _ _ (inv (a.unit.app M)) ≫
        (conjugateIsoEquiv d d' e.symm).hom.app M =
      ((a.ofNatIsoRight e).leftAdjointUniq a').hom.app M ≫
        ((Functor.rightUnitor J').inv ≫ Functor.whiskerLeft J' d'.unit ≫
          (Functor.associator J' P' R').inv ≫
          Functor.whiskerRight (inv a'.unit) R' ≫ (Functor.leftUnitor R').hom).app M := by
  simpa only [Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    NatTrans.comp_app, Functor.id_map, Functor.map_id, Functor.comp_obj, Functor.id_obj,
    Category.id_comp, Category.comp_id, Category.assoc, Adjunction.homEquiv_unit,
    NatIso.isIso_inv_app] using clopen_transport a a' d d' e M

private theorem tail_pasting
    {A B : Type*} [Category A] [Category B] (F G : A ⥤ B) (t : F ⟶ G)
    {X Y X' Y' : A} (a : X ⟶ Y) (b : X ⟶ X') (c : X' ⟶ Y') (v : Y ⟶ Y')
    {Z Z' T I : B} (d : F.obj Y ⟶ Z) (e : Z ⟶ Z') (f : Z' ⟶ I)
    (g : Z ⟶ T) (w : G.obj Y' ⟶ T) (n : T ⟶ I)
    (hc : a ≫ v = b ≫ c) (he : e ≫ f = g ≫ n)
    (hs : d ≫ g = t.app Y ≫ G.map v ≫ w) :
    F.map a ≫ d ≫ e ≫ f = t.app X ≫ G.map b ≫ G.map c ≫ w ≫ n := by
  rw [he, ← Category.assoc d, hs]
  simp only [Category.assoc]
  rw [t.naturality_assoc, ← G.map_comp_assoc, hc, G.map_comp]
  simp only [Category.assoc]

namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] CanonicalBridge.pull Functor.mapDerivedCategory
  Functor.rightDerivedFunctor HasDerivedCategory.standard DerivedCategory.Q
  Functor.leftAdjoint Adjunction.leftAdjointUniq
  CanonicalBridge.push CanonicalBridge.shriek Compositors.pushComp
  ProEtale.SemilinearProperOpen.R
  ProEtale.SemilinearProperOpen.J ProEtale.SemilinearProperOpen.adj
  ProEtale.SemilinearProperOpen.jAdj

attribute [local implicit_reducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition integralCoefficientCommRingSheaf
  integralCoefficientSheaf integralCoefficientSheafTransition
  WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf WeilConjectures.SemilinearSections.rings
  sheafCompose ProEtale.SemilinearProperOpen.derived RingHom.ulift

private theorem clopen_bridge (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j]
    (M : System l E U) :
    (a.clopen j).hom.app M ≫ (b.push l E j).hom.app M =
      (b.shriek l E j).hom.app M ≫
        (ProEtale.SemilinearProperOpen.openToS
          (scalarRings l E) (scalarTransitions l E) j).app M := by
  have := a.unitIso j M
  have := ProEtale.SemilinearProperOpen.jAdj_unit_isIso
    (scalarRings l E) (scalarTransitions l E) j
  rw [a.clopen_transpose]
  delta CanonicalBridge.push CanonicalBridge.shriek ProEtale.SemilinearProperOpen.openToS
  exact clopen_transport_word (o.extension j).adj
    (ProEtale.SemilinearProperOpen.jAdj (scalarRings l E) (scalarTransitions l E) j)
    (o.direct j).adj
    (ProEtale.SemilinearProperOpen.adj (scalarRings l E) (scalarTransitions l E) j)
    (b.pull l E j) M

attribute [local irreducible] presheafToSheaf constantSheaf
  ProEtale.SemilinearProperOpen.openToS ProEtale.SemilinearProperOpen.sComp

private theorem native_comp (o : Operations l E) (c : Compositors l E o)
    (b : CanonicalBridge l E o) {U X W : Scheme.{u}} (s : U ⟶ X) (q : X ⟶ W)
    (M : System l E U) :
    (c.pushComp l E s q).hom.app M ≫ (nativeBridge l E o b (s ≫ q)).hom.app M =
      (nativeBridge l E o b q).hom.app ((Operations.push l E o s).obj M) ≫
        (nativeR l E q).map ((nativeBridge l E o b s).hom.app M) ≫
        (nativeComp l E s q).hom.app M := by
  exact integralSystemBridgePushComposition l E o c b s q M

private theorem native_clopen (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    (M : System l E U) :
    (a.clopen s).hom.app M ≫ (nativeBridge l E o b s).hom.app M =
      (nativeShriek l E o b s).hom.app M ≫ (nativeOpen l E s).app M := by
  exact clopen_bridge l E o c a b s M

private theorem native_eq (o : Operations l E) (b : CanonicalBridge l E o)
    {X Y : Scheme.{u}} {s r : X ⟶ Y} (h : s = r) (M : System l E X) :
    (eqToIso (congrArg (Operations.push l E o) h)).hom.app M ≫
        (nativeBridge l E o b r).hom.app M =
      (nativeBridge l E o b s).hom.app M ≫
        nativeREq l E h M := by
  cases h
  unfold nativeREq
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, Category.comp_id]

attribute [local irreducible] nativeR nativeJ nativeBridge nativeShriek nativeOpen nativeComp
  nativeREq

private theorem native_tail (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    {U X W : Scheme.{u}} (s : U ⟶ X) (q : X ⟶ W) (r : U ⟶ W)
    [IsOpenImmersion s] [IsClosedImmersion s] (h : s ≫ q = r) (M : System l E U) :
    (Operations.push l E o q).map ((a.clopen s).hom.app M) ≫
        (c.pushComp l E s q).hom.app M ≫
        (eqToIso (congrArg (Operations.push l E o) h)).hom.app M ≫
        (nativeBridge l E o b r).hom.app M =
      (nativeBridge l E o b q).hom.app ((Operations.shriek l E o s).obj M) ≫
        (nativeR l E q).map ((nativeShriek l E o b s).hom.app M) ≫
        (nativeR l E q).map ((nativeOpen l E s).app M) ≫
        (nativeComp l E s q).hom.app M ≫
        nativeREq l E h M := by
  exact tail_pasting (A := System l E X) (B := System l E W)
    (Operations.push l E o q) (nativeR l E q) (nativeBridge l E o b q).hom
    ((a.clopen s).hom.app M) ((nativeShriek l E o b s).hom.app M)
    ((nativeOpen l E s).app M) ((nativeBridge l E o b s).hom.app M)
    ((c.pushComp l E s q).hom.app M)
    ((eqToIso (congrArg (Operations.push l E o) h)).hom.app M)
    ((nativeBridge l E o b r).hom.app M) ((nativeBridge l E o b (s ≫ q)).hom.app M)
    ((nativeComp l E s q).hom.app M)
    (nativeREq l E h M)
    (native_clopen l E o c a b s M) (native_eq l E o b h M)
    (native_comp l E o c b s q M)

/-- The clopen/compositor tail commutes with the canonical bridge.
Source: Stacks 0F7B and blueprint fix-prop-coherence.

Proof: Transport the inverse open unit by left-adjoint uniqueness. Its transpose under
the direct adjunction transports by conjugateIsoEquiv, giving the clopen square.
The normalized direct compositors agree on ordinary sections by pullbackComp;
conjugation and the prescribed cochain models lift the agreement to the derived
compositors. Equality induction handles the lift-composite equality. Map the
clopen square through the second projection, append this compositor square,
and use naturality of the direct bridge on the two component morphisms.
No cartesian or restriction factor is used.
(blueprint: lem-sf-integral-system-clopen-tail-bridge). -/
theorem clopenTail_bridge (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : System l E U) :
    let d := properOpenBridgeWord l E o c a b k r p i h M
    d.c ≫ d.d ≫ d.e ≫ d.v = d.j ≫ d.k ≫ d.z ≫ d.w ≫ d.n := by
  unfold properOpenBridgeWord
  exact native_tail l E o c a b (U := U) (X := pullback p i) (W := W)
    (ProEtale.StrictTower.squareLift k r p i h) (pullback.snd p i) r
    (pullback.lift_snd k r h) M

end WeilConjectures.IntegralSystemRealization

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import all WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemBridgePushComposition
import all WeilConjectures.CategoryTheory.SixFunctors.SystemProperOpenLambdaExchange

/-! Transport of the cartesian conjugate through the canonical bridge. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

private theorem mate_transport
    {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
    {L₁ L₁' : A ⥤ B} {R₁ R₁' : B ⥤ A}
    {L₂ L₂' : C ⥤ D} {R₂ R₂' : D ⥤ C}
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (a : L₁ ⊣ R₁) (a' : L₁' ⊣ R₁') (b : L₂ ⊣ R₂) (b' : L₂' ⊣ R₂')
    (e : L₁ ≅ L₁') (f : L₂ ≅ L₂') (g : G ≅ G') (h : H ≅ H')
    (α : G' ⋙ L₂' ⟶ L₁' ⋙ H') (M : B) :
    (mateEquiv a b (TwoSquare.mk _ _ _ _
      (Functor.whiskerRight g.hom L₂ ≫ Functor.whiskerLeft G' f.hom ≫ α ≫
        Functor.whiskerRight e.inv H' ≫ Functor.whiskerLeft L₁ h.inv))).app M ≫
        (conjugateIsoEquiv b b' f.symm).hom.app (H.obj M) ≫ R₂'.map (h.hom.app M) =
      g.hom.app (R₁.obj M) ≫ G'.map ((conjugateIsoEquiv a a' e.symm).hom.app M) ≫
        (mateEquiv a' b' (TwoSquare.mk _ _ _ _ α)).app M := by
  let w : TwoSquare G' L₁ L₂ H' := .mk _ _ _ _
    (Functor.whiskerLeft G' f.hom ≫ α ≫ Functor.whiskerRight e.inv H')
  have he : (TwoSquare.mk _ _ _ _ α).whiskerLeft e.inv =
      w.whiskerRight f.inv := by
    ext X
    simp [w, TwoSquare.whiskerLeft, TwoSquare.whiskerRight]
  have hh := mateEquiv_whiskerTop_conjugateEquiv a a' b b' e.inv f.inv w
    (TwoSquare.mk _ _ _ _ α) he
  have hs := mateEquiv_whiskerTop_whiskerBottom a b w g.hom h.inv
  have ht := congrArg (fun t ↦ t.app M) hs
  have hu := congrArg (fun t ↦ t.app M) hh
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    TwoSquare.whiskerLeft, TwoSquare.whiskerRight, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj] at ht hu
  dsimp only [w] at ht
  simp only [Category.assoc] at ht
  rw [ht]
  simp only [Category.assoc]
  rw [← (conjugateIsoEquiv b b' f.symm).hom.naturality]
  simp only [Functor.comp_obj, ← R₂.map_comp_assoc,
    Iso.inv_hom_id_app, R₂.map_id, Category.id_comp]
  exact congrArg (fun t ↦ g.hom.app (R₁.obj M) ≫ t) hu.symm

private theorem square_as_conjugate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ L₁' : A ⥤ B} {L₂ L₂' : C ⥤ D}
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (e : L₁ ≅ L₁') (f : L₂ ≅ L₂') (g : G ≅ G') (h : H ≅ H')
    (s : G ⋙ L₂ ≅ L₁ ⋙ H) (s' : G' ⋙ L₂' ≅ L₁' ⋙ H')
    (hs : s ≪≫ Functor.isoWhiskerLeft L₁ h ≪≫ Functor.isoWhiskerRight e H' =
      Functor.isoWhiskerLeft G f ≪≫ Functor.isoWhiskerRight g L₂' ≪≫ s') :
    s.hom = Functor.whiskerRight g.hom L₂ ≫ Functor.whiskerLeft G' f.hom ≫ s'.hom ≫
      Functor.whiskerRight e.inv H' ≫ Functor.whiskerLeft L₁ h.inv := by
  have hh := congrArg Iso.hom hs
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom] at hh
  apply (cancel_mono
    (Functor.whiskerLeft L₁ h.hom ≫ Functor.whiskerRight e.hom H')).1
  ext X
  have hx := congr_app hh X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] at hx ⊢
  simp only [Iso.inv_hom_id_app_assoc, ← H'.map_comp, Iso.inv_hom_id_app,
    H'.map_id]
  rw [f.hom.naturality_assoc]
  simpa only [Functor.comp_obj, Category.comp_id] using hx

private theorem cartesian_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ L₁' : A ⥤ B} {R₁ R₁' : B ⥤ A}
    {L₂ L₂' : C ⥤ D} {R₂ R₂' : D ⥤ C}
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (a : L₁ ⊣ R₁) (a' : L₁' ⊣ R₁') (b : L₂ ⊣ R₂) (b' : L₂' ⊣ R₂')
    (e : L₁ ≅ L₁') (f : L₂ ≅ L₂') (g : G ≅ G') (h : H ≅ H')
    (s : G ⋙ L₂ ≅ L₁ ⋙ H) (s' : G' ⋙ L₂' ≅ L₁' ⋙ H')
    (hs : s ≪≫ Functor.isoWhiskerLeft L₁ h ≪≫ Functor.isoWhiskerRight e H' =
      Functor.isoWhiskerLeft G f ≪≫ Functor.isoWhiskerRight g L₂' ≪≫ s')
    (d₁ : R₁ ≅ R₁') (d₂ : R₂ ≅ R₂')
    (hd₁ : d₁ = conjugateIsoEquiv a a' e.symm)
    (hd₂ : d₂ = conjugateIsoEquiv b b' f.symm)
    (θ : R₁ ⋙ G ⟶ H ⋙ R₂) (θ' : R₁' ⋙ G' ⟶ H' ⋙ R₂')
    (hθ : θ = (mateEquiv a b (TwoSquare.mk _ _ _ _ s.hom)))
    (hθ' : θ' = (mateEquiv a' b' (TwoSquare.mk _ _ _ _ s'.hom)))
    (M : B) :
    θ.app M ≫ d₂.hom.app (H.obj M) ≫ R₂'.map (h.hom.app M) =
      g.hom.app (R₁.obj M) ≫ G'.map (d₁.hom.app M) ≫ θ'.app M := by
  subst d₁
  subst d₂
  subst θ
  subst θ'
  rw [square_as_conjugate e f g h s s' hs]
  exact mate_transport a a' b b' e f g h s'.hom M

namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

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

private theorem iso_transport {A : Type*} {C : Type*} [Category C]
    (F G : A → C) (e : ∀ a, F a ≅ G a) {a b : A} (h : a = b) :
    eqToIso (congrArg F h) ≪≫ e b = e a ≪≫ eqToIso (congrArg G h) := by
  subst b
  simp

private theorem composition_forward {A B C : Type*}
    [Category A] [Category B] [Category C]
    {Lf Pf : B ⥤ A} {Lg Pg : C ⥤ B} {Lh Ph : C ⥤ A}
    (f : Lf ≅ Pf) (g : Lg ≅ Pg) (h : Lh ≅ Ph)
    (s : Lh ≅ Lg ⋙ Lf) (r : Ph ≅ Pg ⋙ Pf)
    (H : h.symm ≪≫ s = r ≪≫ Functor.isoWhiskerLeft Pg f.symm ≪≫
      Functor.isoWhiskerRight g.symm Lf) :
    s.hom ≫ Functor.whiskerLeft Lg f.hom ≫ Functor.whiskerRight g.hom Pf =
      h.hom ≫ r.hom := by
  have hh := congrArg Iso.hom H
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom] at hh
  apply (cancel_epi h.inv).1
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hh]
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc]
  rw [f.hom.naturality_assoc]
  simp only [← Pf.map_comp, Iso.inv_hom_id_app, Pf.map_id, Iso.inv_hom_id_app_assoc]
  exact Category.comp_id _

private theorem path_square {C : Type*} [Category C]
    {A B D F G H I J : C} (c₁ : A ≅ B) (c₂ : D ≅ F) (p₁ : G ≅ H)
    (p₂ : I ≅ J) (e₁ : B ⟶ H) (e₂ : F ⟶ J)
    (b₁ : A ⟶ G) (b₂ : D ⟶ I) (q : A ⟶ D) (q' : G ⟶ I)
    (h₁ : c₁.hom ≫ e₁ = b₁ ≫ p₁.hom)
    (h₂ : c₂.hom ≫ e₂ = b₂ ≫ p₂.hom)
    (hq : q ≫ b₂ = b₁ ≫ q') :
    c₁.inv ≫ q ≫ c₂.hom ≫ e₂ = e₁ ≫ p₁.inv ≫ q' ≫ p₂.hom := by
  apply (cancel_epi c₁.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [h₁]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [h₂, reassoc_of% hq]

private theorem path_square_iso {C : Type*} [Category C]
    {A B D F G H I J K L : C} (c₁ : A ≅ B) (c₂ : D ≅ F) (p₁ : G ≅ H)
    (p₂ : I ≅ J) (e₁a : B ≅ K) (e₁b : K ≅ H) (e₂a : F ≅ L) (e₂b : L ≅ J)
    (b₁ : A ⟶ G) (b₂ : D ⟶ I) (q : A ≅ D) (q' : G ≅ I)
    (h₁ : c₁.hom ≫ e₁a.hom ≫ e₁b.hom = b₁ ≫ p₁.hom)
    (h₂ : c₂.hom ≫ e₂a.hom ≫ e₂b.hom = b₂ ≫ p₂.hom)
    (hq : q.hom ≫ b₂ = b₁ ≫ q'.hom) :
    (c₁.symm ≪≫ q ≪≫ c₂) ≪≫ e₂a ≪≫ e₂b =
      e₁a ≪≫ e₁b ≪≫ (p₁.symm ≪≫ q' ≪≫ p₂) := by
  apply Iso.ext
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using
    path_square c₁ c₂ p₁ p₂ (e₁a.hom ≫ e₁b.hom) (e₂a.hom ≫ e₂b.hom)
      b₁ b₂ q.hom q'.hom h₁ h₂ hq

private theorem square_bridge (o : Operations l E) (c : Compositors l E o)
    (b : CanonicalBridge l E o) {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) :
    c.square l E k r p i h ≪≫
        Functor.isoWhiskerLeft (pull l E p) (b.pull l E k) ≪≫
        Functor.isoWhiskerRight (b.pull l E p)
          (ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E) k) =
      Functor.isoWhiskerLeft (pull l E i) (b.pull l E r) ≪≫
        Functor.isoWhiskerRight (b.pull l E i)
          (ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E) r) ≪≫
        ProEtale.SemilinearProperOpen.squareP
          (scalarRings l E) (scalarTransitions l E) k r p i h := by
  have hk := composition_forward
    (A := System l E U) (B := System l E V) (C := System l E Z)
    (b.pull l E k) (b.pull l E p) (b.pull l E (k ≫ p))
    (c.pullComp k p)
    (ProEtale.SemilinearProperOpen.pComp (scalarRings l E) (scalarTransitions l E) k p)
    (pull_bridge_composition l E o c b k p)
  have hr := composition_forward
    (A := System l E U) (B := System l E W) (C := System l E Z)
    (b.pull l E r) (b.pull l E i) (b.pull l E (r ≫ i))
    (c.pullComp r i)
    (ProEtale.SemilinearProperOpen.pComp (scalarRings l E) (scalarTransitions l E) r i)
    (pull_bridge_composition l E o c b r i)
  have he := congrArg Iso.hom (iso_transport (C := System l E Z ⥤ System l E U) (pull l E)
    (ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E))
    (fun f ↦ b.pull l E f) h.symm)
  unfold Compositors.square ProEtale.SemilinearProperOpen.squareP
  exact path_square_iso (C := System l E Z ⥤ System l E U) (c.pullComp r i) (c.pullComp k p)
    (ProEtale.SemilinearProperOpen.pComp (scalarRings l E) (scalarTransitions l E) r i)
    (ProEtale.SemilinearProperOpen.pComp (scalarRings l E) (scalarTransitions l E) k p)
    (Functor.isoWhiskerLeft (pull l E i) (b.pull l E r))
    (Functor.isoWhiskerRight (b.pull l E i)
      (ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E) r))
    (Functor.isoWhiskerLeft (pull l E p) (b.pull l E k))
    (Functor.isoWhiskerRight (b.pull l E p)
      (ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E) k))
    _ _ _ _ hr hk he

private theorem cartesian_eq_exchange (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {V W Z : Scheme.{u}}
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion i] :
    (cartesianConjugate l E o c a p i).hom =
      properExchange l E o c (pullback.fst p i) (pullback.snd p i) p i
        pullback.condition := by
  exact (cartesian_mate l E c a p i).symm

private theorem intrinsic_cartesian_eq_exchange {V W Z : Scheme.{u}}
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion i] :
    (ProEtale.SemilinearProperOpen.cartesianConjugate
      (scalarRings l E) (scalarTransitions l E) p i).hom =
      ProEtale.SemilinearProperOpen.exchange (scalarRings l E) (scalarTransitions l E)
        (pullback.fst p i) (pullback.snd p i) p i pullback.condition := by
  exact (cartesian_mate_generic
    (ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) i)
    (ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E) i)
    (ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E)
      (pullback.fst p i))
    (ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E)
      (pullback.fst p i))
    (ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E) p)
    (ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) p)
    (ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E)
      (pullback.snd p i))
    (ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E)
      (pullback.snd p i))
    (ProEtale.SemilinearProperOpen.jAdj (scalarRings l E) (scalarTransitions l E) i)
    (ProEtale.SemilinearProperOpen.jAdj (scalarRings l E) (scalarTransitions l E)
      (pullback.fst p i))
    (ProEtale.SemilinearProperOpen.adj (scalarRings l E) (scalarTransitions l E) p)
    (ProEtale.SemilinearProperOpen.adj (scalarRings l E) (scalarTransitions l E)
      (pullback.snd p i))
    (ProEtale.SemilinearProperOpen.beta (scalarRings l E) (scalarTransitions l E)
      (pullback.snd p i) (pullback.fst p i) i p pullback.condition.symm
      (IsPullback.of_hasPullback p i).flip)
    (ProEtale.SemilinearProperOpen.squareP (scalarRings l E) (scalarTransitions l E)
      (pullback.fst p i) (pullback.snd p i) p i pullback.condition)
    (fun M ↦ by
      have hs : (ProEtale.SemilinearProperOpen.squareP
          (scalarRings l E) (scalarTransitions l E) (pullback.fst p i)
          (pullback.snd p i) p i pullback.condition).hom =
          (ProEtale.SemilinearProperOpen.squareP
            (scalarRings l E) (scalarTransitions l E) (pullback.snd p i)
            (pullback.fst p i) i p pullback.condition.symm).inv := by
        simp only [ProEtale.SemilinearProperOpen.squareP, Iso.trans_hom, Iso.trans_inv,
          Iso.symm_hom, Iso.symm_inv, eqToIso.inv, eqToIso.hom, Category.assoc]
      rw [hs]
      change (ProEtale.SemilinearProperOpen.jAdj
        (scalarRings l E) (scalarTransitions l E) (pullback.fst p i)).homEquiv _ _
          (ProEtale.SemilinearProperOpen.betaInvApp
            (scalarRings l E) (scalarTransitions l E) (pullback.snd p i)
            (pullback.fst p i) i p pullback.condition.symm M) = _
      exact Equiv.apply_symm_apply _ _)).symm

attribute [local irreducible] mateEquiv conjugateIsoEquiv
  cartesianConjugate properExchange
  ProEtale.SemilinearProperOpen.cartesianConjugate ProEtale.SemilinearProperOpen.exchange

/-- The cartesian conjugate is compatible with the canonical bridge.
Source: Stacks 07A7 and 0F7B; blueprint fix-prop-coherence.
Proof: compare the two pull-composition paths using pull_bridge_composition and
naturality of equality transport. The mate-whiskering identities carry that square
through the pull comparisons and the conjugate push comparisons. The adjunction
triangle identities identify both cartesian conjugates with those mates.
(blueprint: lem-sf-integral-system-cartesian-bridge-transport). -/
theorem cartesianBridge_transport (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    {V W Z : Scheme.{u}} (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion i]
    (M : System l E V) :
    (cartesianConjugate l E o c a p i).hom.app M ≫
        (b.push l E (pullback.snd p i)).hom.app
          ((pull l E (pullback.fst p i)).obj M) ≫
        (ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E)
          (pullback.snd p i)).map ((b.pull l E (pullback.fst p i)).hom.app M) =
      (b.pull l E i).hom.app ((Operations.push l E o p).obj M) ≫
        (ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E) i).map
          ((b.push l E p).hom.app M) ≫
        (ProEtale.SemilinearProperOpen.cartesianConjugate
          (scalarRings l E) (scalarTransitions l E) p i).hom.app M := by
  exact cartesian_transport (o.direct p).adj
    (ProEtale.SemilinearProperOpen.adj (scalarRings l E) (scalarTransitions l E) p)
    (o.direct (pullback.snd p i)).adj
    (ProEtale.SemilinearProperOpen.adj (scalarRings l E) (scalarTransitions l E)
      (pullback.snd p i))
    (b.pull l E p) (b.pull l E (pullback.snd p i))
    (b.pull l E i) (b.pull l E (pullback.fst p i))
    (c.square l E (pullback.fst p i) (pullback.snd p i) p i pullback.condition)
    (ProEtale.SemilinearProperOpen.squareP (scalarRings l E) (scalarTransitions l E)
      (pullback.fst p i) (pullback.snd p i) p i pullback.condition)
    (square_bridge l E o c b _ _ _ _ _)
    (b.push l E p) (b.push l E (pullback.snd p i))
    (by unfold CanonicalBridge.push; rfl) (by unfold CanonicalBridge.push; rfl)
    (cartesianConjugate l E o c a p i).hom
    (ProEtale.SemilinearProperOpen.cartesianConjugate
      (scalarRings l E) (scalarTransitions l E) p i).hom
    (by simpa only [properExchange] using cartesian_eq_exchange l E o c a p i)
    (by
      have hh := intrinsic_cartesian_eq_exchange l E p i
      unfold ProEtale.SemilinearProperOpen.exchange at hh
      exact hh) M

end WeilConjectures.IntegralSystemRealization

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.IntegralSystemProperOpenTransportAdjunct
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! Normalized mate used by the canonical proper/open transport equation. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

/-- Transport a mate across comparison isomorphisms of the two adjunctions and the
vertical functors.

Source: Stacks Project, Tags 07A7 and 0F7B; the mate transport calculation used in
canonical proper/open bridge coordinates.
Proof: factor the square through the middle comparison square, apply the mate
whiskering and conjugation identities, then use naturality of the conjugated
comparison and the inverse/hom cancellation of the vertical isomorphism. -/
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

private theorem mate_transport_with_data
    {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
    {L₁ L₁' : A ⥤ B} {R₁ R₁' : B ⥤ A}
    {L₂ L₂' : C ⥤ D} {R₂ R₂' : D ⥤ C}
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (a : L₁ ⊣ R₁) (a' : L₁' ⊣ R₁') (b : L₂ ⊣ R₂) (b' : L₂' ⊣ R₂')
    (e : L₁ ≅ L₁') (f : L₂ ≅ L₂') (g : G ≅ G') (h : H ≅ H')
    (α : G' ⋙ L₂' ⟶ L₁' ⋙ H')
    (d₁ : R₁ ≅ R₁') (d₂ : R₂ ≅ R₂')
    (δ : R₁' ⋙ G' ⟶ H' ⋙ R₂') (m : R₁ ⋙ G ⟶ H ⋙ R₂)
    (h₁ : d₁ = conjugateIsoEquiv a a' e.symm)
    (h₂ : d₂ = conjugateIsoEquiv b b' f.symm)
    (hδ : δ = (mateEquiv a' b' (TwoSquare.mk _ _ _ _ α)))
    (hm : m = (mateEquiv a b (TwoSquare.mk _ _ _ _
      (Functor.whiskerRight g.hom L₂ ≫ Functor.whiskerLeft G' f.hom ≫ α ≫
        Functor.whiskerRight e.inv H' ≫ Functor.whiskerLeft L₁ h.inv))))
    (M : B) :
    m.app M = G.map (d₁.hom.app M) ≫ g.hom.app (R₁'.obj M) ≫
      δ.app M ≫ d₂.inv.app (H'.obj M) ≫ R₂.map (h.inv.app M) := by
  have ht : m.app M ≫ d₂.hom.app (H.obj M) ≫ R₂'.map (h.hom.app M) =
      g.hom.app (R₁.obj M) ≫ G'.map (d₁.hom.app M) ≫ δ.app M := by
    subst d₁
    subst d₂
    subst δ
    subst m
    exact mate_transport a a' b b' e f g h α M
  apply (cancel_mono (d₂.hom.app (H.obj M) ≫ R₂'.map (h.hom.app M))).1
  simp only [Category.assoc]
  rw [d₂.hom.naturality_assoc]
  simp only [← R₂'.map_comp, Iso.inv_hom_id_app, R₂'.map_id, Category.comp_id]
  rw [g.hom.naturality_assoc]
  simpa using ht

namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The transported mate of the intrinsic semilinear alpha in bridge coordinates.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 07A7.
(blueprint: lem-sf-integral-system-proper-open-transport-core-canonical-mate).
Proof: expand the mate under the four canonical bridge isomorphisms and use the
adjunction-conjugacy formula. -/
def properOpenTransportMate (o : Operations l E) (b : CanonicalBridge l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    Operations.push l E o r ⋙ Operations.shriek l E o i ⟶
      Operations.shriek l E o k ⋙ Operations.push l E o p :=
  (mateEquiv (o.direct r).adj (o.direct p).adj (TwoSquare.mk _ _ _ _
    (Functor.whiskerRight (b.shriek l E i).hom (pull l E p) ≫
      Functor.whiskerLeft (ProEtale.SemilinearProperOpen.J
        (scalarRings l E) (scalarTransitions l E) i) (b.pull l E p).hom ≫
      ProEtale.SemilinearProperOpen.alpha (scalarRings l E)
        (scalarTransitions l E) k r p i h ≫
      Functor.whiskerRight (b.pull l E r).inv
        (ProEtale.SemilinearProperOpen.J
          (scalarRings l E) (scalarTransitions l E) k) ≫
      Functor.whiskerLeft (pull l E r) (b.shriek l E k).inv)))

section
variable {U V W Z : Scheme.{u}}

private def modelPull (f : U ⟶ V) : System l E V ⥤ System l E U :=
  ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E) f

private def modelPush (f : U ⟶ V) : System l E U ⥤ System l E V :=
  ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) f

private def modelShriek (j : U ⟶ V) [IsOpenImmersion j] : System l E U ⥤ System l E V :=
  ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) j

private def modelAdj (f : U ⟶ V) : modelPull l E f ⊣ modelPush l E f :=
  ProEtale.SemilinearProperOpen.adj (scalarRings l E) (scalarTransitions l E) f

variable (o : Operations l E) (b : CanonicalBridge l E o)

private def modelBridgePull (f : U ⟶ V) : pull l E f ≅ modelPull l E f :=
  b.pull l E f

private def modelBridgePush (f : U ⟶ V) : Operations.push l E o f ≅ modelPush l E f :=
  b.push l E f

private def modelBridgeShriek (j : U ⟶ V) [IsOpenImmersion j] :
    Operations.shriek l E o j ≅ modelShriek l E j :=
  b.shriek l E j

private theorem bridge_push_normalized (f : U ⟶ V) : modelBridgePush l E o b f =
    conjugateIsoEquiv (o.direct f).adj (modelAdj l E f)
      (modelBridgePull l E o b f).symm := by
  rfl

variable (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
  [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
  [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)

private def modelAlpha : modelShriek l E i ⋙ modelPull l E p ⟶
    modelPull l E r ⋙ modelShriek l E k :=
  ProEtale.SemilinearProperOpen.alpha (scalarRings l E) (scalarTransitions l E) k r p i h

private def modelMate : modelPush l E r ⋙ modelShriek l E i ⟶
    modelShriek l E k ⋙ modelPush l E p :=
  (mateEquiv (ProEtale.SemilinearProperOpen.adj (scalarRings l E) (scalarTransitions l E) r)
    (ProEtale.SemilinearProperOpen.adj (scalarRings l E) (scalarTransitions l E) p)
      (TwoSquare.mk _ _ _ _ (ProEtale.SemilinearProperOpen.alpha
        (scalarRings l E) (scalarTransitions l E) k r p i h)))

private theorem model_mate_normalized : modelMate l E k r p i h =
    (mateEquiv (modelAdj l E r) (modelAdj l E p)
      (TwoSquare.mk _ _ _ _ (modelAlpha l E k r p i h))) := by
  unfold modelMate modelAdj modelAlpha
  rfl

private theorem transport_mate_normalized : properOpenTransportMate l E o b k r p i h =
    (mateEquiv (o.direct r).adj (o.direct p).adj (TwoSquare.mk _ _ _ _
      (Functor.whiskerRight (modelBridgeShriek l E o b i).hom (pull l E p) ≫
        Functor.whiskerLeft (modelShriek l E i) (modelBridgePull l E o b p).hom ≫
        modelAlpha l E k r p i h ≫
        Functor.whiskerRight (modelBridgePull l E o b r).inv (modelShriek l E k) ≫
        Functor.whiskerLeft (pull l E r) (modelBridgeShriek l E o b k).inv))) := by
  unfold properOpenTransportMate modelBridgeShriek modelBridgePull modelAlpha modelShriek
  rfl

private theorem model_mate_gamma : modelMate l E k r p i h =
    ProEtale.SemilinearProperOpen.gamma (scalarRings l E) (scalarTransitions l E)
      k r p i h := by
  unfold modelMate ProEtale.SemilinearProperOpen.gamma
  rfl

attribute [local irreducible] modelPull modelPush modelShriek modelAdj
  modelBridgePull modelBridgePush modelBridgeShriek modelAlpha modelMate
  Direct.adj CanonicalBridge.push properOpenTransportMate
end

/-- Identify the transported mate with the explicit bridge transport of gamma.
The generic calculation above is instantiated with the canonical conjugate push
isomorphisms. The intrinsic gamma is definitionally the mate of alpha. -/
private theorem canonicalMate_eq_transportedGamma
    (o : Operations l E) (b : CanonicalBridge l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : System l E U) :
    (properOpenTransportMate l E o b k r p i h).app M =
      (transportedGamma l E o b k r p i h).app M := by
  simpa only [transportedGamma, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, modelBridgePush, modelBridgeShriek,
    modelPush, modelShriek, model_mate_gamma, Category.assoc] using
  @mate_transport_with_data
    (System l E W) (System l E U) (System l E Z) (System l E V)
    (inferInstanceAs (Category.{u + 2} (System l E W)))
    (inferInstanceAs (Category.{u + 2} (System l E U)))
    (inferInstanceAs (Category.{u + 2} (System l E Z)))
    (inferInstanceAs (Category.{u + 2} (System l E V)))
    (pull l E r) (modelPull l E r) (Operations.push l E o r) (modelPush l E r)
    (pull l E p) (modelPull l E p) (Operations.push l E o p) (modelPush l E p)
    (Operations.shriek l E o i) (modelShriek l E i)
    (Operations.shriek l E o k) (modelShriek l E k)
    (o.direct r).adj (modelAdj l E r) (o.direct p).adj (modelAdj l E p)
    (modelBridgePull l E o b r) (modelBridgePull l E o b p)
    (modelBridgeShriek l E o b i) (modelBridgeShriek l E o b k)
    (modelAlpha l E k r p i h)
    (modelBridgePush l E o b r) (modelBridgePush l E o b p)
    (modelMate l E k r p i h) (properOpenTransportMate l E o b k r p i h)
    (bridge_push_normalized l E o b r) (bridge_push_normalized l E o b p)
    (model_mate_normalized l E k r p i h)
    (transport_mate_normalized l E o b k r p i h) M

/-- The transported mate has the prescribed proper/open adjunct.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 07A7.
(blueprint: lem-sf-integral-system-proper-open-transport-core-canonical-mate-adjunct).
Proof: expand the mate under the canonical bridge, transpose with the open
adjunction, and cancel the bridge isomorphisms against the defining proper/open
lambda. The resulting equation is the adjunct characterization of the displayed
transported mate. -/
theorem properOpenTransportMate_adjunct (o : Operations l E)
    (c : Compositors l E o) (a : OpenComparisons l E o c)
    (b : CanonicalBridge l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : System l E U) :
    (o.extension i).adj.homEquiv _ _
        ((properOpenTransportMate l E o b k r p i h).app M) =
      (properOpenLambda l E o c a k r p i h).inv.app M := by
  rw [canonicalMate_eq_transportedGamma l E o b k r p i h M]
  exact transportedGamma_adjunct l E o c a b k r p i h M

/-- The adjunct-normalized gamma is this transported mate.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 07A7.
(blueprint: lem-sf-integral-system-proper-open-transport-core-canonical-mate-normalized).
Proof: transpose the gamma with the chosen open adjunction, identify its prescribed
proper/open lambda, and apply uniqueness of mates after canonical bridge transport. -/
theorem properOpenTransportMate_normalized (o : Operations l E)
    (c : Compositors l E o) (a : OpenComparisons l E o c)
    (b : CanonicalBridge l E o)
    (h₀ : ProperOpenTransportAdjunct l E o c a b)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : System l E U) :
    (h₀.gamma k r p i h).app M =
      (properOpenTransportMate l E o b k r p i h).app M := by
  apply ((o.extension i).adj.homEquiv _ _).injective
  rw [h₀.adjunct k r p i h M]
  exact (properOpenTransportMate_adjunct l E o c a b k r p i h M).symm

end WeilConjectures.IntegralSystemRealization

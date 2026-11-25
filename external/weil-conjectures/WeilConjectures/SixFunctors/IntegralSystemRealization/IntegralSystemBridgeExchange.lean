/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
import all WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemBridgePushComposition

/-! # Canonical bridge comparison for a single proper exchange

Source: Stacks 07A7; blueprint fix-prop-coherence, coefficient comparisons of
adjunction units and counits (blueprint: lem-sf-integral-system-bridge-exchange).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf HasDerivedCategory.standard DerivedCategory.Q
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryNatIso
  ProEtale.SemilinearProperOpen.pushComp
  pullbackTensorSequenceAdjunction ProEtale.SemilinearProperOpen.ordinaryAdj
  Adjunction.leftAdjointUniq Adjunction.ofNatIsoRight

attribute [local implicit_reducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition integralCoefficientCommRingSheaf
  integralCoefficientSheaf integralCoefficientSheafTransition
  WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf WeilConjectures.SemilinearSections.rings
  sheafCompose ProEtale.SemilinearProperOpen.derived
  RingHom.ulift

attribute [local irreducible] pullbackTensorSequenceDirect pullbackTensorSequenceInverse
  ProEtale.SemilinearProperOpen.push

private def bridgePair {A B C : Type*} [Category A] [Category B] [Category C]
    {F F' : A ⥤ B} {G G' : B ⥤ C} (e : F ≅ F') (f : G ≅ G') :
    F ⋙ G ≅ F' ⋙ G' :=
  Functor.isoWhiskerRight e G ≪≫ Functor.isoWhiskerLeft F' f

private theorem mateBridge
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ L₁' : A ⥤ B} {R₁ R₁' : B ⥤ A}
    {L₂ L₂' : C ⥤ D} {R₂ R₂' : D ⥤ C} {G G' : A ⥤ C} {H H' : B ⥤ D}
    (a : L₁ ⊣ R₁) (a' : L₁' ⊣ R₁') (b : L₂ ⊣ R₂) (b' : L₂' ⊣ R₂')
    (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂') (eg : G ≅ G') (eh : H ≅ H')
    (α : TwoSquare G L₁ L₂ H) (β : TwoSquare G' L₁' L₂' H')
    (h : α ≫ (bridgePair e₁ eh).hom = (bridgePair eg e₂).hom ≫ β)
    (M : B) :
    (mateEquiv a b α).app M ≫
        (conjugateIsoEquiv b b' e₂.symm).hom.app (H.obj M) ≫
        R₂'.map (eh.hom.app M) =
      eg.hom.app (R₁.obj M) ≫ G'.map ((conjugateIsoEquiv a a' e₁.symm).hom.app M) ≫
        (mateEquiv a' b' β).app M := by
  let w := (β.whiskerTop eg.hom).whiskerBottom eh.inv
  have hw : w.whiskerLeft e₁.inv = α.whiskerRight e₂.inv := by
    refine NatTrans.ext (funext fun X ↦ ?_)
    have hx := congr_app h X
    simp only [bridgePair, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc] at hx
    dsimp only [w, TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
      TwoSquare.whiskerRight, TwoSquare.mk, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app]
    apply (cancel_epi (e₂.hom.app (G.obj X))).mp
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← e₂.hom.naturality_assoc, ← reassoc_of% hx]
    simp only [Iso.hom_inv_id_app_assoc, ← H.map_comp,
      Iso.hom_inv_id_app, H.map_id, Category.comp_id]
  have hm := mateEquiv_whiskerTop_conjugateEquiv a a' b b'
    e₁.inv e₂.inv α w hw
  have hn := mateEquiv_whiskerTop_whiskerBottom a' b' β eg.hom eh.inv
  have hh := congr_app hm M
  rw [hn] at hh
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] at hh
  simp only [conjugateIsoEquiv_apply_hom, Iso.symm_hom]
  rw [← Category.assoc, ← hh]
  simp only [Category.assoc, ← R₂'.map_comp, Iso.inv_hom_id_app,
    R₂'.map_id]
  dsimp only [Functor.comp_obj] at *
  simpa only [Category.comp_id] using
    eg.hom.naturality_assoc ((conjugateEquiv a a' e₁.inv).app M)
      ((mateEquiv a' b' β).app M)

private theorem bridgePullComp (o : Operations l E) (c : Compositors l E o)
    (b : CanonicalBridge l E o) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    c.pullComp f g ≪≫ bridgePair (b.pull l E g) (b.pull l E f) =
      b.pull l E (f ≫ g) ≪≫
        ProEtale.SemilinearProperOpen.pComp (scalarRings l E) (scalarTransitions l E) f g := by
  have h := pull_bridge_composition l E o c b f g
  change (b.pull l E (f ≫ g)).symm ≪≫ c.pullComp f g =
    ProEtale.SemilinearProperOpen.pComp (scalarRings l E) (scalarTransitions l E) f g ≪≫
      (bridgePair (b.pull l E g) (b.pull l E f)).symm at h
  calc
    _ = b.pull l E (f ≫ g) ≪≫
        ((b.pull l E (f ≫ g)).symm ≪≫ c.pullComp f g) ≪≫
        bridgePair (b.pull l E g) (b.pull l E f) := by simp [Iso.trans_assoc]
    _ = _ := by rw [h]; simp [Iso.trans_assoc]

private theorem inverseSquare' {C : Type*} [Category C] {A B D E : C}
    (r : A ≅ B) (s : D ≅ E) (q : A ⟶ D) (t : B ⟶ E)
    (h : r.hom ≫ t = q ≫ s.hom) : r.inv ≫ q = t ≫ s.inv := by
  apply (cancel_epi r.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, h]
  simp

private theorem bridgePullCongr (o : Operations l E) (b : CanonicalBridge l E o)
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (b.pull l E f).hom ≫ (eqToIso (congrArg
      (ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E)) h)).hom =
    (eqToIso (congrArg (pull l E) h)).hom ≫ (b.pull l E g).hom := by
  subst g
  simp

private theorem bridgePullSquare (o : Operations l E) (c : Compositors l E o)
    (b : CanonicalBridge l E o) {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) :
    (c.square l E k r p i h).hom ≫
        (bridgePair (b.pull l E p) (b.pull l E k)).hom =
      (bridgePair (b.pull l E i) (b.pull l E r)).hom ≫
        (ProEtale.SemilinearProperOpen.squareP (scalarRings l E)
          (scalarTransitions l E) k r p i h).hom := by
  have hk := congrArg Iso.hom (bridgePullComp l E o c b k p)
  have hr := congrArg Iso.hom (bridgePullComp l E o c b r i)
  simp only [Iso.trans_hom] at hk hr
  have hr' := inverseSquare' (c.pullComp r i)
    (ProEtale.SemilinearProperOpen.pComp (scalarRings l E) (scalarTransitions l E) r i)
    (b.pull l E (r ≫ i)).hom
    (bridgePair (b.pull l E i) (b.pull l E r)).hom hr
  have hw := bridgePullCongr l E o b h.symm
  simp only [Compositors.square, ProEtale.SemilinearProperOpen.squareP,
    Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [hk, ← reassoc_of% hw]
  rw [← Category.assoc (c.pullComp r i).inv (b.pull l E (r ≫ i)).hom, hr']
  simp only [Category.assoc]

private meta def transportCompObj (x : Lean.Expr) :
    Lean.MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let args := x.getAppArgs
  if x.isAppOf ``Functor.obj && args.size ≥ 2 then
    let f := args[args.size - 2]!
    if f.isAppOf ``Functor.comp then
      let fs := f.getAppArgs
      let h ← Lean.Meta.mkAppM ``Functor.comp_obj
        #[fs[fs.size - 2]!, fs.back!, args.back!]
      return some ((← Lean.Meta.inferType h).getAppArgs.back!,
        ← Lean.Meta.mkHEqOfEq h)
  return none

private meta partial def transportCongruence (x y : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let x := x.consumeMData
  let y := y.consumeMData
  if x == y then return ← Lean.Meta.mkHEqRefl x
  if let some (x', h) ← transportCompObj x then
    return ← Lean.Meta.mkAppM ``HEq.trans #[h, ← transportCongruence x' y]
  if let some (y', h) ← transportCompObj y then
    return ← Lean.Meta.mkAppM ``HEq.trans
      #[← transportCongruence x y', ← Lean.Meta.mkAppM ``HEq.symm #[h]]
  if (← Lean.Meta.isProof x) && (← Lean.Meta.isProof y) then
    return ← Lean.Meta.mkAppM ``proof_irrel_heq #[x, y]
  if x.getAppFn == y.getAppFn && x.isApp && x.getAppNumArgs == y.getAppNumArgs then
    let thm ← Lean.Meta.mkHCongrWithArity x.getAppFn x.getAppNumArgs
    let mut args := #[]
    for a in x.getAppArgs, b in y.getAppArgs, kind in thm.argKinds do
      let h ← transportCongruence a b
      match kind with
      | .eq => args := args ++ #[a, b, ← Lean.Meta.mkEqOfHEq h]
      | .heq => args := args ++ #[a, b, h]
      | _ => throwError "Unexpected congruence argument"
    let h := Lean.mkAppN thm.proof args
    if (← Lean.Meta.inferType h).isHEq then return h
    return ← Lean.Meta.mkHEqOfEq h
  return ← Lean.Meta.mkHEqRefl x

attribute [local irreducible] CanonicalBridge.pull CanonicalBridge.push
  properExchange ProEtale.SemilinearProperOpen.exchange

-- Fix the category presentation once, rather than repeatedly converting between
-- the two definitionally equal presentations in a large diagram proof.
/-- The canonical bridge intertwines the proper-adjunction exchange for one square.
Source: Stacks 07A7; blueprint fix-prop-coherence, transport of adjunction units and
counits (blueprint: lem-sf-integral-system-bridge-exchange).

Proof: the section identities for the ordinary bridge and the ordinary compositor
identify their two composites on every section. Transpose through the ordinary
pullback adjunctions, then localize the equality on complexes. The recorded
pullComp_model equations identify the resulting derived square with c.square.
Conjugating through the direct adjunctions identifies its mate with the intrinsic
exchange. The bridge push comparison is exactly this adjoint conjugate of bridge
pull, so the mate's unit and counit squares give the displayed equation. No
cartesianness, proper base-change invertibility, or faithfulness of finite
evaluation is used. Identity and empty squares obey the same mate calculation. -/
theorem integralSystemBridgeExchange (o : Operations l E) (c : Compositors l E o)
    (b : CanonicalBridge l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) (h : k ≫ p = r ≫ i) (M : System l E V) :
    (properExchange l E o c k r p i h).app M ≫
        (b.push l E r).hom.app ((pull l E k).obj M) ≫
        (ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) r).map
          ((b.pull l E k).hom.app M) =
      (b.pull l E i).hom.app ((Operations.push l E o p).obj M) ≫
        (ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E) i).map
          ((b.push l E p).hom.app M) ≫
        (ProEtale.SemilinearProperOpen.exchange (scalarRings l E) (scalarTransitions l E)
          k r p i h).app M := by
  have hx := mateBridge (o.direct p).adj
    (ProEtale.SemilinearProperOpen.adj (scalarRings l E) (scalarTransitions l E) p)
    (o.direct r).adj
    (ProEtale.SemilinearProperOpen.adj (scalarRings l E) (scalarTransitions l E) r)
    (b.pull l E p) (b.pull l E r) (b.pull l E i) (b.pull l E k)
    (c.square l E k r p i h).hom
    (ProEtale.SemilinearProperOpen.squareP (scalarRings l E)
      (scalarTransitions l E) k r p i h).hom
    (bridgePullSquare l E o c b k r p i h) M
  run_tac Lean.Elab.Tactic.withMainContext do
    let some hd := (← Lean.getLCtx).findFromUserName? `hx
      | Lean.throwError "missing exchange equation"
    let source ← Lean.Meta.whnf hd.type
    let target ← Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget)
    let e ← Lean.Meta.mkEqOfHEq (← transportCongruence source target)
    let result ← Lean.Meta.mkAppM ``Eq.mp #[e, hd.toExpr]
    Lean.Elab.Tactic.closeMainGoal `exact result

end WeilConjectures.IntegralSystemRealization

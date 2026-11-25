/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
import all WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemBridgeExchange

/-! # Canonical bridge comparison for a single open base-change map -/

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

private theorem openUnitBridge {A B : Type*} [Category A] [Category B]
    {J F : A ⥤ B} {P Q : B ⥤ A} (a : J ⊣ P) (b : F ⊣ Q) (e : P ≅ Q) (M : A) :
    a.unit.app M ≫ e.hom.app (J.obj M) ≫
      Q.map (((a.ofNatIsoRight e).leftAdjointUniq b).hom.app M) = b.unit.app M := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (a.ofNatIsoRight e) b M
  simpa only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc] using h

private theorem betaBridge
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {J F : A ⥤ B} {P Q : B ⥤ A} {J₁ F₁ : C ⥤ D} {P₁ Q₁ : D ⥤ C}
    {V V' : A ⥤ C} {W W' : B ⥤ D}
    (a : J ⊣ P) (b : F ⊣ Q) (a₁ : J₁ ⊣ P₁) (b₁ : F₁ ⊣ Q₁)
    (ep : P ≅ Q) (ep₁ : P₁ ≅ Q₁) (ej : J ≅ F) (ej₁ : J₁ ≅ F₁)
    (ev : V ≅ V') (ew : W ≅ W')
    (r : W ⋙ P₁ ≅ P ⋙ V) (s : W' ⋙ Q₁ ≅ Q ⋙ V')
    (α : J ⋙ W ≅ V ⋙ J₁) (β : F ⋙ W' ≅ V' ⋙ F₁)
    (hr : ∀ M, (a₁.homEquiv (V.obj M) (W.obj (J.obj M))) (α.inv.app M) =
      V.map (a.unit.app M) ≫ r.inv.app (J.obj M))
    (hs : ∀ M, (b₁.homEquiv (V'.obj M) (W'.obj (F.obj M))) (β.inv.app M) =
      V'.map (b.unit.app M) ≫ s.inv.app (F.obj M))
    (hu : ∀ M, a.unit.app M ≫ ep.hom.app (J.obj M) ≫ Q.map (ej.hom.app M) =
      b.unit.app M)
    (hu₁ : ∀ M, a₁.unit.app M ≫ ep₁.hom.app (J₁.obj M) ≫ Q₁.map (ej₁.hom.app M) =
      b₁.unit.app M)
    (h : ∀ L, V.map (ep.hom.app L) ≫ ev.hom.app (Q.obj L) ≫ s.inv.app L =
      r.inv.app L ≫ P₁.map (ew.hom.app L) ≫ ep₁.hom.app (W'.obj L))
    (M : A) :
    α.hom.app M ≫ ej₁.hom.app (V.obj M) ≫ F₁.map (ev.hom.app M) =
      ew.hom.app (J.obj M) ≫ W'.map (ej.hom.app M) ≫ β.hom.app M := by
  have hi : ej₁.hom.app (V.obj M) ≫ F₁.map (ev.hom.app M) ≫ β.inv.app M =
      α.inv.app M ≫ ew.hom.app (J.obj M) ≫ W'.map (ej.hom.app M) := by
    apply (a₁.homEquiv _ _).injective
    apply (cancel_mono (ep₁.hom.app (W'.obj (F.obj M)))).mp
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    simp only [Functor.map_comp, Category.assoc]
    have nβ := ep₁.hom.naturality (β.inv.app M)
    have nF := ep₁.hom.naturality (F₁.map (ev.hom.app M))
    have nJ := ep₁.hom.naturality (ej₁.hom.app (V.obj M))
    have nu := b₁.unit.naturality (ev.hom.app M)
    dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_map] at nβ nF nJ nu
    rw [nβ, reassoc_of% nF, reassoc_of% nJ, reassoc_of% (hu₁ (V.obj M))]
    rw [← reassoc_of% nu]
    rw [← Adjunction.homEquiv_unit]
    have hβ := hs M
    dsimp only [Functor.comp_obj] at hβ
    rw [hβ]
    have nw := ep₁.hom.naturality (W'.map (ej.hom.app M))
    have hα := hr M
    rw [Adjunction.homEquiv_unit] at hα
    dsimp only [Functor.comp_obj] at hα
    rw [nw, reassoc_of% hα]
    rw [← reassoc_of% (h (J.obj M))]
    have ns := s.inv.naturality (ej.hom.app M)
    dsimp only [Functor.comp_obj, Functor.comp_map] at ns
    rw [← ns]
    have nv := ev.hom.naturality (a.unit.app M)
    dsimp only [Functor.comp_obj] at nv
    have ne := ev.hom.naturality (ep.hom.app (J.obj M))
    rw [reassoc_of% ne, reassoc_of% nv,
      ← V'.map_comp_assoc, ← V'.map_comp_assoc]
    simp only [Category.assoc, hu]
  apply (cancel_mono (β.inv.app M)).mp
  simp only [Category.assoc]
  rw [hi]
  simp

private theorem intrinsicBetaTranspose
    {U' U X' X : Scheme.{u}} (d : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : d ≫ j = j' ≫ g) (sq : IsPullback d j' j g)
    (N : ProEtale.SemilinearProperOpen.Derived
      (scalarRings l E) (scalarTransitions l E) U) :
      (ProEtale.SemilinearProperOpen.jAdj (scalarRings l E)
        (scalarTransitions l E) j').homEquiv _ _
        ((ProEtale.SemilinearProperOpen.beta (scalarRings l E)
          (scalarTransitions l E) d j' j g h sq).inv.app N) =
      (ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E) d).map
        ((ProEtale.SemilinearProperOpen.jAdj (scalarRings l E)
          (scalarTransitions l E) j).unit.app N) ≫
        (ProEtale.SemilinearProperOpen.squareP (scalarRings l E)
          (scalarTransitions l E) d j' j g h).inv.app
          ((ProEtale.SemilinearProperOpen.J (scalarRings l E)
            (scalarTransitions l E) j).obj N) := by
  change (ProEtale.SemilinearProperOpen.jAdj (scalarRings l E)
    (scalarTransitions l E) j').homEquiv _ _
    (ProEtale.SemilinearProperOpen.betaInvApp (scalarRings l E)
      (scalarTransitions l E) d j' j g h N) = _
  exact Equiv.apply_symm_apply _ _

private theorem canonicalOpenUnit (o : Operations l E) (b : CanonicalBridge l E o)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (M : System l E U) :
    (o.extension j).adj.unit.app M ≫
      (b.pull l E j).hom.app ((Operations.shriek l E o j).obj M) ≫
      (ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E) j).map
        ((b.shriek l E j).hom.app M) =
      (ProEtale.SemilinearProperOpen.jAdj (scalarRings l E)
        (scalarTransitions l E) j).unit.app M := by
  exact openUnitBridge (o.extension j).adj
    (ProEtale.SemilinearProperOpen.jAdj (scalarRings l E) (scalarTransitions l E) j)
    (b.pull l E j) M

attribute [local irreducible] CanonicalBridge.pull CanonicalBridge.shriek
  ProEtale.SemilinearProperOpen.P ProEtale.SemilinearProperOpen.J
  DerivedCategory _root_.instCategoryDerivedCategory
  ProEtale.SemilinearProperOpen.beta ProEtale.SemilinearProperOpen.jAdj

private theorem canonicalInverseSquare (o : Operations l E) (c : Compositors l E o)
    (b : CanonicalBridge l E o) {U' U X' X : Scheme.{u}}
    (d : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (h : d ≫ j = j' ≫ g) (L : System l E X) :
    (pull l E d).map ((b.pull l E j).hom.app L) ≫
      (b.pull l E d).hom.app
        ((ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E) j).obj L) ≫
      (ProEtale.SemilinearProperOpen.squareP (scalarRings l E)
        (scalarTransitions l E) d j' j g h).inv.app L =
    (c.square l E d j' j g h).inv.app L ≫
      (pull l E j').map ((b.pull l E g).hom.app L) ≫
      (b.pull l E j').hom.app
        ((ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E) g).obj L) := by
  have hh := inverseSquare' (c.square l E d j' j g h)
    (ProEtale.SemilinearProperOpen.squareP (scalarRings l E)
      (scalarTransitions l E) d j' j g h)
    (bridgePair (b.pull l E g) (b.pull l E j')).hom
    (bridgePair (b.pull l E j) (b.pull l E d)).hom
    (bridgePullSquare l E o c b d j' j g h)
  simpa only [bridgePair, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc] using (congr_app hh L).symm

/-- The canonical bridge intertwines open base change for one cartesian square.
Source: Stacks 03DI and 07A7; blueprint fix-prop-coherence
(blueprint: lem-sf-integral-system-bridge-open-basechange).
Proof: apply injectivity of the open-adjunction hom equivalence to the desired
forward equation, substitute the specified inverse-beta transpose equation and
both bridge unit equations, use the bridge pull-square comparison, and cancel the
beta isomorphisms. This is a whole-system argument and needs no finite evaluation.
(blueprint: lem-sf-integral-system-bridge-open-basechange).
-/
theorem integralSystemBridgeOpenBaseChange (o : Operations l E)
    (c : Compositors l E o) (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    {U' U X' X : Scheme.{u}} (d : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : d ≫ j = j' ≫ g) (sq : IsPullback d j' j g) (M : System l E U) :
    (a.beta d j' j g h sq).hom.app M ≫
        (b.shriek l E j').hom.app ((pull l E d).obj M) ≫
        (ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) j').map
          ((b.pull l E d).hom.app M) =
      (b.pull l E g).hom.app ((Operations.shriek l E o j).obj M) ≫
        (ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E) g).map
          ((b.shriek l E j).hom.app M) ≫
        (ProEtale.SemilinearProperOpen.beta (scalarRings l E) (scalarTransitions l E)
          d j' j g h sq).hom.app M := by
  refine betaBridge (o.extension j).adj
    (ProEtale.SemilinearProperOpen.jAdj (scalarRings l E) (scalarTransitions l E) j)
    (o.extension j').adj
    (ProEtale.SemilinearProperOpen.jAdj (scalarRings l E) (scalarTransitions l E) j')
    (b.pull l E j) (b.pull l E j') (b.shriek l E j) (b.shriek l E j')
    (b.pull l E d) (b.pull l E g)
    (c.square l E d j' j g h)
    (ProEtale.SemilinearProperOpen.squareP (scalarRings l E)
      (scalarTransitions l E) d j' j g h)
    (a.beta d j' j g h sq)
    (ProEtale.SemilinearProperOpen.beta (scalarRings l E)
      (scalarTransitions l E) d j' j g h sq)
    ?_ ?_ ?_ ?_ ?_ M
  · intro N
    have hx := a.beta_transpose d j' j g h sq N
    run_tac Lean.Elab.Tactic.withMainContext do
      let some hd := (← Lean.getLCtx).findFromUserName? `hx
        | Lean.throwError "missing component equation"
      let source ← Lean.Meta.whnf hd.type
      let target ← Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget)
      let e ← Lean.Meta.mkEqOfHEq (← transportCongruence source target)
      Lean.Elab.Tactic.closeMainGoal `exact (← Lean.Meta.mkAppM ``Eq.mp #[e, hd.toExpr])
  · intro N
    have hx := intrinsicBetaTranspose l E d j' j g h sq N
    run_tac Lean.Elab.Tactic.withMainContext do
      let some hd := (← Lean.getLCtx).findFromUserName? `hx
        | Lean.throwError "missing component equation"
      let source ← Lean.Meta.whnf hd.type
      let target ← Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget)
      let e ← Lean.Meta.mkEqOfHEq (← transportCongruence source target)
      Lean.Elab.Tactic.closeMainGoal `exact (← Lean.Meta.mkAppM ``Eq.mp #[e, hd.toExpr])
  · intro N
    have hx := canonicalOpenUnit l E o b j N
    run_tac Lean.Elab.Tactic.withMainContext do
      let some hd := (← Lean.getLCtx).findFromUserName? `hx
        | Lean.throwError "missing component equation"
      let source ← Lean.Meta.whnf hd.type
      let target ← Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget)
      let e ← Lean.Meta.mkEqOfHEq (← transportCongruence source target)
      Lean.Elab.Tactic.closeMainGoal `exact (← Lean.Meta.mkAppM ``Eq.mp #[e, hd.toExpr])
  · intro N
    have hx := canonicalOpenUnit l E o b j' N
    run_tac Lean.Elab.Tactic.withMainContext do
      let some hd := (← Lean.getLCtx).findFromUserName? `hx
        | Lean.throwError "missing component equation"
      let source ← Lean.Meta.whnf hd.type
      let target ← Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget)
      let e ← Lean.Meta.mkEqOfHEq (← transportCongruence source target)
      Lean.Elab.Tactic.closeMainGoal `exact (← Lean.Meta.mkAppM ``Eq.mp #[e, hd.toExpr])
  · intro N
    have hx := canonicalInverseSquare l E o c b d j' j g h N
    run_tac Lean.Elab.Tactic.withMainContext do
      let some hd := (← Lean.getLCtx).findFromUserName? `hx
        | Lean.throwError "missing component equation"
      let source ← Lean.Meta.whnf hd.type
      let target ← Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget)
      let e ← Lean.Meta.mkEqOfHEq (← transportCongruence source target)
      Lean.Elab.Tactic.closeMainGoal `exact (← Lean.Meta.mkAppM ``Eq.mp #[e, hd.toExpr])

end WeilConjectures.IntegralSystemRealization

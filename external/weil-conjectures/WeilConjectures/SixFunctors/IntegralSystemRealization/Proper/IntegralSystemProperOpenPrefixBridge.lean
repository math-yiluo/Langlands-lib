/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.IntegralSystemProperOpenBridgeWord
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemCartesianBridgeTransport
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralSystemOpenRestrictionBridgeTransport

/-! A factor identity used in proper/open transport. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

private theorem prefix_transport
    {A B C D F : Type*} [Category A] [Category B] [Category C] [Category D] [Category F]
    {J J' : A ⥤ B} {S S' : A ⥤ C} {R R' : B ⥤ D} {P P' : D ⥤ F}
    {Q Q' : B ⥤ C} {T T' : C ⥤ F}
    (ej : J ⟶ J') (es : S ⟶ S') (er : R ⟶ R') (ep : P ⟶ P')
    (eq : Q ⟶ Q') (et : T ⟶ T')
    (θ : R ⋙ P ⟶ Q ⋙ T) (θ' : R' ⋙ P' ⟶ Q' ⋙ T')
    (ρ : J ⋙ Q ⟶ S) (ρ' : J' ⋙ Q' ⟶ S')
    (hc : ∀ X, θ.app X ≫ et.app (Q.obj X) ≫ T'.map (eq.app X) =
      ep.app (R.obj X) ≫ P'.map (er.app X) ≫ θ'.app X)
    (hr : ∀ X, ρ.app X ≫ es.app X =
      eq.app (J.obj X) ≫ Q'.map (ej.app X) ≫ ρ'.app X) (X : A) :
    θ.app (J.obj X) ≫ T.map (ρ.app X) ≫ et.app (S.obj X) ≫ T'.map (es.app X) =
      P.map (R.map (ej.app X) ≫ er.app (J'.obj X)) ≫ ep.app (R'.obj (J'.obj X)) ≫
        θ'.app (J'.obj X) ≫ T'.map (ρ'.app X) := by
  rw [et.naturality_assoc, ← T'.map_comp, hr]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hc]
  have hn := θ'.naturality (ej.app X)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [← P'.map_comp_assoc, ← er.naturality]
  rw [← ep.naturality_assoc, P.map_comp]
  simp only [Category.assoc]

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

/-- The cartesian and restriction prefix commutes with the canonical bridge.
Source: Stacks 0F7B and blueprint fix-prop-coherence.

Proof: On ordinary sections the bridges are the identity and the compositors are the
prescribed pullbackComp maps. Adjoint uniqueness identifies the corresponding
pull compositors. The cochain normalization lifts this identity to the derived
operations. Transport the unit defining beta and take its adjoint conjugate to
obtain the cartesian square. Transport the restriction factor by uniqueness of
open extension, its inverse open unit, and the normalized open compositor.
Map this square by the second-projection direct functor and paste with the
cartesian square. Naturality orders the source-coordinate bridge as displayed.
This argument uses no clopen comparison or final direct compositor.
(blueprint: lem-sf-integral-system-proper-open-prefix-bridge). -/
theorem properOpenPrefix_bridge (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : System l E U) :
    let d := properOpenBridgeWord l E o c a b k r p i h M
    d.a ≫ d.b ≫ d.j ≫ d.k = d.t ≫ d.t' ≫ d.x ≫ d.y := by
  dsimp only
  unfold properOpenBridgeWord
  exact prefix_transport
    (J := Operations.shriek l E o k)
    (J' := ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) k)
    (S := Operations.shriek l E o (ProEtale.StrictTower.squareLift k r p i h))
    (S' := ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E)
      (ProEtale.StrictTower.squareLift k r p i h))
    (R := Operations.push l E o p)
    (R' := ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) p)
    (P := pull l E i)
    (P' := ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E) i)
    (Q := pull l E (pullback.fst p i))
    (Q' := ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E)
      (pullback.fst p i))
    (T := Operations.push l E o (pullback.snd p i))
    (T' := ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E)
      (pullback.snd p i))
    (b.shriek l E k).hom
    (b.shriek l E (ProEtale.StrictTower.squareLift k r p i h)).hom
    (b.push l E p).hom (b.pull l E i).hom
    (b.pull l E (pullback.fst p i)).hom (b.push l E (pullback.snd p i)).hom
    (cartesianConjugate l E o c a p i).hom
    (ProEtale.SemilinearProperOpen.cartesianConjugate
      (scalarRings l E) (scalarTransitions l E) p i).hom
    (restrictFactor l E o c a k r p i h).hom
    (ProEtale.SemilinearProperOpen.restrictFactor
      (scalarRings l E) (scalarTransitions l E) k r p i h).hom
    (cartesianBridge_transport l E o c a b p i)
    (openRestrictionBridge_transport l E o c a b k r p i h) M

end WeilConjectures.IntegralSystemRealization

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import all WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemCompositorAssociativity
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralSystemOrdinaryBridgeComposition

/-! Compatibility of the canonical bridge with direct-image composition. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

private theorem localize_composition
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    {Lf Pf : B ⥤ A} {Lg Pg : C ⥤ B} {Lh Ph : C ⥤ A}
    [Lf.Additive] [Pf.Additive] [Lg.Additive] [Pg.Additive] [Lh.Additive] [Ph.Additive]
    [PreservesFiniteLimits Lf] [PreservesFiniteColimits Lf]
    [PreservesFiniteLimits Pf] [PreservesFiniteColimits Pf]
    [PreservesFiniteLimits Lg] [PreservesFiniteColimits Lg]
    [PreservesFiniteLimits Pg] [PreservesFiniteColimits Pg]
    [PreservesFiniteLimits Lh] [PreservesFiniteColimits Lh]
    [PreservesFiniteLimits Ph] [PreservesFiniteColimits Ph]
    (f : Pf ≅ Lf) (g : Pg ≅ Lg) (h : Ph ≅ Lh)
    (s : Lh ≅ Lg ⋙ Lf) (r : Ph ≅ Pg ⋙ Pf)
    (H : h ≪≫ s = r ≪≫ Functor.isoWhiskerLeft Pg f ≪≫
      Functor.isoWhiskerRight g Lf) :
    (Functor.mapDerivedCategoryNatIso h.symm).symm ≪≫ Functor.mapDerivedCategoryNatIso s ≪≫
        (Functor.mapDerivedCategoryCompIso Lg Lf).symm =
      (Functor.mapDerivedCategoryNatIso r ≪≫ (Functor.mapDerivedCategoryCompIso Pg Pf).symm) ≪≫
        Functor.isoWhiskerLeft Pg.mapDerivedCategory
          (Functor.mapDerivedCategoryNatIso f.symm).symm ≪≫
        Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso g.symm).symm
          Lf.mapDerivedCategory := by
  apply Iso.ext
  have hh := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom) H
  simp only [Functor.mapDerivedCategoryNatIso_trans] at hh
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom, ← Functor.mapDerivedCategoryNatIso_symm, Iso.symm_symm_eq, Category.assoc]
  rw [← Category.assoc, hh]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_isoWhiskerRight]
  rw [← Category.assoc (Functor.mapDerivedCategoryNatIso
    (Functor.isoWhiskerLeft Pg f)).hom,
    Functor.mapDerivedCategoryNatIso_isoWhiskerLeft]
  simp only [Category.assoc]

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

attribute [local instance] pullbackTensorSequenceInverse_additive
  pullbackTensorSequenceInverse_limits pullbackTensorSequenceInverse_colimits
  ProEtale.SemilinearProperOpen.pull_additive ProEtale.SemilinearProperOpen.pull_limits
  ProEtale.SemilinearProperOpen.pull_colimits

private theorem pull_bridge_composition (o : Operations l E) (c : Compositors l E o)
    (b : CanonicalBridge l E o) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (b.pull l E (f ≫ g)).symm ≪≫ c.pullComp f g =
      ProEtale.SemilinearProperOpen.pComp (scalarRings l E) (scalarTransitions l E) f g ≪≫
        Functor.isoWhiskerLeft
          (ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E) g)
          (b.pull l E f).symm ≪≫
        Functor.isoWhiskerRight (b.pull l E g).symm (pull l E f) := by
  rw [pullComp_eq l E c f g]
  exact @localize_composition
    (coefficientSequenceModules l E X) (coefficientSequenceModules l E Y)
    (coefficientSequenceModules l E Z) _ _ _ _ _ _ _ _ _
    (pullbackTensorSequenceInverse l E f)
    (ProEtale.SemilinearProperOpen.pull (scalarRings l E) (scalarTransitions l E) f)
    (pullbackTensorSequenceInverse l E g)
    (ProEtale.SemilinearProperOpen.pull (scalarRings l E) (scalarTransitions l E) g)
    (pullbackTensorSequenceInverse l E (f ≫ g))
    (ProEtale.SemilinearProperOpen.pull (scalarRings l E) (scalarTransitions l E) (f ≫ g))
    (pullbackTensorSequenceInverse_additive l E f)
    (ProEtale.SemilinearProperOpen.pull_additive
      (scalarRings l E) (scalarTransitions l E) f)
    (pullbackTensorSequenceInverse_additive l E g)
    (ProEtale.SemilinearProperOpen.pull_additive
      (scalarRings l E) (scalarTransitions l E) g)
    (pullbackTensorSequenceInverse_additive l E (f ≫ g))
    (ProEtale.SemilinearProperOpen.pull_additive
      (scalarRings l E) (scalarTransitions l E) (f ≫ g))
    (pullbackTensorSequenceInverse_limits l E f)
    (pullbackTensorSequenceInverse_colimits l E f)
    (ProEtale.SemilinearProperOpen.pull_limits
      (scalarRings l E) (scalarTransitions l E) f)
    (ProEtale.SemilinearProperOpen.pull_colimits
      (scalarRings l E) (scalarTransitions l E) f)
    (pullbackTensorSequenceInverse_limits l E g)
    (pullbackTensorSequenceInverse_colimits l E g)
    (ProEtale.SemilinearProperOpen.pull_limits
      (scalarRings l E) (scalarTransitions l E) g)
    (ProEtale.SemilinearProperOpen.pull_colimits
      (scalarRings l E) (scalarTransitions l E) g)
    (pullbackTensorSequenceInverse_limits l E (f ≫ g))
    (pullbackTensorSequenceInverse_colimits l E (f ≫ g))
    (ProEtale.SemilinearProperOpen.pull_limits
      (scalarRings l E) (scalarTransitions l E) (f ≫ g))
    (ProEtale.SemilinearProperOpen.pull_colimits
      (scalarRings l E) (scalarTransitions l E) (f ≫ g))
    (ordinaryPullBridge l E o b f).symm (ordinaryPullBridge l E o b g).symm
    (ordinaryPullBridge l E o b (f ≫ g)).symm (c.ordinaryPull f g)
    (ProEtale.SemilinearProperOpen.pullComp (scalarRings l E) (scalarTransitions l E) f g)
    (ordinary_pull_composition l E o c b f g)

/-- The bridge preserves the section-normalized direct-image compositor.
Source: Stacks 03D8, 07A7; blueprint fix-prop-coherence, strict-system realization.
(blueprint: lem-sf-integral-system-bridge-push-composition).
Proof: the ordinary direct-image comparisons commute with composition since their
components are identity on sections and the two compositors restrict along the same
canonical map of iterated fibre products. Conjugate this ordinary equality through
the three module adjunctions. Localize the resulting inverse-image equality; the
complex-factor equation of the supplied compositor identifies its localization.
Finally conjugate through the derived adjunctions. Conjugation preserves composition
and whiskering, so the resulting equality is exactly the displayed equation. -/
theorem integralSystemBridgePushComposition (o : Operations l E) (c : Compositors l E o)
    (b : CanonicalBridge l E o) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : System l E X) :
    (c.pushComp l E f g).hom.app M ≫ (b.push l E (f ≫ g)).hom.app M =
      (b.push l E g).hom.app ((Operations.push l E o f).obj M) ≫
        (ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) g).map
          ((b.push l E f).hom.app M) ≫
        (ProEtale.SemilinearProperOpen.sComp
          (scalarRings l E) (scalarTransitions l E) f g).hom.app M := by
  have hh := conjugate_composition
    (o.direct f).adj (o.direct g).adj (o.direct (f ≫ g)).adj
    (ProEtale.SemilinearProperOpen.adj (scalarRings l E) (scalarTransitions l E) f)
    (ProEtale.SemilinearProperOpen.adj (scalarRings l E) (scalarTransitions l E) g)
    (ProEtale.SemilinearProperOpen.adj (scalarRings l E) (scalarTransitions l E) (f ≫ g))
    (b.pull l E f).symm (b.pull l E g).symm (b.pull l E (f ≫ g)).symm
    (c.pullComp f g)
    (ProEtale.SemilinearProperOpen.pComp (scalarRings l E) (scalarTransitions l E) f g)
    (pull_bridge_composition l E o c b f g)
  have hh' := congr_app hh M
  exact hh'

end WeilConjectures.IntegralSystemRealization

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCoherence

/-! Ordinary comparison of the canonical bridge with direct-image composition. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

private theorem bridge_conjugate
    {C D : Type*} [Category C] [Category D]
    {L P : C ⥤ D} {S R : D ⥤ C} (a : L ⊣ S) (b : P ⊣ R) (e : S ≅ R) :
    conjugateIsoEquiv a b (((a.ofNatIsoRight e).leftAdjointUniq b).symm) = e := by
  apply Iso.ext
  rw [conjugateIsoEquiv_apply_hom]
  apply (conjugateEquiv a b).symm.injective
  rw [Equiv.symm_apply_apply]
  change (((a.ofNatIsoRight e).leftAdjointUniq b).inv) = _
  apply NatTrans.ext
  funext M
  apply (cancel_epi (((a.ofNatIsoRight e).leftAdjointUniq b).hom.app M)).mp
  simp only [Iso.hom_inv_id_app]
  rw [conjugateEquiv_symm_apply_app]
  rw [← ((a.ofNatIsoRight e).leftAdjointUniq b).hom.naturality_assoc,
    ← ((a.ofNatIsoRight e).leftAdjointUniq b).hom.naturality_assoc]
  rw [Adjunction.leftAdjointUniq_hom_app_counit]
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app]
  rw [← L.map_comp_assoc (e.hom.app (L.obj M)) (e.inv.app (L.obj M)),
    Iso.hom_inv_id_app,
    L.map_id, Category.id_comp]
  exact (a.left_triangle_components M).symm

private theorem conjugate_composition
    {A B C : Type*} [Category A] [Category B] [Category C]
    {Lf Pf : B ⥤ A} {Lg Pg : C ⥤ B} {Lh Ph : C ⥤ A}
    {Sf Rf : A ⥤ B} {Sg Rg : B ⥤ C} {Sh Rh : A ⥤ C}
    (af : Lf ⊣ Sf) (ag : Lg ⊣ Sg) (ah : Lh ⊣ Sh)
    (bf : Pf ⊣ Rf) (bg : Pg ⊣ Rg) (bh : Ph ⊣ Rh)
    (f : Pf ≅ Lf) (g : Pg ≅ Lg) (h : Ph ≅ Lh)
    (s : Lh ≅ Lg ⋙ Lf) (r : Ph ≅ Pg ⋙ Pf)
    (H : h ≪≫ s = r ≪≫ Functor.isoWhiskerLeft Pg f ≪≫
      Functor.isoWhiskerRight g Lf) :
    (conjugateIsoEquiv (ag.comp af) ah s).hom ≫ (conjugateIsoEquiv ah bh h).hom =
      Functor.whiskerLeft Sf (conjugateIsoEquiv ag bg g).hom ≫
        Functor.whiskerRight (conjugateIsoEquiv af bf f).hom Rg ≫
        (conjugateIsoEquiv (bg.comp bf) bh r).hom := by
  change conjugateEquiv (ag.comp af) ah s.hom ≫ conjugateEquiv ah bh h.hom = _
  rw [conjugateEquiv_comp]
  have hh := congrArg Iso.hom H
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom] at hh
  rw [hh]
  rw [← conjugateEquiv_comp (ag.comp af) (bg.comp bf) bh]
  rw [← conjugateEquiv_comp (ag.comp af) (bg.comp af) (bg.comp bf)]
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight]
  simp only [Category.assoc, conjugateIsoEquiv_apply_hom]

private theorem conjugate_composition_injective
    {A B C : Type*} [Category A] [Category B] [Category C]
    {Lf Pf : B ⥤ A} {Lg Pg : C ⥤ B} {Lh Ph : C ⥤ A}
    {Sf Rf : A ⥤ B} {Sg Rg : B ⥤ C} {Sh Rh : A ⥤ C}
    (af : Lf ⊣ Sf) (ag : Lg ⊣ Sg) (ah : Lh ⊣ Sh)
    (bf : Pf ⊣ Rf) (bg : Pg ⊣ Rg) (bh : Ph ⊣ Rh)
    (f : Pf ≅ Lf) (g : Pg ≅ Lg) (h : Ph ≅ Lh)
    (s : Lh ≅ Lg ⋙ Lf) (r : Ph ≅ Pg ⋙ Pf)
    (H : (conjugateIsoEquiv (ag.comp af) ah s).hom ≫ (conjugateIsoEquiv ah bh h).hom =
      Functor.whiskerLeft Sf (conjugateIsoEquiv ag bg g).hom ≫
        Functor.whiskerRight (conjugateIsoEquiv af bf f).hom Rg ≫
        (conjugateIsoEquiv (bg.comp bf) bh r).hom) :
    h ≪≫ s = r ≪≫ Functor.isoWhiskerLeft Pg f ≪≫ Functor.isoWhiskerRight g Lf := by
  apply Iso.ext
  apply (conjugateEquiv (ag.comp af) bh).injective
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  rw [← conjugateEquiv_comp (ag.comp af) ah bh]
  rw [← conjugateEquiv_comp (ag.comp af) (bg.comp bf) bh]
  rw [← conjugateEquiv_comp (ag.comp af) (bg.comp af) (bg.comp bf)]
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight]
  simpa only [conjugateIsoEquiv_apply_hom, Category.assoc] using H

private theorem conjugate_leftAdjointComp
    {A B C : Type*} [Category A] [Category B] [Category C]
    {Lf : B ⥤ A} {Lg : C ⥤ B} {Lh : C ⥤ A}
    {Sf : A ⥤ B} {Sg : B ⥤ C} {Sh : A ⥤ C}
    (af : Lf ⊣ Sf) (ag : Lg ⊣ Sg) (ah : Lh ⊣ Sh) (r : Sf ⋙ Sg ≅ Sh) :
    conjugateIsoEquiv (ag.comp af) ah (Adjunction.leftAdjointCompIso ag af ah r).symm =
      r := by
  apply Iso.ext
  exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv ag af ah r

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

/-- The ordinary bridge preserves the section-normalized direct-image compositor.
Source: Stacks 03D8, 07A7; strict-system realization of blueprint fix-prop-coherence.
(blueprint: lem-sf-integral-system-ordinary-bridge-composition).
Proof: evaluate on each section at (n,U). Both ordinary bridge components are
identity on sections. The supplied compositor and the intrinsic compositor are
restriction along the same canonical map of iterated fibre products. Thus their
components agree; section extensionality proves equality of the natural maps. -/
theorem integralSystemOrdinaryBridgeComposition (o : Operations l E) (c : Compositors l E o)
    (b : CanonicalBridge l E o) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    c.ordinaryDirect f g ≪≫ b.ordinary (f ≫ g) =
      Functor.isoWhiskerLeft (pullbackTensorSequenceDirect l E f) (b.ordinary g) ≪≫
        Functor.isoWhiskerRight (b.ordinary f)
          (ProEtale.SemilinearProperOpen.push (scalarRings l E) (scalarTransitions l E) g) ≪≫
        ProEtale.SemilinearProperOpen.pushComp
          (scalarRings l E) (scalarTransitions l E) f g := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U using Opposite.rec
  rename_i U
  rcases U with ⟨n, U⟩
  ext x
  change ((b.ordinary (f ≫ g)).hom.app M).val.app (op (n, U))
    (((c.ordinaryDirect f g).hom.app M).val.app (op (n, U)) x) =
      ((ProEtale.SemilinearProperOpen.pushComp
        (scalarRings l E) (scalarTransitions l E) f g).hom.app M).val.app (op (n, U))
        (((ProEtale.SemilinearProperOpen.push (scalarRings l E)
          (scalarTransitions l E) g).map ((b.ordinary f).hom.app M)).val.app (op (n, U))
          (((b.ordinary g).hom.app ((pullbackTensorSequenceDirect l E f).obj M)).val.app
            (op (n, U)) x))
  conv_lhs =>
    erw [b.sections (f ≫ g) M n U]
  conv_lhs =>
    erw [c.sections f g M n U]
  conv_rhs =>
    erw [b.sections g ((pullbackTensorSequenceDirect l E f).obj M) n U]
  change _ = ((ProEtale.SemilinearProperOpen.pushComp
    (scalarRings l E) (scalarTransitions l E) f g).hom.app M).val.app (op (n, U))
      (((b.ordinary f).hom.app M).val.app (op (n, (proEtaleBaseChange g).obj U)) x)
  conv_rhs =>
    erw [b.sections f M n ((proEtaleBaseChange g).obj U)]
  exact (ProEtale.SemilinearProperOpen.pushComp_apply
    (scalarRings l E) (scalarTransitions l E) f g M n U x).symm

private def ordinaryPullBridge (o : Operations l E) (b : CanonicalBridge l E o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceInverse l E f ≅
      ProEtale.SemilinearProperOpen.pull (scalarRings l E) (scalarTransitions l E) f :=
  ((pullbackTensorSequenceAdjunction l E f).ofNatIsoRight (b.ordinary f)).leftAdjointUniq
    (ProEtale.SemilinearProperOpen.ordinaryAdj (scalarRings l E) (scalarTransitions l E) f)

attribute [local irreducible] pullbackTensorSequenceDirect pullbackTensorSequenceInverse
  ProEtale.SemilinearProperOpen.push

private theorem ordinary_pull_composition (o : Operations l E) (c : Compositors l E o)
    (b : CanonicalBridge l E o) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (ordinaryPullBridge l E o b (f ≫ g)).symm ≪≫ c.ordinaryPull f g =
      ProEtale.SemilinearProperOpen.pullComp (scalarRings l E) (scalarTransitions l E) f g ≪≫
        Functor.isoWhiskerLeft
          (ProEtale.SemilinearProperOpen.pull (scalarRings l E) (scalarTransitions l E) g)
          (ordinaryPullBridge l E o b f).symm ≪≫
        Functor.isoWhiskerRight (ordinaryPullBridge l E o b g).symm
          (pullbackTensorSequenceInverse l E f) := by
  apply conjugate_composition_injective
    (pullbackTensorSequenceAdjunction l E f) (pullbackTensorSequenceAdjunction l E g)
    (pullbackTensorSequenceAdjunction l E (f ≫ g))
    (ProEtale.SemilinearProperOpen.ordinaryAdj (scalarRings l E) (scalarTransitions l E) f)
    (ProEtale.SemilinearProperOpen.ordinaryAdj (scalarRings l E) (scalarTransitions l E) g)
    (ProEtale.SemilinearProperOpen.ordinaryAdj
      (scalarRings l E) (scalarTransitions l E) (f ≫ g))
  dsimp only [ordinaryPullBridge]
  conv_lhs =>
    arg 2
    erw [bridge_conjugate (pullbackTensorSequenceAdjunction l E (f ≫ g))
      (ProEtale.SemilinearProperOpen.ordinaryAdj
        (scalarRings l E) (scalarTransitions l E) (f ≫ g)) (b.ordinary (f ≫ g))]
  conv_rhs =>
    arg 1
    arg 2
    erw [bridge_conjugate (pullbackTensorSequenceAdjunction l E g)
      (ProEtale.SemilinearProperOpen.ordinaryAdj
        (scalarRings l E) (scalarTransitions l E) g) (b.ordinary g)]
  conv_rhs =>
    arg 2
    arg 1
    arg 1
    erw [bridge_conjugate (pullbackTensorSequenceAdjunction l E f)
      (ProEtale.SemilinearProperOpen.ordinaryAdj
        (scalarRings l E) (scalarTransitions l E) f) (b.ordinary f)]
  conv_lhs =>
    arg 1
    erw [c.conjugate f g]
  have hi :
      (conjugateIsoEquiv
        ((ProEtale.SemilinearProperOpen.ordinaryAdj (scalarRings l E)
          (scalarTransitions l E) g).comp
          (ProEtale.SemilinearProperOpen.ordinaryAdj (scalarRings l E)
            (scalarTransitions l E) f))
        (ProEtale.SemilinearProperOpen.ordinaryAdj (scalarRings l E)
          (scalarTransitions l E) (f ≫ g))
        (ProEtale.SemilinearProperOpen.pullComp
          (scalarRings l E) (scalarTransitions l E) f g)).hom =
      (ProEtale.SemilinearProperOpen.pushComp
        (scalarRings l E) (scalarTransitions l E) f g).hom :=
    congrArg Iso.hom (conjugate_leftAdjointComp
      (ProEtale.SemilinearProperOpen.ordinaryAdj (scalarRings l E) (scalarTransitions l E) f)
      (ProEtale.SemilinearProperOpen.ordinaryAdj (scalarRings l E) (scalarTransitions l E) g)
      (ProEtale.SemilinearProperOpen.ordinaryAdj
        (scalarRings l E) (scalarTransitions l E) (f ≫ g))
      (ProEtale.SemilinearProperOpen.pushComp (scalarRings l E) (scalarTransitions l E) f g))
  conv_rhs =>
    arg 2
    arg 2
    rw [hi]
  exact congrArg Iso.hom (integralSystemOrdinaryBridgeComposition l E o c b f g)

end WeilConjectures.IntegralSystemRealization

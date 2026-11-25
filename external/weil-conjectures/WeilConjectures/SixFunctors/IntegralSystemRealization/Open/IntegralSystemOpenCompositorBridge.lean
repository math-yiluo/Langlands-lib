/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import all WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemBridgePushComposition
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralSystemOrdinaryBridgeComposition

/-! # The canonical bridge preserves open composition. -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
private theorem open_composition
    {A B C : Type*} [Category A] [Category B] [Category C]
    {Lf Pf : A ⥤ B} {Lg Pg : B ⥤ C} {Lh Ph : A ⥤ C}
    {Rf Sf : B ⥤ A} {Rg Sg : C ⥤ B} {Rh Sh : C ⥤ A}
    (af : Lf ⊣ Rf) (ag : Lg ⊣ Rg) (ah : Lh ⊣ Rh)
    (bf : Pf ⊣ Sf) (bg : Pg ⊣ Sg) (bh : Ph ⊣ Sh)
    (ef : Rf ≅ Sf) (eg : Rg ≅ Sg) (eh : Rh ≅ Sh)
    (c : Rh ≅ Rg ⋙ Rf) (d : Sh ≅ Sg ⋙ Sf)
    (H : eh.symm ≪≫ c = d ≪≫ Functor.isoWhiskerLeft Sg ef.symm ≪≫
      Functor.isoWhiskerRight eg.symm Rf) :
    Adjunction.leftAdjointCompIso af ag ah c.symm ≪≫
        (ah.ofNatIsoRight eh).leftAdjointUniq bh =
      Functor.isoWhiskerLeft Lf ((ag.ofNatIsoRight eg).leftAdjointUniq bg) ≪≫
        Functor.isoWhiskerRight ((af.ofNatIsoRight ef).leftAdjointUniq bf) Pg ≪≫
        Adjunction.leftAdjointCompIso bf bg bh d.symm := by
  have h := conjugate_composition_injective ag af ah bg bf bh
    ((ag.ofNatIsoRight eg).leftAdjointUniq bg).symm
    ((af.ofNatIsoRight ef).leftAdjointUniq bf).symm
    ((ah.ofNatIsoRight eh).leftAdjointUniq bh).symm
    (Adjunction.leftAdjointCompIso af ag ah c.symm).symm
    (Adjunction.leftAdjointCompIso bf bg bh d.symm).symm
    (by
      rw [conjugate_leftAdjointComp, conjugate_leftAdjointComp,
        bridge_conjugate, bridge_conjugate, bridge_conjugate]
      have hi := congrArg Iso.inv H
      simp only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
        Functor.isoWhiskerRight_inv] at hi
      apply NatTrans.ext
      funext X
      have hx := congr_app hi X
      simp only [Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Category.assoc] at hx ⊢
      rw [← ef.hom.naturality_assoc (eg.hom.app X)]
      exact hx)
  have hi := congrArg Iso.inv h
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have hx := congr_app hi M
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.trans_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] at hx ⊢
  rw [((ag.ofNatIsoRight eg).leftAdjointUniq bg).hom.naturality_assoc
    (((af.ofNatIsoRight ef).leftAdjointUniq bf).hom.app M)] at hx
  exact hx
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf HasDerivedCategory.standard DerivedCategory.Q
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryNatIso
attribute [local implicit_reducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition integralCoefficientCommRingSheaf
  integralCoefficientSheaf integralCoefficientSheafTransition
  WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf WeilConjectures.SemilinearSections.rings
  sheafCompose ProEtale.SemilinearProperOpen.derived RingHom.ulift

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The section-normalized bridge respects one binary open compositor.
Source: Stacks 03D8, 07A7 and 0F7D; Zheng Lemma 4.10.
(blueprint: lem-sf-integral-system-open-compositor-bridge).
Proof: compare the ordinary direct-image compositor with the intrinsic one on
sections at every pair (n,V). Both restrict the input section along the same
canonical pullback-composition isomorphism; the bridge acts identically on these
sections. Sheaf morphism extensionality gives the ordinary compositor square.
Transpose it along the two ordinary inverse-image adjunctions: conjugation
preserves composition and whiskering, so the corresponding pullback compositor
square commutes. Apply exact localization to complexes and use the representative
equation of c.pullComp to identify the derived square. Finally conjugate along
the open adjunctions. The open bridge is left-adjoint uniqueness and openComp is
leftAdjointCompIso for that same pullback compositor, so its conjugate is exactly
the displayed equation. This applies also to identities and empty opens. -/
theorem integralSystemOpenCompositorBridge
    (o : Operations l E) (c : Compositors l E o) (b : CanonicalBridge l E o)
    {U V X : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] (M : System l E U) :
    (c.openComp l E j k).hom.app M ≫ (b.shriek l E (j ≫ k)).hom.app M =
      (b.shriek l E k).hom.app ((Operations.shriek l E o j).obj M) ≫
        (ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) k).map
          ((b.shriek l E j).hom.app M) ≫
        (ProEtale.SemilinearProperOpen.jComp (scalarRings l E) (scalarTransitions l E)
          j k).hom.app M  := by
  have hh := open_composition
    (o.extension j).adj (o.extension k).adj (o.extension (j ≫ k)).adj
    (ProEtale.SemilinearProperOpen.jAdj (scalarRings l E) (scalarTransitions l E) j)
    (ProEtale.SemilinearProperOpen.jAdj (scalarRings l E) (scalarTransitions l E) k)
    (ProEtale.SemilinearProperOpen.jAdj (scalarRings l E) (scalarTransitions l E) (j ≫ k))
    (b.pull l E j) (b.pull l E k) (b.pull l E (j ≫ k))
    (c.pullComp j k)
    (ProEtale.SemilinearProperOpen.pComp (scalarRings l E) (scalarTransitions l E) j k)
    (pull_bridge_composition l E o c b j k)
  exact congr_app (congrArg Iso.hom hh) M

end WeilConjectures.IntegralSystemRealization

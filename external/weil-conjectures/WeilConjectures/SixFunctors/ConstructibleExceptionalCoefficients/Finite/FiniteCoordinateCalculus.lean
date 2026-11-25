/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate

import all WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
import all WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicConjugateComparisonTransport
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique

/-! # Proved finite coefficient coordinate calculus -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w
open CategoryTheory
namespace WeilConjectures.ConstructibleExceptionalCoefficients

open CategoryTheory.Limits
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
set_option backward.defeqAttrib.useBackward true

private theorem uniq_compositor
    {C D E : Type*} [Category C] [Category D] [Category E]
    {Lg Lgi : C ⥤ D} {Lf Lfi : D ⥤ E} {Lc Lci : C ⥤ E}
    {Rg : D ⥤ C} {Rf : E ⥤ D} {Rc : E ⥤ C}
    (ag : Lg ⊣ Rg) (agi : Lgi ⊣ Rg) (af : Lf ⊣ Rf) (afi : Lfi ⊣ Rf)
    (ac : Lc ⊣ Rc) (aci : Lci ⊣ Rc) (ki : Lci ≅ Lgi ⋙ Lfi) :
    ac.leftAdjointUniq aci ≪≫ ki =
      (conjugateIsoEquiv (ag.comp af) ac).symm
          (conjugateIsoEquiv (agi.comp afi) aci ki) ≪≫
        Functor.isoWhiskerLeft Lg (af.leftAdjointUniq afi) ≪≫
        Functor.isoWhiskerRight (ag.leftAdjointUniq agi) Lfi := by
  apply (conjugateIsoEquiv (agi.comp afi) ac).injective
  simp only [← Iso.trans_assoc]
  rw [conjugateIsoEquiv_trans (agi.comp afi) aci ac,
    conjugateIsoEquiv_trans (agi.comp afi) (ag.comp afi) ac,
    conjugateIsoEquiv_trans (ag.comp afi) (ag.comp af) ac,
    Equiv.apply_symm_apply,
    conjugateIsoEquiv_isoWhiskerRight, conjugateIsoEquiv_isoWhiskerLeft]
  apply Iso.ext
  simp only [Iso.trans_hom, conjugateIsoEquiv_apply_hom,
    conjugateEquiv_leftAdjointUniq_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom]
  ext N
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  erw [Category.id_comp, Category.id_comp]

private theorem adj_right_refl
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) : a.ofNatIsoRight (Iso.refl R) = a := by
  apply Adjunction.ext
  ext K
  simp [Adjunction.ofNatIsoRight]

private theorem uniq_compositor_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    {Lg Lgi : C ⥤ D} {Lf Lfi : D ⥤ E} {Lc Lci : C ⥤ E}
    {Rg Rgi : D ⥤ C} {Rf Rfi : E ⥤ D} {Rc Rci : E ⥤ C}
    (ag : Lg ⊣ Rg) (agi : Lgi ⊣ Rgi) (af : Lf ⊣ Rf) (afi : Lfi ⊣ Rfi)
    (ac : Lc ⊣ Rc) (aci : Lci ⊣ Rci)
    (hg : Rg = Rgi) (hf : Rf = Rfi) (hc : Rc = Rci)
    (ki : Lci ≅ Lgi ⋙ Lfi) :
    ((ac.ofNatIsoRight (eqToIso hc)).leftAdjointUniq aci) ≪≫ ki =
      (conjugateIsoEquiv (ag.comp af) ac).symm
        (Functor.isoWhiskerRight (eqToIso hf) Rg ≪≫
          Functor.isoWhiskerLeft Rfi (eqToIso hg) ≪≫
          conjugateIsoEquiv (agi.comp afi) aci ki ≪≫ (eqToIso hc).symm) ≪≫
        Functor.isoWhiskerLeft Lg ((af.ofNatIsoRight (eqToIso hf)).leftAdjointUniq afi) ≪≫
        Functor.isoWhiskerRight ((ag.ofNatIsoRight (eqToIso hg)).leftAdjointUniq agi) Lfi := by
  subst Rgi Rfi Rci
  simpa only [eqToIso_refl, Functor.isoWhiskerRight_refl, Functor.isoWhiskerLeft_refl,
    Iso.refl_trans, Iso.trans_refl, Iso.refl_symm, adj_right_refl] using
      uniq_compositor ag agi af afi ac aci ki

private theorem coordinate_square_comp
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (e₀ : C₀ ⥤ D₀) (e₁ : C₁ ⥤ D₁) (e₂ : C₂ ⥤ D₂)
    (Lg : C₀ ⥤ C₁) (Lf : C₁ ⥤ C₂) (Lc : C₀ ⥤ C₂)
    (Pg Ig : D₀ ⥤ D₁) (Pf If : D₁ ⥤ D₂) (Pc Ic : D₀ ⥤ D₂)
    (qg : Pg ≅ Ig) (qf : Pf ≅ If) (qc : Pc ≅ Ic)
    (wg : e₀ ⋙ Ig ≅ Lg ⋙ e₁) (wf : e₁ ⋙ If ≅ Lf ⋙ e₂)
    (wc : e₀ ⋙ Ic ≅ Lc ⋙ e₂)
    (cf : Lc ≅ Lg ⋙ Lf) (ci : Ic ≅ Ig ⋙ If) (cr : Pc ≅ Pg ⋙ Pf)
    (hq : qc ≪≫ ci = cr ≪≫ Functor.isoWhiskerLeft Pg qf ≪≫
      Functor.isoWhiskerRight qg If)
    (M : C₀)
    (hw : wc.hom.app M ≫ e₂.map (cf.hom.app M) =
      ci.hom.app (e₀.obj M) ≫ If.map (wg.hom.app M) ≫ wf.hom.app (Lg.obj M)) :
    (qc.hom.app (e₀.obj M) ≫ wc.hom.app M) ≫ e₂.map (cf.hom.app M) =
      cr.hom.app (e₀.obj M) ≫
        Pf.map (qg.hom.app (e₀.obj M) ≫ wg.hom.app M) ≫
          qf.hom.app (e₁.obj (Lg.obj M)) ≫ wf.hom.app (Lg.obj M) := by
  have h := congrArg (fun t ↦ t.hom.app (e₀.obj M)) hq
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app] at h
  rw [Category.assoc, hw, ← Category.assoc, ← Category.assoc, h]
  simp only [Category.assoc, Pf.map_comp]
  rw [← qf.hom.naturality_assoc, ← qf.hom.naturality_assoc]
  simp only [Functor.comp_obj]

private theorem realization_coordinate_comp
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (e₀ : C₀ ≌ D₀) (e₁ : C₁ ≌ D₁) (e₂ : C₂ ≌ D₂)
    (Lg : C₀ ⥤ C₁) (Lf : C₁ ⥤ C₂) (Lc : C₀ ⥤ C₂)
    (Pg : D₀ ⥤ D₁) (Pf : D₁ ⥤ D₂) (Pc : D₀ ⥤ D₂)
    (qg : Pg ≅ e₀.inverse ⋙ Lg ⋙ e₁.functor)
    (qf : Pf ≅ e₁.inverse ⋙ Lf ⋙ e₂.functor)
    (qc : Pc ≅ e₀.inverse ⋙ Lc ⋙ e₂.functor)
    (cf : Lc ≅ Lg ⋙ Lf) (cr : Pc ≅ Pg ⋙ Pf)
    (hq : qc ≪≫
        (Functor.isoWhiskerLeft e₀.inverse (Functor.isoWhiskerRight cf e₂.functor) ≪≫
          Functor.isoWhiskerLeft e₀.inverse
            (Functor.isoWhiskerRight
              (Functor.isoWhiskerLeft Lg (e₁.funInvIdAssoc Lf).symm) e₂.functor)) =
      cr ≪≫ Functor.isoWhiskerLeft Pg qf ≪≫
        Functor.isoWhiskerRight qg (e₁.inverse ⋙ Lf ⋙ e₂.functor)) (M : C₀) :
    (Functor.isoWhiskerLeft e₀.functor qc ≪≫
        e₀.funInvIdAssoc (Lc ⋙ e₂.functor)).hom.app M ≫ e₂.functor.map (cf.hom.app M) =
      cr.hom.app (e₀.functor.obj M) ≫
        Pf.map ((Functor.isoWhiskerLeft e₀.functor qg ≪≫
          e₀.funInvIdAssoc (Lg ⋙ e₁.functor)).hom.app M) ≫
        (Functor.isoWhiskerLeft e₁.functor qf ≪≫
          e₁.funInvIdAssoc (Lf ⋙ e₂.functor)).hom.app (Lg.obj M) := by
  have hw := AlgebraicGeometry.Scheme.transport_comp_square e₀ e₁ e₂ Lg Lf Lc cf M
  have hw' := Functor.square_reverse (e₁.inverse ⋙ Lf ⋙ e₂.functor)
    ((e₀.funInvIdAssoc (Lc ⋙ e₂.functor)).symm.app M)
    ((e₁.funInvIdAssoc (Lf ⋙ e₂.functor)).symm.app (Lg.obj M))
    ((e₀.funInvIdAssoc (Lg ⋙ e₁.functor)).symm.app M) _ _ hw
  exact coordinate_square_comp e₀.functor e₁.functor e₂.functor Lg Lf Lc
    Pg _ Pf _ Pc _ qg qf qc
    (e₀.funInvIdAssoc (Lg ⋙ e₁.functor))
    (e₁.funInvIdAssoc (Lf ⋙ e₂.functor))
    (e₀.funInvIdAssoc (Lc ⋙ e₂.functor)) cf _ cr hq M hw'

section ExactSquares
variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  [Abelian C] [Abelian D] [Abelian E] [Abelian F]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory F]

private theorem derived_square_left_comp
    (U : C ⥤ D) {L L' : D ⥤ F} (V : C ⥤ E) (H : E ⥤ F)
    [U.Additive] [L.Additive] [L'.Additive] [V.Additive] [H.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (z : L ≅ L') (o : U ⋙ L' ≅ V ⋙ H) :
    (Functor.mapDerivedCategorySquareIso (Functor.isoWhiskerLeft U z ≪≫ o)).hom =
      Functor.whiskerLeft U.mapDerivedCategory (Functor.mapDerivedCategoryNatIso z).hom ≫
        (Functor.mapDerivedCategorySquareIso o).hom := by
  have hz := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft U z
  apply (cancel_epi (Functor.mapDerivedCategoryCompIso U L).inv).mp
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapDerivedCategoryNatIso_trans, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← reassoc_of% hz, Iso.inv_hom_id_assoc]

private theorem exact_unit_square
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [G.Additive] [H.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (d : R₁ ⋙ G ≅ H ⋙ R₂)
    (β : G ⋙ L₂ ≅ L₁ ⋙ H)
    (hβ : ∀ K, a₂.unit.app (G.obj K) ≫ R₂.map (β.hom.app K) =
      G.map (a₁.unit.app K) ≫ d.hom.app (L₁.obj K))
    (K : DerivedCategory C) :
    (exactLocalizationDerivedAdjunction a₂).unit.app (G.mapDerivedCategory.obj K) ≫
        R₂.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso β).hom.app K) =
      G.mapDerivedCategory.map ((exactLocalizationDerivedAdjunction a₁).unit.app K) ≫
        (Functor.mapDerivedCategorySquareIso d).hom.app (L₁.mapDerivedCategory.obj K) := by
  let α := Functor.whiskerLeft G.mapDerivedCategory
      (exactLocalizationDerivedAdjunction a₂).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Functor.mapDerivedCategorySquareIso β).hom R₂.mapDerivedCategory
  let γ := Functor.whiskerRight (exactLocalizationDerivedAdjunction a₁).unit
      G.mapDerivedCategory ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft L₁.mapDerivedCategory (Functor.mapDerivedCategorySquareIso d).hom
  have he : α = γ := by
    apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    intro T
    simpa only [α, γ, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id] using CategoryTheory.mate_unit_Q a₁ a₂ d β hβ T
  simpa only [α, γ, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using congr_app he K
end ExactSquares

private theorem uniq_counit
    {C D : Type*} [Category C] [Category D]
    {L Li : C ⥤ D} {R Ri : D ⥤ C} (a : L ⊣ R) (b : Li ⊣ Ri) (p : R ≅ Ri)
    {Z : C} (N : D) (t : Z ⟶ Ri.obj N) :
    ((a.ofNatIsoRight p).leftAdjointUniq b).hom.app Z ≫ Li.map t ≫ b.counit.app N =
      L.map (t ≫ p.inv.app N) ≫ a.counit.app N := by
  rw [← NatTrans.naturality_assoc,
    Adjunction.leftAdjointUniq_hom_app_counit]
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, L.map_comp, Category.assoc]

private theorem transported_open_unit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (e : C ≌ C') (f : D ≌ D') {J : C ⥤ D} {U : D ⥤ C} (adj : J ⊣ U)
    (K : C) :
    (((e.symm.toAdjunction.comp adj).comp f.toAdjunction).unit.app (e.functor.obj K)) ≫
      (f.inverse ⋙ U ⋙ e.functor).map
        (f.functor.map (J.map (e.unitIso.inv.app K))) =
      e.functor.map (adj.unit.app K) ≫
        e.functor.map (U.map (f.unitIso.hom.app (J.obj K))) := by
  simp only [Adjunction.comp_unit_app, Equivalence.toAdjunction_unit,
    Equivalence.symm_unit, Functor.comp_map, Category.assoc]
  change e.counitIso.inv.app (e.functor.obj K) ≫
    e.functor.map (adj.unit.app (e.inverse.obj (e.functor.obj K))) ≫
    e.functor.map (U.map (f.unitIso.hom.app _)) ≫
    e.functor.map (U.map (f.inverse.map (f.functor.map (J.map (e.unitIso.inv.app K))))) = _
  have hf := f.unitIso.hom.naturality (J.map (e.unitIso.inv.app K))
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hf
  have he := adj.unit.naturality (e.unitIso.inv.app K)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at he
  simp only [← e.functor.map_comp, ← U.map_comp]
  rw [← hf, U.map_comp, ← Category.assoc, ← he, Category.assoc]
  rw [e.functor.map_comp, ← Category.assoc, e.counitInv_functor_comp]
  erw [Category.id_comp]

private theorem open_unit_coordinates
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (e : C ≌ C') (f : D ≌ D') {J : C ⥤ D} {U : D ⥤ C} (adj : J ⊣ U)
    {Jr : C' ⥤ D'} {Pr : D' ⥤ C'} (ar : Jr ⊣ Pr)
    (q : Pr ≅ f.inverse ⋙ U ⋙ e.functor) (K : C) :
    let ai := (e.symm.toAdjunction.comp adj).comp f.toAdjunction
    let z := (ar.ofNatIsoRight q).leftAdjointUniq ai
    let w : e.functor ⋙ (e.inverse ⋙ J ⋙ f.functor) ≅ J ⋙ f.functor :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight e.unitIso.symm _ ≪≫ Functor.leftUnitor _
    let o := Functor.isoWhiskerLeft e.functor z ≪≫ w
    let v := Functor.isoWhiskerLeft f.functor q ≪≫ f.funInvIdAssoc (U ⋙ e.functor)
    ar.unit.app (e.functor.obj K) ≫ Pr.map (o.hom.app K) =
      e.functor.map (adj.unit.app K) ≫ v.inv.app (J.obj K) := by
  dsimp only
  let ai := (e.symm.toAdjunction.comp adj).comp f.toAdjunction
  let z := (ar.ofNatIsoRight q).leftAdjointUniq ai
  let w : e.functor ⋙ (e.inverse ⋙ J ⋙ f.functor) ≅ J ⋙ f.functor :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e.unitIso.symm _ ≪≫ Functor.leftUnitor _
  have hz := Adjunction.unit_leftAdjointUniq_hom_app (ar.ofNatIsoRight q) ai
    (e.functor.obj K)
  have hz' : ar.unit.app (e.functor.obj K) ≫ Pr.map (z.hom.app (e.functor.obj K)) =
      ai.unit.app (e.functor.obj K) ≫ q.inv.app _ := by
    have hh := congrArg (fun t ↦ t ≫ q.inv.app _) hz
    simpa only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Category.assoc, ← q.hom.naturality_assoc,
      Iso.hom_inv_id_app, Category.comp_id, z] using hh
  change ar.unit.app (e.functor.obj K) ≫
      Pr.map (z.hom.app (e.functor.obj K) ≫ w.hom.app K) =
    e.functor.map (adj.unit.app K) ≫
      (f.funInvIdAssoc (U ⋙ e.functor)).inv.app (J.obj K) ≫ q.inv.app _
  rw [Pr.map_comp, ← Category.assoc, hz', Category.assoc]
  erw [← q.inv.naturality (w.hom.app K)]
  rw [← Category.assoc]
  have hm : w.hom.app K = f.functor.map (J.map (e.unitIso.inv.app K)) := by
    simp only [w, Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
      Functor.whiskerRight_app, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app]
    erw [Category.id_comp, Category.comp_id]
    rfl
  change (ai.unit.app _ ≫ (f.inverse ⋙ U ⋙ e.functor).map (w.hom.app K)) ≫ _ = _
  rw [hm]
  have ht := transported_open_unit e f adj K
  simp only [Equivalence.funInvIdAssoc_inv_app, Functor.comp_map, Equivalence.unit,
    Category.assoc, ai]
  simpa only [Functor.comp_map, Functor.comp_obj, Category.assoc] using
    congrArg (fun t ↦ t ≫ q.inv.app (f.functor.obj (J.obj K))) ht

private theorem restriction_coordinate_square
    {CA DA EA CB DB EB : Type*}
    [Category CA] [Category DA] [Category EA]
    [Category CB] [Category DB] [Category EB]
    {FA : EA ⥤ DA} {RA : DA ⥤ EA} {FB : EB ⥤ DB} {RB : DB ⥤ EB}
    (adjA : FA ⊣ RA) (adjB : FB ⊣ RB)
    (U₁A : DA ⥤ CA) (U₂A : EA ⥤ CA) (U₁B : DB ⥤ CB) (U₂B : EB ⥤ CB)
    (QX : CA ⥤ CB) (Q₁ : DA ⥤ DB) (Q₂ : EA ⥤ EB)
    (kA : U₂A ≅ FA ⋙ U₁A) (kB : U₂B ≅ FB ⋙ U₁B)
    (l₁ : Q₁ ⋙ U₁B ≅ U₁A ⋙ QX) (l₂ : Q₂ ⋙ U₂B ≅ U₂A ⋙ QX)
    (lv : Q₂ ⋙ FB ≅ FA ⋙ Q₁) (χ : RA ⋙ Q₂ ⟶ Q₁ ⋙ RB)
    (hc : ∀ M, FB.map (χ.app M) ≫ adjB.counit.app (Q₁.obj M) =
      lv.hom.app (RA.obj M) ≫ Q₁.map (adjA.counit.app M))
    (hk : ∀ N, kB.hom.app (Q₂.obj N) ≫ U₁B.map (lv.hom.app N) ≫
        l₁.hom.app (FA.obj N) = l₂.hom.app N ≫ QX.map (kA.hom.app N))
    (M : DA) :
    let ρ := Functor.whiskerLeft RB kB.hom ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight adjB.counit U₁B
    U₂B.map (χ.app M) ≫ ρ.app (Q₁.obj M) =
      l₂.hom.app (RA.obj M) ≫
        QX.map (kA.hom.app (RA.obj M) ≫ U₁A.map (adjA.counit.app M)) ≫ l₁.inv.app M := by
  have ht := AlgebraicGeometry.Etale.restriction_coefficient_mate adjA adjB
    U₁A U₂A U₁B U₂B QX Q₁ Q₂ kA kB l₁ l₂ lv χ hc hk M
  simp only [← Category.assoc] at ht
  have ht' := (l₁.app M).eq_comp_inv.mpr ht
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.comp_obj, Category.id_comp, QX.map_comp,
    Category.assoc, Iso.app_inv] using ht'

/-- Conjugate an arbitrary restriction endomorphism through compatible coordinate squares.
Source: Stacks Tags 03D6 and 03DI, the unit-square and counit-square calculation in
compactification coherence (blueprint: lem-sf-finite-coordinate-calculus).

Proof: invert the first unit square by cancelling its isomorphisms. Expand the
image of the inserted composite. Substitute the second unit square, move the
arbitrary arrow through the inverse pull coordinate by naturality, and move the
first object comparison through the restriction by naturality. Apply the
restriction square, cancel the second pull coordinates, and substitute the
inverse first unit square. Functoriality gives the conjugated endomorphism.
No nonempty object or nonzero morphism assumption is used. -/
theorem restriction_endomorphism_coordinates
    {C D T C' D' T' : Type*}
    [Category C] [Category D] [Category T] [Category C'] [Category D'] [Category T']
    (e : C ⥤ C') (ed : D ⥤ D') (et : T ⥤ T')
    (U₁ : D ⥤ C) (U₂ : T ⥤ C) (P : D ⥤ T)
    (V₁ : D' ⥤ C') (V₂ : T' ⥤ C') (Q : D' ⥤ T')
    (s : ed ⋙ Q ≅ P ⋙ et) (v₁ : ed ⋙ V₁ ≅ U₁ ⋙ e) (v₂ : et ⋙ V₂ ≅ U₂ ⋙ e)
    (ρ : P ⋙ U₂ ⟶ U₁) (ρ' : Q ⋙ V₂ ⟶ V₁)
    {K : C} {M : C'} (a : M ≅ e.obj K) {N₁ : D} {N₂ : T} {L₁ : D'} {L₂ : T'}
    (u₁ : K ≅ U₁.obj N₁) (u₂ : K ⟶ U₂.obj N₂)
    (u₁' : M ≅ V₁.obj L₁) (u₂' : M ⟶ V₂.obj L₂)
    (o₁ : L₁ ≅ ed.obj N₁) (o₂ : L₂ ≅ et.obj N₂)
    (h₁ : u₁'.hom ≫ V₁.map o₁.hom = a.hom ≫ e.map u₁.hom ≫ v₁.inv.app N₁)
    (h₂ : u₂' ≫ V₂.map o₂.hom = a.hom ≫ e.map u₂ ≫ v₂.inv.app N₂)
    (hρ : V₂.map (s.inv.app N₁) ≫ ρ'.app (ed.obj N₁) =
      v₂.hom.app (P.obj N₁) ≫ e.map (ρ.app N₁) ≫ v₁.inv.app N₁)
    (m : N₂ ⟶ P.obj N₁) :
    u₂' ≫ V₂.map (o₂.hom ≫ et.map m ≫ s.inv.app N₁ ≫ Q.map o₁.inv) ≫
        ρ'.app L₁ ≫ u₁'.inv =
      a.hom ≫ e.map (u₂ ≫ U₂.map m ≫ ρ.app N₁ ≫ u₁.inv) ≫ a.inv := by
  have hi : v₁.inv.app N₁ ≫ V₁.map o₁.inv ≫ u₁'.inv = e.map u₁.inv ≫ a.inv := by
    have hh := congrArg
      (fun t ↦ e.map u₁.inv ≫ a.inv ≫ t ≫ V₁.map o₁.inv ≫ u₁'.inv) h₁
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, ← V₁.map_comp_assoc,
      ← e.map_comp_assoc, Iso.hom_inv_id, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id, Iso.hom_inv_id_assoc] using hh.symm
  have hn := v₂.inv.naturality m
  dsimp only [Functor.comp_map] at hn
  have hr := ρ'.naturality o₁.inv
  dsimp only [Functor.comp_map] at hr
  simp only [V₂.map_comp, Category.assoc]
  rw [reassoc_of% h₂, ← reassoc_of% hn, reassoc_of% hr, reassoc_of% hρ]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [hi]
  simp only [e.map_comp, Category.assoc]

end WeilConjectures.ConstructibleExceptionalCoefficients

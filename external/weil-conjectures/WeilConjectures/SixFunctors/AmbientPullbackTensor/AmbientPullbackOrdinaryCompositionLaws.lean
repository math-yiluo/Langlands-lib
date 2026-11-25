/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackTensorData
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPushforwardCompositionSections

/-! Ordinary pullback associativity and unit laws.

Source: Stacks 03CB, 03D3 and 04VG.
(blueprint: new-lem-sf-ambient-pullback-ordinary-composition-laws).

This is the ordinary part of the ambient pullback coherence argument.  The
section-normalized direct-image comparison is pasted over the canonical
fibre-product comparisons; adjunction mates then give the three displayed
identities.  The proof is split from the derived localization step so that the
ordinary and derived calculations can be completed independently.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSimpArgs false
set_option linter.style.emptyLine false
set_option linter.style.cdot false
set_option linter.style.longLine false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections
namespace WeilConjectures.AmbientPullbackTensor
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]

attribute [local irreducible] pull CategoryTheory.Functor.leftAdjoint

private theorem directImage_transport
    {X Y : Scheme.{t}} {f g : X ⟶ Y} (e : f = g)
    (s : Option ℕ) (N : Modules ell E X s) (U : Site Y s)
    (m : ((push ell E f s).obj N).val.obj (op U)) :
    ((eqToIso (congrArg (fun a ↦ push ell E a s) e)).hom.app N).val.app (op U) m =
      N.val.map (eqToHom (congrArg (fun a ↦ (base a s).obj U) e.symm)).op m := by
  cases e
  change m = N.val.map (𝟙 _) m
  rw [PresheafOfModules.map_id]
  rfl

private theorem directComp_hom_apply
    {V W Z : Scheme.{t}} (h : Z ⟶ W) (k : W ⟶ V) (s : Option ℕ)
    (N : Modules ell E Z s) (U : Site V s)
    (m : ((push ell E h s ⋙ push ell E k s).obj N).val.obj (op U)) :
    ((pushComp ell E h k s).inv.app N).val.app (op U) m =
      N.val.map ((baseComp h k s).hom.app U).op m := by
  exact pushComp_inverse_sections ell E h k s N U m

private theorem directImage_map_apply
    {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) {N N' : Modules ell E X s}
    (a : N ⟶ N') (U : Site Y s)
    (m : ((push ell E f s).obj N).val.obj (op U)) :
    (((push ell E f s).map a).val.app (op U)) m =
      a.val.app (op ((base f s).obj U)) m := rfl

private theorem directImage_obj_map_apply
    {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) (N : Modules ell E X s)
    {U V : Site Y s} (a : U ⟶ V)
    (m : ((push ell E f s).obj N).val.obj (op V)) :
    (((push ell E f s).obj N).val.map a.op) m =
      N.val.map ((base f s).map a).op m := rfl

private theorem restriction_pasting
    {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat}
    (N : PresheafOfModules R) {U V T U' V' : C}
    (a : U ⟶ V) (b : V ⟶ T) (c : U ⟶ U') (d : U' ⟶ V') (e : V' ⟶ T)
    (h : a ≫ b = c ≫ d ≫ e) (m : N.obj (op T)) :
    N.map a.op (N.map b.op m) = N.map c.op (N.map d.op (N.map e.op m)) := by
  rw [← PresheafOfModules.map_comp_apply, ← op_comp,
    ← PresheafOfModules.map_comp_apply, ← op_comp,
    ← PresheafOfModules.map_comp_apply, ← op_comp]
  rw [h, Category.assoc]

private theorem pasting_transport
    {C : Type*} [Category C] [HasPullbacks C] {P Q : MorphismProperty C}
    [P.IsStableUnderBaseChange] [Q.IsMultiplicative] [Q.RespectsIso]
    [Q.IsStableUnderBaseChange]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (e : fg = f ≫ g) (U : P.Over Q Z) :
    (MorphismProperty.Over.pullbackComp (P := P) (Q := Q) f g fg e).hom.app U =
      eqToHom (congrArg (fun t ↦ (MorphismProperty.Over.pullback P Q t).obj U) e) ≫
        (MorphismProperty.Over.pullbackComp (P := P) (Q := Q) f g).hom.app U := by
  cases e
  simp

private theorem site_pasting
    {W X Y Z : Scheme.{t}} (j : W ⟶ X) (h : X ⟶ Y) (k : Y ⟶ Z)
    (s : Option ℕ) (U : Site Z s) :
    (baseComp j (h ≫ k) s).hom.app U ≫
        (base j s).map ((baseComp h k s).hom.app U) =
      eqToHom (congrArg (fun a ↦ (base a s).obj U)
        (Category.assoc j h k).symm) ≫
        (baseComp (j ≫ h) k s).hom.app U ≫
        (baseComp j h s).hom.app ((base k s).obj U) := by
  cases s with
  | some n =>
      have hp := NatTrans.congr_app (congrArg Iso.hom
        (MorphismProperty.Over.pullbackComp_assoc (P := @WeaklyEtale) (Q := ⊤)
          j h k)) U
      simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
        Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Category.comp_id] at hp
      rw [pasting_transport (P := @WeaklyEtale) (Q := ⊤) (j ≫ h) k
        (j ≫ h ≫ k) (Category.assoc j h k).symm U] at hp
      simpa only [base, baseComp, Category.assoc] using hp

  | none =>
      rcases U with ⟨n, U⟩
      apply Prod.hom_ext
      · rfl
      ·
        change (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale)
          (Q := ⊤) j (h ≫ k)).hom.app U ≫
            (Scheme.proEtaleBaseChange j).map
              ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale)
                (Q := ⊤) h k).hom.app U) =
          eqToHom (congrArg (fun a ↦
            (MorphismProperty.Over.pullback @WeaklyEtale ⊤ a).obj U)
              (Category.assoc j h k).symm) ≫
            (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale)
              (Q := ⊤) (j ≫ h) k).hom.app U ≫
            (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale)
              (Q := ⊤) j h).hom.app
                ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ k).obj U)
        have hp := NatTrans.congr_app (congrArg Iso.hom
          (MorphismProperty.Over.pullbackComp_assoc (P := @WeaklyEtale) (Q := ⊤)
            j h k)) U
        simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
          Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
          Functor.whiskerLeft_app, Functor.associator_hom_app, Category.comp_id] at hp
        rw [pasting_transport (P := @WeaklyEtale) (Q := ⊤) (j ≫ h) k
          (j ≫ h ≫ k) (Category.assoc j h k).symm U] at hp
        exact hp

private theorem directImage_coherence
    {W X Y Z : Scheme.{t}} (j : W ⟶ X) (h : X ⟶ Y) (k : Y ⟶ Z)
    (s : Option ℕ) :
    Functor.isoWhiskerLeft (push ell E j s) (pushComp ell E h k s).symm ≪≫
        (pushComp ell E j (h ≫ k) s).symm =
      (Functor.associator (push ell E j s) (push ell E h s) (push ell E k s)).symm ≪≫
        Functor.isoWhiskerRight (pushComp ell E j h s).symm (push ell E k s) ≪≫
        (pushComp ell E (j ≫ h) k s).symm ≪≫
        eqToIso (congrArg (fun a ↦ push ell E a s) (Category.assoc j h k)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U using Opposite.rec
  rename_i U
  ext m
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.id_obj,
    Functor.associator_inv_app, Category.id_comp,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [directImage_map_apply ell E k s ((pushComp ell E j h s).symm.hom.app N) U]
  erw [directComp_hom_apply ell E j h s N ((base k s).obj U)]
  erw [directComp_hom_apply ell E (j ≫ h) k s N U]
  conv_rhs => erw [directImage_transport ell E (Category.assoc j h k) s N U]
  conv_lhs => erw [directComp_hom_apply ell E h k s ((push ell E j s).obj N) U m]
  conv_lhs => erw [directComp_hom_apply ell E j (h ≫ k) s N U]
  conv_lhs => erw [directImage_obj_map_apply ell E j s N
    ((baseComp h k s).hom.app U)]
  exact restriction_pasting N.val _ _ _ _ _
    (site_pasting j h k s U) m

private theorem mate_transport
    {C D E I : Type*} [Category C] [Category D] [Category E]
    (L : I → C ⥤ E) (R : I → E ⥤ C) (adj : ∀ i, L i ⊣ R i)
    {F : C ⥤ D} {G : D ⥤ E} {F' : D ⥤ C} {G' : E ⥤ D}
    (aF : F ⊣ F') (aG : G ⊣ G') {i i' : I} (e : i = i')
    (d : G' ⋙ F' ≅ R i) :
    Adjunction.leftAdjointCompIso aF aG (adj i')
        (d ≪≫ eqToIso (congrArg R e)) =
      Adjunction.leftAdjointCompIso aF aG (adj i) d ≪≫ eqToIso (congrArg L e) := by
  cases e
  simp

private theorem ordinary_coherence
    {W X Y Z : Scheme.{t}} (j : W ⟶ X) (h : X ⟶ Y) (k : Y ⟶ Z)
    (s : Option ℕ) (M : Modules ell E Z s) :
    (pull ell E j s).map ((comp ell E h k s).hom.app M) ≫
        (comp ell E j (h ≫ k) s).hom.app M =
      (comp ell E j h s).hom.app ((pull ell E k s).obj M) ≫
        (comp ell E (j ≫ h) k s).hom.app M ≫
        eqToHom (congrArg (fun a ↦ (pull ell E a s).obj M)
          (Category.assoc j h k)) := by
  have hh := Adjunction.leftAdjointCompIso_assoc
    (adjunction ell E k s) (adjunction ell E h s) (adjunction ell E j s)
    (adjunction ell E (h ≫ k) s) (adjunction ell E (j ≫ h) s)
    (adjunction ell E (j ≫ h ≫ k) s)
    (pushComp ell E h k s).symm (pushComp ell E j h s).symm
    ((pushComp ell E (j ≫ h) k s).symm ≪≫
      eqToIso (congrArg (fun a ↦ push ell E a s) (Category.assoc j h k)))
    (pushComp ell E j (h ≫ k) s).symm
    (directImage_coherence ell E j h k s)
  have ht := mate_transport (fun a ↦ pull ell E a s) (fun a ↦ push ell E a s)
    (fun a ↦ adjunction ell E a s) (adjunction ell E k s)
    (adjunction ell E (j ≫ h) s) (Category.assoc j h k)
    (pushComp ell E (j ≫ h) k s).symm
  rw [ht] at hh
  have hi := NatTrans.congr_app (congrArg Iso.hom hh) M
  convert hi.symm using 1 <;>
    simp only [comp, Iso.symm_hom, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_obj, Functor.id_obj,
      Functor.associator_inv_app, Functor.associator_hom_app, Iso.symm_inv,
      Category.id_comp, Category.comp_id, Category.assoc, eqToIso.inv, eqToIso.hom, eqToHom_app]

private theorem site_rightUnit
    {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) (U : Site Y s) :
    eqToHom (congrArg (fun a ↦ (base a s).obj U) (Category.comp_id f).symm) ≫
        (baseComp f (𝟙 Y) s).hom.app U =
      (base f s).map ((baseId Y s).inv.app U) := by
  have hp (V : Y.ProEt) := NatTrans.congr_app (congrArg Iso.hom
    (MorphismProperty.Over.pullbackComp_id_right (P := @WeaklyEtale) (Q := ⊤) f)) V
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.leftUnitor_inv_app,
    MorphismProperty.Over.pullbackCongr_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp] at hp
  have hq (V : Y.ProEt) :=
    (pasting_transport (P := @WeaklyEtale) (Q := ⊤) f (𝟙 Y) f
      (Category.comp_id f).symm V).symm.trans (hp V)
  cases s with
  | some n => exact hq U
  | none =>
      rcases U with ⟨n, V⟩
      apply Prod.hom_ext
      · rfl
      · exact hq V

private theorem site_leftUnit
    {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) (U : Site Y s) :
    eqToHom (congrArg (fun a ↦ (base a s).obj U) (Category.id_comp f).symm) ≫
        (baseComp (𝟙 X) f s).hom.app U =
      (baseId X s).inv.app ((base f s).obj U) := by
  have hp (V : Y.ProEt) := NatTrans.congr_app (congrArg Iso.hom
    (MorphismProperty.Over.pullbackComp_id_left (P := @WeaklyEtale) (Q := ⊤) f)) V
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.rightUnitor_inv_app,
    MorphismProperty.Over.pullbackCongr_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp] at hp
  have hq (V : Y.ProEt) :=
    (pasting_transport (P := @WeaklyEtale) (Q := ⊤) (𝟙 X) f f
      (Category.id_comp f).symm V).symm.trans (hp V)
  cases s with
  | some n => exact hq U
  | none =>
      rcases U with ⟨n, V⟩
      apply Prod.hom_ext
      · rfl
      · exact hq V

private theorem directImage_rightUnit
    {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :
    (pushComp ell E f (𝟙 Y) s).symm ≪≫
        eqToIso (congrArg (fun a ↦ push ell E a s) (Category.comp_id f)) =
      Functor.isoWhiskerLeft (push ell E f s) (pushId ell E Y s) ≪≫
        Functor.rightUnitor (push ell E f s) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U using Opposite.rec
  rename_i U
  ext m
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply, Category.comp_id]
  erw [directImage_transport ell E (Category.comp_id f) s N U]
  erw [directComp_hom_apply ell E f (𝟙 Y) s N U]
  erw [(pushId_existsUnique ell E Y s).exists.choose_spec
    ((push ell E f s).obj N) U m]
  erw [directImage_obj_map_apply ell E f s N ((baseId Y s).inv.app U)]
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, site_rightUnit]
  rfl

private theorem directImage_leftUnit
    {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :
    (pushComp ell E (𝟙 X) f s).symm ≪≫
        eqToIso (congrArg (fun a ↦ push ell E a s) (Category.id_comp f)) =
      Functor.isoWhiskerRight (pushId ell E X s) (push ell E f s) ≪≫
        Functor.leftUnitor (push ell E f s) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U using Opposite.rec
  rename_i U
  ext m
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply, Category.comp_id]
  erw [directImage_transport ell E (Category.id_comp f) s N U]
  erw [directComp_hom_apply ell E (𝟙 X) f s N U]
  erw [directImage_map_apply ell E f s ((pushId ell E X s).hom.app N) U]
  erw [(pushId_existsUnique ell E X s).exists.choose_spec N ((base f s).obj U) m]
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, site_leftUnit]
  rfl

/-- Right-unit part of ordinary ambient pullback coherence.
Source: Stacks 03D3 and 04VG.
(blueprint: new-lem-sf-ambient-pullback-ordinary-right-unit).
The section-normalized identity comparison and the adjunction right-unit law give
this clause. -/
theorem ordinary_pullback_rightUnit (K : Scheme.{t}) (s : Option ℕ) :
    ∀ {X Y : Scheme.{t}} (f : X ⟶ Y) (aX : X ⟶ K) (aY : Y ⟶ K)
      [LocallyOfFiniteType aX] [QuasiCompact aX]
      [LocallyOfFiniteType aY] [QuasiCompact aY]
      (_hf : f ≫ aY = aX) (M : Modules ell E Y s),
      (pull ell E f s).map ((identity ell E Y s).hom.app M) =
        (comp ell E f (𝟙 Y) s).hom.app M ≫
          eqToHom (congrArg (fun a ↦ (pull ell E a s).obj M)
            (Category.comp_id f)) := by
  intro X Y f aX aY _ _ _ _ hf M
  have hh := Adjunction.leftAdjointCompIso_id_comp
    (adjunction ell E (𝟙 Y) s) (adjunction ell E f s)
    ((pushComp ell E f (𝟙 Y) s).symm ≪≫
      eqToIso (congrArg (fun a ↦ push ell E a s) (Category.comp_id f)))
    (pushId ell E Y s) (directImage_rightUnit ell E f s)
  rw [mate_transport (fun a ↦ pull ell E a s) (fun a ↦ push ell E a s)
    (fun a ↦ adjunction ell E a s) (adjunction ell E (𝟙 Y) s)
    (adjunction ell E f s) (Category.comp_id f)] at hh
  have hi := NatTrans.congr_app (congrArg Iso.hom hh) M
  simpa only [comp, identity, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.id_obj, Category.comp_id,
    eqToIso.hom, eqToHom_app] using hi.symm

/-- Left-unit part of ordinary ambient pullback coherence.
Source: Stacks 03D3 and 04VG.
(blueprint: new-lem-sf-ambient-pullback-ordinary-left-unit).
The section-normalized identity comparison and the adjunction left-unit law give
this clause. -/
theorem ordinary_pullback_leftUnit (K : Scheme.{t}) (s : Option ℕ) :
    ∀ {X Y : Scheme.{t}} (f : X ⟶ Y) (aX : X ⟶ K) (aY : Y ⟶ K)
      [LocallyOfFiniteType aX] [QuasiCompact aX]
      [LocallyOfFiniteType aY] [QuasiCompact aY]
      (_hf : f ≫ aY = aX) (M : Modules ell E Y s),
      (identity ell E X s).hom.app ((pull ell E f s).obj M) =
        (comp ell E (𝟙 X) f s).hom.app M ≫
          eqToHom (congrArg (fun a ↦ (pull ell E a s).obj M)
            (Category.id_comp f)) := by
  intro X Y f aX aY _ _ _ _ hf M
  have hh := Adjunction.leftAdjointCompIso_comp_id
    (adjunction ell E f s) (adjunction ell E (𝟙 X) s)
    ((pushComp ell E (𝟙 X) f s).symm ≪≫
      eqToIso (congrArg (fun a ↦ push ell E a s) (Category.id_comp f)))
    (pushId ell E X s) (directImage_leftUnit ell E f s)
  rw [mate_transport (fun a ↦ pull ell E a s) (fun a ↦ push ell E a s)
    (fun a ↦ adjunction ell E a s) (adjunction ell E f s)
    (adjunction ell E (𝟙 X) s) (Category.id_comp f)] at hh
  have hi := NatTrans.congr_app (congrArg Iso.hom hh) M
  simpa only [comp, identity, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj, Category.comp_id,
    eqToIso.hom, eqToHom_app] using hi.symm

/-- Ordinary associativity and unit laws for the ambient pullback comparisons.
Source: Stacks 03CB, 03D3 and 04VG.
(blueprint: new-lem-sf-ambient-pullback-ordinary-composition-laws).
Proof: paste the section-normalized direct-image comparisons over the canonical
fibre-product associativity and identity comparisons, then take their specified
adjunction mates.  The three component equations are exactly the associativity,
right-unit and left-unit clauses below. -/
theorem ordinary_pullback_compositionLaws (K : Scheme.{t}) (s : Option ℕ) :
    (∀ {W X Y Z : Scheme.{t}} (w : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
      (aW : W ⟶ K) (aX : X ⟶ K) (aY : Y ⟶ K) (aZ : Z ⟶ K)
      [LocallyOfFiniteType aW] [QuasiCompact aW] [LocallyOfFiniteType aX]
      [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
      [LocallyOfFiniteType aZ] [QuasiCompact aZ]
      (_hw : w ≫ aX = aW) (_hf : f ≫ aY = aX) (_hg : g ≫ aZ = aY)
      (M : Modules ell E Z s),
      (pull ell E w s).map ((comp ell E f g s).hom.app M) ≫
          (comp ell E w (f ≫ g) s).hom.app M =
        (comp ell E w f s).hom.app ((pull ell E g s).obj M) ≫
          (comp ell E (w ≫ f) g s).hom.app M ≫
          eqToHom (congrArg (fun a ↦ (pull ell E a s).obj M)
            (Category.assoc w f g))) ∧
    (∀ {X Y : Scheme.{t}} (f : X ⟶ Y) (aX : X ⟶ K) (aY : Y ⟶ K)
      [LocallyOfFiniteType aX] [QuasiCompact aX]
      [LocallyOfFiniteType aY] [QuasiCompact aY]
      (_hf : f ≫ aY = aX) (M : Modules ell E Y s),
      (pull ell E f s).map ((identity ell E Y s).hom.app M) =
        (comp ell E f (𝟙 Y) s).hom.app M ≫
          eqToHom (congrArg (fun a ↦ (pull ell E a s).obj M)
            (Category.comp_id f))) ∧
    (∀ {X Y : Scheme.{t}} (f : X ⟶ Y) (aX : X ⟶ K) (aY : Y ⟶ K)
      [LocallyOfFiniteType aX] [QuasiCompact aX]
      [LocallyOfFiniteType aY] [QuasiCompact aY]
      (_hf : f ≫ aY = aX) (M : Modules ell E Y s),
      (identity ell E X s).hom.app ((pull ell E f s).obj M) =
        (comp ell E (𝟙 X) f s).hom.app M ≫
          eqToHom (congrArg (fun a ↦ (pull ell E a s).obj M)
            (Category.id_comp f))) := by
  refine ⟨?_, ordinary_pullback_rightUnit ell E K s, ordinary_pullback_leftUnit ell E K s⟩
  intro W X Y Z w f g aW aX aY aZ _ _ _ _ _ _ _ _ hw hf hg M
  exact ordinary_coherence ell E w f g s M

end WeilConjectures.AmbientPullbackTensor

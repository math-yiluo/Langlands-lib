/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.Tower
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Canonical

/-!
# Associativity of the composition isomorphism in a compact support formalism

For a tower of compactifications `𝒯` of composable morphisms `f`, `g`, `h`
(`AlgebraicGeometry.Compactification.Tower`), the two composites
`Rf_! ⋙ Rg_! ⋙ Rh_! ≅ R(f ≫ g ≫ h)_!` built from the composition isomorphisms of the four
triangles of `𝒯` agree (`compIso_tower`): this is a pasting identity for the exchange maps of
the squares of the tower. Combined with the independence of the triangles, it gives the
associativity of the canonical composition isomorphism `F.lowerShriekCompIso`
(`lowerShriekCompIso_assoc`, blueprint `proposition-composition-base-change-rf-shriek--1`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits TwoSquare

namespace AlgebraicGeometry.CompactSupportFormalism

variable (F : CompactSupportFormalism.{w, v, u}) [F.HasProperExchange]

variable {X Y S T : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S} {h : S ⟶ T}

/-- **The pasting identity of a tower of compactifications**: the two composites of the
composition isomorphisms of the four triangles of a tower agree. -/
theorem compIso_tower (𝒯 : Compactification.Tower f g h) :
    Functor.whiskerRight (F.compIso 𝒯.fg).hom (F.shriek 𝒯.ch) ≫ (F.compIso 𝒯.fg_h).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (F.shriek 𝒯.cf) (F.compIso 𝒯.gh).hom ≫ (F.compIso 𝒯.f_gh).hom := by
  have := HasBaseChange.isIso_baseChange (F := F) 𝒯.isPullback_fg
  have := HasBaseChange.isIso_baseChange (F := F) 𝒯.isPullback_gh
  have := HasBaseChange.isIso_baseChange (F := F) 𝒯.isPullback_mid
  have : IsIso (F.baseChange 𝒯.cf.g (𝒯.q ≫ 𝒯.q') 𝒯.cgh.i 𝒯.p₁ 𝒯.f_gh.isPullback.w) :=
    HasBaseChange.isIso_baseChange (F := F) 𝒯.f_gh.isPullback
  have : IsIso (F.baseChange 𝒯.cfg.g 𝒯.q' 𝒯.ch.i (𝒯.p₁ ≫ 𝒯.p₂) 𝒯.fg_h.isPullback.w) :=
    HasBaseChange.isIso_baseChange (F := F) 𝒯.fg_h.isPullback
  ext K
  have hV := congr_app (F.exchange_paste_vert 𝒯.cf.g 𝒯.p 𝒯.p₁ 𝒯.q 𝒯.cg.i 𝒯.q' 𝒯.q₂
    (𝒯.q ≫ 𝒯.q') 𝒯.cgh.i 𝒯.isPullback_fg.w 𝒯.isPullback_mid.w rfl 𝒯.i_q₂
    𝒯.f_gh.isPullback.w) ((F.sh 𝒯.cf.i).obj K)
  have hH := congr_app (F.exchange_paste_horiz 𝒯.p 𝒯.cg.g 𝒯.q' 𝒯.q₂ 𝒯.ch.i 𝒯.p₁ 𝒯.p₂
    𝒯.cfg.g (𝒯.p₁ ≫ 𝒯.p₂) 𝒯.isPullback_mid.w 𝒯.isPullback_gh.w 𝒯.p_g rfl
    𝒯.fg_h.isPullback.w) ((F.sh 𝒯.cfg.i).obj K)
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, TwoSquare.hComp, TwoSquare.vComp, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Functor.comp_obj]
    at hV hH
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, compIso_hom_app]
  dsimp only [shriek, ExchangeFormalism.shriek, Functor.comp_obj, Functor.comp_map,
    Compactification.copy_i, Compactification.copy_g]
  have hPC := F.pfComp'_assoc_inv_app 𝒯.p₁ 𝒯.p₂ 𝒯.ch.g (𝒯.p₁ ≫ 𝒯.p₂) 𝒯.cgh.g 𝒯.cfgh.g rfl 𝒯.p₂_g
    𝒯.fg_h.p_g 𝒯.p₁_g ((F.sh 𝒯.cfgh.i).obj K)
  have hSC := F.shComp'_assoc_inv_app 𝒯.cf.i 𝒯.q 𝒯.q' 𝒯.cfg.i (𝒯.q ≫ 𝒯.q') 𝒯.cfgh.i 𝒯.i_q rfl
    𝒯.i_q' 𝒯.f_gh.i_q K
  -- naturality
  have hεgh := (F.exchange 𝒯.cg.g 𝒯.q₂ 𝒯.ch.i 𝒯.p₂ 𝒯.isPullback_gh.w).naturality
    ((F.exchange 𝒯.cf.g 𝒯.q 𝒯.cg.i 𝒯.p 𝒯.isPullback_fg.w).app ((F.sh 𝒯.cf.i).obj K) ≫
      (F.pf 𝒯.p).map ((F.shComp' 𝒯.cf.i 𝒯.q 𝒯.cfg.i 𝒯.i_q).inv.app K))
  have hεR := (F.exchange 𝒯.p 𝒯.q' 𝒯.q₂ 𝒯.p₁ 𝒯.isPullback_mid.w).naturality
    ((F.shComp' 𝒯.cf.i 𝒯.q 𝒯.cfg.i 𝒯.i_q).inv.app K)
  have hP := (F.pfComp' 𝒯.p₁ 𝒯.p₂ (𝒯.p₁ ≫ 𝒯.p₂) rfl).inv.naturality
    ((F.shComp' 𝒯.cfg.i 𝒯.q' 𝒯.cfgh.i 𝒯.i_q').inv.app K)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc] at hεgh hεR hP
  simp only [Category.assoc]
  rw [← NatTrans.naturality_assoc, hPC, ← Functor.map_comp_assoc]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc]
  refine congrArg (· ≫ _) (congrArg (F.pf 𝒯.ch.g).map ?_)
  rw [hH, hV]
  have hεR' := congrArg (F.pf 𝒯.p₂).map hεR
  have hSC' := congrArg (fun x ↦ (F.pf 𝒯.p₂).map ((F.pf 𝒯.p₁).map x)) hSC
  simp only [Functor.map_comp] at hεR' hSC'
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (F.sh 𝒯.ch.i) ((F.pfComp' 𝒯.p 𝒯.cg.g 𝒯.cfg.g 𝒯.p_g).inv.app _),
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% hεgh, reassoc_of% hεR']
  erw [← hP]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc, hSC]


section

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]

omit [F.HasProperExchange] in
private lemma whiskerRight_comp_hcomp {G G' G'' : A ⥤ B} {H H' : B ⥤ C} (α : G ⟶ G')
    (β : G' ⟶ G'') (γ : H ⟶ H') :
    Functor.whiskerRight α H ≫ NatTrans.hcomp β γ = NatTrans.hcomp (α ≫ β) γ := by
  ext; simp

omit [F.HasProperExchange] in
private lemma whiskerLeft_comp_hcomp {G G' : A ⥤ B} {H H' H'' : B ⥤ C} (α : H ⟶ H')
    (β : G ⟶ G') (γ : H' ⟶ H'') :
    Functor.whiskerLeft G α ≫ NatTrans.hcomp β γ = NatTrans.hcomp β (α ≫ γ) := by
  ext; simp

omit [F.HasProperExchange] in
private lemma hcomp_eq_whiskerLeft_comp_whiskerRight {G G' : A ⥤ B} {H H' : B ⥤ C}
    (α : G ⟶ G') (β : H ⟶ H') :
    NatTrans.hcomp α β = Functor.whiskerLeft G β ≫ Functor.whiskerRight α H' := by
  ext; simp

omit [F.HasProperExchange] in
private lemma hcomp_eq_whiskerRight_comp_whiskerLeft {G G' : A ⥤ B} {H H' : B ⥤ C}
    (α : G ⟶ G') (β : H ⟶ H') :
    NatTrans.hcomp α β = Functor.whiskerRight α H ≫ Functor.whiskerLeft G' β := by
  ext; simp

omit [F.HasProperExchange] in
private lemma hcomp_comp_hcomp {G G' G'' : A ⥤ B} {H H' H'' : B ⥤ C} (α : G ⟶ G')
    (α' : G' ⟶ G'') (β : H ⟶ H') (β' : H' ⟶ H'') :
    NatTrans.hcomp α β ≫ NatTrans.hcomp α' β' = NatTrans.hcomp (α ≫ α') (β ≫ β') :=
  (NatTrans.exchange _ _ _ _).symm

omit [F.HasProperExchange] in
private lemma hcomp_hcomp_associator {G G' : A ⥤ B} {H H' : B ⥤ C} {K K' : C ⥤ D}
    (α : G ⟶ G') (β : H ⟶ H') (γ : K ⟶ K') :
    NatTrans.hcomp (NatTrans.hcomp α β) γ ≫ (Functor.associator _ _ _).hom =
      (Functor.associator _ _ _).hom ≫ NatTrans.hcomp α (NatTrans.hcomp β γ) := by
  ext; simp

end

/-- The comparison isomorphism from a copy of a compactification to the chosen compactification
of an equal morphism. -/
lemma shriekIso_copy_trans_congr {u u' : X ⟶ Y} [HasCompactification u]
    [HasCompactification u'] [QuasiCompact u] [QuasiCompact u'] (hu : u = u')
    (c : Compactification u') :
    F.shriekIso (c.copy hu) (HasCompactification.compactification u) ≪≫ F.lowerShriekCongr hu =
      F.shriekIso c (HasCompactification.compactification u') := by
  subst hu
  simp only [lowerShriekCongr_refl, Iso.trans_refl]
  rfl

/-- **Associativity of the composition isomorphism**: for composable `f`, `g`, `h`, the two
isomorphisms `Rf_! ⋙ Rg_! ⋙ Rh_! ≅ R(f ≫ g ≫ h)_!` agree.
(blueprint: `proposition-composition-base-change-rf-shriek--1`) -/
theorem lowerShriekCompIso_assoc (f : X ⟶ Y) (g : Y ⟶ S) (h : S ⟶ T) [HasCompactification f]
    [HasCompactification g] [HasCompactification h] [HasCompactification (f ≫ g)]
    [HasCompactification (g ≫ h)] [HasCompactification ((f ≫ g) ≫ h)]
    [HasCompactification (f ≫ g ≫ h)] [QuasiCompact f] [QuasiCompact g] [QuasiCompact h] :
    Functor.whiskerRight (F.lowerShriekCompIso f g).hom (F.lowerShriek h) ≫
        (F.lowerShriekCompIso (f ≫ g) h).hom ≫ (F.lowerShriekCongr (Category.assoc f g h)).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (F.lowerShriek f) (F.lowerShriekCompIso g h).hom ≫
          (F.lowerShriekCompIso f (g ≫ h)).hom := by
  let 𝒯 := Compactification.Tower.ofHasCompactification f g h
  rw [F.lowerShriekCompIso_hom_eq 𝒯.fg, F.lowerShriekCompIso_hom_eq 𝒯.fg_h,
    F.lowerShriekCompIso_hom_eq 𝒯.gh, F.lowerShriekCompIso_hom_eq 𝒯.f_gh]
  have hc := congrArg Iso.hom (F.shriekIso_copy_trans_congr (Category.assoc f g h) 𝒯.cfgh)
  have hT := F.compIso_tower 𝒯
  simp only [Iso.trans_hom] at hc
  rw [← F.shriekIso_symm 𝒯.cfg, ← F.shriekIso_symm 𝒯.cgh]
  simp only [Iso.symm_hom, Functor.whiskerRight_comp, Functor.whiskerLeft_comp, Category.assoc]
  slice_lhs 3 4 => rw [whiskerRight_comp_hcomp, Iso.hom_inv_id, Functor.id_hcomp]
  slice_lhs 2 3 => rw [← hcomp_eq_whiskerRight_comp_whiskerLeft,
    hcomp_eq_whiskerLeft_comp_whiskerRight]
  slice_lhs 1 2 => rw [← hcomp_eq_whiskerRight_comp_whiskerLeft]
  slice_rhs 4 5 => rw [whiskerLeft_comp_hcomp, Iso.hom_inv_id, Functor.hcomp_id]
  slice_rhs 3 4 => rw [← hcomp_eq_whiskerLeft_comp_whiskerRight,
    hcomp_eq_whiskerRight_comp_whiskerLeft]
  slice_rhs 2 3 => rw [← hcomp_eq_whiskerLeft_comp_whiskerRight]
  slice_rhs 1 2 => rw [← hcomp_hcomp_associator]
  simp only [Category.assoc]
  rw [reassoc_of% hT]
  exact congrArg (fun x ↦ _ ≫ _ ≫ _ ≫ _ ≫ x) hc

end AlgebraicGeometry.CompactSupportFormalism

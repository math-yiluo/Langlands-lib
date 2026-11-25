/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Compatibility of induced isomorphisms on derived categories with composition

Consider exact functors `G_i : C_i ⥤ D_i` (`i = 1, 2, 3`) between abelian categories, exact
"pullbacks" `m_g : C₃ ⥤ C₂`, `m_f : C₂ ⥤ C₁`, `m_{fg} : C₃ ⥤ C₁` and `s_g, s_f, s_{fg}`, with
composition isomorphisms `m_{fg} ≅ m_g ⋙ m_f`, `s_{fg} ≅ s_g ⋙ s_f` and comparison isomorphisms
`m_a ⋙ G ≅ G ⋙ s_a` compatible with them. Then the induced isomorphisms on derived categories
are compatible as well (`CategoryTheory.Functor.mapDerivedCategory_compCoherence`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

section CompCoherence

variable {C₃ C₂ C₁ D₃ D₂ D₁ : Type*} [Category* C₃] [Category* C₂] [Category* C₁]
  [Category* D₃] [Category* D₂] [Category* D₁] {G₃ : C₃ ⥤ D₃} {G₂ : C₂ ⥤ D₂} {G₁ : C₁ ⥤ D₁}
  {mg : C₃ ⥤ C₂} {mf : C₂ ⥤ C₁} {mfg : C₃ ⥤ C₁} {sg : D₃ ⥤ D₂} {sf : D₂ ⥤ D₁} {sfg : D₃ ⥤ D₁}

/-- The comparison isomorphisms `i_a : m_a ⋙ G ≅ G ⋙ s_a` are compatible with the composition
isomorphisms `C_m : m_{fg} ≅ m_g ⋙ m_f` and `C_s : s_{fg} ≅ s_g ⋙ s_f`. -/
def CompCoherence (Cm : mfg ≅ mg ⋙ mf) (Cs : sfg ≅ sg ⋙ sf) (ig : mg ⋙ G₂ ≅ G₃ ⋙ sg)
    (iF : mf ⋙ G₁ ≅ G₂ ⋙ sf) (ifg : mfg ⋙ G₁ ≅ G₃ ⋙ sfg) : Prop :=
  ∀ M, ifg.hom.app M ≫ Cs.hom.app (G₃.obj M) =
    G₁.map (Cm.hom.app M) ≫ iF.hom.app (mg.obj M) ≫ sf.map (ig.hom.app M)

variable {A₃ A₂ A₁ : Type*} [Category* A₃] [Category* A₂] [Category* A₁]
  {U₃ : D₃ ⥤ A₃} {U₂ : D₂ ⥤ A₂} {U₁ : D₁ ⥤ A₁} {V₃ : C₃ ⥤ A₃} {V₂ : C₂ ⥤ A₂} {V₁ : C₁ ⥤ A₁}
  {bg : A₃ ⥤ A₂} {bf : A₂ ⥤ A₁} {bfg : A₃ ⥤ A₁}

/-- `CompCoherence` can be checked after a faithful functor `U₁`, through identifications
`c : G ⋙ U ≅ V` under which the comparisons become composites of isomorphisms `φ` and `ψ`
compatible with composition isomorphisms `C_b`. -/
lemma compCoherence_of_faithful [U₁.Faithful]
    (c₃ : G₃ ⋙ U₃ ≅ V₃) (c₂ : G₂ ⋙ U₂ ≅ V₂) (c₁ : G₁ ⋙ U₁ ≅ V₁)
    (φg : V₃ ⋙ bg ≅ mg ⋙ V₂) (φf : V₂ ⋙ bf ≅ mf ⋙ V₁) (φfg : V₃ ⋙ bfg ≅ mfg ⋙ V₁)
    (ψg : U₃ ⋙ bg ≅ sg ⋙ U₂) (ψf : U₂ ⋙ bf ≅ sf ⋙ U₁) (ψfg : U₃ ⋙ bfg ≅ sfg ⋙ U₁)
    (Cm : mfg ≅ mg ⋙ mf) (Cs : sfg ≅ sg ⋙ sf) (Cb : bfg ≅ bg ⋙ bf)
    (hφ : ∀ M, Cb.hom.app (V₃.obj M) ≫ bf.map (φg.hom.app M) ≫ φf.hom.app (mg.obj M) =
      φfg.hom.app M ≫ V₁.map (Cm.hom.app M))
    (hψ : ∀ F, ψfg.hom.app F ≫ U₁.map (Cs.hom.app F) =
      Cb.hom.app (U₃.obj F) ≫ bf.map (ψg.hom.app F) ≫ ψf.hom.app (sg.obj F))
    (ig : mg ⋙ G₂ ≅ G₃ ⋙ sg) (iF : mf ⋙ G₁ ≅ G₂ ⋙ sf) (ifg : mfg ⋙ G₁ ≅ G₃ ⋙ sfg)
    (hig : ∀ M, U₂.map (ig.hom.app M) = c₂.hom.app (mg.obj M) ≫ φg.inv.app M ≫
      bg.map (c₃.inv.app M) ≫ ψg.hom.app (G₃.obj M))
    (hif : ∀ M, U₁.map (iF.hom.app M) = c₁.hom.app (mf.obj M) ≫ φf.inv.app M ≫
      bf.map (c₂.inv.app M) ≫ ψf.hom.app (G₂.obj M))
    (hifg : ∀ M, U₁.map (ifg.hom.app M) = c₁.hom.app (mfg.obj M) ≫ φfg.inv.app M ≫
      bfg.map (c₃.inv.app M) ≫ ψfg.hom.app (G₃.obj M)) :
    CompCoherence Cm Cs ig iF ifg := by
  intro M
  apply U₁.map_injective
  have nψ := ψf.hom.naturality (ig.hom.app M)
  have nc := c₁.hom.naturality (Cm.hom.app M)
  have nC := Cb.hom.naturality (c₃.inv.app M)
  dsimp at nψ nc nC
  have h₂ : φfg.inv.app M ≫ Cb.hom.app (V₃.obj M) =
      V₁.map (Cm.hom.app M) ≫ φf.inv.app (mg.obj M) ≫ bf.map (φg.inv.app M) := by
    rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, ← reassoc_of% (hφ M)]
    simp [← bf.map_comp]
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, hif, hifg]
  simp only [Category.assoc]
  rw [← nψ, hig, hψ, reassoc_of% nc, reassoc_of% nC, reassoc_of% h₂]
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [← bf.map_comp_assoc (c₂.inv.app _),
    Iso.inv_hom_id_app, bf.map_id, Category.id_comp]

end CompCoherence

end CategoryTheory

namespace CategoryTheory.Functor

variable {C₃ C₂ C₁ D₃ D₂ D₁ : Type*} [Category* C₃] [Category* C₂] [Category* C₁]
  [Category* D₃] [Category* D₂] [Category* D₁] [Abelian C₃] [Abelian C₂] [Abelian C₁]
  [Abelian D₃] [Abelian D₂] [Abelian D₁] [HasDerivedCategory C₃] [HasDerivedCategory C₂]
  [HasDerivedCategory C₁] [HasDerivedCategory D₃] [HasDerivedCategory D₂] [HasDerivedCategory D₁]
  {G₃ : C₃ ⥤ D₃} {G₂ : C₂ ⥤ D₂} {G₁ : C₁ ⥤ D₁}
  {mg : C₃ ⥤ C₂} {mf : C₂ ⥤ C₁} {mfg : C₃ ⥤ C₁} {sg : D₃ ⥤ D₂} {sf : D₂ ⥤ D₁} {sfg : D₃ ⥤ D₁}
  [G₃.Additive] [PreservesFiniteLimits G₃] [PreservesFiniteColimits G₃]
  [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [mg.Additive] [PreservesFiniteLimits mg] [PreservesFiniteColimits mg]
  [mf.Additive] [PreservesFiniteLimits mf] [PreservesFiniteColimits mf]
  [mfg.Additive] [PreservesFiniteLimits mfg] [PreservesFiniteColimits mfg]
  [sg.Additive] [PreservesFiniteLimits sg] [PreservesFiniteColimits sg]
  [sf.Additive] [PreservesFiniteLimits sf] [PreservesFiniteColimits sf]
  [sfg.Additive] [PreservesFiniteLimits sfg] [PreservesFiniteColimits sfg]

/-- The isomorphism induced on derived categories by an associator is the identity. -/
lemma mapDerivedCategoryNatIso_associator_hom_app {E₀ E₁ E₂ E₃ : Type*} [Category* E₀]
    [Category* E₁] [Category* E₂] [Category* E₃] [Abelian E₀] [Abelian E₁] [Abelian E₂]
    [Abelian E₃] [HasDerivedCategory E₀] [HasDerivedCategory E₃]
    (F : E₀ ⥤ E₁) (G : E₁ ⥤ E₂) (H : E₂ ⥤ E₃) [(F ⋙ G ⋙ H).Additive]
    [PreservesFiniteLimits (F ⋙ G ⋙ H)] [PreservesFiniteColimits (F ⋙ G ⋙ H)]
    [((F ⋙ G) ⋙ H).Additive]
    [PreservesFiniteLimits ((F ⋙ G) ⋙ H)] [PreservesFiniteColimits ((F ⋙ G) ⋙ H)]
    (M : DerivedCategory E₀) :
    (mapDerivedCategoryNatIso (Functor.associator F G H)).hom.app M = 𝟙 _ := by
  have : Functor.associator F G H = Iso.refl _ := by
    ext
    rfl
  rw [this, mapDerivedCategoryNatIso_refl, NatTrans.id_app]

/-- The isomorphism induced on derived categories by an associator is the identity. -/
lemma mapDerivedCategoryNatIso_associator_inv_app {E₀ E₁ E₂ E₃ : Type*} [Category* E₀]
    [Category* E₁] [Category* E₂] [Category* E₃] [Abelian E₀] [Abelian E₁] [Abelian E₂]
    [Abelian E₃] [HasDerivedCategory E₀] [HasDerivedCategory E₃]
    (F : E₀ ⥤ E₁) (G : E₁ ⥤ E₂) (H : E₂ ⥤ E₃) [(F ⋙ G ⋙ H).Additive]
    [PreservesFiniteLimits (F ⋙ G ⋙ H)] [PreservesFiniteColimits (F ⋙ G ⋙ H)]
    [((F ⋙ G) ⋙ H).Additive]
    [PreservesFiniteLimits ((F ⋙ G) ⋙ H)] [PreservesFiniteColimits ((F ⋙ G) ⋙ H)]
    (M : DerivedCategory E₀) :
    (mapDerivedCategoryNatIso (Functor.associator F G H)).inv.app M = 𝟙 _ := by
  rw [← cancel_epi ((mapDerivedCategoryNatIso (Functor.associator F G H)).hom.app M),
    Iso.hom_inv_id_app, mapDerivedCategoryNatIso_associator_hom_app, Category.comp_id]

/-- **Compatibility of induced isomorphisms on derived categories with composition.** If the
comparison isomorphisms `i_a : m_a ⋙ G ≅ G ⋙ s_a` are compatible with the composition
isomorphisms `C_m : m_{fg} ≅ m_g ⋙ m_f` and `C_s : s_{fg} ≅ s_g ⋙ s_f`, then so are the induced
isomorphisms `D(m_a) ⋙ D(G) ≅ D(G) ⋙ D(s_a)` with the induced composition isomorphisms
`D(m_{fg}) ≅ D(m_g) ⋙ D(m_f)` and `D(s_{fg}) ≅ D(s_g) ⋙ D(s_f)`. -/
lemma mapDerivedCategory_compCoherence (Cm : mfg ≅ mg ⋙ mf) (Cs : sfg ≅ sg ⋙ sf)
    (ig : mg ⋙ G₂ ≅ G₃ ⋙ sg) (iF : mf ⋙ G₁ ≅ G₂ ⋙ sf) (ifg : mfg ⋙ G₁ ≅ G₃ ⋙ sfg)
    (H : CompCoherence Cm Cs ig iF ifg)
    (M : DerivedCategory C₃) :
    (mapDerivedCategoryCompIso mfg G₁).hom.app M ≫ (mapDerivedCategoryNatIso ifg).hom.app M ≫
        (mapDerivedCategoryCompIso G₃ sfg).inv.app M ≫
        (mapDerivedCategoryNatIso Cs).hom.app (G₃.mapDerivedCategory.obj M) ≫
        (mapDerivedCategoryCompIso sg sf).inv.app (G₃.mapDerivedCategory.obj M) =
      G₁.mapDerivedCategory.map ((mapDerivedCategoryNatIso Cm).hom.app M ≫
          (mapDerivedCategoryCompIso mg mf).inv.app M) ≫
        (mapDerivedCategoryCompIso mf G₁).hom.app (mg.mapDerivedCategory.obj M) ≫
        (mapDerivedCategoryNatIso iF).hom.app (mg.mapDerivedCategory.obj M) ≫
        (mapDerivedCategoryCompIso G₂ sf).inv.app (mg.mapDerivedCategory.obj M) ≫
        sf.mapDerivedCategory.map ((mapDerivedCategoryCompIso mg G₂).hom.app M ≫
          (mapDerivedCategoryNatIso ig).hom.app M ≫
          (mapDerivedCategoryCompIso G₃ sg).inv.app M) := by
  have hiso : ifg ≪≫ isoWhiskerLeft G₃ Cs = isoWhiskerRight Cm G₁ ≪≫ Functor.associator _ _ _ ≪≫
      isoWhiskerLeft mg iF ≪≫ (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight ig sf ≪≫
      Functor.associator _ _ _ := by
    ext M
    simpa using H M
  have hD := congrArg (fun e ↦ (mapDerivedCategoryNatIso e).hom.app M) hiso
  simp only [mapDerivedCategoryNatIso_trans, NatTrans.comp_app,
    mapDerivedCategoryNatIso_associator_hom_app, mapDerivedCategoryNatIso_symm,
    Category.id_comp] at hD
  have h₁ := NatTrans.congr_app (mapDerivedCategoryNatIso_isoWhiskerLeft G₃ Cs) M
  have h₂ := NatTrans.congr_app (mapDerivedCategoryNatIso_isoWhiskerRight Cm G₁) M
  have h₃ := NatTrans.congr_app (mapDerivedCategoryNatIso_isoWhiskerLeft mg iF) M
  have h₄ := NatTrans.congr_app (mapDerivedCategoryNatIso_isoWhiskerRight ig sf) M
  have a₁ := NatTrans.congr_app (mapDerivedCategoryCompIso_assoc mg mf G₁) M
  have a₂ := NatTrans.congr_app (mapDerivedCategoryCompIso_assoc mg G₂ sf) M
  have a₃ := NatTrans.congr_app (mapDerivedCategoryCompIso_assoc G₃ sg sf) M
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at h₁ h₂ h₃ h₄ a₁ a₂ a₃
  have h₂' : (mapDerivedCategoryNatIso (isoWhiskerRight Cm G₁)).hom.app M =
      (mapDerivedCategoryCompIso mfg G₁).inv.app M ≫
        G₁.mapDerivedCategory.map ((mapDerivedCategoryNatIso Cm).hom.app M) ≫
        (mapDerivedCategoryCompIso (mg ⋙ mf) G₁).hom.app M := by
    rw [← reassoc_of% h₂, Iso.inv_hom_id_app, Category.comp_id]
  have h₃' : (mapDerivedCategoryNatIso (isoWhiskerLeft mg iF)).hom.app M =
      (mapDerivedCategoryCompIso mg (mf ⋙ G₁)).inv.app M ≫
        (mapDerivedCategoryNatIso iF).hom.app (mg.mapDerivedCategory.obj M) ≫
        (mapDerivedCategoryCompIso mg (G₂ ⋙ sf)).hom.app M := by
    rw [← reassoc_of% h₃, Iso.inv_hom_id_app, Category.comp_id]
  have a₁' : (mapDerivedCategoryCompIso (mg ⋙ mf) G₁).hom.app M ≫
      (mapDerivedCategoryCompIso mg (mf ⋙ G₁)).inv.app M =
      G₁.mapDerivedCategory.map ((mapDerivedCategoryCompIso mg mf).inv.app M) ≫
        (mapDerivedCategoryCompIso mf G₁).hom.app (mg.mapDerivedCategory.obj M) := by
    rw [← cancel_mono ((mapDerivedCategoryCompIso mf G₁).inv.app _), Category.assoc,
      Category.assoc, a₁]
    simp
  have a₂' : (mapDerivedCategoryCompIso mg (G₂ ⋙ sf)).hom.app M ≫
      (mapDerivedCategoryCompIso (mg ⋙ G₂) sf).inv.app M =
      (mapDerivedCategoryCompIso G₂ sf).inv.app (mg.mapDerivedCategory.obj M) ≫
        sf.mapDerivedCategory.map ((mapDerivedCategoryCompIso mg G₂).hom.app M) := by
    rw [← cancel_mono (sf.mapDerivedCategory.map ((mapDerivedCategoryCompIso mg G₂).inv.app M)),
      Category.assoc, Category.assoc, ← a₂]
    simp [← Functor.map_comp]
  rw [← reassoc_of% h₁, a₃, reassoc_of% hD, mapDerivedCategoryNatIso_associator_inv_app,
    Category.id_comp, reassoc_of% h₄, h₂', h₃']
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
  rw [reassoc_of% a₁', reassoc_of% a₂']

/-- `CategoryTheory.Functor.mapDerivedCategory_compCoherence`, stated with the components of the
composite natural transformations. -/
lemma mapDerivedCategory_compCoherence' (Cm : mfg ≅ mg ⋙ mf) (Cs : sfg ≅ sg ⋙ sf)
    (ig : mg ⋙ G₂ ≅ G₃ ⋙ sg) (iF : mf ⋙ G₁ ≅ G₂ ⋙ sf) (ifg : mfg ⋙ G₁ ≅ G₃ ⋙ sfg)
    (H : CompCoherence Cm Cs ig iF ifg) (M : DerivedCategory C₃) :
    ((mapDerivedCategoryCompIso mfg G₁).hom ≫ (mapDerivedCategoryNatIso ifg).hom ≫
        (mapDerivedCategoryCompIso G₃ sfg).inv).app M ≫
        ((mapDerivedCategoryNatIso Cs).hom ≫ (mapDerivedCategoryCompIso sg sf).inv).app
          (G₃.mapDerivedCategory.obj M) =
      G₁.mapDerivedCategory.map
          (((mapDerivedCategoryNatIso Cm).hom ≫ (mapDerivedCategoryCompIso mg mf).inv).app M) ≫
        ((mapDerivedCategoryCompIso mf G₁).hom ≫ (mapDerivedCategoryNatIso iF).hom ≫
          (mapDerivedCategoryCompIso G₂ sf).inv).app (mg.mapDerivedCategory.obj M) ≫
        sf.mapDerivedCategory.map (((mapDerivedCategoryCompIso mg G₂).hom ≫
          (mapDerivedCategoryNatIso ig).hom ≫ (mapDerivedCategoryCompIso G₃ sg).inv).app M) := by
  simpa only [NatTrans.comp_app, Category.assoc] using
    mapDerivedCategory_compCoherence Cm Cs ig iF ifg H M

end CategoryTheory.Functor

namespace CategoryTheory

variable {𝔐₃ 𝔐₂ 𝔐₁ 𝔖₃ 𝔖₂ 𝔖₁ : Type*} [Category* 𝔐₃] [Category* 𝔐₂] [Category* 𝔐₁]
  [Category* 𝔖₃] [Category* 𝔖₂] [Category* 𝔖₁] {G₃ : 𝔐₃ ⥤ 𝔖₃} {G₂ : 𝔐₂ ⥤ 𝔖₂} {G₁ : 𝔐₁ ⥤ 𝔖₁}
  {Lmg Dmg : 𝔐₃ ⥤ 𝔐₂} {Lmf Dmf : 𝔐₂ ⥤ 𝔐₁} {Lmfg Dmfg : 𝔐₃ ⥤ 𝔐₁}
  {Lsg Dsg : 𝔖₃ ⥤ 𝔖₂} {Lsf Dsf : 𝔖₂ ⥤ 𝔖₁} {Lsfg Dsfg : 𝔖₃ ⥤ 𝔖₁}

/-- Transport of the compatibility of comparison isomorphisms with composition isomorphisms
along isomorphisms `L ≅ D` of the functors involved: if the comparisons `D(i_a)` for the
functors `D` are compatible with the composition morphisms `c_m` and `c_s`, then the comparisons
`R_a` for the functors `L` obtained by conjugating with `I : L ≅ D` are compatible with the
composition isomorphisms obtained by conjugating `c_m` and `c_s`. -/
lemma compCoherence_of_isoConj (Img : Lmg ≅ Dmg) (Imf : Lmf ≅ Dmf) (Imfg : Lmfg ≅ Dmfg)
    (Isg : Lsg ≅ Dsg) (Isf : Lsf ≅ Dsf) (Isfg : Lsfg ≅ Dsfg)
    (Dig : Dmg ⋙ G₂ ⟶ G₃ ⋙ Dsg) (DiF : Dmf ⋙ G₁ ⟶ G₂ ⋙ Dsf) (Difg : Dmfg ⋙ G₁ ⟶ G₃ ⋙ Dsfg)
    (cm : Dmfg ⟶ Dmg ⋙ Dmf) (cs : Dsfg ⟶ Dsg ⋙ Dsf)
    (hA : ∀ M, Difg.app M ≫ cs.app (G₃.obj M) =
      G₁.map (cm.app M) ≫ DiF.app (Dmg.obj M) ≫ Dsf.map (Dig.app M))
    (Rg : Lmg ⋙ G₂ ≅ G₃ ⋙ Lsg) (RF : Lmf ⋙ G₁ ≅ G₂ ⋙ Lsf) (Rfg : Lmfg ⋙ G₁ ≅ G₃ ⋙ Lsfg)
    (hRg : ∀ M, Rg.hom.app M = G₂.map (Img.hom.app M) ≫ Dig.app M ≫ Isg.inv.app (G₃.obj M))
    (hRf : ∀ M, RF.hom.app M = G₁.map (Imf.hom.app M) ≫ DiF.app M ≫ Isf.inv.app (G₂.obj M))
    (hRfg : ∀ M, Rfg.hom.app M = G₁.map (Imfg.hom.app M) ≫ Difg.app M ≫
      Isfg.inv.app (G₃.obj M))
    (LCm : Lmfg ≅ Lmg ⋙ Lmf) (LCs : Lsfg ≅ Lsg ⋙ Lsf)
    (hLCm : ∀ M, LCm.hom.app M = Imfg.hom.app M ≫ cm.app M ≫ Dmf.map (Img.inv.app M) ≫
      Imf.inv.app (Lmg.obj M))
    (hLCs : ∀ M, LCs.hom.app M = Isfg.hom.app M ≫ cs.app M ≫ Dsf.map (Isg.inv.app M) ≫
      Isf.inv.app (Lsg.obj M))
    (M : 𝔐₃) :
    Rfg.hom.app M ≫ LCs.hom.app (G₃.obj M) =
      G₁.map (LCm.hom.app M) ≫ RF.hom.app (Lmg.obj M) ≫ Lsf.map (Rg.hom.app M) := by
  have nI := Isf.inv.naturality (Rg.hom.app M)
  have nD := DiF.naturality (Img.hom.app M)
  dsimp at nI nD
  rw [hRfg, hLCs, hLCm, hRf, Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc,
    reassoc_of% (hA M)]
  simp only [Category.assoc]
  rw [← nI, hRg]
  simp only [Functor.map_comp, Category.assoc]
  rw [← G₁.map_comp_assoc (Imf.inv.app _), Iso.inv_hom_id_app, G₁.map_id, Category.id_comp,
    ← reassoc_of% nD, ← G₁.map_comp_assoc (Dmf.map _), ← Dmf.map_comp, Iso.inv_hom_id_app,
    Dmf.map_id,
    G₁.map_id, Category.id_comp]

end CategoryTheory

namespace CategoryTheory

/-- The components of a conjugate `I ⋙ G ≅ A⁻¹ ≫ B ≫ C ≅ G ⋙ J⁻¹` of a composite of
isomorphisms. -/
lemma isoWhiskerRight_trans_isoWhiskerLeft_hom_app {𝔐 𝔐' 𝔖 𝔖' : Type*} [Category* 𝔐]
    [Category* 𝔐'] [Category* 𝔖] [Category* 𝔖'] {L D : 𝔐 ⥤ 𝔐'} {L' D' : 𝔖 ⥤ 𝔖'}
    {G : 𝔐' ⥤ 𝔖'} {G' : 𝔐 ⥤ 𝔖} {P Q : 𝔐 ⥤ 𝔖'} (I : L ≅ D) (A : P ≅ D ⋙ G) (B : P ≅ Q)
    (C : Q ≅ G' ⋙ D') (J : L' ≅ D') (M : 𝔐) :
    (Functor.isoWhiskerRight I G ≪≫ A.symm ≪≫ B ≪≫ C ≪≫
        Functor.isoWhiskerLeft G' J.symm).hom.app M =
      G.map (I.hom.app M) ≫ (A.inv ≫ B.hom ≫ C.hom).app M ≫ J.inv.app (G'.obj M) := by
  simp


/-- The components of the composite of a conjugate `I₁ ≫ e ≫ I₂⁻¹` with a conjugate
`I₂ ≫ c ≫ (I_g⁻¹ ◫ I_f⁻¹)` of a composition isomorphism. -/
lemma trans_trans_isoWhiskerLeft_hom_app {𝔐₃ 𝔐₂ 𝔐₁ : Type*} [Category* 𝔐₃] [Category* 𝔐₂]
    [Category* 𝔐₁] {Lfg Dfg Lgf Dgf : 𝔐₃ ⥤ 𝔐₁} {Lg Dg : 𝔐₃ ⥤ 𝔐₂} {Lf Df : 𝔐₂ ⥤ 𝔐₁}
    (I₁ : Lfg ≅ Dfg) (e : Dfg ≅ Dgf) (I₂ : Lgf ≅ Dgf) (c : Dgf ≅ Dg ⋙ Df) (Ig : Lg ≅ Dg)
    (If : Lf ≅ Df) (M : 𝔐₃) :
    ((I₁ ≪≫ e ≪≫ I₂.symm) ≪≫ I₂ ≪≫ c ≪≫ Functor.isoWhiskerRight Ig.symm Df ≪≫
        Functor.isoWhiskerLeft Lg If.symm).hom.app M =
      I₁.hom.app M ≫ (e.hom ≫ c.hom).app M ≫ Df.map (Ig.inv.app M) ≫ If.inv.app (Lg.obj M) := by
  simp

end CategoryTheory

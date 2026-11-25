/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-!
# Restriction of global sections along a pullback
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section LowerStar

variable {R S T : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
lemma globalSectionsLowerStarIso_hom_app' (g : S ⟶ R) (G : Sheaf (ProEt.topology S) A) :
    (globalSectionsLowerStarIso A g).hom.app G =
      (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId R)).hom.app ((g)_*[A].obj G) ≫
        G.obj.map (Iso.inv (C := S.ProEt) (overPullbackObjMkIdIso g)).op ≫
        (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId S)).inv.app G := by
  simp [globalSectionsLowerStarIso]

set_option backward.isDefEq.respectTransparency.types false in
/-- The invariance of global sections under pushforward is compatible with composition. -/
lemma globalSectionsLowerStarIso_comp (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (G : Sheaf (ProEt.topology T) A) :
    (Sheaf.Γ _ A).map ((lowerStarComp A h₁ h₂).hom.app G) ≫
        (globalSectionsLowerStarIso A (h₁ ≫ h₂)).hom.app G =
      (globalSectionsLowerStarIso A h₂).hom.app ((h₁)_*[A].obj G) ≫
        (globalSectionsLowerStarIso A h₁).hom.app G := by
  rw [globalSectionsLowerStarIso_hom_app', globalSectionsLowerStarIso_hom_app',
    globalSectionsLowerStarIso_hom_app']
  have := (Sheaf.ΓNatIsoSheafSections (ProEt.topology R) A (ProEt.isTerminalMkId R)).hom.naturality
    ((lowerStarComp A h₁ h₂).hom.app G)
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% this]
  congr 1
  simp only [← Category.assoc]
  congr 1
  change ((lowerStarComp A h₁ h₂).hom.app G).hom.app _ ≫ _ = G.obj.map _ ≫ _
  rw [lowerStarComp_hom_app_hom_app]
  refine (G.obj.map_comp _ _).symm.trans ((congrArg G.obj.map ?_).trans (G.obj.map_comp _ _))
  apply Quiver.Hom.unop_inj
  exact (IsTerminal.ofIso (ProEt.isTerminalMkId T)
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ h₁).mapIso (overPullbackObjMkIdIso h₂) ≪≫
      overPullbackObjMkIdIso h₁).symm).hom_ext _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- The invariance of global sections under pushforward along the identity is the identification
`(𝟙 R)_* ≅ 𝟭`. -/
lemma globalSectionsLowerStarIso_id (G : Sheaf (ProEt.topology R) A) :
    (globalSectionsLowerStarIso A (𝟙 R)).hom.app G =
      (Sheaf.Γ _ A).map ((lowerStarId A R).hom.app G) := by
  rw [globalSectionsLowerStarIso_hom_app']
  have := (Sheaf.ΓNatIsoSheafSections (ProEt.topology R) A (ProEt.isTerminalMkId R)).hom.naturality
    ((lowerStarId A R).hom.app G)
  rw [← cancel_mono ((Sheaf.ΓNatIsoSheafSections (ProEt.topology R) A
    (ProEt.isTerminalMkId R)).hom.app G)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  refine Eq.trans ?_ this.symm
  congr 1
  change _ = ((lowerStarId A R).hom.app G).hom.app _
  rw [lowerStarId_hom_app_hom_app]
  refine (Category.comp_id _).trans (congrArg G.obj.map ?_)
  apply Quiver.Hom.unop_inj
  exact (IsTerminal.ofIso (ProEt.isTerminalMkId R) (overPullbackObjMkIdIso (𝟙 R)).symm).hom_ext _ _

/-- The invariance of global sections under pushforward along equal morphisms. -/
lemma globalSectionsLowerStarIso_congr {g g' : S ⟶ R} (h : g = g')
    (G : Sheaf (ProEt.topology S) A) :
    (Sheaf.Γ _ A).map ((lowerStarCongr A h).hom.app G) ≫
        (globalSectionsLowerStarIso A g').hom.app G =
      (globalSectionsLowerStarIso A g).hom.app G := by
  subst h
  simp

end LowerStar

section Restriction

variable {Z W : Scheme.{u}}

/-- The restriction `Γ(W, F) ⟶ Γ(Z, g^* F)` of global sections along `g : Z ⟶ W`: global
sections of the unit `F ⟶ g_* g^* F`, followed by `Γ(W, g_* G) ≅ Γ(Z, G)`. -/
noncomputable def globalSectionsToUpperStar (g : Z ⟶ W) :
    Sheaf.Γ (ProEt.topology W) A ⟶ (g)^*[A] ⋙ Sheaf.Γ (ProEt.topology Z) A :=
  Functor.whiskerRight (upperStarLowerStarAdjunction A g).unit _ ≫
    Functor.whiskerLeft (g)^*[A] (globalSectionsLowerStarIso A g).hom

lemma globalSectionsToUpperStar_app (g : Z ⟶ W) (F : Sheaf (ProEt.topology W) A) :
    (globalSectionsToUpperStar A g).app F =
      (Sheaf.Γ _ A).map ((upperStarLowerStarAdjunction A g).unit.app F) ≫
        (globalSectionsLowerStarIso A g).hom.app ((g)^*[A].obj F) :=
  rfl

/-- The restriction of global sections along a composite is the composite of the
restrictions. -/
lemma globalSectionsToUpperStar_comp {T : Scheme.{u}} (h₁ : T ⟶ Z) (h₂ : Z ⟶ W)
    (F : Sheaf (ProEt.topology W) A) :
    (globalSectionsToUpperStar A (h₁ ≫ h₂)).app F ≫
        (Sheaf.Γ _ A).map ((upperStarComp A h₁ h₂).hom.app F) =
      (globalSectionsToUpperStar A h₂).app F ≫
        (globalSectionsToUpperStar A h₁).app ((h₂)^*[A].obj F) := by
  have h := unit_conjugateEquiv ((upperStarLowerStarAdjunction A h₂).comp
    (upperStarLowerStarAdjunction A h₁)) (upperStarLowerStarAdjunction A (h₁ ≫ h₂))
    (upperStarComp A h₁ h₂).hom F
  rw [conjugateEquiv_upperStarComp_hom, Adjunction.comp_unit_app] at h
  simp only [globalSectionsToUpperStar_app, Category.assoc]
  rw [← (globalSectionsLowerStarIso A (h₁ ≫ h₂)).hom.naturality, Functor.comp_map,
    ← Functor.map_comp_assoc, ← h]
  simp only [Functor.map_comp, Category.assoc, globalSectionsLowerStarIso_comp]
  rw [← (globalSectionsLowerStarIso A h₂).hom.naturality_assoc]
  rfl

/-- The restriction of global sections along an isomorphism `e` is inverse to the invariance
`Γ(Z, e^* F) ≅ Γ(W, F)`. -/
lemma globalSectionsToUpperStar_app_comp_globalSectionsUpperStarIso (e : Z ≅ W)
    (F : Sheaf (ProEt.topology W) A) :
    (globalSectionsToUpperStar A e.hom).app F ≫ (globalSectionsUpperStarIso A e).hom.app F =
      𝟙 _ := by
  have h₁ := Adjunction.unit_leftAdjointUniq_hom_app (upperStarLowerStarAdjunction A e.hom)
    (lowerStarEquivalence A e).symm.toAdjunction F
  have h₂ : (lowerStarEquivalence A e).symm.toAdjunction.unit.app F =
      (lowerStarComp A e.inv e.hom ≪≫ lowerStarCongr A e.inv_hom_id ≪≫
        lowerStarId A W).inv.app F :=
    rfl
  have h₃ := globalSectionsLowerStarIso_comp A e.inv e.hom F
  rw [← globalSectionsLowerStarIso_congr A e.inv_hom_id, globalSectionsLowerStarIso_id] at h₃
  simp only [globalSectionsToUpperStar_app, globalSectionsUpperStarIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc]
  rw [← (globalSectionsLowerStarIso A e.hom).hom.naturality_assoc, Functor.comp_map,
    ← Functor.map_comp_assoc, upperStarIsoLowerStarInv, ← h₃]
  refine (congrArg (fun x ↦ (Sheaf.Γ (ProEt.topology W) A).map x ≫ _) (h₁.trans h₂)).trans ?_
  simp only [← Functor.map_comp]
  have key : (lowerStarComp A e.inv e.hom ≪≫ lowerStarCongr A e.inv_hom_id ≪≫
      lowerStarId A W).inv.app F ≫ ((lowerStarComp A e.inv e.hom).hom.app F ≫
        (lowerStarCongr A e.inv_hom_id).hom.app F ≫ (lowerStarId A W).hom.app F) = 𝟙 F := by
    have := (lowerStarComp A e.inv e.hom ≪≫ lowerStarCongr A e.inv_hom_id ≪≫
      lowerStarId A W).inv_hom_id_app F
    simp only [Iso.trans_hom, NatTrans.comp_app] at this
    exact this
  exact (congrArg (Sheaf.Γ (ProEt.topology W) A).map key).trans
    ((Sheaf.Γ (ProEt.topology W) A).map_id _)

end Restriction

section Transport

variable {P P' P'' Y Y' Y'' : Scheme.{u}}

/-- The transport `Γ(P, t^* F) ⟶ Γ(P', t'^* F')` along a commutative square `τ ≫ t = t' ≫ g`
and a morphism `ψ : g^* F ⟶ F'`: the restriction along `τ`, followed by
`τ^* t^* F ≅ (τ ≫ t)^* F = (t' ≫ g)^* F ≅ t'^* g^* F` and by `t'^* ψ`. For a Weil sheaf, a
geometric point `s` and the Weil structure `ψ`, this is the Frobenius of the stalk at `s`. -/
noncomputable def globalSectionsTransport {τ : P' ⟶ P} {t : P ⟶ Y} {t' : P' ⟶ Y'} {g : Y' ⟶ Y}
    (h : τ ≫ t = t' ≫ g) {F : Sheaf (ProEt.topology Y) A} {F' : Sheaf (ProEt.topology Y') A}
    (ψ : (g)^*[A].obj F ⟶ F') :
    (Sheaf.Γ _ A).obj ((t)^*[A].obj F) ⟶ (Sheaf.Γ _ A).obj ((t')^*[A].obj F') :=
  (globalSectionsToUpperStar A τ).app _ ≫
    (Sheaf.Γ _ A).map ((upperStarCompIso A h).hom.app F ≫ (t')^*[A].map ψ)

/-- The transports compose: transporting along `τ ≫ t = t' ≫ g` with `ψ` and then along
`τ' ≫ t' = t'' ≫ g'` with `ψ'` is transporting along the composite square with
`(g' ≫ g)^* F ≅ g'^* g^* F ⟶ g'^* F' ⟶ F''`. -/
lemma globalSectionsTransport_comp {τ : P' ⟶ P} {τ' : P'' ⟶ P'} {t : P ⟶ Y} {t' : P' ⟶ Y'}
    {t'' : P'' ⟶ Y''} {g : Y' ⟶ Y} {g' : Y'' ⟶ Y'}
    (h : τ ≫ t = t' ≫ g) (h' : τ' ≫ t' = t'' ≫ g') (h'' : (τ' ≫ τ) ≫ t = t'' ≫ (g' ≫ g))
    {F : Sheaf (ProEt.topology Y) A} {F' : Sheaf (ProEt.topology Y') A}
    {F'' : Sheaf (ProEt.topology Y'') A} (ψ : (g)^*[A].obj F ⟶ F')
    (ψ' : (g')^*[A].obj F' ⟶ F'') :
    globalSectionsTransport A h ψ ≫ globalSectionsTransport A h' ψ' =
      globalSectionsTransport A h''
        ((upperStarComp A g' g).hom.app F ≫ (g')^*[A].map ψ ≫ ψ') := by
  have hn {G G' : Sheaf (ProEt.topology P') A} (f : G ⟶ G') :
      (Sheaf.Γ _ A).map f ≫ (globalSectionsToUpperStar A τ').app G' =
        (globalSectionsToUpperStar A τ').app G ≫ (Sheaf.Γ _ A).map ((τ')^*[A].map f) :=
    (globalSectionsToUpperStar A τ').naturality f
  simp only [globalSectionsTransport, Category.assoc]
  rw [reassoc_of% hn, ← reassoc_of% globalSectionsToUpperStar_comp]
  simp only [← Functor.map_comp]
  congr 2
  have e := upperStarCompIso_hom_app_paste A h h' h'' F
  simp only [Functor.map_comp, Category.assoc]
  have hψ : (τ')^*[A].map ((t')^*[A].map ψ) ≫ (upperStarCompIso A h').hom.app F' =
      (upperStarCompIso A h').hom.app _ ≫ (t'')^*[A].map ((g')^*[A].map ψ) :=
    (upperStarCompIso A h').hom.naturality ψ
  rw [reassoc_of% hψ, reassoc_of% e]

/-- Transports along equal morphisms `g = g'` with corresponding morphisms `ψ` and `ψ'` agree. -/
lemma globalSectionsTransport_congr {τ : P' ⟶ P} {t : P ⟶ Y} {t' : P' ⟶ Y'} {g g' : Y' ⟶ Y}
    (h : τ ≫ t = t' ≫ g) (hg : g = g') {F : Sheaf (ProEt.topology Y) A}
    {F' : Sheaf (ProEt.topology Y') A} (ψ : (g)^*[A].obj F ⟶ F') (ψ' : (g')^*[A].obj F ⟶ F')
    (hψ : ψ = (upperStarCongr A hg).hom.app F ≫ ψ') :
    globalSectionsTransport A h ψ = globalSectionsTransport A (h.trans (by rw [hg])) ψ' := by
  subst hg hψ
  simp [upperStarCongr]

/-- Transports along equal morphisms `τ = τ'` agree. -/
lemma globalSectionsTransport_congr_left {τ τ' : P' ⟶ P} {t : P ⟶ Y} {t' : P' ⟶ Y'}
    {g : Y' ⟶ Y} (h : τ ≫ t = t' ≫ g) (hτ : τ = τ') {F : Sheaf (ProEt.topology Y) A}
    {F' : Sheaf (ProEt.topology Y') A} (ψ : (g)^*[A].obj F ⟶ F') :
    globalSectionsTransport A h ψ = globalSectionsTransport A (hτ ▸ h) ψ := by
  subst hτ
  rfl

end Transport

end AlgebraicGeometry.ProEtale

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.SheafHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy

/-!
# Gluing morphisms of pro-étale sheaves along a pro-étale cover

Let `e : W ⟶ X` be a single-morphism pro-étale cover (weakly étale, surjective and
quasi-compact) and `F`, `G` sheaves on `X_proét`. A morphism `φ : e^* F ⟶ e^* G` whose pullbacks
along any two `a b : W' ⟶ W` with `a ≫ e = b ≫ e` agree is the pullback of a morphism `F ⟶ G`
(`AlgebraicGeometry.ProEtale.exists_hom_of_upperStar`): the presheaf of morphisms `F ⟶ G` is a
sheaf (`CategoryTheory.Presheaf.IsSheaf.hom`), and along the weakly étale `e` the pullback is
the restriction along the localization functor
(`AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction`), compatibly with composition
(`AlgebraicGeometry.ProEtale.upperStarComp'_hom_comp_upperStarIsoLocalizationRestriction`).

This is the pro-étale counterpart of `WeilConjectures.SixFunctors.Etale.Derived.HeartGluing`,
whose arguments are followed closely.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

open ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {R S T : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R) (h₁ : WeaklyEtale g₁)
  (h₂ : WeaklyEtale g₂)

/-- Composition of the restrictions along weakly étale maps, for a morphism `g₁₂` equal to
the composite. -/
noncomputable def ProEtale.localizationRestrictionComp (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂)
    (h₁₂ : WeaklyEtale g₁₂) :
    ProEtale.localizationRestriction A g₁₂ h₁₂ ≅
      ProEtale.localizationRestriction A g₂ h₂ ⋙ ProEtale.localizationRestriction A g₁ h₁ :=
  (Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.mapComp ⊤ h₁ h₂ g₁₂ hg).symm)
    A (Scheme.ProEt.topology T) (Scheme.ProEt.topology S)
    (Scheme.ProEt.topology R)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option linter.flexible false in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The composition isomorphism of restrictions is conjugate to that of pushforwards. -/
lemma ProEtale.conjugateEquiv_localizationRestrictionComp_inv (h₁₂ : WeaklyEtale (g₁ ≫ g₂)) :
    conjugateEquiv (ProEtale.localizationRestrictionLowerStarAdjunction A (g₁ ≫ g₂) h₁₂)
        ((ProEtale.localizationRestrictionLowerStarAdjunction A g₂ h₂).comp
          (ProEtale.localizationRestrictionLowerStarAdjunction A g₁ h₁))
        (ProEtale.localizationRestrictionComp A g₁ g₂ h₁ h₂ (g₁ ≫ g₂) rfl h₁₂).inv =
      (ProEtale.lowerStarComp A g₁ g₂).inv := by
  ext G : 2
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun U ↦ ?_)
  simp [conjugateEquiv_apply_app, ProEtale.localizationRestrictionLowerStarAdjunction,
    ProEtale.localizationRestrictionComp, ProEtale.lowerStarComp,
    MorphismProperty.Over.mapPullbackAdj,
    Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp,
    Functor.sheafPushforwardContinuousIso, ProEtale.localizationRestriction,
    ProEtale.lowerStar, ← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  ext
  simp only [MorphismProperty.Over.mapComp, MorphismProperty.Over.pullbackComp]
  apply pullback.hom_ext <;> simp

/-- The identification of the pullback with the restriction is conjugate to the identity. -/
lemma ProEtale.conjugateEquiv_upperStarIsoLocalizationRestriction_hom {X Y : Scheme.{u}}
    (g : X ⟶ Y) (h : WeaklyEtale g) :
    conjugateEquiv (ProEtale.localizationRestrictionLowerStarAdjunction A g h)
        (ProEtale.upperStarLowerStarAdjunction A g)
        (ProEtale.upperStarIsoLocalizationRestriction A g h).hom = 𝟙 _ := by
  simp [ProEtale.upperStarIsoLocalizationRestriction, Adjunction.leftAdjointUniq,
    conjugateIsoEquiv]

/-- Composition of weakly étale pullbacks is composition of restrictions, for the composite
itself. -/
lemma ProEtale.upperStarComp_hom_comp_upperStarIsoLocalizationRestriction_aux
    (h₁₂ : WeaklyEtale (g₁ ≫ g₂)) :
    (ProEtale.upperStarComp A g₁ g₂).hom ≫
        Functor.whiskerRight (ProEtale.upperStarIsoLocalizationRestriction A g₂ h₂).hom
          (ProEtale.upperStar A g₁) ≫
        Functor.whiskerLeft (ProEtale.localizationRestriction A g₂ h₂)
          (ProEtale.upperStarIsoLocalizationRestriction A g₁ h₁).hom =
      (ProEtale.upperStarIsoLocalizationRestriction A (g₁ ≫ g₂) h₁₂).hom ≫
        (ProEtale.localizationRestrictionComp A g₁ g₂ h₁ h₂ (g₁ ≫ g₂) rfl h₁₂).hom := by
  let C := (ProEtale.localizationRestrictionLowerStarAdjunction A g₂ h₂).comp
    (ProEtale.localizationRestrictionLowerStarAdjunction A g₁ h₁)
  let LU := (ProEtale.localizationRestrictionLowerStarAdjunction A g₂ h₂).comp
    (ProEtale.upperStarLowerStarAdjunction A g₁)
  let UU := (ProEtale.upperStarLowerStarAdjunction A g₂).comp
    (ProEtale.upperStarLowerStarAdjunction A g₁)
  let U₁₂ := ProEtale.upperStarLowerStarAdjunction A (g₁ ≫ g₂)
  let L₁₂ := ProEtale.localizationRestrictionLowerStarAdjunction A (g₁ ≫ g₂) h₁₂
  apply (conjugateEquiv C U₁₂).injective
  rw [← conjugateEquiv_comp C UU U₁₂, ← conjugateEquiv_comp C LU UU,
    ← conjugateEquiv_comp C L₁₂ U₁₂]
  dsimp only [C, LU, UU]
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    ProEtale.conjugateEquiv_upperStarIsoLocalizationRestriction_hom,
    ProEtale.conjugateEquiv_upperStarIsoLocalizationRestriction_hom,
    ProEtale.conjugateEquiv_upperStarIsoLocalizationRestriction_hom]
  have h := ProEtale.conjugateEquiv_localizationRestrictionComp_inv A g₁ g₂ h₁ h₂ h₁₂
  simp only [Functor.whiskerRight_id', Functor.whiskerLeft_id', Category.id_comp,
    Category.comp_id]
  have e₁ : conjugateIsoEquiv L₁₂ _
      (ProEtale.localizationRestrictionComp A g₁ g₂ h₁ h₂ (g₁ ≫ g₂) rfl h₁₂).symm =
      (ProEtale.lowerStarComp A g₁ g₂).symm := Iso.ext (by simpa using h)
  have e₂ := (conjugateIsoEquiv U₁₂ UU).apply_symm_apply (ProEtale.lowerStarComp A g₁ g₂).symm
  have h₁ := congrArg Iso.inv e₁
  have h₂ := congrArg Iso.inv e₂
  simp only [conjugateIsoEquiv_apply_inv, Iso.symm_inv] at h₁ h₂
  rw [h₁]
  convert h₂ using 2
  simp [ProEtale.upperStarComp]
  rfl

/-- The composition isomorphism `g₁₂^* ≅ g₂^* ⋙ g₁^*` for a morphism `g₁₂` equal to the
composite. -/
noncomputable def ProEtale.upperStarComp' (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂) :
    ProEtale.upperStar A g₁₂ ≅ ProEtale.upperStar A g₂ ⋙ ProEtale.upperStar A g₁ :=
  ProEtale.upperStarCongr A hg ≪≫ ProEtale.upperStarComp A g₁ g₂

/-- **Composition of weakly étale pullbacks is composition of restrictions.** -/
lemma ProEtale.upperStarComp'_hom_comp_upperStarIsoLocalizationRestriction (g₁₂ : T ⟶ R)
    (hg : g₁₂ = g₁ ≫ g₂) (h₁₂ : WeaklyEtale g₁₂) :
    (ProEtale.upperStarComp' A g₁ g₂ g₁₂ hg).hom ≫
        Functor.whiskerRight (ProEtale.upperStarIsoLocalizationRestriction A g₂ h₂).hom
          (ProEtale.upperStar A g₁) ≫
        Functor.whiskerLeft (ProEtale.localizationRestriction A g₂ h₂)
          (ProEtale.upperStarIsoLocalizationRestriction A g₁ h₁).hom =
      (ProEtale.upperStarIsoLocalizationRestriction A g₁₂ h₁₂).hom ≫
        (ProEtale.localizationRestrictionComp A g₁ g₂ h₁ h₂ g₁₂ hg h₁₂).hom := by
  subst hg
  simp only [ProEtale.upperStarComp', ProEtale.upperStarCongr, eqToIso_refl, Iso.refl_trans]
  exact ProEtale.upperStarComp_hom_comp_upperStarIsoLocalizationRestriction_aux A g₁ g₂ h₁ h₂ h₁₂

/-- Conjugating a composite pullback by the restriction identifications. -/
lemma ProEtale.upperStarComp'_conj (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂) (h₁₂ : WeaklyEtale g₁₂)
    {F G : Sheaf (Scheme.ProEt.topology R) A} (φ : (g₂)^*[A].obj F ⟶ (g₂)^*[A].obj G) :
    (ProEtale.upperStarIsoLocalizationRestriction A g₁₂ h₁₂).inv.app F ≫
        (ProEtale.upperStarComp' A g₁ g₂ g₁₂ hg).hom.app F ≫ (g₁)^*[A].map φ ≫
          (ProEtale.upperStarComp' A g₁ g₂ g₁₂ hg).inv.app G ≫
            (ProEtale.upperStarIsoLocalizationRestriction A g₁₂ h₁₂).hom.app G =
      (ProEtale.localizationRestrictionComp A g₁ g₂ h₁ h₂ g₁₂ hg h₁₂).hom.app F ≫
        (ProEtale.localizationRestriction A g₁ h₁).map
          ((ProEtale.upperStarIsoLocalizationRestriction A g₂ h₂).inv.app F ≫ φ ≫
            (ProEtale.upperStarIsoLocalizationRestriction A g₂ h₂).hom.app G) ≫
        (ProEtale.localizationRestrictionComp A g₁ g₂ h₁ h₂ g₁₂ hg h₁₂).inv.app G := by
  have hF := NatTrans.congr_app
    (ProEtale.upperStarComp'_hom_comp_upperStarIsoLocalizationRestriction A g₁ g₂ h₁ h₂ g₁₂ hg
      h₁₂) F
  have hG := NatTrans.congr_app
    (ProEtale.upperStarComp'_hom_comp_upperStarIsoLocalizationRestriction A g₁ g₂ h₁ h₂ g₁₂ hg
      h₁₂) G
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hF hG
  rw [← cancel_epi ((ProEtale.upperStarIsoLocalizationRestriction A g₁₂ h₁₂).hom.app F),
    Iso.hom_inv_id_app_assoc, ← reassoc_of% hF]
  rw [← cancel_mono ((ProEtale.localizationRestrictionComp A g₁ g₂ h₁ h₂ g₁₂ hg h₁₂).hom.app G)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← hG]
  simp only [Functor.map_comp, Category.assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  have n₁ := (ProEtale.upperStarIsoLocalizationRestriction A g₁ h₁).hom.naturality
    ((ProEtale.upperStarIsoLocalizationRestriction A g₂ h₂).inv.app F ≫ φ ≫
      (ProEtale.upperStarIsoLocalizationRestriction A g₂ h₂).hom.app G)
  erw [Category.comp_id]
  rw [← Functor.map_comp, ← Functor.map_comp]
  erw [← n₁]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]


variable {A} {X W : Scheme.{u}} (e : W ⟶ X) (he : WeaklyEtale e)

/-- The identification of `T ⟶ W ⟶ X` with a weakly étale `X`-scheme `T`. -/
noncomputable def ProEtale.overMapIso (T : X.ProEt) (t : T.left ⟶ W) (h : t ≫ e = T.hom) :
    (MorphismProperty.Over.map ⊤ he).obj (MorphismProperty.Over.mk ⊤ t
      (MorphismProperty.of_postcomp _ _ _ he (h ▸ T.prop))) ≅ T :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by simp [h])

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- **Gluing morphisms of pro-étale sheaves along a single pro-étale cover**, in terms of the
restrictions along the localization functor. -/
theorem ProEtale.exists_hom_of_localizationRestriction [Surjective e] [QuasiCompact e]
    (F G : Sheaf (Scheme.ProEt.topology X) A)
    (ψ : (ProEtale.localizationRestriction A e he).obj F ⟶
      (ProEtale.localizationRestriction A e he).obj G)
    (hψ : ∀ (T : X.ProEt) (tj tk : T.left ⟶ W) (hj : tj ≫ e = T.hom) (hk : tk ≫ e = T.hom),
      F.obj.map (ProEtale.overMapIso e he T tj hj).hom.op ≫ ψ.hom.app (op _) ≫
          G.obj.map (ProEtale.overMapIso e he T tj hj).inv.op =
        F.obj.map (ProEtale.overMapIso e he T tk hk).hom.op ≫ ψ.hom.app (op _) ≫
          G.obj.map (ProEtale.overMapIso e he T tk hk).inv.op) :
    ∃ φ : F ⟶ G, (ProEtale.localizationRestriction A e he).map φ = ψ := by
  let P := presheafHom F.obj G.obj
  let V' : Unit → X.ProEt := fun _ ↦ MorphismProperty.Over.mk ⊤ e he
  let top : X.ProEt := MorphismProperty.Over.mk ⊤ (𝟙 X) inferInstance
  let π : ∀ j, V' j ⟶ top := fun _ ↦ MorphismProperty.Over.homMk e (Category.comp_id _) trivial
  have hw : ∀ j (T : Over (V' j)), T.hom.left ≫ e = T.left.hom := fun j T ↦ by
    simpa [V'] using MorphismProperty.Over.w T.hom
  let Φ : ∀ j, Over (V' j) ⥤ W.ProEt := fun j ↦
    { obj T := MorphismProperty.Over.mk ⊤ T.hom.left
        (MorphismProperty.of_postcomp _ _ _ he (by
          rw [hw j T]; exact T.left.prop))
      map g := MorphismProperty.Over.homMk g.left.left
        (congrArg (fun f ↦ f.left) (Over.w g)) trivial }
  let κ : ∀ j, Φ j ⋙ MorphismProperty.Over.map ⊤ he ≅ Over.forget (V' j) := fun j ↦
    NatIso.ofComponents (fun T ↦ ProEtale.overMapIso e he T.left T.hom.left
      (hw j T)) (fun g ↦ by ext; simp [ProEtale.overMapIso, Φ])
  let x : ∀ j, P.obj (op (V' j)) := fun j ↦
    (Functor.isoWhiskerRight (NatIso.op (κ j)) F.obj).hom ≫
      Functor.whiskerLeft (Φ j).op ψ.hom ≫
        (Functor.isoWhiskerRight (NatIso.op (κ j)) G.obj).inv
  have hx : Presieve.Arrows.Compatible P π x := by
    intro i k Z gi gk h
    refine NatTrans.ext (funext fun T ↦ ?_)
    exact hψ T.unop.left _ _ (hw i ((Over.map gi).obj T.unop)) (hw k ((Over.map gk).obj T.unop))
  have hP : Presheaf.IsSheaf (Scheme.ProEt.topology X) P :=
    Presheaf.IsSheaf.hom F.obj G.obj G.property
  have hcov : Sieve.generate (Presieve.ofArrows V' π) ∈ Scheme.ProEt.topology X top := by
    rw [Scheme.ProEt.mem_topology_iff]
    refine ⟨Presieve.ofArrows V' π, ?_, Sieve.le_generate _⟩
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    change Presieve.ofArrows (fun _ : Unit ↦ W) (fun _ ↦ e) ∈ Scheme.proetalePrecoverage X
    rw [Presieve.ofArrows_pUnit]
    exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) he
  have hsf : (Presieve.ofArrows V' π).IsSheafFor P := by
    have := (isSheaf_iff_isSheaf_of_type _ _).mp hP
    rw [Presieve.isSheafFor_iff_generate]
    exact this _ hcov
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsf x hx
  let toTop : ∀ U : X.ProEt, U ⟶ top := fun U ↦
    MorphismProperty.Over.homMk U.hom (Category.comp_id _) trivial
  have htop : ∀ {U : X.ProEt} (f : U ⟶ top), f = toTop U := fun f ↦ by
    exact MorphismProperty.Over.Hom.ext
      ((Category.comp_id _).symm.trans (MorphismProperty.Over.w f))
  let s : P.sections := ⟨fun U ↦ P.map (toTop U.unop).op t, fun {U U'} f ↦ by
    simp only [← Functor.map_comp_apply]
    rw [show (toTop U.unop).op ≫ f = (f.unop ≫ toTop U.unop).op from rfl,
      htop (f.unop ≫ toTop U.unop)]⟩
  refine ⟨⟨presheafHomSectionsEquiv _ _ s⟩, ?_⟩
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun W' ↦ ?_)
  let g₀ : (MorphismProperty.Over.map ⊤ he).obj W'.unop ⟶ V' () :=
    MorphismProperty.Over.homMk W'.unop.hom rfl trivial
  have h := congrArg (fun α ↦ α.app (op (Over.mk g₀))) (ht ())
  have hκ : ProEtale.overMapIso e he _ g₀.left (hw () (Over.mk g₀)) = Iso.refl _ := by
    ext; rfl
  dsimp only [x] at h
  simp only [NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatIso.op_hom, NatIso.op_inv,
    NatTrans.op_app] at h
  have h₁ : (κ ()).hom.app (Over.mk g₀) = 𝟙 _ := congrArg Iso.hom hκ
  have h₂ : (κ ()).inv.app (Over.mk g₀) = 𝟙 _ := congrArg Iso.inv hκ
  rw [h₁, h₂] at h
  erw [op_id, F.obj.map_id, G.obj.map_id, Category.id_comp, Category.comp_id] at h
  refine Eq.trans ?_ h
  change t.app (op (Over.mk (𝟙 _ ≫ toTop _))) = t.app (op (Over.mk (g₀ ≫ π ())))
  rw [htop (𝟙 _ ≫ toTop _), htop (g₀ ≫ π ())]


-- the `simp` call computes the composite restrictions on sections
set_option linter.flexible false in
include he in
/-- **Gluing morphisms of pro-étale sheaves along a single pro-étale cover**: morphisms
`e^* F ⟶ e^* G` whose pullbacks along any two `a b : W' ⟶ W` with `a ≫ e = b ≫ e` agree
descend to morphisms `F ⟶ G`. -/
theorem ProEtale.exists_hom_of_upperStar [Surjective e] [QuasiCompact e]
    (F G : Sheaf (Scheme.ProEt.topology X) A) (φ : (e)^*[A].obj F ⟶ (e)^*[A].obj G)
    (hφ : ∀ {W' : Scheme.{u}} (a b : W' ⟶ W) (w : W' ⟶ X) (ha : w = a ≫ e) (hb : w = b ≫ e)
      (_ : WeaklyEtale a) (_ : WeaklyEtale b) (_ : WeaklyEtale w),
      (ProEtale.upperStarComp' A a e w ha).hom.app F ≫ (a)^*[A].map φ ≫
          (ProEtale.upperStarComp' A a e w ha).inv.app G =
        (ProEtale.upperStarComp' A b e w hb).hom.app F ≫ (b)^*[A].map φ ≫
          (ProEtale.upperStarComp' A b e w hb).inv.app G) :
    ∃ φ' : F ⟶ G, (e)^*[A].map φ' = φ := by
  let θ := ProEtale.upperStarIsoLocalizationRestriction A e he
  let ψ := θ.inv.app F ≫ φ ≫ θ.hom.app G
  refine Exists.elim (ProEtale.exists_hom_of_localizationRestriction e he F G ψ
    fun T tj tk hj hk ↦ ?_) fun φ' hφ' ↦ ⟨φ', ?_⟩
  · have ha : WeaklyEtale tj := by
      have : WeaklyEtale (tj ≫ e) := hj ▸ T.prop
      exact WeaklyEtale.of_comp tj e
    have hb : WeaklyEtale tk := by
      have : WeaklyEtale (tk ≫ e) := hk ▸ T.prop
      exact WeaklyEtale.of_comp tk e
    have hj' : T.hom = tj ≫ e := hj.symm
    have hk' : T.hom = tk ≫ e := hk.symm
    have E := hφ tj tk T.hom hj' hk' ha hb T.prop
    have E' := congrArg (fun f ↦
      (ProEtale.upperStarIsoLocalizationRestriction A T.hom T.prop).inv.app F ≫
      f ≫ (ProEtale.upperStarIsoLocalizationRestriction A T.hom T.prop).hom.app G) E
    simp only [Category.assoc] at E'
    rw [ProEtale.upperStarComp'_conj A tj e ha he T.hom hj' T.prop,
      ProEtale.upperStarComp'_conj A tk e hb he T.hom hk' T.prop] at E'
    let U₀ : T.left.ProEt := MorphismProperty.Over.mk ⊤ (𝟙 T.left) inferInstance
    have E'' := congrArg (fun f ↦ f.hom.app (op U₀)) E'
    simp [ProEtale.localizationRestrictionComp, Functor.sheafPushforwardContinuousComp',
      Functor.sheafPushforwardContinuousComp, Functor.sheafPushforwardContinuousIso,
      ProEtale.localizationRestriction] at E''
    let ε : T ≅ (MorphismProperty.Over.map ⊤ T.prop).obj U₀ :=
      MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp _)
    have side : ∀ (t : T.left ⟶ W) (h : t ≫ e = T.hom) (h' : T.hom = t ≫ e)
        (ht : WeaklyEtale t),
        F.obj.map (ProEtale.overMapIso e he T t h).hom.op ≫ ψ.hom.app (op _) ≫
            G.obj.map (ProEtale.overMapIso e he T t h).inv.op =
          F.obj.map ε.inv.op ≫ F.obj.map ((MorphismProperty.Over.mapComp ⊤ ht he T.hom
            h').inv.app U₀).op ≫ ψ.hom.app (op ((MorphismProperty.Over.map ⊤ ht).obj U₀)) ≫
            G.obj.map ((MorphismProperty.Over.mapComp ⊤ ht he T.hom h').hom.app U₀).op ≫
              G.obj.map ε.hom.op := by
      intro t h h' ht
      let ι₀ : (MorphismProperty.Over.map ⊤ ht).obj U₀ ⟶ MorphismProperty.Over.mk ⊤ t
          (MorphismProperty.of_postcomp _ _ _ he (h ▸ T.prop)) :=
        MorphismProperty.Over.homMk (𝟙 _) (Category.id_comp t).symm trivial
      let κ₀ : MorphismProperty.Over.mk ⊤ t
          (MorphismProperty.of_postcomp _ _ _ he (h ▸ T.prop)) ⟶
            (MorphismProperty.Over.map ⊤ ht).obj U₀ :=
        MorphismProperty.Over.homMk (𝟙 _) (Category.id_comp t) trivial
      have hκι : κ₀ ≫ ι₀ = 𝟙 _ := MorphismProperty.Over.Hom.ext (by simp [ι₀, κ₀])
      have nat := ψ.hom.naturality ι₀.op
      have hψt : ψ.hom.app (op (MorphismProperty.Over.mk ⊤ t
          (MorphismProperty.of_postcomp _ _ _ he (h ▸ T.prop)))) =
          ((ProEtale.localizationRestriction A e he).obj F).obj.map ι₀.op ≫
            ψ.hom.app (op ((MorphismProperty.Over.map ⊤ ht).obj U₀)) ≫
              ((ProEtale.localizationRestriction A e he).obj G).obj.map κ₀.op := by
        rw [reassoc_of% nat, ← Functor.map_comp, ← op_comp, hκι, op_id,
          CategoryTheory.Functor.map_id,
          Category.comp_id]
      erw [hψt]
      simp only [ProEtale.localizationRestriction, Functor.sheafPushforwardContinuous_obj_obj_map,
        ← Functor.map_comp_assoc, ← Functor.map_comp, ← op_comp, Category.assoc]
      congr 2
    rw [side tj hj hj' ha, side tk hk hk' hb]
    simp only [ψ] at E'' ⊢
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Category.assoc]
      at E'' ⊢
    rw [reassoc_of% E'']
  · have := θ.hom.naturality φ'
    rw [hφ'] at this
    simpa [ψ] using (cancel_mono (θ.hom.app G)).1 (this.trans (by simp [ψ]))

end AlgebraicGeometry

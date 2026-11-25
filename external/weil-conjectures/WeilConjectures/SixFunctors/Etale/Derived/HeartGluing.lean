/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.SheafHom
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Gluing morphisms between sheaves placed in degree zero

Morphisms `F[0] ⟶ G[0]` in `D(X_ét, Λ)` between étale sheaves placed in degree zero are
morphisms of sheaves `F ⟶ G`, and morphisms of sheaves glue along open covers: the presheaf
`V ↦ Hom(F|_V, G|_V)` is a sheaf (`CategoryTheory.Presheaf.IsSheaf.hom`). So morphisms `K ⟶ M`
between objects of `D(X_ét, Λ)` that are isomorphic to sheaves in degree zero can be glued from
morphisms `Le_j^* K ⟶ Le_j^* M` on the members `e_j : V_j ⟶ X` of an open cover which agree on
overlaps.

For an étale `g`, the pullback `g^*` is restriction along the localization functor
(`AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction`); the composition isomorphisms of
pullbacks correspond to the composition of restrictions
(`AlgebraicGeometry.Etale.upperStarComp_hom_comp_upperStarIsoLocalizationRestriction`), which is
what makes the local morphisms into compatible sections of the sheaf of morphisms.

## Main statements

- `AlgebraicGeometry.Etale.exists_hom_of_localizationRestriction`,
  `AlgebraicGeometry.Etale.exists_hom_of_upperStar`: gluing of morphisms of étale sheaves.
- `AlgebraicGeometry.Etale.exists_hom_of_isOpenImmersion_cover`: gluing in the derived category.
-/

@[expose] public section

universe u' u



open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {R S T : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R) (h₁ : Etale g₁) (h₂ : Etale g₂)
  (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂) (h₁₂ : Etale g₁₂)

/-- Composition of the restrictions along étale maps. -/
noncomputable def Etale.localizationRestrictionComp :
    Etale.localizationRestriction A g₁₂ h₁₂ ≅
      Etale.localizationRestriction A g₂ h₂ ⋙ Etale.localizationRestriction A g₁ h₁ :=
  (Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.mapComp ⊤ h₁ h₂ g₁₂ hg).symm)
    A (T.smallGrothendieckTopology @Etale) (S.smallGrothendieckTopology @Etale)
    (R.smallGrothendieckTopology @Etale)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
-- the `simp` call computes the conjugate on sections
set_option linter.flexible false in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma Etale.conjugateEquiv_localizationRestrictionComp_inv :
    conjugateEquiv (Etale.localizationRestrictionLowerStarAdjunction A g₁₂ h₁₂)
        ((Etale.localizationRestrictionLowerStarAdjunction A g₂ h₂).comp
          (Etale.localizationRestrictionLowerStarAdjunction A g₁ h₁))
        (Etale.localizationRestrictionComp A g₁ g₂ h₁ h₂ g₁₂ hg h₁₂).inv =
      (Etale.lowerStarComp A g₁ g₂ g₁₂ hg).inv := by
  subst hg
  ext G : 2
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun U ↦ ?_)
  simp [conjugateEquiv_apply_app, Etale.localizationRestrictionLowerStarAdjunction,
    Etale.localizationRestrictionComp, Etale.lowerStarComp, MorphismProperty.Over.mapPullbackAdj,
    Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp,
    Functor.sheafPushforwardContinuousIso, Etale.localizationRestriction,
    Etale.lowerStar, ← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  ext
  simp only [MorphismProperty.Over.mapComp, MorphismProperty.Over.pullbackComp]
  apply pullback.hom_ext <;> simp

lemma Etale.conjugateEquiv_upperStarIsoLocalizationRestriction_hom {X Y : Scheme.{u}}
    (g : X ⟶ Y) (h : Etale g) :
    conjugateEquiv (Etale.localizationRestrictionLowerStarAdjunction A g h)
        (Etale.upperStarLowerStarAdjunction A g)
        (Etale.upperStarIsoLocalizationRestriction A g h).hom = 𝟙 _ := by
  simp [Etale.upperStarIsoLocalizationRestriction, Adjunction.leftAdjointUniq, conjugateIsoEquiv]

/-- **Composition of étale pullbacks is composition of restrictions.** -/
lemma Etale.upperStarComp_hom_comp_upperStarIsoLocalizationRestriction :
    (Etale.upperStarComp A g₁ g₂ g₁₂ hg).hom ≫
        Functor.whiskerRight (Etale.upperStarIsoLocalizationRestriction A g₂ h₂).hom
          (Etale.upperStar A g₁) ≫
        Functor.whiskerLeft (Etale.localizationRestriction A g₂ h₂)
          (Etale.upperStarIsoLocalizationRestriction A g₁ h₁).hom =
      (Etale.upperStarIsoLocalizationRestriction A g₁₂ h₁₂).hom ≫
        (Etale.localizationRestrictionComp A g₁ g₂ h₁ h₂ g₁₂ hg h₁₂).hom := by
  let C := (Etale.localizationRestrictionLowerStarAdjunction A g₂ h₂).comp
    (Etale.localizationRestrictionLowerStarAdjunction A g₁ h₁)
  let LU := (Etale.localizationRestrictionLowerStarAdjunction A g₂ h₂).comp
    (Etale.upperStarLowerStarAdjunction A g₁)
  let UU := (Etale.upperStarLowerStarAdjunction A g₂).comp (Etale.upperStarLowerStarAdjunction A g₁)
  let U₁₂ := Etale.upperStarLowerStarAdjunction A g₁₂
  let L₁₂ := Etale.localizationRestrictionLowerStarAdjunction A g₁₂ h₁₂
  apply (conjugateEquiv C U₁₂).injective
  rw [← conjugateEquiv_comp C UU U₁₂, ← conjugateEquiv_comp C LU UU,
    ← conjugateEquiv_comp C L₁₂ U₁₂]
  dsimp only [C, LU, UU]
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    Etale.conjugateEquiv_upperStarIsoLocalizationRestriction_hom,
    Etale.conjugateEquiv_upperStarIsoLocalizationRestriction_hom,
    Etale.conjugateEquiv_upperStarIsoLocalizationRestriction_hom]
  have h := Etale.conjugateEquiv_localizationRestrictionComp_inv A g₁ g₂ h₁ h₂ g₁₂ hg h₁₂
  simp only [Functor.whiskerRight_id', Functor.whiskerLeft_id', Category.id_comp, Category.comp_id]
  have e₁ : conjugateIsoEquiv L₁₂ _
      (Etale.localizationRestrictionComp A g₁ g₂ h₁ h₂ g₁₂ hg h₁₂).symm =
      (Etale.lowerStarComp A g₁ g₂ g₁₂ hg).symm := Iso.ext (by simpa using h)
  have e₂ := (conjugateIsoEquiv U₁₂ UU).apply_symm_apply (Etale.lowerStarComp A g₁ g₂ g₁₂ hg).symm
  have h₁ := congrArg Iso.inv e₁
  have h₂ := congrArg Iso.inv e₂
  simp only [conjugateIsoEquiv_apply_inv, Iso.symm_inv] at h₁ h₂
  rw [h₁]
  convert h₂ using 2
  simp [Etale.upperStarComp]
  rfl

end AlgebraicGeometry


open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {X : Scheme.{u}} {ι : Type u} {V : ι → Scheme.{u}} (e : ∀ j, V j ⟶ X)
  (he : ∀ j, Etale (e j))

/-- The identification of `T ⟶ V_j ⟶ X` with an étale `X`-scheme `T`. -/
noncomputable def Etale.overMapIso (j : ι) (T : X.Etale) (t : T.left ⟶ V j) (h : t ≫ e j = T.hom) :
    (MorphismProperty.Over.map ⊤ (he j)).obj (MorphismProperty.Over.mk ⊤ t
      (MorphismProperty.of_postcomp _ _ _ (he j) (h ▸ T.prop))) ≅ T :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by simp [h])

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
theorem Etale.exists_hom_of_localizationRestriction
    (hcov : ⋃ j, Set.range (e j).base = Set.univ) (F G : Sheaf X.smallEtaleTopology A)
    (ψ : ∀ j, (Etale.localizationRestriction A (e j) (he j)).obj F ⟶
      (Etale.localizationRestriction A (e j) (he j)).obj G)
    (hψ : ∀ j k (T : X.Etale) (tj : T.left ⟶ V j) (tk : T.left ⟶ V k) (hj : tj ≫ e j = T.hom)
      (hk : tk ≫ e k = T.hom),
      F.obj.map (Etale.overMapIso e he j T tj hj).hom.op ≫ (ψ j).hom.app (op _) ≫
          G.obj.map (Etale.overMapIso e he j T tj hj).inv.op =
        F.obj.map (Etale.overMapIso e he k T tk hk).hom.op ≫ (ψ k).hom.app (op _) ≫
          G.obj.map (Etale.overMapIso e he k T tk hk).inv.op) :
    ∃ φ : F ⟶ G, ∀ j, (Etale.localizationRestriction A (e j) (he j)).map φ = ψ j := by
  let P := presheafHom F.obj G.obj
  let V' : ι → X.Etale := fun j ↦ MorphismProperty.Over.mk ⊤ (e j) (he j)
  let top : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X) inferInstance
  let π : ∀ j, V' j ⟶ top := fun j ↦ MorphismProperty.Over.homMk (e j) (Category.comp_id _) trivial
  have hw : ∀ j (T : Over (V' j)), T.hom.left ≫ e j = T.left.hom := fun j T ↦ by
    simpa [V'] using MorphismProperty.Over.w T.hom
  -- the transport of `ψ j` to the localized site at `V' j`
  let Φ : ∀ j, Over (V' j) ⥤ (V j).Etale := fun j ↦
    { obj T := MorphismProperty.Over.mk ⊤ T.hom.left
        (MorphismProperty.of_postcomp _ _ _ (he j) (by
          rw [hw j T]; exact T.left.prop))
      map g := MorphismProperty.Over.homMk g.left.left
        (congrArg (fun f ↦ f.left) (Over.w g)) trivial }
  let κ : ∀ j, Φ j ⋙ MorphismProperty.Over.map ⊤ (he j) ≅ Over.forget (V' j) := fun j ↦
    NatIso.ofComponents (fun T ↦ Etale.overMapIso e he j T.left T.hom.left
      (hw j T)) (fun g ↦ by ext; simp [Etale.overMapIso, Φ])
  let x : ∀ j, P.obj (op (V' j)) := fun j ↦
    (Functor.isoWhiskerRight (NatIso.op (κ j)) F.obj).hom ≫
      Functor.whiskerLeft (Φ j).op (ψ j).hom ≫
        (Functor.isoWhiskerRight (NatIso.op (κ j)) G.obj).inv
  have hx : Presieve.Arrows.Compatible P π x := by
    intro i k Z gi gk h
    refine NatTrans.ext (funext fun T ↦ ?_)
    exact hψ i k T.unop.left _ _ (hw i ((Over.map gi).obj T.unop)) (hw k ((Over.map gk).obj T.unop))
  have hP : Presheaf.IsSheaf X.smallEtaleTopology P := Presheaf.IsSheaf.hom F.obj G.obj G.property
  have hsf : (Presieve.ofArrows V' π).IsSheafFor P := by
    have := (isSheaf_iff_isSheaf_of_type _ _).mp hP
    rw [Presieve.isSheafFor_iff_generate]
    exact this _ ((ofArrows_mem_smallEtaleTopology_iff π).2 hcov)
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsf x hx
  let toTop : ∀ U : X.Etale, U ⟶ top := fun U ↦
    MorphismProperty.Over.homMk U.hom (Category.comp_id _) trivial
  have htop : ∀ {U : X.Etale} (f : U ⟶ top), f = toTop U := fun f ↦ by
    exact MorphismProperty.Over.Hom.ext
      ((Category.comp_id _).symm.trans (MorphismProperty.Over.w f))
  let s : P.sections := ⟨fun U ↦ P.map (toTop U.unop).op t, fun {U U'} f ↦ by
    simp only [← Functor.map_comp_apply]
    rw [show (toTop U.unop).op ≫ f = (f.unop ≫ toTop U.unop).op from rfl,
      htop (f.unop ≫ toTop U.unop)]⟩
  refine ⟨⟨presheafHomSectionsEquiv _ _ s⟩, fun j ↦ ?_⟩
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun W ↦ ?_)
  let g₀ : (MorphismProperty.Over.map ⊤ (he j)).obj W.unop ⟶ V' j :=
    MorphismProperty.Over.homMk W.unop.hom rfl trivial
  have h := congrArg (fun α ↦ α.app (op (Over.mk g₀))) (ht j)
  have hκ : Etale.overMapIso e he j _ g₀.left (hw j (Over.mk g₀)) = Iso.refl _ := by
    ext; rfl
  dsimp only [x] at h
  simp only [NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatIso.op_hom, NatIso.op_inv,
    NatTrans.op_app] at h
  have h₁ : (κ j).hom.app (Over.mk g₀) = 𝟙 _ := congrArg Iso.hom hκ
  have h₂ : (κ j).inv.app (Over.mk g₀) = 𝟙 _ := congrArg Iso.inv hκ
  rw [h₁, h₂] at h
  erw [op_id, F.obj.map_id, G.obj.map_id, Category.id_comp, Category.comp_id] at h
  refine Eq.trans ?_ h
  change t.app (op (Over.mk (𝟙 _ ≫ toTop _))) = t.app (op (Over.mk (g₀ ≫ π j)))
  rw [htop (𝟙 _ ≫ toTop _), htop (g₀ ≫ π j)]

end AlgebraicGeometry


open CategoryTheory Limits Opposite

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- Conjugating a composite pullback by the restriction identifications. -/
lemma Etale.upperStarComp_conj {R S T : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R) (h₁ : Etale g₁)
    (h₂ : Etale g₂) (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂) (h₁₂ : Etale g₁₂)
    {F G : Sheaf R.smallEtaleTopology A} (φ : (g₂)^*[A].obj F ⟶ (g₂)^*[A].obj G) :
    (Etale.upperStarIsoLocalizationRestriction A g₁₂ h₁₂).inv.app F ≫
        (Etale.upperStarComp A g₁ g₂ g₁₂ hg).hom.app F ≫ (g₁)^*[A].map φ ≫
          (Etale.upperStarComp A g₁ g₂ g₁₂ hg).inv.app G ≫
            (Etale.upperStarIsoLocalizationRestriction A g₁₂ h₁₂).hom.app G =
      (Etale.localizationRestrictionComp A g₁ g₂ h₁ h₂ g₁₂ hg h₁₂).hom.app F ≫
        (Etale.localizationRestriction A g₁ h₁).map
          ((Etale.upperStarIsoLocalizationRestriction A g₂ h₂).inv.app F ≫ φ ≫
            (Etale.upperStarIsoLocalizationRestriction A g₂ h₂).hom.app G) ≫
        (Etale.localizationRestrictionComp A g₁ g₂ h₁ h₂ g₁₂ hg h₁₂).inv.app G := by
  have hF := NatTrans.congr_app
    (Etale.upperStarComp_hom_comp_upperStarIsoLocalizationRestriction A g₁ g₂ h₁ h₂ g₁₂ hg h₁₂) F
  have hG := NatTrans.congr_app
    (Etale.upperStarComp_hom_comp_upperStarIsoLocalizationRestriction A g₁ g₂ h₁ h₂ g₁₂ hg h₁₂) G
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hF hG
  rw [← cancel_epi ((Etale.upperStarIsoLocalizationRestriction A g₁₂ h₁₂).hom.app F),
    Iso.hom_inv_id_app_assoc, ← reassoc_of% hF]
  rw [← cancel_mono ((Etale.localizationRestrictionComp A g₁ g₂ h₁ h₂ g₁₂ hg h₁₂).hom.app G)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← hG]
  simp only [Functor.map_comp, Category.assoc,
    ]
  simp only [Iso.inv_hom_id_app_assoc]
  have n₁ := (Etale.upperStarIsoLocalizationRestriction A g₁ h₁).hom.naturality
    ((Etale.upperStarIsoLocalizationRestriction A g₂ h₂).inv.app F ≫ φ ≫
      (Etale.upperStarIsoLocalizationRestriction A g₂ h₂).hom.app G)
  erw [Category.comp_id]
  rw [← Functor.map_comp, ← Functor.map_comp]
  erw [← n₁]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]

variable {X : Scheme.{u}} {ι : Type u} {V : ι → Scheme.{u}} (e : ∀ j, V j ⟶ X)
  (he : ∀ j, Etale (e j))

-- the `simp` call computes the composite restrictions on sections
set_option linter.flexible false in
include he in
theorem Etale.exists_hom_of_upperStar (hcov : ⋃ j, Set.range (e j).base = Set.univ)
    (F G : Sheaf X.smallEtaleTopology A) (φ : ∀ j, (e j)^*[A].obj F ⟶ (e j)^*[A].obj G)
    (hφ : ∀ j k {W : Scheme.{u}} (a : W ⟶ V j) (b : W ⟶ V k) (w : W ⟶ X) (ha : w = a ≫ e j)
      (hb : w = b ≫ e k) (_ : Etale a) (_ : Etale b) (_ : Etale w),
      (Etale.upperStarComp A a (e j) w ha).hom.app F ≫ (a)^*[A].map (φ j) ≫
          (Etale.upperStarComp A a (e j) w ha).inv.app G =
        (Etale.upperStarComp A b (e k) w hb).hom.app F ≫ (b)^*[A].map (φ k) ≫
          (Etale.upperStarComp A b (e k) w hb).inv.app G) :
    ∃ φ' : F ⟶ G, ∀ j, (e j)^*[A].map φ' = φ j := by
  let θ := fun j ↦ Etale.upperStarIsoLocalizationRestriction A (e j) (he j)
  let ψ := fun j ↦ (θ j).inv.app F ≫ φ j ≫ (θ j).hom.app G
  refine Exists.elim (Etale.exists_hom_of_localizationRestriction e he hcov F G ψ
    fun j k T tj tk hj hk ↦ ?_) fun φ' hφ' ↦ ⟨φ', fun j ↦ ?_⟩
  · have ha : Etale tj := by
      have : Etale (tj ≫ e j) := hj ▸ T.prop
      exact .of_comp tj (e j)
    have hb : Etale tk := by
      have : Etale (tk ≫ e k) := hk ▸ T.prop
      exact .of_comp tk (e k)
    have E := hφ j k tj tk T.hom hj.symm hk.symm ha hb T.prop
    have E' := congrArg (fun f ↦
      (Etale.upperStarIsoLocalizationRestriction A T.hom T.prop).inv.app F ≫
      f ≫ (Etale.upperStarIsoLocalizationRestriction A T.hom T.prop).hom.app G) E
    simp only [Category.assoc] at E'
    rw [Etale.upperStarComp_conj tj (e j) ha (he j) T.hom hj.symm T.prop,
      Etale.upperStarComp_conj tk (e k) hb (he k) T.hom hk.symm T.prop] at E'
    let U₀ : T.left.Etale := MorphismProperty.Over.mk ⊤ (𝟙 T.left) inferInstance
    have E'' := congrArg (fun f ↦ f.hom.app (op U₀)) E'
    simp [Etale.localizationRestrictionComp, Functor.sheafPushforwardContinuousComp',
      Functor.sheafPushforwardContinuousComp, Functor.sheafPushforwardContinuousIso,
      Etale.localizationRestriction] at E''
    let ε : T ≅ (MorphismProperty.Over.map ⊤ T.prop).obj U₀ :=
      MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp _)
    have side : ∀ (i : ι) (t : T.left ⟶ V i) (h : t ≫ e i = T.hom) (ht : Etale t),
        F.obj.map (Etale.overMapIso e he i T t h).hom.op ≫ (ψ i).hom.app (op _) ≫
            G.obj.map (Etale.overMapIso e he i T t h).inv.op =
          F.obj.map ε.inv.op ≫ F.obj.map ((MorphismProperty.Over.mapComp ⊤ ht (he i) T.hom
            h.symm).inv.app U₀).op ≫ (ψ i).hom.app (op ((MorphismProperty.Over.map ⊤ ht).obj U₀)) ≫
            G.obj.map ((MorphismProperty.Over.mapComp ⊤ ht (he i) T.hom h.symm).hom.app U₀).op ≫
              G.obj.map ε.hom.op := by
      intro i t h ht
      let ι₀ : (MorphismProperty.Over.map ⊤ ht).obj U₀ ⟶ MorphismProperty.Over.mk ⊤ t
          (MorphismProperty.of_postcomp _ _ _ (he i) (h ▸ T.prop)) :=
        MorphismProperty.Over.homMk (𝟙 _) (Category.id_comp t).symm trivial
      let κ₀ : MorphismProperty.Over.mk ⊤ t
          (MorphismProperty.of_postcomp _ _ _ (he i) (h ▸ T.prop)) ⟶
            (MorphismProperty.Over.map ⊤ ht).obj U₀ :=
        MorphismProperty.Over.homMk (𝟙 _) (Category.id_comp t) trivial
      have hκι : κ₀ ≫ ι₀ = 𝟙 _ := MorphismProperty.Over.Hom.ext (by simp [ι₀, κ₀])
      have nat := (ψ i).hom.naturality ι₀.op
      have hψt : (ψ i).hom.app (op (MorphismProperty.Over.mk ⊤ t
          (MorphismProperty.of_postcomp _ _ _ (he i) (h ▸ T.prop)))) =
          ((Etale.localizationRestriction A (e i) (he i)).obj F).obj.map ι₀.op ≫
            (ψ i).hom.app (op ((MorphismProperty.Over.map ⊤ ht).obj U₀)) ≫
              ((Etale.localizationRestriction A (e i) (he i)).obj G).obj.map κ₀.op := by
        rw [reassoc_of% nat, ← Functor.map_comp, ← op_comp, hκι, op_id,
          CategoryTheory.Functor.map_id,
          Category.comp_id]
      erw [hψt]
      simp only [Etale.localizationRestriction, Functor.sheafPushforwardContinuous_obj_obj_map,
        ← Functor.map_comp_assoc, ← Functor.map_comp, ← op_comp, Category.assoc]
      congr 2
    rw [side j tj hj ha, side k tk hk hb]
    simp only [ψ] at E'' ⊢
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Category.assoc] at E'' ⊢
    rw [reassoc_of% E'']
  · have := (θ j).hom.naturality φ'
    rw [hφ' j] at this
    simpa [ψ] using (cancel_mono ((θ j).hom.app G)).1 (this.trans (by simp [ψ]))

end AlgebraicGeometry


open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The derived composition isomorphism on a sheaf in degree zero is the composition isomorphism
of the pullbacks. -/
lemma Etale.leftDerivedUpperStarComp_hom_app_singleFunctor_obj {T S R : Scheme.{u}}
    (g₁ : T ⟶ S) (g₂ : S ⟶ R) (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂)
    (F : Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.leftDerivedUpperStarComp _ g₁ g₂ g₁₂ hg).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj F) ≫
      (L((g₁)^*[ModuleCat.{u + 1} Λ])).map
        (((g₂)^*[_]).singleFunctorCompLeftDerivedFunctorIso.hom.app F) ≫
      ((g₁)^*[_]).singleFunctorCompLeftDerivedFunctorIso.hom.app ((g₂)^*[_].obj F) =
    ((g₁₂)^*[_]).singleFunctorCompLeftDerivedFunctorIso.hom.app F ≫
      (DerivedCategory.singleFunctor _ 0).map ((Etale.upperStarComp _ g₁ g₂ g₁₂ hg).hom.app F) := by
  simp only [Etale.leftDerivedUpperStarComp, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.leftDerivedFunctorCompIso_hom_app_singleFunctor_obj]
  exact Functor.leftDerivedFunctorNatIso_hom_app_singleFunctor_obj _ _ _ F

/-- Transport of a local morphism along a composite of pullbacks. -/
lemma Etale.leftDerivedUpperStarComp_conj_comp {W P Y Z : Scheme.{u}} (f : W ⟶ P) (g : P ⟶ Y)
    (h : Y ⟶ Z) (fg : W ⟶ Y) (gh : P ⟶ Z) (fgh : W ⟶ Z) (hfg : fg = f ≫ g) (hgh : gh = g ≫ h)
    (hfgh : fgh = fg ≫ h) {K M : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (δ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ (L((h)^*[ModuleCat.{u + 1} Λ])).obj M) :
    (Etale.leftDerivedUpperStarComp _ fg h fgh hfgh).hom.app K ≫ (L((fg)^*[_])).map δ ≫
        (Etale.leftDerivedUpperStarComp _ fg h fgh hfgh).inv.app M =
      (Etale.leftDerivedUpperStarComp _ f gh fgh
          (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app K ≫
        (L((f)^*[_])).map ((Etale.leftDerivedUpperStarComp _ g h gh hgh).hom.app K ≫
          (L((g)^*[_])).map δ ≫ (Etale.leftDerivedUpperStarComp _ g h gh hgh).inv.app M) ≫
        (Etale.leftDerivedUpperStarComp _ f gh fgh
          (by rw [hfgh, hfg, hgh, Category.assoc])).inv.app M := by
  have a₁ := Etale.leftDerivedUpperStarComp_assoc'_app _ f g h fg gh fgh hfg hgh hfgh K
  have a₂ := Etale.leftDerivedUpperStarComp_assoc'_app _ f g h fg gh fgh hfg hgh hfgh M
  have n := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g fg hfg).hom.naturality δ
  have a₂' : (Etale.leftDerivedUpperStarComp _ f g fg hfg).hom.app _ ≫
      (L((f)^*[_])).map ((Etale.leftDerivedUpperStarComp _ g h gh hgh).inv.app M) ≫
        (Etale.leftDerivedUpperStarComp _ f gh fgh
          (by rw [hfgh, hfg, hgh, Category.assoc])).inv.app M =
      (Etale.leftDerivedUpperStarComp _ fg h fgh hfgh).inv.app M := by
    rw [← cancel_epi ((Etale.leftDerivedUpperStarComp _ fg h fgh hfgh).hom.app M),
      ← reassoc_of% a₂]
    simp [← Functor.map_comp_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% a₁]
  erw [← reassoc_of% n]
  rw [a₂']

/-- Coherent comparison isomorphisms preserve the transport of a morphism by conjugation. -/
private lemma map_conj_of_comparison
    {C₀ : Type*} {C₁ : Type*} {C₂ : Type*} {D₀ : Type*} {D₁ : Type*} {D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category D₀] [Category D₁] [Category D₂]
    (S₀ : C₀ ⥤ D₀) (S₁ : C₁ ⥤ D₁) (S₂ : C₂ ⥤ D₂)
    (F₁ : C₀ ⥤ C₁) (F₂ : C₁ ⥤ C₂) (F₁₂ : C₀ ⥤ C₂)
    (L₁ : D₀ ⥤ D₁) (L₂ : D₁ ⥤ D₂) (L₁₂ : D₀ ⥤ D₂)
    (s₁ : S₀ ⋙ L₁ ≅ F₁ ⋙ S₁) (s₂ : S₁ ⋙ L₂ ≅ F₂ ⋙ S₂)
    (s₁₂ : S₀ ⋙ L₁₂ ≅ F₁₂ ⋙ S₂) (c : F₁₂ ≅ F₁ ⋙ F₂) (d : L₁₂ ≅ L₁ ⋙ L₂)
    (hc : ∀ X, d.hom.app (S₀.obj X) ≫ L₂.map (s₁.hom.app X) ≫ s₂.hom.app (F₁.obj X) =
      s₁₂.hom.app X ≫ S₂.map (c.hom.app X))
    {K M : D₀} {X Y : C₀} (k : S₀.obj X ⟶ K) (m : M ⟶ S₀.obj Y)
    (δ : L₁.obj K ⟶ L₁.obj M) (φ : F₁.obj X ⟶ F₁.obj Y)
    (hφ : S₁.map φ = s₁.inv.app X ≫ L₁.map k ≫ δ ≫ L₁.map m ≫ s₁.hom.app Y) :
    S₂.map (c.hom.app X ≫ F₂.map φ ≫ c.inv.app Y) =
      s₁₂.inv.app X ≫ L₁₂.map k ≫
        (d.hom.app K ≫ L₂.map δ ≫ d.inv.app M) ≫ L₁₂.map m ≫ s₁₂.hom.app Y := by
  have h₁ : ∀ Z, S₂.map (c.hom.app Z) = s₁₂.inv.app Z ≫ d.hom.app (S₀.obj Z) ≫
      L₂.map (s₁.hom.app Z) ≫ s₂.hom.app (F₁.obj Z) := fun Z ↦ by
    rw [hc Z, Iso.inv_hom_id_app_assoc]
  have h₂ : S₂.map (c.inv.app Y) = s₂.inv.app (F₁.obj Y) ≫ L₂.map (s₁.inv.app Y) ≫
      d.inv.app (S₀.obj Y) ≫ s₁₂.hom.app Y := by
    rw [← cancel_epi (S₂.map (c.hom.app Y)), ← Functor.map_comp,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, h₁ Y]
    simp [← Functor.map_comp_assoc]
  have h : s₁.hom.app X ≫ S₁.map φ ≫ s₁.inv.app Y = L₁.map k ≫ δ ≫ L₁.map m := by
    rw [hφ]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  have h' := congrArg L₂.map h
  simp only [Functor.map_comp] at h'
  have nK := d.hom.naturality k
  have nM := d.inv.naturality m
  simp only [Functor.comp_map] at nK nM
  have nφ := (NatIso.naturality_1 s₂ φ).symm
  dsimp only [Functor.comp_map] at nφ
  rw [Functor.map_comp, Functor.map_comp, h₁ X, h₂, nφ]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% h', ← reassoc_of% nK, reassoc_of% nM]

/-- The comparison with degree-zero sheaves transports conjugation along a composite pullback. -/
private lemma Etale.leftDerivedUpperStarComp_map_conj {T S R : Scheme.{u}}
    (g₁ : T ⟶ S) (g₂ : S ⟶ R) (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂)
    {K M : DerivedCategory (Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {F G : Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (k : (DerivedCategory.singleFunctor _ 0).obj F ⟶ K)
    (m : M ⟶ (DerivedCategory.singleFunctor _ 0).obj G)
    (δ : (L((g₂)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ (L((g₂)^*[_])).obj M)
    (φ : (g₂)^*[ModuleCat.{u + 1} Λ].obj F ⟶ (g₂)^*[_].obj G)
    (hφ : (DerivedCategory.singleFunctor _ 0).map φ =
      ((g₂)^*[_]).singleFunctorCompLeftDerivedFunctorIso.inv.app F ≫
        (L((g₂)^*[_])).map k ≫ δ ≫ (L((g₂)^*[_])).map m ≫
          ((g₂)^*[_]).singleFunctorCompLeftDerivedFunctorIso.hom.app G) :
    (DerivedCategory.singleFunctor _ 0).map
      ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) g₁ g₂ g₁₂ hg).hom.app F ≫
        (g₁)^*[_].map φ ≫ (Etale.upperStarComp _ g₁ g₂ g₁₂ hg).inv.app G) =
      ((g₁₂)^*[_]).singleFunctorCompLeftDerivedFunctorIso.inv.app F ≫
        (L((g₁₂)^*[_])).map k ≫
          ((leftDerivedUpperStarComp _ g₁ g₂ g₁₂ hg).hom.app K ≫
            (L((g₁)^*[_])).map δ ≫ (leftDerivedUpperStarComp _ g₁ g₂ g₁₂ hg).inv.app M) ≫
          (L((g₁₂)^*[_])).map m ≫
            ((g₁₂)^*[_]).singleFunctorCompLeftDerivedFunctorIso.hom.app G := by
  exact map_conj_of_comparison
    (DerivedCategory.singleFunctor _ 0) (DerivedCategory.singleFunctor _ 0)
    (DerivedCategory.singleFunctor _ 0) (g₂)^*[_] (g₁)^*[_] (g₁₂)^*[_]
    (L((g₂)^*[_])) (L((g₁)^*[_])) (L((g₁₂)^*[_]))
    ((g₂)^*[_]).singleFunctorCompLeftDerivedFunctorIso
    ((g₁)^*[_]).singleFunctorCompLeftDerivedFunctorIso
    ((g₁₂)^*[_]).singleFunctorCompLeftDerivedFunctorIso
    (Etale.upperStarComp _ g₁ g₂ g₁₂ hg) (Etale.leftDerivedUpperStarComp _ g₁ g₂ g₁₂ hg)
    (Etale.leftDerivedUpperStarComp_hom_app_singleFunctor_obj g₁ g₂ g₁₂ hg) k m δ φ hφ

theorem Etale.exists_hom_of_isOpenImmersion_cover {X : Scheme.{u}}
    {K M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (eK : K ≅ (DerivedCategory.singleFunctor _ 0).obj F)
    (eM : M ≅ (DerivedCategory.singleFunctor _ 0).obj G)
    {ι : Type u} {V : ι → Scheme.{u}} (e : ∀ j, V j ⟶ X) [∀ j, IsOpenImmersion (e j)]
    (hcov : ∀ x : X, ∃ j, x ∈ Set.range (e j).base)
    (δ : ∀ j, (L((e j)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ (L((e j)^*[ModuleCat.{u + 1} Λ])).obj M)
    (hδ : ∀ j k {W : Scheme.{u}} (a : W ⟶ V j) (b : W ⟶ V k) [IsOpenImmersion a]
      [IsOpenImmersion b] (h : a ≫ e j = b ≫ e k),
      (leftDerivedUpperStarComp _ a (e j)).hom.app K ≫ (L((a)^*[_])).map (δ j) ≫
          (leftDerivedUpperStarComp _ a (e j)).inv.app M =
        (leftDerivedUpperStarComp _ b (e k) (a ≫ e j) h).hom.app K ≫ (L((b)^*[_])).map (δ k) ≫
          (leftDerivedUpperStarComp _ b (e k) (a ≫ e j) h).inv.app M) :
    ∃ γ : K ⟶ M, ∀ j, (L((e j)^*[ModuleCat.{u + 1} Λ])).map γ = δ j := by
  let s := fun {Y Z : Scheme.{u}} (g : Y ⟶ Z) ↦
    ((g)^*[ModuleCat.{u + 1} Λ]).singleFunctorCompLeftDerivedFunctorIso
  let φ := fun j ↦ (DerivedCategory.singleFunctor (Sheaf (V j).smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0).preimage ((s (e j)).inv.app F ≫ (L((e j)^*[_])).map eK.inv ≫ δ j ≫
      (L((e j)^*[_])).map eM.hom ≫ (s (e j)).hom.app G)
  have hφ : ∀ j, (DerivedCategory.singleFunctor _ 0).map (φ j) = (s (e j)).inv.app F ≫
      (L((e j)^*[_])).map eK.inv ≫ δ j ≫ (L((e j)^*[_])).map eM.hom ≫ (s (e j)).hom.app G :=
    fun j ↦ Functor.map_preimage _ _
  have he : ∀ j, Etale (e j) := fun j ↦ inferInstance
  have hcov' : ⋃ j, Set.range (e j).base = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 (hcov x)
  obtain ⟨φ', hφ'⟩ := Etale.exists_hom_of_upperStar e he hcov' F G φ (by
    intro j k W a b w ha hb _ _ _
    apply (DerivedCategory.singleFunctor _ 0).map_injective
    rw [Etale.leftDerivedUpperStarComp_map_conj a (e j) w ha eK.inv eM.hom
      (δ j) (φ j) (hφ j),
      Etale.leftDerivedUpperStarComp_map_conj b (e k) w hb eK.inv eM.hom
        (δ k) (φ k) (hφ k)]
    have hab : a ≫ e j = b ≫ e k := ha.symm.trans hb
    let ℓ := pullback.lift a b hab
    have T₁ := Etale.leftDerivedUpperStarComp_conj_comp ℓ (pullback.fst (e j) (e k)) (e j) a
      (pullback.fst (e j) (e k) ≫ e j) w (pullback.lift_fst _ _ _).symm rfl
      (by rw [ha, ← pullback.lift_fst a b hab, Category.assoc]) (δ j)
    have T₂ := Etale.leftDerivedUpperStarComp_conj_comp ℓ (pullback.snd (e j) (e k)) (e k) b
      (pullback.fst (e j) (e k) ≫ e j) w (pullback.lift_snd _ _ _).symm pullback.condition
      (by rw [hb, ← pullback.lift_snd a b hab, Category.assoc]) (δ k)
    have H := hδ j k (pullback.fst (e j) (e k)) (pullback.snd (e j) (e k)) pullback.condition
    have hτ : (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) a (e j) w ha).hom.app K ≫
        (L((a)^*[ModuleCat.{u + 1} Λ])).map (δ j) ≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) a (e j) w ha).inv.app M =
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) b (e k) w hb).hom.app K ≫
        (L((b)^*[ModuleCat.{u + 1} Λ])).map (δ k) ≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) b (e k) w hb).inv.app M := by
      rw [T₁, T₂, H]
    rw [hτ])
  refine ⟨eK.hom ≫ (DerivedCategory.singleFunctor _ 0).map φ' ≫ eM.inv, fun j ↦ ?_⟩
  have hs := (NatIso.naturality_2 (s (e j)) φ').symm
  dsimp only [Functor.comp_map] at hs
  rw [Functor.map_comp, Functor.map_comp, hs, hφ' j, hφ j]
  simp [← Functor.map_comp_assoc]

end AlgebraicGeometry

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.PushforwardZeroSingle
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.DescentDiagram

/-!
# Underived transition maps of the pushforward stages

For `f₀ : Z ⟶ X` and `q : X ⟶ Y`, consider the stages `(Z, Y, f₀ ≫ q, q, 𝟙 Z)` over `X`. Their
underived functors send a sheaf `J` on `Z` to `q^* (f₀ ≫ q)_* J ≅ q^* q_* (f₀_* J)`
(`AlgebraicGeometry.Etale.pushforwardStageIso`), and under these identifications the
underived transition maps (`AlgebraicGeometry.Etale.LimitStage.sheafTransition`) are the
counits `q^* q_* F ⟶ F` and the transition maps `AlgebraicGeometry.Etale.descentTransition`
of the system `q^* q_* F` for `F = f₀_* J`
(`AlgebraicGeometry.Etale.sheafTransition_pushforwardStage_proj`,
`AlgebraicGeometry.Etale.pushforwardStageIso_descentTransition`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

section Descent

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {X Y Z : Scheme.{u}} (q : X ⟶ Y) (g : Y ⟶ Z) (r : X ⟶ Z) (hr : r = q ≫ g)
  (F : Sheaf X.smallEtaleTopology A)

/-- The transition map `r^* r_* F ⟶ q^* q_* F` is the composition isomorphism
`r^* ≅ q^* g^*` followed by the pullback along `q` of
`g^* r_* F ≅ g^* g_* q_* F ⟶ q_* F`. -/
lemma descentTransition_eq_upperStarComp :
    descentTransition A q g r hr F =
      (Etale.upperStarComp A q g r hr).hom.app ((r)_*[A].obj F) ≫
        (q)^*[A].map ((g)^*[A].map ((lowerStarComp A q g r hr).inv.app F) ≫
          (upperStarLowerStarAdjunction A g).counit.app ((q)_*[A].obj F)) := by
  apply ((upperStarLowerStarAdjunction A r).homEquiv _ _).injective
  rw [homEquiv_descentTransition, Adjunction.homEquiv_unit, Functor.map_comp,
    reassoc_of% (Etale.upperStarComp_hom_app_unit_app A q g ((r)_*[A].obj F) r hr),
    Adjunction.comp_unit_app]
  have n1 := (lowerStarComp A q g r hr).hom.naturality ((q)^*[A].map
    ((g)^*[A].map ((lowerStarComp A q g r hr).inv.app F) ≫
      (upperStarLowerStarAdjunction A g).counit.app ((q)_*[A].obj F)))
  have n2 := (upperStarLowerStarAdjunction A q).unit.naturality
    ((g)^*[A].map ((lowerStarComp A q g r hr).inv.app F) ≫
      (upperStarLowerStarAdjunction A g).counit.app ((q)_*[A].obj F))
  have n3 := (upperStarLowerStarAdjunction A g).unit.naturality
    ((lowerStarComp A q g r hr).inv.app F)
  simp only [Functor.comp_map, Functor.id_map] at n1 n2 n3
  rw [Category.assoc, ← n1, ← Functor.map_comp_assoc, ← n2]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% n3,
    reassoc_of% ((upperStarLowerStarAdjunction A g).right_triangle_components
      ((q)_*[A].obj F)), descentTransitionAux]
  rfl

omit [HasSmallSiteSheafify A] in
/-- Morphisms to `q_* F` are determined by their transposes `q^* M ⟶ F`. -/
lemma eq_of_upperStar_map_comp_counit {M : Sheaf Y.smallEtaleTopology A}
    {x y : M ⟶ (q)_*[A].obj F}
    (h : (q)^*[A].map x ≫ (upperStarLowerStarAdjunction A q).counit.app F =
      (q)^*[A].map y ≫ (upperStarLowerStarAdjunction A q).counit.app F) : x = y := by
  apply ((upperStarLowerStarAdjunction A q).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  exact h

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- Changing the composite in a pair of composition isomorphisms of the pushforwards. -/
lemma lowerStarComp_hom_inv_app_congr {T S S' R : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (h₁' : T ⟶ S') (h₂' : S' ⟶ R) (k k' : T ⟶ R) (e : k = k') (p : k = h₁ ≫ h₂)
    (p' : k = h₁' ≫ h₂') (G : Sheaf T.smallEtaleTopology A) :
    (lowerStarComp A h₁ h₂ k p).hom.app G ≫ (lowerStarComp A h₁' h₂' k p').inv.app G =
      (lowerStarComp A h₁ h₂ k' (e ▸ p)).hom.app G ≫
        (lowerStarComp A h₁' h₂' k' (e ▸ p')).inv.app G := by
  subst e
  rfl

end Descent

variable (Λ : Type (u + 1)) [CommRing Λ]

section Pushforward

variable {X Y Z : Scheme.{u}} (f₀ : Z ⟶ X) (J : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- `(f₀ ≫ q)_* (𝟙 Z)^* J ≅ q_* f₀_* J`. -/
noncomputable def pushforwardStageIso (q : X ⟶ Y) :
    ((f₀ ≫ q)_*[ModuleCat.{u + 1} Λ]).obj (((𝟙 Z)^*[ModuleCat.{u + 1} Λ]).obj J) ≅
      ((q)_*[ModuleCat.{u + 1} Λ]).obj (((f₀)_*[ModuleCat.{u + 1} Λ]).obj J) :=
  ((f₀ ≫ q)_*[ModuleCat.{u + 1} Λ]).mapIso ((Etale.upperStarId _ Z).app J) ≪≫
    ((Etale.lowerStarComp _ f₀ q (f₀ ≫ q) rfl).app J).symm

/-- `(𝟙 X)^* f₀_* (𝟙 Z)^* J ≅ f₀_* J`. -/
noncomputable def pushforwardStagePtIso :
    ((𝟙 X)^*[ModuleCat.{u + 1} Λ]).obj
        (((f₀)_*[ModuleCat.{u + 1} Λ]).obj (((𝟙 Z)^*[ModuleCat.{u + 1} Λ]).obj J)) ≅
      ((f₀)_*[ModuleCat.{u + 1} Λ]).obj J :=
  (Etale.upperStarId _ X).app _ ≪≫ ((f₀)_*[ModuleCat.{u + 1} Λ]).mapIso
    ((Etale.upperStarId _ Z).app J)

/-- The underived transition map of the projection `(Z, X, f₀, 𝟙, 𝟙) ⟶ (Z, Y, f₀ ≫ q, q, 𝟙)`
is the counit `q^* q_* (f₀_* J) ⟶ f₀_* J`. -/
lemma sheafTransition_pushforwardStage_proj (q : X ⟶ Y) :
    (LimitStage.sheafTransition Λ (⟨𝟙 Z, q, by simp, by simp, by simp⟩ :
        LimitStage.Hom (⟨Z, X, f₀, 𝟙 X, 𝟙 Z⟩ : LimitStage X Z) ⟨Z, Y, f₀ ≫ q, q, 𝟙 Z⟩)).app J ≫
      (pushforwardStagePtIso Λ f₀ J).hom =
    ((q)^*[ModuleCat.{u + 1} Λ]).map (pushforwardStageIso Λ f₀ J q).hom ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).counit.app
        (((f₀)_*[ModuleCat.{u + 1} Λ]).obj J) := by
  have h1 : (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (𝟙 X) q q (by simp)).hom.app
      (((f₀ ≫ q)_*[ModuleCat.{u + 1} Λ]).obj (((𝟙 Z)^*[ModuleCat.{u + 1} Λ]).obj J)) =
      (Etale.upperStarId (ModuleCat.{u + 1} Λ) X).inv.app (((q)^*[ModuleCat.{u + 1} Λ]).obj
        (((f₀ ≫ q)_*[ModuleCat.{u + 1} Λ]).obj (((𝟙 Z)^*[ModuleCat.{u + 1} Λ]).obj J))) := by
    rw [Etale.upperStarComp_id_left]
    simp
  have h2 : (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (𝟙 Z) (𝟙 Z) (𝟙 Z) (by simp)).inv.app J =
      (Etale.upperStarId (ModuleCat.{u + 1} Λ) Z).hom.app
        (((𝟙 Z)^*[ModuleCat.{u + 1} Λ]).obj J) := by
    rw [Etale.upperStarComp_id_left]
    simp
  have n := (Etale.upperStarId (ModuleCat.{u + 1} Λ) X).hom.naturality
    ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ)
        (⟨by simp⟩ : CommSq (𝟙 Z) f₀ (f₀ ≫ q) q)).app (((𝟙 Z)^*[ModuleCat.{u + 1} Λ]).obj J) ≫
      ((f₀)_*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarId (ModuleCat.{u + 1} Λ) Z).hom.app
          (((𝟙 Z)^*[ModuleCat.{u + 1} Λ]).obj J)))
  simp only [Functor.id_map] at n
  rw [LimitStage.sheafTransition_app]
  simp only [pushforwardStagePtIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, h1, h2,
    Category.assoc]
  rw [reassoc_of% n, Iso.inv_hom_id_app_assoc]
  erw [← Adjunction.homEquiv_counit]
  refine (Equiv.eq_symm_apply _).mpr ?_
  erw [Adjunction.homEquiv_unit]
  simp only [Functor.map_comp]
  rw [reassoc_of% (Etale.unit_map_baseChangeMap_app (ModuleCat.{u + 1} Λ)
    (⟨by simp⟩ : CommSq (𝟙 Z) f₀ (f₀ ≫ q) q) (((𝟙 Z)^*[ModuleCat.{u + 1} Λ]).obj J))]
  simp only [Etale.squareLowerStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  rw [reassoc_of% (lowerStarComp_hom_inv_app_congr (ModuleCat.{u + 1} Λ) (𝟙 Z) (f₀ ≫ q) f₀ q
    (𝟙 Z ≫ f₀ ≫ q) (f₀ ≫ q) (Category.id_comp _) (by simp) (by simp) _),
    Etale.lowerStarComp_id_left]
  have n4 := (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) f₀ q (f₀ ≫ q) rfl).inv.naturality
    ((Etale.upperStarId (ModuleCat.{u + 1} Λ) Z).hom.app (((𝟙 Z)^*[ModuleCat.{u + 1} Λ]).obj J) ≫
      (Etale.upperStarId (ModuleCat.{u + 1} Λ) Z).hom.app J)
  simp only [Functor.comp_map, Functor.map_comp] at n4
  have k1 := Etale.upperStarId_hom_app_unit_app (ModuleCat.{u + 1} Λ) Z
    (((𝟙 Z)^*[ModuleCat.{u + 1} Λ]).obj J)
  have k2 := (Etale.lowerStarId (ModuleCat.{u + 1} Λ) Z).hom.naturality
    ((Etale.upperStarId (ModuleCat.{u + 1} Λ) Z).hom.app (((𝟙 Z)^*[ModuleCat.{u + 1} Λ]).obj J))
  simp only [Functor.id_map] at k2
  have key : (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 Z)).unit.app
        (((𝟙 Z)^*[ModuleCat.{u + 1} Λ]).obj J) ≫
      (Etale.lowerStarId (ModuleCat.{u + 1} Λ) Z).hom.app _ ≫
      (Etale.upperStarId (ModuleCat.{u + 1} Λ) Z).hom.app
        (((𝟙 Z)^*[ModuleCat.{u + 1} Λ]).obj J) = 𝟙 _ := by
    rw [← k2, reassoc_of% k1]
    exact Iso.inv_hom_id_app _ _
  have key' := congrArg ((f₀ ≫ q)_*[ModuleCat.{u + 1} Λ]).map key
  simp only [Functor.map_comp, CategoryTheory.Functor.map_id] at key'
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Category.assoc]
  rw [← n4]
  erw [Category.id_comp]
  rw [Category.assoc, reassoc_of% key']
  rfl

/-- The underived transition map of `(Z, Y, f₀ ≫ q, q, 𝟙) ⟶ (Z, Y', f₀ ≫ r, r, 𝟙)` for
`r = q ≫ g` is the transition map `r^* r_* (f₀_* J) ⟶ q^* q_* (f₀_* J)`. -/
lemma pushforwardStageIso_descentTransition (q : X ⟶ Y) {Y' : Scheme.{u}} (g : Y ⟶ Y')
    (r : X ⟶ Y') (hr : r = q ≫ g) :
    ((r)^*[ModuleCat.{u + 1} Λ]).map (pushforwardStageIso Λ f₀ J r).hom ≫
        descentTransition _ q g r hr (((f₀)_*[ModuleCat.{u + 1} Λ]).obj J) =
      (LimitStage.sheafTransition Λ (⟨𝟙 Z, g, by simp [hr], hr.symm, by simp⟩ :
        LimitStage.Hom (⟨Z, Y, f₀ ≫ q, q, 𝟙 Z⟩ : LimitStage X Z)
          ⟨Z, Y', f₀ ≫ r, r, 𝟙 Z⟩)).app J ≫
        ((q)^*[ModuleCat.{u + 1} Λ]).map (pushforwardStageIso Λ f₀ J q).hom := by
  have hq := sheafTransition_pushforwardStage_proj Λ f₀ J q
  have hr' := sheafTransition_pushforwardStage_proj Λ f₀ J r
  have hc := LimitStage.sheafTransition_comp_app Λ
    (⟨𝟙 Z, q, by simp, by simp, by simp⟩ :
      LimitStage.Hom (⟨Z, X, f₀, 𝟙 X, 𝟙 Z⟩ : LimitStage X Z) ⟨Z, Y, f₀ ≫ q, q, 𝟙 Z⟩)
    (⟨𝟙 Z, g, by simp [hr], hr.symm, by simp⟩ :
      LimitStage.Hom (⟨Z, Y, f₀ ≫ q, q, 𝟙 Z⟩ : LimitStage X Z) ⟨Z, Y', f₀ ≫ r, r, 𝟙 Z⟩) J
  rw [show LimitStage.Hom.comp _ _ = (⟨𝟙 Z, r, by simp, by simp, by simp⟩ :
      LimitStage.Hom (⟨Z, X, f₀, 𝟙 X, 𝟙 Z⟩ : LimitStage X Z) ⟨Z, Y', f₀ ≫ r, r, 𝟙 Z⟩) from
    LimitStage.Hom.ext (by simp) hr.symm] at hc
  have hL : ((r)^*[ModuleCat.{u + 1} Λ]).map (pushforwardStageIso Λ f₀ J r).hom ≫
      descentTransition _ q g r hr (((f₀)_*[ModuleCat.{u + 1} Λ]).obj J) =
      (Etale.upperStarComp (ModuleCat.{u + 1} Λ) q g r hr).hom.app
          (((f₀ ≫ r)_*[ModuleCat.{u + 1} Λ]).obj (((𝟙 Z)^*[ModuleCat.{u + 1} Λ]).obj J)) ≫
        ((q)^*[ModuleCat.{u + 1} Λ]).map
          (((g)^*[ModuleCat.{u + 1} Λ]).map (pushforwardStageIso Λ f₀ J r).hom ≫
            ((g)^*[ModuleCat.{u + 1} Λ]).map ((lowerStarComp (ModuleCat.{u + 1} Λ) q g r hr).inv.app
              (((f₀)_*[ModuleCat.{u + 1} Λ]).obj J)) ≫
            (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).counit.app
              (((q)_*[ModuleCat.{u + 1} Λ]).obj (((f₀)_*[ModuleCat.{u + 1} Λ]).obj J))) := by
    have nn := (Etale.upperStarComp (ModuleCat.{u + 1} Λ) q g r hr).hom.naturality
      (pushforwardStageIso Λ f₀ J r).hom
    simp only [Functor.comp_map] at nn
    rw [descentTransition_eq_upperStarComp, reassoc_of% nn]
    simp only [Functor.map_comp]
  have hR : (LimitStage.sheafTransition Λ (⟨𝟙 Z, g, by simp [hr], hr.symm, by simp⟩ :
      LimitStage.Hom (⟨Z, Y, f₀ ≫ q, q, 𝟙 Z⟩ : LimitStage X Z)
        ⟨Z, Y', f₀ ≫ r, r, 𝟙 Z⟩)).app J ≫
      ((q)^*[ModuleCat.{u + 1} Λ]).map (pushforwardStageIso Λ f₀ J q).hom =
      (Etale.upperStarComp (ModuleCat.{u + 1} Λ) q g r hr).hom.app
          (((f₀ ≫ r)_*[ModuleCat.{u + 1} Λ]).obj (((𝟙 Z)^*[ModuleCat.{u + 1} Λ]).obj J)) ≫
        ((q)^*[ModuleCat.{u + 1} Λ]).map
          ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ)
              (⟨by simp [hr]⟩ : CommSq (𝟙 Z) (f₀ ≫ q) (f₀ ≫ r) g)).app
              (((𝟙 Z)^*[ModuleCat.{u + 1} Λ]).obj J) ≫
            ((f₀ ≫ q)_*[ModuleCat.{u + 1} Λ]).map
              ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (𝟙 Z) (𝟙 Z) (𝟙 Z) (by simp)).inv.app J) ≫
            (pushforwardStageIso Λ f₀ J q).hom) := by
    rw [LimitStage.sheafTransition_app]
    simp only [Functor.map_comp, Category.assoc]
  rw [hL, hR]
  congr 2
  apply eq_of_upperStar_map_comp_counit
  rw [← cancel_epi ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) q g r hr).hom.app
    (((f₀ ≫ r)_*[ModuleCat.{u + 1} Λ]).obj (((𝟙 Z)^*[ModuleCat.{u + 1} Λ]).obj J)))]
  rw [← reassoc_of% hL, ← reassoc_of% hR, descentTransition_counit, ← hr',
    ← hq, reassoc_of% hc]

end Pushforward

end AlgebraicGeometry.Etale

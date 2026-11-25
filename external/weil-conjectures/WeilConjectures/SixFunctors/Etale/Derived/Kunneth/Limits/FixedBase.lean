/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.StageAlgebra
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.TransitionMono

/-!
# Higher direct images along a limit over a fixed base, as a system of stages

The fixed-base limit theorem `AlgebraicGeometry.Etale.higherDirectImage_limit` (Stacks 09Z1),
for a cofiltered system `D` of schemes over `W` mapping to `S` through `k : W ⟶ S`, pulled back
along any `p : X ⟶ S`, written in the language of systems of stages
(`AlgebraicGeometry.Etale.isStalkColimit_fixedBaseSystem`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Identity

variable {S T : Scheme.{u}}

/-- The transition map `AlgebraicGeometry.Etale.overLowerStarTransition` along an identity is the
identity. -/
lemma overLowerStarTransition_id (g : T ⟶ S) {T₁ : Scheme.{u}} (π : T₁ ⟶ T) (ρ : T₁ ⟶ T₁)
    (hρ : ρ = 𝟙 T₁) (h : ρ ≫ π = π)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.overLowerStarTransition Λ g π π ρ h K = 𝟙 _ := by
  subst hρ
  have hbc : (Etale.baseChange (ModuleCat.{u + 1} Λ)
      (⟨by simp⟩ : CommSq (𝟙 T₁) (π ≫ g) (π ≫ g) (𝟙 S))).app
        (D+((π)^*[ModuleCat.{u + 1} Λ]).obj K) =
      (upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) S).hom.app
          (R+((π ≫ g)_*[ModuleCat.{u + 1} Λ]).obj (D+((π)^*[ModuleCat.{u + 1} Λ]).obj K)) ≫
        R+((π ≫ g)_*[ModuleCat.{u + 1} Λ]).map
          ((upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) T₁).inv.app
            (D+((π)^*[ModuleCat.{u + 1} Λ]).obj K)) := by
    rw [Etale.baseChange_eq_derivedBaseChangeMapPlus, Etale.derivedBaseChangeMapPlus_id]
    simp
  rw [Etale.overLowerStarTransition, Etale.lowerStarPlusTransition_eq_baseChange Λ (𝟙 T₁)
    (π ≫ g) (π ≫ g) (by simp) ⟨by simp⟩, hbc]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp, Etale.upperStarCompDerivedPlus_id_left_inv_app,
    CategoryTheory.Functor.map_id]

/-- The transition map `AlgebraicGeometry.Etale.higherDirectImageOverMap` along an identity is
the identity. -/
lemma higherDirectImageOverMap_id (g : T ⟶ S)
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (U : Over T) :
    Etale.higherDirectImageOverMap Λ g G q (𝟙 U) = 𝟙 _ := by
  have h := Etale.homologyFunctor_map_overLowerStarTransition Λ g G q (𝟙 U)
  rw [overLowerStarTransition_id Λ g U.hom _ (Over.id_left U), CategoryTheory.Functor.map_id,
    Category.id_comp] at h
  exact (cancel_epi _).1 (h.symm.trans (Category.comp_id _).symm)

end Identity

section FixedBase

variable {W S : Scheme.{u}} (k : W ⟶ S) (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  (q : ℤ) {I : Type u} [Category.{u} I] (D : I ⥤ Over W) (c : Cone D)

/-- The diagram `i ↦ R^q(Dᵢ ⟶ S)_*(G|_{Dᵢ})` of sheaves on `S`. -/
@[simps]
noncomputable def fixedBaseDiagram : Iᵒᵖ ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj i := Etale.higherDirectImage Λ ((D.obj i.unop).hom ≫ k) q
    (((D.obj i.unop).hom)^*[ModuleCat.{u + 1} Λ].obj G)
  map f := Etale.higherDirectImageOverMap Λ k G q (D.map f.unop)
  map_id i := by
    rw [unop_id, D.map_id]
    exact higherDirectImageOverMap_id Λ k G q _
  map_comp f g := by
    rw [unop_comp, D.map_comp]
    exact Etale.higherDirectImageOverMap_comp Λ k G q _ _

/-- The cocone of transition maps to `R^q(c.pt ⟶ S)_*(G|_{c.pt})`. -/
@[simps]
noncomputable def fixedBaseCocone : Cocone (fixedBaseDiagram Λ k G q D) where
  pt := Etale.higherDirectImage Λ (c.pt.hom ≫ k) q ((c.pt.hom)^*[ModuleCat.{u + 1} Λ].obj G)
  ι :=
    { app i := Etale.higherDirectImageOverMap Λ k G q (c.π.app i.unop)
      naturality i j f := by
        simp only [fixedBaseDiagram_map, Functor.const_obj_obj, Functor.const_obj_map,
          Category.comp_id]
        rw [← Etale.higherDirectImageOverMap_comp, c.w] }

/-- The fixed-base limit theorem (Stacks 09Z1) as a colimit of sheaves. -/
noncomputable def isColimitFixedBaseCocone [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)] [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (hc : IsLimit ((Over.forget W).mapCone c)) [QuasiCompact (c.pt.hom ≫ k)]
    [QuasiSeparated (c.pt.hom ≫ k)] :
    IsColimit (fixedBaseCocone Λ k G q D c) :=
  isColimitOfIsElementwiseColimit _ fun s ↦
    ⟨(Etale.higherDirectImage_limit Λ k G D c hc q s).1,
      (Etale.higherDirectImage_limit Λ k G D c hc q s).2⟩

variable {X : Scheme.{u}} (p : X ⟶ S)

/-- The stage `(V, S, V ⟶ W ⟶ S, p, V ⟶ W)` over `X` attached to a scheme `V` over `W`. -/
abbrev fixedBaseStage (V : Over W) : LimitStage X W := ⟨V.left, S, V.hom ≫ k, p, V.hom⟩

/-- The morphism of stages attached to a morphism of schemes over `W`. -/
abbrev fixedBaseHom {U V : Over W} (φ : U ⟶ V) :
    LimitStage.Hom (fixedBaseStage k p U) (fixedBaseStage k p V) :=
  ⟨φ.left, 𝟙 S, by rw [Category.comp_id, ← Category.assoc, Over.w], by simp, Over.w φ⟩

/-- Over a fixed base, the transition maps of stages are the pullbacks of the transition maps
`AlgebraicGeometry.Etale.overLowerStarTransition`. -/
lemma transition_fixedBaseHom {U V : Over W} (φ : U ⟶ V)
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (LimitStage.transition Λ (fixedBaseHom k p φ)).app K =
      D+((p)^*[ModuleCat.{u + 1} Λ]).map
        (Etale.overLowerStarTransition Λ k V.hom U.hom φ.left (Over.w φ) K) := by
  have h1 := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_id_right (ModuleCat.{u + 1} Λ)
    p) (R+((V.hom ≫ k)_*[ModuleCat.{u + 1} Λ]).obj (D+((V.hom)^*[ModuleCat.{u + 1} Λ]).obj K))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_inv_app] at h1
  have h1' : (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) p (𝟙 S) p
      (Category.comp_id p).symm).hom.app
        (R+((V.hom ≫ k)_*[ModuleCat.{u + 1} Λ]).obj (D+((V.hom)^*[ModuleCat.{u + 1} Λ]).obj K)) =
      D+((p)^*[ModuleCat.{u + 1} Λ]).map ((upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) S).inv.app
        (R+((V.hom ≫ k)_*[ModuleCat.{u + 1} Λ]).obj
          (D+((V.hom)^*[ModuleCat.{u + 1} Λ]).obj K))) := by
    rw [← cancel_mono (D+((p)^*[ModuleCat.{u + 1} Λ]).map
      ((upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) S).hom.app _)), ← Functor.map_comp,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    exact h1
  rw [LimitStage.transition_app, Etale.overLowerStarTransition,
    Etale.lowerStarPlusTransition_eq_baseChange Λ φ.left (V.hom ≫ k) (U.hom ≫ k)
      (by rw [← Category.assoc, Over.w]) ⟨(fixedBaseHom k p φ).wg⟩]
  erw [h1']
  simp only [Functor.map_comp, Category.assoc]

/-- The fixed-base system of stages over `X`. -/
@[simps]
noncomputable def fixedBaseSystem : LimitStageSystem X W I where
  obj i := fixedBaseStage k p (D.obj i)
  map f := fixedBaseHom k p (D.map f)
  map_id i := LimitStage.Hom.ext (by simp) rfl
  map_comp f g := LimitStage.Hom.ext (by simp) (by simp)
  pt := fixedBaseStage k p c.pt
  π i := fixedBaseHom k p (c.π.app i)
  w f := LimitStage.Hom.ext (by simp [← Over.comp_left]) (by simp)

lemma fixedBaseSystem_π_eq (i : I) :
    (fixedBaseSystem (k := k) (p := p) (D := D) (c := c)).π i = fixedBaseHom k p (c.π.app i) :=
  rfl

lemma fixedBaseSystem_map_eq {i j : I} (f : i ⟶ j) :
    (fixedBaseSystem (k := k) (p := p) (D := D) (c := c)).map f = fixedBaseHom k p (D.map f) :=
  rfl

/-- **The fixed-base limit theorem, pulled back along `p : X ⟶ S`, as a system of stages.** -/
theorem isStalkColimit_fixedBaseSystem [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)] [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (hc : IsLimit ((Over.forget W).mapCone c)) [QuasiCompact (c.pt.hom ≫ k)]
    [QuasiSeparated (c.pt.hom ≫ k)] :
    (fixedBaseSystem (k := k) (p := p) (D := D) (c := c)).IsStalkColimit Λ
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G) q := by
  have hcol := isColimitOfPreserves ((p)^*[ModuleCat.{u + 1} Λ])
    (isColimitFixedBaseCocone Λ k G q D c hc)
  intro x
  refine ModuleCat.IsElementwiseColimit.of_iso
    (fun i ↦ (X.uliftPointSmallEtale x).sheafFiber.mapIso
      (Etale.sourceStageIso Λ p k G q (D.obj i)))
    ((X.uliftPointSmallEtale x).sheafFiber.mapIso (Etale.sourceStageIso Λ p k G q c.pt))
    (fun i ↦ ?_) (fun f ↦ ?_) (isElementwiseColimit_sheafFiber_of_isColimit hcol x)
  · simp only [Functor.mapIso_hom, fixedBaseSystem_π_eq,
      stalkHomology, Functor.comp_map, transition_fixedBaseHom, Functor.mapCocone_ι_app,
      fixedBaseCocone_ι_app]
    exact (Etale.sheafFiber_map_sourceStageIso_naturality Λ p k G q (c.π.app i) x).symm
  · simp only [Functor.mapIso_hom, fixedBaseSystem_map_eq, stalkHomology,
      Functor.comp_map, transition_fixedBaseHom, fixedBaseDiagram_map,
      Quiver.Hom.unop_op]
    exact (Etale.sheafFiber_map_sourceStageIso_naturality Λ p k G q (D.map f) x).symm

end FixedBase

end AlgebraicGeometry.Etale

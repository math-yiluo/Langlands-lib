/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ExtendScalars

/-!
# Extension of scalars and composition of pullbacks

The identifications `f^*(Λ ⊗ F) ≅ Λ ⊗ f^* F` of `AlgebraicGeometry.Etale.upperStarExtendScalarsIso`
are compatible with the composition isomorphisms of pullbacks
(`AlgebraicGeometry.Etale.upperStarExtendScalarsIso_comp`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)

/-- The unit of `Adjunction.ofNatIsoRight`. -/
private lemma ofNatIsoRight_unit_app {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D}
    {G H : D ⥤ C} (adj : F ⊣ G) (e : G ≅ H) (x : C) :
    (adj.ofNatIsoRight e).unit.app x = adj.unit.app x ≫ e.hom.app _ := by
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]

/-- The identification `f^*(Λ ⊗ F) ≅ Λ ⊗ f^* F` through the units of the adjunctions. -/
private lemma unit_app_upperStarExtendScalarsIso {S T : Scheme.{u}} (f : S ⟶ T)
    (x : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (extendScalarsAdjunction Λ T).unit.app x ≫
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        ((upperStarLowerStarAdjunction _ f).unit.app ((extendScalars Λ T).obj x) ≫
          (f)_*[ModuleCat.{u + 1} Λ].map ((upperStarExtendScalarsIso Λ f).hom.app x)) =
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app x ≫
      (f)_*[AddCommGrpCat.{u + 1}].map
        ((extendScalarsAdjunction Λ S).unit.app ((f)^*[AddCommGrpCat.{u + 1}].obj x)) := by
  have := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((extendScalarsAdjunction Λ T).comp (upperStarLowerStarAdjunction _ f))
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).comp
      (extendScalarsAdjunction Λ S)).ofNatIsoRight
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))) x
  rw [Adjunction.homEquiv_unit, ofNatIsoRight_unit_app] at this
  simpa [upperStarExtendScalarsIso, Adjunction.comp_unit_app] using this

/-- Forgetting the `Λ`-module structure commutes with the composition isomorphisms of the
pushforwards. -/
private lemma sheafCompose_map_lowerStarComp_hom_app {S T : Scheme.{u}} (f : X ⟶ S) (f' : S ⟶ T)
    (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        ((lowerStarComp (ModuleCat.{u + 1} Λ) f f').hom.app N) =
      (lowerStarComp AddCommGrpCat.{u + 1} f f').hom.app
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj N) := by
  rfl

private lemma sheafCompose_map_lowerStar_map {S T : Scheme.{u}} (f : S ⟶ T)
    {N N' : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : N ⟶ N') :
    (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        ((f)_*[ModuleCat.{u + 1} Λ].map φ) =
      (f)_*[AddCommGrpCat.{u + 1}].map
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map φ) :=
  rfl

/-- The identifications `f^*(Λ ⊗ F) ≅ Λ ⊗ f^* F` are compatible with composition: for `g` and
`h`, the identification for `g ≫ h` is
`(g ≫ h)^*(Λ ⊗ F) ≅ g^* h^*(Λ ⊗ F) ≅ g^*(Λ ⊗ h^* F) ≅ Λ ⊗ g^* h^* F ≅ Λ ⊗ (g ≫ h)^* F`. -/
lemma upperStarExtendScalarsIso_comp (M : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStarComp _ g h).hom.app ((extendScalars Λ Z).obj M) ≫
        (g)^*[ModuleCat.{u + 1} Λ].map ((upperStarExtendScalarsIso Λ h).hom.app M) ≫
          (upperStarExtendScalarsIso Λ g).hom.app ((h)^*[AddCommGrpCat.{u + 1}].obj M) =
      (upperStarExtendScalarsIso Λ (g ≫ h)).hom.app M ≫
        (extendScalars Λ X).map ((upperStarComp _ g h).hom.app M) := by
  have h1 : (upperStarLowerStarAdjunction _ (g ≫ h)).unit.app ((extendScalars Λ Z).obj M) ≫
      (g ≫ h)_*[ModuleCat.{u + 1} Λ].map
        ((upperStarComp _ g h).hom.app ((extendScalars Λ Z).obj M) ≫
          (g)^*[ModuleCat.{u + 1} Λ].map ((upperStarExtendScalarsIso Λ h).hom.app M) ≫
            (upperStarExtendScalarsIso Λ g).hom.app ((h)^*[AddCommGrpCat.{u + 1}].obj M)) =
      ((upperStarLowerStarAdjunction _ h).unit.app ((extendScalars Λ Z).obj M) ≫
        (h)_*[ModuleCat.{u + 1} Λ].map ((upperStarExtendScalarsIso Λ h).hom.app M)) ≫
        (h)_*[ModuleCat.{u + 1} Λ].map ((upperStarLowerStarAdjunction _ g).unit.app _ ≫
            (g)_*[ModuleCat.{u + 1} Λ].map
              ((upperStarExtendScalarsIso Λ g).hom.app ((h)^*[AddCommGrpCat.{u + 1}].obj M))) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) g h).hom.app _ := by
    rw [Functor.map_comp, reassoc_of% (upperStarComp_hom_app_unit_app (ModuleCat.{u + 1} Λ) g h
      ((extendScalars Λ Z).obj M)), ← (lowerStarComp (ModuleCat.{u + 1} Λ) g h).hom.naturality]
    have hn := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.naturality
      ((upperStarExtendScalarsIso Λ h).hom.app M)
    simp only [Adjunction.comp_unit_app, Functor.comp_map, Functor.map_comp, Category.assoc] at hn ⊢
    simp only [← Functor.map_comp_assoc (h)_*[ModuleCat.{u + 1} Λ]]
    rw [← reassoc_of% hn]
  have h2 : (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (g ≫ h)).unit.app M ≫
      (g ≫ h)_*[AddCommGrpCat.{u + 1}].map
        ((extendScalarsAdjunction Λ X).unit.app ((g ≫ h)^*[AddCommGrpCat.{u + 1}].obj M) ≫
          (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
            ((extendScalars Λ X).map ((upperStarComp _ g h).hom.app M))) =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit.app M ≫
        (h)_*[AddCommGrpCat.{u + 1}].map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app _ ≫
            (g)_*[AddCommGrpCat.{u + 1}].map ((extendScalarsAdjunction Λ X).unit.app _)) ≫
        (lowerStarComp AddCommGrpCat.{u + 1} g h).hom.app _ := by
    have hn := (extendScalarsAdjunction Λ X).unit.naturality
      ((upperStarComp AddCommGrpCat.{u + 1} g h).hom.app M)
    simp only [Functor.id_map, Functor.comp_map] at hn
    rw [← hn, Functor.map_comp, reassoc_of% (upperStarComp_hom_app_unit_app AddCommGrpCat.{u + 1}
      g h M), ← (lowerStarComp AddCommGrpCat.{u + 1} g h).hom.naturality]
    simp only [Adjunction.comp_unit_app, Functor.comp_map, Functor.map_comp, Category.assoc]
    rfl
  apply (((extendScalarsAdjunction Λ Z).comp
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (g ≫ h))).homEquiv _ _).injective
  conv_rhs => rw [Adjunction.homEquiv_naturality_right, upperStarExtendScalarsIso,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [Adjunction.homEquiv_unit, ofNatIsoRight_unit_app, Adjunction.comp_unit_app,
    Adjunction.comp_unit_app]
  simp only [NatIso.ofComponents_hom_app, Iso.refl_hom, Functor.comp_map, Category.assoc]
  rw [← Functor.map_comp, h1, Functor.map_comp, ← Category.assoc,
    unit_app_upperStarExtendScalarsIso, Functor.map_comp, sheafCompose_map_lowerStarComp_hom_app,
    sheafCompose_map_lowerStar_map, Category.assoc, ← Functor.map_comp_assoc,
    unit_app_upperStarExtendScalarsIso]
  refine h2.symm.trans ?_
  simp only [Functor.map_comp]
  rfl

/-- Pulling back along `f : X ⟶ Y` the map `π_Y^* W ⟶ Λ ⊗ B_Y` induced by `ρ : W ⟶ Λ ⊗ B_S` and
`c_Y : π_Y^* B_S ⟶ B_Y`, and composing with `c_f : f^* B_Y ⟶ B_X`, gives the map induced by `ρ` and
`c_X : π_X^* B_S ⟶ B_X`, provided `c_X` is the composite of `c_Y` and `c_f`. -/
lemma upperStarComp_hom_app_comp_upperStar_map_extendScalars {S : Scheme.{u}} (f : X ⟶ Y)
    (πY : Y ⟶ S) (πX : X ⟶ S) (hπ : πX = f ≫ πY)
    {BS : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {BY : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {BX : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (cY : (πY)^*[AddCommGrpCat.{u + 1}].obj BS ⟶ BY)
    (cX : (πX)^*[AddCommGrpCat.{u + 1}].obj BS ⟶ BX)
    (cf : (f)^*[AddCommGrpCat.{u + 1}].obj BY ⟶ BX)
    (hc : (upperStarComp _ f πY πX hπ).hom.app BS ≫ (f)^*[AddCommGrpCat.{u + 1}].map cY ≫ cf = cX)
    {W : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (ρ : W ⟶ (extendScalars Λ S).obj BS) :
    (upperStarComp _ f πY πX hπ).hom.app W ≫
        (f)^*[ModuleCat.{u + 1} Λ].map ((πY)^*[ModuleCat.{u + 1} Λ].map ρ ≫
          (upperStarExtendScalarsIso Λ πY).hom.app BS ≫ (extendScalars Λ Y).map cY) ≫
        (upperStarExtendScalarsIso Λ f).hom.app BY ≫ (extendScalars Λ X).map cf =
      (πX)^*[ModuleCat.{u + 1} Λ].map ρ ≫ (upperStarExtendScalarsIso Λ πX).hom.app BS ≫
        (extendScalars Λ X).map cX := by
  subst hπ hc
  have n1 := (upperStarComp (ModuleCat.{u + 1} Λ) f πY).hom.naturality ρ
  have n2 := (upperStarExtendScalarsIso Λ f).hom.naturality cY
  simp only [Functor.comp_map, Functor.comp_obj] at n1 n2
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% n1, reassoc_of% n2, reassoc_of% (upperStarExtendScalarsIso_comp Λ f πY BS)]

end AlgebraicGeometry.Etale

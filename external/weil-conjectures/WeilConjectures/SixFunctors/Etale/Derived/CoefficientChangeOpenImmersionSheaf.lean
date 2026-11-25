/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeStalk

/-!
# Restriction of scalars and the base change of the extension by zero, on sheaves

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings. For a commutative square
`g' ≫ j = j' ≫ g''` of schemes with `j`, `j'` open immersions, the base change map
`AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChangeMap : g'^* ⋙ j'_! ⟶ j_! ⋙ g''^*`
of étale sheaves is compatible with restriction of scalars along `ρ`, through the comparisons
`AlgebraicGeometry.Etale.upperStarRestrictScalarsIso` of the pullbacks and
`AlgebraicGeometry.Etale.openImmersionLowerShriekRestrictScalarsIso` of the extensions by zero
(`AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChangeMap_app_restrictScalars`).

Both sides are compared through their transposes under `j'_! ⊣ j'^*`. The comparison of the
extensions by zero is the transpose of the restriction of scalars of the unit of `j_! ⊣ j^*`
(`AlgebraicGeometry.Etale.openImmersionLowerShriekUpperStarAdjunction_unit_app_comp_upperStarMap`),
and the comparison of the pullbacks is compatible with the square isomorphisms of pullbacks
(`AlgebraicGeometry.Etale.upperStarRestrictScalarsIso_hom_app_comp_squareUpperStarIso`).

This is the underived input of the compatibility of the derived base change of the extension by
zero with the coefficient comparisons, used for the compatible systems of Frobenius coefficient
morphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

section Abstract

variable {𝒞 : Type*} [Category 𝒞]

/-- A diagram chase: rewriting a composite along a naturality square and two equations. -/
private lemma comp_comp_comp_eq_of_eq {A B B' C C' D : 𝒞} {a : A ⟶ B} {b : B ⟶ B'}
    {f : B' ⟶ C'} {g : C' ⟶ D} {c : B ⟶ C} {d : C ⟶ C'} {x : A ⟶ C} {y : C ⟶ D}
    (hnat : c ≫ d = b ≫ f) (hx : a ≫ c = x) (hy : d ≫ g = y) : a ≫ b ≫ f ≫ g = x ≫ y := by
  rw [← reassoc_of% hnat, reassoc_of% hx, hy]

end Abstract

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The unit of `j^* ⊣ j_*` along an open immersion commutes with restriction of scalars. -/
lemma restrictScalars_map_openImmersionRestrictionLowerStarAdjunction_unit_app
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (Sheaf.restrictScalars X.smallEtaleTopology ρ).map
        ((openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ') j).unit.app G) =
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj G) := by
  rfl

/-- The comparison `j^* ∘ Res ≅ Res ∘ j^*` of pullbacks along an open immersion is compatible
with the identifications of the pullbacks with the restrictions along `j`. -/
lemma upperStarRestrictScalarsIso_hom_app_comp_upperStarIsoOpenImmersionRestriction
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (upperStarRestrictScalarsIso ρ j).hom.app G ≫
        (Sheaf.restrictScalars U.smallEtaleTopology ρ).map
          ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ') j).hom.app G) =
      (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ) j).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj G) := by
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).homEquiv _ _).injective
  have h₁ : (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).homEquiv _ _
      ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ) j).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj G)) =
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj G) :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _
  have h₂ : (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') j).homEquiv _ _
      ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ') j).hom.app G) =
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ') j).unit.app G :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _
  rw [Adjunction.homEquiv_unit] at h₂
  refine Eq.trans ?_ h₁.symm
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  -- `erw`: `upperStarRestrictScalarsIso` is `asIso` of `upperStarRestrictScalars`
  erw [← restrictScalars_map_unit_app ρ j G]
  rw [← restrictScalars_map_openImmersionRestrictionLowerStarAdjunction_unit_app, ← h₂,
    Functor.map_comp]
  rfl

/-- The unit of `Res ⊣ Coext` commutes with the restriction along an open immersion. -/
lemma restrictCoextendScalarsAdj_unit_app_openImmersionRestriction_obj
    (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (Sheaf.restrictCoextendScalarsAdj U.smallEtaleTopology ρ).unit.app
        ((openImmersionRestriction (ModuleCat.{u + 1} Λ') j).obj N) =
      (openImmersionRestriction (ModuleCat.{u + 1} Λ') j).map
        ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology ρ).unit.app N) := by
  ext V : 3
  rw [restrictCoextendScalarsAdj_unit_app_hom_app]
  rfl

/-- The comparison `j_! ∘ Res ≅ Res ∘ j_!` is the transpose, under `j_! ⊣ j^*`, of the
restriction of scalars of the unit of `j_! ⊣ j^*`. -/
lemma openImmersionLowerShriekAdjunction_unit_app_comp_openImmersionRestrictionMap
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
        ((Sheaf.restrictScalars U.smallEtaleTopology ρ).obj G) ≫
      (openImmersionRestriction (ModuleCat.{u + 1} Λ) j).map
        ((openImmersionLowerShriekRestrictScalarsIso ρ j).hom.app G) =
      (Sheaf.restrictScalars U.smallEtaleTopology ρ).map
        ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ') j).unit.app G) := by
  have h := unit_conjugateEquiv_symm
    ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ') j).comp
      (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology ρ))
    ((Sheaf.restrictCoextendScalarsAdj U.smallEtaleTopology ρ).comp
      (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) j)) (𝟙 _) G
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  apply ((Sheaf.restrictCoextendScalarsAdj U.smallEtaleTopology ρ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp]
  simp only [NatTrans.id_app, Functor.comp_map, Category.assoc] at h
  refine h.symm.trans ?_
  -- `erw`: `Res ∘ j^*` and `j^* ∘ Res` agree only up to unfolding
  erw [Category.comp_id, ← restrictCoextendScalarsAdj_unit_app_openImmersionRestriction_obj]
  exact (Adjunction.unit_naturality _ _).symm

/-- The comparison `j_! ∘ Res ≅ Res ∘ j_!` is the transpose, under `j_! ⊣ j^*` with `j^*` the
pullback, of the restriction of scalars of the unit, up to the comparison `j^* ∘ Res ≅ Res ∘ j^*`
of pullbacks. -/
lemma openImmersionLowerShriekUpperStarAdjunction_unit_app_comp_upperStarMap
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
        ((Sheaf.restrictScalars U.smallEtaleTopology ρ).obj G) ≫
      (j)^*[ModuleCat.{u + 1} Λ].map
        ((openImmersionLowerShriekRestrictScalarsIso ρ j).hom.app G) ≫
      (upperStarRestrictScalarsIso ρ j).hom.app ((j)_!open[ModuleCat.{u + 1} Λ'].obj G) =
      (Sheaf.restrictScalars U.smallEtaleTopology ρ).map
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ') j).unit.app G) := by
  have h₀ : (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ) j).inv.app
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj
          ((j)_!open[ModuleCat.{u + 1} Λ'].obj G)) ≫
      (upperStarRestrictScalarsIso ρ j).hom.app ((j)_!open[ModuleCat.{u + 1} Λ'].obj G) =
      (Sheaf.restrictScalars U.smallEtaleTopology ρ).map
        ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ') j).inv.app
          ((j)_!open[ModuleCat.{u + 1} Λ'].obj G)) :=
    (Iso.inv_comp_eq ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ) j).app
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj
        ((j)_!open[ModuleCat.{u + 1} Λ'].obj G)))).2
      ((Iso.eq_comp_inv ((Sheaf.restrictScalars U.smallEtaleTopology ρ).mapIso
        ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ') j).app
          ((j)_!open[ModuleCat.{u + 1} Λ'].obj G)))).2
        (upperStarRestrictScalarsIso_hom_app_comp_upperStarIsoOpenImmersionRestriction ρ j _))
  have h₁ := (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ) j).inv.naturality
    ((openImmersionLowerShriekRestrictScalarsIso ρ j).hom.app G)
  have h₂ := openImmersionLowerShriekAdjunction_unit_app_comp_openImmersionRestrictionMap ρ j G
  rw [openImmersionLowerShriekUpperStarAdjunction_unit_app,
    openImmersionLowerShriekUpperStarAdjunction_unit_app]
  exact (comp_comp_comp_eq_of_eq h₁ h₂ h₀).trans
    ((Sheaf.restrictScalars U.smallEtaleTopology ρ).map_comp _ _).symm

end OpenImmersion


section Square

/-- Compatibility of `AlgebraicGeometry.Etale.upperStarRestrictScalarsIso` with the composition
isomorphisms `h₁₂^* ≅ h₂^* ⋙ h₁^*` for any `h₁₂ = h₁ ≫ h₂`, componentwise. -/
lemma upperStarRestrictScalarsIso_hom_app_comp_upperStarComp {T S R : Scheme.{u}} (h₁ : T ⟶ S)
    (h₂ : S ⟶ R) (h₁₂ : T ⟶ R) (hh₁₂ : h₁₂ = h₁ ≫ h₂)
    (G : Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (upperStarRestrictScalarsIso ρ h₁₂).hom.app G ≫
        (Sheaf.restrictScalars T.smallEtaleTopology ρ).map
          ((upperStarComp (ModuleCat.{u + 1} Λ') h₁ h₂ h₁₂ hh₁₂).hom.app G) =
      (upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh₁₂).hom.app
          ((Sheaf.restrictScalars R.smallEtaleTopology ρ).obj G) ≫
        (h₁)^*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalarsIso ρ h₂).hom.app G) ≫
        (upperStarRestrictScalarsIso ρ h₁).hom.app ((h₂)^*[ModuleCat.{u + 1} Λ'].obj G) := by
  subst hh₁₂
  simpa using congr_app (upperStarRestrictScalarsIso_comp_hom ρ h₁ h₂) G

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Compatibility of `AlgebraicGeometry.Etale.upperStarRestrictScalarsIso` with the square
isomorphisms `g^* ⋙ f'^* ≅ f^* ⋙ g'^*` of a commutative square, componentwise. -/
lemma upperStarRestrictScalarsIso_hom_app_comp_squareUpperStarIso (sq : CommSq g' f' f g)
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (f')^*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalarsIso ρ g).hom.app G) ≫
        (upperStarRestrictScalarsIso ρ f').hom.app ((g)^*[ModuleCat.{u + 1} Λ'].obj G) ≫
        (Sheaf.restrictScalars X'.smallEtaleTopology ρ).map
          ((squareUpperStarIso (ModuleCat.{u + 1} Λ') sq).hom.app G) =
      (squareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app
          ((Sheaf.restrictScalars Y.smallEtaleTopology ρ).obj G) ≫
        (g')^*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalarsIso ρ f).hom.app G) ≫
        (upperStarRestrictScalarsIso ρ g').hom.app ((f)^*[ModuleCat.{u + 1} Λ'].obj G) := by
  have e₁ := upperStarRestrictScalarsIso_hom_app_comp_upperStarComp ρ f' g (g' ≫ f) sq.w G
  have e₂ := upperStarRestrictScalarsIso_hom_app_comp_upperStarComp ρ g' f (g' ≫ f) rfl G
  simp only [squareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [← cancel_epi ((upperStarComp (ModuleCat.{u + 1} Λ) f' g (g' ≫ f) sq.w).hom.app
    ((Sheaf.restrictScalars Y.smallEtaleTopology ρ).obj G)), Iso.hom_inv_id_app_assoc,
    ← reassoc_of% e₁, ← e₂, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

end Square


section BaseChange

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- **Restriction of scalars and base change for the extension by zero**: for a commutative
square `g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions, the base change map
`g'^* ⋙ j'_! ⟶ j_! ⋙ g''^*` over `Λ` and over `Λ'` are compatible with the comparisons
`AlgebraicGeometry.Etale.upperStarRestrictScalarsIso` and
`AlgebraicGeometry.Etale.openImmersionLowerShriekRestrictScalarsIso`. -/
lemma openImmersionLowerShriekBaseChangeMap_app_restrictScalars (sq : CommSq g' j' j g'')
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (j')_!open[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalarsIso ρ g').hom.app F) ≫
        (openImmersionLowerShriekRestrictScalarsIso ρ j').hom.app
          ((g')^*[ModuleCat.{u + 1} Λ'].obj F) ≫
        (Sheaf.restrictScalars Z'.smallEtaleTopology ρ).map
          ((openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ') sq).app F) =
      (openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app
          ((Sheaf.restrictScalars U.smallEtaleTopology ρ).obj F) ≫
        (g'')^*[ModuleCat.{u + 1} Λ].map
          ((openImmersionLowerShriekRestrictScalarsIso ρ j).hom.app F) ≫
        (upperStarRestrictScalarsIso ρ g'').hom.app ((j)_!open[ModuleCat.{u + 1} Λ'].obj F) := by
  apply ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j').homEquiv _
    _).injective
  rw [← Iso.cancel_iso_hom_right _ _ ((upperStarRestrictScalarsIso ρ j').app
    ((g'')^*[ModuleCat.{u + 1} Λ'].obj ((j)_!open[ModuleCat.{u + 1} Λ'].obj F)))]
  have hs2 := (upperStarRestrictScalarsIso ρ j').hom.naturality
    ((openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ') sq).app F)
  have hs5 := (upperStarRestrictScalarsIso ρ g').hom.naturality
    ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ') j).unit.app F)
  have ht2 := (squareUpperStarIso (ModuleCat.{u + 1} Λ) sq.flip).hom.naturality
    ((openImmersionLowerShriekRestrictScalarsIso ρ j).hom.app F)
  have ht3 := congrArg (g')^*[ModuleCat.{u + 1} Λ].map
    (openImmersionLowerShriekUpperStarAdjunction_unit_app_comp_upperStarMap ρ j F)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hs2 hs5 ht2
  simp only [Functor.map_comp] at ht3
  simp only [Iso.app_hom, Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [hs2, Adjunction.unit_naturality_assoc]
  simp only [Functor.comp_obj]
  rw [reassoc_of% (openImmersionLowerShriekUpperStarAdjunction_unit_app_comp_upperStarMap ρ j'
      ((g')^*[ModuleCat.{u + 1} Λ'].obj F)),
    ← (Sheaf.restrictScalars U'.smallEtaleTopology ρ).map_comp,
    unit_map_openImmersionLowerShriekBaseChangeMap_app,
    (Sheaf.restrictScalars U'.smallEtaleTopology ρ).map_comp, ← reassoc_of% hs5,
    unit_map_openImmersionLowerShriekBaseChangeMap_app_assoc,
    ← reassoc_of% ht2, ← upperStarRestrictScalarsIso_hom_app_comp_squareUpperStarIso,
    reassoc_of% ht3]

end BaseChange

end AlgebraicGeometry.Etale

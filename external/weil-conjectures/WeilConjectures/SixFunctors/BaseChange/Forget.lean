/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget

/-!
# The base change map and the underlying abelian sheaves

For a commutative square of schemes and an étale sheaf `F` of `Λ`-modules, the base change map
`g^* f_* F ⟶ f'_* g'^* F` is an isomorphism if and only if the base change map of the
underlying abelian sheaf of `F` is: up to the comparison isomorphisms
`AlgebraicGeometry.Etale.upperStarForget₂Comparison` the second one is the underlying map of
abelian sheaves of the first one.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The square isomorphism of pushforwards commutes with taking underlying abelian sheaves. -/
lemma squareLowerStarIso_hom_app_sheafCompose_forget₂ (sq : CommSq g' f' f g)
    (H : Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (squareLowerStarIso AddCommGrpCat.{u + 1} sq).hom.app
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj H) =
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        ((squareLowerStarIso (ModuleCat.{u + 1} Λ) sq).hom.app H) := by
  rfl

/-- Pushforward commutes with taking underlying abelian sheaves on the nose. -/
lemma lowerStar_map_sheafCompose_forget₂_map (h : X ⟶ Y)
    {G G' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (x : G ⟶ G') :
    (h)_*[AddCommGrpCat.{u + 1}].map
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map x) =
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        ((h)_*[ModuleCat.{u + 1} Λ].map x) :=
  rfl

/-- The base change map commutes with taking underlying abelian sheaves, up to the comparison
isomorphisms `f^* (forget₂ G) ≅ forget₂ (f^* G)` of
`AlgebraicGeometry.Etale.upperStarForget₂Comparison`. -/
lemma upperStarForget₂Comparison_comp_map_baseChangeMap_app (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    upperStarForget₂Comparison Λ g ((f)_*[ModuleCat.{u + 1} Λ].obj F) ≫
        (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
          ((baseChangeMap (ModuleCat.{u + 1} Λ) sq).app F) =
      (baseChangeMap AddCommGrpCat.{u + 1} sq).app
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) ≫
        (f')_*[AddCommGrpCat.{u + 1}].map (upperStarForget₂Comparison Λ g' F) := by
  apply ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp,
    ← assoc, ← assoc, unit_comp_lowerStar_map_upperStarForget₂Comparison]
  rw [lowerStar_map_sheafCompose_forget₂_map, ← Functor.map_comp, unit_map_baseChangeMap_app]
  erw [unit_map_baseChangeMap_app AddCommGrpCat.{u + 1} sq
    ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)]
  rw [assoc]
  erw [← (squareLowerStarIso AddCommGrpCat.{u + 1} sq).hom.naturality
    (upperStarForget₂Comparison Λ g' F)]
  rw [Functor.comp_map, ← assoc, ← Functor.map_comp,
    unit_comp_lowerStar_map_upperStarForget₂Comparison,
    squareLowerStarIso_hom_app_sheafCompose_forget₂, Functor.map_comp]
  rfl

/-- The base change map of an étale sheaf of `Λ`-modules is an isomorphism if and only if the
base change map of its underlying abelian sheaf is one. -/
theorem isIso_baseChangeMap_app_iff_forget₂ (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((baseChangeMap (ModuleCat.{u + 1} Λ) sq).app F) ↔
      IsIso ((baseChangeMap AddCommGrpCat.{u + 1} sq).app
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)) := by
  rw [← isIso_comp_right_iff _
      ((f')_*[AddCommGrpCat.{u + 1}].map (upperStarForget₂Comparison Λ g' F)),
    ← upperStarForget₂Comparison_comp_map_baseChangeMap_app, isIso_comp_left_iff]
  exact (isIso_iff_of_reflects_iso _ _).symm

end AlgebraicGeometry.Etale

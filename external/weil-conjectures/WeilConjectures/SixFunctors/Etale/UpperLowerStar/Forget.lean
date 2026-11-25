/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

/-!
# Pullback of étale sheaves of modules and their underlying abelian sheaves

For a commutative ring `Λ` and a morphism of schemes `f : X ⟶ Y`, pulling back an étale sheaf of
`Λ`-modules commutes with taking the underlying abelian sheaf. Consequently the pullback map on
global sections `Γ(Y, G) ⟶ Γ(X, f^* G)` is an isomorphism for `G` if and only if it is one for
the underlying abelian sheaf of `G`.
Constant sheaves also commute with taking the underlying abelian sheaf.

## Main definitions and results

- `AlgebraicGeometry.Etale.upperStarForget₂Comparison`: the comparison map
  `f^* (forget₂ G) ⟶ forget₂ (f^* G)`, which is an isomorphism.
- `AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_iff_forget₂`.
- `AlgebraicGeometry.Etale.constantSheafSheafComposeForget₂Iso`: constant sheaves commute with
  forgetting the module structure.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The comparison map `f^* (forget₂ G) ⟶ forget₂ (f^* G)` between the pullback of the
underlying abelian sheaf of an étale sheaf `G` of `Λ`-modules and the underlying abelian sheaf
of its pullback. It is the mate of the equality `f_* ∘ forget₂ = forget₂ ∘ f_*`: it corresponds
under `f^* ⊣ f_*` to `forget₂` of the unit `G ⟶ f_* f^* G`, i.e. it is the unique map making
```
forget₂ G ------η------> f_* f^* (forget₂ G)
     \                          |
      \                    f_* (comparison)
       \                        v
        ----forget₂ η----> f_* (forget₂ (f^* G))
```
commute (`unit_comp_lowerStar_map_upperStarForget₂Comparison`). It is an isomorphism, see
`AlgebraicGeometry.Etale.isIso_upperStarForget₂Comparison`. -/
noncomputable def upperStarForget₂Comparison
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (f)^*[AddCommGrpCat.{u + 1}].obj
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) ⟶
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((f)^*[ModuleCat.{u + 1} Λ].obj G) :=
  ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).symm
    ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app G))

/-- The comparison map `f^* (forget₂ G) ⟶ forget₂ (f^* G)` is compatible with the units of
`f^* ⊣ f_*`. -/
lemma unit_comp_lowerStar_map_upperStarForget₂Comparison
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) ≫
      (f)_*[AddCommGrpCat.{u + 1}].map (upperStarForget₂Comparison Λ f G) =
    (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app G) :=
  ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- The comparison map `f^* (forget₂ G) ⟶ forget₂ (f^* G)` is an isomorphism: for every abelian
sheaf `T` on `X`, precomposition with it is identified with the chain of bijections
`Hom(forget₂ (f^* G), T) ≃ Hom(f^* G, R T) ≃ Hom(G, f_* R T) = Hom(G, R f_* T)
≃ Hom(forget₂ G, f_* T) ≃ Hom(f^* (forget₂ G), T)`, where `R` is the right adjoint of
`forget₂` (coinduction), see `CategoryTheory.Sheaf.forget₂CoinduceAdj`.
(blueprint: `lem-weil-pbc-module-abelian-inverse-image-comparison`) -/
instance isIso_upperStarForget₂Comparison
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (upperStarForget₂Comparison Λ f G) := by
  have key {a : ModuleCat.{u + 1} Λ} {b : AddCommGrpCat.{u + 1}}
      (x : (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj a ⟶ b) :
      (forget₂ _ _).map ((ModuleCat.forget₂CoinduceAdj Λ).unit.app a) ≫
        (forget₂ _ _).map ((ModuleCat.coinduce Λ).map x) ≫
          (ModuleCat.forget₂CoinduceAdj Λ).counit.app b = x := by
    have h := ((ModuleCat.forget₂CoinduceAdj Λ).homEquiv a b).symm_apply_apply x
    rwa [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit, Functor.map_comp_assoc] at h
  rw [isIso_iff_coyoneda_map_bijective]
  intro T
  let adjX := Sheaf.forget₂CoinduceAdj X.smallEtaleTopology Λ
  let adjY := Sheaf.forget₂CoinduceAdj Y.smallEtaleTopology Λ
  let e := (adjX.homEquiv _ T).trans
    (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv G _).trans
      (adjY.homEquiv G ((f)_*[AddCommGrpCat.{u + 1}].obj T)).symm)
  have he (g) : upperStarForget₂Comparison Λ f G ≫ g =
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).symm (e g) := by
    rw [upperStarForget₂Comparison, ← Adjunction.homEquiv_naturality_right_symm]
    congr 1
    apply Sheaf.hom_ext
    ext U : 2
    simp only [e, adjX, adjY, Sheaf.forget₂CoinduceAdj, Equiv.trans_apply,
      Adjunction.homEquiv_unit]
    erw [Adjunction.homEquiv_counit]
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, sheafCompose_map_hom,
      Functor.whiskerRight_app, Functor.map_comp, Category.assoc,
      sheafComposeAdjunction_counit_app_hom, Functor.whiskerLeft_app]
    congr 1
    exact (key _).symm
  have : (fun g ↦ upperStarForget₂Comparison Λ f G ≫ g) =
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).symm ∘ e :=
    funext he
  rw [this]
  exact (Equiv.bijective _).comp e.bijective

/-- The pullback map on global sections of an étale sheaf of `Λ`-modules is an isomorphism if
and only if it is one for the underlying abelian sheaf. -/
theorem isIso_globalSectionsUpperStarMap_iff_forget₂
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) f G) ↔
      IsIso (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)) := by
  simp only [globalSectionsUpperStarMap, isIso_comp_left_iff, ← Category.assoc,
    isIso_comp_right_iff]
  rw [← isIso_comp_right_iff _ (((sheafSections _ _).obj (Opposite.op (⊤_ Y.Etale))).map
      ((f)_*[AddCommGrpCat.{u + 1}].map (upperStarForget₂Comparison Λ f G))), ← Functor.map_comp,
    unit_comp_lowerStar_map_upperStarForget₂Comparison]
  exact (isIso_iff_of_reflects_iso (((sheafSections _ _).obj (Opposite.op (⊤_ Y.Etale))).map
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app G))
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).symm

/-- Constant sheaves commute with forgetting the module structure. -/
noncomputable def constantSheafSheafComposeForget₂Iso :
    constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≅
      forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ⋙
        constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  haveI : Y.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    Sheaf.preservesSheafification_of_adjunction _ (ModuleCat.forget₂CoinduceAdj Λ)
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
    (sheafComposeNatIso Y.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
      (sheafificationAdjunction _ (ModuleCat.{u + 1} Λ))
      (sheafificationAdjunction _ AddCommGrpCat.{u + 1})).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)) _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry.Etale

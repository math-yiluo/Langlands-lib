/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetLaxMonoidal
public import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal

/-!
# Pullbacks of pro-étale sheaves, underlying abelian sheaves and tensor products

For a commutative ring `Λ` and a morphism of schemes `g`, the identification
`AlgebraicGeometry.ProEtale.sheafComposeForget₂CompUpperStarIso : g^* ∘ U ≅ U ∘ g^*` of the
pullbacks of the underlying abelian sheaves `U` of pro-étale sheaves of `Λ`-modules is
compatible with the comonoidal structures `δ` of the pullbacks and the lax monoidal structure
`μ` of `U` (`AlgebraicGeometry.ProEtale.upperStar_map_μ_comp_sheafComposeForget₂CompUpperStarIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- The identification `g^* (U M) ≅ U (g^* M)` of `sheafComposeForget₂CompUpperStarIso` is the
transpose of `U` applied to the unit of `g^* ⊣ g_*`, where `U` takes underlying abelian sheaves
and `g_* (U P) = U (g_* P)`. -/
@[reassoc]
lemma unit_app_comp_lowerStar_map_sheafComposeForget₂CompUpperStarIso_hom_app
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app _ ≫
      (g)_*[AddCommGrpCat.{u + 1}].map ((sheafComposeForget₂CompUpperStarIso Λ g).hom.app M) =
    (sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app M) := by
  have h := unit_conjugateEquiv_symm
    ((upperStarLowerStarAdjunction _ g).comp (sheafComposeAdjunction _ (Adjunction.ofIsLeftAdjoint
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))))
    ((sheafComposeAdjunction _ (Adjunction.ofIsLeftAdjoint
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))).comp
        (upperStarLowerStarAdjunction _ g)) (Iso.refl _).hom M
  have hu : (sheafComposeAdjunction _ (Adjunction.ofIsLeftAdjoint
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))).unit.app
        ((g)_*[ModuleCat.{u + 1} Λ].obj ((g)^*[ModuleCat.{u + 1} Λ].obj M)) =
      (g)_*[ModuleCat.{u + 1} Λ].map ((sheafComposeAdjunction _ (Adjunction.ofIsLeftAdjoint
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))).unit.app
          ((g)^*[ModuleCat.{u + 1} Λ].obj M)) :=
    rfl
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app, Iso.refl_hom, NatTrans.id_app] at h
  erw [Category.comp_id] at h
  rw [← hu, ← Adjunction.unit_naturality, Category.assoc, Functor.comp_map,
    ← Functor.map_comp] at h
  apply ((sheafComposeAdjunction _ (Adjunction.ofIsLeftAdjoint
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact h.symm

/-- The pushforward `g_*` commutes with taking underlying abelian sheaves `U` monoidally: the
tensor maps of `U ∘ g_*` and `g_* ∘ U` agree. -/
@[reassoc]
lemma μ_sheafComposeForget₂_comp_map_lowerStar_μ
    (P Q : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ)) :
    μ (sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
        ((g)_*[ModuleCat.{u + 1} Λ].obj P) ((g)_*[ModuleCat.{u + 1} Λ].obj Q) ≫
      (sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        (μ (g)_*[ModuleCat.{u + 1} Λ] P Q) =
    μ (g)_*[AddCommGrpCat.{u + 1}]
        ((sheafCompose (ProEt.topology Y)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj P)
        ((sheafCompose (ProEt.topology Y)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj Q) ≫
      (g)_*[AddCommGrpCat.{u + 1}].map
        (μ (sheafCompose (ProEt.topology Y)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) P Q) := by
  have h := NatTrans.IsMonoidal.tensor
    (τ := (Functor.sheafPushforwardContinuousCompSheafComposeIso
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) (ProEt.topology X) (ProEt.topology Y)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).hom) P Q
  rw [Functor.LaxMonoidal.comp_μ, Functor.LaxMonoidal.comp_μ] at h
  simp only [Functor.sheafPushforwardContinuousCompSheafComposeIso, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id, Category.id_comp, tensorHom_id, id_whiskerRight] at h
  exact h

/-- The identification `g^* (U M) ≅ U (g^* M)` of `sheafComposeForget₂CompUpperStarIso` is
compatible with the tensor products: the square
```
g^*(U M ⊗ U N) ──g^* μ──▶ g^* U(M ⊗ N) ──≅──▶ U g^*(M ⊗ N) ──U δ──▶ U(g^* M ⊗ g^* N)
      │                                                                  ▲
      δ                                                                  μ
      ▼                                                                  │
g^* U M ⊗ g^* U N ─────────────────≅ ⊗ ≅──────────────────────▶ U g^* M ⊗ U g^* N
```
commutes, where `U` is the underlying abelian sheaf functor, lax monoidal. -/
@[reassoc]
lemma upperStar_map_μ_comp_sheafComposeForget₂CompUpperStarIso
    (M N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    (g)^*[AddCommGrpCat.{u + 1}].map
        (μ (sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
          M N) ≫
      (sheafComposeForget₂CompUpperStarIso Λ g).hom.app (M ⊗ N) ≫
      (sheafCompose (ProEt.topology Y) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        (δ (g)^*[ModuleCat.{u + 1} Λ] M N) =
    δ (g)^*[AddCommGrpCat.{u + 1}] _ _ ≫
      ((sheafComposeForget₂CompUpperStarIso Λ g).hom.app M ⊗ₘ
        (sheafComposeForget₂CompUpperStarIso Λ g).hom.app N) ≫
      μ (sheafCompose (ProEt.topology Y) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
        ((g)^*[ModuleCat.{u + 1} Λ].obj M) ((g)^*[ModuleCat.{u + 1} Λ].obj N) := by
  apply ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp,
    Adjunction.unit_naturality_assoc,
    unit_app_comp_lowerStar_map_sheafComposeForget₂CompUpperStarIso_hom_app_assoc,
    Functor.map_comp, Functor.map_comp,
    Adjunction.unit_app_tensor_comp_map_δ_assoc, ← μ_natural_assoc, tensorHom_comp_tensorHom_assoc,
    unit_app_comp_lowerStar_map_sheafComposeForget₂CompUpperStarIso_hom_app,
    unit_app_comp_lowerStar_map_sheafComposeForget₂CompUpperStarIso_hom_app]
  erw [← μ_sheafComposeForget₂_comp_map_lowerStar_μ Λ g ((g)^*[ModuleCat.{u + 1} Λ].obj M)
    ((g)^*[ModuleCat.{u + 1} Λ].obj N)]
  conv_rhs => erw [μ_natural_assoc]
  conv_rhs => rw [← Functor.map_comp, ← Adjunction.unit_app_tensor_comp_map_δ,
    Functor.map_comp]
  rfl

end AlgebraicGeometry.ProEtale

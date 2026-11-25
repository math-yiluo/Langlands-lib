/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.TraceFormula.Product

/-!
# Vanishing on the boundary for the ordinary Künneth formula, finite coefficients

Let `k` be a field, `Λ` a finite ring whose exponent is invertible in `k`, and `X`, `Y`, `U`, `Z`
separated `k`-schemes of finite type. For a morphism `f : U ⟶ Y`, a morphism `i : Z ⟶ X`, a
complex `M ∈ D(X_ét, Λ)` with `Li^* M = 0` and any `G ∈ D(U_ét, Λ)`, the complex
`R(𝟙 × f)_* (Lp_X^* M ⊗ᴸ Lp_U^* G)` vanishes on `Z ⨯ Y`
(`AlgebraicGeometry.Etale.isZero_upperStar_prodMap_lowerStar_prodMap_tensor`).

By the base change theorem for a pushforward tensored with a complex (blueprint
`lemma-kunneth-field-coefficients--1`, `AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap`) for the
cartesian squares
```
X <--p_X-- X ⨯ Y <--(𝟙 × f)-- X ⨯ U
|            |                  |
v            v p_Y              v p_U
Spec k <---- Y <------f-------- U
```
the complex is `Lp_X^* M ⊗ᴸ Lp_Y^* Rf_* G` (the ordinary Künneth formula, blueprint
`lemma-kunneth-one-identity-factor--1`), and its pullback to `Z ⨯ Y` is `Lp_Z^* Li^* M ⊗ᴸ (…) = 0`.

This is the finite-coefficient stage of the boundary vanishing
`ProEtale.CondensedRing.isZero_upperStar_lowerStar_externalProduct_lowerShriek`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]
  {X Y U Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]

/-- **Vanishing on the boundary, finite coefficients**: for morphisms `f : U ⟶ Y` and
`i : Z ⟶ X` of `k`-schemes of finite type, `M ∈ D(X_ét, Λ)` with `Li^* M = 0` and
`G ∈ D(U_ét, Λ)`, the pullback to `Z ⨯ Y` of `R(𝟙 × f)_* (Lp_X^* M ⊗ᴸ Lp_U^* G)` vanishes.
By the ordinary Künneth formula (blueprint `lemma-kunneth-one-identity-factor--1`, through
`isIso_tensorBaseChangeMap`, blueprint `lemma-kunneth-field-coefficients--1`) the complex is
`Lp_X^* M ⊗ᴸ Lp_Y^* Rf_* G`, whose pullback to `Z ⨯ Y` is `Lp_Z^* Li^* M ⊗ᴸ (…) = 0`. -/
theorem isZero_upperStar_prodMap_lowerStar_prodMap_tensor (f : U ⟶ Y) (i : Z ⟶ X)
    (M : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hM : IsZero (L((i.left)^*[ModuleCat.{u + 1} Λ]).obj M))
    (G : DerivedCategory (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsZero (L(((prod.map i (𝟙 Y)).left)^*[ModuleCat.{u + 1} Λ]).obj
      (R(((prod.map (𝟙 X) f).left)_*[ModuleCat.{u + 1} Λ]).obj
        (((-⊗ᴸ-((X ⨯ U).left)[ModuleCat.{u + 1} Λ]).obj
          (L(((prod.fst : X ⨯ U ⟶ X).left)^*[ModuleCat.{u + 1} Λ]).obj M)).obj
          (L(((prod.snd : X ⨯ U ⟶ U).left)^*[ModuleCat.{u + 1} Λ]).obj G)))) := by
  have hsq : IsPullback (prod.snd : X ⨯ U ⟶ U).left (prod.map (𝟙 X) f).left f.left
      (prod.snd : X ⨯ Y ⟶ Y).left := by
    refine IsPullback.of_bot ?_ (congrArg CommaMorphism.left (prod.map_snd (𝟙 X) f).symm)
      (ProEtale.CondensedRing.isPullback_prod_left X Y).flip
    rw [← Over.comp_left, prod.map_fst, Category.comp_id, Over.w f]
    exact (ProEtale.CondensedRing.isPullback_prod_left X U).flip
  have := isIso_tensorBaseChangeMap Λ X.hom Y.hom U.hom (prod.fst : X ⨯ Y ⟶ X).left
    (prod.snd : X ⨯ Y ⟶ Y).left (prod.map (𝟙 X) f).left (prod.snd : X ⨯ U ⟶ U).left
    f.left (Over.w f) (ProEtale.CondensedRing.isPullback_prod_left X Y) hsq.flip M G
  -- `L(i × 𝟙)^* Lp_X^* M ≅ Lp_Z^* Li^* M` vanishes
  have hZ : IsZero (L(((prod.map i (𝟙 Y)).left)^*[ModuleCat.{u + 1} Λ]).obj
      (L(((prod.fst : X ⨯ Y ⟶ X).left)^*[ModuleCat.{u + 1} Λ]).obj M)) :=
    ((L(((prod.fst : Z ⨯ Y ⟶ Z).left)^*[ModuleCat.{u + 1} Λ])).map_isZero hM).of_iso
      (((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) _ _ (prod.fst ≫ i : Z ⨯ Y ⟶ X).left
        (by rw [← Over.comp_left, prod.map_fst])).app M).symm ≪≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) _ _ _ (Over.comp_left _ _ _ _ _)).app M)
  refine (isZero_derivedTensor_obj_obj_of_isZero_left hZ
    (L(((prod.map i (𝟙 Y)).left)^*[ModuleCat.{u + 1} Λ]).obj
      (L(((prod.snd : X ⨯ Y ⟶ Y).left)^*[ModuleCat.{u + 1} Λ]).obj
        (R((f.left)_*[ModuleCat.{u + 1} Λ]).obj G)))).of_iso
    ((L(((prod.map i (𝟙 Y)).left)^*[ModuleCat.{u + 1} Λ])).mapIso ?_ ≪≫
      leftDerivedUpperStarTensorIso _ (prod.map i (𝟙 Y)).left _ _)
  exact (R(((prod.map (𝟙 X) f).left)_*[ModuleCat.{u + 1} Λ])).mapIso
    (((-⊗ᴸ-((X ⨯ U).left)[ModuleCat.{u + 1} Λ]).mapIso
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) _ _ _
        (by rw [← Over.comp_left, prod.map_fst, Category.comp_id])).app M)).app _) ≪≫
    (asIso (tensorBaseChangeMap _ _ _ _ _ _ _ _)).symm

end AlgebraicGeometry.Etale

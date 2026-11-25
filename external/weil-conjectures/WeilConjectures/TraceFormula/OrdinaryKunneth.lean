/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.KunnethNatTrans
public import WeilConjectures.TraceFormula.KunnethVerdier
public import WeilConjectures.TraceFormula.GenericBaseChange

/-!

# Ordinary Künneth formula along an open immersion

Let `X, Y` be separated `k`-schemes of finite type, `j : U ⟶ Y` an open immersion and
`G = 𝟙_X × j : X ⨯ U ⟶ X ⨯ Y`. For `M ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` and `B ∈ Dᵇc(U)⟦ℚ̲̄_ℓ⟧` the *Künneth map*
```
M ⊠ Rj_* B = Lp_X^* M ⊗ᴸ Lp_Y^* Rj_* B ⟶ RG_* (M ⊠ B)
```
(`ProEtale.CondensedRing.openKunnethMap`) is the adjoint, for `LG^* ⊣ RG_*`, of the monoidal
structure of `LG^*`, the composition isomorphisms `LG^* Lp_X^* ≅ Lp_X^*` and
`LG^* Lp_Y^* ≅ Lp_U^* Lj^*`, and the counit `Lj^* Rj_* B ⟶ B`.

## Main statements

- `ProEtale.CondensedRing.openKunnethMap`: the Künneth map, defined as the component of the
  generic Künneth natural transformation `CategoryTheory.Adjunction.kunnethNatTrans`.
- `ProEtale.CondensedRing.isIso_exchangeRight_prodMapUpperStarSndIso`,
  `ProEtale.CondensedRing.isIso_homEquiv_prodMapUpperStarSndIso_hom_app_comp_map_counit`: the
  transpose `Lp_Y^* Rj_* B ⟶ RG_* Lp_U^* B` of the second factor of the Künneth map is the base
  change morphism of the square `commSq_prodMap_snd`, hence an isomorphism by generic base change
  (`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_prodMap`).
- `ProEtale.CondensedRing.isIso_openKunnethMap_of_isDualizable`: the Künneth map is an
  isomorphism for dualizable `M`, by generic base change and the projection formula at the
  dualizable object `Lp_X^* M`.

The general case, by dévissage in `M`, is in
`WeilConjectures.TraceFormula.OrdinaryKunnethDevissage`.

## Implementation notes

Definitions abstract the instance proofs in their bodies into auxiliary constants, and comparing
terms built from them with separately elaborated terms makes the elaborator and the kernel unfold
the six functors. The Künneth map is therefore the component of a generic construction, and its
properties are obtained by unification with generic lemmas (`unfold openKunnethMap` followed by
`refine` with the data taken from the goal). The coefficient ring is always written explicitly:
writing it `_` elaborates its `Precoherent Profinite` instance to an auxiliary proof constant.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

-- the tensor products are elaborated through the monoidal category instance, as in the
-- abstract lemmas of `CategoryTheory.Adjunction.ProjectionMorphismDualizable`
attribute [local instance 2000] MonoidalCategory.toMonoidalCategoryStruct

variable {X Y U : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom]

/-- The composition isomorphism `L(𝟙 × j)^* Lp_X^* ≅ Lp_X^*` for the projections of `X ⨯ Y` and
`X ⨯ U`. -/
noncomputable def prodMapUpperStarFstIso (j : U ⟶ Y) :
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.fst : X ⨯ Y ⟶ X) ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j) ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.fst : X ⨯ U ⟶ X) :=
  (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j)
      prod.fst).symm ≪≫
    eqToIso (by rw [prod.map_fst, Category.comp_id])

/-- The composition isomorphism `L(𝟙 × j)^* Lp_Y^* ≅ Lp_U^* Lj^*` for the projections of `X ⨯ Y`
and `X ⨯ U`. -/
noncomputable def prodMapUpperStarSndIso (j : U ⟶ Y) :
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.snd : X ⨯ Y ⟶ Y) ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j) ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.snd : X ⨯ U ⟶ U) :=
  (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j)
      prod.snd).symm ≪≫
    eqToIso (by rw [prod.map_snd]) ≪≫
    boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ prod.snd j

/-- The second factor `L(𝟙 × j)^* Lp_Y^* Rj_* B ⟶ Lp_U^* B` of the transpose of the Künneth map:
the composition isomorphism `prodMapUpperStarSndIso` followed by the counit of `Lj^* ⊣ Rj_*`. -/
noncomputable def openKunnethSecondFactor (j : U ⟶ Y)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ Y ⟶ Y)).obj
          ((boundedConstructibleLowerStar ℓ j).obj B)) ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (prod.snd : X ⨯ U ⟶ U)).obj ((𝟭 _).obj B) :=
  (prodMapUpperStarSndIso ℓ j).hom.app _ ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (prod.snd : X ⨯ U ⟶ U)).map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
        j).counit.app B)

/-- The *Künneth map* `M ⊠ Rj_* B ⟶ R(𝟙 × j)_* (M ⊠ B)` for an open immersion `j : U ⟶ Y`: the
adjoint, for `L(𝟙 × j)^* ⊣ R(𝟙 × j)_*`, of the monoidal structure of `L(𝟙 × j)^*`, the
composition isomorphisms of the pullbacks and the counit `Lj^* Rj_* B ⟶ B`. It is the component at
`M` of the generic Künneth natural transformation `CategoryTheory.Adjunction.kunnethNatTrans`. -/
noncomputable def openKunnethMap (j : U ⟶ Y) (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    externalProduct ℓ (Y := Y) M
        ((boundedConstructibleLowerStar ℓ j).obj B) ⟶
      (boundedConstructibleLowerStar ℓ
        (prod.map (𝟙 X) j)).obj (externalProduct ℓ M B) :=
  ((boundedConstructibleUpperStarLowerStarAdjunction ℓ (prod.map (𝟙 X) j)).kunnethNatTrans
      (prodMapUpperStarFstIso ℓ j) (openKunnethSecondFactor ℓ j B)).app M

/-- `prodMapUpperStarSndIso` is the pullback comparison of the square `commSq_prodMap_snd`. -/
lemma prodMapUpperStarSndIso_eq_pullbackSquareComparison (j : U ⟶ Y) :
    prodMapUpperStarSndIso ℓ (X := X) j =
      boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
        (commSq_prodMap_snd j) :=
  rfl

/-- The exchange morphism `Lp_Y^* Rj_* ⟶ R(𝟙 × j)_* Lp_U^*` of `prodMapUpperStarSndIso` is an
isomorphism: it is the base change morphism of the square `commSq_prodMap_snd`, an isomorphism by
generic base change (`isIso_boundedConstructibleBaseChange_prodMap`). -/
lemma isIso_exchangeRight_prodMapUpperStarSndIso (j : U ⟶ Y) :
    IsIso (Adjunction.exchangeRight
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ j)
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ
        (prod.map (𝟙 X) j))
      (prodMapUpperStarSndIso ℓ (X := X) j)) := by
  rw [prodMapUpperStarSndIso_eq_pullbackSquareComparison,
    ← boundedConstructibleBaseChange_eq_exchangeRight]
  exact isIso_boundedConstructibleBaseChange_prodMap ℓ j

/-- `isIso_homEquiv_prodMapUpperStarSndIso_hom_app_comp_map_counit` for an abstract
isomorphism `θ` in place of `prodMapUpperStarSndIso`, so that neither the elaborator nor the
kernel unfolds `prodMapUpperStarSndIso`. -/
lemma isIso_homEquiv_hom_app_comp_map_counit_aux (j : U ⟶ Y)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (θ : boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.snd : X ⨯ Y ⟶ Y) ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j) ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.snd : X ⨯ U ⟶ U))
    (hθ : IsIso (Adjunction.exchangeRight
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ j)
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ
        (prod.map (𝟙 X) j)) θ)) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
      (prod.map (𝟙 X) j)).homEquiv
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ Y ⟶ Y)).obj
          ((boundedConstructibleLowerStar ℓ j).obj B))
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ U ⟶ U)).obj B)
        (θ.hom.app
          ((boundedConstructibleLowerStar ℓ j).obj B) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ U ⟶ U)).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            j).counit.app B))) :=
  Adjunction.isIso_homEquiv_hom_app_comp_map_counit _ _ θ B hθ

/-- The transpose `Lp_Y^* Rj_* B ⟶ R(𝟙 × j)_* Lp_U^* B` of the second factor of the Künneth map,
the counit of `Lj^* ⊣ Rj_*` transported along `prodMapUpperStarSndIso`, is an isomorphism: it is
the exchange morphism of `prodMapUpperStarSndIso`
(`isIso_exchangeRight_prodMapUpperStarSndIso`). -/
lemma isIso_homEquiv_prodMapUpperStarSndIso_hom_app_comp_map_counit (j : U ⟶ Y)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
      (prod.map (𝟙 X) j)).homEquiv
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ Y ⟶ Y)).obj
          ((boundedConstructibleLowerStar ℓ j).obj B))
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ U ⟶ U)).obj B)
        ((prodMapUpperStarSndIso ℓ (X := X) j).hom.app
          ((boundedConstructibleLowerStar ℓ j).obj B) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ U ⟶ U)).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            j).counit.app B))) :=
  isIso_homEquiv_hom_app_comp_map_counit_aux ℓ j B _
    (isIso_exchangeRight_prodMapUpperStarSndIso ℓ j)

/-- `openKunnethSecondFactor` for an abstract isomorphism `θ` in place of
`prodMapUpperStarSndIso`. As a definition in this file, its body is elaborated with the same
auxiliary proof constants as that of `openKunnethSecondFactor`, so that
`openKunnethSecondFactor_eq_secondFactorOf` is checked syntactically by the kernel. -/
noncomputable def secondFactorOf (j : U ⟶ Y)
    (θ : boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.snd : X ⨯ Y ⟶ Y) ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j) ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.snd : X ⨯ U ⟶ U))
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ Y ⟶ Y)).obj
          ((boundedConstructibleLowerStar ℓ j).obj B)) ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (prod.snd : X ⨯ U ⟶ U)).obj ((𝟭 _).obj B) :=
  θ.hom.app _ ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (prod.snd : X ⨯ U ⟶ U)).map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
        j).counit.app B)

lemma openKunnethSecondFactor_eq_secondFactorOf (j : U ⟶ Y)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    openKunnethSecondFactor ℓ (X := X) j B = secondFactorOf ℓ j (prodMapUpperStarSndIso ℓ j) B :=
  rfl

/-- The transpose of `secondFactorOf θ B` is an isomorphism if the exchange morphism of `θ` is. -/
lemma isIso_homEquiv_secondFactorOf (j : U ⟶ Y)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (θ : boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.snd : X ⨯ Y ⟶ Y) ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j) ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.snd : X ⨯ U ⟶ U))
    (hθ : IsIso (Adjunction.exchangeRight
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ j)
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ
        (prod.map (𝟙 X) j)) θ)) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
      (prod.map (𝟙 X) j)).homEquiv _ _ (secondFactorOf ℓ j θ B)) := by
  unfold secondFactorOf
  exact Adjunction.isIso_homEquiv_hom_app_comp_map_counit _ _ θ _ hθ

/-- The transpose of `openKunnethSecondFactor` along `L(𝟙 × j)^* ⊣ R(𝟙 × j)_*` is an
isomorphism. -/
lemma isIso_homEquiv_openKunnethSecondFactor (j : U ⟶ Y)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
      (prod.map (𝟙 X) j)).homEquiv _ _ (openKunnethSecondFactor ℓ j B)) := by
  rw [openKunnethSecondFactor_eq_secondFactorOf]
  exact isIso_homEquiv_secondFactorOf ℓ j B _ (isIso_exchangeRight_prodMapUpperStarSndIso ℓ j)

/-- **The ordinary Künneth formula for a dualizable first factor**: for an open immersion
`j : U ⟶ Y`, a dualizable `M ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` and any `B ∈ Dᵇc(U)⟦ℚ̲̄_ℓ⟧`, the Künneth map
`M ⊠ Rj_* B ⟶ R(𝟙 × j)_* (M ⊠ B)` is an isomorphism. Its second factor is the base change
morphism of `commSq_prodMap_snd`, an isomorphism by generic base change
(`isIso_homEquiv_prodMapUpperStarSndIso_hom_app_comp_map_counit`), and the projection morphism
of `L(𝟙 × j)^* ⊣ R(𝟙 × j)_*` at the dualizable object `Lp_X^* M` is an isomorphism
(`CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom_exchangeRight_of_isDualizable`). -/
theorem isIso_openKunnethMap_of_isDualizable (j : U ⟶ Y)
    {M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (hM : IsDualizable M)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (openKunnethMap ℓ j M B) := by
  unfold openKunnethMap
  refine Adjunction.isIso_kunnethNatTrans_app_of_isDualizable _ _ _ ?_ ?_
  · obtain ⟨_⟩ := hM
    exact ⟨@HasRightDual.mk _ _ _ _ _ (ExactPairing.map _ M Mᘁ)⟩
  · exact isIso_homEquiv_openKunnethSecondFactor ℓ j B

end AlgebraicGeometry.ProEtale.CondensedRing

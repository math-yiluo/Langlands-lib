/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMorphismComp
public import WeilConjectures.TraceFormula.OrdinaryKunnethDevissage
public import WeilConjectures.TraceFormula.GenericBaseChangePullback

/-!

# The relative Künneth formula in projection form

Let
```
P ──p₁──▶ X
│ p₂       │
▼          ▼
Y ───────▶ Spec k
```
be a cartesian square of separated `k`-schemes of finite type. For `A ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` and
`W ∈ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧`, the projection morphism
```
Rp₂_* (Lp₁^* A) ⊗ W ⟶ Rp₂_* (Lp₁^* A ⊗ Lp₂^* W)
```
is an isomorphism (`ProEtale.CondensedRing.isIso_projectionMorphism_upperStar_of_isPullback`,
SGA 4½ [Th. finitude] Cor. 1.11).

## Proof

Compactify `X ⟶ Spec k` as `X ⟶ X̄ ⟶ Spec k`, with `j : X ⟶ X̄` an open immersion and `X̄` proper.
Then `p₂ = e ≫ m ≫ g` with `e = (p₂, p₁) : P ⟶ Y ⨯ X` an isomorphism, `m = 𝟙 × j` and
`g : Y ⨯ X̄ ⟶ Y` the first projection, which is proper. The projection morphism of a composite is
an isomorphism if those of the factors are
(`CategoryTheory.Adjunction.isIso_projectionMorphism_of_comp`):

* for `e`, by the proper projection formula, `e` being an isomorphism; moreover the unit of
  `Le^* ⊣ Re_*` is an isomorphism;
* for `g`, by the proper projection formula
  (`isIso_projectionMorphism_boundedConstructible_padicAlgCl`);
* for `m`, at `(Lp_X^* A, Lg^* W)`, by the ordinary Künneth formula along the open immersion `j`
  (`ProEtale.CondensedRing.isIso_openKunnethMap`), through the left projection morphism
  (`ProEtale.CondensedRing.isIso_projectionMorphism_prodMap_id_of_isOpenImmersion`).

## Main statements

- `ProEtale.CondensedRing.isIso_projectionMorphism_upperStar_of_isPullback`

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

-- the tensor products are elaborated through the monoidal category instance, as in
-- `WeilConjectures.TraceFormula.OrdinaryKunneth`
attribute [local instance 2000] MonoidalCategory.toMonoidalCategoryStruct

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Factors

variable {X Y U P Q : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]

/-- **The ordinary Künneth formula in projection form**: for an open immersion `j : U ⟶ Y`, the
projection morphism of `L(𝟙 × j)^* ⊣ R(𝟙 × j)_*` at `(Lp_U^* B, Lp_X^* M)` is an isomorphism.
Up to the braidings it is the left projection morphism, which is the Künneth map
`isIso_openKunnethMap` up to the generic base change isomorphism of its second factor. -/
lemma isIso_projectionMorphism_prodMap_id_of_isOpenImmersion (j : U ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
        (prod.map (𝟙 X) j)).projectionMorphism
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ U ⟶ U)).obj B)
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.fst : X ⨯ Y ⟶ X)).obj M)) := by
  have h := isIso_openKunnethMap ℓ j M B
  unfold openKunnethMap at h
  rw [Adjunction.kunnethNatTrans_app] at h
  have : IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
      (prod.map (𝟙 X) j)).leftProjectionMorphism
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (prod.fst : X ⨯ Y ⟶ X)).obj M)
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (prod.snd : X ⨯ U ⟶ U)).obj B)) :=
    (Adjunction.isIso_homEquiv_δ_tensorHom_iff_isIso_leftProjectionMorphism _ _
      inferInstance _ (isIso_homEquiv_openKunnethSecondFactor ℓ j B)).mp h
  exact Adjunction.isIso_projectionMorphism_of_isIso_leftProjectionMorphism _
    (fun K L ↦ (boundedConstructibleUpperStar_map_braiding_hom_δ ℓ _ K L).symm) _ _

/-- The projection morphism of `L(e ≫ q)^* ⊣ R(e ≫ q)_*` at `(Le^* A, W)`, for an isomorphism
`e`, is an isomorphism if the one of `Lq^* ⊣ Rq_*` at `(A, W)` is. -/
lemma isIso_projectionMorphism_comp_of_isIso (e : P ⟶ Q) [IsIso e] (q : Q ⟶ Y)
    (A : Dᵇc(Q.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (W : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    [hA : IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ q).projectionMorphism A W)] :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ (e ≫ q)).projectionMorphism
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ e).obj A) W) := by
  have : IsIso e.left := inferInstanceAs (IsIso ((Over.forget _).map e))
  have : IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ q).projectionMorphism
      ((boundedConstructibleLowerStar ℓ e).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ e).obj A)) W) :=
    (Adjunction.isIso_projectionMorphism_iff_of_iso _
      (asIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ e).unit.app A)) W).mp hA
  exact Adjunction.isIso_projectionMorphism_of_comp
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ e)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ q)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (e ≫ q))
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ e q)
    (boundedConstructibleUpperStarComp_hom_app_tensor_δ ℓ e q) _ _

/-- For an open immersion `j : U ⟶ Y` such that the first projection `g : X ⨯ Y ⟶ X` is proper,
the projection morphism of `L((𝟙 × j) ≫ g)^* ⊣ R((𝟙 × j) ≫ g)_*` at `(Lp_U^* A, W)` is an
isomorphism: it is composed of the one of `g`, an isomorphism by the proper projection formula,
and the one of `𝟙 × j` (`isIso_projectionMorphism_prodMap_id_of_isOpenImmersion`). -/
lemma isIso_projectionMorphism_prodMap_id_comp_fst (j : U ⟶ Y) [IsOpenImmersion j.left]
    [IsProper (prod.fst : X ⨯ Y ⟶ X).left]
    (A : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (W : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
        (prod.map (𝟙 X) j ≫ prod.fst)).projectionMorphism
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ U ⟶ U)).obj A) W) := by
  have := isIso_projectionMorphism_prodMap_id_of_isOpenImmersion ℓ j W A
  exact Adjunction.isIso_projectionMorphism_of_comp
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (prod.map (𝟙 X) j))
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ prod.fst)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (prod.map (𝟙 X) j ≫ prod.fst))
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ _ _)
    (boundedConstructibleUpperStarComp_hom_app_tensor_δ ℓ _ _) _ _

/-- Transport of `isIso_projectionMorphism_comp_of_isIso` along factorizations `p₂ = e ≫ q` and
`p₁ = e ≫ p` with `e` an isomorphism: the projection morphism of `Lp₂^* ⊣ Rp₂_*` at `(Lp₁^* A, W)`
is an isomorphism if the one of `Lq^* ⊣ Rq_*` at `(Lp^* A, W)` is. -/
lemma isIso_projectionMorphism_upperStar_of_comp_isIso (e : P ⟶ Q) [IsIso e] (q : Q ⟶ Y)
    (p : Q ⟶ X) {p₁ : P ⟶ X} {p₂ : P ⟶ Y} (h₁ : e ≫ p = p₁) (h₂ : e ≫ q = p₂)
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (W : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    [IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ q).projectionMorphism
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj A) W)] :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ p₂).projectionMorphism
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p₁).obj A) W) := by
  subst h₁ h₂
  have := isIso_projectionMorphism_comp_of_isIso ℓ e q
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj A) W
  exact (Adjunction.isIso_projectionMorphism_iff_of_iso _
    ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ e p).app A) W).mpr this

end Factors

variable {X Y P : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] in
/-- For a proper `g : Z ⟶ s` to the base point, the first projection `Y ⨯ Z ⟶ Y` is proper: it is
the base change `𝟙 × g : Y ⨯ Z ⟶ Y ⨯ s` followed by the isomorphism `Y ⨯ s ≅ Y`. -/
lemma isProper_prodFst_of_isProper_toPoint {Z : Over (Spec (.of k))} (g : Z ⟶ point k)
    [IsProper g.left] : IsProper (prod.fst : Y ⨯ Z ⟶ Y).left := by
  have : IsProper (prod.map (𝟙 Y) g).left :=
    MorphismProperty.of_isPullback ((IsPullback.of_prod_snd_with_id g Y).map (Over.forget _))
      (inferInstanceAs (IsProper g.left))
  have : IsIso (prod.lift (𝟙 Y) (toPoint Y) ≫ prod.fst) := by
    rw [prod.lift_fst]
    infer_instance
  have : IsIso (prod.fst : Y ⨯ point k ⟶ Y) :=
    IsIso.of_isIso_comp_left (prod.lift (𝟙 Y) (toPoint Y)) _
  have : IsIso (prod.fst : Y ⨯ point k ⟶ Y).left :=
    inferInstanceAs (IsIso ((Over.forget _).map prod.fst))
  have e : (prod.fst : Y ⨯ Z ⟶ Y) = prod.map (𝟙 Y) g ≫ prod.fst := by simp
  rw [e, Over.comp_left]
  infer_instance

/-- **The relative Künneth formula in projection form** (SGA 4½ [Th. finitude] Cor. 1.11): for a
cartesian square `P = X ×_k Y` with projections `p₁`, `p₂`, the projection morphism
`Rp₂_* (Lp₁^* A) ⊗ W ⟶ Rp₂_* (Lp₁^* A ⊗ Lp₂^* W)` is an isomorphism. Compactifying
`X ⟶ X̄ ⟶ Spec k`, `p₂` factors as the isomorphism `(p₂, p₁) : P ⟶ Y ⨯ X`, the morphism
`𝟙 × j : Y ⨯ X ⟶ Y ⨯ X̄` along the open immersion `j : X ⟶ X̄` and the proper projection
`Y ⨯ X̄ ⟶ Y`. -/
theorem isIso_projectionMorphism_upperStar_of_isPullback {p₁ : P ⟶ X} {p₂ : P ⟶ Y}
    (h : IsPullback p₁.left p₂.left X.hom Y.hom)
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (W : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ p₂).projectionMorphism
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p₁).obj A) W) := by
  have := isIso_prodLift_of_isPullback h
  let c := compactificationOverField (toPoint X)
  have := isProper_prodFst_of_isProper_toPoint (Y := Y) c.overG
  have := isIso_projectionMorphism_prodMap_id_comp_fst ℓ (X := Y) c.overI A W
  exact isIso_projectionMorphism_upperStar_of_comp_isIso ℓ (prod.lift p₂ p₁)
    (prod.map (𝟙 Y) c.overI ≫ prod.fst) prod.snd (prod.lift_snd _ _) (by simp) A W

end AlgebraicGeometry.ProEtale.CondensedRing

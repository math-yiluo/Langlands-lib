/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.OrdinaryKunneth
public import WeilConjectures.TraceFormula.ProperKunneth

/-!

# The ordinary Künneth map and proper pushforward in the first factor: composites

Let `j : U ⟶ Y` be an open immersion and `g : Z ⟶ X` a proper morphism of separated `k`-schemes
of finite type. For `N ∈ Dᵇc(Z)⟦ℚ̲̄_ℓ⟧` and `B ∈ Dᵇc(U)⟦ℚ̲̄_ℓ⟧`, if the Künneth map
`κ_Z(N, B) : N ⊠ Rj_* B ⟶ R(𝟙 × j)_* (N ⊠ B)` (`ProEtale.CondensedRing.openKunnethMap`) is an
isomorphism, so is `κ_X(Rg_* N, B)`
(`ProEtale.CondensedRing.isIso_openKunnethMap_lowerStar_of_isProper`).

## Proof

The second factor of the Künneth map has invertible transpose (generic base change,
`ProEtale.CondensedRing.isIso_exchangeRight_prodMapUpperStarSndIso`), so `κ_X(M, B)` is an
isomorphism if and only if the left projection morphism
`Lp_X^* M ⊗ R(𝟙 × j)_* Lp_U^* B ⟶ R(𝟙 × j)_* (L(𝟙 × j)^* Lp_X^* M ⊗ Lp_U^* B)` is
(`CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom_iff_isIso_leftProjectionMorphism`).
These left projection morphisms are compared
(`ProEtale.CondensedRing.isIso_leftProjectionMorphism_prodMap_lowerStar`) through the Künneth map
of `q = g × j : Z ⨯ U ⟶ X ⨯ Y`, the transpose along `Lq^* ⊣ Rq_*` of
```
Lq^* (Lp_X^* Rg_* N ⊗ Lp_Y^* Rj_* B) ⟶ Lq^* Lp_X^* Rg_* N ⊗ Lq^* Lp_Y^* Rj_* B ⟶ Lp_Z^* N ⊗ Lp_U^* B
```
built from the transported counits (`ProEtale.CondensedRing.prodUpperStarCounit`), decomposed
along the two factorizations of `q`:

* `q = (g × 𝟙_U) ≫ (𝟙_X × j)`: by `CategoryTheory.Adjunction.homEquiv_δ_tensorHom_eq` it is the
  left projection morphism of `𝟙_X × j` at `(Lp_X^* Rg_* N, Lp_U^* B)` up to proper and generic
  base change morphisms and the proper projection formula for `g × 𝟙_U`
  (`CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom_iff_of_isIso`);
* `q = (𝟙_Z × j) ≫ (g × 𝟙_Y)`: by the mirrored decomposition
  `CategoryTheory.Adjunction.homEquiv_δ_tensorHom_eq_right` it is `R(g × 𝟙_Y)_*` of the left
  projection morphism of `𝟙_Z × j` at `(Lp_Z^* N, Lp_U^* B)` up to the same kind of isomorphisms
  (`CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom_of_isIso_right`).

## Implementation notes

The Künneth maps are only compared through abstract lemmas instantiated by unification: terms
obtained by unfolding definitions contain auxiliary proof constants and `eqToHom`s, and comparing
them with separately elaborated terms makes the elaborator and the kernel unfold large terms.

This module holds the abstract decompositions of the Künneth map of a composite and the first
comparison, along `q = (𝟙_Z × j) ≫ (g × 𝟙_Y)`; the rest of the proof is in
`WeilConjectures.TraceFormula.OrdinaryKunnethClosed` (split for compile time).

## Main statements

- `ProEtale.CondensedRing.isIso_homEquiv_δ_tensorHom_prodUpperStarCounit_prodMap_id_comp`

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃ u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

open Functor.OplaxMonoidal

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃]
  {R' : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} (adjR : R' ⊣ R)
  {S' : C₃ ⥤ C₂} {S : C₂ ⥤ C₃} (adjS : S' ⊣ S)
  {Q' : C₃ ⥤ C₁} {Q : C₁ ⥤ C₃} (adjQ : Q' ⊣ Q)
  [MonoidalCategory C₁] [MonoidalCategory C₂] [MonoidalCategory C₃] [R'.OplaxMonoidal]
  [S'.OplaxMonoidal] [Q'.OplaxMonoidal]

/-- **The Künneth map of a composite, through the first factor.** Let `Q' ≅ S' ⋙ R'` be
compatible with the oplax monoidal structures, let `c₁ : Q' U ⟶ A₁` and `c₂ : Q' V ⟶ A₂`, and
suppose that `c₁` comes from `d₁ : S' U ⟶ W` up to `i₁ : R' W ⟶ A₁`. Then the transpose of
`Q' (U ⊗ V) ⟶ Q' U ⊗ Q' V ⟶ A₁ ⊗ A₂` is the composite
```
U ⊗ V ⟶ S W ⊗ V ⟶ S (W ⊗ S' V) ⟶ S (W ⊗ R A₂) ⟶ S R (R' W ⊗ A₂) ⟶ S R (A₁ ⊗ A₂) ≅ Q (A₁ ⊗ A₂)
```
of the transpose of `d₁`, the projection morphism of `S`, the transpose `h₂` of
`Q' V ≅ R' S' V ⟶ A₂`, the left projection morphism of `R` and `i₁`. This is the mirror image of
`CategoryTheory.Adjunction.homEquiv_δ_tensorHom_eq`. -/
lemma homEquiv_δ_tensorHom_eq_right (e : Q' ≅ S' ⋙ R')
    (he : ∀ U V : C₃, δ Q' U V ≫ (e.hom.app U ⊗ₘ e.hom.app V) =
      e.hom.app (U ⊗ V) ≫ R'.map (δ S' U V) ≫ δ R' (S'.obj U) (S'.obj V))
    {U V : C₃} {A₁ A₂ : C₁} (c₁ : Q'.obj U ⟶ A₁) (c₂ : Q'.obj V ⟶ A₂) {W : C₂}
    (d₁ : S'.obj U ⟶ W) (i₁ : R'.obj W ⟶ A₁) (hc₁ : e.inv.app U ≫ c₁ = R'.map d₁ ≫ i₁) :
    adjQ.homEquiv _ _ (δ Q' U V ≫ (c₁ ⊗ₘ c₂)) =
      adjS.homEquiv _ _ d₁ ▷ V ≫ adjS.projectionMorphism W V ≫
        S.map (W ◁ adjR.homEquiv _ _ (e.inv.app V ≫ c₂) ≫ adjR.leftProjectionMorphism W A₂ ≫
          R.map (i₁ ▷ A₂)) ≫
        (rightAdjointUniq ((adjS.comp adjR).ofNatIsoLeft e.symm) adjQ).hom.app _ := by
  have hδ : e.inv.app (U ⊗ V) ≫ δ Q' U V =
      R'.map (δ S' U V) ≫ δ R' (S'.obj U) (S'.obj V) ≫ (e.inv.app U ⊗ₘ e.inv.app V) := by
    rw [← cancel_epi (e.hom.app (U ⊗ V)), Iso.hom_inv_id_app_assoc, ← reassoc_of% he U V,
      tensorHom_comp_tensorHom, Iso.hom_inv_id_app, Iso.hom_inv_id_app, id_tensorHom_id,
      Category.comp_id]
  have key : e.inv.app (U ⊗ V) ≫ δ Q' U V ≫ (c₁ ⊗ₘ c₂) =
      R'.map (δ S' U V ≫ d₁ ▷ S'.obj V) ≫
        (δ R' W (S'.obj V) ≫ R'.obj W ◁ (e.inv.app V ≫ c₂)) ≫ i₁ ▷ A₂ := by
    rw [reassoc_of% hδ, tensorHom_comp_tensorHom, hc₁, Functor.map_comp, Category.assoc,
      Category.assoc, ← δ_natural_left_assoc, ← whisker_exchange_assoc, tensorHom_def',
      comp_whiskerRight]
  rw [homEquiv_eq_homEquiv_homEquiv adjR adjS adjQ e, key, homEquiv_naturality_left (adj := adjR),
    homEquiv_naturality_right (adj := adjR), homEquiv_δ_whiskerLeft,
    homEquiv_naturality_right (adj := adjS), homEquiv_δ_whiskerRight]
  simp only [Category.assoc, Functor.map_comp]

/-- The Künneth map of a composite (`CategoryTheory.Adjunction.homEquiv_δ_tensorHom_eq_right`) is
an isomorphism if the transposes of `d₁` and of `Q' V ≅ R' S' V ⟶ A₂`, the projection morphism of
`S` at `(W, V)`, the left projection morphism of `R` at `(W, A₂)` and `i₁` are isomorphisms. -/
lemma isIso_homEquiv_δ_tensorHom_of_isIso_right (e : Q' ≅ S' ⋙ R')
    (he : ∀ U V : C₃, δ Q' U V ≫ (e.hom.app U ⊗ₘ e.hom.app V) =
      e.hom.app (U ⊗ V) ≫ R'.map (δ S' U V) ≫ δ R' (S'.obj U) (S'.obj V))
    {U V : C₃} {A₁ A₂ : C₁} (c₁ : Q'.obj U ⟶ A₁) (c₂ : Q'.obj V ⟶ A₂) {W : C₂}
    (d₁ : S'.obj U ⟶ W) (i₁ : R'.obj W ⟶ A₁) (hc₁ : e.inv.app U ≫ c₁ = R'.map d₁ ≫ i₁)
    [IsIso (adjS.homEquiv _ _ d₁)] [IsIso (adjS.projectionMorphism W V)] [IsIso i₁]
    [IsIso (adjR.homEquiv _ _ (e.inv.app V ≫ c₂))] [IsIso (adjR.leftProjectionMorphism W A₂)] :
    IsIso (adjQ.homEquiv _ _ (δ Q' U V ≫ (c₁ ⊗ₘ c₂))) := by
  rw [homEquiv_δ_tensorHom_eq_right adjR adjS adjQ e he c₁ c₂ d₁ i₁ hc₁]
  infer_instance

/-- The Künneth map of a composite (`CategoryTheory.Adjunction.homEquiv_δ_tensorHom_eq`) is an
isomorphism if and only if the left projection morphism of `S` at `(U, W)` is, provided the
transposes of `d₂` and of `Q' U ≅ R' S' U ⟶ A₁`, the projection morphism of `R` at `(A₁, W)` and
`i₂` are isomorphisms. -/
lemma isIso_homEquiv_δ_tensorHom_iff_of_isIso (e : Q' ≅ S' ⋙ R')
    (he : ∀ U V : C₃, δ Q' U V ≫ (e.hom.app U ⊗ₘ e.hom.app V) =
      e.hom.app (U ⊗ V) ≫ R'.map (δ S' U V) ≫ δ R' (S'.obj U) (S'.obj V))
    {U V : C₃} {A₁ A₂ : C₁} (c₁ : Q'.obj U ⟶ A₁) (c₂ : Q'.obj V ⟶ A₂) {W : C₂}
    (d₂ : S'.obj V ⟶ W) (i₂ : R'.obj W ⟶ A₂) (hc₂ : e.inv.app V ≫ c₂ = R'.map d₂ ≫ i₂)
    [IsIso (adjS.homEquiv _ _ d₂)] [IsIso (adjR.homEquiv _ _ (e.inv.app U ≫ c₁))]
    [IsIso (adjR.projectionMorphism A₁ W)] [IsIso i₂] :
    IsIso (adjQ.homEquiv _ _ (δ Q' U V ≫ (c₁ ⊗ₘ c₂))) ↔
      IsIso (adjS.leftProjectionMorphism U W) := by
  have : IsIso (adjR.homEquiv _ _ (e.inv.app U ≫ c₁) ▷ W ≫ adjR.projectionMorphism A₁ W ≫
      R.map (A₁ ◁ i₂)) := inferInstance
  rw [homEquiv_δ_tensorHom_eq adjR adjS adjQ e he c₁ c₂ d₂ i₂ hc₂, isIso_comp_left_iff,
    ← Category.assoc, isIso_comp_right_iff, isIso_comp_right_iff]

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]

/-- A Künneth map `B ⊗ X ⟶ G (A₁ ⊗ A₂)`, the transpose of `F (B ⊗ X) ⟶ F B ⊗ F X ⟶ A₁ ⊗ A₂`
built from an isomorphism `a : F B ⟶ A₁` and a morphism `c : F X ⟶ A₂` with invertible transpose,
is an isomorphism if and only if the left projection morphism `B ⊗ G A₂ ⟶ G (F B ⊗ A₂)` is
(`homEquiv_δ_whiskerLeft`). -/
lemma isIso_homEquiv_δ_tensorHom_iff_isIso_leftProjectionMorphism {B X : D} {A₁ A₂ : C}
    (a : F.obj B ⟶ A₁) (ha : IsIso a) (c : F.obj X ⟶ A₂) (hc : IsIso (adj.homEquiv _ _ c)) :
    IsIso (adj.homEquiv _ _ (Functor.OplaxMonoidal.δ F B X ≫ (a ⊗ₘ c))) ↔
      IsIso (adj.leftProjectionMorphism B A₂) := by
  rw [tensorHom_def', ← Category.assoc, homEquiv_naturality_right, homEquiv_δ_whiskerLeft,
    isIso_comp_right_iff, isIso_comp_left_iff]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

-- the tensor products are elaborated through the monoidal category instance, as in
-- `WeilConjectures.TraceFormula.OrdinaryKunneth`
attribute [local instance 2000] MonoidalCategory.toMonoidalCategoryStruct

variable {X Y U Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- The invertibility of the Künneth map of transported counits only depends on the morphisms
involved up to equality. -/
lemma isIso_homEquiv_δ_tensorHom_prodUpperStarCounit_congr {P Q X₁ X₂ Y₁ Y₂ : Over (Spec (.of k))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
    [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
    [LocallyOfFiniteType X₂.hom] [QuasiCompact X₂.hom] [IsSeparated X₂.hom]
    [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
    [LocallyOfFiniteType Y₂.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom]
    {q q' : P ⟶ Q} {p₁ p₁' : P ⟶ X₁} {p₂ p₂' : P ⟶ X₂} {π₁ : Q ⟶ Y₁} {π₂ : Q ⟶ Y₂}
    {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} (hq : q = q') (hp₁ : p₁ = p₁') (hp₂ : p₂ = p₂')
    (w₁ : q ≫ π₁ = p₁ ≫ f₁) (w₂ : q ≫ π₂ = p₂ ≫ f₂) (w₁' : q' ≫ π₁ = p₁' ≫ f₁)
    (w₂' : q' ≫ π₂ = p₂' ≫ f₂) (B₁ : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B₂ : Dᵇc(X₂.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
        q).homEquiv _ _
      (Functor.OplaxMonoidal.δ
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ q) _ _ ≫
        (prodUpperStarCounit ℓ w₁ B₁ ⊗ₘ prodUpperStarCounit ℓ w₂ B₂))) ↔
      IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
        q').homEquiv _ _
      (Functor.OplaxMonoidal.δ
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ q') _ _ ≫
        (prodUpperStarCounit ℓ w₁' B₁ ⊗ₘ prodUpperStarCounit ℓ w₂' B₂))) := by
  subst hq hp₁ hp₂
  rfl

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] in
/-- The base change `g × 𝟙 : Z ⨯ W ⟶ X ⨯ W` of a proper morphism `g` is proper. -/
lemma isProper_prodMap_id {W : Over (Spec (.of k))} (g : Z ⟶ X) [IsProper g.left] :
    IsProper (prod.map g (𝟙 W)).left :=
  MorphismProperty.of_isPullback ((IsPullback.of_prod_fst_with_id g W).map (Over.forget _))
    (inferInstanceAs (IsProper g.left))

/-- The transpose of a transported counit of a square `(𝟙 × j) ≫ p' = p_U ≫ j`, with `p'` the
second projection, is an isomorphism (generic base change). -/
lemma isIso_homEquiv_prodUpperStarCounit_of_eq_snd (j : U ⟶ Y) {p' : X ⨯ Y ⟶ Y}
    (hp : p' = prod.snd) (w : prod.map (𝟙 X) j ≫ p' = prod.snd ≫ j)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
      (prod.map (𝟙 X) j)).homEquiv _ _ (prodUpperStarCounit ℓ w B)) := by
  subst hp
  rw [homEquiv_prodUpperStarCounit]
  have := isIso_boundedConstructibleBaseChange_prodMap ℓ (X := X) j
  infer_instance

-- the instantiation of the abstract lemmas involves large terms
/-- **The Künneth map of `g × j` along `(𝟙 × j) ≫ (g × 𝟙)`**: for a proper `g : Z ⟶ X`, if the
left projection morphism of `L(𝟙_Z × j)^* ⊣ R(𝟙_Z × j)_*` at `(Lp_Z^* N, Lp_U^* B)` is an
isomorphism, so is the Künneth map of `(𝟙_Z × j) ≫ (g × 𝟙_Y)` built from the transported counits
(`CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom_of_isIso_right`); the remaining comparison
maps are proper and generic base change morphisms and proper projection morphisms. -/
lemma isIso_homEquiv_δ_tensorHom_prodUpperStarCounit_prodMap_id_comp (g : Z ⟶ X)
    [IsProper g.left] (j : U ⟶ Y) (N : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (w₁' : (prod.map (𝟙 Z) j ≫ prod.map g (𝟙 Y)) ≫ prod.fst =
      (prod.map (𝟙 Z) j ≫ prod.fst) ≫ g)
    (w₂' : (prod.map (𝟙 Z) j ≫ prod.map g (𝟙 Y)) ≫ prod.snd = prod.snd ≫ j)
    (h : IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
        (prod.map (𝟙 Z) j)).leftProjectionMorphism
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.fst : Z ⨯ Y ⟶ Z)).obj N)
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : Z ⨯ U ⟶ U)).obj B))) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction
      ℓ (prod.map (𝟙 Z) j ≫ prod.map g (𝟙 Y))).homEquiv _ _
      (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.map (𝟙 Z) j ≫ prod.map g (𝟙 Y))) _ _ ≫
        (prodUpperStarCounit ℓ w₁' N ⊗ₘ prodUpperStarCounit ℓ w₂' B))) := by
  have := isProper_prodMap_id (W := Y) g
  have hsnd : prod.map g (𝟙 Y) ≫ (prod.snd : X ⨯ Y ⟶ Y) = prod.snd := by simp
  have w₂'' : prod.map (𝟙 Z) j ≫ prod.map g (𝟙 Y) ≫ (prod.snd : X ⨯ Y ⟶ Y) = prod.snd ≫ j := by
    simp
  have sqY := IsPullback.of_prod_fst_with_id g Y
  have := isIso_homEquiv_prodUpperStarCounit ℓ sqY N
  have : IsIso ((boundedConstructibleUpperStarLowerStarAdjunction
      ℓ (prod.map (𝟙 Z) j)).homEquiv _ _
      ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
        (prod.map (𝟙 Z) j) (prod.map g (𝟙 Y))).inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ prod.snd).obj
          ((boundedConstructibleLowerStar ℓ j).obj B)) ≫
        prodUpperStarCounit ℓ w₂' B)) := by
    rw [upperStarComp_inv_app_comp_prodUpperStarCounit_right ℓ w₂' w₂'' B,
      Adjunction.homEquiv_naturality_left]
    have := isIso_homEquiv_prodUpperStarCounit_of_eq_snd ℓ (X := Z) j hsnd w₂'' B
    infer_instance
  exact Adjunction.isIso_homEquiv_δ_tensorHom_of_isIso_right
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (prod.map (𝟙 Z) j))
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (prod.map g (𝟙 Y))) _
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ _ _)
    (boundedConstructibleUpperStarComp_hom_app_tensor_δ ℓ _ _) _ _ _
    ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
      (prod.map (𝟙 Z) j) prod.fst).inv.app N)
    (upperStarComp_inv_app_comp_prodUpperStarCounit_left ℓ w₁' sqY.w.symm N)

end AlgebraicGeometry.ProEtale.CondensedRing

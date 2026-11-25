/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.GenericBaseChange

/-!

# Generic base change along a structure morphism

Let `X` and `Y` be separated `k`-schemes of finite type and
```
P ──p₁──▶ X
│ p₂       │ a_X
▼          ▼
Y ──a_Y──▶ Spec k
```
a cartesian square. Its base change morphism `La_Y^* Ra_X_* ⟶ Rp₂_* Lp₁^*` on
`Dᵇc(-)⟦ℚ̲̄_ℓ⟧` is an isomorphism
(`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isPullback_toPoint`).

The square is the horizontal pasting of the square
```
P ──(p₂, p₁)──▶ Y ⨯ X
│ p₂              │ 𝟙 × a_X
▼                 ▼
Y ──(𝟙, a_Y)──▶ Y ⨯ Spec k
```
whose horizontal maps are isomorphisms, with the product square
`ProEtale.CondensedRing.commSq_prodMap_snd (a_X)`, whose base change morphism is an isomorphism by
generic base change (`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_prodMap`).

## Main statements

- `ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isPullback_toPoint`: generic
  base change along `Y ⟶ Spec k` for any cartesian square over the base point.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y P : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

omit [Fact (ringChar k).Prime] in
/-- The morphism `(𝟙, a_Y) : Y ⟶ Y ⨯ s` to the product with the base point is an isomorphism. -/
instance isIso_prodLift_id_toPoint (Y : Over (Spec (.of k))) :
    IsIso (prod.lift (𝟙 Y) (toPoint Y)) :=
  ⟨⟨prod.fst, prod.lift_fst _ _, prod.hom_ext (by simp) (toPoint_ext _ _)⟩⟩

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom] in
/-- If `P` is the fibre product of the structure morphisms of `X` and `Y`, the morphism
`(p₂, p₁) : P ⟶ Y ⨯ X` is an isomorphism. -/
lemma isIso_prodLift_of_isPullback {p₁ : P ⟶ X} {p₂ : P ⟶ Y}
    (h : IsPullback p₁.left p₂.left X.hom Y.hom) : IsIso (prod.lift p₂ p₁) := by
  have hYX := (isPullback_prod_left Y X).flip
  have e : (prod.lift p₂ p₁).left = (h.isoIsPullback _ _ hYX).hom := by
    refine hYX.hom_ext ?_ ?_
    · rw [IsPullback.isoIsPullback_hom_fst, ← Over.comp_left, prod.lift_snd]
    · rw [IsPullback.isoIsPullback_hom_snd, ← Over.comp_left, prod.lift_fst]
  rw [← isIso_iff_of_reflects_iso _ (Over.forget _), Over.forget_map, e]
  infer_instance

/-- The formalism `boundedConstructibleExchangeFormalism`, for `ℚ̄_ℓ`-sheaves. -/
local notation "𝔽" => boundedConstructibleExchangeFormalism ℓ k

/-- **Generic base change along a structure morphism**: for a cartesian square
```
P ──p₁──▶ X
│ p₂       │ a_X
▼          ▼
Y ──a_Y──▶ Spec k
```
of separated `k`-schemes of finite type, the base change morphism
`La_Y^* Ra_X_* ⟶ Rp₂_* Lp₁^*` is an isomorphism on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧`.

The square is the horizontal pasting of a square with isomorphisms `P ≅ Y ⨯ X` and
`Y ≅ Y ⨯ s` as horizontal maps (`isIso_boundedConstructibleBaseChange_of_isIso`) with the
product square `commSq_prodMap_snd (toPoint X)`
(`isIso_boundedConstructibleBaseChange_prodMap`). -/
theorem isIso_boundedConstructibleBaseChange_of_isPullback_toPoint {p₁ : P ⟶ X} {p₂ : P ⟶ Y}
    (sq : CommSq p₁ p₂ (toPoint X) (toPoint Y))
    (h : IsPullback p₁.left p₂.left X.hom Y.hom) :
    IsIso (boundedConstructibleBaseChange ℓ sq) := by
  have : IsIso (prod.lift p₂ p₁) := isIso_prodLift_of_isPullback h
  have sq₁ : CommSq (prod.lift p₂ p₁) p₂ (prod.map (𝟙 Y) (toPoint X))
      (prod.lift (𝟙 Y) (toPoint Y)) :=
    ⟨prod.hom_ext (by simp) (toPoint_ext _ _)⟩
  have h₁ := isIso_boundedConstructibleBaseChange_of_isIso ℓ sq₁
  have h₂ := isIso_boundedConstructibleBaseChange_prodMap ℓ (X := Y) (toPoint X)
  rw [boundedConstructibleBaseChange_eq_pfBaseChange] at h₁ h₂
  have e := (𝔽).pfBaseChange_paste_horiz (SepFinType.homMk (prod.lift p₂ p₁))
    (SepFinType.homMk (prod.snd : Y ⨯ X ⟶ X)) (SepFinType.homMk p₂)
    (SepFinType.homMk (prod.map (𝟙 Y) (toPoint X))) (SepFinType.homMk (toPoint X))
    (SepFinType.homMk (prod.lift (𝟙 Y) (toPoint Y)))
    (SepFinType.homMk (prod.snd : Y ⨯ point k ⟶ point k))
    (SepFinType.homMk p₁) (SepFinType.homMk (toPoint Y))
    (SepFinType.homMk_comp_homMk sq₁.w)
    (SepFinType.homMk_comp_homMk (commSq_prodMap_snd (toPoint X)).w)
    (ObjectProperty.hom_ext _ (by simp)) (ObjectProperty.hom_ext _ (by simp))
    (SepFinType.homMk_comp_homMk sq.w)
  rw [boundedConstructibleBaseChange_eq_pfBaseChange, e]
  dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp]
  refine IsIso.comp_isIso' (IsIso.comp_isIso' inferInstance ?_) inferInstance
  refine IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' ?_ (IsIso.comp_isIso' inferInstance
    (IsIso.comp_isIso' ?_ inferInstance)))
  · exact Functor.isIso_whiskerRight _ _
  · exact Functor.isIso_whiskerLeft _ _

end AlgebraicGeometry.ProEtale.CondensedRing

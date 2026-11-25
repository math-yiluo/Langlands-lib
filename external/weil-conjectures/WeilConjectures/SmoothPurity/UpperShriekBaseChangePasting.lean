/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.UpperShriekSmoothBaseChange

/-!
# Horizontal pasting of the exceptional base change map

For cartesian squares of separated `k`-schemes of finite type
```
X₁ --g'₁--> X₂ --g'₂--> X₃
|           |           |
f₁          f₂          f
v           v           v
Y₁ --g₁---> Y₂ --g₂---> Y₃
```
the exceptional base change map `L(g'₁ ≫ g'₂)^* Rf^! L ⟶ Rf₁^! L(g₁ ≫ g₂)^* L` of the outer
rectangle (`ProEtale.CondensedRing.upperShriekBaseChange`) is `Lg'₁^*` of the map of the right
square followed by the map of the left square, through the composition isomorphisms of the
pullbacks (`ProEtale.CondensedRing.upperShriekBaseChange_paste_horiz`). This is the mate of the
horizontal pasting law of compact-support base change
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz`) by the
abstract pasting law `CategoryTheory.Adjunction.exceptionalBaseChange_paste_horiz`.

Consequently the class of morphisms `g` along which `Rf^!` commutes with base change is closed
under composition, and we get base change along immersions (a closed immersion followed by an
open immersion) for smooth `f`
(`ProEtale.CondensedRing.isIso_upperShriekBaseChange_of_isClosedImmersion_comp_isOpenImmersion`),
as well as the invariance of the base change map under isomorphisms of pullback squares
(`ProEtale.CondensedRing.isIso_upperShriekBaseChange_iff_of_iso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* D₁] [Category* D₂] [Category* D₃]
  {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂} {L : C₃ ⥤ D₃} {R : D₃ ⥤ C₃}
  {u₁ : C₂ ⥤ C₁} {u₂ : C₃ ⥤ C₂} {u : C₃ ⥤ C₁} {v₁ : D₂ ⥤ D₁} {v₂ : D₃ ⥤ D₂} {v : D₃ ⥤ D₁}

/-- **Horizontal pasting of exceptional base changes**: let `bc₂ : L ⋙ v₂ ⟶ u₂ ⋙ L₂` and
`bc₁ : L₂ ⋙ v₁ ⟶ u₁ ⋙ L₁` be invertible base changes for adjunctions `L ⊣ R`, `L₂ ⊣ R₂` and
`L₁ ⊣ R₁`, and let `bc : L ⋙ v ⟶ u ⋙ L₁` be their pasting through `u ≅ u₂ ⋙ u₁` and
`v ≅ v₂ ⋙ v₁`. Then the exceptional base change of `bc` is `u₁` of that of `bc₂` followed by that
of `bc₁`, through the same isomorphisms. -/
lemma exceptionalBaseChange_paste_horiz (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a : L ⊣ R)
    (eu : u ≅ u₂ ⋙ u₁) (ev : v ≅ v₂ ⋙ v₁) (bc₁ : L₂ ⋙ v₁ ⟶ u₁ ⋙ L₁) [IsIso bc₁]
    (bc₂ : L ⋙ v₂ ⟶ u₂ ⋙ L₂) [IsIso bc₂] (bc : L ⋙ v ⟶ u ⋙ L₁) [IsIso bc]
    (h : ∀ K, bc.app K = ev.hom.app (L.obj K) ≫ v₁.map (bc₂.app K) ≫ bc₁.app (u₂.obj K) ≫
      L₁.map (eu.inv.app K)) (N : D₃) :
    exceptionalBaseChange a a₁ bc N =
      eu.hom.app (R.obj N) ≫ u₁.map (exceptionalBaseChange a a₂ bc₂ N) ≫
        exceptionalBaseChange a₂ a₁ bc₁ (v₂.obj N) ≫ R₁.map (ev.inv.app N) := by
  apply (a₁.homEquiv _ _).symm.injective
  have h₂ : L₂.map (exceptionalBaseChange a a₂ bc₂ N) ≫ a₂.counit.app (v₂.obj N) =
      inv (bc₂.app (R.obj N)) ≫ v₂.map (a.counit.app N) :=
    (a₂.homEquiv _ _).symm_apply_apply _
  have hinv (K : C₃) : inv (bc.app K) = L₁.map (eu.hom.app K) ≫ inv (bc₁.app (u₂.obj K)) ≫
      v₁.map (inv (bc₂.app K)) ≫ ev.inv.app (L.obj K) := by
    rw [IsIso.inv_eq_of_hom_inv_id]
    rw [h]
    simp [← Functor.map_comp_assoc]
  have h₀ : (a₁.homEquiv _ _).symm (exceptionalBaseChange a a₁ bc N) =
      inv (bc.app (R.obj N)) ≫ v.map (a.counit.app N) :=
    (a₁.homEquiv _ _).symm_apply_apply _
  have h₁ : (a₁.homEquiv _ _).symm (exceptionalBaseChange a₂ a₁ bc₁ (v₂.obj N)) =
      inv (bc₁.app (R₂.obj (v₂.obj N))) ≫ v₁.map (a₂.counit.app (v₂.obj N)) :=
    (a₁.homEquiv _ _).symm_apply_apply _
  have n₁ := (inv bc₁).naturality (exceptionalBaseChange a a₂ bc₂ N)
  have n₂ := ev.inv.naturality (a.counit.app N)
  simp only [Functor.comp_map, NatIso.isIso_inv_app, Functor.comp_obj, Functor.id_obj] at n₁ n₂
  rw [h₀, Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm, h₁, hinv]
  simp only [Category.assoc]
  congr 1
  rw [reassoc_of% n₁, ← Functor.map_comp_assoc, h₂]
  simp [n₂]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Pasting

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Over (Spec (.of k))}
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X₂.hom] [QuasiCompact X₂.hom] [IsSeparated X₂.hom]
  [LocallyOfFiniteType X₃.hom] [QuasiCompact X₃.hom] [IsSeparated X₃.hom]
  [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
  [LocallyOfFiniteType Y₂.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom]
  [LocallyOfFiniteType Y₃.hom] [QuasiCompact Y₃.hom] [IsSeparated Y₃.hom]
  {g'₁ : X₁ ⟶ X₂} {g'₂ : X₂ ⟶ X₃} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} {f : X₃ ⟶ Y₃}
  {g₁ : Y₁ ⟶ Y₂} {g₂ : Y₂ ⟶ Y₃}

/-- **The exceptional base change map is compatible with horizontal pasting**: for cartesian
squares `g'₁ ≫ f₂ = f₁ ≫ g₁` and `g'₂ ≫ f = f₂ ≫ g₂`, the exceptional base change map of the
outer rectangle is
```
L(g'₁ ≫ g'₂)^* Rf^! L ≅ Lg'₁^* Lg'₂^* Rf^! L ⟶ Lg'₁^* Rf₂^! Lg₂^* L ⟶ Rf₁^! Lg₁^* Lg₂^* L
  ≅ Rf₁^! L(g₁ ≫ g₂)^* L,
```
`Lg'₁^*` of the map of the right square followed by the map of the left square. -/
theorem upperShriekBaseChange_paste_horiz (sq₁ : IsPullback g'₁ f₁ f₂ g₁)
    (sq₂ : IsPullback g'₂ f₂ f g₂) (L : Dᵇc(Y₃.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    upperShriekBaseChange ℓ (sq₁.paste_horiz sq₂) L =
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g'₁ g'₂).hom.app
          ((boundedConstructibleUpperShriek ℓ f).obj L) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g'₁).map
          (upperShriekBaseChange ℓ sq₂ L) ≫
        upperShriekBaseChange ℓ sq₁
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g₂).obj L) ≫
        (boundedConstructibleUpperShriek ℓ f₁).map
          ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g₁ g₂).inv.app
            L) := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₁
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₂
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (sq₁.paste_horiz sq₂)
  rw [upperShriekBaseChange_eq_exceptionalBaseChange,
    upperShriekBaseChange_eq_exceptionalBaseChange, upperShriekBaseChange_eq_exceptionalBaseChange]
  exact Adjunction.exceptionalBaseChange_paste_horiz
    (boundedConstructibleUpperShriekAdjunction ℓ f₁)
    (boundedConstructibleUpperShriekAdjunction ℓ f₂)
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g'₁ g'₂)
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g₁ g₂)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₁)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₂)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (sq₁.paste_horiz sq₂))
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz ℓ sq₁ sq₂) L

/-- **Composition of base changes**: if `Rf^!` commutes with base change along `g₂` at `L` and
`Rf₂^!` commutes with base change along `g₁` at `Lg₂^* L`, then `Rf^!` commutes with base change
along `g₁ ≫ g₂` at `L`. -/
theorem isIso_upperShriekBaseChange_paste_horiz (sq₁ : IsPullback g'₁ f₁ f₂ g₁)
    (sq₂ : IsPullback g'₂ f₂ f g₂) (L : Dᵇc(Y₃.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    [IsIso (upperShriekBaseChange ℓ sq₂ L)]
    [IsIso (upperShriekBaseChange ℓ sq₁
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g₂).obj L))] :
    IsIso (upperShriekBaseChange ℓ (sq₁.paste_horiz sq₂) L) := by
  rw [upperShriekBaseChange_paste_horiz ℓ sq₁ sq₂ L]
  infer_instance

/-- **Cancellation of base changes on the left**: if `Rf₂^!` commutes with base change along `g₁`
at `Lg₂^* L` and `Rf^!` commutes with base change along `g₁ ≫ g₂` at `L`, then `Lg'₁^*` inverts
the exceptional base change map of `g₂` at `L`. -/
theorem isIso_upperStar_map_upperShriekBaseChange_of_paste_horiz
    (sq₁ : IsPullback g'₁ f₁ f₂ g₁) (sq₂ : IsPullback g'₂ f₂ f g₂)
    (L : Dᵇc(Y₃.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    [IsIso (upperShriekBaseChange ℓ sq₁
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g₂).obj L))]
    (h : IsIso (upperShriekBaseChange ℓ (sq₁.paste_horiz sq₂) L)) :
    IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g'₁).map
      (upperShriekBaseChange ℓ sq₂ L)) := by
  rwa [upperShriekBaseChange_paste_horiz ℓ sq₁ sq₂ L, isIso_comp_left_iff,
    isIso_comp_right_iff] at h

/-- **Cancellation of base changes on the right**: if `Lg'₁^*` inverts the exceptional base change
map of `g₂` at `L` and `Rf^!` commutes with base change along `g₁ ≫ g₂` at `L`, then `Rf₂^!`
commutes with base change along `g₁` at `Lg₂^* L`. -/
theorem isIso_upperShriekBaseChange_of_paste_horiz (sq₁ : IsPullback g'₁ f₁ f₂ g₁)
    (sq₂ : IsPullback g'₂ f₂ f g₂) (L : Dᵇc(Y₃.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    [IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g'₁).map
      (upperShriekBaseChange ℓ sq₂ L))]
    (h : IsIso (upperShriekBaseChange ℓ (sq₁.paste_horiz sq₂) L)) :
    IsIso (upperShriekBaseChange ℓ sq₁
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g₂).obj L)) := by
  rwa [upperShriekBaseChange_paste_horiz ℓ sq₁ sq₂ L, isIso_comp_left_iff, isIso_comp_left_iff,
    isIso_comp_right_iff] at h

end Pasting

section Invariance

variable {X Y X' X'' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType X''.hom] [QuasiCompact X''.hom] [IsSeparated X''.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y}

/-- The exceptional base change map only depends on the morphisms of the square: if the
horizontal maps of two cartesian squares with the same vertical maps agree, then one exceptional
base change map is an isomorphism if and only if the other one is. -/
lemma isIso_upperShriekBaseChange_iff_of_eq {f' : X' ⟶ Y'} {g'₁ g'₂ : X' ⟶ X} {g₁ g₂ : Y' ⟶ Y}
    (sq₁ : IsPullback g'₁ f' f g₁) (sq₂ : IsPullback g'₂ f' f g₂) (h' : g'₁ = g'₂) (h : g₁ = g₂)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (upperShriekBaseChange ℓ sq₁ L) ↔ IsIso (upperShriekBaseChange ℓ sq₂ L) := by
  subst h' h
  rfl

/-- One direction of `isIso_upperShriekBaseChange_iff_of_isPullback`. -/
lemma isIso_upperShriekBaseChange_of_isPullback {g : Y' ⟶ Y} {f'₁ : X' ⟶ Y'} {g'₁ : X' ⟶ X}
    {f'₂ : X'' ⟶ Y'} {g'₂ : X'' ⟶ X} (sq₁ : IsPullback g'₁ f'₁ f g)
    (sq₂ : IsPullback g'₂ f'₂ f g) (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    [IsIso (upperShriekBaseChange ℓ sq₂ L)] :
    IsIso (upperShriekBaseChange ℓ sq₁ L) := by
  let e := sq₁.isoIsPullback _ _ sq₂
  have sqe : IsPullback e.hom f'₁ f'₂ (𝟙 Y') :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsPullback.isoIsPullback_hom_snd]⟩
  have : IsIso (upperShriekBaseChange ℓ sqe
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj L)) :=
    isIso_upperShriekBaseChange_of_isOpenImmersion_right ℓ sqe _
  have := isIso_upperShriekBaseChange_paste_horiz ℓ sqe sq₂ L
  exact (isIso_upperShriekBaseChange_iff_of_eq ℓ (sqe.paste_horiz sq₂) sq₁
    (IsPullback.isoIsPullback_hom_fst _ _ _ _) (Category.id_comp g) L).1 this

/-- **The exceptional base change map does not depend on the choice of the fibre product**: for
two cartesian squares with the same maps `f` and `g`, one exceptional base change map is an
isomorphism if and only if the other one is. -/
theorem isIso_upperShriekBaseChange_iff_of_isPullback {g : Y' ⟶ Y} {f'₁ : X' ⟶ Y'}
    {g'₁ : X' ⟶ X} {f'₂ : X'' ⟶ Y'} {g'₂ : X'' ⟶ X} (sq₁ : IsPullback g'₁ f'₁ f g)
    (sq₂ : IsPullback g'₂ f'₂ f g) (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (upperShriekBaseChange ℓ sq₁ L) ↔ IsIso (upperShriekBaseChange ℓ sq₂ L) :=
  ⟨fun _ ↦ isIso_upperShriekBaseChange_of_isPullback ℓ sq₂ sq₁ L,
    fun _ ↦ isIso_upperShriekBaseChange_of_isPullback ℓ sq₁ sq₂ L⟩

/-- `isIso_upperShriekBaseChange_iff_of_isPullback` for two equal vertical maps `f₁ = f₂`. -/
theorem isIso_upperShriekBaseChange_iff_of_isPullback_of_eq {f₁ f₂ : X ⟶ Y} (hf : f₁ = f₂)
    {g : Y' ⟶ Y} {f'₁ : X' ⟶ Y'} {g'₁ : X' ⟶ X} {f'₂ : X'' ⟶ Y'} {g'₂ : X'' ⟶ X}
    (sq₁ : IsPullback g'₁ f'₁ f₁ g) (sq₂ : IsPullback g'₂ f'₂ f₂ g)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (upperShriekBaseChange ℓ sq₁ L) ↔ IsIso (upperShriekBaseChange ℓ sq₂ L) := by
  subst hf
  exact isIso_upperShriekBaseChange_iff_of_isPullback ℓ sq₁ sq₂ L

/-- **Smooth base change for `Rf^!` along an immersion**: for a cartesian square
`g' ≫ f = f' ≫ g` with `f` smooth and `g` an immersion, the exceptional base change map
`Lg'^* Rf^! L ⟶ Rf'^! Lg^* L` is an isomorphism. The immersion is a closed immersion into an open
subscheme `W` of `Y` (`Scheme.Hom.liftCoborder`), and the base change map along it is pasted from
those along the open immersion `W ⟶ Y` (`isIso_upperShriekBaseChange_of_isOpenImmersion_right`)
and along the closed immersion
(`isIso_upperShriekBaseChange_of_smooth_of_isClosedImmersion`). -/
theorem isIso_upperShriekBaseChange_of_isImmersion {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) [Smooth f.left] [IsImmersion g.left]
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (upperShriekBaseChange ℓ sq L) := by
  let j := overRestrictι Y g.left.coborderRange
  let i : Y' ⟶ overRestrict Y g.left.coborderRange :=
    Over.homMk g.left.liftCoborder (by
      simp only [Over.mk_hom, ← Category.assoc, Scheme.Hom.liftCoborder_ι]
      exact Over.w g)
  have hij : i ≫ j = g := by
    ext1
    exact g.left.liftCoborder_ι
  have sq₂ := IsPullback.of_hasPullback f j
  let g'₁ : X' ⟶ pullback f j :=
    pullback.lift g' (f' ≫ i) (by rw [sq.w, Category.assoc, hij])
  have sq₁ : IsPullback g'₁ f' (pullback.snd f j) i := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) sq₂
    rw [pullback.lift_fst, hij]
    exact sq
  have : Smooth (pullback.snd f j).left := by
    have hsq₂ := sq₂.map (Over.forget _)
    simp only [Over.forget_map] at hsq₂
    exact MorphismProperty.of_isPullback hsq₂ inferInstance
  have : IsClosedImmersion i.left :=
    inferInstanceAs (IsClosedImmersion g.left.liftCoborder)
  have := isIso_upperShriekBaseChange_of_isOpenImmersion_right ℓ sq₂ L
  have := isIso_upperShriekBaseChange_of_smooth_of_isClosedImmersion ℓ sq₁
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj L)
  have := isIso_upperShriekBaseChange_paste_horiz ℓ sq₁ sq₂ L
  exact (isIso_upperShriekBaseChange_iff_of_eq ℓ (sq₁.paste_horiz sq₂) sq
    (pullback.lift_fst _ _ _) hij L).1 this

end Invariance

end AlgebraicGeometry.ProEtale.CondensedRing

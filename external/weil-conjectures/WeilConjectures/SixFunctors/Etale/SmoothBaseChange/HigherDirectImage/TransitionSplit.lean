/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Functor.EpiMono
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent

/-!
# Injectivity of the transition maps of higher direct images on geometric stalks

Let `f : X ⟶ Y` be quasi-compact and quasi-separated, `e : Y' ⟶ Y` smooth and `π : X' ⟶ X` the
base change of `e`. After pullback along `e`, the transition map `Rf_* K ⟶ R(π ≫ f)_* π^* K` is
a split monomorphism: by smooth base change it becomes the transition map along the projection
`X' ×_Y Y' ⟶ X'` over `Y'`, which has the section `(𝟙, f')`. Consequently the transition map
`R^q f_* G ⟶ R^q (π ≫ f)_* π^* G` is injective on the stalks at the geometric points of `Y`
which lift to `Y'`, although `e` need not be surjective.

## Main statements

- `AlgebraicGeometry.Etale.isSplitMono_upperStar_map_lowerStarPlusTransition`: the splitting.
- `AlgebraicGeometry.Etale.injective_sheafFiber_map_higherDirectImageTransition`: injectivity
  on stalks.

The compatibility of these transition maps with the transition maps over `X` is
`AlgebraicGeometry.Etale.higherDirectImageTransition_comp_higherDirectImageOverMap`, in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.TransitionOverMap`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

/-- If `x ≫ y` is an isomorphism, then `x` is a split monomorphism. -/
lemma CategoryTheory.isSplitMono_of_isIso_comp {C : Type*} [Category* C] {A B D : C}
    (x : A ⟶ B) (y : B ⟶ D) (hxy : IsIso (x ≫ y)) : IsSplitMono x :=
  IsSplitMono.mk' ⟨y ≫ inv (x ≫ y), by rw [← Category.assoc, IsIso.hom_inv_id]⟩

/-- A natural isomorphism `F ≅ G` transports split monomorphisms `F.map φ` to `G.map φ`. -/
lemma CategoryTheory.isSplitMono_map_of_iso {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) {A B : C} (φ : A ⟶ B) [IsSplitMono (F.map φ)] :
    IsSplitMono (G.map φ) := by
  rw [← NatIso.naturality_1 e φ]
  infer_instance

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

open Scheme in
/-- After pullback along a smooth `e : Y' ⟶ Y`, the transition map `Rf_* K ⟶ R(π ≫ f)_* π^* K`
along the base change `π : X' ⟶ X` of `e` is a split monomorphism: by smooth base change it is
the transition map along `X' ×_Y Y' ⟶ X'` over `Y'`, which has the section `(𝟙, f')`. -/
theorem Etale.isSplitMono_upperStar_map_lowerStarPlusTransition {X Y Y' X' : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (e : Y' ⟶ Y) [Smooth e]
    (π : X' ⟶ X) (f' : X' ⟶ Y') (sq : IsPullback π f' f e)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ j, IsTorsionSheafOfInvertibleOrder Y
      ((DerivedCategory.Plus.homologyFunctor _ j).obj K)) :
    IsSplitMono (D+((e)^*[ModuleCat.{u + 1} Λ]).map
      (Etale.lowerStarPlusTransition Λ π f (π ≫ f) rfl K)) := by
  let e' := pullback.fst (π ≫ f) e
  let h' := pullback.snd (π ≫ f) e
  have sq'' : CommSq e' h' (π ≫ f) e := ⟨pullback.condition⟩
  let a : pullback (π ≫ f) e ⟶ X' := sq.lift (e' ≫ π) h' (by simpa using pullback.condition)
  have wa : a ≫ π = e' ≫ π := sq.lift_fst _ _ _
  have wh : a ≫ f' = h' := sq.lift_snd _ _ _
  have key := Etale.baseChange_app_comp_targetTransitionPlus Λ sq.toCommSq π (π ≫ f) rfl sq''
    a wa wh K
  -- the section `σ = (𝟙, f')` of `a`
  let σ : X' ⟶ pullback (π ≫ f) e := pullback.lift (𝟙 X') f' (by simpa using sq.w)
  have hσe : σ ≫ e' = 𝟙 X' ≫ 𝟙 X' := by simp [σ, e']
  have hσh : σ ≫ h' = f' := by simp [σ, h']
  have hσa : σ ≫ a = 𝟙 X' := by
    apply sq.hom_ext
    · rw [Category.assoc, wa, ← Category.assoc, hσe]
      simp
    · simp [a, σ, hσh, wh]
  have hcomp := Etale.targetTransitionPlus_comp Λ π f' π a e' h' wa wh (𝟙 X') σ (𝟙 X') f'
    hσe hσh π (𝟙 X') hσa (by simp) (by simp) (by simp) K
  have hiso := Etale.isIso_targetTransitionPlus Λ π f' π (𝟙 X') (𝟙 X') f' (by simp) (by simp) K
  have hT : IsSplitMono (Etale.targetTransitionPlus Λ π f' π a e' h' wa wh K) := by
    rw [← hcomp] at hiso
    exact isSplitMono_of_isIso_comp _ _ hiso
  have hBC := Etale.isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder Λ e sq K hK
  refine IsSplitMono.mk' (SplitMono.mk ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq'').app _ ≫
      retraction (Etale.targetTransitionPlus Λ π f' π a e' h' wa wh K) ≫
      inv ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)) ?_)
  rw [← Category.assoc, ← Category.assoc, ← key]
  simp

open Scheme in
/-- The transition map of higher direct images along the base change `π : X' ⟶ X` of a smooth
`e : Y' ⟶ Y` is injective on the stalks at the geometric points of `Y` which lift to `Y'`. -/
theorem Etale.injective_sheafFiber_map_higherDirectImageTransition {X Y Y' X' : Scheme.{u}}
    [HasInvertibleExponent Λ Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (e : Y' ⟶ Y) [Smooth e]
    (π : X' ⟶ X) (f' : X' ⟶ Y') (sq : IsPullback π f' f e)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y') (q : ℤ) :
    Function.Injective (((pointSmallEtale (t ≫ e)).ulift.{u + 1}).sheafFiber.map
      (Etale.higherDirectImageTransition Λ π f (π ≫ f) rfl q G)).hom := by
  obtain ⟨n, hn, hΛ, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := Y)
  -- Stated for an arbitrary `K`, so that the complex `G[0]` is only supplied at the end, in the
  -- form in which it appears in the body of `Etale.higherDirectImageTransition`: the kernel then
  -- never compares two differently elaborated copies of the derived categories involved.
  have key (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (hK : ∀ j, IsTorsionSheafOfInvertibleOrder Y
        ((DerivedCategory.Plus.homologyFunctor _ j).obj K)) :
      Mono (((pointSmallEtale (t ≫ e)).ulift.{u + 1}).sheafFiber.map
        ((DerivedCategory.Plus.homologyFunctor _ q).map
          (Etale.lowerStarPlusTransition Λ π f (π ≫ f) rfl K))) := by
    have hs := Etale.isSplitMono_upperStar_map_lowerStarPlusTransition Λ f e π f' sq K hK
    let τ := Etale.lowerStarPlusTransition Λ π f (π ≫ f) rfl K
    have h₀ : IsSplitMono ((D+((e)^*[ModuleCat.{u + 1} Λ]) ⋙
        DerivedCategory.Plus.homologyFunctor _ q).map τ) := by
      rw [Functor.comp_map]
      infer_instance
    have h₁ : IsSplitMono (((DerivedCategory.Plus.homologyFunctor _ q) ⋙
        (e)^*[ModuleCat.{u + 1} Λ]).map τ) :=
      isSplitMono_map_of_iso
        (((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q).symm τ
    have h₂ : IsSplitMono ((DerivedCategory.Plus.homologyFunctor _ q ⋙
        (e)^*[ModuleCat.{u + 1} Λ] ⋙ ((pointSmallEtale t).ulift.{u + 1}).sheafFiber).map τ) :=
      inferInstanceAs (IsSplitMono (((pointSmallEtale t).ulift.{u + 1}).sheafFiber.map
        (((DerivedCategory.Plus.homologyFunctor _ q) ⋙ (e)^*[ModuleCat.{u + 1} Λ]).map τ)))
    have h₃ : IsSplitMono ((DerivedCategory.Plus.homologyFunctor _ q ⋙
        ((pointSmallEtale (t ≫ e)).ulift.{u + 1}).sheafFiber).map τ) :=
      isSplitMono_map_of_iso (Functor.isoWhiskerLeft (DerivedCategory.Plus.homologyFunctor _ q)
        (Etale.upperStarCompUliftSheafFiberIso (ModuleCat.{u + 1} Λ) e t)) τ
    exact h₃.mono
  rw [← ModuleCat.mono_iff_injective]
  -- The transition map is `H.map (τ ≫ s)` with `s` an isomorphism; `τ` and `s` are found by
  -- unification with its body rather than elaborated again.
  exact Functor.mono_map_map_comp_of_isIso _ _ _ _
    (key _ fun j ↦ IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero Λ n hn.ne' hΛ hu _)

end AlgebraicGeometry

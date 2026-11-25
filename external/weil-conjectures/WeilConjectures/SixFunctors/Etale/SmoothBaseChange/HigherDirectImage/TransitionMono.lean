/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Limit
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition
import WeilConjectures.Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Composition and injectivity of the transition maps of higher direct images

The transition maps `AlgebraicGeometry.Etale.higherDirectImageOverMap` of higher direct images
along morphisms of schemes over a fixed scheme compose
(`AlgebraicGeometry.Etale.higherDirectImageOverMap_comp`).

The transition map `R^q h_* K ⟶ R^q h₁_* (a^* K)` along `a : Y₁ ⟶ Y` is a monomorphism as soon as,
after base change along an étale surjective morphism `g : X' ⟶ X` of the base, the projection
`Y ×_X X' ⟶ Y` factors through `a`
(`AlgebraicGeometry.Etale.mono_homologyFunctor_map_lowerStarPlusTransition`). Indeed, by the
pasting law the pullback along `g` of the transition map, followed by a further base-change map,
is the base-change map of the cartesian square of `h` along `g`, which is an isomorphism by étale
base change; and the pullback along a surjective morphism is faithful.

## Main statements

- `AlgebraicGeometry.Etale.higherDirectImageOverMap_comp`: the transition maps compose.
- `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isLimit_of_mono`: a higher direct image
  vanishes if it injects into the stages of a limit over which the higher direct image vanishes.
- `AlgebraicGeometry.Etale.mono_homologyFunctor_map_lowerStarPlusTransition`,
  `AlgebraicGeometry.Etale.mono_higherDirectImageOverMap`: the injectivity criterion.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The transition maps `AlgebraicGeometry.Etale.higherDirectImageOverMap` along morphisms of
schemes over `T` compose. -/
lemma Etale.higherDirectImageOverMap_comp {T S : Scheme.{u}} (g : T ⟶ S)
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) {U V W : Over T}
    (φ : U ⟶ V) (ψ : V ⟶ W) :
    Etale.higherDirectImageOverMap Λ g G q (φ ≫ ψ) =
      Etale.higherDirectImageOverMap Λ g G q ψ ≫ Etale.higherDirectImageOverMap Λ g G q φ := by
  refine (cancel_epi ((DerivedCategory.Plus.homologyFunctor _ q).map
    (R+((W.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).map
      ((((W.hom)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
        G)))).1 ?_
  have kψ := Etale.homologyFunctor_map_overLowerStarTransition Λ g G q ψ
  have kφ := Etale.homologyFunctor_map_overLowerStarTransition Λ g G q φ
  have hc := congrArg (DerivedCategory.Plus.homologyFunctor _ q).map
    (Etale.overLowerStarTransition_comp Λ g W.hom V.hom U.hom ψ.left φ.left (φ ≫ ψ).left
      (Over.w ψ) (Over.w φ) (Over.w (φ ≫ ψ)) (Over.comp_left _ _ _ φ ψ).symm
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G))
  rw [Functor.map_comp] at hc
  rw [← Etale.homologyFunctor_map_overLowerStarTransition, ← hc]
  erw [Category.assoc, kφ, ← Category.assoc, kψ, Category.assoc]

/-- **Injectivity of the transition maps.** Let `a : Y₁ ⟶ Y` and `h : Y ⟶ X` with
`a ≫ h = h₁`, and let `g : X' ⟶ X` be étale and surjective. If the projection
`pr : Y ×_X X' ⟶ Y` factors through `a`, then the transition map
`R^q h_* K ⟶ R^q h₁_* (a^* K)` is a monomorphism in every degree `q`.

By the pasting law (`AlgebraicGeometry.Etale.baseChange_app_paste_horiz_of_eq`), the pullback
along `g` of the transition map, which is a base-change map
(`AlgebraicGeometry.Etale.lowerStarPlusTransition_eq_baseChange`), followed by the base-change
map of the square formed by the factorisation of `pr`, is the base-change map of the cartesian
square of `h` along `g`; the latter is an isomorphism by étale base change
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_etale`). So the pullback of the
transition map along `g` is a split monomorphism, and `g^*` is faithful as `g` is surjective
(`AlgebraicGeometry.Etale.faithful_upperStar_of_surjective`). -/
theorem Etale.mono_homologyFunctor_map_lowerStarPlusTransition {X Y Y₁ X' Y' : Scheme.{u}}
    (a : Y₁ ⟶ Y) (h : Y ⟶ X) (h₁ : Y₁ ⟶ X) (w : a ≫ h = h₁) (g : X' ⟶ X) [Etale g]
    (hg : Function.Surjective g.base) {pr : Y' ⟶ Y} {h' : Y' ⟶ X'}
    (sq : IsPullback pr h' h g) (pr₁ : Y' ⟶ Y₁) (hpr : pr₁ ≫ a = pr)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (q : ℤ) :
    Mono ((DerivedCategory.Plus.homologyFunctor _ q).map
      (Etale.lowerStarPlusTransition Λ a h h₁ w K)) := by
  have sqA : CommSq a h₁ h (𝟙 X) := ⟨by rw [w, Category.comp_id]⟩
  have sqB : CommSq pr₁ h' h₁ g := ⟨by rw [← w, ← Category.assoc, hpr, sq.w]⟩
  have hB : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := by
    have := Etale.isIso_derivedBaseChangeMapPlus_of_etale Λ sq
    rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
    infer_instance
  rw [Etale.baseChange_app_paste_horiz_of_eq Λ sqA sqB sq.toCommSq hpr (Category.comp_id g)
    K] at hB
  -- the pullback along `g` of the base-change map of the degenerate square is a split mono
  have hsplit : IsSplitMono (D+((g)^*[ModuleCat.{u + 1} Λ]).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) sqA).app K)) := by
    have hsm {A B C : DerivedCategory.Plus (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
        (m : A ⟶ B) (n : B ⟶ C) (_ : IsIso (m ≫ n)) : IsSplitMono m :=
      IsSplitMono.mk' ⟨n ≫ inv (m ≫ n), by rw [← Category.assoc, IsIso.hom_inv_id]⟩
    exact hsm _ _ (@IsIso.of_isIso_comp_left _ _ _ _ _ _ _ _ hB)
  have hmono : Mono ((g)^*[ModuleCat.{u + 1} Λ].map
      ((DerivedCategory.Plus.homologyFunctor _ q).map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sqA).app K))) := by
    have e := (((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso
      q).hom.naturality ((Etale.baseChange (ModuleCat.{u + 1} Λ) sqA).app K)
    simp only [Functor.comp_map] at e
    have e' := (Iso.eq_comp_inv
      ((((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q).app _)).2 e
    rw [e']
    exact mono_comp' (mono_comp' (IsIso.mono_of_iso _)
      (IsSplitMono.mk' (hsplit.exists_splitMono.some.map _)).mono) (IsIso.mono_of_iso _)
  have := Etale.faithful_upperStar_of_surjective.{u} Λ g hg
  have : Mono ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) sqA).app K)) :=
    (g)^*[ModuleCat.{u + 1} Λ].mono_of_mono_map hmono
  rw [Etale.lowerStarPlusTransition_eq_baseChange Λ a h h₁ w sqA, Functor.map_comp]
  infer_instance

/-- **Injectivity of the transition maps over a base.** For `k : T ⟶ S`, a sheaf `G` on `T`, a
morphism `φ : U ⟶ V` of schemes over `T` and an étale surjective `g : S' ⟶ S` such that the
projection `(V ×_S S') ⟶ V` factors through `φ`, the transition map
`R^q (V → S)_* (G|_V) ⟶ R^q (U → S)_* (G|_U)` is a monomorphism. -/
theorem Etale.mono_higherDirectImageOverMap {T S S' P : Scheme.{u}} (k : T ⟶ S)
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) {U V : Over T}
    (φ : U ⟶ V) (g : S' ⟶ S) [Etale g] (hg : Function.Surjective g.base) {pr : P ⟶ V.left}
    {h' : P ⟶ S'} (sq : IsPullback pr h' (V.hom ≫ k) g) (pr₁ : P ⟶ U.left)
    (hpr : pr₁ ≫ φ.left = pr) :
    Mono (Etale.higherDirectImageOverMap Λ k G q φ) := by
  have := Etale.mono_homologyFunctor_map_lowerStarPlusTransition Λ φ.left (V.hom ≫ k)
    (U.hom ≫ k) (by rw [← Category.assoc, Over.w]) g hg sq pr₁ hpr
    ((DerivedCategory.Plus.singleFunctor _ 0).obj (((V.hom)^*[ModuleCat.{u + 1} Λ]).obj G)) q
  exact Functor.mono_map_comp_map_map_comp_map_map_of_isIso _ _ _ _ _ this

open ZeroObject in
/-- **Vanishing of a higher direct image through a limit.** Let `k : W ⟶ S`, `G` a sheaf on `W`,
and `T = lim T_i` a cofiltered limit of schemes over `W` with affine transition morphisms, all
quasi-compact and quasi-separated over `S`. Let `V` be a scheme over `W` receiving a morphism
from some `T_{i₀}`, such that all the transition maps
`R^q (V → S)_* (G|_V) ⟶ R^q (T_i → S)_* (G|_{T_i})`
are monomorphisms. If `R^q (T → S)_* (G|_T) = 0`, then `R^q (V → S)_* (G|_V) = 0`.

On every geometric stalk, an element `y` maps to some `T_{i₀}` and then to zero over `T`, hence
by the limit theorem `AlgebraicGeometry.Etale.higherDirectImage_limit` it dies at some stage
`T_j`; the transition map to that stage being injective, `y = 0`. -/
theorem Etale.isZero_higherDirectImage_of_isLimit_of_mono {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Over W) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)] [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)] (q : ℤ) {V : Over W}
    {i₀ : I} (τ : D.obj i₀ ⟶ V)
    (hmono : ∀ (i : I) (ψ : D.obj i ⟶ V), Mono (Etale.higherDirectImageOverMap Λ k G q ψ))
    (hT : IsZero (Etale.higherDirectImage Λ (c.pt.hom ≫ k) q
      ((c.pt.hom)^*[ModuleCat.{u + 1} Λ].obj G))) :
    IsZero (Etale.higherDirectImage Λ (V.hom ≫ k) q ((V.hom)^*[ModuleCat.{u + 1} Λ].obj G)) := by
  have : LocallySmall.{u + 1} S.Etale := locallySmall_max.{u + 1, u}
  let R := Etale.higherDirectImage Λ (V.hom ≫ k) q ((V.hom)^*[ModuleCat.{u + 1} Λ].obj G)
  suffices h : IsIso (0 : R ⟶ 0) from IsZero.of_iso (isZero_zero _) (asIso (0 : R ⟶ 0))
  refine Scheme.isIso_of_isIso_sheafFiber_map _ fun s ↦ ?_
  let fib := (S.uliftPointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have : PreservesFiniteLimits fib := inferInstance
  have : fib.IsLeftAdjoint := inferInstance
  have hz : IsZero (fib.obj R) := by
    refine ModuleCat.isZero_iff_subsingleton.2 ⟨fun y₁ y₂ ↦ ?_⟩
    suffices h : ∀ y : fib.obj R, y = 0 by rw [h y₁, h y₂]
    intro y
    let y' := (fib.map (Etale.higherDirectImageOverMap Λ k G q τ)).hom y
    have h0 : (fib.map (Etale.higherDirectImageOverMap Λ k G q (c.π.app i₀))).hom y' = 0 :=
      (ModuleCat.isZero_iff_subsingleton.1 (fib.map_isZero hT)).elim _ _
    obtain ⟨j, g, hg⟩ := (Etale.higherDirectImage_limit Λ k G D c hc q s).2 i₀ y' h0
    have := hmono j (D.map g ≫ τ)
    refine ((ModuleCat.mono_iff_injective (fib.map
      (Etale.higherDirectImageOverMap Λ k G q (D.map g ≫ τ)))).1 inferInstance) ?_
    have hcomp : fib.map (Etale.higherDirectImageOverMap Λ k G q (D.map g ≫ τ)) =
        fib.map (Etale.higherDirectImageOverMap Λ k G q τ) ≫
          fib.map (Etale.higherDirectImageOverMap Λ k G q (D.map g)) := by
      rw [Etale.higherDirectImageOverMap_comp]
      exact fib.map_comp _ _
    rw [map_zero, hcomp]
    exact hg
  exact isIso_of_source_target_iso_zero _ hz.isoZero (fib.map_isZero (isZero_zero _)).isoZero

end AlgebraicGeometry

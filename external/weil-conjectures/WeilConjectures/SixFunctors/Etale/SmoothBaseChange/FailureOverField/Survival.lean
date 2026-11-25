/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.ClosedOpen
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Limit
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Colimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.EpiMono
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition

/-!
# Survival of a cokernel element under base change

An element `ξ` of a geometric stalk of `R^q h_* e⁻¹ F` that is not in the image of the
base-change map is transported along `π : T' ⟶ T` by the transition maps
`AlgebraicGeometry.Etale.baseChangeTargetTransition`; the property
`AlgebraicGeometry.Etale.SurvivesBaseChange` asks that its image is still not in the image of
the base-change map over `T'`. This file verifies the four hypotheses of the
minimal-counterexample lemma `AlgebraicGeometry.exists_spec_field_of_isQcqsLocalProperty` for
it: invariance under thickenings, compatibility with limits, the closed–open splitting and the
failure over the empty scheme.

## Main definitions

- `AlgebraicGeometry.Etale.SurvivesBaseChange`: the property "the chosen cokernel element
  survives" of schemes over `T`.

## Main statements

- `AlgebraicGeometry.Etale.isQcqsLocalProperty_survivesBaseChange`: that property satisfies
  the hypotheses of the minimal-counterexample lemma.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

section Survival

variable {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

/-- The property "the chosen cokernel element survives" of schemes `π : T' ⟶ T` over `T`.

Fix a Cartesian square `sq` with base `g : T ⟶ S`, a sheaf `F` on `T_ét`, a point `x` of `X`
and an element `ξ` of the stalk of `R^q h_* e⁻¹ F` at the geometric point over `x`. For
`π : T' ⟶ T` let `Y' = T' ×_S X`. The property holds for `π` if the image of `ξ` under the
transition map to the stalk of `R^q h'_* e'⁻¹ π⁻¹ F` is not in the image of the base-change
map of the square over `π ≫ g`. -/
def Etale.SurvivesBaseChange (q : ℤ) (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    ⦃T' : Scheme.{u}⦄ (π : T' ⟶ T) : Prop :=
  ((X.uliftPointSmallEtale x).sheafFiber.map
      (Etale.baseChangeTargetTransition Λ e h q π
        (sq.lift (pullback.fst (π ≫ g) p ≫ π) (pullback.snd (π ≫ g) p)
          (by rw [Category.assoc]; exact pullback.condition))
        (pullback.fst (π ≫ g) p) (pullback.snd (π ≫ g) p) (sq.lift_fst _ _ _)
        (sq.lift_snd _ _ _) F)).hom ξ ∉
    Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
      (Etale.baseChangeHomologyMap Λ (IsPullback.of_hasPullback (π ≫ g) p) q
        (((π)^*[ModuleCat.{u + 1} Λ]).obj F))).hom

variable {Λ}

/-- Along the identity of `T` the transition maps do not change the base-change map: an
element `ξ` not in the image of the base-change map over `T` survives along `𝟙 T`. -/
theorem Etale.survivesBaseChange_id (q : ℤ) (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    (hξ : ξ ∉ Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
      (Etale.baseChangeHomologyMap Λ sq q F)).hom) :
    Etale.SurvivesBaseChange Λ q sq F x ξ (𝟙 T) := by
  have hpb := IsPullback.of_hasPullback (𝟙 T ≫ g) p
  let a := sq.lift (pullback.fst (𝟙 T ≫ g) p ≫ 𝟙 T) (pullback.snd (𝟙 T ≫ g) p)
    (by rw [Category.assoc]; exact pullback.condition)
  have hc := Etale.baseChangeHomologyMap_comp_baseChangeTargetTransition Λ sq q (𝟙 T) hpb a
    (sq.lift_fst _ _ _) (sq.lift_snd _ _ _) F
  let b : Y ⟶ pullback (𝟙 T ≫ g) p :=
    pullback.lift e h (by rw [Category.id_comp]; exact sq.w)
  have hab : a ≫ b = 𝟙 _ := pullback.hom_ext (by simp [a, b]) (by simp [a, b])
  have hba : b ≫ a = 𝟙 _ := sq.hom_ext (by simp [a, b]) (by simp [a, b])
  have degT : CommSq a (pullback.snd (𝟙 T ≫ g) p) h (𝟙 X) :=
    ⟨by rw [sq.lift_snd, Category.comp_id]⟩
  have hT : IsIso (Etale.baseChangeTargetTransition Λ e h q (𝟙 T) a (pullback.fst (𝟙 T ≫ g) p)
      (pullback.snd (𝟙 T ≫ g) p) (sq.lift_fst _ _ _) (sq.lift_snd _ _ _) F) := by
    rw [Etale.baseChangeTargetTransition,
      Etale.lowerStarPlusTransition_eq_baseChange Λ a h _ (sq.lift_snd _ _ _) degT]
    have := fun K ↦ Etale.isIso_baseChange_app_of_inverses Λ degT b (𝟙 X) hab hba
      (Category.id_comp _) (Category.id_comp _) K
    infer_instance
  have degS : CommSq (𝟙 T) (𝟙 T ≫ g) g (𝟙 S) := ⟨by rw [Category.comp_id]⟩
  have hS : IsIso (Etale.baseChangeSourceTransition Λ p g q (𝟙 T) F) := by
    rw [Etale.baseChangeSourceTransition,
      Etale.lowerStarPlusTransition_eq_baseChange Λ (𝟙 T) g _ rfl degS]
    have := fun K ↦ Etale.isIso_baseChange_app_of_inverses Λ degS (𝟙 T) (𝟙 S)
      (Category.id_comp _) (Category.id_comp _) (Category.id_comp _) (Category.id_comp _) K
    infer_instance
  rintro ⟨η', hη'⟩
  apply hξ
  have hc' := congrArg (fun f ↦ ModuleCat.Hom.hom ((X.uliftPointSmallEtale x).sheafFiber.map f)) hc
  simp only [Functor.map_comp, ModuleCat.hom_comp] at hc'
  refine ⟨(inv ((X.uliftPointSmallEtale x).sheafFiber.map
    (Etale.baseChangeSourceTransition Λ p g q (𝟙 T) F))).hom η', ?_⟩
  apply ((ConcreteCategory.isIso_iff_bijective ((X.uliftPointSmallEtale x).sheafFiber.map
    (Etale.baseChangeTargetTransition Λ e h q (𝟙 T) a (pullback.fst (𝟙 T ≫ g) p)
      (pullback.snd (𝟙 T ≫ g) p) (sq.lift_fst _ _ _) (sq.lift_snd _ _ _) F))).1
        inferInstance).1
  have h1 := LinearMap.congr_fun hc' ((inv ((X.uliftPointSmallEtale x).sheafFiber.map
    (Etale.baseChangeSourceTransition Λ p g q (𝟙 T) F))).hom η')
  simp only [LinearMap.coe_comp, Function.comp_apply] at h1
  rw [← hη']
  convert h1 using 2
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, IsIso.inv_hom_id, ModuleCat.hom_id,
    LinearMap.id_apply]

/-- Step (1) of blueprint `lemma-reduction-field--1`: the survival of `ξ` is invariant under
thickenings. A thickening does not change the étale site (blueprint
`lemma-reduction-field`, `AlgebraicGeometry.Etale.isEquivalence_upperStar_of_thickening`),
so the transition maps along it are isomorphisms compatible with the base-change maps. -/
theorem Etale.survivesBaseChange_comp_iff_of_surjective (q : ℤ) (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    {T₁ T₂ : Scheme.{u}} (i : T₁ ⟶ T₂) [IsClosedImmersion i] (hi : Function.Surjective i.base)
    (f₂ : T₂ ⟶ T) :
    Etale.SurvivesBaseChange Λ q sq F x ξ (i ≫ f₂) ↔ Etale.SurvivesBaseChange Λ q sq F x ξ f₂ := by
  have : Surjective i := ⟨hi⟩
  -- the fibre products over `T₂` and over `T₁`
  have sq₂ := IsPullback.of_hasPullback (f₂ ≫ g) p
  have sq₁ := IsPullback.of_hasPullback ((i ≫ f₂) ≫ g) p
  obtain ⟨a', hae, hah⟩ : ∃ a' : pullback ((i ≫ f₂) ≫ g) p ⟶ pullback (f₂ ≫ g) p,
      a' ≫ pullback.fst (f₂ ≫ g) p = pullback.fst ((i ≫ f₂) ≫ g) p ≫ i ∧
        a' ≫ pullback.snd (f₂ ≫ g) p = pullback.snd ((i ≫ f₂) ≫ g) p :=
    ⟨pullback.lift (pullback.fst _ _ ≫ i) (pullback.snd _ _)
      ((Category.assoc _ _ _).trans (by rw [← Category.assoc i f₂ g]; exact pullback.condition)),
      by simp, by simp⟩
  have hpb : IsPullback (pullback.fst ((i ≫ f₂) ≫ g) p) a' i (pullback.fst (f₂ ≫ g) p) := by
    refine IsPullback.of_bot ?_ hae.symm sq₂
    rw [hah, ← Category.assoc]
    exact sq₁
  have : IsUniversalHomeomorphism a' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb inferInstance
  have ha : a' ≫ sq.lift (pullback.fst (f₂ ≫ g) p ≫ f₂) (pullback.snd (f₂ ≫ g) p)
      (by rw [Category.assoc]; exact pullback.condition) =
      sq.lift (pullback.fst ((i ≫ f₂) ≫ g) p ≫ i ≫ f₂) (pullback.snd ((i ≫ f₂) ≫ g) p)
        ((Category.assoc _ _ _).trans pullback.condition) :=
    sq.hom_ext (by simp [reassoc_of% hae]) (by simp [hah])
  unfold Etale.SurvivesBaseChange
  exact not_congr (Etale.mem_range_iff_of_isUniversalHomeomorphism Λ q F x ξ f₂ sq₂ _
    (sq.lift_fst _ _ _) (sq.lift_snd _ _ _) i sq₁ _ (sq.lift_fst _ _ _) (sq.lift_snd _ _ _) a'
    hae hah ha)

-- the transition maps are compared through large terms of the derived categories
/-- Step (2) of blueprint `lemma-reduction-field--1`: the survival of `ξ` passes to cofiltered
limits along affine transition morphisms. By the limit theorem for higher direct images
(blueprint `lemma-reduction-field`,
`AlgebraicGeometry.Etale.higherDirectImage_limit`) the stalks over the limit are the colimits
of the stalks over the stages, on both sides of the base-change map. -/
theorem Etale.survivesBaseChange_of_isLimit [IsAffine S] (q : ℤ) (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over T)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
    (c : Cone D) (hc : IsLimit ((Over.forget T).mapCone c))
    (hD : ∀ i, Etale.SurvivesBaseChange Λ q sq F x ξ (D.obj i).hom) :
    Etale.SurvivesBaseChange Λ q sq F x ξ c.pt.hom := by
  have hlf (U : Over T) :
      ((Etale.stageFunctor sq).obj U).hom ≫ e = pullback.fst (U.hom ≫ g) p ≫ U.hom :=
    sq.lift_fst _ _ _
  have hls (U : Over T) : ((Etale.stageFunctor sq).obj U).hom ≫ h = pullback.snd (U.hom ≫ g) p :=
    sq.lift_snd _ _ _
  have sqU (U : Over T) : IsPullback (pullback.fst (U.hom ≫ g) p)
      (((Etale.stageFunctor sq).obj U).hom ≫ h) (U.hom ≫ g) p := by
    rw [hls]; exact IsPullback.of_hasPullback _ _
  have hconv (U : Over T) : Etale.SurvivesBaseChange Λ q sq F x ξ U.hom ↔
      ((X.uliftPointSmallEtale x).sheafFiber.map ((DerivedCategory.Plus.homologyFunctor _ q).map
        (Etale.targetTransitionPlus Λ e h U.hom ((Etale.stageFunctor sq).obj U).hom
          (pullback.fst (U.hom ≫ g) p) (((Etale.stageFunctor sq).obj U).hom ≫ h) (hlf U) rfl
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))).hom ξ ∉
      Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
        ((DerivedCategory.Plus.homologyFunctor _ q).map
          ((Etale.baseChange (ModuleCat.{u + 1} Λ) (sqU U).toCommSq).app
            (D+((U.hom)^*[ModuleCat.{u + 1} Λ]).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))).hom := by
    rw [← Etale.mem_range_baseChangeHomologyMap_iff Λ q F x ξ U.hom _ _ (sqU U) _ (hlf U) rfl]
    exact not_congr (Etale.mem_range_baseChangeHomologyMap_congr Λ q F x ξ U.hom _ _ _ _ _ _
      (hlf U) (hls U) rfl)
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom ((D ⋙ Over.forget T).map f) :=
    fun f ↦ (inferInstance : IsAffineHom (D.map f).left)
  have : ∀ i, CompactSpace ((D ⋙ Over.forget T).obj i) :=
    fun i ↦ (inferInstance : CompactSpace (D.obj i).left)
  have i₀ : I := IsCofiltered.nonempty.some
  have : IsAffineHom (c.π.app i₀).left :=
    isAffineHom_π_app (D ⋙ Over.forget T) ((Over.forget T).mapCone c) hc i₀
  have : CompactSpace c.pt.left :=
    Scheme.compactSpace_of_isLimit (D ⋙ Over.forget T) ((Over.forget T).mapCone c) hc
  have : QuasiSeparatedSpace c.pt.left := quasiSeparatedSpace_of_quasiSeparated (c.π.app i₀).left
  have hw (U V : Over T) (φ : U ⟶ V) : ((Etale.stageFunctor sq).map φ).left ≫
      pullback.fst (V.hom ≫ g) p = pullback.fst (U.hom ≫ g) p ≫ φ.left := by simp
  have hwh (U V : Over T) (φ : U ⟶ V) : ((Etale.stageFunctor sq).map φ).left ≫
      ((Etale.stageFunctor sq).obj V).hom ≫ h = ((Etale.stageFunctor sq).obj U).hom ≫ h := by
    rw [← Category.assoc, Over.w]
  rw [hconv]
  refine ModuleCat.notMem_range_of_forall_notMem_range
    (A := fun i ↦ (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).obj
      (D+((p)^*[ModuleCat.{u + 1} Λ]).obj (R+(((D.obj i).hom ≫ g)_*[ModuleCat.{u + 1} Λ]).obj
        (D+(((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj 
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))))
    (B := fun i ↦ (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).obj
      (R+((((Etale.stageFunctor sq).obj (D.obj i)).hom ≫ h)_*[ModuleCat.{u + 1} Λ]).obj
        (D+((pullback.fst ((D.obj i).hom ≫ g) p)^*[ModuleCat.{u + 1} Λ]).obj
          (D+(((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj 
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))))
    (φ := fun i ↦ (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) (sqU (D.obj i)).toCommSq).app
        (D+(((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj 
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))
    (tA := fun {i j} f ↦ (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).map
      (D+((p)^*[ModuleCat.{u + 1} Λ]).map (Etale.overLowerStarTransition Λ g (D.obj i).hom
        (D.obj j).hom (D.map f).left (Over.w (D.map f))
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))
    (tB := fun {i j} f ↦ (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).map
      (Etale.overTargetTransition Λ _ _ _ _ (D.obj i).hom (D.obj j).hom (D.map f).left
        ((Etale.stageFunctor sq).map (D.map f)).left (hw _ _ (D.map f)) (hwh _ _ (D.map f))
        (Over.w (D.map f)) ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    (sA := fun i ↦ (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).map
      (D+((p)^*[ModuleCat.{u + 1} Λ]).map (Etale.overLowerStarTransition Λ g (D.obj i).hom c.pt.hom
        (c.π.app i).left (Over.w (c.π.app i)) ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))
    (sB := fun i ↦ (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).map
      (Etale.overTargetTransition Λ (pullback.fst ((D.obj i).hom ≫ g) p)
        (((Etale.stageFunctor sq).obj (D.obj i)).hom ≫ h) (pullback.fst (c.pt.hom ≫ g) p)
        (((Etale.stageFunctor sq).obj c.pt).hom ≫ h) (D.obj i).hom c.pt.hom (c.π.app i).left
        ((Etale.stageFunctor sq).map (c.π.app i)).left (hw c.pt (D.obj i) (c.π.app i))
        (hwh c.pt (D.obj i) (c.π.app i))
        (Over.w (c.π.app i)) ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    (τ := fun i ↦ (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).map
      (Etale.targetTransitionPlus Λ e h (D.obj i).hom ((Etale.stageFunctor sq).obj (D.obj i)).hom
        (pullback.fst ((D.obj i).hom ≫ g) p) (((Etale.stageFunctor sq).obj (D.obj i)).hom ≫ h)
        (hlf (D.obj i)) rfl ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    (Al := (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).obj
      (D+((p)^*[ModuleCat.{u + 1} Λ]).obj (R+((c.pt.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).obj
        (D+((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj 
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))))
    (Bl := (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).obj
      (R+((((Etale.stageFunctor sq).obj c.pt).hom ≫ h)_*[ModuleCat.{u + 1} Λ]).obj
        (D+((pullback.fst (c.pt.hom ≫ g) p)^*[ModuleCat.{u + 1} Λ]).obj
          (D+((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj 
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))))
    (φl := (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) (sqU c.pt).toCommSq).app
        (D+((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj 
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))
    (τl := (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).map
      (Etale.targetTransitionPlus Λ e h c.pt.hom ((Etale.stageFunctor sq).obj c.pt).hom
        (pullback.fst (c.pt.hom ≫ g) p) (((Etale.stageFunctor sq).obj c.pt).hom ≫ h)
        (hlf c.pt) rfl ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    (hτ := ?_) (hτl := ?_) (hφ := ?_) (hφl := ?_) (hsA := ?_) (hA := ?_) (hB := ?_)
    (hξ := fun i ↦ (hconv (D.obj i)).1 (hD i))
  case refine_1 =>
    intro i j f
    rw [← Functor.map_comp, Etale.targetTransitionPlus_comp_overTargetTransition Λ e h
      _ _ _ _ _ _ _ _ (hlf _) rfl (hlf _) rfl _ _ _ _ _
      (Over.w ((Etale.stageFunctor sq).map (D.map f)))]
  case refine_2 =>
    intro i
    rw [← Functor.map_comp]
    exact congrArg _ (Etale.targetTransitionPlus_comp_overTargetTransition Λ e h
      (pullback.fst ((D.obj i).hom ≫ g) p) (((Etale.stageFunctor sq).obj (D.obj i)).hom ≫ h)
      (pullback.fst (c.pt.hom ≫ g) p) (((Etale.stageFunctor sq).obj c.pt).hom ≫ h) (D.obj i).hom
      c.pt.hom _ _ (hlf _) rfl (hlf c.pt) rfl (c.π.app i).left
      ((Etale.stageFunctor sq).map (c.π.app i)).left (hw c.pt (D.obj i) (c.π.app i))
      (hwh c.pt (D.obj i) (c.π.app i)) (Over.w (c.π.app i))
      (Over.w ((Etale.stageFunctor sq).map (c.π.app i))) _)
  case refine_3 =>
    intro i j f
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (Etale.baseChange_app_comp_overTargetTransition Λ g
      (sqU (D.obj i)).toCommSq (sqU (D.obj j)).toCommSq _ _ (hw _ _ (D.map f)) (hwh _ _ (D.map f))
      (Over.w (D.map f)) _)
  case refine_4 =>
    intro i
    exact (Functor.map_comp _ _ _).symm.trans ((congrArg _
      (Etale.baseChange_app_comp_overTargetTransition Λ g
      (sqU (D.obj i)).toCommSq (sqU c.pt).toCommSq _ _ (hw c.pt (D.obj i) (c.π.app i))
      (hwh c.pt (D.obj i) (c.π.app i)) (Over.w (c.π.app i)) _)).trans (Functor.map_comp _ _ _))
  case refine_5 =>
    intro i j f
    exact (Functor.map_comp _ _ _).symm.trans (congrArg _ ((Functor.map_comp _ _ _).symm.trans
      (congrArg _ (Etale.overLowerStarTransition_comp Λ g (D.obj i).hom (D.obj j).hom c.pt.hom
        (D.map f).left (c.π.app j).left (c.π.app i).left (Over.w (D.map f)) (Over.w (c.π.app j))
        (Over.w (c.π.app i)) (by rw [← Over.comp_left, c.w f]) _))))
  case refine_6 =>
    have lim := Etale.higherDirectImage_limit Λ g F D c hc q
    intro y
    refine ModuleCat.mem_iSup_range_of_comm _
      (fun i ↦ (X.uliftPointSmallEtale x).sheafFiber.map (((p)^*[ModuleCat.{u + 1} Λ]).map
        (Etale.higherDirectImageOverMap Λ g F q (c.π.app i))))
      (fun i ↦ (X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.sourceStageIso Λ p g F q (D.obj i)).hom)
      ((X.uliftPointSmallEtale x).sheafFiber.mapIso (Etale.sourceStageIso Λ p g F q c.pt))
      (fun i ↦ ?_) y
      (Etale.mem_iSup_range_sheafFiber_map_upperStar Λ p x _ _ (fun s y ↦ (lim s).1 y) _)
    exact Etale.sheafFiber_map_sourceStageIso_naturality Λ p g F q (c.π.app i) x
  case refine_7 =>
    have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom ((D ⋙ Etale.stageFunctor sq).map f).left :=
      fun f ↦ (inferInstance : IsAffineHom ((Etale.stageFunctor sq).map (D.map f)).left)
    have : ∀ i, QuasiCompact (((D ⋙ Etale.stageFunctor sq).obj i).hom ≫ h) := fun i ↦ by
      change QuasiCompact (((Etale.stageFunctor sq).obj (D.obj i)).hom ≫ h)
      rw [hls]; infer_instance
    have : ∀ i, QuasiSeparated (((D ⋙ Etale.stageFunctor sq).obj i).hom ≫ h) := fun i ↦ by
      change QuasiSeparated (((Etale.stageFunctor sq).obj (D.obj i)).hom ≫ h)
      rw [hls]; infer_instance
    have : QuasiCompact (((Etale.stageFunctor sq).mapCone c).pt.hom ≫ h) := by
      change QuasiCompact (((Etale.stageFunctor sq).obj c.pt).hom ≫ h)
      rw [hls]; infer_instance
    have : QuasiSeparated (((Etale.stageFunctor sq).mapCone c).pt.hom ≫ h) := by
      change QuasiSeparated (((Etale.stageFunctor sq).obj c.pt).hom ≫ h)
      rw [hls]; infer_instance
    have lim := Etale.higherDirectImage_limit Λ h (((e)^*[ModuleCat.{u + 1} Λ]).obj F)
      (D ⋙ Etale.stageFunctor sq) ((Etale.stageFunctor sq).mapCone c)
      (Etale.isLimitStageFunctorMapCone sq c hc) q x
    intro i b hb
    have h₁ := congrArg (fun m ↦ m.hom b)
      (Etale.sheafFiber_map_stageTargetTransition Λ sq F q x (U := c.pt) (c.π.app i))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₁
    obtain ⟨j, f, hf⟩ := lim.2 i _ (h₁.symm.trans ((congrArg _ hb).trans (map_zero _)))
    refine ⟨j, f, ?_⟩
    have h₂ := congrArg (fun m ↦ m.hom b)
      (Etale.sheafFiber_map_stageTargetTransition Λ sq F q x (D.map f))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₂
    exact (injective_iff_map_eq_zero _).1
      ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1 _ (h₂.trans hf)


/-- Step (3) of blueprint `lemma-reduction-field--1`: if `ξ` survives over a quasi-compact
quasi-separated `T'` and `Z ⊆ T'` is closed with quasi-compact complement `V`, then `ξ`
survives over `V` or over `Z`. Embed `π⁻¹ F` into `j_* J ⊕ i_* i⁻¹ π⁻¹ F` with `J` injective
on `V`; by `AlgebraicGeometry.Etale.mono_cokernelMap` the image of `ξ` survives in one of the
summands. For the closed summand use the exactness of `i_*`; for the open summand use the
universal base-change property in degrees `< q` for the base change of `p` along `T' ⟶ S`,
the Leray spectral sequence, and `AlgebraicGeometry.Etale.mono_cokernelDesc`. -/
theorem Etale.survivesBaseChange_or_of_isClosedImmersion [IsAffine S] (q : ℤ) (hq : 1 ≤ q)
    (hprev : ∀ q' < q, Etale.UniversalBaseChangeProperty Λ p q') (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    {T' Z : Scheme.{u}} [CompactSpace T'] [QuasiSeparatedSpace T'] (f : T' ⟶ T)
    (V : T'.Opens) (hV : IsCompact (V : Set T')) (i : Z ⟶ T') [IsClosedImmersion i]
    (hi : Set.range i.base = (V : Set T')ᶜ) (hf : Etale.SurvivesBaseChange Λ q sq F x ξ f) :
    Etale.SurvivesBaseChange Λ q sq F x ξ (V.ι ≫ f) ∨
      Etale.SurvivesBaseChange Λ q sq F x ξ (i ≫ f) := by
  have : LocallySmall.{u + 1} X.Etale := locallySmall_max.{u + 1, u}
  have : PreservesFiniteLimits ((X.uliftPointSmallEtale x).sheafFiber
    (A := ModuleCat.{u + 1} Λ)) := inferInstance
  have : PreservesFiniteColimits ((X.uliftPointSmallEtale x).sheafFiber
    (A := ModuleCat.{u + 1} Λ)) := inferInstance
  have : ((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)).Additive :=
    Functor.additive_of_preserves_binary_products _
  -- quasi-compactness and quasi-separatedness
  have : QuasiCompact (f ≫ g) := (quasiCompact_iff_compactSpace _).2 inferInstance
  have : QuasiSeparated (f ≫ g) :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated)).2 inferInstance
  have : CompactSpace V := isCompact_iff_compactSpace.1 hV
  have : QuasiCompact V.ι := (quasiCompact_iff_compactSpace _).2 inferInstance
  have hrange : Set.range i.base = (Set.range V.ι.base)ᶜ := by
    rw [hi]
    congr
    exact (Scheme.Opens.range_ι V).symm
  -- the base-change properties in lower degrees
  have hprev' : Etale.BaseChangeProperty Λ p (q - 1) :=
    (hprev (q - 1) (by lia)).baseChangeProperty
  have sq₂ := IsPullback.of_hasPullback (f ≫ g) p
  have hbc : ∀ a < q, Etale.BaseChangeProperty Λ (pullback.fst (f ≫ g) p) a :=
    fun a ha ↦ hprev a ha _ _ _ sq₂.flip
  have : (Etale.baseChangeTargetFunctor Λ (pullback.fst (f ≫ g) p) (pullback.snd (f ≫ g) p)
      q).Additive := by
    unfold Etale.baseChangeTargetFunctor
    infer_instance
  -- the fibre products over `V` and over `Z`
  have sqV : IsPullback (pullback.fst ((V.ι ≫ f) ≫ g) p)
      (pullback.lift (pullback.fst ((V.ι ≫ f) ≫ g) p ≫ V.ι) (pullback.snd ((V.ι ≫ f) ≫ g) p)
        (by simpa using (pullback.condition :
          pullback.fst ((V.ι ≫ f) ≫ g) p ≫ (V.ι ≫ f) ≫ g = _))) V.ι
      (pullback.fst (f ≫ g) p) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback (f ≫ g) p)
    rw [pullback.lift_snd, ← Category.assoc]
    exact IsPullback.of_hasPullback _ _
  have sqZ : IsPullback (pullback.fst ((i ≫ f) ≫ g) p)
      (pullback.lift (pullback.fst ((i ≫ f) ≫ g) p ≫ i) (pullback.snd ((i ≫ f) ≫ g) p)
        (by simpa using (pullback.condition :
          pullback.fst ((i ≫ f) ≫ g) p ≫ (i ≫ f) ≫ g = _))) i
      (pullback.fst (f ≫ g) p) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback (f ≫ g) p)
    rw [pullback.lift_snd, ← Category.assoc]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨βV, hβViso, hβV⟩ := Etale.exists_baseChangeTargetTransition_comp_eq Λ q F f
    (sq.lift (pullback.fst (f ≫ g) p ≫ f) (pullback.snd (f ≫ g) p)
      (by rw [Category.assoc]; exact pullback.condition)) (sq.lift_fst _ _ _) (sq.lift_snd _ _ _)
    V.ι (sq.lift (pullback.fst ((V.ι ≫ f) ≫ g) p ≫ V.ι ≫ f) (pullback.snd ((V.ι ≫ f) ≫ g) p)
      ((Category.assoc _ _ _).trans pullback.condition)) (sq.lift_fst _ _ _) (sq.lift_snd _ _ _)
    _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (sq.hom_ext (by simp) (by simp)) sqV.toCommSq
  obtain ⟨βZ, hβZiso, hβZ⟩ := Etale.exists_baseChangeTargetTransition_comp_eq Λ q F f
    (sq.lift (pullback.fst (f ≫ g) p ≫ f) (pullback.snd (f ≫ g) p)
      (by rw [Category.assoc]; exact pullback.condition)) (sq.lift_fst _ _ _) (sq.lift_snd _ _ _)
    i (sq.lift (pullback.fst ((i ≫ f) ≫ g) p ≫ i ≫ f) (pullback.snd ((i ≫ f) ≫ g) p)
      ((Category.assoc _ _ _).trans pullback.condition)) (sq.lift_fst _ _ _) (sq.lift_snd _ _ _)
    _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (sq.hom_ext (by simp) (by simp)) sqZ.toCommSq
  -- an injective sheaf on `V` containing `(V.ι ≫ f)^* F`
  obtain ⟨J, ι, _, _⟩ : ∃ (J : Sheaf V.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (ι : ((V.ι ≫ f)^*[ModuleCat.{u + 1} Λ]).obj F ⟶ J), Injective J ∧ Mono ι :=
    ⟨_, Injective.ι _, inferInstance, inferInstance⟩
  have hα₁ : ((V.ι)^*[ModuleCat.{u + 1} Λ]).map (βV ≫ ((V.ι)_*[ModuleCat.{u + 1} Λ]).map ι) ≫
      (Etale.upperStarLowerStarAdjunction _ V.ι).counit.app J =
      (((V.ι)^*[ModuleCat.{u + 1} Λ]).map βV ≫
        (Etale.upperStarLowerStarAdjunction _ V.ι).counit.app
          (((V.ι ≫ f)^*[ModuleCat.{u + 1} Λ]).obj F)) ≫ ι := by
    rw [Functor.map_comp, Category.assoc]
    erw [(Etale.upperStarLowerStarAdjunction _ V.ι).counit.naturality ι]
    rw [Category.assoc]
    rfl
  have : Mono (((V.ι)^*[ModuleCat.{u + 1} Λ]).map (βV ≫ ((V.ι)_*[ModuleCat.{u + 1} Λ]).map ι) ≫
      (Etale.upperStarLowerStarAdjunction _ V.ι).counit.app J) := by
    have := hβViso
    rw [hα₁]
    infer_instance
  have := hβZiso
  have hα := Etale.mono_biprod_lift Λ V.ι i hrange (βV ≫ ((V.ι)_*[ModuleCat.{u + 1} Λ]).map ι) βZ
  have hcok := Etale.mono_cokernelMap Λ q hq hprev' (IsPullback.of_hasPullback (f ≫ g) p)
    (biprod.lift (βV ≫ ((V.ι)_*[ModuleCat.{u + 1} Λ]).map ι) βZ)
  unfold Etale.SurvivesBaseChange at hf ⊢
  have key := fun y ↦ mem_range_of_mono_cokernelMap
    ((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ))
    (Etale.baseChangeHomologyMap Λ (IsPullback.of_hasPullback (f ≫ g) p) q
      (((f)^*[ModuleCat.{u + 1} Λ]).obj F))
    (Etale.baseChangeHomologyMap Λ (IsPullback.of_hasPullback (f ≫ g) p) q _)
    ((Etale.baseChangeSourceFunctor Λ p (f ≫ g) q).map
      (biprod.lift (βV ≫ ((V.ι)_*[ModuleCat.{u + 1} Λ]).map ι) βZ))
    ((Etale.baseChangeTargetFunctor Λ (pullback.fst (f ≫ g) p) (pullback.snd (f ≫ g) p) q).map
      (biprod.lift (βV ≫ ((V.ι)_*[ModuleCat.{u + 1} Λ]).map ι) βZ))
    (Etale.baseChangeHomologyMap_naturality Λ _ q _) y
  have hη := fun hmem ↦ hf (key _ hmem)
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨hVin, hZin⟩ := hcon
  rw [← hβV, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply] at hVin
  rw [← hβZ, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply] at hZin
  apply hη
  refine mem_range_of_decomp ((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ))
    (fun G ↦ Etale.baseChangeHomologyMap Λ (IsPullback.of_hasPullback (f ≫ g) p) q G)
    (Etale.baseChangeHomologyMap_naturality Λ _ q) biprod.fst biprod.snd
    biprod.inl biprod.inr biprod.total _ ?_ ?_
  · by_contra hA
    refine Etale.notMem_range_of_baseChangeProperty Λ (IsPullback.of_hasPullback (f ≫ g) p)
      V.ι ((V.ι ≫ f) ≫ g) (IsPullback.of_hasPullback _ _) _ (pullback.lift_snd _ _ _) sqV q hq
      hbc βV ι x _ ?_ hVin
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp, biprod.lift_fst] at hA
    exact hA
  · by_contra hB
    refine Etale.notMem_range_of_isFinite Λ (IsPullback.of_hasPullback (f ≫ g) p)
      i ((i ≫ f) ≫ g) (Category.assoc _ _ _).symm (IsPullback.of_hasPullback _ _) _
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) sqZ q βZ x _ ?_ hZin
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp, biprod.lift_snd] at hB
    exact hB

/-- Step (4) of blueprint `lemma-reduction-field--1`: nothing survives over the empty scheme,
since there the fibre `T' ×_S X` is empty and `R^q h'_* e'⁻¹ π⁻¹ F` vanishes. -/
theorem Etale.not_survivesBaseChange_of_isEmpty (q : ℤ) (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    {T' : Scheme.{u}} (π : T' ⟶ T) [IsEmpty T'] :
    ¬ Etale.SurvivesBaseChange Λ q sq F x ξ π := by
  intro hP
  apply hP
  have : IsEmpty ↥(pullback (π ≫ g) p) :=
    ⟨fun y ↦ isEmptyElim ((pullback.fst (π ≫ g) p).base y)⟩
  have hsheaf (G : Sheaf (pullback (π ≫ g) p).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      IsZero G := by
    refine (IsZero.iff_id_eq_zero G).2 (IsTerminal.hom_ext ?_ _ _)
    refine IsTerminal.isTerminalOfObj (sheafToPresheaf _ _) _ (Functor.isTerminal fun U ↦ ?_)
    have : IsEmpty U.unop.left :=
      ⟨fun y ↦ isEmptyElim (show ↥(pullback (π ≫ g) p) from U.unop.hom.base y)⟩
    exact Scheme.Etale.isTerminalSectionsOfIsEmpty G U.unop
  have hK (K : DerivedCategory.Plus
      (Sheaf (pullback (π ≫ g) p).smallEtaleTopology (ModuleCat.{u + 1} Λ))) : IsZero K :=
    IsZero.of_full_of_faithful_of_isZero DerivedCategory.Plus.ι K
      (DerivedCategory.isZero_of_forall_isZero_homology _ fun _ ↦ hsheaf _)
  have : R+((pullback.snd (π ≫ g) p)_*[ModuleCat.{u + 1} Λ]).IsRightAdjoint :=
    (Etale.derivedUpperStarLowerStarAdjunctionPlus _ _).isRightAdjoint
  have hzero : IsZero ((Etale.baseChangeTargetFunctor Λ (pullback.fst (π ≫ g) p)
      (pullback.snd (π ≫ g) p) q).obj (((π)^*[ModuleCat.{u + 1} Λ]).obj F)) :=
    (DerivedCategory.Plus.homologyFunctor _ q).map_isZero
      (R+((pullback.snd (π ≫ g) p)_*[ModuleCat.{u + 1} Λ]).map_isZero (hK _))
  have : LocallySmall.{u + 1} X.Etale := locallySmall_max.{u + 1, u}
  have : ((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)).IsLeftAdjoint :=
    inferInstance
  have := (ModuleCat.isZero_iff_subsingleton.1
    (((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)).map_isZero hzero))
  exact ⟨0, Subsingleton.elim _ _⟩

/-- The property "the chosen cokernel element survives" satisfies the hypotheses of the
minimal-counterexample lemma `AlgebraicGeometry.exists_spec_field_of_isQcqsLocalProperty`. -/
theorem Etale.isQcqsLocalProperty_survivesBaseChange [IsAffine S] (q : ℤ) (hq : 1 ≤ q)
    (hprev : ∀ q' < q, Etale.UniversalBaseChangeProperty Λ p q') (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ)) :
    T.IsQcqsLocalProperty (Etale.SurvivesBaseChange Λ q sq F x ξ) where
  invariant_under_thickening i _ hi f₂ :=
    Etale.survivesBaseChange_comp_iff_of_surjective q sq F x ξ i hi f₂
  compatible_with_cofilteredLimit D _ _ _ c hc hD :=
    Etale.survivesBaseChange_of_isLimit q sq F x ξ D c hc hD
  of_opens_or_closedComplement f V hV i _ hi hf :=
    Etale.survivesBaseChange_or_of_isClosedImmersion q hq hprev sq F x ξ f V hV i hi hf
  not_of_isEmpty π _ :=
    Etale.not_survivesBaseChange_of_isEmpty q sq F x ξ π

end Survival

end AlgebraicGeometry

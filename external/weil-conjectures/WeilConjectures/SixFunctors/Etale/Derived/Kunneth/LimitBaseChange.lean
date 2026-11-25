/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.VaryingBase
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.Transport
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.DescentLimit

/-!
# Base change along limits of Cartesian squares

Let `I` be a cofiltered category and `i ↦ (Yᵢ, Xᵢ, Tᵢ, Sᵢ)` an inverse system of Cartesian
squares

```
Yᵢ --eᵢ--> Tᵢ
|          |
hᵢ         gᵢ
v          v
Xᵢ --pᵢ--> Sᵢ
```

with affine transition morphisms and `gᵢ` quasi-compact quasi-separated, with limit square
`(Y, X, T, S)`. If the degree-`q` base-change map
`pᵢ⁻¹ R^q gᵢ_* Fᵢ ⟶ R^q hᵢ_* eᵢ⁻¹ Fᵢ` is an isomorphism at every stage, then so is the one of
the limit square (blueprint `corollary-open-direct-image-over-field--2`, Stacks 0EZT). As an
application, smooth base change holds along limits of smooth schemes (blueprint
`corollary-open-direct-image-over-field--2`, Stacks 0F09).

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit`: the limit statement for
  coefficients pulled back from a fixed scheme `W`.
- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit_of_forall`: the limit
  statement when the stage maps are isomorphisms for all coefficient sheaves.
- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit_smooth`: smooth base change
  along a limit of smooth schemes.

## References

- Stacks Project, Lemma 59.88.3, <https://stacks.math.columbia.edu/tag/0EZT>
- Stacks Project, Lemma 59.89.3, <https://stacks.math.columbia.edu/tag/0F09>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `corollary-open-direct-image-over-field--2`: Higher direct images along limits of
cartesian squares.

Let `i ↦ (Yᵢ, Xᵢ, Tᵢ, Sᵢ)` be a cofiltered system of Cartesian squares
`IsPullback (e.app i) (h.app i) (g.app i) (p.app i)` with affine transition morphisms and every
`g.app i` quasi-compact quasi-separated, all `Sᵢ` and `Xᵢ` quasi-compact quasi-separated,
and let `sq₀ : IsPullback e₀ h₀ g₀ p₀` be a Cartesian
square of limits (the four limit cones being compatible with the four morphisms), with `g₀`
quasi-compact quasi-separated. Let `G` be a sheaf on a scheme `W` to which the system `T` maps.
If for a fixed degree `q` every base-change map `pᵢ⁻¹ R^q gᵢ_* (G|_{Tᵢ}) ⟶ R^q hᵢ_* eᵢ⁻¹ (G|_{Tᵢ})`
is an isomorphism, then so is `p₀⁻¹ R^q g₀_* (G|_T) ⟶ R^q h₀_* e₀⁻¹ (G|_T)`.

The hypotheses that the `Sᵢ` and `Xᵢ` are quasi-compact and quasi-separated are not in the
blueprint. They could be removed by localising on `S_{i₀}` and `X_{i₀}`, and every use of this
lemma satisfies them. -/
@[stacks 0EZT]
theorem Etale.isIso_baseChangeHomologyMap_of_isLimit {I : Type u} [Category.{u} I]
    [IsCofiltered I] {S X T Y : I ⥤ Scheme.{u}} (p : X ⟶ S) (g : T ⟶ S) (e : Y ⟶ T)
    (h : Y ⟶ X) (hsq : ∀ i, IsPullback (e.app i) (h.app i) (g.app i) (p.app i))
    [∀ i, QuasiCompact (g.app i)] [∀ i, QuasiSeparated (g.app i)]
    [∀ i, CompactSpace (S.obj i)] [∀ i, QuasiSeparatedSpace (S.obj i)]
    [∀ i, CompactSpace (X.obj i)] [∀ i, QuasiSeparatedSpace (X.obj i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (S.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (T.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (Y.map f)]
    {cS : Cone S} (hS : IsLimit cS) {cX : Cone X} (hX : IsLimit cX)
    {cT : Cone T} (hT : IsLimit cT) {cY : Cone Y} (hY : IsLimit cY)
    {p₀ : cX.pt ⟶ cS.pt} {g₀ : cT.pt ⟶ cS.pt} {e₀ : cY.pt ⟶ cT.pt} {h₀ : cY.pt ⟶ cX.pt}
    (hp₀ : ∀ i, p₀ ≫ cS.π.app i = cX.π.app i ≫ p.app i)
    (hg₀ : ∀ i, g₀ ≫ cS.π.app i = cT.π.app i ≫ g.app i)
    (he₀ : ∀ i, e₀ ≫ cT.π.app i = cY.π.app i ≫ e.app i)
    (hh₀ : ∀ i, h₀ ≫ cX.π.app i = cY.π.app i ≫ h.app i)
    (sq₀ : IsPullback e₀ h₀ g₀ p₀) [QuasiCompact g₀] [QuasiSeparated g₀]
    {W : Scheme.{u}} (w : T ⟶ (Functor.const I).obj W) (w₀ : cT.pt ⟶ W)
    (hw₀ : ∀ i, cT.π.app i ≫ w.app i = w₀)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (H : ∀ i, IsIso (Etale.baseChangeHomologyMap Λ (hsq i) q
      (((w.app i)^*[ModuleCat.{u + 1} Λ]).obj G))) :
    IsIso (Etale.baseChangeHomologyMap Λ sq₀ q (((w₀)^*[ModuleCat.{u + 1} Λ]).obj G)) := by
  have : ∀ i, QuasiCompact (h.app i) := fun i ↦
    MorphismProperty.of_isPullback (hsq i) inferInstance
  have : ∀ i, QuasiSeparated (h.app i) := fun i ↦
    MorphismProperty.of_isPullback (hsq i) inferInstance
  have : QuasiCompact h₀ := MorphismProperty.of_isPullback sq₀ inferInstance
  have : QuasiSeparated h₀ := MorphismProperty.of_isPullback sq₀ inferInstance
  let K := (DerivedCategory.Plus.singleFunctor (Sheaf W.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0).obj G
  have hw' : ∀ i, cY.π.app i ≫ (e ≫ w).app i = e₀ ≫ w₀ := fun i ↦ by
    rw [NatTrans.comp_app, ← Category.assoc, ← he₀, Category.assoc, hw₀]
  let 𝒳 := Etale.varyingBaseSystem h hh₀ (e ≫ w) (e₀ ≫ w₀) hw'
  let 𝒜 := (Etale.varyingBaseSystem g hg₀ w w₀ hw₀).comapB p₀
  have h𝒳 := Etale.isStalkColimit_varyingBaseSystem Λ h hh₀ (e ≫ w) (e₀ ≫ w₀) hw' hX hY G q
  have h𝒜 := Etale.LimitStageSystem.isStalkColimit_comapB p₀ _
    (Etale.isStalkColimit_varyingBaseSystem Λ g hg₀ w w₀ hw₀ hS hT G q)
  let β (i : I) : Etale.LimitStage.Hom (𝒳.obj i) (𝒜.obj i) :=
    ⟨e.app i, p.app i, (hsq i).w, (hp₀ i).symm, rfl⟩
  let β₀ : Etale.LimitStage.Hom ⟨cY.pt, cX.pt, h₀, 𝟙 _, e₀ ≫ w₀⟩ 𝒜.pt :=
    ⟨e₀, p₀, sq₀.w, by simp [𝒜], rfl⟩
  have hβ (i : I) : IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.LimitStage.transition Λ (β i)).app K)) :=
    Etale.LimitStage.isIso_homology_transition_of_isIso Λ (β i) q K
      ((Etale.isIso_baseChangeHomologyMap_iff_upperStar Λ (hsq i) q (w.app i) G).1 (H i))
  have hβ₀ : IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.LimitStage.transition Λ β₀).app K)) := by
    refine Scheme.isIso_of_isIso_sheafFiber_map _ fun x ↦ ?_
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ModuleCat.IsElementwiseColimit.bijective_of_bijective
      (fun i ↦ (Etale.stalkHomology Λ q x).map ((Etale.LimitStage.transition Λ (β i)).app K))
      ((Etale.stalkHomology Λ q x).map ((Etale.LimitStage.transition Λ β₀).app K))
      (fun i ↦ ?_) (fun f ↦ ?_) (fun f ↦ ?_) (fun i ↦ ?_) (h𝒜 x) (h𝒳 x)
    · have hc : (𝒳.π i).comp (β i) = β₀.comp (𝒜.π i) :=
        Etale.LimitStage.Hom.ext (he₀ i).symm (hp₀ i).symm
      rw [← Functor.map_comp, ← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.comp_app,
        Etale.LimitStage.transition_comp, Etale.LimitStage.transition_comp, hc]
    · have hc : (β _).comp (𝒜.map f) = (𝒳.map f).comp (β _) :=
        Etale.LimitStage.Hom.ext (e.naturality f).symm (p.naturality f).symm
      rw [← Functor.map_comp, ← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.comp_app,
        Etale.LimitStage.transition_comp, Etale.LimitStage.transition_comp, hc]
    · rw [← Functor.map_comp, ← NatTrans.comp_app, Etale.LimitStage.transition_comp, 𝒜.w]
    · rw [Functor.comp_map]
      exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  rw [Etale.isIso_baseChangeHomologyMap_iff_upperStar Λ sq₀ q w₀ G]
  exact Etale.LimitStage.isIso_homology_baseChange_of_isIso Λ β₀ q K hβ₀

/-- Blueprint `corollary-open-direct-image-over-field--2`: Higher direct images along limits of
cartesian squares, for all coefficient sheaves.

In the situation of `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit`, if for a
fixed degree `q` every stage base-change map is an isomorphism for every sheaf of `Λ`-modules
on `Tᵢ`, then the base-change map of the limit square is an isomorphism for every sheaf `F` of
`Λ`-modules on `T`: such an `F` is the filtered colimit of the pullbacks of its direct images
to the stages (blueprint
`corollary-open-direct-image-over-field--2`). -/
@[stacks 0EZT]
theorem Etale.isIso_baseChangeHomologyMap_of_isLimit_of_forall {I : Type u} [Category.{u} I]
    [IsCofiltered I] {S X T Y : I ⥤ Scheme.{u}} (p : X ⟶ S) (g : T ⟶ S) (e : Y ⟶ T)
    (h : Y ⟶ X) (hsq : ∀ i, IsPullback (e.app i) (h.app i) (g.app i) (p.app i))
    [∀ i, QuasiCompact (g.app i)] [∀ i, QuasiSeparated (g.app i)]
    [∀ i, CompactSpace (S.obj i)] [∀ i, QuasiSeparatedSpace (S.obj i)]
    [∀ i, CompactSpace (X.obj i)] [∀ i, QuasiSeparatedSpace (X.obj i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (S.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (T.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (Y.map f)]
    {cS : Cone S} (hS : IsLimit cS) {cX : Cone X} (hX : IsLimit cX)
    {cT : Cone T} (hT : IsLimit cT) {cY : Cone Y} (hY : IsLimit cY)
    {p₀ : cX.pt ⟶ cS.pt} {g₀ : cT.pt ⟶ cS.pt} {e₀ : cY.pt ⟶ cT.pt} {h₀ : cY.pt ⟶ cX.pt}
    (hp₀ : ∀ i, p₀ ≫ cS.π.app i = cX.π.app i ≫ p.app i)
    (hg₀ : ∀ i, g₀ ≫ cS.π.app i = cT.π.app i ≫ g.app i)
    (he₀ : ∀ i, e₀ ≫ cT.π.app i = cY.π.app i ≫ e.app i)
    (hh₀ : ∀ i, h₀ ≫ cX.π.app i = cY.π.app i ≫ h.app i)
    (sq₀ : IsPullback e₀ h₀ g₀ p₀) [QuasiCompact g₀] [QuasiSeparated g₀] (q : ℤ)
    (H : ∀ i (F : Sheaf (T.obj i).smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsIso (Etale.baseChangeHomologyMap Λ (hsq i) q F))
    (F : Sheaf cT.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq₀ q F) := by
  have : ∀ i, CompactSpace (T.obj i) := fun i ↦
    QuasiCompact.compactSpace_of_compactSpace (g.app i)
  have : ∀ i, QuasiSeparatedSpace (T.obj i) := fun i ↦
    quasiSeparatedSpace_of_quasiSeparated (g.app i)
  have : QuasiCompact h₀ := MorphismProperty.of_isPullback sq₀ inferInstance
  have : QuasiSeparated h₀ := MorphismProperty.of_isPullback sq₀ inferInstance
  have hc₀ := Etale.isColimitDescentCocone (Λ := Λ) hT F
  have := Etale.preservesFilteredColimitsOfSize_higherDirectImage Λ g₀ q
  have := Etale.preservesFilteredColimitsOfSize_higherDirectImage Λ h₀ q
  have := preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
    (DerivedCategory.Plus.singleFunctor (Sheaf cT.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
      R+((g₀)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.homologyFunctor _ q)
  have := preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
    (DerivedCategory.Plus.singleFunctor (Sheaf cY.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
      R+((h₀)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.homologyFunctor _ q)
  have : PreservesColimitsOfSize.{u, u} ((p₀)^*[ModuleCat.{u + 1} Λ]) :=
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p₀).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u, u} ((e₀)^*[ModuleCat.{u + 1} Λ]) :=
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) e₀).leftAdjoint_preservesColimits
  have : PreservesColimitsOfShape Iᵒᵖ (Etale.baseChangeSourceFunctor Λ p₀ g₀ q) :=
    preservesColimitsOfShape_of_natIso (Etale.baseChangeSourceFunctorIso Λ p₀ g₀ q).symm
  have : PreservesColimitsOfShape Iᵒᵖ (Etale.baseChangeTargetFunctor Λ e₀ h₀ q) :=
    preservesColimitsOfShape_of_natIso (Etale.baseChangeTargetFunctorIso Λ e₀ h₀ q).symm
  have : IsIso (Functor.whiskerLeft (Etale.descentDiagram (ModuleCat.{u + 1} Λ) cT F)
      (Etale.baseChangeHomologyNatTrans Λ sq₀ q)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro i
    -- the system over `Over i.unop`, with coefficients pulled back from `Tᵢ`
    let j := i.unop
    have : ∀ U : Over j, CompactSpace ((Over.forget j ⋙ S).obj U) := fun U ↦
      inferInstanceAs (CompactSpace (S.obj U.left))
    have : ∀ U : Over j, QuasiSeparatedSpace ((Over.forget j ⋙ S).obj U) := fun U ↦
      inferInstanceAs (QuasiSeparatedSpace (S.obj U.left))
    have : ∀ U : Over j, CompactSpace ((Over.forget j ⋙ X).obj U) := fun U ↦
      inferInstanceAs (CompactSpace (X.obj U.left))
    have : ∀ U : Over j, QuasiSeparatedSpace ((Over.forget j ⋙ X).obj U) := fun U ↦
      inferInstanceAs (QuasiSeparatedSpace (X.obj U.left))
    have : ∀ U : Over j, QuasiCompact ((Functor.whiskerLeft (Over.forget j) g).app U) :=
      fun U ↦ inferInstanceAs (QuasiCompact (g.app U.left))
    have : ∀ U : Over j, QuasiSeparated ((Functor.whiskerLeft (Over.forget j) g).app U) :=
      fun U ↦ inferInstanceAs (QuasiSeparated (g.app U.left))
    have : ∀ {U V : Over j} (φ : U ⟶ V), IsAffineHom ((Over.forget j ⋙ S).map φ) :=
      fun φ ↦ inferInstanceAs (IsAffineHom (S.map φ.left))
    have : ∀ {U V : Over j} (φ : U ⟶ V), IsAffineHom ((Over.forget j ⋙ X).map φ) :=
      fun φ ↦ inferInstanceAs (IsAffineHom (X.map φ.left))
    have : ∀ {U V : Over j} (φ : U ⟶ V), IsAffineHom ((Over.forget j ⋙ T).map φ) :=
      fun φ ↦ inferInstanceAs (IsAffineHom (T.map φ.left))
    have : ∀ {U V : Over j} (φ : U ⟶ V), IsAffineHom ((Over.forget j ⋙ Y).map φ) :=
      fun φ ↦ inferInstanceAs (IsAffineHom (Y.map φ.left))
    let w : Over.forget j ⋙ T ⟶ (Functor.const (Over j)).obj (T.obj j) :=
      { app U := T.map U.hom
        naturality U V φ := by
          simp only [Functor.comp_obj, Over.forget_obj, Functor.comp_map, Over.forget_map,
            Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, ← T.map_comp,
            Over.w φ] }
    exact Etale.isIso_baseChangeHomologyMap_of_isLimit Λ (Functor.whiskerLeft (Over.forget j) p)
      (Functor.whiskerLeft (Over.forget j) g) (Functor.whiskerLeft (Over.forget j) e)
      (Functor.whiskerLeft (Over.forget j) h) (fun U ↦ hsq U.left)
      ((Functor.Initial.isLimitWhiskerEquiv (Over.forget j) cS).symm hS)
      ((Functor.Initial.isLimitWhiskerEquiv (Over.forget j) cX).symm hX)
      ((Functor.Initial.isLimitWhiskerEquiv (Over.forget j) cT).symm hT)
      ((Functor.Initial.isLimitWhiskerEquiv (Over.forget j) cY).symm hY)
      (fun U ↦ hp₀ U.left) (fun U ↦ hg₀ U.left) (fun U ↦ he₀ U.left) (fun U ↦ hh₀ U.left) sq₀
      w (cT.π.app j) (fun U ↦ cT.w U.hom) _ q (fun U ↦ H U.left _)
  exact isIso_app_coconePt_of_preservesColimit _ _ _ hc₀

/-- The degree-`q` base-change map is an isomorphism at `F` if and only if it is one at a sheaf
isomorphic to `F`. -/
lemma Etale.isIso_baseChangeHomologyMap_iff_of_iso {X S T Y : Scheme.{u}} {p : X ⟶ S}
    {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X} (sq : IsPullback e h g p) (q : ℤ)
    {F F' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (i : F ≅ F') :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) ↔
      IsIso (Etale.baseChangeHomologyMap Λ sq q F') := by
  have n := Etale.baseChangeHomologyMap_naturality Λ sq q i.hom
  constructor
  · intro _
    rw [← IsIso.inv_comp_eq] at n
    rw [← n]
    infer_instance
  · intro _
    rw [← IsIso.eq_comp_inv] at n
    rw [n]
    infer_instance

section Core

variable {S T : Scheme.{u}} (g : T ⟶ S) {I : Type u} [Category.{u} I] (X : I ⥤ Scheme.{u})
  (p : X ⟶ (Functor.const I).obj S)

/-- The system `i ↦ T ×_S Xᵢ`. -/
@[simps]
noncomputable def Etale.smoothLimitPullbackFunctor : I ⥤ Scheme.{u} where
  obj i := pullback g (p.app i)
  map {i j} f := pullback.map g (p.app i) g (p.app j) (𝟙 T) (X.map f) (𝟙 S) (by simp)
    (by simp [p.naturality f])
  map_id i := pullback.hom_ext (by simp) (by simp)
  map_comp f f' := pullback.hom_ext (by simp) (by simp)

lemma Etale.isPullback_smoothLimitPullbackFunctor_map {i j : I} (f : i ⟶ j) :
    IsPullback ((Etale.smoothLimitPullbackFunctor g X p).map f) (pullback.snd g (p.app i))
      (pullback.snd g (p.app j)) (X.map f) := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback g (p.app j))
  simp only [Etale.smoothLimitPullbackFunctor_map, pullback.lift_fst, Category.comp_id]
  have : X.map f ≫ p.app j = p.app i := by simp [p.naturality f]
  rw [this]
  exact IsPullback.of_hasPullback g (p.app i)

variable [∀ i, QuasiCompact (p.app i)] [∀ i, QuasiSeparated (p.app i)]
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f)]

instance {i j : I} (f : i ⟶ j) : IsAffineHom ((Etale.smoothLimitPullbackFunctor g X p).map f) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom)
    (Etale.isPullback_smoothLimitPullbackFunctor_map g X p f).flip inferInstance

/-- **Smooth base change along a limit of smooth schemes over a quasi-compact quasi-separated
base.** Let `Xᵢ ⟶ S` be a cofiltered system of smooth quasi-compact quasi-separated morphisms
with affine transition maps and limit `X₀ ⟶ S`, `S` quasi-compact and quasi-separated, and
`g : T ⟶ S` quasi-compact quasi-separated. For every sheaf `F` on `T` with torsion stalks of
orders invertible on `S`, the base-change map of the Cartesian square `Y = T ×_S X₀` is an
isomorphism in every degree. -/
theorem Etale.isIso_baseChangeHomologyMap_of_isLimit_smooth_of_qcqs [IsCofiltered I]
    [QuasiCompact g] [QuasiSeparated g] [CompactSpace S] [QuasiSeparatedSpace S]
    [∀ i, Smooth (p.app i)] {cX : Cone X} (hX : IsLimit cX) (p₀ : cX.pt ⟶ S)
    (hp₀ : ∀ i, cX.π.app i ≫ p.app i = p₀) {Y : Scheme.{u}} {e : Y ⟶ T} {h : Y ⟶ cX.pt}
    (sq : IsPullback e h g p₀) (q : ℤ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder S F] :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  have : IsConnected I := IsCofiltered.isConnected I
  have : ∀ i, CompactSpace (((Functor.const I).obj S).obj i) := fun _ ↦
    inferInstanceAs (CompactSpace S)
  have : ∀ i, QuasiSeparatedSpace (((Functor.const I).obj S).obj i) :=
    fun _ ↦ inferInstanceAs (QuasiSeparatedSpace S)
  have : ∀ i, CompactSpace (X.obj i) := fun i ↦ QuasiCompact.compactSpace_of_compactSpace (p.app i)
  have : ∀ i, QuasiSeparatedSpace (X.obj i) := fun i ↦ quasiSeparatedSpace_of_quasiSeparated
    (p.app i)
  have : ∀ i, QuasiCompact (((Functor.const I).map g).app i) := fun _ ↦
    inferInstanceAs (QuasiCompact g)
  have : ∀ i, QuasiSeparated (((Functor.const I).map g).app i) := fun _ ↦
    inferInstanceAs (QuasiSeparated g)
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (((Functor.const I).obj S).map f) :=
    fun _ ↦ (inferInstance : IsAffineHom (𝟙 S))
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (((Functor.const I).obj T).map f) :=
    fun _ ↦ (inferInstance : IsAffineHom (𝟙 T))
  let e' : Etale.smoothLimitPullbackFunctor g X p ⟶ (Functor.const I).obj T :=
    { app i := pullback.fst g (p.app i)
      naturality i j f := by simp }
  let h' : Etale.smoothLimitPullbackFunctor g X p ⟶ X :=
    { app i := pullback.snd g (p.app i)
      naturality i j f := by simp }
  have hsq (i : I) : IsPullback (e'.app i) (h'.app i) (((Functor.const I).map g).app i)
      (p.app i) := IsPullback.of_hasPullback g (p.app i)
  let cY : Cone (Etale.smoothLimitPullbackFunctor g X p) :=
    { pt := Y
      π :=
        { app i := pullback.lift e (h ≫ cX.π.app i)
            (by rw [sq.w, Category.assoc, hp₀])
          naturality i j f := pullback.hom_ext (by simp) (by simp) } }
  have hcY : IsLimit cY := isLimitOfIsPullbackOfIsConnected h' cY cX
    { hom := h
      w i := by simp [cY, h'] }
    (fun i ↦ by
      refine IsPullback.of_right ?_ (by simp [cY, h']) (IsPullback.of_hasPullback g (p.app i))
      simp only [cY, pullback.lift_fst, hp₀]
      exact sq)
    hX
  have key := Etale.isIso_baseChangeHomologyMap_of_isLimit Λ p ((Functor.const I).map g) e' h'
    hsq (isLimitConstCone I S) hX (isLimitConstCone I T) hcY (p₀ := p₀) (g₀ := g) (e₀ := e)
    (h₀ := h) (fun i ↦ (Category.comp_id _).trans (hp₀ i).symm)
    (fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm)
    (fun _ ↦ (Category.comp_id _).trans (pullback.lift_fst _ _ _).symm)
    (fun i ↦ by simp [cY, h']) sq (𝟙 _) (𝟙 T) (fun _ ↦ Category.id_comp _) F q (fun i ↦ ?_)
  · exact (Etale.isIso_baseChangeHomologyMap_iff_of_iso Λ sq q
      ((Etale.upperStarId (ModuleCat.{u + 1} Λ) T).app F)).1 key
  · refine (Etale.isIso_baseChangeHomologyMap_iff_of_iso Λ (hsq i) q
      ((Etale.upperStarId (ModuleCat.{u + 1} Λ) T).app F)).2 ?_
    have : Scheme.IsTorsionSheafOfInvertibleOrder (((Functor.const I).obj S).obj i) F :=
      inferInstanceAs (Scheme.IsTorsionSheafOfInvertibleOrder S F)
    exact Etale.isIso_baseChangeHomologyMap_of_smooth Λ (p.app i) g (e'.app i) (h'.app i)
      (hsq i) q F

end Core

/-- Pullbacks of sheaves torsion of orders invertible on `S` are torsion of orders invertible on
any `S'` mapping to `S`. -/
lemma Scheme.IsTorsionSheafOfInvertibleOrder.upperStar {S S' T T' : Scheme.{u}} (b : S' ⟶ S)
    (c : T' ⟶ T) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [hF : Scheme.IsTorsionSheafOfInvertibleOrder S F] :
    Scheme.IsTorsionSheafOfInvertibleOrder S' (((c)^*[ModuleCat.{u + 1} Λ]).obj F) where
  exists_isUnit_nsmul_eq_zero Ω _ _ s x := by
    let ψ := (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) c s).app F
    obtain ⟨n, hn, hu, hx⟩ := hF.exists_isUnit_nsmul_eq_zero Ω (s ≫ c) (ψ.hom.hom x)
    refine ⟨n, hn, by simpa using hu.map b.appTop.hom, ?_⟩
    have h1 : ψ.hom.hom (n • x) = 0 := by rw [map_nsmul, hx]
    have h2 : ψ.inv.hom (ψ.hom.hom (n • x)) = n • x := by
      rw [← ModuleCat.comp_apply, ψ.hom_inv_id, ModuleCat.id_apply]
    rw [← h2, h1, map_zero]

/-- Smooth base change along a limit of smooth schemes, for a system given as a functor
`X : I ⥤ Scheme` with a cone of morphisms `p : X ⟶ S` (blueprint
`corollary-open-direct-image-over-field--2`, see
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit_smooth`). The base `S` is arbitrary:
the statement is local on `S` (`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_etale_cover`)
and holds over affine opens by
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit_smooth_of_qcqs`. -/
theorem Etale.isIso_baseChangeHomologyMap_of_isLimit_smooth' {S T : Scheme.{u}} (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g] {I : Type u} [Category.{u} I] [IsCofiltered I]
    (X : I ⥤ Scheme.{u}) (p : X ⟶ (Functor.const I).obj S) [∀ i, Smooth (p.app i)]
    [∀ i, QuasiCompact (p.app i)] [∀ i, QuasiSeparated (p.app i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f)] {cX : Cone X} (hX : IsLimit cX)
    (p₀ : cX.pt ⟶ S) (hp₀ : ∀ i, cX.π.app i ≫ p.app i = p₀) {Y : Scheme.{u}} {e : Y ⟶ T}
    {h : Y ⟶ cX.pt} (sq : IsPullback e h g p₀) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder S F] :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  have : IsConnected I := IsCofiltered.isConnected I
  -- the cover of `S` by its affine opens and its pullbacks
  let a (V : S.affineOpens) := pullback.fst p₀ V.1.ι
  let f (V : S.affineOpens) := pullback.snd p₀ V.1.ι
  let b (V : S.affineOpens) := V.1.ι
  let c' (V : S.affineOpens) := pullback.fst g V.1.ι
  let g' (V : S.affineOpens) := pullback.snd g V.1.ι
  let e' (V : S.affineOpens) := pullback.fst (g' V) (f V)
  let h' (V : S.affineOpens) := pullback.snd (g' V) (f V)
  refine Etale.isIso_baseChangeHomologyMap_of_etale_cover Λ a (fun x ↦ ?_) f b
    (fun V ↦ pullback.condition.symm) c' g' (fun V ↦ IsPullback.of_hasPullback g V.1.ι) e' h'
    (fun V ↦ IsPullback.of_hasPullback (g' V) (f V)) sq q F (fun V ↦ ?_)
  · obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (p₀.base x)) isOpen_univ
    obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p₀)
      (g := Scheme.Opens.ι V) x (⟨p₀.base x, hxV⟩ : (V : Scheme.{u})) rfl
    exact ⟨⟨V, hV⟩, y, hy⟩
  · -- the restricted system over the affine open `V`
    have : QuasiCompact (g' V) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback g V.1.ι) inferInstance
    have : QuasiSeparated (g' V) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback g V.1.ι) inferInstance
    let Xr := Etale.smoothLimitPullbackFunctor V.1.ι X p
    let pr : Xr ⟶ (Functor.const I).obj V.1 :=
      { app i := pullback.fst V.1.ι (p.app i)
        naturality i j φ := by simp [Xr] }
    let sr : Xr ⟶ X :=
      { app i := pullback.snd V.1.ι (p.app i)
        naturality i j φ := by simp [Xr] }
    have : ∀ i, Smooth (pr.app i) := fun i ↦
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback V.1.ι (p.app i)).flip inferInstance
    have : ∀ i, QuasiCompact (pr.app i) := fun i ↦
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback V.1.ι (p.app i)).flip inferInstance
    have : ∀ i, QuasiSeparated (pr.app i) := fun i ↦
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback V.1.ι (p.app i)).flip inferInstance
    have : ∀ {i j : I} (φ : i ⟶ j), IsAffineHom (Xr.map φ) := fun φ ↦
      (inferInstance : IsAffineHom ((Etale.smoothLimitPullbackFunctor V.1.ι X p).map φ))
    let cr : Cone Xr :=
      { pt := pullback p₀ V.1.ι
        π :=
          { app i := pullback.lift (f V) (a V ≫ cX.π.app i)
              (by rw [Category.assoc, hp₀, ← pullback.condition])
            naturality i j φ := pullback.hom_ext (by simp [Xr, f])
              (by simp [Xr, a, cX.w φ]) } }
    have hcr : IsLimit cr := isLimitOfIsPullbackOfIsConnected (I := I) sr cr cX
      { hom := a V
        w i := by simp [cr, sr] }
      (fun i ↦ by
        refine IsPullback.of_right ?_ (by simp [cr, sr])
          (IsPullback.of_hasPullback V.1.ι (p.app i))
        simp only [cr, pullback.lift_fst, hp₀]
        exact (IsPullback.of_hasPullback p₀ V.1.ι).flip)
      hX
    have : Scheme.IsTorsionSheafOfInvertibleOrder V.1 (((c' V)^*[ModuleCat.{u + 1} Λ]).obj F) :=
      Scheme.IsTorsionSheafOfInvertibleOrder.upperStar Λ V.1.ι (c' V) F
    exact Etale.isIso_baseChangeHomologyMap_of_isLimit_smooth_of_qcqs Λ (g' V) Xr pr hcr (f V)
      (fun i ↦ by simp [cr, pr]) (IsPullback.of_hasPullback (g' V) (f V)) q _

/-- Blueprint `corollary-open-direct-image-over-field--2`: Smooth base change for limits of smooth
schemes.

Let `S' = lim Sᵢ` be a cofiltered limit of schemes `Sᵢ` which are smooth, quasi-compact and
quasi-separated over `S`, with affine transition morphisms, let `g : T ⟶ S` be quasi-compact
quasi-separated and form the Cartesian square

```
Y --e--> T
|        |
h        g
v        v
S' -----> S
```

Then for every sheaf `F` of `Λ`-modules on `T` whose geometric stalks are torsion of orders
invertible on `S`, the base-change map `R^q g_* F |_{S'} ⟶ R^q h_* e⁻¹ F` is an isomorphism in
every degree `q`. -/
@[stacks 0F09]
theorem Etale.isIso_baseChangeHomologyMap_of_isLimit_smooth {S T : Scheme.{u}} (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g] {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Over S) [∀ i, Smooth (D.obj i).hom] [∀ i, QuasiCompact (D.obj i).hom]
    [∀ i, QuasiSeparated (D.obj i).hom] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) {Y : Scheme.{u}} {e : Y ⟶ T}
    {h : Y ⟶ c.pt.left} (sq : IsPullback e h g c.pt.hom) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder S F] :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  let p : D ⋙ Over.forget S ⟶ (Functor.const I).obj S :=
    { app i := (D.obj i).hom
      naturality i j f := by simp }
  have : ∀ i, Smooth (p.app i) := fun i ↦ (inferInstance : Smooth (D.obj i).hom)
  have : ∀ i, QuasiCompact (p.app i) := fun i ↦ (inferInstance : QuasiCompact (D.obj i).hom)
  have : ∀ i, QuasiSeparated (p.app i) := fun i ↦
    (inferInstance : QuasiSeparated (D.obj i).hom)
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom ((D ⋙ Over.forget S).map f) := fun f ↦
    (inferInstance : IsAffineHom (D.map f).left)
  exact Etale.isIso_baseChangeHomologyMap_of_isLimit_smooth' Λ g (D ⋙ Over.forget S) p hc
    c.pt.hom (fun i ↦ Over.w (c.π.app i)) sq q F

end AlgebraicGeometry

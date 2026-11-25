/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.DimensionShift
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.DescentLimit
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.PushforwardZeroDescent
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.StageAlgebra

/-!
# Higher direct images to the stages of a limit

Let `S₀ = lim Sᵢ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps, `πᵢ : S₀ ⟶ Sᵢ`, and let `f₀ : Z ⟶ S₀` be a morphism. For a sheaf `G` of
`Λ`-modules on `Z`, the base-change maps `πᵢ^* R^q(f₀ ≫ πᵢ)_* G ⟶ R^q f₀_* G` exhibit
`R^q f₀_* G` as the filtered colimit of the `πᵢ^* R^q(f₀ ≫ πᵢ)_* G`, on every geometric stalk
(`AlgebraicGeometry.Etale.isStalkColimit_pushforwardStageSystem`).

In degree `0` this is the statement `F = colimᵢ πᵢ^* πᵢ_* F` of blueprint
`corollary-open-direct-image-over-field--2` for `F = f₀_* G`; the higher degrees follow by dimension
shifting (`AlgebraicGeometry.Etale.LimitStageSystem.isStalkColimit_of_injective`), since all the
functors involved send injective sheaves to sheaves without higher cohomology.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} (c : Cone D) {Z : Scheme.{u}}
  (f₀ : Z ⟶ c.pt)

/-- The system of stages `(Z, Sᵢ, f₀ ≫ πᵢ, πᵢ, 𝟙 Z)` over the limit `S₀ = c.pt`, with limit stage
`(Z, S₀, f₀, 𝟙 S₀, 𝟙 Z)`. -/
@[simps]
noncomputable def pushforwardStageSystem : LimitStageSystem c.pt Z I where
  obj i := ⟨Z, D.obj i, f₀ ≫ c.π.app i, c.π.app i, 𝟙 Z⟩
  map {i j} f := ⟨𝟙 Z, D.map f, by simp, by simp, by simp⟩
  map_id i := LimitStage.Hom.ext rfl (D.map_id i)
  map_comp f g := LimitStage.Hom.ext (by simp) (D.map_comp f g)
  pt := ⟨Z, c.pt, f₀, 𝟙 c.pt, 𝟙 Z⟩
  π i := ⟨𝟙 Z, c.π.app i, by simp, by simp, by simp⟩
  w f := LimitStage.Hom.ext (by simp) (by simp)

lemma isZero_pushforwardStageSystem_of_injective
    (J : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J] (q : ℤ) (hq : q ≠ 0) :
    (∀ i, IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((LimitStage.functor Λ ((pushforwardStageSystem c f₀).obj i)).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj J)))) ∧
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((LimitStage.functor Λ (pushforwardStageSystem c f₀).pt).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj J))) := by
  have : Injective (((𝟙 Z)^*[ModuleCat.{u + 1} Λ]).obj J) :=
    Injective.of_iso ((Etale.upperStarId (ModuleCat.{u + 1} Λ) Z).app J).symm inferInstance
  refine ⟨fun i ↦ ?_, ?_⟩
  · have : Injective ((((pushforwardStageSystem c f₀).obj i).w)^*[ModuleCat.{u + 1} Λ].obj J) :=
      this
    exact LimitStage.isZero_homology_functor_obj_single_of_injective Λ _ J hq
  · have : Injective (((pushforwardStageSystem c f₀).pt.w)^*[ModuleCat.{u + 1} Λ].obj J) := this
    exact LimitStage.isZero_homology_functor_obj_single_of_injective Λ _ J hq

variable [IsCofiltered I] (hc : IsLimit c) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- Degree zero, at injective sheaves: blueprint `corollary-open-direct-image-over-field--2` for
`F = f₀_* J`. -/
lemma isStalkColimit_pushforwardStageSystem_zero
    (J : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J] :
    (pushforwardStageSystem c f₀).IsStalkColimit Λ
      ((DerivedCategory.Plus.singleFunctor _ 0).obj J) 0 := by
  refine LimitStageSystem.isStalkColimit_of_iso _ (singleFunctorIsoQObj Λ J) fun x ↦ ?_
  have hcol := isColimitDescentCocone hc (((f₀)_*[ModuleCat.{u + 1} Λ]).obj J)
  refine ModuleCat.IsElementwiseColimit.of_iso
    (fun i ↦ (c.pt.uliftPointSmallEtale x).sheafFiber.mapIso
      (LimitStage.homologyZeroIso Λ ((pushforwardStageSystem c f₀).obj i) J ≪≫
        ((c.π.app i)^*[ModuleCat.{u + 1} Λ]).mapIso (pushforwardStageIso Λ f₀ J (c.π.app i))))
    ((c.pt.uliftPointSmallEtale x).sheafFiber.mapIso
      (LimitStage.homologyZeroIso Λ (pushforwardStageSystem c f₀).pt J ≪≫
        pushforwardStagePtIso Λ f₀ J))
    (fun i ↦ ?_) (fun {i j} f ↦ ?_) (isElementwiseColimit_sheafFiber_of_isColimit hcol x)
  · simp only [Functor.mapIso_hom, Iso.trans_hom, stalkHomology, Functor.comp_map,
      ← Functor.map_comp, descentCocone_ι_app, Category.assoc]
    congr 1
    rw [reassoc_of% (LimitStage.homology_map_transition_homologyZeroIso Λ
      ((pushforwardStageSystem c f₀).π i) J)]
    exact congrArg (_ ≫ ·) (sheafTransition_pushforwardStage_proj Λ f₀ J (c.π.app i)).symm
  · simp only [Functor.mapIso_hom, Iso.trans_hom, stalkHomology, Functor.comp_map,
      ← Functor.map_comp, descentDiagram_map, Category.assoc]
    congr 1
    rw [reassoc_of% (LimitStage.homology_map_transition_homologyZeroIso Λ
      ((pushforwardStageSystem c f₀).map f) J)]
    exact congrArg (_ ≫ ·) (pushforwardStageIso_descentTransition Λ f₀ J (c.π.app i)
      (D.map f) (c.π.app j) (c.w f).symm)

include hc in
/-- **Higher direct images to the stages of a limit.** For `S₀ = lim Sᵢ` with affine transition
maps and quasi-compact quasi-separated stages, `f₀ : Z ⟶ S₀` and a sheaf `G` on `Z`, the maps
`πᵢ^* R^q(f₀ ≫ πᵢ)_* G ⟶ R^q f₀_* G` present `R^q f₀_* G` as the filtered colimit of the
`πᵢ^* R^q(f₀ ≫ πᵢ)_* G`, on every geometric stalk of `S₀`. -/
theorem isStalkColimit_pushforwardStageSystem
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (pushforwardStageSystem c f₀).IsStalkColimit Λ
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G) q := by
  obtain hq | hq := lt_or_ge q 0
  · exact LimitStageSystem.isStalkColimit_of_isZero _
      (fun i ↦ LimitStage.isZero_homology_functor_obj_single_of_lt Λ _ G hq)
      (LimitStage.isZero_homology_functor_obj_single_of_lt Λ _ G hq)
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
  exact LimitStageSystem.isStalkColimit_of_injective _
    (fun J _ q hq ↦ isZero_pushforwardStageSystem_of_injective Λ c f₀ J q hq)
    (fun J _ ↦ isStalkColimit_pushforwardStageSystem_zero Λ c f₀ hc J) n G

end

end AlgebraicGeometry.Etale

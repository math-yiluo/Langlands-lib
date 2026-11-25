/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Exchange.BaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.Support
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Geometric stalks of base change maps after a further base change

Consider a cube of cartesian squares over `u : S' ⟶ S` as in
`AlgebraicGeometry.Etale.baseChange_app_cube`, whose side faces satisfy base change. For a
geometric point `s` of `X'`, the base change map of the pulled-back square is an isomorphism on
the stalk at `s` if and only if the base change map of the original square is an isomorphism on
the stalk at the image `s ≫ uX`
(`AlgebraicGeometry.Etale.isIso_sheafFiber_baseChangeHomologyMap_cube_iff`).
Moreover, whether a morphism of sheaves is an isomorphism on the stalk at a geometric point only
depends on the underlying point (`AlgebraicGeometry.Etale.isIso_sheafFiber_map_of_apply_eq`).
These are the inputs for transporting the hypothesis of the projective case of blueprint
`corollary-open-direct-image-over-field--2` to the base change to a separable closure.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- A morphism `ψ` of étale sheaves of `Λ`-modules is an isomorphism on the (universe lifted)
stalk at a geometric point if and only if its kernel and cokernel have vanishing stalks there. -/
lemma isIso_uliftSheafFiber_map_iff {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (ψ : G ⟶ H) :
    IsIso ((pointSmallEtale s).ulift.{u + 1}.sheafFiber.map ψ) ↔
      IsZero ((pointSmallEtale s).ulift.{u + 1}.sheafFiber.obj (kernel ψ)) ∧
        IsZero ((pointSmallEtale s).ulift.{u + 1}.sheafFiber.obj (cokernel ψ)) := by
  have : LocallySmall.{u + 1} X.Etale := locallySmall_max.{u + 1, u}
  set Φ := (pointSmallEtale s).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} Λ)
  have : PreservesFiniteLimits Φ := inferInstance
  have : PreservesFiniteColimits Φ := inferInstance
  have : Φ.Additive := Functor.additive_of_preserves_binary_products _
  have e₁ := (ShortComplex.exact_of_f_is_kernel (ShortComplex.mk (kernel.ι ψ) ψ
    (kernel.condition ψ)) (kernelIsKernel ψ)).map Φ
  have e₂ := (ShortComplex.exact_of_g_is_cokernel (ShortComplex.mk ψ (cokernel.π ψ)
    (cokernel.condition ψ)) (cokernelIsCokernel ψ)).map Φ
  have hm : Mono (Φ.map ψ) ↔ IsZero (Φ.obj (kernel ψ)) := by
    refine e₁.mono_g_iff.trans ⟨fun h0 ↦ ?_, fun hz ↦ hz.eq_of_src _ _⟩
    have : Mono (Φ.map (kernel.ι ψ)) := inferInstance
    exact IsZero.of_mono_eq_zero (Φ.map (kernel.ι ψ)) h0
  have he : Epi (Φ.map ψ) ↔ IsZero (Φ.obj (cokernel ψ)) := by
    refine e₂.epi_f_iff.trans ⟨fun h0 ↦ ?_, fun hz ↦ hz.eq_of_tgt _ _⟩
    have : Epi (Φ.map (cokernel.π ψ)) := inferInstance
    exact IsZero.of_epi_eq_zero (Φ.map (cokernel.π ψ)) h0
  rw [isIso_iff_mono_and_epi, hm, he]

/-- Whether a morphism of étale sheaves of `Λ`-modules is an isomorphism on the stalk at a
geometric point only depends on the underlying point: its kernel and cokernel have vanishing
stalks at both geometric points simultaneously
(`AlgebraicGeometry.Etale.isZero_sheafFiber_iff_of_apply_eq`). -/
lemma isIso_sheafFiber_map_of_apply_eq {X : Scheme.{u}}
    {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (ψ : G ⟶ H)
    {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsSepClosed Ω₁] [Field Ω₂] [IsSepClosed Ω₂]
    (s₁ : Spec (.of Ω₁) ⟶ X) (s₂ : Spec (.of Ω₂) ⟶ X) (h : s₁ default = s₂ default)
    (hψ : IsIso ((pointSmallEtale s₁).ulift.{u + 1}.sheafFiber.map ψ)) :
    IsIso ((pointSmallEtale s₂).ulift.{u + 1}.sheafFiber.map ψ) := by
  have hz (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (hM : IsZero ((pointSmallEtale s₁).ulift.{u + 1}.sheafFiber.obj M)) :
      IsZero ((pointSmallEtale s₂).ulift.{u + 1}.sheafFiber.obj M) :=
    ((isZero_sheafFiber_iff_of_apply_eq M s₁ s₂ h).1
      (hM.of_iso (((pointSmallEtale s₁).uliftSheafFiberIso _).app M).symm)).of_iso
        (((pointSmallEtale s₂).uliftSheafFiberIso _).app M)
  rw [isIso_uliftSheafFiber_map_iff] at hψ ⊢
  exact ⟨hz _ hψ.1, hz _ hψ.2⟩

variable {X S T Y X' S' T' Y' : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
  {u : S' ⟶ S} {uT : T' ⟶ T} {uX : X' ⟶ X} {uY : Y' ⟶ Y} {g' : T' ⟶ S'} {p' : X' ⟶ S'}
  {e' : Y' ⟶ T'} {h' : Y' ⟶ X'}

/-- **Stalks of base change maps in a cube.** In a cube of cartesian squares over `u : S' ⟶ S` as
in `AlgebraicGeometry.Etale.baseChange_app_cube`, if the degree-`q` base change maps of the side
faces `bT` (at `F`) and `bX` (at `e⁻¹ F`) are isomorphisms for all `q`, then for a geometric point
`s` of `X'` the degree-`q` base change map of the pulled-back square at `uT⁻¹ F` is an isomorphism
on the stalk at `s` if and only if the one of the original square at `F` is an isomorphism on the
stalk at `s ≫ uX`. -/
theorem isIso_sheafFiber_baseChangeHomologyMap_cube_iff (sq : IsPullback e h g p)
    (bT : IsPullback uT g' g u) (sq' : IsPullback e' h' g' p') (bX : IsPullback uY h' h uX)
    (hp : p' ≫ u = uX ≫ p) (he : e' ≫ uT = uY ≫ e)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hT : ∀ q, IsIso (Etale.baseChangeHomologyMap Λ bT q F))
    (hX : ∀ q, IsIso (Etale.baseChangeHomologyMap Λ bX q ((e)^*[ModuleCat.{u + 1} Λ].obj F)))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X') (q : ℤ) :
    IsIso ((pointSmallEtale s).ulift.{u + 1}.sheafFiber.map
        (Etale.baseChangeHomologyMap Λ sq' q ((uT)^*[ModuleCat.{u + 1} Λ].obj F))) ↔
      IsIso ((pointSmallEtale (s ≫ uX)).ulift.{u + 1}.sheafFiber.map
        (Etale.baseChangeHomologyMap Λ sq q F)) := by
  set K := (DerivedCategory.Plus.singleFunctor (Sheaf T.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0).obj F
  set Φ := (pointSmallEtale s).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} Λ)
  have : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) bT.toCommSq).app K) := by
    rw [DerivedCategory.Plus.isIso_iff]
    exact fun q ↦ (Etale.isIso_baseChangeHomologyMap_iff Λ bT q F).1 (hT q)
  have : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) bX.toCommSq).app
      (((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K)) := by
    refine (NatTrans.isIso_app_iff_of_iso _
      ((((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app F).symm).1 ?_
    rw [DerivedCategory.Plus.isIso_iff]
    exact fun q ↦ (Etale.isIso_baseChangeHomologyMap_iff Λ bX q _).1 (hX q)
  -- the base change map of `sq'` at `uT⁻¹ F` versus at `uT^* K`
  have h₁ : IsIso (Φ.map (Etale.baseChangeHomologyMap Λ sq' q
        ((uT)^*[ModuleCat.{u + 1} Λ].obj F))) ↔
      IsIso ((DerivedCategory.Plus.homologyFunctor _ q ⋙ Φ).map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq'.toCommSq).app
          (((uT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K))) :=
    NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight
      (Etale.baseChange (ModuleCat.{u + 1} Λ) sq'.toCommSq)
      (DerivedCategory.Plus.homologyFunctor _ q ⋙ Φ))
      ((((uT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app F).symm
  -- the cube
  have h₂ : IsIso ((DerivedCategory.Plus.homologyFunctor _ q ⋙ Φ).map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq'.toCommSq).app
          (((uT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K))) ↔
      IsIso ((DerivedCategory.Plus.homologyFunctor _ q ⋙ Φ).map
        (((uX)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
          ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K))) := by
    refine (Arrow.isIso_iff_isIso_of_isIso
      ((DerivedCategory.Plus.homologyFunctor _ q ⋙ Φ).mapArrow.mapIso
        (Etale.baseChangeCubeArrowIso Λ sq.toCommSq bT.toCommSq sq'.toCommSq bX.toCommSq hp he
          K)).hom).trans ?_
    dsimp only [Functor.mapArrow_obj, Arrow.mk_hom]
    rw [Functor.map_comp]
    exact isIso_comp_right_iff _ _
  -- commuting the pullback along `uX` with the cohomology sheaves and the stalk
  have h₃ : IsIso ((DerivedCategory.Plus.homologyFunctor _ q ⋙ Φ).map
        (((uX)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
          ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K))) ↔
      IsIso (((uX)^*[ModuleCat.{u + 1} Λ] ⋙ Φ).map
        (Etale.baseChangeHomologyMap Λ sq q F)) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerRight
      (((uX)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q) Φ)
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)).symm
  exact h₁.trans (h₂.trans (h₃.trans (NatIso.isIso_map_iff
    (Etale.upperStarCompUliftSheafFiberIso (ModuleCat.{u + 1} Λ) uX s) _)))

end Etale

end AlgebraicGeometry

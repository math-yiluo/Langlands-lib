/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MatesCounit
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.BaseChangeCharts

/-!
# Base change for the affine line from the projective line

The elementary case (a) of the proof of blueprint
`proposition-exceptional-inverse-image-smooth-morphism--6` concerns the projection `p : 𝔸¹_S ⟶ S`.
It factors as the standard chart `j : 𝔸¹_S ⟶ ℙ¹_S`, an open immersion, followed by the proper
projection `q : ℙ¹_S ⟶ S`. Base change holds for `Rj^!`
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion_right`) and
base change maps compose
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_comp`), so base change for
the affine line follows from base change for the projective line: this is the reduction of the
blueprint to the projective-line adjunction `Rq_* ⊣ q^*(1)[2]`
(`proposition-adjunction-projective-line--1`) whose unit and counit commute with base change
(`proposition-adjunction-projective-line`).

## Main definitions

- `AlgebraicGeometry.Etale.ProjectiveLineBaseChange`

## Main statements

- `AlgebraicGeometry.Etale.affineLineBaseChange_of_projectiveLineBaseChange`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

variable (Λ) in
/-- *Base change for projective-line projections*: for every scheme `S` on which the
exponent of `Λ` is invertible and every cartesian square of the projection
`q : ℙ¹_S ⟶ S` (here `ℙ¹_S = ℙ(Option (Fin 1); S)`, the target of the standard chart of `𝔸¹_S`)
with quasi-compact base change admitting a compactification, the canonical base change map
`Lg'^* Rq^! ⟶ Rq'^! Lg^*` is an isomorphism. By the blueprint
(`proposition-adjunction-projective-line`), `Rq^! = q^*(1)[2]` with counit built from the
projective-line trace, and unit and counit commute with base change. -/
def ProjectiveLineBaseChange : Prop :=
  ∀ ⦃S : Scheme.{u}⦄ [HasInvertibleExponent Λ S] ⦃S' P' : Scheme.{u}⦄
    {g : S' ⟶ S} {q' : P' ⟶ S'} {g' : P' ⟶ ℙ(Option (ULift.{u} (Fin 1)); S)}
    (sq : IsPullback g' q' (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) g) [HasCompactification q']
    [QuasiCompact q'], IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq)

/-- **Base change for the affine line from the projective line.** The projection
`𝔸¹_S ⟶ S` is the standard chart `𝔸¹_S ⟶ ℙ¹_S`, a quasi-compact open immersion, followed by
the projection `ℙ¹_S ⟶ S`; base change maps compose, and base change holds for open
immersions. -/
theorem affineLineBaseChange_of_projectiveLineBaseChange (h : ProjectiveLineBaseChange Λ) :
    AffineLineBaseChange Λ := by
  intro S _ S' P' g p' g' sq _ _
  have : QuasiCompact (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S ≫
      ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) := by
    rw [AffineSpace.toRelativeProjectiveSpace_over]
    infer_instance
  have : QuasiCompact (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S) :=
    .of_comp _ (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)
  have : HasCompactification (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S) :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  exact isIso_rightDerivedUpperShriekBaseChangeMap_of_comp
    (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S)
    (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) (AffineSpace.toRelativeProjectiveSpace_over _ S) sq
    (fun _ _ _ _ _ sq' _ _ ↦
      isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion_right Λ sq')
    (fun _ _ _ _ _ sq' _ _ ↦ h sq')

section Adjunction

variable [HasTateTwist Λ]

variable (Λ) in
/-- *The projective-line adjunction commutes with base change* (the form in which blueprint
`proposition-adjunction-projective-line` is used): for every scheme `S` on which the exponent of `Λ`
is invertible and every `g : S' ⟶ S`, with the cartesian square

```
  ℙ¹_{S'} --g'--> ℙ¹_S
     |             |
     q'            q
     ↓             ↓
     S' ----g----> S
```

(`AlgebraicGeometry.ProjectiveSpace.isPullback_map`), there are adjunctions
`Rq_! ⊣ Lq^*(1)[2]` and `Rq'_! ⊣ Lq'^*(1)[2]` whose counits are compatible with the
compact-support base change `Ex_! : Lg^* Rq_! ⟶ Rq'_! Lg'^*` and the canonical isomorphism
`Lg'^*(Lq^* K(1)[2]) ≅ Lq'^* Lg^* K(1)[2]`:

`Ex_! ≫ Rq'_!(Lg'^* Lq^* K(1)[2] ≅ Lq'^* Lg^* K(1)[2]) ≫ ε'_{Lg^* K} = Lg^* ε_K`.

In the blueprint, `Rq_! = Rq_*` (`q` is proper), and the counit is
`ε_K : Rq_* q^* K(1)[2] ≅ K ⊗ Rq_* Λ(1)[2] ⟶ K`, from the trace `Tr_q` of
`lemma-cohomology-projective-line-trace`; the counit commutes with base change since the trace and
the projection formula do. Base change for an arbitrary cartesian square of `q` follows, since such
a square is isomorphic to this one
(`AlgebraicGeometry.Etale.projectiveLineBaseChange_of_adjunction`). -/
def ProjectiveLineAdjunctionBaseChange : Prop :=
  ∀ ⦃S : Scheme.{u}⦄ [HasInvertibleExponent Λ S] ⦃S' : Scheme.{u}⦄ (g : S' ⟶ S),
    haveI : HasInvertibleExponent Λ ℙ(Option (ULift.{u} (Fin 1)); S) := .of_hom (_ ↘ S)
    haveI : HasInvertibleExponent Λ S' := .of_hom g
    haveI : HasInvertibleExponent Λ ℙ(Option (ULift.{u} (Fin 1)); S') := .of_hom (_ ↘ S')
    ∃ (adj : R((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_![ModuleCat.{u + 1} Λ] ⊣
        L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
          twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)
      (adj' : R((ℙ(Option (ULift.{u} (Fin 1)); S') ↘ S'))_![ModuleCat.{u + 1} Λ] ⊣
        L(((ℙ(Option (ULift.{u} (Fin 1)); S') ↘ S'))^*[ModuleCat.{u + 1} Λ]) ⋙
          twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S') 1),
      ∀ K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        (rightDerivedLowerShriekBaseChangeMap Λ
            (ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1))) g)).app
            ((twistShift Λ _ 1).obj
              ((L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ])).obj K)) ≫
          (R((ℙ(Option (ULift.{u} (Fin 1)); S') ↘ S'))_![ModuleCat.{u + 1} Λ]).map
            ((leftDerivedUpperStarTwistShiftIso Λ
                (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g) 1 _).hom ≫
              (twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S') 1).map
                ((derivedSquareUpperStarIso _
                  (ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1))) g).toCommSq).inv.app
                    K)) ≫
            adj'.counit.app ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) =
          (L((g)^*[ModuleCat.{u + 1} Λ])).map (adj.counit.app K)

/-- **Base change for the projective line from the adjunction** (the formal part of the
blueprint argument "the unit and counit commute with base change"). For the standard square of
`g : S' ⟶ S` (`AlgebraicGeometry.ProjectiveSpace.isPullback_map`), the base change map of
`Rq^!` is the mate of the inverse of `Ex_!`, which, computed through the adjunctions
`Rq_! ⊣ Lq^*(1)[2]` and `Rq'_! ⊣ Lq'^*(1)[2]` with compatible counits, is the canonical
isomorphism `Lg'^*(Lq^* K(1)[2]) ≅ Lq'^* Lg^* K(1)[2]`
(`CategoryTheory.isIso_mateEquiv_app_of_counit`). An arbitrary cartesian square of `q` is
isomorphic to the standard one through an isomorphism `e : P' ≅ ℙ¹_{S'}` over `S'`: stacking the
square of the open immersion `𝟙 : ℙ¹_S ⟶ ℙ¹_S` with vertical map `e` on the standard square, the
base change maps compose
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff`). -/
theorem projectiveLineBaseChange_of_adjunction (h : ProjectiveLineAdjunctionBaseChange Λ) :
    ProjectiveLineBaseChange Λ := by
  intro S _ S' P' g q' g' sq _ _
  have : HasInvertibleExponent Λ ℙ(Option (ULift.{u} (Fin 1)); S) := .of_hom (_ ↘ S)
  have : HasInvertibleExponent Λ S' := .of_hom g
  have : HasInvertibleExponent Λ ℙ(Option (ULift.{u} (Fin 1)); S') := .of_hom (_ ↘ S')
  have sq₀ := ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1))) g
  have h₀ : IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq₀) := by
    obtain ⟨adj, adj', hc⟩ := h g
    have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq₀
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact isIso_mateEquiv_app_of_counit (rightDerivedUpperShriekAdjunction _ _)
      (rightDerivedUpperShriekAdjunction _ _) adj adj'
      (inv (rightDerivedLowerShriekBaseChangeMap Λ sq₀)) K
      ((leftDerivedUpperStarTwistShiftIso Λ _ 1 _).hom ≫
        (twistShift Λ _ 1).map ((derivedSquareUpperStarIso _ sq₀.toCommSq).inv.app K))
      (by simp [← hc K])
  let e := sq.isoIsPullback _ _ sq₀
  have sqe : IsPullback g' e.hom (𝟙 _) (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g) :=
    IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, IsPullback.isoIsPullback_hom_fst]⟩
  have : HasCompactification (𝟙 ℙ(Option (ULift.{u} (Fin 1)); S)) :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  have : HasCompactification e.hom := (Compactification.ofIsOpenImmersion _).hasCompactification
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion_right Λ sqe
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  exact (isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff sqe sq₀ sq (Category.id_comp _)
    (IsPullback.isoIsPullback_hom_snd _ _ _ _) K inferInstance).2 inferInstance

end Adjunction

end Etale

end AlgebraicGeometry

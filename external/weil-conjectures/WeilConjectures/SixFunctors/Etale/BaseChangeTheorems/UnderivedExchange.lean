/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.SeparablyClosed
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.FibreSections
public import WeilConjectures.SixFunctors.BaseChange.Sections
public import WeilConjectures.SixFunctors.BaseChange.Forget
public import WeilConjectures.SixFunctors.Finite.Descent

/-!
# The underived proper base change

For a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper, the underived base change map `g^* f_* F ⟶ f'_* g'^* F` of
`AlgebraicGeometry.Etale.baseChangeMap` is an isomorphism for every étale sheaf `F` of
`Λ`-modules on `X`. At a geometric point `ȳ'` of `Y'` lying over the geometric point `ȳ` of
`Y`, both stalks are the sections of `F` over the same closed geometric fibre
`X_ȳ = X'_ȳ'`: the stalk of `f_* F` at `ȳ` is `Γ(X ×_Y Y_(ȳ), F|)` over the strict
henselisation, which is `Γ(X_ȳ, F|)` by the degree-zero comparison over a strictly henselian
base, and likewise for `f'`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isProper`: the underived proper base change.

## References

- Stacks Project, Lemma 59.91.5, <https://stacks.math.columbia.edu/tag/0A3T>
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

set_option backward.isDefEq.respectTransparency false in
/-- **The stalks of the underived proper exchange.** For a cartesian square with `f` proper and
an algebraically closed geometric point `y'` of `Y'`, the base change map
`g^* f_* F ⟶ f'_* g'^* F` of abelian étale sheaves is bijective on stalks at `y'`: through the
stalk formula `AlgebraicGeometry.Etale.bijective_stalkToFibreSections_of_isProper`, both stalks
are the sections over the geometric fibre `X' ×_{Y'} Spec Ω = X ×_Y Spec Ω`, and the base change
map becomes the identity of these sections. -/
lemma Etale.bijective_sheafFiber_map_baseChangeMap_of_isProper {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    [IsProper f] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] (y' : Spec (.of Ω) ⟶ Y') :
    Function.Bijective ((pointSmallEtale y').sheafFiber.map
      ((Etale.baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app F)) := by
  have : IsProper f' := MorphismProperty.of_isPullback sq ‹_›
  let Z := pullback f' y'
  let a' : Z ⟶ X' := pullback.fst f' y'
  let b' : Z ⟶ Spec (.of Ω) := pullback.snd f' y'
  have h' : IsPullback a' b' f' y' := IsPullback.of_hasPullback f' y'
  have hP : IsPullback (a' ≫ g') b' f (y' ≫ g) := h'.paste_horiz sq
  let ζ := stalkToFibreSections f (y' ≫ g) (a' ≫ g') b' hP.w F
  let ζ' := stalkToFibreSections f' y' a' b' h'.w ((g')^*[AddCommGrpCat.{u + 1}].obj F)
  let e := (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} g y').hom.app
    ((f)_*[AddCommGrpCat.{u + 1}].obj F)
  let c := ((upperStarComp AddCommGrpCat.{u + 1} a' g' (a' ≫ g') rfl).inv.app F).hom.app
    (op (Scheme.Etale.mk (𝟙 Z)))
  have hζ : Function.Bijective ζ := bijective_stalkToFibreSections_of_isProper f (y' ≫ g)
    (a' ≫ g') b' F hP
  have hζ' : Function.Bijective ζ' := bijective_stalkToFibreSections_of_isProper f' y' a' b'
    ((g')^*[AddCommGrpCat.{u + 1}].obj F) h'
  have he : Function.Bijective e := ConcreteCategory.bijective_of_isIso e
  have hc : Function.Bijective c := ConcreteCategory.bijective_of_isIso c
  let BC := (pointSmallEtale y').sheafFiber.map
    ((Etale.baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app F)
  have key : ∀ x, c (ζ' (BC x)) = ζ (e x) := by
    intro x
    have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    obtain ⟨V, v, σ, rfl⟩ := (pointSmallEtale y').toPresheafFiber_jointly_surjective x
    let vl : Spec (.of Ω) ⟶ V.left := v.left
    obtain ⟨V₁, a, U, φ, hφ, s, ⟨w, hw⟩, hσ⟩ :=
      exists_pullSection_eq g ((f)_*[AddCommGrpCat.{u + 1}].obj F) σ (vl default)
    obtain ⟨l, hl, -⟩ := exists_fac_of_etale_of_isSepClosed a.left v.left w hw
    have hl₁ : l ≫ V₁.hom = y' := by
      rw [← MorphismProperty.Over.w a, ← Category.assoc, hl]
      exact CategoryTheory.Over.w v
    have hv : (pointSmallEtale y').fiber.map a (fiberPt l hl₁) = v :=
      CategoryTheory.Over.OverMorphism.ext hl
    rw [← hv, ← GrothendieckTopology.Point.toPresheafFiber_w_apply]
    erw [hσ]
    have h₁ := GrothendieckTopology.Point.toPresheafFiber_naturality_apply (pointSmallEtale y')
      ((Etale.baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app F).hom V₁ (fiberPt l hl₁)
      (pullSection g ((f)_*[AddCommGrpCat.{u + 1}].obj F) φ hφ s)
    rw [baseChangeMap_app_pullSection] at h₁
    have h₃ := upperStarCompSheafFiberIso_hom_toPresheafFiber_pullSection g
      ((f)_*[AddCommGrpCat.{u + 1}].obj F) y' φ hφ s (fiberPt l hl₁)
    erw [h₁, h₃, toPresheafFiber_stalkToFibreSections, toPresheafFiber_stalkToFibreSections]
    rw [fibreRestriction_apply, fibreRestriction_apply]
    simp only [c]
    rw [← restrictAlong_apply, restrictAlong_pullSection]
    refine pullSection_congr _ _ _ ?_ _
    apply pullback.hom_ext <;> simp
  have h₁ : Function.Bijective (c ∘ ζ' ∘ BC) := by
    rw [show c ∘ ζ' ∘ BC = ζ ∘ e from funext key]
    exact hζ.comp he
  exact (Function.Bijective.of_comp_iff' (hc.comp hζ') BC).1 h₁

/-- **The underived proper exchange is an isomorphism**: for a cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper, the base change map `g^* f_* F ⟶ f'_* g'^* F` is an isomorphism for every
étale sheaf `F` of `Λ`-modules on `X`. At a geometric point `ȳ'` of `Y'` both stalks are the
sections of `F` over the closed geometric fibre `X_ȳ = X'_ȳ'`, by the stalk formula over the
strict henselisation and the degree-zero comparison
`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_geometricFibre`, and the induced
map of stalks is the identity; geometric stalks are conservative.
(blueprint: `proposition-proper-base-change-degree-zero`) -/
@[stacks 0A3T]
theorem Etale.isIso_baseChangeMap_of_isProper {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) [IsProper f] :
    IsIso (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  rw [isIso_baseChangeMap_app_iff_forget₂]
  refine Scheme.isIso_of_isIso_sheafFiber_map _ fun y' ↦ ?_
  have : IsIso ((pointSmallEtale (Y'.algClosurePoint y')).sheafFiber.map
      ((Etale.baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F))) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (Etale.bijective_sheafFiber_map_baseChangeMap_of_isProper sq _ _)
  change IsIso (((pointSmallEtale (Y'.algClosurePoint y')).ulift.{u + 1}).sheafFiber.map _)
  rw [← NatIso.naturality_2 ((pointSmallEtale (Y'.algClosurePoint y')).uliftSheafFiberIso
    AddCommGrpCat.{u + 1})]
  infer_instance

end AlgebraicGeometry

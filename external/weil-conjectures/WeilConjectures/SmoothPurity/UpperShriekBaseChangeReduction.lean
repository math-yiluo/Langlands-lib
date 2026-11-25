/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRestrictionOfHomEq
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionConservative
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionLowerShriekCanonical
public import WeilConjectures.SmoothPurity.UpperShriekBaseChangePasting
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange

/-!
# Smooth base change for `Rf^!` from finite coefficients, along any morphism

For a cartesian square of separated `k`-schemes of finite type
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
with `f` smooth, this file reduces the invertibility of the exceptional base change map
`Lg'^* Rf^! L ⟶ Rf'^! Lg^* L` with `ℚ̄_ℓ`-coefficients
(`ProEtale.CondensedRing.upperShriekBaseChange`), for an *arbitrary* `g`, to smooth base change
with finite étale coefficients
(`Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension`) and a single
coherence: the compatibility of the reduction modulo `ℓ`, read on the étale site
(`ProEtale.CondensedRing.etaleReduction`), with compact-support base change `Ex_!`
(`ProEtale.CondensedRing.EtaleReductionLowerShriekBaseChangeCompatible`).

## The argument

The exceptional base change map is the mate of the inverse of `Ex_!` under the adjunctions
`Rf_! ⊣ Rf^!` and `Rf'_! ⊣ Rf'^!`, for all coefficient rings. A coefficient change commuting with
`Rf_!`, `Rf'_!`, `Lg^*` and `Lg'^*` compatibly with `Ex_!` carries the mate to the mate, up to the
exchanges for `Rf^!` and `Rf'^!` (`CategoryTheory.Adjunction.map_mateEquiv_app_comp`).

* For the extensions of scalars `𝒪_E ⟶ E ⟶ ℚ̄_ℓ` the compatibility with `Ex_!` is
  `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_extendScalars` and
  `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_toPadicAlgCl`, and the
  exchanges for `Rf^!` are invertible. So the `ℚ̄_ℓ` map is invertible at the image of an
  integral complex as soon as the `𝒪_E` map
  (`ProEtale.CondensedRing.PadicIntegersRingObj.upperShriekBaseChange`) is invertible there
  (`ProEtale.CondensedRing.isIso_upperShriekBaseChange_of_forall_isIso_integral`); every
  bounded constructible `ℚ̄_ℓ`-complex has an integral model.
* For the reduction modulo `ℓ`, read on the étale site, compatibility with `Ex_!` is the
  hypothesis `EtaleReductionLowerShriekBaseChangeCompatible`, for comparisons
  `γ : Rf_! ⋙ red ≅ red ⋙ Rf_!` with invertible transposes. Then the reduction of the `𝒪_E` map
  is identified with the étale exceptional base change map, which is invertible by smooth base
  change with finite coefficients, and the reduction modulo `ℓ` reflects isomorphisms
  (`ProEtale.CondensedRing.isIso_of_isIso_etaleReduction_map`)
  (`ProEtale.CondensedRing.isIso_upperShriekBaseChange_integral_of_compatible`).

* Reduction to proper morphisms: writing `f = j ≫ p` for the chosen compactification, the map
  for `f` is the restriction along an open immersion of the map for the proper `p`
  (`ProEtale.CondensedRing.isIso_upperStar_map_upperShriekBaseChange_iff`), and so is the étale
  one
  (`Etale.isIso_leftDerivedUpperStar_map_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion`).
  For the proper `p` the canonical comparison `ProEtale.CondensedRing.etaleReductionLowerShriekIso`
  is available, so the only remaining input is its compatibility with `Ex_!`
  (`ProEtale.CondensedRing.EtaleReductionProperBaseChangeCompatible`).

## Main results

- `ProEtale.CondensedRing.isIso_upperShriekBaseChange_of_etaleReductionCompatible`: smooth base
  change for `Rf^!` with `ℚ̄_ℓ`-coefficients along any `g`, for `f` smooth of relative dimension
  `d`, given comparisons of the reduction modulo `ℓ` with `Rf_!`, `Rf'_!` compatible with `Ex_!`.
- `ProEtale.CondensedRing.isIso_upperShriekBaseChange_of_etaleReductionProperCompatible`: the
  same, given only that the canonical comparison `etaleReductionLowerShriekIso` for the proper
  part `p` of the chosen compactification of `f` and for its base change along `g` is compatible
  with `Ex_!`.
- `isIso_upperShriekBaseChange_of_smooth_of_etaleReductionProperCompatibleAll`: for every
  smooth `f`, every `g` and every `L`, given the single coherence statement
  `ProEtale.CondensedRing.EtaleReductionProperBaseChangeCompatibleAll`.

## The remaining coherence

`EtaleReductionProperBaseChangeCompatible` is not proved here. Through `Rp_! ≅ Rp_*` on both
sides (`boundedConstructibleLowerShriekIsoLowerStar_padicIntegers`,
`Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`) it is the compatibility of the
reduction with proper base change `Ex_*`, the mate of the square isomorphisms of the pullbacks.
It amounts to two coherences for `red = ρ ∘ red^{cond}`: the pullback comparison
`etaleReductionUpperStarIso` is compatible with the composition isomorphisms of the pullbacks,
and the pushforward comparison of the étale reading
(`ProEtale.CondensedRing.finiteEtaleReadingLowerStarIso`) is the mate of its pullback
comparison.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **Smooth base change restricted to an open part of a compactification**, with finite
coefficients: let `j : X ⟶ Z` be an open immersion and `p : Z ⟶ Y` a morphism such that
`j ≫ p` is smooth of relative dimension `d`, let `g : Y' ⟶ Y` be a morphism with base change
`p' : Z' ⟶ Y'` of `p`, and let `o : X'' ⟶ Z'` be the base change of `j`. Then `Lo^*` of the
exceptional base change map `Lg'^* Rp^! K ⟶ Rp'^! Lg^* K` of `p` is an isomorphism: through the
composition law of base change maps (`isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff`) it is
`Ro^! ≅ Lo^*` of it, and the base change maps of `j ≫ p` and of `j` are isomorphisms by smooth
base change (`isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension`). -/
theorem isIso_leftDerivedUpperStar_map_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion
    {X Z Y X'' Z' Y' : Scheme.{u}} [QuasiSeparatedSpace Y] [QuasiSeparatedSpace Z]
    [HasInvertibleExponent Λ X] (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d (j ≫ p)] {g : Y' ⟶ Y} {q : Z' ⟶ Z} {p' : Z' ⟶ Y'}
    (sqp : IsPullback q p' p g) {a : X'' ⟶ X} {o : X'' ⟶ Z'} (sqo : IsPullback a o j q)
    [HasCompactification j] [HasCompactification p] [HasCompactification (j ≫ p)]
    [HasCompactification o] [HasCompactification p'] [HasCompactification (o ≫ p')]
    [QuasiCompact o] [QuasiCompact p'] [QuasiCompact (o ≫ p')]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((L((o)^*[ModuleCat.{u + 1} Λ])).map
      ((rightDerivedUpperShriekBaseChangeMap Λ sqp).app K)) := by
  have : SmoothOfRelativeDimension 0 j :=
    (iff_smoothOfRelativeDimension_zero j).1 inferInstance
  have : IsOpenImmersion o := MorphismProperty.of_isPullback sqo inferInstance
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ j 0 sqo
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ (j ≫ p) d
    (sqo.paste_vert sqp)
  have h := (isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff sqo sqp (sqo.paste_vert sqp)
    rfl rfl K inferInstance).1 inferInstance
  exact (NatIso.isIso_map_iff (rightDerivedUpperShriekIsoOfIsOpenImmersion Λ o ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) o).symm) _).1 h

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-! ### The exceptional base change map with `𝒪_E`- and `E`-coefficients -/

/-- Compact-support base change `Ex_! : Rf_! ⋙ Lg^* ≅ Lg'^* ⋙ Rf'_!` with `𝒪_E`-coefficients, as
an isomorphism (`isIso_boundedConstructibleLowerShriekBaseChange_padicIntegers`). -/
noncomputable def PadicIntegersRingObj.lowerShriekBaseChangeIso (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] (sq : IsPullback g' f' f g) :
    PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ⋙
        boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g ≅
      boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g' ⋙
        PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f' :=
  @asIso _ _ _ _ (boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E sq)
    (isIso_boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E sq)

/-- The exceptional base change map `Rf^! ⋙ Lg'^* ⟶ Lg^* ⋙ Rf'^!` with `𝒪_E`-coefficients: the
mate of the inverse of compact-support base change
(`ProEtale.CondensedRing.PadicIntegersRingObj.lowerShriekBaseChangeIso`) under the adjunctions
`Rf_! ⊣ Rf^!` and `Rf'_! ⊣ Rf'^!`. -/
noncomputable def PadicIntegersRingObj.upperShriekBaseChange (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] (sq : IsPullback g' f' f g) :
    PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E f ⋙
        boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g' ⟶
      boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g ⋙
        PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E f' :=
  (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f')
    (TwoSquare.mk _ _ _ _ (PadicIntegersRingObj.lowerShriekBaseChangeIso ℓ E sq).inv))

/-- Compact-support base change `Ex_! : Rf_! ⋙ Lg^* ≅ Lg'^* ⋙ Rf'_!` with `E`-coefficients, as an
isomorphism (`isIso_boundedConstructibleLowerShriekBaseChange_padicSubfield`). -/
noncomputable def ContinuousMapRingObj.lowerShriekBaseChangeIso (E : FiniteIntermediateField ℓ)
    (sq : IsPullback g' f' f g) :
    ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E f ⋙
        boundedConstructibleUpperStar (Profinite.continuousMapRingObj E.1) ℓ g ≅
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E.1) ℓ g' ⋙
        ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E f' :=
  asIso (boundedConstructibleLowerShriekBaseChange_padicSubfield ℓ E sq)

/-- The exceptional base change map `Rf^! ⋙ Lg'^* ⟶ Lg^* ⋙ Rf'^!` with `E`-coefficients, for a
finite subextension `E ⊆ ℚ̄_ℓ`: the mate of the inverse of compact-support base change
(`ProEtale.CondensedRing.ContinuousMapRingObj.lowerShriekBaseChangeIso`). -/
noncomputable def ContinuousMapRingObj.upperShriekBaseChange (E : FiniteIntermediateField ℓ)
    (sq : IsPullback g' f' f g) :
    ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E f ⋙
        boundedConstructibleUpperStar (Profinite.continuousMapRingObj E.1) ℓ g' ⟶
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E.1) ℓ g ⋙
        ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E f' :=
  (mateEquiv (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f')
    (TwoSquare.mk _ _ _ _ (ContinuousMapRingObj.lowerShriekBaseChangeIso ℓ E sq).inv))

/-- Compact-support base change `Ex_! : Rf_! ⋙ Lg^* ≅ Lg'^* ⋙ Rf'_!` with `ℚ̄_ℓ`-coefficients, as
an isomorphism (`isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl`). -/
noncomputable def lowerShriekBaseChangeIso (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriek ℓ f ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g' ⋙
        boundedConstructibleLowerShriek ℓ f' :=
  @asIso _ _ _ _ (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
    (isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)

/-- The exceptional base change map with `ℚ̄_ℓ`-coefficients is the mate of the inverse of the
isomorphism `ProEtale.CondensedRing.lowerShriekBaseChangeIso`. -/
lemma upperShriekBaseChangeNatTrans_eq_mateEquiv (sq : IsPullback g' f' f g) :
    upperShriekBaseChangeNatTrans ℓ sq =
      (mateEquiv (boundedConstructibleUpperShriekAdjunction ℓ f)
        (boundedConstructibleUpperShriekAdjunction ℓ f')
        (TwoSquare.mk _ _ _ _ (lowerShriekBaseChangeIso ℓ sq).inv)) :=
  rfl

/-! ### Coefficient change from `𝒪_E` to `ℚ̄_ℓ` -/

/-- The extension of scalars `T : 𝒪_E ⟶ E` carries the exceptional base change map with
`𝒪_E`-coefficients to the one with `E`-coefficients, up to the exchanges for `Rf^!` and `Rf'^!`:
for every functor `G`, if `G` inverts `T` of the former at `P`, then it inverts the latter at
`T P`. -/
theorem isIso_map_upperShriekBaseChange_padicSubfield_of_isIso_map
    (E : FiniteIntermediateField ℓ) (sq : IsPullback g' f' f g)
    (P : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) {C : Type*} [Category* C]
    (G : Dᵇc(X'.left)⟦Profinite.continuousMapRingObj E.1⟧ ⥤ C)
    (hG : IsIso (G.map ((boundedConstructibleExtendScalars X'.left ℓ E).map
      ((PadicIntegersRingObj.upperShriekBaseChange ℓ E.1 sq).app P)))) :
    IsIso (G.map ((ContinuousMapRingObj.upperShriekBaseChange ℓ E sq).app
      ((boundedConstructibleExtendScalars Y.left ℓ E).obj P))) := by
  have e : (PadicIntegersRingObj.lowerShriekBaseChangeIso ℓ E.1 sq).hom =
      boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E.1 sq := rfl
  have e' : (ContinuousMapRingObj.lowerShriekBaseChangeIso ℓ E sq).hom =
      boundedConstructibleLowerShriekBaseChange_padicSubfield ℓ E sq := rfl
  have h := Adjunction.map_mateEquiv_app_comp_of_hom_eq
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 f)
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 f')
    (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ g')
    (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ g)
    (PadicIntegersRingObj.lowerShriekBaseChangeIso ℓ E.1 sq)
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f')
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E.1) ℓ g')
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E.1) ℓ g)
    (ContinuousMapRingObj.lowerShriekBaseChangeIso ℓ E sq)
    (boundedConstructibleExtendScalars Y.left ℓ E) (boundedConstructibleExtendScalars X.left ℓ E)
    (boundedConstructibleExtendScalars X'.left ℓ E)
    (boundedConstructibleExtendScalars Y'.left ℓ E)
    (boundedConstructibleLowerShriekExtendScalarsIso ℓ E f)
    (boundedConstructibleLowerShriekExtendScalarsIso ℓ E f')
    (boundedConstructibleUpperStarExtendScalarsIso ℓ E g')
    (boundedConstructibleUpperStarExtendScalarsIso ℓ E g) e e'
    (by with_reducible exact boundedConstructibleLowerShriekBaseChange_extendScalars ℓ E sq) P
  have : IsIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 f)
      (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
      (TwoSquare.mk _ _ _ _
        (boundedConstructibleLowerShriekExtendScalarsIso ℓ E f).inv)) :=
    isIso_boundedConstructibleUpperShriekExtendScalars ℓ E f
  have : IsIso (mateEquiv
      (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 f')
      (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f')
      (TwoSquare.mk _ _ _ _
        (boundedConstructibleLowerShriekExtendScalarsIso ℓ E f').inv)) :=
    isIso_boundedConstructibleUpperShriekExtendScalars ℓ E f'
  have h₁ := congrArg G.map h
  simp only [Functor.map_comp] at h₁
  unfold PadicIntegersRingObj.upperShriekBaseChange at hG
  have hR := cast (congrArg IsIso h₁) inferInstance
  rw [isIso_comp_left_iff, isIso_comp_left_iff] at hR
  exact hR

/-- The extension of scalars `T : E ⟶ ℚ̄_ℓ` carries the exceptional base change map with
`E`-coefficients to the one with `ℚ̄_ℓ`-coefficients, up to the exchanges for `Rf^!` and `Rf'^!`:
for every functor `G`, if `G` inverts `T` of the former at `P`, then it inverts the latter at
`T P`. -/
theorem isIso_map_upperShriekBaseChange_of_isIso_map_padicSubfield
    (E : FiniteIntermediateField ℓ) (sq : IsPullback g' f' f g)
    (P : Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E.1⟧) {C : Type*} [Category* C]
    (G : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ C)
    (hG : IsIso (G.map ((boundedConstructibleToPadicAlgCl X'.left ℓ E).map
      ((ContinuousMapRingObj.upperShriekBaseChange ℓ E sq).app P)))) :
    IsIso (G.map (upperShriekBaseChange ℓ sq
      ((boundedConstructibleToPadicAlgCl Y.left ℓ E).obj P))) := by
  have e : (ContinuousMapRingObj.lowerShriekBaseChangeIso ℓ E sq).hom =
      boundedConstructibleLowerShriekBaseChange_padicSubfield ℓ E sq := rfl
  have e' : (lowerShriekBaseChangeIso ℓ sq).hom =
      boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq := rfl
  have h := Adjunction.map_mateEquiv_app_comp_of_hom_eq
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f')
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E.1) ℓ g')
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E.1) ℓ g)
    (ContinuousMapRingObj.lowerShriekBaseChangeIso ℓ E sq)
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleUpperShriekAdjunction ℓ f')
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)
    (lowerShriekBaseChangeIso ℓ sq)
    (boundedConstructibleToPadicAlgCl Y.left ℓ E) (boundedConstructibleToPadicAlgCl X.left ℓ E)
    (boundedConstructibleToPadicAlgCl X'.left ℓ E)
    (boundedConstructibleToPadicAlgCl Y'.left ℓ E)
    (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f)
    (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f')
    (boundedConstructibleUpperStarToPadicAlgClIso ℓ E g')
    (boundedConstructibleUpperStarToPadicAlgClIso ℓ E g) e e'
    (by with_reducible exact boundedConstructibleLowerShriekBaseChange_toPadicAlgCl ℓ E sq) P
  have : IsIso (mateEquiv (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
      (boundedConstructibleUpperShriekAdjunction ℓ f)
      (TwoSquare.mk _ _ _ _
        (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f).inv)) :=
    isIso_boundedConstructibleUpperShriekToPadicAlgCl ℓ E f
  have : IsIso (mateEquiv (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f')
      (boundedConstructibleUpperShriekAdjunction ℓ f')
      (TwoSquare.mk _ _ _ _
        (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f').inv)) :=
    isIso_boundedConstructibleUpperShriekToPadicAlgCl ℓ E f'
  have h₁ := congrArg G.map h
  simp only [Functor.map_comp] at h₁
  unfold ContinuousMapRingObj.upperShriekBaseChange at hG
  have hR := cast (congrArg IsIso h₁) inferInstance
  rw [isIso_comp_left_iff, isIso_comp_left_iff] at hR
  rw [upperShriekBaseChange_eq_upperShriekBaseChangeNatTrans_app,
    upperShriekBaseChangeNatTrans_eq_mateEquiv]
  exact hR

/-- **From integral to `ℚ̄_ℓ`-coefficients, after pullback**: let `o : Z ⟶ X'` be a morphism. If,
for every finite subextension `E ⊆ ℚ̄_ℓ`, the pullback `Lo^*` of the exceptional base change map
with `𝒪_E`-coefficients is an isomorphism, then so is `Lo^*` of the one with `ℚ̄_ℓ`-coefficients.
Every bounded constructible `ℚ̄_ℓ`-complex `L` is the extension of scalars of an integral model
(`ProEtale.exists_padicAlgCl_iso_integralModel`), the coefficient changes `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`
commute with `Lo^*` and carry the exceptional base change maps to each other
(`isIso_map_upperShriekBaseChange_padicSubfield_of_isIso_map`,
`isIso_map_upperShriekBaseChange_of_isIso_map_padicSubfield`). -/
theorem isIso_upperStar_map_upperShriekBaseChange_of_forall_integral
    (sq : IsPullback g' f' f g) {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] (o : Z ⟶ X')
    (h : ∀ (E : FiniteIntermediateField ℓ) (P : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧),
      IsIso ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ o).map
        ((PadicIntegersRingObj.upperShriekBaseChange ℓ E.1 sq).app P)))
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ o).map
      (upperShriekBaseChange ℓ sq L)) := by
  have := noetherianSpace_left_of_over Y
  obtain ⟨E, P, ⟨e⟩⟩ := exists_padicAlgCl_iso_integralModel (X := Y.left) ℓ L
  have h₁ : IsIso ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E.1) ℓ o).map
      ((ContinuousMapRingObj.upperShriekBaseChange ℓ E sq).app
        ((boundedConstructibleExtendScalars Y.left ℓ E).obj P))) := by
    refine isIso_map_upperShriekBaseChange_padicSubfield_of_isIso_map ℓ E sq P _ ?_
    have := h E P
    exact (NatIso.isIso_map_iff (boundedConstructibleUpperStarExtendScalarsIso ℓ E o) _).1
      (inferInstanceAs (IsIso ((boundedConstructibleExtendScalars Z.left ℓ E).map _)))
  have h₂ : IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ o).map
      (upperShriekBaseChange ℓ sq ((boundedConstructibleToPadicAlgCl Y.left ℓ E).obj
        ((boundedConstructibleExtendScalars Y.left ℓ E).obj P)))) := by
    refine isIso_map_upperShriekBaseChange_of_isIso_map_padicSubfield ℓ E sq _ _ ?_
    exact (NatIso.isIso_map_iff (boundedConstructibleUpperStarToPadicAlgClIso ℓ E o) _).1
      (inferInstanceAs (IsIso ((boundedConstructibleToPadicAlgCl Z.left ℓ E).map _)))
  rw [upperShriekBaseChange_eq_upperShriekBaseChangeNatTrans_app] at h₂ ⊢
  exact (NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight (upperShriekBaseChangeNatTrans ℓ sq)
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ o)) e).1 h₂

/-- **From integral to `ℚ̄_ℓ`-coefficients**: if, for every finite subextension `E ⊆ ℚ̄_ℓ`, the
exceptional base change map with `𝒪_E`-coefficients is an isomorphism, then so is the one with
`ℚ̄_ℓ`-coefficients (`isIso_upperStar_map_upperShriekBaseChange_of_forall_integral` for
`o = 𝟙`). -/
theorem isIso_upperShriekBaseChange_of_forall_isIso_integral (sq : IsPullback g' f' f g)
    (h : ∀ (E : FiniteIntermediateField ℓ) (P : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧),
      IsIso ((PadicIntegersRingObj.upperShriekBaseChange ℓ E.1 sq).app P))
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (upperShriekBaseChange ℓ sq L) := by
  have h' := isIso_upperStar_map_upperShriekBaseChange_of_forall_integral ℓ sq (𝟙 X')
    (fun E P ↦ by have := h E P; infer_instance) L
  rwa [← NatIso.isIso_map_iff (boundedConstructibleUpperStarId _ ℓ X').symm] at h'

/-! ### Reduction modulo `ℓ` and smooth base change with finite coefficients -/

section Reduction

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-- **Compatibility of the reduction modulo `ℓⁿ` with compact-support base change** (blueprint
`sk-thm-sf-compatibility`, (7), for the coefficient map `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ` read on the étale
site): for comparisons `γ_f : Rf_! ⋙ red_Y ≅ red_X ⋙ Rf_!` and `γ_{f'}`, the reduction of
compact-support base change `Ex_!` with `𝒪_E`-coefficients, read through `γ_{f'}` and the
pullback comparison for `g'` (`etaleReductionUpperStarIso`), is the étale compact-support base
change `Etale.rightDerivedLowerShriekBaseChangeMap` of the reduction, read through the pullback
comparison for `g` and `γ_f`:
```
red(Lg^* Rf_! M) ⟶ red(Rf'_! Lg'^* M) ≅ Rf'_! red(Lg'^* M) ≅ Rf'_! Lg'^* red M
      ‖                                                              ‖
Lg^* red(Rf_! M) ≅ Lg^* Rf_! red M --------------Ex_!------------> Rf'_! Lg'^* red M
```
-/
def EtaleReductionLowerShriekBaseChangeCompatible (sq : IsPullback g' f' f g)
    [HasCompactification f.left] [HasCompactification f'.left]
    (γf : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ⋙ etaleReduction ℓ E n Y ≅
      etaleReduction ℓ E n X ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left)
    (γf' : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f' ⋙ etaleReduction ℓ E n Y' ≅
      etaleReduction ℓ E n X' ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f'.left) :
    Prop :=
  ∀ M : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧,
    (etaleReduction ℓ E n Y').map
        ((boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E sq).app M) ≫
      γf'.hom.app
        ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g').obj M) ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
        f'.left).map ((etaleReductionUpperStarIso ℓ E n g').hom.app M) =
    (etaleReductionUpperStarIso ℓ E n g).hom.app
        ((PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f).obj M) ≫
      (L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g.left)).map
        (γf.hom.app M) ≫
      (Etale.rightDerivedLowerShriekBaseChangeMap (integersModPowCoeff.{u} ℓ E n) sq.overLeft).app
        ((etaleReduction ℓ E n X).obj M)

/-- **The reduction of the exceptional base change map with `𝒪_E`-coefficients**: for
comparisons `γ_f`, `γ_{f'}` of the reduction modulo `ℓ` with `Rf_!` and `Rf'_!` whose transposes
`(Rf^! K)_{𝒪_E ⧸ ℓ} ⟶ Rf^! (K_{𝒪_E ⧸ ℓ})` are invertible and which are compatible with
compact-support base change (`EtaleReductionLowerShriekBaseChangeCompatible`), the reduction of
the exceptional base change map `Lg'^* Rf^! P ⟶ Rf'^! Lg^* P` is, up to isomorphisms, the étale
exceptional base change map of the reduction of `P`
(`CategoryTheory.Adjunction.map_mateEquiv_app_comp_of_hom_eq`). So every functor `G` which
inverts the latter inverts the former. -/
theorem isIso_map_etaleReduction_map_upperShriekBaseChange_integral (sq : IsPullback g' f' f g)
    [HasCompactification f.left] [HasCompactification f'.left]
    (γf : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ⋙ etaleReduction ℓ E 1 Y ≅
      etaleReduction ℓ E 1 X ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E 1)) f.left)
    (γf' : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f' ⋙ etaleReduction ℓ E 1 Y' ≅
      etaleReduction ℓ E 1 X' ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E 1)) f'.left)
    (hγf : IsIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
      (Etale.rightDerivedUpperShriekAdjunction _ f.left) (TwoSquare.mk _ _ _ _ γf.inv)))
    (hγf' : IsIso (mateEquiv
      (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f')
      (Etale.rightDerivedUpperShriekAdjunction _ f'.left) (TwoSquare.mk _ _ _ _ γf'.inv)))
    (hσ : EtaleReductionLowerShriekBaseChangeCompatible ℓ E 1 sq γf γf')
    (P : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) {C : Type*} [Category* C]
    (G : DerivedCategory (Sheaf X'.left.smallEtaleTopology
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E 1))) ⥤ C)
    (hG : IsIso (G.map ((Etale.rightDerivedUpperShriekBaseChangeMap
      (integersModPowCoeff.{u} ℓ E 1) sq.overLeft).app ((etaleReduction ℓ E 1 Y).obj P)))) :
    IsIso (G.map ((etaleReduction ℓ E 1 X').map
      ((PadicIntegersRingObj.upperShriekBaseChange ℓ E sq).app P))) := by
  have := Etale.isIso_rightDerivedLowerShriekBaseChangeMap (integersModPowCoeff.{u} ℓ E 1)
    sq.overLeft
  have e : (PadicIntegersRingObj.lowerShriekBaseChangeIso ℓ E sq).hom =
      boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E sq := rfl
  have e' : (asIso (Etale.rightDerivedLowerShriekBaseChangeMap
      (integersModPowCoeff.{u} ℓ E 1) sq.overLeft)).hom =
      Etale.rightDerivedLowerShriekBaseChangeMap (integersModPowCoeff.{u} ℓ E 1) sq.overLeft := rfl
  unfold EtaleReductionLowerShriekBaseChangeCompatible at hσ
  have h := Adjunction.map_mateEquiv_app_comp_of_hom_eq
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f')
    (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g')
    (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g)
    (PadicIntegersRingObj.lowerShriekBaseChangeIso ℓ E sq)
    (Etale.rightDerivedUpperShriekAdjunction _ f.left)
    (Etale.rightDerivedUpperShriekAdjunction _ f'.left)
    (L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E 1)) g'.left))
    (L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E 1)) g.left))
    (asIso (Etale.rightDerivedLowerShriekBaseChangeMap
      (integersModPowCoeff.{u} ℓ E 1) sq.overLeft))
    (etaleReduction ℓ E 1 Y) (etaleReduction ℓ E 1 X) (etaleReduction ℓ E 1 X')
    (etaleReduction ℓ E 1 Y') γf γf' (etaleReductionUpperStarIso ℓ E 1 g')
    (etaleReductionUpperStarIso ℓ E 1 g) e e' (by with_reducible exact hσ) P
  have hG' : IsIso (G.map ((mateEquiv (Etale.rightDerivedUpperShriekAdjunction _ f.left)
      (Etale.rightDerivedUpperShriekAdjunction _ f'.left)
      (TwoSquare.mk _ _ _ _ (asIso (Etale.rightDerivedLowerShriekBaseChangeMap
        (integersModPowCoeff.{u} ℓ E 1) sq.overLeft)).inv)).app
          ((etaleReduction ℓ E 1 Y).obj P))) := hG
  have h₁ := congrArg G.map h
  simp only [Functor.map_comp] at h₁
  have hR := cast (congrArg IsIso h₁.symm) inferInstance
  rw [isIso_comp_right_iff] at hR
  exact hR

/-- **Smooth base change for `Rf^!` with `𝒪_E`-coefficients, from finite coefficients**: let
`f` be smooth of relative dimension `d` and let `γ_f`, `γ_{f'}` be comparisons of the reduction
modulo `ℓ` with `Rf_!` and `Rf'_!` whose transposes `(Rf^! K)_{𝒪_E ⧸ ℓ} ⟶ Rf^! (K_{𝒪_E ⧸ ℓ})`
are invertible and which are compatible with compact-support base change
(`EtaleReductionLowerShriekBaseChangeCompatible`). Then the exceptional base change map
`Lg'^* Rf^! P ⟶ Rf'^! Lg^* P` with `𝒪_E`-coefficients is an isomorphism: its reduction is
identified with the étale exceptional base change map of the reduction
(`isIso_map_etaleReduction_map_upperShriekBaseChange_integral`), invertible by smooth base change
with finite coefficients
(`Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension`), and the
reduction reflects isomorphisms (`isIso_of_isIso_etaleReduction_map`). -/
theorem isIso_upperShriekBaseChange_integral_of_compatible (sq : IsPullback g' f' f g) (d : ℕ)
    [SmoothOfRelativeDimension d f.left] [HasCompactification f.left]
    [HasCompactification f'.left]
    (γf : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ⋙ etaleReduction ℓ E 1 Y ≅
      etaleReduction ℓ E 1 X ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E 1)) f.left)
    (γf' : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f' ⋙ etaleReduction ℓ E 1 Y' ≅
      etaleReduction ℓ E 1 X' ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E 1)) f'.left)
    (hγf : IsIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
      (Etale.rightDerivedUpperShriekAdjunction _ f.left) (TwoSquare.mk _ _ _ _ γf.inv)))
    (hγf' : IsIso (mateEquiv
      (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f')
      (Etale.rightDerivedUpperShriekAdjunction _ f'.left) (TwoSquare.mk _ _ _ _ γf'.inv)))
    (hσ : EtaleReductionLowerShriekBaseChangeCompatible ℓ E 1 sq γf γf')
    (P : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    IsIso ((PadicIntegersRingObj.upperShriekBaseChange ℓ E sq).app P) := by
  have := isNoetherian_of_locallyOfFiniteType Y.hom
  have : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E 1) X.left :=
    HasInvertibleExponent.of_hom X.hom
  have := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension
    (integersModPowCoeff.{u} ℓ E 1) f.left d sq.overLeft
  refine isIso_of_isIso_etaleReduction_map ℓ E one_ne_zero _
    (isIso_map_etaleReduction_map_upperShriekBaseChange_integral ℓ E sq γf γf' hγf hγf' hσ P
      (𝟭 _) ?_)
  exact inferInstanceAs (IsIso ((Etale.rightDerivedUpperShriekBaseChangeMap
    (integersModPowCoeff.{u} ℓ E 1) sq.overLeft).app _))

/-- The square `sq` admits comparisons of the reduction modulo `ℓ` with `Rf_!` and `Rf'_!`, with
invertible transposes, which are compatible with compact-support base change
(`EtaleReductionLowerShriekBaseChangeCompatible`). -/
def HasEtaleReductionLowerShriekBaseChangeCompatible (sq : IsPullback g' f' f g) : Prop :=
  haveI := HasCompactification.of_over f
  haveI := HasCompactification.of_over f'
  ∃ (γf : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ⋙ etaleReduction ℓ E 1 Y ≅
      etaleReduction ℓ E 1 X ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E 1)) f.left)
    (γf' : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f' ⋙ etaleReduction ℓ E 1 Y' ≅
      etaleReduction ℓ E 1 X' ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E 1)) f'.left),
    IsIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
      (Etale.rightDerivedUpperShriekAdjunction _ f.left) (TwoSquare.mk _ _ _ _ γf.inv)) ∧
    IsIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f')
      (Etale.rightDerivedUpperShriekAdjunction _ f'.left) (TwoSquare.mk _ _ _ _ γf'.inv)) ∧
    EtaleReductionLowerShriekBaseChangeCompatible ℓ E 1 sq γf γf'

end Reduction

/-- **Smooth base change for `Rf^!` along any morphism, given the compatibility of the reduction
modulo `ℓ` with compact-support base change** (SGA 4, Exposé XVIII, Théorème 3.2.5 and
Théorème 2.9 (Var 4); blueprint `proposition-compatibility-purity-base-change`): for a cartesian
square `g' ≫ f = f' ≫ g` of separated `k`-schemes of finite type with `f` smooth of relative
dimension `d` and `g` arbitrary, the exceptional base change map `Lg'^* Rf^! L ⟶ Rf'^! Lg^* L` with
`ℚ̄_ℓ`-coefficients is an isomorphism for every `L`, provided that, for every finite subextension
`E ⊆ ℚ̄_ℓ`, the reduction modulo `ℓ` admits comparisons with `Rf_!` and `Rf'_!` (with invertible
transposes) compatible with compact-support base change
(`HasEtaleReductionLowerShriekBaseChangeCompatible`). The `ℚ̄_ℓ` map comes from the `𝒪_E` maps
(`isIso_upperShriekBaseChange_of_forall_isIso_integral`), which are invertible by smooth base
change with finite coefficients (`isIso_upperShriekBaseChange_integral_of_compatible`). -/
theorem isIso_upperShriekBaseChange_of_etaleReductionCompatible (sq : IsPullback g' f' f g)
    (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (h : ∀ E : FiniteIntermediateField ℓ, HasEtaleReductionLowerShriekBaseChangeCompatible ℓ E.1 sq)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (upperShriekBaseChange ℓ sq L) := by
  have := HasCompactification.of_over f
  have := HasCompactification.of_over f'
  refine isIso_upperShriekBaseChange_of_forall_isIso_integral ℓ sq (fun E P ↦ ?_) L
  obtain ⟨γf, γf', hγf, hγf', hσ⟩ := h E
  exact isIso_upperShriekBaseChange_integral_of_compatible ℓ E.1 sq d γf γf' hγf hγf' hσ P

/-! ### Reduction to proper morphisms -/

/-- **Compatibility of the canonical reduction comparison for proper morphisms with
compact-support base change**: for a cartesian square `g' ≫ f = f' ≫ g` with `f` (hence `f'`)
proper, the canonical isomorphisms `Rf_! ⋙ red ≅ red ⋙ Rf_!` and `Rf'_! ⋙ red ≅ red ⋙ Rf'_!`
of the reduction modulo `ℓ` (`etaleReductionLowerShriekIso`) are compatible with compact-support
base change (`EtaleReductionLowerShriekBaseChangeCompatible`). -/
def EtaleReductionProperBaseChangeCompatible (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
    [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    (sq : IsPullback g' f' f g) [IsProper f.left] : Prop :=
  haveI : IsProper f'.left := MorphismProperty.of_isPullback sq.overLeft inferInstance
  haveI := HasCompactification.of_over f
  haveI := HasCompactification.of_over f'
  EtaleReductionLowerShriekBaseChangeCompatible ℓ E 1 sq (etaleReductionLowerShriekIso ℓ E 1 f)
    (etaleReductionLowerShriekIso ℓ E 1 f')

/-- **Smooth base change for `Rf^!` along any morphism, given the compatibility of the canonical
reduction comparison for proper morphisms with compact-support base change** (SGA 4, Exposé
XVIII, Théorème 3.2.5; blueprint `proposition-compatibility-purity-base-change`): let
`g' ≫ f = f' ≫ g` be a cartesian square of separated `k`-schemes of finite type with `f` smooth of
relative dimension `d` and `g` arbitrary, and write `f = j ≫ p` for the chosen compactification
(`compactificationOverField`), with `j` an open immersion and `p` proper. If, for every finite
subextension `E ⊆ ℚ̄_ℓ`, the canonical comparisons of the reduction modulo `ℓ` with `Rp_!` and with
the lower shriek of the base change of `p` along `g` are compatible with compact-support base change
(`EtaleReductionProperBaseChangeCompatible`), then the exceptional base change map
`Lg'^* Rf^! L ⟶ Rf'^! Lg^* L` with `ℚ̄_ℓ`-coefficients is an isomorphism for every `L`.

The map for `f` is the restriction along the open immersion `o : X' ⟶ Z ⨯_Y Y'` of the map for
`p` (`isIso_upperStar_map_upperShriekBaseChange_iff`); it comes from `𝒪_E`-coefficients
(`isIso_upperStar_map_upperShriekBaseChange_of_forall_integral`), where the reduction modulo `ℓ`
reflects isomorphisms and identifies it with the étale map
(`isIso_map_etaleReduction_map_upperShriekBaseChange_integral`), whose restriction along `o` is
invertible by smooth base change for `f` with finite coefficients
(`Etale.isIso_leftDerivedUpperStar_map_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion`).
-/
theorem isIso_upperShriekBaseChange_of_etaleReductionProperCompatible
    (sq : IsPullback g' f' f g) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (h : ∀ E : FiniteIntermediateField ℓ, EtaleReductionProperBaseChangeCompatible ℓ E.1
      (IsPullback.of_hasPullback (compactificationOverField f).overG g))
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (upperShriekBaseChange ℓ sq L) := by
  let c := compactificationOverField f
  have sqp := IsPullback.of_hasPullback c.overG g
  have hsq := IsPullback.of_hasPullback (c.overI ≫ c.overG) g
  rw [isIso_upperShriekBaseChange_iff_of_isPullback_of_eq ℓ c.overI_overG.symm sq hsq,
    ← isIso_upperStar_map_upperShriekBaseChange_iff ℓ sqp c.overI L]
  let o := sqp.lift (pullback.fst (c.overI ≫ c.overG) g ≫ c.overI)
    (pullback.snd (c.overI ≫ c.overG) g) (by rw [Category.assoc, pullback.condition])
  have sqo : IsPullback (pullback.fst (c.overI ≫ c.overG) g) o c.overI
      (pullback.fst c.overG g) :=
    IsPullback.of_bot ((sqp.lift_snd _ _ _).symm ▸ IsPullback.of_hasPullback _ g)
      (sqp.lift_fst _ _ _).symm sqp
  have : IsOpenImmersion o.left := MorphismProperty.of_isPullback sqo.overLeft inferInstance
  refine isIso_upperStar_map_upperShriekBaseChange_of_forall_integral ℓ sqp o (fun E P ↦ ?_) L
  have := isNoetherian_of_locallyOfFiniteType Y.hom
  have := isNoetherian_of_locallyOfFiniteType c.overObj.hom
  have : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 1) X.left :=
    HasInvertibleExponent.of_hom X.hom
  have : IsProper (pullback.snd c.overG g).left :=
    MorphismProperty.of_isPullback sqp.overLeft inferInstance
  have := HasCompactification.of_over c.overI
  have := HasCompactification.of_over c.overG
  have := HasCompactification.of_over (c.overI ≫ c.overG)
  have := HasCompactification.of_over o
  have := HasCompactification.of_over (pullback.snd c.overG g)
  have := HasCompactification.of_over (o ≫ pullback.snd c.overG g)
  have : SmoothOfRelativeDimension d (c.overI.left ≫ c.overG.left) := by
    rw [← Over.comp_left, c.overI_overG]
    infer_instance
  have hét :=
    Etale.isIso_leftDerivedUpperStar_map_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion
    (integersModPowCoeff.{u} ℓ E.1 1) c.overI.left c.overG.left d sqp.overLeft sqo.overLeft
    ((etaleReduction ℓ E.1 1 Y).obj P)
  refine isIso_of_isIso_etaleReduction_map ℓ E.1 one_ne_zero _
    ((NatIso.isIso_map_iff (etaleReductionUpperStarIso ℓ E.1 1 o) _).2 ?_)
  exact isIso_map_etaleReduction_map_upperShriekBaseChange_integral ℓ E.1 sqp
    (etaleReductionLowerShriekIso ℓ E.1 1 c.overG)
    (etaleReductionLowerShriekIso ℓ E.1 1 (pullback.snd c.overG g))
    (isIso_mateEquiv_etaleReductionLowerShriekIso ℓ E.1 1 c.overG)
    (isIso_mateEquiv_etaleReductionLowerShriekIso ℓ E.1 1 (pullback.snd c.overG g)) (h E) P
    (L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 1)) o.left)) hét

variable (k) in
/-- **The canonical reduction comparisons for proper morphisms are compatible with compact-support
base change**: for every finite subextension `E ⊆ ℚ̄_ℓ`, every proper morphism `p : Z ⟶ S` and
every morphism `g : S' ⟶ S` of separated `k`-schemes of finite type,
`EtaleReductionProperBaseChangeCompatible` holds for the fibre product square of `p` and `g`. -/
def EtaleReductionProperBaseChangeCompatibleAll : Prop :=
  ∀ (E : FiniteIntermediateField ℓ) (S S' Z : Over (Spec (.of k))) [LocallyOfFiniteType S.hom]
    [QuasiCompact S.hom] [IsSeparated S.hom] [LocallyOfFiniteType S'.hom] [QuasiCompact S'.hom]
    [IsSeparated S'.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (p : Z ⟶ S) [IsProper p.left] (g : S' ⟶ S),
    EtaleReductionProperBaseChangeCompatible ℓ E.1 (IsPullback.of_hasPullback p g)

/-- **Smooth base change for `Rf^!`, modulo the compatibility of the reduction with
compact-support base change**: if the canonical reduction comparisons for proper morphisms are
compatible with compact-support base change (`EtaleReductionProperBaseChangeCompatibleAll`), then
for every cartesian square `g' ≫ f = f' ≫ g` of separated `k`-schemes of finite type with `f`
smooth, the exceptional base change map `Lg'^* Rf^! L ⟶ Rf'^! Lg^* L` with `ℚ̄_ℓ`-coefficients
is an isomorphism for every `L`. On the opens where `f` has constant relative dimension
(`isIso_upperShriekBaseChange_of_forall_smoothOfRelativeDimension`) this is
`isIso_upperShriekBaseChange_of_etaleReductionProperCompatible`. -/
theorem isIso_upperShriekBaseChange_of_smooth_of_etaleReductionProperCompatibleAll
    (hcompat : EtaleReductionProperBaseChangeCompatibleAll ℓ k) (sq : IsPullback g' f' f g)
    [Smooth f.left] (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (upperShriekBaseChange ℓ sq L) :=
  isIso_upperShriekBaseChange_of_forall_smoothOfRelativeDimension ℓ sq L fun _ d _ ↦
    isIso_upperShriekBaseChange_of_etaleReductionProperCompatible ℓ _ d
      (fun E ↦ hcompat E _ _ _ _ g) L

end AlgebraicGeometry.ProEtale.CondensedRing

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionGeneral
public import WeilConjectures.TraceFormula.OrdinaryKunnethReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibilityProper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralUpperShriekCompatibility
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel

/-!
# Vanishing of `Lg'^* Rf^! Rj_!` for smooth `f` and disjoint `g`, `j`

Let `f : X ⟶ Y` be smooth of relative dimension `d`, `g : Y' ⟶ Y` a morphism with base change
`g' : X' ⟶ X` and `j : U ⟶ Y` an open immersion whose image is disjoint from that of `g`. Then
`Lg'^* Rf^! Rj_! M = 0` for every `M`. This is the content of smooth base change for `Rf^!`
along `g` at extensions by zero: `Lg'^* Rf^! Rj_! M ≅ Rf'^! Lg^* Rj_! M = 0`.

The statement only involves objects, not morphisms, so it is transported from finite
coefficients to `𝒪_E` and to `ℚ̄_ℓ` through the (non-canonical) coefficient comparisons:

* `Etale.isZero_leftDerivedUpperStar_obj_rightDerivedUpperShriek_obj_rightDerivedLowerShriek_obj`:
  on the étale site with finite coefficients, from smooth base change
  (`Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension`);
* `ProEtale.CondensedRing.isZero_upperStar_obj_upperShriek_obj_lowerShriek_obj_padicIntegers`:
  for bounded constructible `𝒪_E`-complexes, since the reduction modulo `ℓ` commutes with
  `Lg'^*`, `Rf^!` and `Rj_!` (`etaleReductionUpperStarIso`, `hasEtaleReductionLowerShriekIso`)
  and detects zero objects (`isZero_of_isZero_etaleReduction`);
* `ProEtale.CondensedRing.isZero_upperStar_obj_upperShriek_obj_lowerShriek_obj_padicAlgCl`:
  for bounded constructible `ℚ̄_ℓ`-complexes, through integral models
  (`ProEtale.exists_padicAlgCl_iso_integralModel`) and the coefficient comparisons for
  `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- For `f` smooth of relative dimension `d`, a cartesian square `g' ≫ f = f' ≫ g` and an open
immersion `j` with image disjoint from that of `g`, `Lg'^* Rf^! Rj_! N = 0`: by smooth base change
it is `Rf'^! Lg^* Rj_! N`, and `Lg^* Rj_! = 0`. -/
theorem isZero_leftDerivedUpperStar_obj_rightDerivedUpperShriek_obj_rightDerivedLowerShriek_obj
    {X Y X' Y' U : Scheme.{u}} [QuasiSeparatedSpace Y] [HasInvertibleExponent Λ X]
    (f : X ⟶ Y) [HasCompactification f] (d : ℕ) [SmoothOfRelativeDimension d f]
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    [HasCompactification f'] [QuasiCompact f'] (j : U ⟶ Y) [IsOpenImmersion j]
    [HasCompactification j] [QuasiCompact j] (hgj : Disjoint (Set.range g.base) (Set.range j.base))
    (N : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsZero ((L((g')^*[ModuleCat.{u + 1} Λ])).obj
      ((R(f)^![Λ]).obj ((R(j)_![ModuleCat.{u + 1} Λ]).obj N))) := by
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ f d sq
  have h₀ : IsZero ((L((g)^*[ModuleCat.{u + 1} Λ])).obj ((R(j)_![ModuleCat.{u + 1} Λ]).obj N)) :=
    (isZero_leftDerivedUpperStar_obj_mapDerivedCategory_openImmersionLowerShriek_of_disjoint_range
      (ModuleCat.{u + 1} Λ) j g hgj N).of_iso
      ((L((g)^*[ModuleCat.{u + 1} Λ])).mapIso
        ((rightDerivedLowerShriekIsoOfIsOpenImmersion Λ j).app N))
  have h₁ : IsZero ((R(f')^![Λ]).obj
      ((L((g)^*[ModuleCat.{u + 1} Λ])).obj ((R(j)_![ModuleCat.{u + 1} Λ]).obj N))) := by
    rw [IsZero.iff_id_eq_zero]
    exact ((rightDerivedUpperShriekAdjunction Λ f').homEquiv _ _).symm.injective
      (h₀.eq_of_tgt _ _)
  exact h₁.of_iso
    (asIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app _))

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {X Y X' Y' U : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]

omit [LocallyOfFiniteType Y'.hom] in
/-- For `f` smooth of relative dimension `d`, a cartesian square `g' ≫ f = f' ≫ g` and an open
immersion `j` with image disjoint from that of `g`, `Lg'^* Rf^! Rj_! M = 0` for bounded
constructible `𝒪_E`-complexes `M`: its reduction modulo `ℓ`, read on the étale site, is
`Lg'^* Rf^! Rj_!` of the reduction of `M`, which vanishes by smooth base change with finite
coefficients. -/
theorem isZero_upperStar_obj_upperShriek_obj_lowerShriek_obj_padicIntegers
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (j : U ⟶ Y) [IsOpenImmersion j.left]
    (hgj : Disjoint (Set.range g.left.base) (Set.range j.left.base))
    (M : Dᵇc(U.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g').obj
      ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E f).obj
        ((PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E j).obj M))) := by
  have := HasCompactification.of_over f
  have := HasCompactification.of_over f'
  have := HasCompactification.of_over j
  have := isNoetherian_of_locallyOfFiniteType Y.hom
  have : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E 1) X.left :=
    HasInvertibleExponent.of_hom X.hom
  have hsq : IsPullback g'.left f'.left f.left g.left := by
    simpa only [Over.forget_map] using sq.map (Over.forget _)
  obtain ⟨γf, hγf⟩ := hasEtaleReductionLowerShriekIso ℓ E 1 f
  obtain ⟨γj, -⟩ := hasEtaleReductionLowerShriekIso ℓ E 1 j
  refine isZero_of_isZero_etaleReduction ℓ E one_ne_zero ?_
  have h :=
    Etale.isZero_leftDerivedUpperStar_obj_rightDerivedUpperShriek_obj_rightDerivedLowerShriek_obj
      (integersModPowCoeff.{u} ℓ E 1) f.left d hsq j.left hgj ((etaleReduction ℓ E 1 U).obj M)
  refine h.of_iso ((etaleReductionUpperStarIso ℓ E 1 g').app _ ≪≫ ?_)
  refine (L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E 1)) g'.left)).mapIso
    (asIso (((mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
      (Etale.rightDerivedUpperShriekAdjunction _ f.left)
      (TwoSquare.mk _ _ _ _ γf.inv)).app _)) ≪≫ ?_)
  exact (Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E 1) f.left).mapIso (γj.app M)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' U : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]

omit [LocallyOfFiniteType Y'.hom] in
/-- For `f` smooth of relative dimension `d`, a cartesian square `g' ≫ f = f' ≫ g` and an open
immersion `j` with image disjoint from that of `g`, `Lg'^* Rf^! Rj_! M = 0` for bounded
constructible `ℚ̄_ℓ`-complexes `M`: writing `M ≅ ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} M₀)` for an integral model
`M₀`, the coefficient comparisons identify it with the extension of scalars of the vanishing
`𝒪_E`-complex `Lg'^* Rf^! Rj_! M₀`. -/
theorem isZero_upperStar_obj_upperShriek_obj_lowerShriek_obj_padicAlgCl
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (j : U ⟶ Y) [IsOpenImmersion j.left]
    (hgj : Disjoint (Set.range g.left.base) (Set.range j.left.base))
    (M : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').obj
      ((boundedConstructibleUpperShriek ℓ f).obj
        ((boundedConstructibleLowerShriek ℓ j).obj M))) := by
  have := noetherianSpace_left_of_over U
  obtain ⟨E, M₀, ⟨e⟩⟩ := exists_padicAlgCl_iso_integralModel (X := U.left) ℓ M
  have h₀ := isZero_upperStar_obj_upperShriek_obj_lowerShriek_obj_padicIntegers ℓ E.1 f d sq j
    hgj M₀
  have := isIso_boundedConstructibleUpperShriekExtendScalars ℓ E f
  have := isIso_boundedConstructibleUpperShriekToPadicAlgCl ℓ E f
  -- `E`-coefficients
  have h₁ : IsZero ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E.1) ℓ g').obj
      ((ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E f).obj
        ((ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E j).obj
          ((boundedConstructibleExtendScalars U.left ℓ E).obj M₀)))) := by
    refine ((boundedConstructibleExtendScalars X'.left ℓ E).map_isZero h₀).of_iso ?_
    refine (boundedConstructibleUpperStar _ ℓ g').mapIso
      ((ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E f).mapIso
        ((boundedConstructibleLowerShriekExtendScalarsIso ℓ E j).app M₀).symm) ≪≫ ?_
    refine (boundedConstructibleUpperStar _ ℓ g').mapIso
      (asIso ((boundedConstructibleUpperShriekExtendScalars ℓ E f).app _)).symm ≪≫ ?_
    exact ((boundedConstructibleUpperStarExtendScalarsIso ℓ E g').app _).symm
  refine (((boundedConstructibleToPadicAlgCl X'.left ℓ E).map_isZero h₁).of_iso ?_)
  refine (boundedConstructibleUpperStar _ ℓ g').mapIso
    ((boundedConstructibleUpperShriek ℓ f).mapIso
      ((boundedConstructibleLowerShriek ℓ j).mapIso e.symm)) ≪≫ ?_
  refine (boundedConstructibleUpperStar _ ℓ g').mapIso
    ((boundedConstructibleUpperShriek ℓ f).mapIso
      ((boundedConstructibleLowerShriekToPadicAlgClIso ℓ E j).app _).symm) ≪≫ ?_
  refine (boundedConstructibleUpperStar _ ℓ g').mapIso
    (asIso ((boundedConstructibleUpperShriekToPadicAlgCl ℓ E f).app _)).symm ≪≫ ?_
  exact ((boundedConstructibleUpperStarToPadicAlgClIso ℓ E g').app _).symm

end AlgebraicGeometry.ProEtale.CondensedRing

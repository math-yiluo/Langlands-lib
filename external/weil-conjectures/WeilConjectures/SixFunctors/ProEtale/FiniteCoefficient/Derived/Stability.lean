/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarEtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageCohomologicalDimension
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.CategoryTheory.Sites.NsmulSheaf

/-!

# Stability of `Dctf` under direct image on the pro-étale site

This file is the pro-étale counterpart of the direct-image part of
`WeilConjectures.SixFunctors.Etale.Derived.Stability`: for `Y` of finite type over a field `k`,
coefficients killed by an integer `N` invertible in `k`, and `f : X ⟶ Y` separated of finite
type, the derived direct image `Rf_* : D(X_proét) ⥤ D(Y_proét)` preserves bounded
constructibility, and for a finite coefficient ring `Λ` and `dim X ≤ d` it moves the Tor
amplitude from `[a, b]` to `[a, b + 2d]`.

## Main statements

- `AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedLowerStar`,
  `AlgebraicGeometry.ProEtale.torAmplitudeIn_rightDerivedLowerStar`
  (`proposition-open-direct-image-preserves-finite`).
- `ProEtale.boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar_mapDerivedCategory`
  (`proposition-six-operations-dctf--2`): the case of a complex `ν^* K'` of étale origin.
- `AlgebraicGeometry.ProEtale.boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar`
  (`proposition-six-operations-dctf--2`): the case of every bounded constructible complex.

## Implementation notes

The blueprint deduces this corollary from its étale counterpart
`sk-thm-sf-direct-image-tor-amplitude` by writing a bounded constructible pro-étale complex as
`ν^* K'` for an étale complex `K'` (`theorem-comparison-constructible-sheaves`). Here bounded
constructibility on the pro-étale site
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`) is *defined* as étale
origin, so that lemma is built in. The two comparison inputs are `Rf_* ν^* K' ≅ ν^* Rf_* K'`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarMapDerivedCategoryObjIso`) and the fact that
`ν^*` preserves and detects Tor amplitude
(`AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff`, which needs
the coefficients to be a finite ring `Λ`).

The coefficient category is torsion of order invertible on the base: `N • 𝟙 M = 0` for every
`M : A`, with `(N : k) ≠ 0`. Without this the statements fail, already for
`A = ModuleCat (ZMod p)` and the affine line over a separably closed field of characteristic
`p`, whose `H¹` is infinite by Artin–Schreier theory. Being of finite type over a field is the
base condition of Deligne's finiteness theorem. These are the finite coefficient stages
`A_{E,n}` of the blueprint, where étale-origin bounded constructibility is the right notion.

A dimension bound `dim X ≤ d` is `topologicalKrullDim X ≤ (d : WithBot ℕ∞)`, as in the étale
file.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section Pullback

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived pullback along a morphism `f : X ⟶ Y` of pro-étale sites preserves the Tor
amplitude interval, as soon as `f^*` preserves flat sheaves: `K` is represented by a complex `P`
of flat sheaves in degrees `[a, b]`, so `Lf^* K` is represented by the complex `f^* P` of flat
sheaves in degrees `[a, b]`. This is the pro-étale counterpart of
`AlgebraicGeometry.Etale.torAmplitudeIn_leftDerivedUpperStar`. -/
theorem torAmplitudeIn_leftDerivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(ProEtale.upperStar A f).PreservesFlat] (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hta : DerivedCategory.torAmplitudeIn A Y a b K) :
    DerivedCategory.torAmplitudeIn A X a b ((L(ProEtale.upperStar A f)).obj K) := by
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ := _root_.DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn hta
  refine (DerivedCategory.torAmplitudeIn A X a b).prop_of_iso
    (((ProEtale.upperStar A f).mapDerivedCategoryFactors.app P).symm ≪≫
      (ProEtale.upperStar A f).mapDerivedCategory.mapIso e ≪≫
      ((leftDerivedUpperStarIsoMapDerivedCategory A f).app K).symm)
    (_root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat _ a b fun n ↦ ?_)
  exact Functor.PreservesFlat.flat_obj (F := ProEtale.upperStar A f) (hP n)

end Pullback

section DirectImage

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {k : Type u} [Field k] (N : ℕ) (hN : (N : k) ≠ 0) (hA : ∀ M : ModuleCat.{u + 1} Λ, N • 𝟙 M = 0)
  {X Y : Scheme.{u}} (s : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType s] [QuasiCompact s]
  (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

include hN hA s

/-- Blueprint `proposition-open-direct-image-preserves-finite`: Direct image preserves bounded
constructibility on the pro-étale site.

Let `Y` be of finite type over a field `k`, let `Λ` be a finite ring killed by an integer `N`
invertible in `k`, and let `f : X ⟶ Y` be separated of finite type. If `K` is a bounded
constructible complex on `X_proét`, then `Rf_* K` is bounded constructible on `Y_proét`.

Write `K ≅ ν^* K'` for a bounded constructible étale complex `K'`. Then
`Rf_* K ≅ ν^* Rf_* K'` (`AlgebraicGeometry.ProEtale.rightDerivedLowerStarMapDerivedCategoryObjIso`),
and `Rf_* K'` is bounded constructible
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_finite`). -/
theorem boundedConstructible_rightDerivedLowerStar
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hbc : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := hbc
  -- `N` vanishes in `Λ` and is invertible on the `k`-scheme `Y`
  have hNΛ : (N : Λ) = 0 := by
    simpa using congrArg (fun g ↦ g.hom (1 : Λ)) (hA (ModuleCat.of Λ Λ))
  have hNY : IsUnit (N : Γ(Y, ⊤)) := by
    simpa using (Ne.isUnit hN).map ((Scheme.ΓSpecIso (.of k)).inv ≫ s.appTop).hom
  have : HasInvertibleExponent Λ Y :=
    ⟨N, Nat.pos_of_ne_zero (by rintro rfl; exact hN Nat.cast_zero), hNΛ, hNY⟩
  exact (DerivedCategory.boundedConstructible _ Y).prop_of_iso
    ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).mapIso e.symm ≪≫
      rightDerivedLowerStarMapDerivedCategoryObjIso _ f K' hK'.1.1).symm
    (DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
      (Etale.boundedConstructible_rightDerivedLowerStar_of_finite Λ (f ≫ s) s f rfl hK'))

/-- Blueprint `proposition-six-operations-dctf--2`: The pro-étale direct image for objects of
étale origin.

Let `Y` be of finite type over a field `k`, let `Λ` be a finite ring killed by an integer `N`
invertible in `k`, let `f : X ⟶ Y` be separated of finite type with `dim X ≤ d`, and let `K'`
be a bounded constructible complex of étale sheaves of `Λ`-modules on `X` of Tor amplitude in
`[a, b]`. Then the pro-étale direct image `Rf_* ν^* K'` is bounded constructible on `Y_proét`
with Tor amplitude in `[a, b + 2d]`.

Indeed `Rf_* ν^* K' ≅ ν^* Rf_* K'`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarMapDerivedCategoryObjIso`), where `Rf_* K'` is
bounded constructible with Tor amplitude in `[a, b + 2d]` on the étale site
(`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar`), and `ν^*` preserves both
properties (`AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff`). -/
theorem boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar_mapDerivedCategory
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hbc : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K')
    (hta : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K') :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
        ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj
          (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K')) ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
        ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj
          (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K')) := by
  have : NeZero N := ⟨by rintro rfl; exact hN Nat.cast_zero⟩
  -- `N` is invertible on the `k`-scheme `Y`
  have hNY : IsUnit (N : Γ(Y, ⊤)) := by
    simpa using (Ne.isUnit hN).map ((Scheme.ΓSpecIso (.of k)).inv ≫ s.appTop).hom
  have e := rightDerivedLowerStarMapDerivedCategoryObjIso (ModuleCat.{u + 1} Λ) f K' hbc.1.1
  refine ⟨boundedConstructible_rightDerivedLowerStar Λ N hN hA s f
    (DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj hbc),
    (DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))).prop_of_iso
      e.symm ?_⟩
  exact (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff _ _ _).2
    (Etale.torAmplitudeIn_rightDerivedLowerStar _ (f ≫ s) s f rfl d hd a b N
      (_root_.DerivedCategory.nsmul_id_eq_zero_of_forall
        (Sheaf.nsmul_id_eq_zero_of_forall hA) K') hNY hbc hta)

/-- Blueprint `proposition-six-operations-dctf--2`: The pro-étale direct image for all finite-Tor
objects.

Let `Y` be of finite type over a field `k`, let `Λ` be a finite ring killed by an integer `N`
invertible in `k`, and let `f : X ⟶ Y` be separated of finite type with `dim X ≤ d`. If `K` is a
bounded constructible complex on `X_proét` with Tor amplitude in `[a, b]`, then `Rf_* K` is
bounded constructible on `Y_proét` with Tor amplitude in `[a, b + 2d]`.

The complex `K` is `ν^* K'` for a bounded constructible étale complex `K'`, which has Tor
amplitude in `[a, b]` since `ν^*` detects Tor amplitude
(`AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff`); conclude by
the case of objects of étale origin (`proposition-six-operations-dctf--2`). -/
theorem boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hbc : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hta : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
        ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K) ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
        ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := hbc
  have h := boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar_mapDerivedCategory Λ N
    hN hA s f d hd a b hK' ((DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b K').1
      ((DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b).prop_of_iso e.symm hta))
  have e' := (R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).mapIso e
  exact ⟨(DerivedCategory.boundedConstructible _ Y).prop_of_iso e' h.1,
    (DerivedCategory.torAmplitudeIn _ Y a (b + 2 * (d : ℤ))).prop_of_iso e' h.2⟩

/-- Blueprint `proposition-open-direct-image-preserves-finite`: Tor amplitude of the pro-étale
direct image.

In the situation of `AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedLowerStar`,
for a finite ring `Λ`, if `dim X ≤ d` and `K` has Tor amplitude in `[a, b]`, then `Rf_* K` has
Tor amplitude in `[a, b + 2d]`. The shift `2d` is the uniform vanishing of `Rᵖf_*` above twice
the dimension of the source, for torsion coefficients of order invertible on the base. -/
theorem torAmplitudeIn_rightDerivedLowerStar (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hbc : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hta : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
      ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K) :=
  (boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar Λ N hN hA s f d hd a b hbc
    hta).2

end Finite

section OpenImmersion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {U X : Scheme.{u}} (j : U ⟶ X)
  [IsOpenImmersion j] [QuasiCompact j]

/-- Blueprint `proposition-open-direct-image-preserves-finite`: Scalar projection formula and the
Tor bound for an open immersion.

Let `Λ` be a finite ring and `j : U ⟶ X` a quasi-compact open immersion whose higher direct
images `Rᵠj_* F` of étale sheaves of `Λ`-modules vanish for `q > d`, that is
`d ≥ cd(j)`; for schemes of finite type over a separably closed field this holds for some `d`
(`theorem-results-from-etale-theory--6`,
`AlgebraicGeometry.Etale.hasFiniteCohomologicalDimensionMorphism`). Let `K ∈ D(U_ét, Λ)` have Tor
amplitude in `[a, b]`. Then:

1. for every `Λ`-module `M`, the projection map `Rj_* K ⊗ᴸ M_X ⟶ Rj_*(K ⊗ᴸ Lj^* M_X)` is an
   isomorphism
   (`Etale.isIso_rightDerivedLowerStarProjectionMap_constantSingle_of_cohomologicalDimension`,
   by generation of `D(Λ)` by `Λ` and commutation of
   `Rj_*` with direct sums, `proposition-open-direct-image-preserves-finite`, instead of computing
   sections with `proposition-open-direct-image-preserves-finite`);
2. `Rj_* K` has Tor amplitude in `[a, b + d]` on `X_ét`
   (`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar_of_cohomologicalDimension`, by
   the residue test applied to (1));
3. `Rj_{proét,*} ν_U^* K ≅ ν_X^* Rj_* K` has Tor amplitude in `[a, b + d]` against every
   module sheaf on `X_proét` (`theorem-comparison-direct-images--1` and
   `corollary-finite-tor-amplitude-under-comparison--1`). -/
theorem projection_torAmplitudeIn_rightDerivedLowerStar_of_isOpenImmersion (d : ℕ)
    (hd : ∀ (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      IsZero (((Etale.lowerStar (ModuleCat.{u + 1} Λ) j).rightDerived q).obj F)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hta : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) U a b K) :
    (∀ M : ModuleCat.{u + 1} Λ,
      IsIso (((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) j).app K).app
        (Etale.constantSingle (ModuleCat.{u + 1} Λ) X M))) ∧
    Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a (b + d)
      ((R(Etale.lowerStar (ModuleCat.{u + 1} Λ) j)).obj K) ∧
    Nonempty ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) j)).obj
        (D(ν^*(U)[ModuleCat.{u + 1} Λ]).obj K) ≅
      D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj ((R(Etale.lowerStar (ModuleCat.{u + 1} Λ) j)).obj K)) ∧
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a (b + d)
      ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) j)).obj
        (D(ν^*(U)[ModuleCat.{u + 1} Λ]).obj K)) := by
  have h₂ := Etale.torAmplitudeIn_rightDerivedLowerStar_of_cohomologicalDimension Λ j d hd a b hta
  let e := rightDerivedLowerStarMapDerivedCategoryObjIso (ModuleCat.{u + 1} Λ) j K
    ⟨a, (_root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hta).1⟩
  have h₁ := Etale.isIso_rightDerivedLowerStarProjectionMap_constantSingle_of_cohomologicalDimension
    Λ j d hd K
  exact ⟨h₁, h₂, ⟨e⟩,
    (DerivedCategory.torAmplitudeIn _ X a (b + d)).prop_of_iso e.symm
      ((DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff _ _ _).2 h₂)⟩

end OpenImmersion

end DirectImage

end ProEtale

end AlgebraicGeometry

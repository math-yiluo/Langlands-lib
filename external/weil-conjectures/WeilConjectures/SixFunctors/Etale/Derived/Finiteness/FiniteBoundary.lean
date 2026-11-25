/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper
import WeilConjectures.SixFunctors.Etale.Derived.Supports

/-!
# Proper direct images and a finite boundary

Let `b : Y ⟶ S` be proper, let `a : G ⟶ Y` be an open immersion whose closed complement
`i : Z ⟶ Y` is finite over `S`. A complex on `Y` is then controlled by its restriction to `G`
and its direct image to `S`: the part supported on `Z` is seen faithfully by `Rb_*`, since
`Rb_* i_* = R(bi)_*` and the finite direct image `(bi)_*` is exact and conservative. These are
the two boundary steps of Deligne's generic constructibility theorem
(`theorem-generic-constructibility-base-change-rj`).

## Main statements

- `AlgebraicGeometry.Etale.isZero_of_isZero_lowerStar_obj_of_isFinite`: the direct image along a
  finite morphism detects the zero sheaf.
- `AlgebraicGeometry.Etale.isIso_of_isIso_upperStar_map_of_isIso_rightDerivedLowerStar_map`:
  a morphism which is an isomorphism over `G` and after `Rb_*` is an isomorphism
  (`lemma-detection-proper-direct-image--2`).
- `AlgebraicGeometry.Etale.boundedConstructible_of_upperStar_of_rightDerivedLowerStar`:
  a complex which is bounded constructible over `G` and after `Rb_*` is bounded constructible
  (`lemma-detection-proper-direct-image--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The direct image along a finite morphism detects the zero sheaf**: by the stalk formula,
the stalk of `f_* G` at a geometric point `y` is the product of the stalks of `G` at the
geometric points over `y`, and every geometric point `t` of `X` lies over `t ≫ f`. -/
theorem isZero_of_isZero_lowerStar_obj_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hG : IsZero ((f)_*[ModuleCat.{u + 1} Λ].obj G)) : IsZero G := by
  have : LocallySmall.{u + 1} Y.Etale := locallySmall_max.{u + 1, u}
  have : LocallySmall.{u + 1} X.Etale := locallySmall_max.{u + 1, u}
  have : IsIso (0 : G ⟶ 0) := Scheme.isIso_of_isIso_sheafFiber_map _ fun x ↦ by
    let t := X.algClosurePoint x
    let y := t ≫ f
    have : (((pointSmallEtale y).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).IsLeftAdjoint := inferInstance
    have : ((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)).IsLeftAdjoint :=
      inferInstance
    have h₁ : IsZero ((pointSmallEtale y).sheafFiber.obj ((f)_*[ModuleCat.{u + 1} Λ].obj G)) :=
      ((((pointSmallEtale y).ulift.{u + 1}).sheafFiber (A := ModuleCat.{u + 1} Λ)).map_isZero
        hG).of_iso (((pointSmallEtale y).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} Λ)).app
          _).symm
    have h₂ := h₁.of_iso (Etale.stalkIsoPi (ModuleCat.{u + 1} Λ) f y G).symm
    classical
    have : HasLimitsOfShape (Discrete (f.GeometricFiber y)) (ModuleCat.{u + 1} Λ) :=
      hasLimitsOfShape_discrete _ _
    have : HasLimit (Discrete.functor fun s : f.GeometricFiber y ↦
        (pointSmallEtale s.1).sheafFiber.obj G) := HasLimitsOfShape.has_limit _
    have h₃ : IsZero ((pointSmallEtale t).sheafFiber.obj G) :=
      h₂.of_epi (Pi.π _ (⟨t, rfl⟩ : f.GeometricFiber y))
    have h₄ : IsZero ((X.uliftPointSmallEtale x).sheafFiber.obj G) :=
      h₃.of_iso (((pointSmallEtale t).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} Λ)).app G)
    exact isIso_of_source_target_iso_zero _ h₄.isoZero
      (((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)).map_isZero
        (isZero_zero _)).isoZero
  exact IsZero.of_iso (isZero_zero _) (asIso (0 : G ⟶ 0))

/-- An object of the derived category all of whose homology sheaves vanish is zero. -/
lemma isZero_of_forall_isZero_homology {X : Scheme.{u}}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : ∀ n, IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj K)) : IsZero K := by
  have : K.IsLE (-1) := (_root_.DerivedCategory.isLE_iff K (-1)).2 fun i _ ↦ h i
  have : K.IsGE 0 := (_root_.DerivedCategory.isGE_iff K 0).2 fun i _ ↦ h i
  exact _root_.DerivedCategory.TStructure.t.isZero K (-1) 0 (by lia)

open Pretriangulated in
/-- Blueprint `lemma-detection-proper-direct-image--2`: A proper direct image detects a comparison
off a finite boundary.

Let `b : Y ⟶ S` be a morphism (proper, in the blueprint), let `a : G ⟶ Y` be an open immersion
with closed complement `i : Z ⟶ Y`, and suppose that `i ≫ b` is finite. Let `c : K ⟶ L` be a
morphism of complexes of étale sheaves of `Λ`-modules on `Y` (bounded below, in the blueprint;
neither hypothesis is needed). If the restriction `a^* c` and the direct image `Rb_* c` are
isomorphisms, then so is `c`.

The cone `M` of `c` vanishes on `G`, so the open–closed triangle identifies it with
`Ri_* i^* M`, and `0 = Rb_* M = R(bi)_* i^* M = (bi)_* i^* M`; the finite direct image `(bi)_*`
is exact and detects the zero sheaf, so `i^* M = 0` and `M = 0`. -/
theorem isIso_of_isIso_upperStar_map_of_isIso_rightDerivedLowerStar_map {S Y G Z : Scheme.{u}}
    (b : Y ⟶ S) (a : G ⟶ Y) [IsOpenImmersion a] (i : Z ⟶ Y) [IsClosedImmersion i]
    (hai : Set.range i = (Set.range a)ᶜ) [IsFinite (i ≫ b)]
    {K L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (c : K ⟶ L)
    (ha : IsIso ((Etale.upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategory.map c))
    (hb : IsIso ((R((b)_*[ModuleCat.{u + 1} Λ])).map c)) :
    IsIso c := by
  obtain ⟨M, g, h, hT⟩ := distinguished_cocone_triangle c
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 ?_
  have hMa : IsZero ((Etale.upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategory.obj M) :=
    (Triangle.isZero₃_iff_isIso₁ _ (Functor.map_distinguished _ _ hT)).2 ha
  have hMb : IsZero ((R((b)_*[ModuleCat.{u + 1} Λ])).obj M) :=
    (Triangle.isZero₃_iff_isIso₁ _ (Functor.map_distinguished _ _ hT)).2 hb
  obtain ⟨w, hw⟩ := exists_distTriang_openClosed (ModuleCat.{u + 1} Λ) a i hai M
  have hu : IsIso ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app M) :=
    (Triangle.isZero₁_iff_isIso₂ _ hw).1 (Functor.map_isZero _ hMa)
  let N := (Etale.upperStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategory.obj M
  have hN : IsZero ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (i ≫ b)).mapDerivedCategory.obj N) :=
    (hMb.of_iso ((R((b)_*[ModuleCat.{u + 1} Λ])).mapIso
      (asIso ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app
        M)).symm)).of_iso
      ((rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) i b).app N ≪≫
        (rightDerivedFunctorLowerStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ)
          (i ≫ b)).app N).symm
  have hN' : IsZero N := isZero_of_forall_isZero_homology Λ fun n ↦
    isZero_of_isZero_lowerStar_obj_of_isFinite Λ (i ≫ b)
      ((_root_.DerivedCategory.homologyFunctor _ n).map_isZero hN |>.of_iso
        (((Etale.lowerStar (ModuleCat.{u + 1} Λ) (i ≫ b)).mapDerivedCategoryHomologyFunctorIso
          n).app N))
  exact (Functor.map_isZero _ hN').of_iso (asIso
    ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app M))

/-- Blueprint `lemma-detection-proper-direct-image--1`: Recovering constructibility at a finite
boundary.

Let `b : Y ⟶ S` be a proper morphism between schemes of finite type over a field `k`, and let
`Λ` be a finite ring whose exponent is invertible on `S`. Let `a : G ⟶ Y` be an open immersion
with closed complement `i : Z ⟶ Y`, and assume that `i ≫ b` is finite. If `K` is a bounded below
complex on `Y` such that `a^* K` and `Rb_* K` are bounded constructible, then `K` is bounded
constructible. -/
theorem boundedConstructible_of_upperStar_of_rightDerivedLowerStar [Finite Λ] {k : Type u}
    [Field k] {S Y G Z : Scheme.{u}} (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    [QuasiCompact aS] [HasInvertibleExponent Λ S] (b : Y ⟶ S) [IsProper b] (a : G ⟶ Y)
    [IsOpenImmersion a] (i : Z ⟶ Y) [IsClosedImmersion i] (hai : Set.range i = (Set.range a)ᶜ)
    [IsFinite (i ≫ b)]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hK : ∃ n : ℤ, K.IsGE n)
    (ha : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) G
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategory.obj K))
    (hb : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) S
      ((R((b)_*[ModuleCat.{u + 1} Λ])).obj K)) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K := by
  cases isEmpty_or_nonempty Y with
  | inl hY => exact boundedConstructible_of_isZero Λ (isZero_derivedCategory_of_isEmpty _ Y K)
  | inr hY =>
  have : Nonempty S := ⟨b hY.some⟩
  have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) aS
  have : IsNoetherian S :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian aS
      __ := QuasiCompact.compactSpace_of_compactSpace aS }
  have : IsNoetherian Y :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (b ≫ aS)
      __ := QuasiCompact.compactSpace_of_compactSpace (b ≫ aS) }
  have : IsNoetherian Z :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (i ≫ b ≫ aS)
      __ := QuasiCompact.compactSpace_of_compactSpace (i ≫ b ≫ aS) }
  have : IsFinite i := ((IsClosedImmersion.iff_isFinite_and_mono i).1 inferInstance).1
  let P := DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
  let Q := DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) S
  obtain ⟨w, hw⟩ := exists_distTriang_openClosed (ModuleCat.{u + 1} Λ) a i hai K
  let N := (Etale.upperStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategory.obj K
  -- the first vertex `a_! a^* K` is bounded constructible, and so is its direct image
  have h₁ : P (D((a)_!open[ModuleCat.{u + 1} Λ]).obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategory.obj K)) :=
    boundedConstructible_mapDerivedCategory_openImmersionLowerShriek Λ a ha
  have hb₁ := boundedConstructible_rightDerivedLowerStar_of_isProper aS b h₁
  -- so is the direct image of the third vertex `Ri_* i^* K`
  have hb₃ : Q ((R((b)_*[ModuleCat.{u + 1} Λ])).obj
      ((R((i)_*[ModuleCat.{u + 1} Λ])).obj N)) :=
    Q.ext_of_isTriangulatedClosed₃ _
      ((R((b)_*[ModuleCat.{u + 1} Λ])).map_distinguished _ hw) hb₁ hb
  -- hence `i^* K` is bounded constructible, `i ≫ b` being finite
  have hN : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z N :=
    DerivedCategory.boundedConstructible_of_rightDerivedLowerStar (i ≫ b) N
      (Q.prop_of_iso ((rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) i b).app N) hb₃)
  exact P.ext_of_isTriangulatedClosed₂ _ hw h₁
    (boundedConstructible_rightDerivedLowerStar_of_isFinite Λ i hN)

end Etale

end AlgebraicGeometry

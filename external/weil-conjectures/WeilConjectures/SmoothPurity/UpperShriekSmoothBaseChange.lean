/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRestriction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionClosedLowerStar
public import WeilConjectures.SmoothPurity.UpperShriekOpenVanishing
public import WeilConjectures.TraceFormula.OpenClosedTriangle
public import WeilConjectures.TraceFormula.ClosedPieceTriangle
public import WeilConjectures.TraceFormula.PurityBaseChangeRestriction
public import WeilConjectures.AlgebraicGeometry.SmoothRelativeDimensionCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleOpenCoverIsIso

/-!
# Base change for `Rf^!` along closed and open immersions

For a cartesian square of separated `k`-schemes of finite type
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
this file proves that the exceptional base change map `Lg'^* Rf^! L ⟶ Rf'^! Lg^* L` with
`ℚ̄_ℓ`-coefficients (`ProEtale.CondensedRing.upperShriekBaseChange`) is an isomorphism for every
bounded constructible `L`:

* `ProEtale.CondensedRing.isIso_upperShriekBaseChange_of_isClosedImmersion`: when `f` is smooth
  of relative dimension `d` and `g` is a closed immersion;
* `ProEtale.CondensedRing.isIso_upperShriekBaseChange_of_isOpenImmersion_right`: when `g` is an
  open immersion (for any `f`).

## Proof

Both statements are deduced from the case `L = Rg_* N`, where the exceptional base change map is
invertible because the counits of `Lg^* ⊣ Rg_*` and `Lg'^* ⊣ Rg'_*` are
(`CategoryTheory.Adjunction.isIso_exceptionalBaseChange`), through the naturality of the map
along the unit `η : L ⟶ Rg_* Lg^* L`. The map `Rf'^! Lg^* η` is always invertible, and
`Lg'^* Rf^! η` is invertible as soon as `Lg'^* Rf^!` kills the cone of `η`:

* for an open immersion `g`, the cone is supported on the closed complement, which
  `Lg'^* Rf^!` kills by compact-support base change and adjunction;
* for a closed immersion `g`, the cone is `Rj_! Lj^* L[1]` for the open complement `j`, and
  `Lg'^* Rf^! Rj_! = 0` is the vanishing
  `ProEtale.CondensedRing.isZero_upperStar_obj_upperShriek_obj_lowerShriek_obj_padicAlgCl`. It
  only involves objects, so it is transported from smooth base change with finite étale
  coefficients through the (non-canonical) coefficient comparisons, and no compatibility of the
  coefficient comparisons with compact-support base change is needed.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {𝒳 𝒴 𝒳' 𝒴' : Type*} [Category* 𝒳] [Category* 𝒴] [Category* 𝒳'] [Category* 𝒴']
  {L : 𝒳 ⥤ 𝒴} {R : 𝒴 ⥤ 𝒳} {L' : 𝒳' ⥤ 𝒴'} {R' : 𝒴' ⥤ 𝒳'} {v : 𝒴 ⥤ 𝒴'} {u : 𝒳 ⥤ 𝒳'}
  (a : L ⊣ R) (a' : L' ⊣ R') (bc : L ⋙ v ⟶ u ⋙ L') [IsIso bc]

/-- The exceptional base change is the component of the mate of the inverse of the base
change. -/
lemma exceptionalBaseChange_eq_mateEquiv_app (N : 𝒴) :
    exceptionalBaseChange a a' bc N =
      (mateEquiv a a' (TwoSquare.mk _ _ _ _ (asIso bc).inv)).app N := by
  rw [Adjunction.mateEquiv_app_eq_homEquiv a a' u v (asIso bc) N, exceptionalBaseChange]
  simp [NatIso.isIso_inv_app]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The exceptional base change map as a natural transformation `Rf^! ⋙ Lg'^* ⟶ Lg^* ⋙ Rf'^!`:
the mate of the inverse of compact-support base change. -/
noncomputable def upperShriekBaseChangeNatTrans (sq : IsPullback g' f' f g) :
    boundedConstructibleUpperShriek ℓ f ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g' ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g ⋙
        boundedConstructibleUpperShriek ℓ f' :=
  haveI := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  (mateEquiv (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleUpperShriekAdjunction ℓ f')
    (TwoSquare.mk _ _ _ _
      (asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)).inv))

/-- The exceptional base change map is the component of `upperShriekBaseChangeNatTrans`. -/
lemma upperShriekBaseChange_eq_upperShriekBaseChangeNatTrans_app (sq : IsPullback g' f' f g)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    upperShriekBaseChange ℓ sq L = (upperShriekBaseChangeNatTrans ℓ sq).app L := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  rw [upperShriekBaseChange_eq_exceptionalBaseChange,
    Adjunction.exceptionalBaseChange_eq_mateEquiv_app]
  rfl

/-- The exceptional base change map is an isomorphism at `Rg_* N` as soon as the counits of
`Lg^* ⊣ Rg_*` and `Lg'^* ⊣ Rg'_*` are isomorphisms, for instance when `g` is a closed or an open
immersion. -/
theorem isIso_upperShriekBaseChange_lowerStar_obj (sq : IsPullback g' f' f g)
    [IsIso (boundedConstructibleUpperStarLowerStarAdjunction ℓ g).counit]
    [IsIso (boundedConstructibleUpperStarLowerStarAdjunction ℓ g').counit]
    (N : Dᵇc(Y'.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (upperShriekBaseChange ℓ sq ((boundedConstructibleLowerStar ℓ g).obj N)) := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  rw [upperShriekBaseChange_eq_exceptionalBaseChange]
  exact Adjunction.isIso_exceptionalBaseChange _ _
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ g)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ g') _ N

/-- **Smooth base change for `Rf^!` along a closed immersion**: for a cartesian square
`g' ≫ f = f' ≫ g` with `f` smooth of relative dimension `d` and `g` a closed immersion, the
exceptional base change map `Lg'^* Rf^! L ⟶ Rf'^! Lg^* L` is an isomorphism for every bounded
constructible `ℚ̄_ℓ`-complex `L`. With `j` the open complement of `g`, the open–closed triangle
`Rj_! Lj^* L ⟶ L ⟶ Rg_* Lg^* L` reduces this to `L = Rg_* N`, using
`Lg'^* Rf^! Rj_! = 0` (`isZero_upperStar_obj_upperShriek_obj_lowerShriek_obj_padicAlgCl`). -/
theorem isIso_upperShriekBaseChange_of_isClosedImmersion (sq : IsPullback g' f' f g) (d : ℕ)
    [SmoothOfRelativeDimension d f.left] [IsClosedImmersion g.left]
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (upperShriekBaseChange ℓ sq L) := by
  have hsq : IsPullback g'.left f'.left f.left g.left := by
    simpa only [Over.forget_map] using sq.map (Over.forget _)
  have : IsClosedImmersion g'.left := MorphismProperty.of_isPullback hsq.flip inferInstance
  let j := overOpenComplement g
  have hcompl : IsCompl (Set.range j.left.base) (Set.range g.left.base) :=
    (isCompl_range_overOpenComplement g).symm
  obtain ⟨δ, hT⟩ := exists_distTriang_openClosed_boundedConstructible ℓ hcompl L
  let F := boundedConstructibleUpperShriek ℓ f ⋙
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g'
  have hF := F.map_distinguished _ hT
  have h₁ : IsZero ((F.mapTriangle.obj (Triangle.mk
      ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app L)
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app L) δ)).obj₁) :=
    isZero_upperStar_obj_upperShriek_obj_lowerShriek_obj_padicAlgCl ℓ f d sq j
      hcompl.symm.disjoint _
  have hFη : IsIso (F.map ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app L)) :=
    (Triangle.isZero₁_iff_isIso₂ _ hF).1 h₁
  have hGη : IsIso ((boundedConstructibleUpperShriek ℓ f').map
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app L))) := by
    have : IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app L)) :=
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ g).isIso_map_unit_app_of_isIso_counit L
    infer_instance
  have hN := isIso_upperShriekBaseChange_lowerStar_obj ℓ sq
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj L)
  rw [upperShriekBaseChange_eq_upperShriekBaseChangeNatTrans_app] at hN ⊢
  have hn := (upperShriekBaseChangeNatTrans ℓ sq).naturality
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app L)
  have : IsIso ((upperShriekBaseChangeNatTrans ℓ sq).app L ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g ⋙
        boundedConstructibleUpperShriek ℓ f').map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app L)) := by
    erw [← hn]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hFη hN
  have : IsIso ((boundedConstructibleUpperStar _ ℓ g ⋙
      boundedConstructibleUpperShriek ℓ f').map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app L)) := hGη
  exact IsIso.of_isIso_comp_right _ ((boundedConstructibleUpperStar _ ℓ g ⋙
    boundedConstructibleUpperShriek ℓ f').map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app L))

/-! ### Base change along an open immersion -/

omit [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom] in
/-- For an open immersion `v'` and a closed immersion `i` whose images under `f` and in `Y` are
disjoint, `Lv'^* Rf^! Ri_* K = 0`: by adjunction a morphism into it is a morphism
`Li^* Rf_! v'_! M ⟶ K`, and `Li^* Rf_! v'_! M ≅ Rf_Z! Li'^* v'_! M = 0` by compact-support base
change. -/
lemma isZero_upperStar_obj_upperShriek_obj_lowerStar_obj {X₀ Z : Over (Spec (.of k))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (f : X ⟶ Y) {v : Y' ⟶ Y} (v' : X₀ ⟶ X) {f₀ : X₀ ⟶ Y'} (w : v' ≫ f = f₀ ≫ v)
    [IsOpenImmersion v'.left] (i : Z ⟶ Y)
    (hvi : Disjoint (Set.range v.left.base) (Set.range i.left.base))
    (K : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ v').obj
      ((boundedConstructibleUpperShriek ℓ f).obj ((boundedConstructibleLowerStar ℓ i).obj K))) := by
  have sqZ := IsPullback.of_hasPullback f i
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqZ
  have hdisj : Disjoint (Set.range v'.left.base) (Set.range (pullback.fst f i).left.base) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    have h₁ := congrArg f.left.base hb
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left,
      pullback.condition, w, Over.comp_left, Over.comp_left, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply] at h₁
    exact Set.disjoint_left.1 hvi ⟨_, h₁.symm⟩ ⟨_, rfl⟩
  set adjv := boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
    (Profinite.padicAlgClRingObj ℓ) ℓ v'
  set adjf := boundedConstructibleUpperShriekAdjunction ℓ f
  set adji := boundedConstructibleUpperStarLowerStarAdjunction ℓ i
  rw [IsZero.iff_id_eq_zero]
  refine (adjv.homEquiv _ _).symm.injective ((adjf.homEquiv _ _).symm.injective
    ((adji.homEquiv _ _).symm.injective ?_))
  have h₀ := isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek
    (Profinite.padicAlgClRingObj ℓ) ℓ v' (pullback.fst f i) hdisj
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ v').obj
      ((boundedConstructibleUpperShriek ℓ f).obj ((boundedConstructibleLowerStar ℓ i).obj K)))
  have h₁ : IsZero ((boundedConstructibleLowerShriek ℓ (pullback.snd f i)).obj
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (pullback.fst f i)).obj
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ v').obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ v').obj
            ((boundedConstructibleUpperShriek ℓ f).obj
              ((boundedConstructibleLowerStar ℓ i).obj K)))))) := by
    rw [IsZero.iff_id_eq_zero] at h₀ ⊢
    rw [← (boundedConstructibleLowerShriek ℓ (pullback.snd f i)).map_id, h₀, Functor.map_zero]
  exact (h₁.of_iso (asIso ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqZ).app
    _))).eq_of_src _ _

/-- **Base change of `Rf^!` along an open immersion**: for a cartesian square
`v' ≫ f = f' ≫ v` with `v` an open immersion, the exceptional base change map
`Lv'^* Rf^! L ⟶ Rf'^! Lv^* L` is an isomorphism for every `L`. With `η : L ⟶ Rv_* Lv^* L` the
unit, the map is an isomorphism at `Rv_* Lv^* L` (the counit of `Lv^* ⊣ Rv_*` being invertible),
`Rf'^! Lv^* η` is invertible, and so is `Lv'^* Rf^! η`: the cone `C` of `η` satisfies
`Lv^* C = 0`, hence `C ≅ Ri_* Li^* C` for the closed complement `i`, and
`Lv'^* Rf^! Ri_* = 0` (`isZero_upperStar_obj_upperShriek_obj_lowerStar_obj`). -/
theorem isIso_upperShriekBaseChange_of_isOpenImmersion_right (sq : IsPullback g' f' f g)
    [IsOpenImmersion g.left] (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (upperShriekBaseChange ℓ sq L) := by
  have hsq : IsPullback g'.left f'.left f.left g.left := by
    simpa only [Over.forget_map] using sq.map (Over.forget _)
  have : IsOpenImmersion g'.left := MorphismProperty.of_isPullback hsq.flip inferInstance
  have hcounit (A B : Over (Spec (.of k))) [LocallyOfFiniteType A.hom] [QuasiCompact A.hom]
      [IsSeparated A.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
      (o : A ⟶ B) [IsOpenImmersion o.left] :
      IsIso (boundedConstructibleUpperStarLowerStarAdjunction ℓ o).counit :=
    (Adjunction.Triple.mk (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ o)
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ o)).isIso_unit_iff_isIso_counit.1
        inferInstance
  have := hcounit _ _ g
  have := hcounit _ _ g'
  let i := overClosedComplement g
  let η := (boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app L
  let F := boundedConstructibleUpperShriek ℓ f ⋙
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g'
  let V := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g
  have hVη : IsIso (V.map η) :=
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ g).isIso_map_unit_app_of_isIso_counit L
  obtain ⟨C, b, c, hT⟩ := distinguished_cocone_triangle η
  -- `Lv^* C = 0`
  have hVC : IsZero (V.obj C) :=
    (Triangle.isZero₃_iff_isIso₁ _ (V.map_distinguished _ hT)).2 hVη
  -- `C ≅ Ri_* Li^* C`
  obtain ⟨δ, hT'⟩ := exists_distTriang_openImmersionLowerShriek_lowerStar g i
    (isCompl_range_overClosedComplement g).symm C
  have hj : IsZero ((boundedConstructibleOpenImmersionLowerShriek
      (Profinite.padicAlgClRingObj ℓ) ℓ g).obj (V.obj C)) := by
    rw [IsZero.iff_id_eq_zero] at hVC ⊢
    rw [← (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ g).map_id,
      hVC, Functor.map_zero]
  have hiC := (Triangle.isZero₁_iff_isIso₂ _ hT').1 hj
  have hFC : IsZero (F.obj C) :=
    (isZero_upperStar_obj_upperShriek_obj_lowerStar_obj ℓ f g' sq.w i
      (isCompl_range_overClosedComplement g).symm.disjoint _).of_iso
      (F.mapIso (@asIso _ _ _ _ _ hiC))
  have hFη : IsIso (F.map η) :=
    (Triangle.isZero₃_iff_isIso₁ _ (F.map_distinguished _ hT)).1 hFC
  have hN := isIso_upperShriekBaseChange_lowerStar_obj ℓ sq (V.obj L)
  rw [upperShriekBaseChange_eq_upperShriekBaseChangeNatTrans_app] at hN ⊢
  have hn := (upperShriekBaseChangeNatTrans ℓ sq).naturality η
  have : IsIso ((upperShriekBaseChangeNatTrans ℓ sq).app L ≫
      (V ⋙ boundedConstructibleUpperShriek ℓ f').map η) := by
    erw [← hn]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hFη hN
  have : IsIso ((V ⋙ boundedConstructibleUpperShriek ℓ f').map η) :=
    inferInstanceAs (IsIso ((boundedConstructibleUpperShriek ℓ f').map (V.map η)))
  exact IsIso.of_isIso_comp_right _ ((V ⋙ boundedConstructibleUpperShriek ℓ f').map η)

/-! ### Smooth morphisms of locally constant relative dimension -/

/-- **Reduction to constant relative dimension**: for `f` smooth, the exceptional base change map
of a cartesian square at `L` is an isomorphism as soon as it is one for the squares of the
restrictions `U ⟶ X ⟶ Y` of `f` to the opens `U` on which `f` has constant relative dimension.
The restrictions to a finite cover of `X'` by such opens jointly reflect isomorphisms
(`isIso_of_isIso_upperStar_of_isOpenImmersion`), and the restriction of the exceptional base
change map is that of the restricted square (`isIso_upperStar_map_upperShriekBaseChange_iff`). -/
theorem isIso_upperShriekBaseChange_of_forall_smoothOfRelativeDimension
    (sq : IsPullback g' f' f g) [Smooth f.left] (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (h : ∀ (U : X.left.Opens) (d : ℕ), SmoothOfRelativeDimension d (overRestrictι X U ≫ f).left →
      IsIso (upperShriekBaseChange ℓ (IsPullback.of_hasPullback (overRestrictι X U ≫ f) g) L)) :
    IsIso (upperShriekBaseChange ℓ sq L) := by
  obtain ⟨ι, _, U, hU, hd⟩ := exists_finite_openCover_smoothOfRelativeDimension f
  -- the restriction `o' i : (U i) ×_Y Y' ⟶ X'` of the square to the open `U i`
  let o' (i : ι) : pullback (overRestrictι X (U i) ≫ f) g ⟶ X' :=
    sq.lift (pullback.fst (overRestrictι X (U i) ≫ f) g ≫ overRestrictι X (U i))
      (pullback.snd (overRestrictι X (U i) ≫ f) g) (by rw [Category.assoc, pullback.condition])
  have sqo (i : ι) : IsPullback (pullback.fst (overRestrictι X (U i) ≫ f) g).left (o' i).left
      (overRestrictι X (U i)).left g'.left := by
    have t := IsPullback.of_hasPullback (overRestrictι X (U i) ≫ f) g
    rw [← sq.lift_snd (pullback.fst (overRestrictι X (U i) ≫ f) g ≫ overRestrictι X (U i))
      (pullback.snd (overRestrictι X (U i) ≫ f) g)
      (by rw [Category.assoc, pullback.condition])] at t
    have h := IsPullback.of_bot t (sq.lift_fst _ _ _).symm sq
    simpa only [Over.forget_map] using h.map (Over.forget _)
  have : ∀ i, IsOpenImmersion (o' i).left := fun i ↦
    MorphismProperty.of_isPullback (sqo i) inferInstance
  refine isIso_of_isIso_upperStar_of_isOpenImmersion ℓ o' ?_ _ fun i ↦ ?_
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨i, hi⟩ : ∃ i, g'.left.base x ∈ U i := by
      have : g'.left.base x ∈ (⨆ i, U i : X.left.Opens) := by rw [hU]; trivial
      simpa using this
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    have hr : Set.range (o' i).left.base =
        g'.left.base ⁻¹' Set.range (overRestrictι X (U i)).left.base := by
      rw [← (sqo i).isoPullback_hom_snd, Scheme.Hom.comp_base, TopCat.coe_comp,
        Function.Surjective.range_comp (f := ⇑(sqo i).isoPullback.hom.base)
          (sqo i).isoPullback.hom.homeomorph.surjective, Scheme.Pullback.range_snd]
    rw [hr, range_overRestrictι]
    exact hi
  · obtain ⟨d, hd⟩ := hd i
    exact (isIso_upperStar_map_upperShriekBaseChange_iff ℓ sq (overRestrictι X (U i)) L).2
      (h (U i) d hd)

/-- **Smooth base change for `Rf^!` along a closed immersion**, for `f` smooth (of locally constant
relative dimension): the exceptional base change map `Lg'^* Rf^! L ⟶ Rf'^! Lg^* L` is an
isomorphism for every bounded constructible `L` when `g` is a closed immersion. This is the
`sorry`-free special case of `isIso_upperShriekBaseChange_of_smooth`, which rests on the `sorry`d
`smoothOrientation_baseChange`. -/
theorem isIso_upperShriekBaseChange_of_smooth_of_isClosedImmersion (sq : IsPullback g' f' f g)
    [Smooth f.left] [IsClosedImmersion g.left] (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (upperShriekBaseChange ℓ sq L) :=
  isIso_upperShriekBaseChange_of_forall_smoothOfRelativeDimension ℓ sq L fun _ d _ ↦
    isIso_upperShriekBaseChange_of_isClosedImmersion ℓ _ d L

end AlgebraicGeometry.ProEtale.CondensedRing

/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.ShriekBaseChangeMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeProper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompositionTriangle
import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate

/-!

# The compact-support base change as a mate of the composition isomorphisms

Let `sq : IsPullback g' f' f g` be a cartesian square of separated `k`-schemes of finite type
with `g` and `g'` proper. This file shows that the compact-support base change
`Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` on bounded constructible `ℚ̄_ℓ`-sheaves is the mate, for the
adjunctions `Lg'^* ⊣ Rg'_!` and `Lg^* ⊣ Rg_!` (the adjunctions `Lg^* ⊣ Rg_*` transported along
`Rg_! ≅ Rg_*`), of the composition isomorphism
`Rg'_! ⋙ Rf_! ≅ R(g' ≫ f)_! = R(f' ≫ g)_! ≅ Rf'_! ⋙ Rg_!`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv'`,
blueprint `proposition-composition-base-change-rf-shriek`, clause (4)).

The proof computes everything through a compactification `X ⟶[i] Z ⟶[p] Y` of `f` and a
compactification `X' ⟶[i'] Z' ⟶[p'] Y'` of `f'` lying over it along `h : Z' ⟶ Z`: the two
composition isomorphisms are those of the triangles of compactifications
`(X' ⟶[𝟙] X' ⟶[g'] X, X ⟶[i] Z ⟶[p] Y)` and `(X' ⟶[i'] Z' ⟶[p'] Y', Y' ⟶[𝟙] Y' ⟶[g] Y)`
(`boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle`), whose composite is the mate of
the compact-support exchange map of `(c, c')` by the formal computation
`CategoryTheory.ExchangeFormalism.mateEquiv_shriekBaseChange_eq_compIso`.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The formalism `boundedConstructibleExchangeFormalism`, for `ℚ̄_ℓ`-sheaves. -/
local notation "𝔽" => boundedConstructibleExchangeFormalism ℓ k

section Copy

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The comparisons of compactifications are compatible with transporting a compactification
along an equality `φ = ψ` of morphisms (`AlgebraicGeometry.Compactification.copy`). -/
lemma boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_copy {φ ψ : X ⟶ Y}
    (e : φ = ψ) (d : Compactification ψ.left) :
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
        (d.copy (congrArg CommaMorphism.left e)) (compactificationOverField φ)).hom ≫
      eqToHom (congrArg (boundedConstructibleLowerShriek ℓ) e) ≫
      (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
        (compactificationOverField ψ) d).hom = 𝟙 _ := by
  subst e
  rw [eqToHom_refl, Category.id_comp, ← Iso.trans_hom,
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans]
  exact congrArg Iso.hom (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_refl ℓ d)

end Copy

section Triangle

variable {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]

/-- **The inverse of the composition isomorphism of the lower shriek is computed by any triangle
of compactifications** `T` of `f` and `g`: it is the comparisons of the chosen compactifications
with `T.cf` and `T.cg`, followed by the composition isomorphism of `T` and the comparison of
`T.cfg` with the chosen compactification of `f ≫ g`. -/
theorem boundedConstructibleLowerShriekComp_padicAlgCl_inv_eq_triangle (f : X ⟶ Y) (g : Y ⟶ S)
    (T : AlgebraicGeometry.Compactification.Triangle f.left g.left) :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ T
    haveI := isIso_exchange_triangleShriekTriangle ℓ T
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).inv =
      NatTrans.hcomp (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (compactificationOverField f) T.cf).hom
          (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
            (compactificationOverField g) T.cg).hom ≫
        ((𝔽).compIso (triangleShriekTriangle T)).hom ≫
        (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (Compactification.Triangle.overCfg T) (compactificationOverField (f ≫ g))).hom := by
  have e : NatTrans.hcomp (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          T.cf (compactificationOverField f)).hom
        (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          T.cg (compactificationOverField g)).hom ≫
      NatTrans.hcomp (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (compactificationOverField f) T.cf).hom
        (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (compactificationOverField g) T.cg).hom = 𝟙 _ := by
    rw [← NatTrans.exchange, ← Iso.trans_hom, ← Iso.trans_hom,
      boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans,
      boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans,
      boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_refl,
      boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_refl]
    ext
    simp
  rw [← cancel_epi (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom, Iso.hom_inv_id,
    boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle ℓ f g T]
  simp only [Category.assoc]
  rw [reassoc_of% e, Iso.inv_hom_id_assoc, ← Iso.trans_hom,
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans,
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_refl, Iso.refl_hom]
  rfl

end Triangle

section BaseChange

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  (c : Compactification f.left) (c' : Compactification f'.left)
  (h : c'.overObj ⟶ c.overObj) (hi : IsPullback g' c'.overI c.overI h)
  (hp : IsPullback h c'.overG c.overG g)

/-- The triangle of compactifications `X' ⟶[𝟙] X' ⟶[g'] X`, `X ⟶[i] Z ⟶[p] Y`,
`X' ⟶[i'] Z' ⟶[p' ≫ g] Y` of `g'` and `f`, for a compactification `c = (i, p)` of `f` and a
compactification `c' = (i', p')` of `f'` lying over it along `h : Z' ⟶ Z`. -/
noncomputable abbrev baseChangeTriangleLeft (c : Compactification f.left)
    (c' : Compactification f'.left)
    (h : c'.overObj ⟶ c.overObj) (hi : IsPullback g' c'.overI c.overI h)
    (hp : IsPullback h c'.overG c.overG g) [IsProper g.left] [IsProper g'.left]
    (w : g' ≫ f = f' ≫ g) :
    AlgebraicGeometry.Compactification.Triangle g'.left f.left where
  cf := .ofIsProper g'.left
  cg := c
  cfg := (c'.postcomp g.left).copy (congrArg CommaMorphism.left w)
  q := c'.i
  p := h.left
  i_q := Category.id_comp _
  p_g := congrArg CommaMorphism.left hp.w
  isPullback := hi.overLeft

/-- The triangle of compactifications `X' ⟶[i'] Z' ⟶[p'] Y'`, `Y' ⟶[𝟙] Y' ⟶[g] Y`,
`X' ⟶[i'] Z' ⟶[p' ≫ g] Y` of `f'` and `g`, for a compactification `c' = (i', p')` of `f'`. -/
noncomputable abbrev baseChangeTriangleRight (c' : Compactification f'.left) [IsProper g.left] :
    AlgebraicGeometry.Compactification.Triangle f'.left g.left where
  cf := c'
  cg := .ofIsProper g.left
  cfg := c'.postcomp g.left
  q := 𝟙 c'.Z
  p := c'.g
  i_q := Category.comp_id _
  p_g := rfl
  isPullback := IsPullback.of_id_snd

omit [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom] in
/-- The exchange map of the exchange formalism of a cartesian square whose bottom side is proper
is an isomorphism (interchange of proper direct image and extension by zero). -/
lemma isIso_exchange_boundedConstructibleExchangeFormalism {Z Z' : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom] {i : X ⟶ Z}
    {i' : X' ⟶ Z'} {t : Z' ⟶ Z} [IsOpenImmersion i.left] [IsOpenImmersion i'.left]
    [IsProper t.left] (sq : IsPullback g' i' i t) :
    haveI := isIso_baseChange_boundedConstructibleExchangeFormalism ℓ sq
    IsIso ((𝔽).exchange (SepFinType.homMk g') (SepFinType.homMk i') (SepFinType.homMk i)
      (SepFinType.homMk t) (SepFinType.homMk_comp_homMk sq.w)) := by
  have h := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ sq
  rw [boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_eq_exchange] at h
  exact h

/-- The triangle of factorizations of the triangle of compactifications `baseChangeTriangleLeft`
is the triangle `shriekBaseChangeTriangleLeft` of the exchange formalism. -/
lemma compIso_triangleShriekTriangle_baseChangeTriangleLeft [IsProper g.left] [IsProper g'.left]
    (w : g' ≫ f = f' ≫ g) :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (baseChangeTriangleLeft c c' h hi hp w)
    haveI := isIso_exchange_triangleShriekTriangle ℓ (baseChangeTriangleLeft c c' h hi hp w)
    haveI := isIso_baseChange_boundedConstructibleExchangeFormalism ℓ hi
    haveI : IsProper h.left := MorphismProperty.of_isPullback (P := @IsProper) hp.overLeft.flip
      (inferInstanceAs (IsProper g.left))
    haveI := isIso_exchange_boundedConstructibleExchangeFormalism ℓ hi
    ((𝔽).compIso (triangleShriekTriangle (baseChangeTriangleLeft c c' h hi hp w))).hom =
      ((𝔽).compIso (ExchangeFormalism.shriekBaseChangeTriangleLeft (SepFinType.homMk c.overI)
        (SepFinType.homMk c.overG) (SepFinType.homMk c'.overI) (SepFinType.homMk c'.overG)
        (SepFinType.homMk g') (SepFinType.homMk h) (SepFinType.homMk g)
        (SepFinType.homMk_comp_homMk hi.w) (SepFinType.homMk_comp_homMk hp.w))).hom := by
  obtain ⟨X'l, ⟨⟨⟩⟩, X'h⟩ := X'
  obtain ⟨Y'l, ⟨⟨⟩⟩, Y'h⟩ := Y'
  obtain ⟨g'l, ⟨⟨⟨⟩⟩⟩, g'w⟩ := g'
  obtain ⟨gl, ⟨⟨⟨⟩⟩⟩, gw⟩ := g
  dsimp only at g'l gl
  obtain rfl : X'h = g'l ≫ X.hom := by simpa using g'w.symm
  obtain rfl : Y'h = gl ≫ Y.hom := by simpa using gw.symm
  rfl

/-- The triangle of factorizations of the triangle of compactifications `baseChangeTriangleRight`
is the triangle `shriekBaseChangeTriangleRight` of the exchange formalism. -/
lemma compIso_triangleShriekTriangle_baseChangeTriangleRight [IsProper g.left] :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (baseChangeTriangleRight c' (g := g))
    haveI := isIso_exchange_triangleShriekTriangle ℓ (baseChangeTriangleRight c' (g := g))
    haveI := (𝔽).isIso_baseChange_id_vert (SepFinType.homMk c'.overG)
      (ExchangeFormalism.shriekBaseChangeTriangleRight (𝒪 := SepFinType.openImmersion)
        (SepFinType.homMk c'.overI) (SepFinType.homMk c'.overG) (SepFinType.homMk g)).w
    haveI := (𝔽).isIso_exchange_id_vert (SepFinType.homMk c'.overG)
      (ExchangeFormalism.shriekBaseChangeTriangleRight (𝒪 := SepFinType.openImmersion)
        (SepFinType.homMk c'.overI) (SepFinType.homMk c'.overG) (SepFinType.homMk g)).w
    ((𝔽).compIso (triangleShriekTriangle (baseChangeTriangleRight c' (g := g)))).inv =
      ((𝔽).compIso (ExchangeFormalism.shriekBaseChangeTriangleRight
        (SepFinType.homMk c'.overI) (SepFinType.homMk c'.overG) (SepFinType.homMk g))).inv := by
  obtain ⟨Y'l, ⟨⟨⟩⟩, Y'h⟩ := Y'
  obtain ⟨gl, ⟨⟨⟨⟩⟩⟩, gw⟩ := g
  dsimp only at gl
  obtain rfl : Y'h = gl ≫ Y.hom := by simpa using gw.symm
  rfl

omit [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom] in
/-- The identification `Rg'_!^{𝟙} ≅ Rg'_*` of the trivial compactification of a proper `g'` is
`(𝟙)_! ≅ 𝟭` of the exchange formalism. -/
lemma boundedConstructibleLowerShriekOfCompactificationOfIsProperIso_inv_eq [IsProper g'.left] :
    (boundedConstructibleLowerShriekOfCompactificationOfIsProperIso ℓ g').inv =
      (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight ((𝔽).shId (SepFinType.mk X')).inv ((𝔽).pf (SepFinType.homMk g')) := by
  rw [boundedConstructibleLowerShriekOfCompactificationOfIsProperIso,
    boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_eq_shId]
  obtain ⟨X'l, ⟨⟨⟩⟩, X'h⟩ := X'
  obtain ⟨g'l, ⟨⟨⟨⟩⟩⟩, g'w⟩ := g'
  dsimp only at g'l
  obtain rfl : X'h = g'l ≫ X.hom := by simpa using g'w.symm
  rfl

omit [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] in
/-- The identification `Rg_!^{𝟙} ≅ Rg_*` of the trivial compactification of a proper `g` is
`(𝟙)_! ≅ 𝟭` of the exchange formalism. -/
lemma boundedConstructibleLowerShriekOfCompactificationOfIsProperIso_hom_eq [IsProper g.left] :
    (boundedConstructibleLowerShriekOfCompactificationOfIsProperIso ℓ g).hom =
      Functor.whiskerRight ((𝔽).shId (SepFinType.mk Y')).hom ((𝔽).pf (SepFinType.homMk g)) ≫
        (Functor.leftUnitor _).hom := by
  rw [boundedConstructibleLowerShriekOfCompactificationOfIsProperIso,
    boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_eq_shId]
  obtain ⟨Y'l, ⟨⟨⟩⟩, Y'h⟩ := Y'
  obtain ⟨gl, ⟨⟨⟨⟩⟩⟩, gw⟩ := g
  dsimp only at gl
  obtain rfl : Y'h = gl ≫ Y.hom := by simpa using gw.symm
  rfl

/-- **The mate of the compact-support exchange map of a pair of compactifications** `(c, c')`
under `Lg'^* ⊣ Rg'_*` and `Lg^* ⊣ Rg_*` is, through `Rg'_*^{𝟙} ≅ Rg'_*` and `Rg_*^{𝟙} ≅ Rg_*`,
the composite of the composition isomorphisms of the triangles `baseChangeTriangleLeft` and
`baseChangeTriangleRight`. -/
theorem mateEquiv_boundedConstructibleLowerShriekOfCompactificationBaseChange
    [IsProper g.left] [IsProper g'.left] (w : g' ≫ f = f' ≫ g) :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (baseChangeTriangleLeft c c' h hi hp w)
    haveI := isIso_exchange_triangleShriekTriangle ℓ (baseChangeTriangleLeft c c' h hi hp w)
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (baseChangeTriangleRight c' (g := g))
    haveI := isIso_exchange_triangleShriekTriangle ℓ (baseChangeTriangleRight c' (g := g))
    (mateEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ g')
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ g)
        (boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ c c' h hi hp)) =
      Functor.whiskerRight (boundedConstructibleLowerShriekOfCompactificationOfIsProperIso ℓ g').inv
          (boundedConstructibleLowerShriekOfCompactification ℓ c) ≫
        ((𝔽).compIso (triangleShriekTriangle (baseChangeTriangleLeft c c' h hi hp w))).hom ≫
        ((𝔽).compIso (triangleShriekTriangle (baseChangeTriangleRight c' (g := g)))).inv ≫
        Functor.whiskerLeft (boundedConstructibleLowerShriekOfCompactification ℓ c')
          (boundedConstructibleLowerShriekOfCompactificationOfIsProperIso ℓ g).hom := by
  have : IsProper h.left := MorphismProperty.of_isPullback (P := @IsProper) hp.overLeft.flip
    (inferInstanceAs (IsProper g.left))
  have := isIso_baseChange_boundedConstructibleExchangeFormalism ℓ hi
  have := isIso_exchange_boundedConstructibleExchangeFormalism ℓ hi
  simp only [boundedConstructibleLowerShriekOfCompactificationOfIsProperIso_inv_eq,
    boundedConstructibleLowerShriekOfCompactificationOfIsProperIso_hom_eq,
    compIso_triangleShriekTriangle_baseChangeTriangleLeft,
    compIso_triangleShriekTriangle_baseChangeTriangleRight]
  exact (𝔽).mateEquiv_shriekBaseChange_eq_compIso (SepFinType.homMk c.overI)
    (SepFinType.homMk c.overG) (SepFinType.homMk c'.overI) (SepFinType.homMk c'.overG)
    (SepFinType.homMk g') (SepFinType.homMk h) (SepFinType.homMk g)
    (SepFinType.homMk_comp_homMk hi.w) (SepFinType.homMk_comp_homMk hp.w)

/-- **The composition square of the lower shriek through triangles**: the isomorphism
`Rg'_! ⋙ Rf_! ≅ R(g' ≫ f)_! = R(f' ≫ g)_! ≅ Rf'_! ⋙ Rg_!` of a commutative square is, up to the
comparisons of compactifications, the composite of the composition isomorphisms of the triangles
`baseChangeTriangleLeft` and `baseChangeTriangleRight`. -/
theorem boundedConstructibleLowerShriekComp_padicAlgCl_inv_comp_hom_eq_triangles
    [IsProper g.left] [IsProper g'.left] (w : g' ≫ f = f' ≫ g) :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (baseChangeTriangleLeft c c' h hi hp w)
    haveI := isIso_exchange_triangleShriekTriangle ℓ (baseChangeTriangleLeft c c' h hi hp w)
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (baseChangeTriangleRight c' (g := g))
    haveI := isIso_exchange_triangleShriekTriangle ℓ (baseChangeTriangleRight c' (g := g))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g' f).inv ≫ eqToHom (by rw [w]) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f' g).hom =
      NatTrans.hcomp (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (compactificationOverField g') (.ofIsProper g'.left)).hom
          (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
            (compactificationOverField f) c).hom ≫
        ((𝔽).compIso (triangleShriekTriangle (baseChangeTriangleLeft c c' h hi hp w))).hom ≫
        ((𝔽).compIso (triangleShriekTriangle (baseChangeTriangleRight c' (g := g)))).inv ≫
        NatTrans.hcomp (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          c' (compactificationOverField f')).hom
          (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
            (.ofIsProper g.left) (compactificationOverField g)).hom := by
  rw [boundedConstructibleLowerShriekComp_padicAlgCl_inv_eq_triangle ℓ g' f
      (baseChangeTriangleLeft c c' h hi hp w),
    boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle ℓ f' g
      (baseChangeTriangleRight c' (g := g))]
  simp only [Category.assoc]
  rw [reassoc_of% (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_copy ℓ w
    (c'.postcomp g.left))]

/-- **`Ex_!` is the mate of the composition isomorphism** (blueprint
`proposition-composition-base-change-rf-shriek`, clause (4)): for a cartesian square
`sq : g' ≫ f = f' ≫ g` with `g` and `g'` proper, the compact-support base-change morphism
`Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` is the mate, for the adjunctions `Lg'^* ⊣ Rg'_*` and
`Lg^* ⊣ Rg_*` transported along `Rg'_! ≅ Rg'_*` and `Rg_! ≅ Rg_*`, of the composition isomorphism
`Rg'_! ⋙ Rf_! ≅ R(g' ≫ f)_! = R(f' ≫ g)_! ≅ Rf'_! ⋙ Rg_!`. -/
theorem boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv'
    (sq : IsPullback g' f' f g) [IsProper g.left] [IsProper g'.left] :
    boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq =
      (mateEquiv ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g').ofNatIsoRight
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g').symm)
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).ofNatIsoRight
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).symm)).symm
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ g' f).symm ≪≫ eqToIso (by rw [sq.w]) ≪≫
          boundedConstructibleLowerShriekComp_padicAlgCl ℓ f' g).hom := by
  obtain ⟨c⟩ : Nonempty (Compactification f.left) := ⟨compactificationOverField f⟩
  have hi := c.overBaseChange_isPullback_i sq
  have hp := c.overBaseChange_isPullback_g sq
  refine Eq.symm ((Equiv.symm_apply_eq _).2 ?_)
  refine Eq.trans ?_ ((mateEquiv_ofNatIsoRight _ _ _ _ _)).symm
  rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_baseChange ℓ sq c
    (c.ofIsPullback sq.overLeft) (c.overBaseChangeFst sq) hi hp]
  have hm := mateEquiv_mk_whiskerRight_comp_comp_whiskerLeft
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ g')
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ g)
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (compactificationOverField f) c).hom
    (boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ c _ _ hi hp)
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (c.ofIsPullback sq.overLeft) (compactificationOverField f')).hom
  erw [hm]
  rw [mateEquiv_boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ c _ _ hi hp sq.w]
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
  rw [boundedConstructibleLowerShriekComp_padicAlgCl_inv_comp_hom_eq_triangles ℓ c _ _ hi hp sq.w]
  simp only [boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_eq ℓ g',
    boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_eq ℓ g]
  refine hcomp_comp_comp_hcomp_eq _ _ _ _ _ _ _ _ _ ?_
  rw [← Iso.symm_hom, boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_symm]

end BaseChange

end AlgebraicGeometry.ProEtale.CondensedRing

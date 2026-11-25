/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.OverPullbackFiniteType
public import WeilConjectures.CategoryTheory.Monoidal.ExceptionalTensorMap
public import WeilConjectures.TraceFormula.BaseChangeCoherence
public import WeilConjectures.TraceFormula.ExceptionalKunnethFunctoriality
public import WeilConjectures.TraceFormula.OpenPieceCoherence
public import WeilConjectures.TraceFormula.PurityTensorMap

/-!

# The exceptional base change map under restriction to an open subscheme

Let
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
be a cartesian square of separated `k`-schemes of finite type, `o : U ⟶ X` an open immersion
and `U' = U ⨯_Y Y'` the fibre product of `o ≫ f` and `g`, with induced open immersion
`o' : U' ⟶ X'`.
This file shows that the restriction `Lo'^*` of the exceptional base change map
`Lg'^* Rf^! L ⟶ Rf'^! Lg^* L` (`ProEtale.CondensedRing.upperShriekBaseChange`) is an isomorphism
if and only if the exceptional base change map of the square of `o ≫ f` is
(`ProEtale.CondensedRing.isIso_upperStar_map_upperShriekBaseChange_iff`).

## Proof

The exceptional base change map is compatible with vertical pasting of cartesian squares
(`ProEtale.CondensedRing.upperShriekBaseChange_paste_vert`, from the pasting of compact-support
base change and the abstract `CategoryTheory.Adjunction.exceptionalBaseChange_paste`), and it is
an isomorphism for a square of open immersions
(`ProEtale.CondensedRing.isIso_upperShriekBaseChange_of_isOpenImmersion`): through
`Ro^! ≅ Lo^*` it is the pullback comparison `Lg'^* Lo^* ≅ Lo'^* Lg^*`, since compact-support
base change is the base change of extension by zero
(`CategoryTheory.Adjunction.exceptionalBaseChange_eq_of_exchangeLeft`). Finally
`Ro'^! ≅ Lo'^*`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

/-- **The exceptional base change of transported adjunctions**: let `L ⊣ R` and `L_o ⊣ L_s` with
`λ : L ≅ L_o` (so that `R ≅ L_s`, the conjugate isomorphism), and similarly for `L' ⊣ R'`. If
the base change `bc : L ⋙ v ⟶ u ⋙ L'` is, through `λ` and `λ'`, the inverse of a morphism
`e : u ⋙ L_o' ⟶ L_o ⋙ v` which is the exchange of an isomorphism
`θ : L_s ⋙ u ≅ v ⋙ L_s'`, then the exceptional base change `u R N ⟶ R' v N` is `θ` through
`R ≅ L_s` and `R' ≅ L_s'`. -/
lemma exceptionalBaseChange_eq_of_exchangeLeft {C D C' D' : Type*} [Category* C]
    [Category* D] [Category* C'] [Category* D'] {L Lo : C ⥤ D} {R Ls : D ⥤ C}
    {L' Lo' : C' ⥤ D'} {R' Ls' : D' ⥤ C'} {v : D ⥤ D'} {u : C ⥤ C'} (a : L ⊣ R)
    (a' : L' ⊣ R') (b : Lo ⊣ Ls) (b' : Lo' ⊣ Ls') (lam : L ≅ Lo) (lam' : L' ≅ Lo')
    (bc : L ⋙ v ⟶ u ⋙ L') [IsIso bc] (θ : Ls ⋙ u ≅ v ⋙ Ls')
    (e : u ⋙ Lo' ⟶ Lo ⋙ v) (he : e = exchangeLeft b b' θ)
    (hbc : ∀ K, bc.app K ≫ lam'.hom.app (u.obj K) ≫ e.app K = v.map (lam.hom.app K)) (N : D) :
    exceptionalBaseChange a a' bc N =
      u.map ((conjugateIsoEquiv a b lam.symm).hom.app N) ≫ θ.hom.app N ≫
        (conjugateIsoEquiv a' b' lam'.symm).inv.app (v.obj N) := by
  subst he
  apply (a'.homEquiv _ _).symm.injective
  have hι := conjugateEquiv_counit a b lam.inv N
  have hι' := conjugateEquiv_counit b' a' lam'.hom (v.obj N)
  have hex :=
    AlgebraicGeometry.ProEtale.CondensedRing.Adjunction.exchangeLeft_app_comp_map_counit_app
      b b' θ N
  have hn := (exchangeLeft b b' θ).naturality ((conjugateEquiv a b lam.inv).app N)
  simp only [Functor.comp_map] at hn
  rw [exceptionalBaseChange, Equiv.symm_apply_apply, homEquiv_counit, IsIso.inv_comp_eq,
    conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_apply_inv]
  simp only [Iso.symm_hom, Iso.symm_inv, Functor.map_comp, Category.assoc, hι']
  have h₁ : a.counit.app N =
      lam.hom.app (R.obj N) ≫ Lo.map ((conjugateEquiv a b lam.inv).app N) ≫ b.counit.app N := by
    rw [hι, Iso.hom_inv_id_app_assoc]
  rw [h₁, v.map_comp, v.map_comp, ← hbc, Category.assoc, Category.assoc, ← reassoc_of% hn,
    hex, ← L'.map_comp_assoc]
  erw [lam'.hom.naturality_assoc]
  simp

/-- **Pasting of exceptional base changes**: for squares of adjunctions `L_o ⊣ R_o`, `L ⊣ R`
(bottom row) and `L_o' ⊣ R_o'`, `L' ⊣ R'` (top row) with base changes
`bc_o : L_o ⋙ u ⟶ w ⋙ L_o'` and `bc : L ⋙ v ⟶ u ⋙ L'`, and adjunctions `L_U ⊣ R_U`,
`L_U' ⊣ R_U'` with `c : L_U ≅ L_o ⋙ L` and `c' : L_U' ≅ L_o' ⋙ L'` such that the base
change `bc_U` is the pasting of `bc_o` and `bc`, the exceptional base change of `bc_U` is that of
`bc_o` followed by `R_o'` of that of `bc`, through the conjugate isomorphisms `R_U ≅ R ⋙ R_o`
and `R_U' ≅ R' ⋙ R_o'`. -/
lemma exceptionalBaseChange_paste {B C D B' C' D' : Type*} [Category* B] [Category* C]
    [Category* D] [Category* B'] [Category* C'] [Category* D'] {Lo : B ⥤ C} {Ro : C ⥤ B}
    {L : C ⥤ D} {R : D ⥤ C} {LU : B ⥤ D} {RU : D ⥤ B} {Lo' : B' ⥤ C'} {Ro' : C' ⥤ B'}
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} {LU' : B' ⥤ D'} {RU' : D' ⥤ B'} {w : B ⥤ B'}
    {u : C ⥤ C'} {v : D ⥤ D'} (ao : Lo ⊣ Ro) (a : L ⊣ R) (aU : LU ⊣ RU)
    (ao' : Lo' ⊣ Ro')
    (a' : L' ⊣ R') (aU' : LU' ⊣ RU') (cL : LU ≅ Lo ⋙ L) (cL' : LU' ≅ Lo' ⋙ L')
    (bcO : Lo ⋙ u ⟶ w ⋙ Lo') [IsIso bcO] (bc : L ⋙ v ⟶ u ⋙ L') [IsIso bc]
    (bcU : LU ⋙ v ⟶ w ⋙ LU') [IsIso bcU]
    (h : ∀ M, bcU.app M ≫ cL'.hom.app (w.obj M) =
      v.map (cL.hom.app M) ≫ bc.app (Lo.obj M) ≫ L'.map (bcO.app M)) (N : D) :
    exceptionalBaseChange aU aU' bcU N ≫
        (conjugateIsoEquiv aU' (ao'.comp a') cL'.symm).hom.app (v.obj N) =
      w.map ((conjugateIsoEquiv aU (ao.comp a) cL.symm).hom.app N) ≫
        exceptionalBaseChange ao ao' bcO (R.obj N) ≫
          Ro'.map (exceptionalBaseChange a a' bc N) := by
  apply ((ao'.comp a').homEquiv _ _).symm.injective
  have hc := conjugateEquiv_counit aU (ao.comp a) cL.inv N
  have hc' := conjugateEquiv_counit aU' (ao'.comp a') cL'.inv (v.obj N)
  have hU : LU'.map (exceptionalBaseChange aU aU' bcU N) ≫ aU'.counit.app (v.obj N) =
      inv (bcU.app (RU.obj N)) ≫ v.map (aU.counit.app N) :=
    (aU'.homEquiv _ _).symm_apply_apply _
  have hO : Lo'.map (exceptionalBaseChange ao ao' bcO (R.obj N)) ≫
      ao'.counit.app (u.obj (R.obj N)) =
      inv (bcO.app (Ro.obj (R.obj N))) ≫ u.map (ao.counit.app (R.obj N)) :=
    (ao'.homEquiv _ _).symm_apply_apply _
  have hF : L'.map (exceptionalBaseChange a a' bc N) ≫ a'.counit.app (v.obj N) =
      inv (bc.app (R.obj N)) ≫ v.map (a.counit.app N) :=
    (a'.homEquiv _ _).symm_apply_apply _
  have hinv (M : B) : inv (bcU.app M) = cL'.hom.app (w.obj M) ≫ L'.map (inv (bcO.app M)) ≫
      inv (bc.app (Lo.obj M)) ≫ v.map (cL.inv.app M) := by
    rw [IsIso.inv_eq_of_hom_inv_id]
    rw [reassoc_of% h]
    simp
  simp only [comp_counit_app, Functor.comp_obj, Functor.comp_map] at hc hc'
  rw [homEquiv_counit, homEquiv_counit, conjugateIsoEquiv_apply_hom,
    conjugateIsoEquiv_apply_hom]
  simp only [Iso.symm_hom, Functor.comp_map, comp_counit_app, Functor.comp_obj, Functor.map_comp,
    Category.assoc]
  have n1 := cL'.inv.naturality (exceptionalBaseChange aU aU' bcU N)
  have n2 := ao'.counit.naturality (exceptionalBaseChange a a' bc N)
  have n3 := (inv bc).naturality
    (Lo.map ((conjugateEquiv aU (ao.comp a) cL.inv).app N) ≫ ao.counit.app (R.obj N))
  have n4 := (inv bcO).naturality ((conjugateEquiv aU (ao.comp a) cL.inv).app N)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj,
    NatIso.isIso_inv_app, Functor.map_comp] at n1 n2 n3 n4
  rw [hc', reassoc_of% n1, hU, hinv, ← L'.map_comp_assoc (Lo'.map (Ro'.map _)), n2,
    L'.map_comp_assoc, hF, ← L'.map_comp_assoc (Lo'.map (exceptionalBaseChange _ _ _ _)), hO]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← v.map_comp, ← hc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← L'.map_comp_assoc, n4]
  simp only [Functor.map_comp, Category.assoc, reassoc_of% n3]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' U U' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]

/-- The exceptional base change map is the abstract exceptional base change
`Adjunction.exceptionalBaseChange` of the adjunctions `Rf_! ⊣ Rf^!` and `Rf'_! ⊣ Rf'^!`. -/
lemma upperShriekBaseChange_eq_exceptionalBaseChange {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    haveI := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
    upperShriekBaseChange ℓ sq L = Adjunction.exceptionalBaseChange
      (boundedConstructibleUpperShriekAdjunction ℓ f)
      (boundedConstructibleUpperShriekAdjunction ℓ f')
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq) L :=
  rfl

/-- **The exceptional base change map along an open immersion is an isomorphism**: for a
cartesian square with vertical open immersions `o` and `o'`, `Lg'^* Ro^! M ⟶ Ro'^! Lg^* M` is
`Lg'^* Lo^* M ≅ Lo'^* Lg^* M` through `Ro^! ≅ Lo^*` and `Ro'^! ≅ Lo'^*`. -/
theorem isIso_upperShriekBaseChange_of_isOpenImmersion {o : U ⟶ X} {g : X' ⟶ X} {o' : U' ⟶ X'}
    {g' : U' ⟶ U} (sq : IsPullback g' o' o g) [IsOpenImmersion o.left]
    [IsOpenImmersion o'.left] (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (upperShriekBaseChange ℓ sq M) := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  have h := Adjunction.exceptionalBaseChange_eq_of_exchangeLeft
    (boundedConstructibleUpperShriekAdjunction ℓ o)
    (boundedConstructibleUpperShriekAdjunction ℓ o')
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ o)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ o')
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ o)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ o')
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
      sq.toCommSq.flip)
    (boundedConstructibleOpenImmersionLowerShriekBaseChange' (Profinite.padicAlgClRingObj ℓ) ℓ
      sq.toCommSq)
    (boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft _ ℓ sq.toCommSq)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isOpenImmersion ℓ sq) M
  rw [upperShriekBaseChange_eq_exceptionalBaseChange, h]
  infer_instance

/-- **The exceptional base change map is compatible with vertical pasting**: for cartesian
squares
```
U' --gU--> U
|          |
o'         o
v          v
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
the exceptional base change map of the outer square is that of the upper square followed by
`Ro'^!` of that of the lower square, through `R(o ≫ f)^! ≅ Ro^! Rf^!` and
`R(o' ≫ f')^! ≅ Ro'^! Rf'^!`. -/
theorem upperShriekBaseChange_paste_vert {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g) {o : U ⟶ X} {o' : U' ⟶ X'} {gU : U' ⟶ U}
    (sqo : IsPullback gU o' o g') (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    upperShriekBaseChange ℓ (sqo.paste_vert sq) L ≫
        (boundedConstructibleUpperShriekComp_padicAlgCl ℓ o' f').hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj L) =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ gU).map
          ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ o f).hom.app L) ≫
        upperShriekBaseChange ℓ sqo
          ((boundedConstructibleUpperShriek ℓ f).obj L) ≫
        (boundedConstructibleUpperShriek ℓ o').map
          (upperShriekBaseChange ℓ sq L) := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqo
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (sqo.paste_vert sq)
  exact Adjunction.exceptionalBaseChange_paste
    (boundedConstructibleUpperShriekAdjunction ℓ o)
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleUpperShriekAdjunction ℓ (o ≫ f))
    (boundedConstructibleUpperShriekAdjunction ℓ o')
    (boundedConstructibleUpperShriekAdjunction ℓ f')
    (boundedConstructibleUpperShriekAdjunction ℓ (o' ≫ f'))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ o f)
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ o' f')
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqo)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (sqo.paste_vert sq))
    (fun M ↦ by
      rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert ℓ sqo sq M]
      simp) L

/-- **The exceptional base change map and restriction to an open subscheme**: in the situation of
`upperShriekBaseChange_paste_vert` with `o` an open immersion, `Ro'^!` of the exceptional base
change map of the lower square is an isomorphism if and only if the exceptional base change map
of the outer square is, the one of the upper square being invertible. -/
theorem isIso_upperShriek_map_upperShriekBaseChange_iff {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g) {o : U ⟶ X} {o' : U' ⟶ X'}
    {gU : U' ⟶ U} (sqo : IsPullback gU o' o g') [IsOpenImmersion o.left]
    [IsOpenImmersion o'.left] (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperShriek ℓ o').map
        (upperShriekBaseChange ℓ sq L)) ↔
      IsIso (upperShriekBaseChange ℓ (sqo.paste_vert sq) L) := by
  have := isIso_upperShriekBaseChange_of_isOpenImmersion ℓ sqo
    ((boundedConstructibleUpperShriek ℓ f).obj L)
  rw [← isIso_comp_right_iff (upperShriekBaseChange ℓ (sqo.paste_vert sq) L)
    ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ o' f').hom.app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj L)),
    upperShriekBaseChange_paste_vert ℓ sq sqo L, isIso_comp_left_iff, isIso_comp_left_iff]

/-- **The exceptional base change map and restriction to an open subscheme**, with the pullback
`Lo'^*` in place of `Ro'^!` (`Ro'^! ≅ Lo'^*` for the open immersion `o'`). -/
theorem isIso_upperStar_map_upperShriekBaseChange_iff_of_isPullback {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g) {o : U ⟶ X} {o' : U' ⟶ X'}
    {gU : U' ⟶ U} {fU : U' ⟶ Y'} (sqo : IsPullback gU o' o g')
    (sqU : IsPullback gU fU (o ≫ f) g)
    (hfU : o' ≫ f' = fU) [IsOpenImmersion o.left]
    [IsOpenImmersion o'.left] (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ o').map
        (upperShriekBaseChange ℓ sq L)) ↔
      IsIso (upperShriekBaseChange ℓ sqU L) := by
  subst hfU
  rw [← NatIso.isIso_map_iff (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ o')]
  exact isIso_upperShriek_map_upperShriekBaseChange_iff ℓ sq sqo L

/-- **The exceptional base change map and restriction to an open subscheme**, for the fibre
product `U' = U ⨯_Y Y'` of `o ≫ f` and `g`: with `o' : U' ⟶ X'` the induced open immersion,
`Lo'^*` of the exceptional base change map of the square of `f` is an isomorphism if and only if
the exceptional base change map of the square of `o ≫ f` is. -/
theorem isIso_upperStar_map_upperShriekBaseChange_iff {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g) (o : U ⟶ X) [IsOpenImmersion o.left]
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (sq.lift (pullback.fst (o ≫ f) g ≫ o) (pullback.snd (o ≫ f) g)
          (by rw [Category.assoc, pullback.condition]))).map
        (upperShriekBaseChange ℓ sq L)) ↔
      IsIso (upperShriekBaseChange ℓ (IsPullback.of_hasPullback (o ≫ f) g) L) := by
  have sqo : IsPullback (pullback.fst (o ≫ f) g)
      (sq.lift (pullback.fst (o ≫ f) g ≫ o) (pullback.snd (o ≫ f) g)
        (by rw [Category.assoc, pullback.condition])) o g' :=
    IsPullback.of_bot ((sq.lift_snd _ _ _).symm ▸ IsPullback.of_hasPullback (o ≫ f) g)
      (sq.lift_fst _ _ _).symm sq
  have hsqo := sqo.map (Over.forget _)
  simp only [Over.forget_map] at hsqo
  have : IsOpenImmersion (sq.lift (pullback.fst (o ≫ f) g ≫ o) (pullback.snd (o ≫ f) g)
      (by rw [Category.assoc, pullback.condition])).left :=
    MorphismProperty.of_isPullback hsqo inferInstance
  exact isIso_upperStar_map_upperShriekBaseChange_iff_of_isPullback ℓ sq sqo
    (IsPullback.of_hasPullback (o ≫ f) g) (sq.lift_snd _ _ _) L

/-- **The exceptional base change map at the unit and restriction to an open subscheme**
(`isIso_upperStar_map_upperShriekBaseChange_iff` at `L = ℚ̄_ℓ`). -/
theorem isIso_upperStar_map_upperShriekBaseChange_unit_iff {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g) (o : U ⟶ X)
    [IsOpenImmersion o.left] :
    IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (sq.lift (pullback.fst (o ≫ f) g ≫ o) (pullback.snd (o ≫ f) g)
          (by rw [Category.assoc, pullback.condition]))).map
        (upperShriekBaseChange ℓ sq
          (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)))) ↔
      IsIso (upperShriekBaseChange ℓ (IsPullback.of_hasPullback (o ≫ f) g)
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) :=
  isIso_upperStar_map_upperShriekBaseChange_iff ℓ sq o _

end AlgebraicGeometry.ProEtale.CondensedRing

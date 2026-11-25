/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarComparisons
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarPullbackCube
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarExchangeRightAdjunct

/-! # The exchange equality for condensed finite-to-Qbar coefficient change -/

@[expose] public section

-- Keep resolution constructions out of implicit instance matching.
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

private theorem lifted_naturality
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (PC : ObjectProperty C) (PD : ObjectProperty D)
    (PE : ObjectProperty E) (PF : ObjectProperty F)
    {l : C ⥤ D} {tD : D ⥤ F} {tC : C ⥤ E} {l' : E ⥤ F}
    (hl : ∀ K : PC.FullSubcategory, PD (l.obj K.obj))
    (htD : ∀ K : PD.FullSubcategory, PF (tD.obj K.obj))
    (htC : ∀ K : PC.FullSubcategory, PE (tC.obj K.obj))
    (hl' : ∀ K : PE.FullSubcategory, PF (l'.obj K.obj))
    (α : l ⋙ tD ≅ tC ⋙ l')
    {K M : PC.FullSubcategory} (v : K ⟶ M) :
    (PF.lift (PD.ι ⋙ tD) htD).map ((PD.lift (PC.ι ⋙ l) hl).map v) ≫
        (PF.isoMk (α.app M.obj)).hom =
      (PF.isoMk (α.app K.obj)).hom ≫
        (PF.lift (PE.ι ⋙ l') hl').map ((PE.lift (PC.ι ⋙ tC) htC).map v) := by
  exact ObjectProperty.hom_ext _ (α.hom.naturality v.hom)

private theorem path_exchange {C : Type*} [Category C]
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ A₉ A₁₀ A₁₁ : C}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃} {d : A₃ ⟶ A₄}
    {e : A₂ ⟶ A₅} {h : A₅ ⟶ A₄} {z : A₁ ⟶ A₆} {j : A₆ ⟶ A₅}
    {p : A₆ ⟶ A₇} {t : A₇ ⟶ A₄} {q : A₀ ⟶ A₈} {w : A₈ ⟶ A₉}
    {s : A₉ ⟶ A₇} {v : A₉ ⟶ A₁₀} {u : A₁₀ ⟶ A₄}
    {x : A₈ ⟶ A₁₁} {y : A₁₁ ⟶ A₁₀}
    (h₁ : c ≫ d = e ≫ h) (h₂ : b ≫ e = z ≫ j)
    (h₃ : j ≫ h = p ≫ t) (h₄ : a ≫ z ≫ p = q ≫ w ≫ s)
    (h₅ : s ≫ t = v ≫ u) (h₆ : w ≫ v = x ≫ y) :
    a ≫ b ≫ c ≫ d = q ≫ x ≫ y ≫ u := by
  rw [h₁, ← Category.assoc b e h, h₂, Category.assoc z j h, h₃]
  rw [← Category.assoc z p t, ← Category.assoc a (z ≫ p) t, h₄]
  simp only [Category.assoc]
  rw [h₅, ← Category.assoc w v u, h₆, Category.assoc]

private theorem left_normalization
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {lf : B ⥤ A} {rf : A ⥤ B} {lg : B ⥤ D}
    {lp : D ⥤ C} {gp : A ⥤ C} {rp : C ⥤ D}
    {Lf : B' ⥤ A'} {Rf : A' ⥤ B'} {Lg : B' ⥤ D'}
    {Lp : D' ⥤ C'} {Gp : A' ⥤ C'} {Rp : C' ⥤ D'}
    {tA : A ⥤ A'} {tB : B ⥤ B'} {tC : C ⥤ C'} {tD : D ⥤ D'}
    (εf : rf ⋙ lf ⟶ 𝟭 A) (εp : rp ⋙ lp ⟶ 𝟭 C)
    (εF : Rf ⋙ Lf ⟶ 𝟭 A') (εP : Rp ⋙ Lp ⟶ 𝟭 C')
    (αf : ∀ V, tA.obj (lf.obj V) ≅ Lf.obj (tB.obj V))
    (αg : ∀ V, tD.obj (lg.obj V) ≅ Lg.obj (tB.obj V))
    (αp : ∀ V, tC.obj (lp.obj V) ≅ Lp.obj (tD.obj V))
    (αq : ∀ V, tC.obj (gp.obj V) ≅ Gp.obj (tA.obj V))
    (hn : ∀ {U V : A} (v : U ⟶ V),
      tC.map (gp.map v) ≫ (αq V).hom = (αq U).hom ≫ Gp.map (tA.map v))
    (sqE : lg ⋙ lp ⟶ lf ⋙ gp) (sqΩ : Lg ⋙ Lp ⟶ Lf ⋙ Gp)
    (β : rf ⋙ lg ⟶ gp ⋙ rp) (Β : Rf ⋙ Lg ⟶ Gp ⋙ Rp)
    (K : A) (δ : tB.obj (rf.obj K) ⟶ Rf.obj (tA.obj K))
    (hβ : coefficientAdjunctCondition εf εp sqE β K)
    (hΒ : coefficientAdjunctCondition εF εP sqΩ Β (tA.obj K))
    (hδ : Lf.map δ ≫ εF.app (tA.obj K) =
      (αf (rf.obj K)).inv ≫ tA.map (εf.app K))
    (hc : coefficientPullbackCube αf αg αp αq sqE sqΩ (rf.obj K)) :
    Lp.map (((αg (rf.obj K)).hom ≫ Lg.map δ) ≫ Β.app (tA.obj K)) ≫
        εP.app (Gp.obj (tA.obj K)) =
      (αp (lg.obj (rf.obj K))).inv ≫
        tC.map (lp.map (β.app K) ≫ εp.app (gp.obj K)) ≫ (αq K).hom := by
  dsimp only [coefficientAdjunctCondition] at hβ hΒ
  dsimp only [coefficientPullbackCube] at hc
  have hz := sqΩ.naturality δ
  have hah := hn (εf.app K)
  have hmδ := Gp.congr_map hδ
  have hmβ := tC.congr_map hβ
  simp only [Functor.comp_obj, Functor.comp_map] at hz
  simp only [Functor.comp_obj, Functor.id_obj] at hah
  simp only [Functor.map_comp] at hmδ hmβ
  have hp := path_exchange hΒ hz hmδ hc.symm hah.symm hmβ.symm
  simpa only [Functor.map_comp, Category.assoc] using hp

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))

section Edge

variable {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
  [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
  [IsSeparated (T ↘ Spec (.of k))]
  [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
  [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]

private theorem pull_hom_naturality {K M : PadicSubfieldConstructible U ℓ E}
    (v : K ⟶ M) :
    (constructibleToPadicAlgCl T ℓ E).map
        ((boundedConstructibleUpperStar (k := k)
      (X := T.asOver (Spec (.of k))) (Y := U.asOver (Spec (.of k)))
        (Profinite.continuousMapRingObj E) ℓ (h.asOver (Spec (.of k)))).map v) ≫
      (constructibleToQbarPullIso ℓ k E h M).hom =
    (constructibleToQbarPullIso ℓ k E h K).hom ≫
      (boundedConstructibleUpperStar (k := k)
      (X := T.asOver (Spec (.of k))) (Y := U.asOver (Spec (.of k)))
        (Profinite.padicAlgClRingObj ℓ) ℓ (h.asOver (Spec (.of k)))).map
        ((constructibleToPadicAlgCl U ℓ E).map v) := by
  exact lifted_naturality _ _ _ _
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj (k := k)
      (X := T.asOver (Spec (.of k))) (Y := U.asOver (Spec (.of k))) _ ℓ (h.asOver (Spec
        (.of k))) K)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj T ℓ E K)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj U ℓ E K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj (k := k)
      (X := T.asOver (Spec (.of k))) (Y := U.asOver (Spec (.of k))) _ ℓ (h.asOver (Spec
        (.of k))) K)
    (derivedPullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) h) v

end Edge

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

attribute [local irreducible] constructibleToQbarPullIso constructibleToQbarPushHom
  boundedConstructibleUpperStar boundedConstructibleLowerStar constructibleToPadicAlgCl
  boundedConstructibleUpperStarLowerStarAdjunction
  ContinuousMapRingObj.boundedConstructibleLowerStar
  ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction

set_option backward.isDefEq.respectTransparency true in
attribute [-instance] catToReflQuiver in
set_option backward.isDefEq.respectTransparency true in
/-- Normalization of the left side of coefficient exchange under the pullback adjunction.
Source: ModuleObject/Colimit/TwoColimit.lean, final transport paragraph;
ChangeOfCoefficients.lean, derivedPullIso and derivedPushHom;
Mathlib/CategoryTheory/Adjunction/Mates.lean
(blueprint: lem-weil-pbc-qbar-condensed-exchange-left-adjunct).

Proof in words. Expand the left adjunct using functoriality. The adjunct of the Omega base-change
map is its square comparison followed by pullback of the counit: this follows by expanding
the mate, then applying naturality and the triangle identity. Move the push comparison for f
through the square by naturality. Its adjunct is inverse alpha_f followed by scalar extension
of the E counit, since pushHomOfComapIso is the mate of inverse pullIsoOfComapIso; the
iterated mate/conjugation identity proves this assertion. Coefficient pullback comparisons
commute with the specified square comparison: restriction of scalars commutes strictly with
pushforward, these comparisons respect pushforward composition after forgetting module
actions, and localization uniqueness gives the corresponding right-derived coherence.
Conjugating gives coherence for the specified derived pullback composition maps, hence for
the square maps obtained from them and sq.w. Restrict along the fully faithful constructible
inclusions. Substitute this cube identity, use naturality of alpha_g' on the E counit, and
use the E base-change adjunct identity in reverse. Functoriality combines the E base-change
map and its counit, giving exactly the displayed middle expression. Only pullback
comparisons are inverted. No properness or Cartesianity is required. -/
theorem constructibleToQbar_exchange_left_adjunct
    (sq : CommSq g' f' f g) (K : PadicSubfieldConstructible X ℓ E) :
    (boundedConstructibleUpperStar (k := k)
      (X := X'.asOver (Spec (.of k))) (Y := Y'.asOver (Spec (.of k)))
        (Profinite.padicAlgClRingObj ℓ) ℓ (f'.asOver (Spec (.of k)))).map
      (constructibleToQbarSourceHom ℓ k E f g K ≫
        (boundedConstructibleBaseChange (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
      (X' := X'.asOver (Spec (.of k))) (Y' := Y'.asOver (Spec (.of k)))
        ℓ (sq.asOver (Spec (.of k)))).app
          ((constructibleToPadicAlgCl X ℓ E).obj K)) ≫
      (boundedConstructibleUpperStarLowerStarAdjunction (k := k)
      (X := X'.asOver (Spec (.of k))) (Y := Y'.asOver (Spec (.of k)))
        ℓ (f'.asOver (Spec (.of k)))).counit.app
          ((boundedConstructibleUpperStar (k := k)
      (X := X'.asOver (Spec (.of k))) (Y := X.asOver (Spec (.of k)))
        (Profinite.padicAlgClRingObj ℓ) ℓ (g'.asOver (Spec (.of k)))).obj
            ((constructibleToPadicAlgCl X ℓ E).obj K)) =
    (constructibleToQbarPullIso ℓ k E f'
        ((boundedConstructibleUpperStar (k := k)
      (X := Y'.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
        (Profinite.continuousMapRingObj E) ℓ (g.asOver (Spec (.of k)))).obj
          ((ContinuousMapRingObj.boundedConstructibleLowerStar (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
        ℓ E (f.asOver (Spec (.of k)))).obj K))).inv ≫
      (constructibleToPadicAlgCl X' ℓ E).map
        ((boundedConstructibleUpperStar (k := k)
      (X := X'.asOver (Spec (.of k))) (Y := Y'.asOver (Spec (.of k)))
        (Profinite.continuousMapRingObj E) ℓ (f'.asOver (Spec (.of k)))).map
            ((ContinuousMapRingObj.boundedConstructibleBaseChange (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
      (X' := X'.asOver (Spec (.of k))) (Y' := Y'.asOver (Spec (.of k)))
        ℓ E (sq.asOver (Spec (.of k)))).app K) ≫
          (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction (k := k)
      (X := X'.asOver (Spec (.of k))) (Y := Y'.asOver (Spec (.of k)))
        ℓ E (f'.asOver (Spec (.of k)))).counit.app
              ((boundedConstructibleUpperStar (k := k)
      (X := X'.asOver (Spec (.of k))) (Y := X.asOver (Spec (.of k)))
        (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of k)))).obj K)) ≫
      (constructibleToQbarPullIso ℓ k E g' K).hom := by
  dsimp only [constructibleToQbarSourceHom]
  exact left_normalization
    (A := AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj
      (Profinite.continuousMapRingObj E) (X.asOver (Spec (.of k))).left))
    (B := AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj
      (Profinite.continuousMapRingObj E) (Y.asOver (Spec (.of k))).left))
    (C := AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj
      (Profinite.continuousMapRingObj E) (X'.asOver (Spec (.of k))).left))
    (D := AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj
      (Profinite.continuousMapRingObj E) (Y'.asOver (Spec (.of k))).left))
    (A' := AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj
      (Profinite.padicAlgClRingObj ℓ) (X.asOver (Spec (.of k))).left))
    (B' := AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj
      (Profinite.padicAlgClRingObj ℓ) (Y.asOver (Spec (.of k))).left))
    (C' := AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj
      (Profinite.padicAlgClRingObj ℓ) (X'.asOver (Spec (.of k))).left))
    (D' := AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj
      (Profinite.padicAlgClRingObj ℓ) (Y'.asOver (Spec (.of k))).left))
    (lf := boundedConstructibleUpperStar (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
        (Profinite.continuousMapRingObj E) ℓ
      (f.asOver (Spec (.of k))))
    (rf := ContinuousMapRingObj.boundedConstructibleLowerStar (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
        ℓ E
      (f.asOver (Spec (.of k))))
    (lg := boundedConstructibleUpperStar (k := k)
      (X := Y'.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
        (Profinite.continuousMapRingObj E) ℓ
      (g.asOver (Spec (.of k))))
    (lp := boundedConstructibleUpperStar (k := k)
      (X := X'.asOver (Spec (.of k))) (Y := Y'.asOver (Spec (.of k)))
        (Profinite.continuousMapRingObj E) ℓ
      (f'.asOver (Spec (.of k))))
    (gp := boundedConstructibleUpperStar (k := k)
      (X := X'.asOver (Spec (.of k))) (Y := X.asOver (Spec (.of k)))
        (Profinite.continuousMapRingObj E) ℓ
      (g'.asOver (Spec (.of k))))
    (rp := ContinuousMapRingObj.boundedConstructibleLowerStar (k := k)
      (X := X'.asOver (Spec (.of k))) (Y := Y'.asOver (Spec (.of k)))
        ℓ E
      (f'.asOver (Spec (.of k))))
    (Lf := boundedConstructibleUpperStar (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
        (Profinite.padicAlgClRingObj ℓ) ℓ
      (f.asOver (Spec (.of k))))
    (Rf := boundedConstructibleLowerStar (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
        ℓ
      (f.asOver (Spec (.of k))))
    (Lg := boundedConstructibleUpperStar (k := k)
      (X := Y'.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
        (Profinite.padicAlgClRingObj ℓ) ℓ
      (g.asOver (Spec (.of k))))
    (Lp := boundedConstructibleUpperStar (k := k)
      (X := X'.asOver (Spec (.of k))) (Y := Y'.asOver (Spec (.of k)))
        (Profinite.padicAlgClRingObj ℓ) ℓ
      (f'.asOver (Spec (.of k))))
    (Gp := boundedConstructibleUpperStar (k := k)
      (X := X'.asOver (Spec (.of k))) (Y := X.asOver (Spec (.of k)))
        (Profinite.padicAlgClRingObj ℓ) ℓ
      (g'.asOver (Spec (.of k))))
    (Rp := boundedConstructibleLowerStar (k := k)
      (X := X'.asOver (Spec (.of k))) (Y := Y'.asOver (Spec (.of k)))
        ℓ
      (f'.asOver (Spec (.of k))))
    (tA := constructibleToPadicAlgCl X ℓ E)
    (tB := constructibleToPadicAlgCl Y ℓ E)
    (tC := constructibleToPadicAlgCl X' ℓ E)
    (tD := constructibleToPadicAlgCl Y' ℓ E)
    (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
        ℓ E
      (f.asOver (Spec (.of k)))).counit
    (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction (k := k)
      (X := X'.asOver (Spec (.of k))) (Y := Y'.asOver (Spec (.of k)))
        ℓ E
      (f'.asOver (Spec (.of k)))).counit
    (boundedConstructibleUpperStarLowerStarAdjunction (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
        ℓ
      (f.asOver (Spec (.of k)))).counit
    (boundedConstructibleUpperStarLowerStarAdjunction (k := k)
      (X := X'.asOver (Spec (.of k))) (Y := Y'.asOver (Spec (.of k)))
        ℓ
      (f'.asOver (Spec (.of k)))).counit
    (fun V ↦ constructibleToQbarPullIso ℓ k E f V)
    (fun V ↦ constructibleToQbarPullIso ℓ k E g V)
    (fun V ↦ constructibleToQbarPullIso ℓ k E f' V)
    (fun V ↦ constructibleToQbarPullIso ℓ k E g' V)
    (fun v ↦ pull_hom_naturality ℓ k E g' v)
    (boundedConstructiblePullbackSquareComparison (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
      (X' := X'.asOver (Spec (.of k))) (Y' := Y'.asOver (Spec (.of k)))
        (Profinite.continuousMapRingObj E) ℓ
      (sq.asOver (Spec (.of k)))).hom
    (boundedConstructiblePullbackSquareComparison (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
      (X' := X'.asOver (Spec (.of k))) (Y' := Y'.asOver (Spec (.of k)))
        (Profinite.padicAlgClRingObj ℓ) ℓ
      (sq.asOver (Spec (.of k)))).hom
    (ContinuousMapRingObj.boundedConstructibleBaseChange (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
      (X' := X'.asOver (Spec (.of k))) (Y' := Y'.asOver (Spec (.of k)))
        ℓ E
      (sq.asOver (Spec (.of k))))
    (boundedConstructibleBaseChange (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
      (X' := X'.asOver (Spec (.of k))) (Y' := Y'.asOver (Spec (.of k)))
        ℓ
      (sq.asOver (Spec (.of k))))
    K (constructibleToQbarPushHom ℓ k E f K)
    (coefficientAdjunctCondition_of_eq
    (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
      ℓ E (f.asOver (Spec (.of k))))
    (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction (k := k)
      (X := X'.asOver (Spec (.of k))) (Y := Y'.asOver (Spec (.of k)))
      ℓ E (f'.asOver (Spec (.of k))))
    (boundedConstructiblePullbackSquareComparison (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
      (X' := X'.asOver (Spec (.of k))) (Y' := Y'.asOver (Spec (.of k)))
      (Profinite.continuousMapRingObj E) ℓ (sq.asOver (Spec (.of k))))
    (ContinuousMapRingObj.boundedConstructibleBaseChange (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
      (X' := X'.asOver (Spec (.of k))) (Y' := Y'.asOver (Spec (.of k)))
      ℓ E (sq.asOver (Spec (.of k))))
    (ContinuousMapRingObj.boundedConstructibleBaseChange_eq_squareExchange (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
      (X' := X'.asOver (Spec (.of k))) (Y' := Y'.asOver (Spec (.of k)))
      ℓ E (sq.asOver (Spec (.of k)))) K)
    (coefficientAdjunctCondition_of_eq
    (boundedConstructibleUpperStarLowerStarAdjunction (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
      ℓ (f.asOver (Spec (.of k))))
    (boundedConstructibleUpperStarLowerStarAdjunction (k := k)
      (X := X'.asOver (Spec (.of k))) (Y := Y'.asOver (Spec (.of k)))
      ℓ (f'.asOver (Spec (.of k))))
    (boundedConstructiblePullbackSquareComparison (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
      (X' := X'.asOver (Spec (.of k))) (Y' := Y'.asOver (Spec (.of k)))
      (Profinite.padicAlgClRingObj ℓ) ℓ (sq.asOver (Spec (.of k))))
    (boundedConstructibleBaseChange (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
      (X' := X'.asOver (Spec (.of k))) (Y' := Y'.asOver (Spec (.of k)))
      ℓ (sq.asOver (Spec (.of k))))
    (boundedConstructibleBaseChange_eq_squareExchange (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
      (X' := X'.asOver (Spec (.of k))) (Y' := Y'.asOver (Spec (.of k)))
      ℓ (sq.asOver (Spec (.of k))))
        ((constructibleToPadicAlgCl X ℓ E).obj K))
    (constructibleToQbar_push_counit ℓ k E f K)
    (constructibleToQbar_pullback_cube ℓ k E f g f' g' sq
      ((ContinuousMapRingObj.boundedConstructibleLowerStar (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
        ℓ E
        (f.asOver (Spec (.of k)))).obj K))

end AlgebraicGeometry.ProEtale.CondensedRing

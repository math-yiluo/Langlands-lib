/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProjectiveLineTraceModel
import WeilConjectures.AlgebraicGeometry.FiniteShiftedLineSquare
import WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar
import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange

/-! # Exchange for the coefficient trace on projective-line presentations -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace
attribute [local instance 20000] Etale.sheafBraidedCategory

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  rightDerivedLowerShriekBaseChangeMap rightDerivedLowerShriekIsoRightDerivedLowerStar

section ProperComparisons

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.leftDerivedFunctor

private theorem proper_hom_app
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q] [HasCompactification q]
    (K : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app K =
      R(((HasCompactification.compactification q).g)_*[ModuleCat.{u + 1} A]).map
        ((derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A)
          (HasCompactification.compactification q).i).app K) ≫
      (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A)
        (HasCompactification.compactification q).i
        (HasCompactification.compactification q).g q
        (HasCompactification.compactification q).comm).app K := by
  rw [rightDerivedLowerShriekIsoRightDerivedLowerStar_hom,
    rightDerivedLowerShriekToLowerStarComp_comp_eq]
  rfl

attribute [local irreducible] rightDerivedLowerShriekOfCompactificationIso

private theorem proper_compactification_hom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q] [HasCompactification q]
    [QuasiCompact q] (c : Compactification q) (K : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekIso A c).hom.app K ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app K =
      R((c.g)_*[ModuleCat.{u + 1} A]).map
        ((derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app K) ≫
      (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) c.i c.g q c.comm).app K := by
  exact (congrArg (fun z ↦ (rightDerivedLowerShriekIso A c).hom.app K ≫ z)
    (proper_hom_app A q K)).trans
      (rightDerivedLowerShriekOfCompactificationIso_hom_app_comp_toLowerStar
        A c (HasCompactification.compactification q) K)

private theorem raw_exchange_combined
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' q' q g)
    (c : Compactification q) (c' : Compactification q') (h : c'.Z ⟶ c.Z)
    (hi : IsPullback g' c'.i c.i h) (hp : CommSq h c'.g c.g g)
    (K : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap' (ModuleCat.{u + 1} A)
        c c' h hi hp).app K ≫
      R((c'.g)_*[ModuleCat.{u + 1} A]).map
        ((derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c'.i).app
          (L((g')^*[ModuleCat.{u + 1} A]).obj K)) ≫
      (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) c'.i c'.g q' c'.comm).app
        (L((g')^*[ModuleCat.{u + 1} A]).obj K) =
    L((g)^*[ModuleCat.{u + 1} A]).map
      (R((c.g)_*[ModuleCat.{u + 1} A]).map
        ((derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app K) ≫
        (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) c.i c.g q c.comm).app K) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app K := by
  exact (rightDerivedLowerShriekOfCompactificationBaseChangeMap'_app_comp_toLowerStar
    (ModuleCat.{u + 1} A) sq c c' h hi hp K).trans
    (CategoryTheory.Functor.map_comp_assoc L((g)^*[ModuleCat.{u + 1} A]) _ _ _).symm

private theorem exchange_of_forget
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {K₀ K₁ : C} {T₀ T₁ T₂ T₃ : D}
    (a : F.obj K₀ ⟶ T₀) (b : T₀ ⟶ T₁) (p : T₁ ⟶ T₃)
    (f : T₀ ⟶ T₂) (g : T₂ ⟶ T₃) (d s : K₀ ⟶ K₁)
    (e : F.obj K₁ ⟶ T₃)
    (hi : b ≫ p = f ≫ g) (hb : a ≫ f ≫ g = F.map s ≫ e) (hq : d = s) :
    a ≫ b ≫ p = F.map d ≫ e := by
  rw [hi, hb, hq]

private theorem comp_whisker_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    {P : C ⥤ E} {J : C ⥤ D} {Q Q' : D ⥤ E}
    (a : P ⟶ J ⋙ Q) (b : Q ⟶ Q') (K : C) :
    (a ≫ Functor.whiskerLeft J b).app K = a.app K ≫ b.app (J.obj K) := rfl

attribute [local irreducible] rightDerivedLowerShriekBaseChangeMap'

private theorem primed_exchange_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [HasCompactification q'] [QuasiCompact q']
    (c : Compactification q) (c' : Compactification q') (h : c'.Z ⟶ c.Z)
    (hi : IsPullback g' c'.i c.i h) (hp : CommSq h c'.g c.g g)
    (K : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekBaseChangeMap' A c c' h hi hp).app K =
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap' (ModuleCat.{u + 1} A)
        c c' h hi hp).app K ≫
      (rightDerivedLowerShriekIso A c').hom.app (L((g')^*[ModuleCat.{u + 1} A]).obj K) := by
  simpa only [rightDerivedLowerShriekBaseChangeMap'] using
    comp_whisker_app
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap' (ModuleCat.{u + 1} A)
        c c' h hi hp) (rightDerivedLowerShriekIso A c').hom K

private theorem proper_exchange_raw
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' q' q g)
    [IsProper q] [IsProper q'] [HasCompactification q] [HasCompactification q']
    [QuasiCompact q'] (c' : Compactification q')
    (h : c'.Z ⟶ (HasCompactification.compactification q).Z)
    (hi : IsPullback g' c'.i (HasCompactification.compactification q).i h)
    (hp : CommSq h c'.g (HasCompactification.compactification q).g g)
    (K : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap' (ModuleCat.{u + 1} A)
        (HasCompactification.compactification q) c' h hi hp).app K ≫
      (rightDerivedLowerShriekIso A c').hom.app (L((g')^*[ModuleCat.{u + 1} A]).obj K) ≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q').hom.app
        (L((g')^*[ModuleCat.{u + 1} A]).obj K) =
    L((g)^*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app K) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app K := by
  exact exchange_of_forget L((g)^*[ModuleCat.{u + 1} A]) _ _ _ _ _ _ _ _
    (proper_compactification_hom A q' c' (L((g')^*[ModuleCat.{u + 1} A]).obj K))
    (raw_exchange_combined A sq (HasCompactification.compactification q) c' h hi hp K)
    (proper_hom_app A q K)

private theorem replace_first
    {C : Type*} [Category C] {V₀ V₁ V₂ V₃ : C}
    (a : V₀ ⟶ V₂) (d : V₀ ⟶ V₁) (b : V₁ ⟶ V₂) (c : V₂ ⟶ V₃)
    (t : V₀ ⟶ V₃) (h : a = d ≫ b) (H : d ≫ b ≫ c = t) : a ≫ c = t := by
  rw [h, Category.assoc]
  exact H

private theorem proper_exchange_compactification
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' q' q g)
    [IsProper q] [IsProper q'] [HasCompactification q] [HasCompactification q']
    [QuasiCompact q'] (c' : Compactification q')
    (h : c'.Z ⟶ (HasCompactification.compactification q).Z)
    (hi : IsPullback g' c'.i (HasCompactification.compactification q).i h)
    (hp : CommSq h c'.g (HasCompactification.compactification q).g g)
    (K : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekBaseChangeMap' A (HasCompactification.compactification q)
        c' h hi hp).app K ≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q').hom.app
        (L((g')^*[ModuleCat.{u + 1} A]).obj K) =
    L((g)^*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app K) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app K := by
  exact replace_first
    ((rightDerivedLowerShriekBaseChangeMap' A (HasCompactification.compactification q)
      c' h hi hp).app K)
    ((rightDerivedLowerShriekOfCompactificationBaseChangeMap' (ModuleCat.{u + 1} A)
      (HasCompactification.compactification q) c' h hi hp).app K)
    ((rightDerivedLowerShriekIso A c').hom.app (L((g')^*[ModuleCat.{u + 1} A]).obj K))
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q').hom.app
      (L((g')^*[ModuleCat.{u + 1} A]).obj K))
    (L((g)^*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app K) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app K)
    (primed_exchange_app A (HasCompactification.compactification q) c' h hi hp K)
    (proper_exchange_raw A sq c' h hi hp K)

private theorem replace_arrow
    {C : Type*} [Category C] {V₀ V₁ V₂ : C}
    (a a' : V₀ ⟶ V₁) (c : V₁ ⟶ V₂) (t : V₀ ⟶ V₂)
    (h : a = a') (H : a' ≫ c = t) : a ≫ c = t := by
  rw [h]
  exact H

private theorem proper_exchange_raw_model
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' q' q g)
    [IsProper q] [IsProper q'] [HasCompactification q] [HasCompactification q']
    [QuasiCompact q'] (K : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekBaseChangeMap A sq).app K ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) q').hom.app (L((g')^*[ModuleCat.{u + 1} A]).obj K) =
      L((g)^*[ModuleCat.{u + 1} A]).map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar
            (ModuleCat.{u + 1} A) q).hom.app K) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app K := by
  have h₀ := NatTrans.congr_app (rightDerivedLowerShriekBaseChangeMap_eq A sq) K
  have H := proper_exchange_compactification A sq.toCommSq
    ((HasCompactification.compactification q).ofIsPullback sq)
    (pullback.fst (HasCompactification.compactification q).g g)
    ((HasCompactification.compactification q).isPullback_i_ofIsPullback sq)
    (IsPullback.of_hasPullback (HasCompactification.compactification q).g g).toCommSq K
  exact replace_arrow ((rightDerivedLowerShriekBaseChangeMap A sq).app K)
    ((rightDerivedLowerShriekBaseChangeMap' A (HasCompactification.compactification q)
      ((HasCompactification.compactification q).ofIsPullback sq)
      (pullback.fst (HasCompactification.compactification q).g g)
      ((HasCompactification.compactification q).isPullback_i_ofIsPullback sq)
      (IsPullback.of_hasPullback (HasCompactification.compactification q).g g).toCommSq).app K)
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q').hom.app
      (L((g')^*[ModuleCat.{u + 1} A]).obj K))
    (L((g)^*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app K) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app K) h₀ H

-- Convert category aliases before specializing the functors or their comparison maps.
private theorem proper_exchange_transport_raw
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' q' q g)
    [IsProper q] [IsProper q'] [HasCompactification q] [HasCompactification q']
    [QuasiCompact q']
    (F : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (G : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (H S : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (H' S' : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hF : F = L((g)^*[ModuleCat.{u + 1} A]))
    (hG : G = L((g')^*[ModuleCat.{u + 1} A]))
    (hH : H = R(q)_![ModuleCat.{u + 1} A])
    (hH' : H' = R(q')_![ModuleCat.{u + 1} A])
    (hS : S = R((q)_*[ModuleCat.{u + 1} A]))
    (hS' : S' = R((q')_*[ModuleCat.{u + 1} A]))
    (η : H ≅ S) (η' : H' ≅ S')
    (hη : HEq η (rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) q))
    (hη' : HEq η' (rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) q'))
    (β : H ⋙ F ⟶ G ⋙ H') (βs : S ⋙ F ⟶ G ⋙ S')
    (hb : HEq β (rightDerivedLowerShriekBaseChangeMap A sq))
    (hbs : HEq βs (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq))
    (K : DerivedCategoryModule A X) :
    β.app K ≫ η'.hom.app (G.obj K) = F.map (η.hom.app K) ≫ βs.app K := by
  subst F G H H' S S'
  have he := eq_of_heq hη
  have he' := eq_of_heq hη'
  have hb' := eq_of_heq hb
  have hbs' := eq_of_heq hbs
  subst η η' β βs
  exact proper_exchange_raw_model A sq K

private theorem proper_exchange_transport_ordinary
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' q' q g)
    [IsProper q] [IsProper q'] [HasCompactification q] [HasCompactification q']
    [QuasiCompact q']
    (F : DerivedCategoryModule A Y ⥤
      DerivedCategoryModule A Y') (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A X')
    (H S : DerivedCategoryModule A X ⥤
      DerivedCategoryModule A Y) (H' S' : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A Y')
    (hF : F = L((g)^*[ModuleCat.{u + 1} A]))
    (hG : G = L((g')^*[ModuleCat.{u + 1} A]))
    (hH : H = R(q)_![ModuleCat.{u + 1} A])
    (hH' : H' = R(q')_![ModuleCat.{u + 1} A])
    (hS : S = R((q)_*[ModuleCat.{u + 1} A]))
    (hS' : S' = R((q')_*[ModuleCat.{u + 1} A]))
    (η : H ≅ S) (η' : H' ≅ S')
    (hη : HEq η (rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) q))
    (hη' : HEq η' (rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) q'))
    (β : H ⋙ F ⟶ G ⋙ H') (βs : S ⋙ F ⟶ G ⋙ S')
    (hb : HEq β (rightDerivedLowerShriekBaseChangeMap A sq))
    (hbs : HEq βs (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq))
    (K : DerivedCategoryModule A X) :
    β.app K ≫ η'.hom.app (G.obj K) = F.map (η.hom.app K) ≫ βs.app K := by
  exact proper_exchange_transport_raw A sq F G H S H' S'
    hF hG hH hH' hS hS' η η' hη hη' β βs hb hbs K

private theorem proper_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' q' q g)
    [IsProper q] [IsProper q'] [HasCompactification q] [HasCompactification q']
    [QuasiCompact q'] (K : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekBaseChangeMap A sq).app K ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) q').hom.app ((ordinaryFinitePullback A g').obj K) =
      (ordinaryFinitePullback A g).map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar
            (ModuleCat.{u + 1} A) q).hom.app K) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app K := by
  exact proper_exchange_transport_ordinary A sq
    (ordinaryFinitePullback A g) (ordinaryFinitePullback A g')
    R(q)_![ModuleCat.{u + 1} A] R((q)_*[ModuleCat.{u + 1} A])
    R(q')_![ModuleCat.{u + 1} A] R((q')_*[ModuleCat.{u + 1} A])
    rfl rfl rfl rfl rfl rfl
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q)
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q')
    HEq.rfl HEq.rfl (rightDerivedLowerShriekBaseChangeMap A sq)
    (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq) HEq.rfl HEq.rfl K

end ProperComparisons

section DerivedComparisons

set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2 ordinaryFinitePullback._proof_3
  ordinaryFinitePullback._proof_4 ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8 ordinaryFinitePullback._proof_9
  ordinaryFinitePullback._proof_10 ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions

private lemma mate_ofNatIsoLeft
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂')
    (α : TwoSquare G L₁' L₂' H) :
    (mateEquiv (adj₁.ofNatIsoLeft e₁) (adj₂.ofNatIsoLeft e₂) α) =
      (mateEquiv adj₁ adj₂ ((α.whiskerRight e₂.hom).whiskerLeft e₁.inv)) := by
  ext K
  simp -implicitDefEqProofs [mateEquiv_apply, Adjunction.ofNatIsoLeft_unit,
    Adjunction.ofNatIsoLeft_counit, Category.assoc, ← Functor.map_comp]

private lemma mate_whiskerTop
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G G' : C ⥤ E} {H : D ⥤ F}
    (α : TwoSquare G' L₁ L₂ H) (γ : G ⟶ G') (K : D) :
    (mateEquiv adj₁ adj₂ (α.whiskerTop γ)).app K =
      γ.app (R₁.obj K) ≫ (mateEquiv adj₁ adj₂ α).app K := by
  simp -implicitDefEqProofs [mateEquiv, TwoSquare.whiskerTop]

private lemma mate_whiskerBottom
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G : C ⥤ E} {H H' : D ⥤ F}
    (α : TwoSquare G L₁ L₂ H) (δ : H ⟶ H') (K : D) :
    (mateEquiv adj₁ adj₂ (α.whiskerBottom δ)).app K =
      (mateEquiv adj₁ adj₂ α).app K ≫ R₂.map (δ.app K) := by
  simp -implicitDefEqProofs [mateEquiv, TwoSquare.whiskerBottom, ← Functor.map_comp, δ.naturality]

private lemma exact_exchange_transport
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (sq : CommSq g' f' f g) :
    Functor.whiskerLeft (rightDerivedLowerStar (ModuleCat.{u + 1} A) f)
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).inv ≫
      derivedBaseChangeMap (ModuleCat.{u + 1} A) sq ≫
      Functor.whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g').hom _ =
      exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq := by
  let B := ModuleCat.{u + 1} A
  let α := TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso B sq).hom
  have hs :
      ((((α.whiskerTop (leftDerivedUpperStarIsoMapDerivedCategory B g).hom).whiskerBottom
        (leftDerivedUpperStarIsoMapDerivedCategory B g').inv).whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory B f').hom).whiskerLeft
        (leftDerivedUpperStarIsoMapDerivedCategory B f).inv) =
      TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso B sq).hom := by
    ext M
    simp -implicitDefEqProofs only [α, TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
      TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app]
    simp -implicitDefEqProofs only [derivedSquareUpperStarIso, leftDerivedUpperStarComp,
      exactDerivedSquareUpperStarIso, squareUpperStarIso,
      Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
      leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Category.assoc,
      Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
      Iso.inv_hom_id_app_assoc]
    rw [← (upperStar B g').leftDerivedFunctorIsoMapDerivedCategory.inv.naturality]
  have hm := mate_ofNatIsoLeft
    (derivedUpperStarLowerStarAdjunction B f) (derivedUpperStarLowerStarAdjunction B f')
    (leftDerivedUpperStarIsoMapDerivedCategory B f)
    (leftDerivedUpperStarIsoMapDerivedCategory B f')
    ((α.whiskerTop (leftDerivedUpperStarIsoMapDerivedCategory B g).hom).whiskerBottom
      (leftDerivedUpperStarIsoMapDerivedCategory B g').inv)
  rw [← mapDerivedUpperStarLowerStarAdjunction_eq,
    ← mapDerivedUpperStarLowerStarAdjunction_eq, hs] at hm
  change _ = derivedBaseChangeMap B sq at hm
  rw [← hm]
  ext K
  simp -implicitDefEqProofs only [NatTrans.comp_app, Functor.whiskerLeft_app]
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, B, rightDerivedLowerStar]
  rw [mate_whiskerBottom, mate_whiskerTop]
  change _ = (mateEquiv (mapDerivedUpperStarLowerStarAdjunction B f)
    (mapDerivedUpperStarLowerStarAdjunction B f') α).app K
  dsimp only [B, rightDerivedLowerStar, Functor.comp_obj]
  simp -implicitDefEqProofs only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp -implicitDefEqProofs only [Iso.inv_hom_id_app_assoc]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private lemma line_projective_exchange (A : Type (u + 1)) [CommRing A]
    {S' S : Scheme.{u}} (g : S' ⟶ S) (M : DerivedCategoryModule A (ProjectiveLine S)) :
    ordinaryFiniteP1Exchange A g M =
      (derivedBaseChangeMap (ModuleCat.{u + 1} A)
        (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).toCommSq).app M := by
  have h := NatTrans.congr_app (exact_exchange_transport A
    (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).toCommSq) M
  simp -implicitDefEqProofs only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  rw [ordinaryFiniteP1Exchange, ← h]
  dsimp only [ordinaryFinitePushforward, rightDerivedLowerStar]
  simp -implicitDefEqProofs [Category.assoc, ← Functor.map_comp]

private theorem comp_hom
    (A : Type (u + 1)) [CommRing A] {X P Y : Scheme.{u}}
    (e : X ⟶ P) (p : P ⟶ Y) (q : X ⟶ Y) (w : e ≫ p = q) :
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e p ≪≫
      rightDerivedLowerStarCongr (ModuleCat.{u + 1} A) w).hom =
      rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) e p q w.symm := by
  subst q
  simp only [rightDerivedLowerStarCongr_refl, Iso.trans_refl]
  change conjugateEquiv
    ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).comp
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e))
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (e ≫ p))
    (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) e p) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm).hom = _
  exact (conjugateEquiv_leftDerivedUpperStarComp_hom (ModuleCat.{u + 1} A)
    e p (e ≫ p) rfl).symm

private theorem unit_coefficient_square
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) {G : C ⥤ E} {H : D ⥤ F}
    (s : G ⋙ L₂ ⟶ L₁ ⋙ H) (ex : R₁ ⋙ G ⟶ H ⋙ R₂)
    (hu : ∀ K, G.map (a₁.unit.app K) ≫ ex.app (L₁.obj K) =
      a₂.unit.app (G.obj K) ≫ R₂.map (s.app K))
    {K : C} {P : D} {K' : E} {P' : F}
    (a : L₁.obj K ⟶ P) (b : G.obj K ⟶ K') (c : H.obj P ⟶ P')
    (d : L₂.obj K' ⟶ P')
    (hc : s.app K ≫ H.map a ≫ c = L₂.map b ≫ d) :
    G.map (a₁.unit.app K ≫ R₁.map a) ≫
        ex.app P ≫ R₂.map c =
      b ≫ a₂.unit.app K' ≫ R₂.map d := by
  simp only [Functor.map_comp, Category.assoc]
  erw [(ex.naturality_assoc a)]
  erw [reassoc_of% hu K]
  change a₂.unit.app (G.obj K) ≫ R₂.map (s.app K) ≫ R₂.map (H.map a) ≫ R₂.map c = _
  simp only [← Functor.map_comp, hc]
  rw [Functor.map_comp]
  exact a₂.unit_naturality_assoc b (R₂.map d)

private theorem forward_pasting
    {C : Type*} [Category C] {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ : C}
    (a : O₀ ⟶ O₁) (k : O₁ ⟶ O₂) (x : O₂ ⟶ O₃) (y : O₃ ⟶ O₄)
    (ep₀ : O₀ ⟶ O₅) (ep₁ : O₁ ⟶ O₆) (u : O₅ ⟶ O₆)
    (v : O₆ ⟶ O₇) (w : O₇ ⟶ O₈) (kp : O₇ ⟶ O₃) (kl : O₈ ⟶ O₄)
    (h : O₅ ⟶ O₈) (hcomp : k ≫ x = ep₁ ≫ v ≫ kp)
    (hn : kp ≫ y = w ≫ kl) (he : a ≫ ep₁ = ep₀ ≫ u)
    (hu : u ≫ v ≫ w = h) :
    (a ≫ k) ≫ x ≫ y = ep₀ ≫ h ≫ kl := by
  simp only [Category.assoc]
  rw [reassoc_of% hcomp, hn, reassoc_of% he, reassoc_of% hu]

private theorem inverse_transport
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {M L : C} {M' L' P : D} (j : M ≅ L) (j' : M' ≅ L')
    (x : F.obj L ⟶ P) (y : P ⟶ L') (z : F.obj M ⟶ M')
    (h : F.map j.hom ≫ x ≫ y = z ≫ j'.hom) :
    x ≫ y ≫ j'.inv = F.map j.inv ≫ z := by
  apply (cancel_epi (F.map j.hom)).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id]
  rw [reassoc_of% h, Iso.hom_inv_id, Category.comp_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

private theorem coefficient_exchange_transport
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    (R : D ⥤ C) (P : C ⥤ E) (Q : D ⥤ E)
    (R' : D' ⥤ C') (P' : C' ⥤ E') (Q' : D' ⥤ E')
    (F : E ⥤ E') (H : C ⥤ C') (J : D ⥤ D')
    (k : R ⋙ P ≅ Q) (k' : R' ⋙ P' ≅ Q')
    (ex : Q ⋙ F ⟶ J ⋙ Q') (ep : P ⋙ F ⟶ H ⋙ P') (ee : R ⋙ H ⟶ J ⋙ R')
    {M : C} {M' : C'} {L : D} {L' : D'}
    (b : M ≅ R.obj L) (b' : M' ≅ R'.obj L') (l : J.obj L ≅ L')
    (m : H.obj M ≅ M') (j : P.obj M ≅ Q.obj L) (j' : P'.obj M' ≅ Q'.obj L')
    (hc : F.map (k.hom.app L) ≫ ex.app L =
      ep.app (R.obj L) ≫ P'.map (ee.app L) ≫ k'.hom.app (J.obj L))
    (hu : H.map b.hom ≫ ee.app L ≫ R'.map l.hom = m.hom ≫ b'.hom)
    (hj : j.hom = P.map b.hom ≫ k.hom.app L)
    (hj' : j'.hom = P'.map b'.hom ≫ k'.hom.app L') :
    ex.app L ≫ Q'.map l.hom ≫ j'.inv = F.map j.inv ≫ ep.app M ≫ P'.map m.hom := by
  have hf := forward_pasting
    (F.map (P.map b.hom)) (F.map (k.hom.app L)) (ex.app L) (Q'.map l.hom)
    (ep.app M) (ep.app (R.obj L)) (P'.map (H.map b.hom)) (P'.map (ee.app L))
    (P'.map (R'.map l.hom)) (k'.hom.app (J.obj L)) (k'.hom.app L')
    (P'.map (m.hom ≫ b'.hom)) hc (k'.hom.naturality l.hom).symm
    (ep.naturality b.hom)
    (by simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using P'.congr_map hu)
  apply inverse_transport F j j'
  rw [hj, hj']
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using hf

@[irreducible] private noncomputable def presentationCoefficient
    (A : Type (u + 1)) [CommRing A] {X P : Scheme.{u}} (e : X ≅ P)
    (M : DerivedCategoryModule A P) (L : DerivedCategoryModule A X)
    (c : (ordinaryFinitePullback A e.hom).obj M ≅ L) :
    M ≅ (ordinaryFinitePushforward A e.hom).obj L :=
  asIso ((derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} A) e.hom).unit.app M) ≪≫
    (ordinaryFinitePushforward A e.hom).mapIso c

private theorem presentationCoefficient_hom
    (A : Type (u + 1)) [CommRing A] {X P : Scheme.{u}} (e : X ≅ P)
    (M : DerivedCategoryModule A P) (L : DerivedCategoryModule A X)
    (c : (ordinaryFinitePullback A e.hom).obj M ≅ L) :
    (presentationCoefficient A e M L c).hom =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e.hom).unit.app M ≫
        (ordinaryFinitePushforward A e.hom).map c.hom := by
  rw [presentationCoefficient]
  rfl

@[irreducible] private noncomputable def presentationCompositor
    (A : Type (u + 1)) [CommRing A] {X P Y : Scheme.{u}}
    (q : X ⟶ Y) (p : P ⟶ Y) (e : X ≅ P) (w : e.hom ≫ p = q) :
    ordinaryFinitePushforward A e.hom ⋙ ordinaryFinitePushforward A p ≅
      ordinaryFinitePushforward A q :=
  rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.hom p ≪≫
    rightDerivedLowerStarCongr (ModuleCat.{u + 1} A) w

private theorem presentationCompositor_hom
    (A : Type (u + 1)) [CommRing A] {X P Y : Scheme.{u}}
    (q : X ⟶ Y) (p : P ⟶ Y) (e : X ≅ P) (w : e.hom ≫ p = q) :
    (presentationCompositor A q p e w).hom =
      rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) e.hom p q w.symm := by
  rw [presentationCompositor]
  exact comp_hom A e.hom p q w

@[irreducible] private noncomputable def presentationComparison
    (A : Type (u + 1)) [CommRing A]
    {X P Y : Scheme.{u}} (q : X ⟶ Y) (p : P ⟶ Y) (e : X ≅ P)
    (w : e.hom ≫ p = q) (M : DerivedCategoryModule A P)
    (L : DerivedCategoryModule A X) (c : (ordinaryFinitePullback A e.hom).obj M ≅ L) :
    (ordinaryFinitePushforward A p).obj M ≅ (ordinaryFinitePushforward A q).obj L :=
  (ordinaryFinitePushforward A p).mapIso (presentationCoefficient A e M L c) ≪≫
    (presentationCompositor A q p e w).app L

private theorem map_iso_trans_hom
    {C D E : Type*} [Category C] [Category D] [Category E]
    (R : C ⥤ D) (P : D ⥤ E) (Q : C ⥤ E) (k : R ⋙ P ≅ Q)
    {M : D} {L : C} (b : M ≅ R.obj L) :
    (P.mapIso b ≪≫ k.app L).hom = P.map b.hom ≫ k.hom.app L := rfl

private theorem presentationComparison_hom
    (A : Type (u + 1)) [CommRing A]
    {X P Y : Scheme.{u}} (q : X ⟶ Y) (p : P ⟶ Y) (e : X ≅ P)
    (w : e.hom ≫ p = q) (M : DerivedCategoryModule A P)
    (L : DerivedCategoryModule A X) (c : (ordinaryFinitePullback A e.hom).obj M ≅ L) :
    (presentationComparison A q p e w M L c).hom =
      (ordinaryFinitePushforward A p).map (presentationCoefficient A e M L c).hom ≫
        (presentationCompositor A q p e w).hom.app L := by
  simpa only [presentationComparison] using
    map_iso_trans_hom (ordinaryFinitePushforward A e.hom)
      (ordinaryFinitePushforward A p) (ordinaryFinitePushforward A q)
      (presentationCompositor A q p e w) (presentationCoefficient A e M L c)

private theorem presentation_pasting
    (A : Type (u + 1)) [CommRing A]
    {X X' P P' Y Y' : Scheme.{u}}
    {q : X ⟶ Y} {q' : X' ⟶ Y'} {p : P ⟶ Y} {p' : P' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} {h : P' ⟶ P}
    (sq : CommSq g' q' q g) (sp : CommSq h p' p g)
    [IsProper p] [IsProper p']
    (e : X ≅ P) (w : e.hom ≫ p = q)
    (e' : X' ≅ P') (w' : e'.hom ≫ p' = q')
    (we : g' ≫ e.hom = e'.hom ≫ h)
    (L : DerivedCategoryModule A X) :
    (ordinaryFinitePullback A g).map
        ((presentationCompositor A q p e w).hom.app L) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app L =
    (derivedBaseChangeMap (ModuleCat.{u + 1} A) sp).app
        ((ordinaryFinitePushforward A e.hom).obj L) ≫
      (ordinaryFinitePushforward A p').map
        ((derivedBaseChangeMap (ModuleCat.{u + 1} A) (CommSq.mk we)).app L) ≫
      (presentationCompositor A q' p' e' w').hom.app
        ((ordinaryFinitePullback A g').obj L) := by
  rw [presentationCompositor_hom, presentationCompositor_hom]
  exact map_rightDerivedLowerStarCompHom_derivedBaseChangeMap
    (ModuleCat.{u + 1} A) sq
    ⟨P, p, e.hom, w.symm, inferInstance, inferInstance⟩
    ⟨P', p', e'.hom, w'.symm, inferInstance, inferInstance⟩
    h (IsPullback.of_vert_isIso ⟨we⟩) sp L

private theorem presentation_exchange
    (A : Type (u + 1)) [CommRing A]
    {X X' P P' Y Y' : Scheme.{u}}
    {q : X ⟶ Y} {q' : X' ⟶ Y'} {p : P ⟶ Y} {p' : P' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} {h : P' ⟶ P}
    (sq : CommSq g' q' q g) (sp : CommSq h p' p g)
    [IsProper p] [IsProper p']
    (e : X ≅ P) (w : e.hom ≫ p = q)
    (e' : X' ≅ P') (w' : e'.hom ≫ p' = q')
    (we : g' ≫ e.hom = e'.hom ≫ h)
    (M : DerivedCategoryModule A P) (M' : DerivedCategoryModule A P')
    (L : DerivedCategoryModule A X) (L' : DerivedCategoryModule A X')
    (c : (ordinaryFinitePullback A e.hom).obj M ≅ L)
    (c' : (ordinaryFinitePullback A e'.hom).obj M' ≅ L')
    (l : (ordinaryFinitePullback A g').obj L ≅ L')
    (m : (ordinaryFinitePullback A h).obj M ≅ M')
    (hc : (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) (CommSq.mk we)).hom.app M ≫
      (ordinaryFinitePullback A g').map c.hom ≫ l.hom =
      (ordinaryFinitePullback A e'.hom).map m.hom ≫ c'.hom) :
    (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app L ≫
      (ordinaryFinitePushforward A q').map l.hom ≫
      (presentationComparison A q' p' e' w' M' L' c').inv =
    (ordinaryFinitePullback A g).map (presentationComparison A q p e w M L c).inv ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sp).app M ≫
      (ordinaryFinitePushforward A p').map m.hom := by
  let se : IsPullback g' e'.hom e.hom h := IsPullback.of_vert_isIso ⟨we⟩
  have hcomp := presentation_pasting A sq sp e w e' w' we L
  let b := presentationCoefficient A e M L c
  let b' := presentationCoefficient A e' M' L' c'
  let k := presentationCompositor A q p e w
  let k' := presentationCompositor A q' p' e' w'
  have hunit : (ordinaryFinitePullback A h).map b.hom ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) se.toCommSq).app L ≫
      (ordinaryFinitePushforward A e'.hom).map l.hom = m.hom ≫ b'.hom := by
    dsimp only [b, b']
    rw [presentationCoefficient_hom, presentationCoefficient_hom]
    exact unit_coefficient_square
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e.hom)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e'.hom)
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) se.toCommSq).hom
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) se.toCommSq)
      (map_unit_derivedBaseChangeMap_app (ModuleCat.{u + 1} A) se.toCommSq)
      c.hom m.hom l.hom c'.hom hc
  exact coefficient_exchange_transport
    (ordinaryFinitePushforward A e.hom) (ordinaryFinitePushforward A p)
    (ordinaryFinitePushforward A q) (ordinaryFinitePushforward A e'.hom)
    (ordinaryFinitePushforward A p') (ordinaryFinitePushforward A q')
    (ordinaryFinitePullback A g) (ordinaryFinitePullback A h) (ordinaryFinitePullback A g')
    k k' (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq)
    (derivedBaseChangeMap (ModuleCat.{u + 1} A) sp)
    (derivedBaseChangeMap (ModuleCat.{u + 1} A) se.toCommSq)
    b b' l m (presentationComparison A q p e w M L c)
    (presentationComparison A q' p' e' w' M' L' c') hcomp hunit
    (presentationComparison_hom A q p e w M L c)
    (presentationComparison_hom A q' p' e' w' M' L' c')

private theorem cancel_coincidence
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {K K' : C} {O₀ O₁ O₂ O₃ : D} (i : K ≅ K')
    (b : F.obj K ⟶ O₀) (c : O₀ ⟶ O₁) (d : O₁ ⟶ O₂)
    (j : O₀ ⟶ O₃) (v : O₃ ⟶ O₂) (β : F.obj K' ⟶ O₃)
    (hn : c ≫ d = j ≫ v) (hb : b ≫ j = F.map i.hom ≫ β) :
    F.map i.inv ≫ b ≫ c ≫ d = β ≫ v := by
  rw [hn, reassoc_of% hb, ← F.map_comp_assoc, i.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

private theorem proper_coefficient_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' q' q g)
    [IsProper q] [IsProper q'] [HasCompactification q] [HasCompactification q']
    [QuasiCompact q'] (L : DerivedCategoryModule A X) (L' : DerivedCategoryModule A X')
    (l : (ordinaryFinitePullback A g').obj L ≅ L') :
    (ordinaryFinitePullback A g).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) q).inv.app L) ≫
      (rightDerivedLowerShriekBaseChangeMap A sq).app L ≫
      (R(q')_![ModuleCat.{u + 1} A]).map l.hom ≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} A) q').hom.app L' =
    (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app L ≫
      (ordinaryFinitePushforward A q').map l.hom := by
  exact cancel_coincidence (ordinaryFinitePullback A g)
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).app L)
    ((rightDerivedLowerShriekBaseChangeMap A sq).app L)
    ((R(q')_![ModuleCat.{u + 1} A]).map l.hom)
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) q').hom.app L')
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) q').hom.app ((ordinaryFinitePullback A g').obj L))
    ((ordinaryFinitePushforward A q').map l.hom)
    ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app L)
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) q').hom.naturality l.hom)
    (proper_exchange A sq L)

private theorem regroup_presentation
    {C : Type*} [Category C] {O₀ O₁ O₂ O₃ O₄ O₅ : C}
    (a : O₀ ⟶ O₁) (b : O₁ ⟶ O₂) (c : O₂ ⟶ O₃)
    (d : O₀ ⟶ O₄) (e : O₄ ⟶ O₅) (f : O₅ ⟶ O₃)
    (h : a ≫ b ≫ c = d ≫ e ≫ f) :
    (a ≫ b) ≫ c = d ≫ (e ≫ f) := by
  simpa only [Category.assoc] using h

private theorem append_trace_exchange
    {C : Type*} [Category C] {O₀ O₁ O₂ O₃ O₄ O₅ O₆ : C}
    (a : O₀ ⟶ O₁) (b : O₁ ⟶ O₂) (c : O₂ ⟶ O₃) (d : O₃ ⟶ O₄)
    (e : O₀ ⟶ O₅) (f : O₅ ⟶ O₄) (τ : O₄ ⟶ O₆) (r : O₀ ⟶ O₆)
    (he : a ≫ b ≫ c ≫ d = e ≫ f) (ht : (e ≫ f) ≫ τ = r) :
    a ≫ b ≫ c ≫ d ≫ τ = r := by
  simpa only [Category.assoc] using (congrArg (fun z ↦ z ≫ τ) he).trans ht

attribute [local irreducible] ArbitraryBaseFiniteP1Splitting.trace
  ordinaryFiniteShiftedLinePullback

private theorem map_iso_trans_trace
    {C D E : Type*} [Category C] [Category D] [Category E]
    (R : C ⥤ D) (P : D ⥤ E) (Q : C ⥤ E)
    {T : C ⥤ E} (u : R ⋙ P ≅ T) (v : T ≅ Q)
    {M : D} {L : C} {U : E} (b : M ≅ R.obj L) (τ : P.obj M ⟶ U) :
    v.inv.app L ≫ u.inv.app L ≫ P.map b.inv ≫ τ =
      (P.mapIso b ≪≫ (u ≪≫ v).app L).inv ≫ τ := by
  change _ = ((v.inv.app L ≫ u.inv.app L) ≫ P.map b.inv) ≫ τ
  simp only [Category.assoc]

private theorem trace_model
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (q : X ⟶ Y) (e : X ≅ ProjectiveLine Y)
    (w : e.hom ≫ (ProjectiveLine Y ↘ Y) = q) (hY : IsUnit (N : Γ(Y, ⊤)))
    (d : ArbitraryBaseFiniteP1Splitting A N hA t Y hY) :
    presentedFiniteP1Trace A N hA t q e w hY d =
      (presentationComparison A q (ProjectiveLine Y ↘ Y) e w
        ((ordinaryFiniteLine A N hA (ProjectiveLine Y))⟦(2 : ℤ)⟧)
        ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)
        (ordinaryFiniteShiftedLinePullback A N hA t e.hom
          (finiteP1_unitOnPullback N (ProjectiveLine Y ↘ Y) hY))).inv ≫ d.trace := by
  subst q
  unfold presentedFiniteP1Trace presentationComparison presentationCoefficient
    presentationCompositor
  exact map_iso_trans_trace (ordinaryFinitePushforward A e.hom)
    (ordinaryFinitePushforward A (ProjectiveLine Y ↘ Y))
    (ordinaryFinitePushforward A (e.hom ≫ (ProjectiveLine Y ↘ Y)))
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.hom (ProjectiveLine Y ↘ Y))
    (rightDerivedLowerStarCongr (ModuleCat.{u + 1} A) rfl)
    (asIso ((derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} A) e.hom).unit.app
        ((ordinaryFiniteLine A N hA (ProjectiveLine Y))⟦(2 : ℤ)⟧)) ≪≫
      (ordinaryFinitePushforward A e.hom).mapIso
        (ordinaryFiniteShiftedLinePullback A N hA t e.hom
          (finiteP1_unitOnPullback N (ProjectiveLine Y ↘ Y) hY))) d.trace

private theorem transport_trace
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {M L U : C} {M' L' U' : D} (j : M ≅ L) (j' : M' ≅ L')
    (E : F.obj L ⟶ L') (E₀ : F.obj M ⟶ M')
    (τ : M ⟶ U) (τ' : M' ⟶ U') (u : F.obj U ⟶ U')
    (tr : L ⟶ U) (tr' : L' ⟶ U')
    (he : E ≫ j'.inv = F.map j.inv ≫ E₀)
    (hb : E₀ ≫ τ' = F.map τ ≫ u)
    (ht : tr = j.inv ≫ τ) (ht' : tr' = j'.inv ≫ τ') :
    E ≫ tr' = F.map tr ≫ u := by
  rw [ht, ht', ← Category.assoc, he]
  simp only [Functor.map_comp, Category.assoc]
  rw [hb]

/-- The transported coefficient trace commutes with compact-support exchange.
Source: blueprint prop-asd-smooth-base-change.proof.md, second paragraph, trace square;
thm-amb-p1-adjunction.proof.md, transport between projective-line presentations.
(auxiliary; not a blueprint node)

Proof: take the second clause of hbc g hY hY' for the standard projective lines.
It is the trace square for ordinaryFiniteP1Exchange followed by the normalized
shifted-line comparison. The two presentation isomorphisms give a map between this
standard square and sq; we is precisely its horizontal commutativity condition.
Expand presentedFiniteP1Trace on both sides. Exchange pasting moves the direct-image
composition comparisons through the square. The mate unit identity moves the
adjunction unit of e through exchange to the adjunction unit of e'. The normalized
finite-line pullback comparisons respect composition (their roots and pure tensor
normalizations characterize them uniquely), so the remaining line comparison is
the one along g'. Cancel the presentation units, which are isomorphisms. Finally
proper coincidence identifies compact-support exchange with ordinary proper
exchange: the unbounded compactification exchange commutes with forgetting supports,
and the compactification comparison isomorphism preserves that forget-supports map.
This gives the displayed coefficient equation. No arbitrary complex K,
projection formula, tensor trace, counit, or exceptional inverse image enters.
Identity pullback, zero coefficients, N=1 and empty bases use the same equations. -/
theorem presentedFiniteP1Trace_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t T hT)
    (hbc : ArbitraryBaseFiniteP1BaseChange A N hA t d)
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' q' q g)
    [IsProper q] [IsProper q'] [HasCompactification q] [HasCompactification q']
    [QuasiCompact q']
    (e : X ≅ ProjectiveLine Y) (w : e.hom ≫ (ProjectiveLine Y ↘ Y) = q)
    (e' : X' ≅ ProjectiveLine Y') (w' : e'.hom ≫ (ProjectiveLine Y' ↘ Y') = q')
    (we : e'.hom ≫ ProjectiveSpace.map (ULift.{u} (Fin 2)) g = g' ≫ e.hom)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hY' : IsUnit (N : Γ(Y', ⊤))) :
    let L := (ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧
    let L' := (ordinaryFiniteLine A N hA X')⟦(2 : ℤ)⟧
    let l := ordinaryFiniteShiftedLinePullback A N hA t g'
      (finiteP1_unitOnPullback N q hY)
    (ordinaryFinitePullback A g).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) q).inv.app L) ≫
      (rightDerivedLowerShriekBaseChangeMap A sq).app L ≫
      (R(q')_![ModuleCat.{u + 1} A]).map l.hom ≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} A) q').hom.app L' ≫
      presentedFiniteP1Trace A N hA t q' e' w' hY' (d Y' hY') =
    (ordinaryFinitePullback A g).map
        (presentedFiniteP1Trace A N hA t q e w hY (d Y hY)) ≫
      (ordinaryFiniteUnitPullback A g).hom := by
  let M := (ordinaryFiniteLine A N hA (ProjectiveLine Y))⟦(2 : ℤ)⟧
  let M' := (ordinaryFiniteLine A N hA (ProjectiveLine Y'))⟦(2 : ℤ)⟧
  let L := (ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧
  let L' := (ordinaryFiniteLine A N hA X')⟦(2 : ℤ)⟧
  let hP := finiteP1_unitOnPullback N (ProjectiveLine Y ↘ Y) hY
  let hP' := finiteP1_unitOnPullback N (ProjectiveLine Y' ↘ Y') hY'
  let c := ordinaryFiniteShiftedLinePullback A N hA t e.hom hP
  let c' := ordinaryFiniteShiftedLinePullback A N hA t e'.hom hP'
  let l := ordinaryFiniteShiftedLinePullback A N hA t g' (finiteP1_unitOnPullback N q hY)
  let m := ordinaryFiniteShiftedLinePullback A N hA t
    (ProjectiveSpace.map (ULift.{u} (Fin 2)) g) hP
  let sp := (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).toCommSq
  have hc := ordinaryFiniteShiftedLinePullback_square A N hA t (CommSq.mk we.symm)
    hP hP' (finiteP1_unitOnPullback N q hY)
  have hp := presentation_exchange A sq.toCommSq sp e w e' w' we.symm
    M M' L L' c c' l m hc
  have hb₀ := (hbc g hY hY').2.symm
  have hb := ((congrArg (fun z ↦
    (z ≫ (ordinaryFinitePushforward A (ProjectiveLine Y' ↘ Y')).map m.hom) ≫
      (d Y' hY').trace) (line_projective_exchange A g M)).symm).trans hb₀
  have he := proper_coefficient_exchange A sq L L' l
  have ht := transport_trace (ordinaryFinitePullback A g)
    (presentationComparison A q (ProjectiveLine Y ↘ Y) e w M L c)
    (presentationComparison A q' (ProjectiveLine Y' ↘ Y') e' w' M' L' c')
    ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app L ≫
      (ordinaryFinitePushforward A q').map l.hom)
    ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sp).app M ≫
      (ordinaryFinitePushforward A (ProjectiveLine Y' ↘ Y')).map m.hom)
    (d Y hY).trace (d Y' hY').trace (ordinaryFiniteUnitPullback A g).hom
    (presentedFiniteP1Trace A N hA t q e w hY (d Y hY))
    (presentedFiniteP1Trace A N hA t q' e' w' hY' (d Y' hY'))
    (regroup_presentation
      ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app L)
      ((ordinaryFinitePushforward A q').map l.hom)
      (presentationComparison A q' (ProjectiveLine Y' ↘ Y') e' w' M' L' c').inv
      ((ordinaryFinitePullback A g).map
        (presentationComparison A q (ProjectiveLine Y ↘ Y) e w M L c).inv)
      ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sp).app M)
      ((ordinaryFinitePushforward A (ProjectiveLine Y' ↘ Y')).map m.hom) hp) hb
    (trace_model A N hA t q e w hY (d Y hY))
    (trace_model A N hA t q' e' w' hY' (d Y' hY'))
  exact append_trace_exchange
    ((ordinaryFinitePullback A g).map
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} A) q).inv.app L))
    ((rightDerivedLowerShriekBaseChangeMap A sq).app L)
    ((R(q')_![ModuleCat.{u + 1} A]).map l.hom)
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) q').hom.app L')
    ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app L)
    ((ordinaryFinitePushforward A q').map l.hom)
    (presentedFiniteP1Trace A N hA t q' e' w' hY' (d Y' hY'))
    ((ordinaryFinitePullback A g).map
      (presentedFiniteP1Trace A N hA t q e w hY (d Y hY)) ≫
      (ordinaryFiniteUnitPullback A g).hom) he ht

end DerivedComparisons
end AlgebraicGeometry.Etale

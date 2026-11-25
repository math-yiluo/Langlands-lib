/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.CompactProjectionExchange
import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionProper
/-! # Ordered proper projection and compact-support exchange -/

@[expose] public section
set_option autoImplicit false
-- Keep local functor aliases out of the component comparisons to avoid expensive unfolding.
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local instance high] SymmetricCategory.toBraidedCategory

attribute [local instance 20000] Etale.sheafBraidedCategory

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
  Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedTensor
  rightDerivedLowerShriekBaseChangeMap rightDerivedLowerShriekIsoRightDerivedLowerStar
  derivedTensorSymmetry compactProjectionMapCoeffFirst ordinaryFiniteProjection

attribute [local implicit_reducible] rightDerivedLowerShriek
  derivedTensorRightDerivedLowerShriek rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerStar rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
  ordinaryFiniteTwistedPullback derivedTensorRight

private theorem inverseSquare
    {C : Type*} [Category C] {O₀ O₁ O₂ O₃ : C}
    (a : O₀ ≅ O₁) (b : O₂ ≅ O₃) (p : O₀ ⟶ O₂) (r : O₁ ⟶ O₃)
    (h : p ≫ b.hom = a.hom ≫ r) : r ≫ b.inv = a.inv ≫ p := by
  apply (cancel_mono b.hom).1
  simp -implicitDefEqProofs only [Category.assoc, b.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

private theorem naturalityPasting
    {C : Type*} [Category C] {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ : C}
    (a : O₀ ⟶ O₁) (s' : O₁ ⟶ O₂) (s : O₀ ⟶ O₃) (b : O₃ ⟶ O₂)
    (p' : O₂ ⟶ O₄) (p : O₃ ⟶ O₅) (d : O₅ ⟶ O₄)
    (t' : O₄ ⟶ O₆) (t : O₅ ⟶ O₇) (e : O₇ ⟶ O₆)
    (hs : a ≫ s' = s ≫ b) (hp : b ≫ p' = p ≫ d)
    (ht : d ≫ t' = t ≫ e) :
    a ≫ s' ≫ p' ≫ t' = (s ≫ p ≫ t) ≫ e := by
  simp -implicitDefEqProofs only [Category.assoc]
  rw [reassoc_of% hs, reassoc_of% hp, ht]

private theorem mapSquare
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {O₀ O₁ O₂ O₃ : C} {a : O₀ ⟶ O₁} {b : O₁ ⟶ O₃}
    {c : O₀ ⟶ O₂} {d : O₂ ⟶ O₃} (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d :=
  (F.map_comp a b).symm.trans ((F.congr_map h).trans (F.map_comp c d))

private theorem forwardExchange
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (R : E ⥤ D) (T : D ⥤ D)
    {c₀ c₁ c₂ : C} {x₀ x₁ x₂ x₃ : E} {d₀ d₁ d₂ d₃ d₄ : D}
    {a : c₀ ⟶ c₁} {p : c₁ ⟶ c₂} {P : c₀ ⟶ c₂}
    {B : F.obj c₂ ⟶ R.obj x₀} {u : x₀ ⟶ x₁} {s : x₁ ⟶ x₂}
    {v : x₂ ⟶ x₃} {a₀ : F.obj c₁ ⟶ T.obj d₀}
    {a₁ : F.obj c₀ ⟶ T.obj d₄} {f : d₄ ⟶ d₀}
    {b : d₀ ⟶ d₁} {j : d₁ ⟶ d₂} (i : d₂ ⟶ d₃) (i' : d₃ ⟶ d₂)
    (hi : i ≫ i' = 𝟙 d₂)
    {p₀ : T.obj d₁ ⟶ R.obj x₂} {p₁ : T.obj d₂ ⟶ R.obj x₃}
    {P₁ : T.obj d₃ ⟶ R.obj x₃}
    (hP : P = a ≫ p) (hP₁ : P₁ = T.map i' ≫ p₁)
    (hp : F.map p ≫ B ≫ R.map u ≫ R.map s = a₀ ≫ T.map b ≫ p₀)
    (hn : T.map j ≫ p₁ = p₀ ≫ R.map v)
    (ht : F.map a ≫ a₀ = a₁ ≫ T.map f) :
    F.map P ≫ B ≫ R.map (u ≫ s ≫ v) =
      a₁ ≫ T.map (f ≫ b ≫ j ≫ i) ≫ P₁ := by
  simp -implicitDefEqProofs only [hP, hP₁, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hp, ← hn, reassoc_of% ht]
  have hmap : T.map i ≫ T.map i' = 𝟙 (T.obj _) :=
    (T.map_comp i i').symm.trans ((T.congr_map hi).trans (T.map_id _))
  rw [reassoc_of% hmap]

private theorem coincidenceSquare
    {C : Type*} [Category C] {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ : C}
    {s : O₀ ⟶ O₁} {p : O₁ ⟶ O₂} {t : O₂ ⟶ O₃} {c : O₃ ⟶ O₄}
    {d : O₂ ⟶ O₅} {t' : O₅ ⟶ O₄} {m : O₁ ⟶ O₆} {p' : O₆ ⟶ O₅}
    {a : O₀ ⟶ O₇} {s' : O₇ ⟶ O₆}
    (hn : t ≫ c = d ≫ t') (hp : p ≫ d = m ≫ p') (hs : s ≫ m = a ≫ s') :
    (s ≫ p ≫ t) ≫ c = a ≫ (s' ≫ p' ≫ t') := by
  simp -implicitDefEqProofs only [Category.assoc]
  rw [hn, reassoc_of% hp, reassoc_of% hs]

private theorem projectionCoincidenceRaw
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q] [HasCompactification q]
    (K : DerivedCategoryModule A Y) (L : DerivedCategoryModule A X) :
    ((projectionMap (ModuleCat.{u + 1} A) q).app L).app K ≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj L).obj
          ((ordinaryFinitePullback A q).obj K)) =
    ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) q).hom.app L)).app K ≫
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app L).app K := by
  have h : (rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) q).hom =
      compactificationForgetSupports (ModuleCat.{u + 1} A)
        (HasCompactification.compactification q) := by
    rw [rightDerivedLowerShriekIsoRightDerivedLowerStar_hom,
      rightDerivedLowerShriekToLowerStarComp_comp_eq]
    rfl
  rw [h]
  exact projectionMapOfCompactification_comp_compactificationForgetSupports
    (ModuleCat.{u + 1} A) (HasCompactification.compactification q) L K

private theorem orderedProjection_coincidence
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q] [HasCompactification q]
    (K : DerivedCategoryModule A Y) (L : DerivedCategoryModule A X) :
    let C := rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q
    compactProjectionMapCoeffFirst A q K L ≫
        C.hom.app ((ordinaryFiniteTwistedPullback A q L).obj K) =
      ((ordinaryFiniteTensor A Y).obj K).map (C.hom.app L) ≫
        ordinaryFiniteProjection A q L K := by
  let sx : ((derivedTensor (ModuleCat.{u + 1} A) X).obj L).obj
      ((ordinaryFinitePullback A q).obj K) ⟶
      (ordinaryFiniteTwistedPullback A q L).obj K :=
    ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app L).app
      ((ordinaryFinitePullback A q).obj K)
  unfold compactProjectionMapCoeffFirst ordinaryFiniteProjection
  exact coincidenceSquare
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) q).hom.naturality sx)
    (projectionCoincidenceRaw A q K L)
    (((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app K).naturality
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} A) q).hom.app L)).symm

private theorem orderedProjection_inv_coincidence
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q] [HasCompactification q]
    (K : DerivedCategoryModule A Y) (L : DerivedCategoryModule A X) :
    let C := rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q
    ordinaryFiniteProjection A q L K ≫
        C.inv.app ((ordinaryFiniteTwistedPullback A q L).obj K) =
      ((ordinaryFiniteTensor A Y).obj K).map (C.inv.app L) ≫
        compactProjectionMapCoeffFirst A q K L := by
  simp -implicitDefEqProofs only [ordinaryFinitePullback, ordinaryFiniteTensor,
    ordinaryFinitePushforward,
    ordinaryFiniteTwistedPullback, derivedTensorRight, Functor.comp_obj,
    Functor.flip_obj_obj] at *
  exact inverseSquare
    (((ordinaryFiniteTensor A Y).obj K).mapIso
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} A) q).app L))
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) q).app ((ordinaryFiniteTwistedPullback A q L).obj K))
    (compactProjectionMapCoeffFirst A q K L) (ordinaryFiniteProjection A q L K)
    (orderedProjection_coincidence A q K L)

private theorem compactProjection_coefficient_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q] [HasCompactification q]
    (K : DerivedCategoryModule A Y) {L L' : DerivedCategoryModule A X} (l : L ⟶ L') :
    ((ordinaryFiniteTensor A Y).obj K).map ((R(q)_![ModuleCat.{u + 1} A]).map l) ≫
        compactProjectionMapCoeffFirst A q K L' =
      compactProjectionMapCoeffFirst A q K L ≫
        (R(q)_![ModuleCat.{u + 1} A]).map
          (((ordinaryFiniteTensor A X).obj ((ordinaryFinitePullback A q).obj K)).map l) := by
  have hs := ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app K).naturality
    ((R(q)_![ModuleCat.{u + 1} A]).map l)
  have hp := NatTrans.congr_app ((projectionMap (ModuleCat.{u + 1} A) q).naturality l) K
  have ht := NatTrans.congr_app
    ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.naturality l)
    ((ordinaryFinitePullback A q).obj K)
  simp -implicitDefEqProofs only [ordinaryFinitePullback, ordinaryFiniteTensor,
    Functor.flip_obj_obj,
    Functor.flip_obj_map] at *
  simp -implicitDefEqProofs only [derivedTensorRightDerivedLowerShriek,
    rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar, Functor.comp_map] at hp
  unfold compactProjectionMapCoeffFirst
  simp -implicitDefEqProofs only [rightDerivedLowerShriek] at *
  simp -implicitDefEqProofs only [derivedTensorRightDerivedLowerShriek,
    rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar, Functor.comp_obj,
    Functor.comp_map] at *
  simp -implicitDefEqProofs only [NatTrans.comp_app] at hp
  exact naturalityPasting _ _ _ _ _ _ _ _ _ _ hs hp
    (mapSquare (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (HasCompactification.compactification q)) ht)

/-- The forward ordered projection square with an arbitrary source coefficient.
Source: blueprint prop-asd-smooth-base-change.proof.md, second paragraph, projection square;
Stacks, Tag 0E48, compatibility with a diagram.
(auxiliary; not a blueprint node)
Proof: the compact-support projection square is
projectionMap_rightDerivedLowerShriekBaseChangeMap. Conjugate its source and target
by tensor symmetry to put the base coefficient first. Naturality of the symmetry
moves it across the exchange arrow. Naturality of the target projection in the
source coefficient then appends l. The pullback tensor comparison followed by the
inverse-image square comparison is exactly ordinaryFiniteTwistedPullbackComparison.
For proper maps, the compactification projection/forget-supports identity
identifies the compact-support projection with ordinaryFiniteProjection, conjugated
by the proper coincidence isomorphisms. Substitute these identifications in the
square and cancel adjacent coincidence isomorphisms. No trace, projective-line
presentation, splitting, exponent or adjunction of exceptional inverse images occurs.
The identity square, zero coefficient complex and empty schemes obey the same
naturality and cancellation equations. -/
theorem properOrderedProjection_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' q' q g)
    [IsProper q] [IsProper q'] [HasCompactification q] [HasCompactification q']
    [QuasiCompact q']
    (L : DerivedCategoryModule A X) (L' : DerivedCategoryModule A X')
    (l : (ordinaryFinitePullback A g').obj L ≅ L') (K : DerivedCategoryModule A Y) :
    let F := ordinaryFinitePullback A g
    let R' := R(q')_![ModuleCat.{u + 1} A]
    let C := rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q
    let C' := rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q'
    let E := F.map (C.inv.app L) ≫ (rightDerivedLowerShriekBaseChangeMap A sq).app L ≫
      R'.map l.hom ≫ C'.hom.app L'
    let c := ordinaryFiniteTwistedPullbackComparison A q q' g g' L L' K
      ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).symm.app K) l
    F.map (ordinaryFiniteProjection A q L K ≫
        C.inv.app ((ordinaryFiniteTwistedPullback A q L).obj K)) ≫
      (rightDerivedLowerShriekBaseChangeMap A sq).app
        ((ordinaryFiniteTwistedPullback A q L).obj K) ≫ R'.map c.hom =
    (ordinaryFiniteTensorPullback A g K ((ordinaryFinitePushforward A q).obj L)).hom ≫
      ((ordinaryFiniteTensor A Y').obj (F.obj K)).map E ≫
      ordinaryFiniteProjection A q' L' (F.obj K) ≫
      C'.inv.app ((ordinaryFiniteTwistedPullback A q' L').obj (F.obj K)) := by
  dsimp only
  let W := (ordinaryFiniteTwistedPullback A q L).obj K
  let W₂ := (ordinaryFiniteTwistedPullback A q'
    ((ordinaryFinitePullback A g').obj L)).obj ((ordinaryFinitePullback A g).obj K)
  let W₃ := (ordinaryFiniteTwistedPullback A q' L').obj ((ordinaryFinitePullback A g).obj K)
  let u : (ordinaryFinitePullback A g').obj W ⟶
      ((ordinaryFiniteTensor A X').obj
        ((ordinaryFinitePullback A g').obj ((ordinaryFinitePullback A q).obj K))).obj
          ((ordinaryFinitePullback A g').obj L) :=
    (ordinaryFiniteTensorPullback A g' ((ordinaryFinitePullback A q).obj K) L).hom
  let s : ((ordinaryFiniteTensor A X').obj
        ((ordinaryFinitePullback A g').obj ((ordinaryFinitePullback A q).obj K))).obj
          ((ordinaryFinitePullback A g').obj L) ⟶ W₂ :=
    (derivedTensorRight (ModuleCat.{u + 1} A) X'
      ((ordinaryFinitePullback A g').obj L)).map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).symm.app K).hom
  let v : W₂ ⟶ W₃ :=
    ((ordinaryFiniteTensor A X').obj
      ((ordinaryFinitePullback A q').obj ((ordinaryFinitePullback A g).obj K))).map
      l.hom
  have hp := compactProjectionMapCoeffFirst_baseChangeMap A sq L K
  have hn := compactProjection_coefficient_naturality A q'
    ((ordinaryFinitePullback A g).obj K) l.hom
  have ht := leftDerivedUpperStarTensorIso_hom_naturality_right
    (A := ModuleCat.{u + 1} A) g K
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} A) q).inv.app L)
  have hP' := orderedProjection_inv_coincidence A q' ((ordinaryFinitePullback A g).obj K) L'
  exact forwardExchange (ordinaryFinitePullback A g) (R(q')_![ModuleCat.{u + 1} A])
    ((ordinaryFiniteTensor A Y').obj ((ordinaryFinitePullback A g).obj K))
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q').hom.app L')
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q').inv.app L')
    (Iso.hom_inv_id_app
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q') L')
    (B := (rightDerivedLowerShriekBaseChangeMap A sq).app
      ((ordinaryFiniteTwistedPullback A q L).obj K))
    (u := u) (s := s) (v := v)
    (a := ((ordinaryFiniteTensor A Y).obj K).map
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).inv.app L))
    (p := compactProjectionMapCoeffFirst A q K L)
    (orderedProjection_inv_coincidence A q K L) hP' hp hn ht

end AlgebraicGeometry.Etale

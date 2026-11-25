/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# Canonical maps and predicates for derived direct-image coherence

Source: blueprint main-20261015, `proposition-composition-base-change-rf-shriek--1`, Composition
isomorphism and Canonicity and associativity; Stacks Tags 08BJ, 070I, 070Y and 0D6E
(blueprint: def-sfb-derived-direct-image-open-coherence-data).

All categories below are the ordinary unbounded derived categories of internal modules
on the small pro-etale sites, with the actual pulled-back condensed coefficient rings.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Direct image preserves K-injectives, as the right adjoint of exact module pullback.
Source: Stacks Tag 08BJ (blueprint: lem-sfb-derived-direct-image-open-coherence). -/
instance lowerStar_preservesKInjectives {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (lowerStar Λ f).PreservesKInjectiveComplexes :=
  (upperStarLowerStarAdjunction Λ f).preservesKInjectiveComplexes

/-- The resolution-normalized composition comparison: derive the inverse of the existing
module direct-image comparison and then use the canonical derived composition isomorphism.
Source: Stacks Tag 0D6E (blueprint: lem-sfb-derived-direct-image-open-coherence). -/
noncomputable def directImageComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (lowerStar Λ (f ≫ g)).rightDerivedFunctor ≅
      (lowerStar Λ f).rightDerivedFunctor ⋙ (lowerStar Λ g).rightDerivedFunctor :=
  Functor.rightDerivedFunctorNatIso (lowerStarComp Λ f g).symm ≪≫
    Functor.rightDerivedFunctorCompIso (lowerStar Λ f) (lowerStar Λ g)

/-- The canonical pullback square comparison on module objects; coefficient actions use
extension along alpha, equivalently restriction along alpha inverse by CartesianCoefficients.
Source: blueprint composition proof (blueprint: lem-sfb-derived-direct-image-open-coherence). -/
noncomputable def openCoherencePullbackSquare
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} (sq : CommSq i f' f j) :
    upperStar Λ j ⋙ upperStar Λ f' ≅ upperStar Λ f ⋙ upperStar Λ i :=
  (upperStarComp Λ f' j).symm ≪≫
    eqToIso (congrArg (upperStar Λ) sq.w.symm) ≪≫ upperStarComp Λ i f

/-- The canonical underived open restriction map, defined as the mate of the specified
pullback square comparison. Its sectionwise normalization is stated below.
Source: Stacks Tag 09A5 (blueprint: lem-sfb-derived-direct-image-open-coherence). -/
noncomputable def directImageOpenRestriction
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} (sq : CommSq i f' f j) :
    lowerStar Λ f ⋙ upperStar Λ j ⟶ upperStar Λ i ⋙ lowerStar Λ f' :=
  (mateEquiv (upperStarLowerStarAdjunction Λ f) (upperStarLowerStarAdjunction Λ f')
    (TwoSquare.mk _ _ _ _ (openCoherencePullbackSquare Λ sq).hom))

/-- The same pullback square comparison after exact, termwise passage to derived categories.
Source: blueprint composition proof (blueprint: lem-sfb-derived-direct-image-open-coherence). -/
noncomputable def derivedOpenCoherencePullbackSquare
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} (sq : CommSq i f' f j) :
    (upperStar Λ j).mapDerivedCategory ⋙ (upperStar Λ f').mapDerivedCategory ≅
      (upperStar Λ f).mapDerivedCategory ⋙ (upperStar Λ i).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (openCoherencePullbackSquare Λ sq) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The canonical derived open restriction map, using the exact-left derived adjunctions.
Source: blueprint composition proof (blueprint: lem-sfb-derived-direct-image-open-coherence). -/
noncomputable def derivedDirectImageOpenRestriction
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} (sq : CommSq i f' f j) :
    (lowerStar Λ f).rightDerivedFunctor ⋙ (upperStar Λ j).mapDerivedCategory ⟶
      (upperStar Λ i).mapDerivedCategory ⋙ (lowerStar Λ f').rightDerivedFunctor :=
  (mateEquiv
    (upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction Λ f').mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (derivedOpenCoherencePullbackSquare Λ sq).hom))

/-- Open restriction preserves K-injectives because exact extension by zero is its left
adjoint. Source: Stacks Tag 08BJ (blueprint: lem-sfb-derived-direct-image-open-coherence). -/
instance upperStar_preservesKInjectives {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] : (upperStar Λ j).PreservesKInjectiveComplexes :=
  (openImmersionLowerShriekUpperStarAdjunction Λ j).preservesKInjectiveComplexes

/-- The canonical open-slice section identification, expressed by the module adjunction
unit at the distinguished site object. Source: Stacks Tag 09A5
(blueprint: lem-sfb-derived-direct-image-open-coherence). -/
noncomputable def openCoherenceSectionCoprojection
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (V : X.ProEt) :
    M.X.obj.obj
        (op ((MorphismProperty.Over.map (f := j) ⊤ (inferInstance : WeaklyEtale j)).obj V)) →
      ((upperStar Λ j).obj M).X.obj.obj (op V) :=
  fun s ↦ ((upperStar Λ j).obj M).X.obj.map
    ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j inferInstance trivial).unit.app V).op
      ((((upperStarLowerStarAdjunction Λ j).unit.app M).hom.hom.app
        (op ((MorphismProperty.Over.map (f := j) ⊤
          (inferInstance : WeaklyEtale j)).obj V))) s)

/-- The fibre-product identification used to compare sections in a Cartesian open square.
It is the identity on the test object and the specified open inclusion on the other factor.
Source: blueprint composition proof (blueprint: lem-sfb-derived-direct-image-open-coherence). -/
noncomputable def openCoherenceSectionArrow
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion i]
    (sq : CommSq i f' f j) (V : Y'.ProEt) :
    (MorphismProperty.Over.map (f := i) ⊤ (inferInstance : WeaklyEtale i)).obj
        ((Scheme.proEtaleBaseChange f').obj V) ⟶
      (Scheme.proEtaleBaseChange f).obj
        ((MorphismProperty.Over.map (f := j) ⊤ (inferInstance : WeaklyEtale j)).obj V) :=
  MorphismProperty.Over.homMk
    (pullback.map V.hom f' (V.hom ≫ j) f (𝟙 V.left) i j
      (Category.id_comp _).symm sq.w.symm)
    (pullback.lift_snd _ _ _)

/-- Sectionwise normalization: the open-slice identifications are bijective, and the
comparison sends a section to the same section along the canonical fibre-product map.
Identity maps and identity opens are included in these quantifiers.
Source: Stacks Tag 09A5 (blueprint: lem-sfb-derived-direct-image-open-coherence). -/
def OpenCoherenceSectionwise
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion i]
    (sq : CommSq i f' f j) : Prop :=
  (∀ (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (V : Y'.ProEt), Function.Bijective (openCoherenceSectionCoprojection Λ j M V)) ∧
  (∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (V : X'.ProEt), Function.Bijective (openCoherenceSectionCoprojection Λ i M V)) ∧
  ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (V : Y'.ProEt)
    (s : M.X.obj.obj (op ((Scheme.proEtaleBaseChange f).obj
      ((MorphismProperty.Over.map (f := j) ⊤ (inferInstance : WeaklyEtale j)).obj V)))),
    ((directImageOpenRestriction Λ sq).app M).hom.hom.app (op V)
        (openCoherenceSectionCoprojection Λ j ((lowerStar Λ f).obj M) V s) =
      openCoherenceSectionCoprojection Λ i M ((Scheme.proEtaleBaseChange f').obj V)
        (M.X.obj.map (openCoherenceSectionArrow sq V).op s)

/-- Associativity with the canonical functor associator and scheme associativity inserted.
Source: blueprint canonicity paragraph (blueprint: lem-sfb-derived-direct-image-open-coherence).
-/
def DirectImageCompositionAssociative {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) : Prop :=
  (directImageComposition Λ (f ≫ g) h).hom ≫
      whiskerRight (directImageComposition Λ f g).hom
        (lowerStar Λ h).rightDerivedFunctor ≫ (Functor.associator _ _ _).hom =
    (Functor.rightDerivedFunctorNatIso
      (eqToIso (congrArg (lowerStar Λ) (Category.assoc f g h)))).hom ≫
      (directImageComposition Λ f (g ≫ h)).hom ≫
      whiskerLeft (lowerStar Λ f).rightDerivedFunctor (directImageComposition Λ g h).hom

-- Use the same `EssentiallySmall` instance as the derived functors themselves, so that the
-- kernel can match the `representative` field against them
-- (see `DerivedOpenRestrictionNormalization`).
attribute [-instance] InternalAbelianSheafModule.comparison_essentiallySmall in
/-- Open restriction is invertible and is the class of the degreewise canonical underived
restriction comparison on every K-injective representative. No boundedness is imposed.
Source: Stacks Tags 08BJ, 070I and 070Y
(blueprint: lem-sfb-derived-direct-image-open-coherence). -/
structure DirectImageRestrictionNormalized
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion i]
    (sq : CommSq i f' f j) : Prop where
  /-- The derived comparison is invertible. -/
  derived_isIso : IsIso (derivedDirectImageOpenRestriction Λ sq)
  /-- The specified underived mate is invertible. -/
  underived_isIso : IsIso (directImageOpenRestriction Λ sq)
  /-- The open-slice coprojections and section formula have the specified normalization. -/
  sectionwise : OpenCoherenceSectionwise Λ sq
  /-- The derived mate has the specified value on every K-injective representative. -/
  representative :
    letI : Preadditive
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
      (Mod.instAbelian (condensedRingObj Λ X)).toPreadditive
    letI : Preadditive
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :=
      (Mod.instAbelian (condensedRingObj Λ Y)).toPreadditive
    letI : Preadditive
      (Mod (Sheaf (Scheme.ProEt.topology X') Ab.{u + 1}) (condensedRingObj Λ X')) :=
      (Mod.instAbelian (condensedRingObj Λ X')).toPreadditive
    letI : Preadditive
      (Mod (Sheaf (Scheme.ProEt.topology Y') Ab.{u + 1}) (condensedRingObj Λ Y')) :=
      (Mod.instAbelian (condensedRingObj Λ Y')).toPreadditive
    ∀ (I : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
      [I.IsKInjective],
      (derivedDirectImageOpenRestriction Λ sq).app (DerivedCategory.Q.obj I) ≫
          (lowerStar Λ f').rightDerivedFunctor.map
            ((upperStar Λ i).mapDerivedCategoryFactors.hom.app I) =
        (upperStar Λ j).mapDerivedCategory.map
            ((lowerStar Λ f).rightDerivedFunctorObjQIso I).hom ≫
          (upperStar Λ j).mapDerivedCategoryFactors.hom.app
            (((lowerStar Λ f).mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (directImageOpenRestriction Λ sq) (.up ℤ)).app I) ≫
          ((lowerStar Λ f').rightDerivedFunctorObjQIso
            (((upperStar Λ i).mapHomologicalComplex (.up ℤ)).obj I)).inv

/-- Exact derived restriction along a composite, including its canonical comparison.
Source: blueprint canonicity paragraph (blueprint: lem-sfb-derived-direct-image-open-coherence).
-/
noncomputable def openCoherenceRestrictionComp
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) (j : Y ⟶ Z) :
    (upperStar Λ (i ≫ j)).mapDerivedCategory ≅
      (upperStar Λ j).mapDerivedCategory ⋙ (upperStar Λ i).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (upperStarComp Λ i j) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

end AlgebraicGeometry.ProEtale.CondensedRing
